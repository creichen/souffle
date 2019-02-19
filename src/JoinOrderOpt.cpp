#include "AstTransforms.h"
#include "Global.h"
#include "json11.h"
#include <memory>
#include <string>
#include <numeric>
#include <map>
#include <set>
#include <fstream>
#include <cmath>
#include "FuncChecksCommon.h"
#include "boost/range/irange.hpp"
#include "boost/pending/disjoint_sets.hpp"

using namespace souffle;

class SimpleCostModel {
  const std::map<ProjDesc, rel_size_t> &projSize;
  const std::vector<AstAtom*> &atoms;
  const std::set<std::string> joinVars;
public:
  SimpleCostModel(const std::vector<AstAtom*> &atoms,
                  const std::map<ProjDesc, rel_size_t> &projSize) :
    projSize(projSize),
    atoms(atoms),
    joinVars(collectJoinVariables(atoms.begin(), atoms.end())) {}

  rel_size_t relationSize(unsigned i) const {
    auto r = boost::irange(atoms[i]->getArity());
    std::set<unsigned> indices(r.begin(), r.end());
    auto it = projSize.find(make_pair(atoms[i]->getName().getName(), std::move(indices)));
    assert (it != projSize.end());
    return it->second;
  }

  rel_size_t joinSize(const std::vector<unsigned> &joinAtoms) const {
    // This implements the first algorithm in the paper
    // "On the Estimation of Join Result Sizes"

    // use a set, to easily iterate in increasing order
    std::vector<rel_size_t> selectivity;

    DEBUG(
      std::cout << "Computing join size on vars: ";
      for (auto &v : joinVars)
        std::cout << v << " ";
      std::cout << "\n";
      );

    for (unsigned atomIdx : joinAtoms) {
      const auto &joinIndices = collectVarIndices(atoms[atomIdx], joinVars);
      assert(!joinIndices.empty());
      auto it = projSize.find(make_pair(atoms[atomIdx]->getName().getName(), std::move(joinIndices)));
      assert (it != projSize.end());

      // TODO: this probably will not happen...
      if (it->second == 0) {
        std::cerr << "Relation " << atoms[atomIdx]->getName().getName()
                  << " has an empty projection on " << joinIndices << "\n";
        return 0;
      }

      assert(it->second && "Relation with empty projection");
      selectivity.push_back(it->second);

      DEBUG(
        atoms[atomIdx]->print(std::cout);
        std::cout << "\n projection size: " << it->second;
        std::cout << "\n relation size: " << relationSize(atomIdx) << "\n";
        );
    }

    // Multiply all the selectivities, except the smallest one
    // The value of the product can be fairly bing and overflow uint64_t
    // Use double to get a larger range.

    std::sort(selectivity.begin(), selectivity.end());
    auto selP = std::accumulate(std::next(selectivity.begin()), selectivity.end(), 1.0,
                                std::multiplies<double>());
    auto sizeP = std::accumulate(joinAtoms.begin(), joinAtoms.end(), 1.0,
                                 [this](double f, unsigned i){
                                   return f * relationSize(i);
                                 });

    assert(selP != 0.0);
    auto r = sizeP / selP;
    assert(r < (float)std::numeric_limits<rel_size_t>::max());


    DEBUG(std::cout << "Estimated join size " << r << "\n");

    return r;
  }

  unsigned countAtoms() const {
    return atoms.size();
  }
};


/** Given a vector of atoms, partition it such that
    atoms in different classes have disjoint argument
    sets.
 */
static std::vector<std::vector<AstAtom*>>
getDisjointJoins(const std::vector<AstAtom*> &atoms) {
  // union-find container definition
  using RankPA = std::map<AstAtom*, unsigned>;
  using ParentPA = std::map<AstAtom*, AstAtom*>;
  RankPA ranks;
  ParentPA parents;
  boost::associative_property_map<RankPA> ranksp(ranks);
  boost::associative_property_map<ParentPA> parentsp(parents);
  boost::disjoint_sets<decltype(ranksp), decltype(parentsp)> eqAtoms(ranksp, parentsp);
  // collect the arguments of the atoms
  std::set<std::string> joinVars;
  std::map<AstAtom*, std::set<std::string>> argMap;
  for (auto *atom : atoms) {
    eqAtoms.make_set(atom);
    for (auto *arg : atom->getArguments()) {
      if (auto *var = dynamic_cast<AstVariable*>(arg)) {
        argMap[atom].emplace(var->getName());
      } else {
        assert(dynamic_cast<AstUnnamedVariable*>(arg) && "Expecting only variables as arguments");
      }
    }
  }

  // any two atoms that have arguments in common belong to
  // the same equivalence class
  for (auto it1 = argMap.begin(), end = argMap.end(); it1 != end; ++it1) {
    for (auto it2 = std::next(it1); it2 != end; ++it2) {
      auto &p1 = *it1, &p2 = *it2;
      assert(p1.first != p2.first);

      std::vector<std::string> commonArgs;
      std::set_intersection(p1.second.begin(), p1.second.end(),
                            p2.second.begin(), p2.second.end(),
                            std::back_inserter(commonArgs));
      if (!commonArgs.empty())
        eqAtoms.union_set(p1.first, p2.first);
    }
  }

  // add a comparison function for deterministic iteration order
  auto comp = [](AstAtom *a, AstAtom *b) {
    return a->getName().getName() <
           b->getName().getName();
  };
  std::map<AstAtom*, std::vector<AstAtom*>, decltype(comp)> eqClasses(comp);
  for (auto *atom : atoms) {
    eqClasses[eqAtoms.find_set(atom)].push_back(atom);
  }

  // now move everything into a vector
  std::vector<std::vector<AstAtom*>> ret;
  for (auto &kv : eqClasses) {
    assert(!kv.second.empty() && "Unexpected empty join set");
    ret.emplace_back(kv.second);
  }

  return ret;
}

class SimpleJoinOrderOptimizer : public JoinOrderOptimizer<SimpleCostModel> {
  SimpleCostModel scm;
public:
  // Note: the scm object passed into the JoinOrderOptimizer constructor is
  // not initialized. This should be OK as long as the JoinOrderOptimizer
  // constructor does nothing more than storing a reference to scm.
  SimpleJoinOrderOptimizer(std::vector<AstAtom*> &joinSet,
                           const std::map<ProjDesc, rel_size_t> &projSize) :
    JoinOrderOptimizer(scm /*not initialized!!!*/), scm(joinSet, projSize) {}
};

static bool optimizeClause(AstClause &clause,
                           const std::map<ProjDesc, rel_size_t> &projSize) {

  const auto &atoms = clause.getAtoms();
  auto joinSets = getDisjointJoins(atoms);

  std::cout << "=== Optimizing clause:\n";
  clause.print(std::cout);

  std::cout << "\nJoin sets: " << joinSets.size() << "\n";

  auto atomIndex = [&atoms](const AstAtom* a) {
    auto it = std::find(atoms.begin(), atoms.end(), a);
    assert(it != atoms.end());
    return std::distance(atoms.begin(), it);
  };

  std::vector<unsigned> newAtomOrder;

  // TODO: heuristic
  // sort the join sets on descending order
  std::sort(joinSets.begin(), joinSets.end(),
            [](const decltype(joinSets)::value_type &v1,
               const decltype(joinSets)::value_type &v2) {
              return v1.size() < v2.size();
            });

  for (auto &joinSet : joinSets) {
    if (joinSet.size() == 1) {
      // not worth to optimize joins involving one atom
      std::cout << "\[" << atomIndex(joinSet[0]) << "]\n";
      newAtomOrder.push_back(atomIndex(joinSet[0]));
      continue;
    }

    SimpleJoinOrderOptimizer jopt(joinSet, projSize);
    SimpleJoinOrderOptimizer::bitset bits(joinSet.size(), 0);
    bits.set(0, joinSet.size(), true);
    const auto &joinOrderR = jopt.getReverseJoinOrder(bits);

    std::cout << "\n[";
    for (auto i : make_range(joinOrderR.rbegin(), joinOrderR.rend())) {
      std::cout << atomIndex(joinSet[i]) << " ";
      newAtomOrder.push_back(atomIndex(joinSet[i]));

    }
    std::cout << "]\n";
  }

  clause.reorderAtoms(newAtomOrder);
  clause.clearExecutionPlan();

  clause.print(std::cout);
  std::cout << "\n===================================\n";

  return false;
}

bool JoinOrderTransformer::transform(AstTranslationUnit &translationUnit) {
  if (!Global::config().has("opt-join"))
    return false;

  // read the size of the projection from a JSON file
  std::ifstream projSizeS(Global::config().get("opt-join"));
  std::string projSizeStr((std::istreambuf_iterator<char>(projSizeS)), std::istreambuf_iterator<char>());
  std::string err;
  auto projSizeJ = json11::Json::parse(projSizeStr, err);

  assert(projSizeJ.is_array());
  std::map<ProjDesc, rel_size_t> projSize;
  for (auto &o : projSizeJ.array_items()) {
    assert(o.is_object());
    const auto &name = o["name"].string_value();
    const rel_size_t size = o["size"].long_value();
    std::set<unsigned> indices;
    for (auto i : o["attr"].array_items())
      indices.insert(i.int_value());
    projSize.emplace(std::make_pair(name, std::move(indices)), size);
  }

  // now build a cost model object
  auto *program = translationUnit.getProgram();

  for (auto *rel : program->getRelations()) {
    for (auto *clause : rel->getClauses()) {
      if (shouldOptimizeClause(*clause))
        optimizeClause(*clause, projSize);
    }
  }

  return false;

}
