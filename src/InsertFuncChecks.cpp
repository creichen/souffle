#include "AstTransforms.h"
#include "Global.h"
#include "json11.h"
#include <memory>
#include <string>
#include <numeric>
#include <map>
#include <set>
#include <fstream>
#include "FuncChecksCommon.h"
#include "boost/range/irange.hpp"
#include "boost/pending/disjoint_sets.hpp"

using namespace souffle;



static std::string generateRelName(const std::string &predName,
                                   const std::set<unsigned> argSet,
                                   unsigned dst) {
  std::string res = "nf_";
  res += predName;
  for (unsigned i : argSet) {
    res += "_" + std::to_string(i);
  }
  res += "_to_" + std::to_string(dst);
  return res;
}

static std::string generateProjectionName(const std::string &relName,
                                          const std::set<unsigned> &args) {
  std::string res = "proj_";
  res += relName;
  for (unsigned i : args) {
    res += "_" + std::to_string(i);
  }
  return res;
}

/** Generate a projection of relation R using arguments args. Output the size
    of the projection.
 */
std::unique_ptr<AstRelation>
generateProjection(const AstRelation &R, const std::set<unsigned> &args) {
  auto relId = AstRelationIdentifier(generateProjectionName(R.getName().getName(), args));

  auto rel = std::make_unique<AstRelation>();
  rel->setName(relId);
  // transfer the types
  for (auto arg : args) {
    auto attr = R.getAttribute(arg);
    rel->addAttribute(std::unique_ptr<AstAttribute>(attr->clone()));
  }
  // now introduce a projection clause
  auto cls = std::make_unique<AstClause>();
  auto head = std::make_unique<AstAtom>(rel->getName());
  auto body = std::make_unique<AstAtom>(R.getName());

  for (auto arg : args) {
    head->addArgument(std::make_unique<AstVariable>("v" + std::to_string(arg)));
  }

  for (unsigned i = 0; i < R.getArity(); ++i) {
    if (!args.count(i))
      body->addArgument(std::make_unique<AstUnnamedVariable>());
    else
      body->addArgument(std::make_unique<AstVariable>("v" + std::to_string(i)));
  }

  cls->setHead(std::move(head));
  cls->addToBody(std::move(body));

  DEBUG(
    cls->print(std::cout);
    std::cout << "\n";);


  rel->addClause(std::move(cls));

  auto io = std::make_unique<AstIODirective>();
  io->setAsPrintSize();
  io->addName(relId);

  rel->addIODirectives(std::move(io));

  DEBUG(rel->print(std::cout);
        std::cout << "\n");


  return rel;
}

template<typename I>
static std::set<std::string> collectJoinVariables(I begin, I end) {
  std::set<std::string> joinVars;
  std::map<AstAtom*, std::set<std::string>> argMap;
  for (auto *atom : make_range(begin, end)) {
    for (auto *arg : atom->getArguments()) {
      auto *var = dynamic_cast<AstVariable*>(arg);
      assert(var && "Expecting only variables as arguments");
      argMap[atom].emplace(var->getName());
    }
  }

  for (auto it1 = argMap.begin(), end = argMap.end(); it1 != end; ++it1) {
    for (auto it2 = std::next(it1); it2 != end; ++it2) {
      auto &p1 = *it1, &p2 = *it2;
      assert(p1.first != p2.first);

      std::vector<std::string> commonArgs;
      std::set_intersection(p1.second.begin(), p1.second.end(),
                            p2.second.begin(), p2.second.end(),
                            std::back_inserter(commonArgs));

      std::set<std::string> nextJoinVars;
      std::set_union(joinVars.begin(), joinVars.end(), commonArgs.begin(), commonArgs.end(),
                     std::inserter(nextJoinVars, nextJoinVars.begin()));
      joinVars = std::move(nextJoinVars);
    }
  }
  return joinVars;
}

static std::set<unsigned> collectVarIndices(const AstAtom *atom,
                                            const std::set<std::string> &joinVars) {
  std::set<unsigned> projIndices;
  for (unsigned i = 0; i < atom->getArity(); ++i) {
    auto *var = dynamic_cast<AstVariable*>(atom->getArgument(i));
    assert(var && "Expecting only variables as arguments");
    if (joinVars.count(var->getName()))
      projIndices.insert(i);
  }
  return projIndices;
}

using ProjDesc = std::pair<std::string /* original relation name */,
                           std::set<unsigned> /* projection indices */>;

static std::map<ProjDesc, std::unique_ptr<AstRelation>>
generateProjectionsForProgram(AstProgram *prog) {
  std::map<ProjDesc, std::unique_ptr<AstRelation>> projections;

  auto generateProj = [&projections](const AstRelation *relToProj,
                                     const std::set<unsigned> &projIndices) {
    if (!projections.count(std::make_pair(relToProj->getName().getName(), projIndices))) {
      auto projRel = generateProjection(*relToProj, projIndices);
      projections.emplace(std::make_pair(relToProj->getName().getName(), projIndices),
                          std::move(projRel));
    }
  };

  for (auto *rel : prog->getRelations()) {
    for (auto *cls : rel->getClauses()) {
      // optimize only relations with fixed execution plans
      // TODO: introduce a new annotation for this
      if (!cls->getExecutionPlan())
        continue;

      const auto &atoms = cls->getAtoms();
      auto joinVars = collectJoinVariables(atoms.begin(), atoms.end());

      for (auto *atom : atoms) {
        const auto &projIndices = collectVarIndices(atom, joinVars);
        if (projIndices.empty())
          continue;

        auto *relToProj = prog->getRelation(atom->getName());
        generateProj(relToProj, projIndices);

        std::set<unsigned> allIndices(boost::irange(atom->getArity()).begin(),
                                      boost::irange(atom->getArity()).end());
        generateProj(relToProj, allIndices);
      }
    }
  }
  return projections;
}

bool ProjectionTransformer::transform(AstTranslationUnit &translationUnit) {
  if (!Global::config().has("gen-proj"))
    return false;

  auto projections =
    generateProjectionsForProgram(translationUnit.getProgram());

  auto &dir = Global::config().get("output-dir");
  std::ofstream projMapFile(dir + "/ProjMap.csv");

  for (auto &p : projections) {
    projMapFile << p.first.first << "\t";
    projMapFile << p.second->getName().getName();
    for (auto i : p.first.second) {
      projMapFile << "\t" << i;
    }
    projMapFile << "\n";
    translationUnit.getProgram()->appendRelation(std::move(p.second));
  }

  return false;
}

/** for every relation, generate other relations to test for functional relations
    between its columns */
std::map<FunctionalRelationDesc, std::unique_ptr<AstRelation>> generateFuncTestPredicates(const AstRelation &R) {
  auto rName = R.getName().getName();
  auto nArgs = R.getArity();

  std::vector<unsigned> indices(nArgs);
  std::iota(indices.begin(), indices.end(), 0);

  std::map<FunctionalRelationDesc, std::unique_ptr<AstRelation>> clauses;

  for (unsigned n = nArgs - 1; n > 0; --n) {
    auto choice = choose<decltype(indices)::iterator>(indices.begin(), indices.end(), n);
    do {
      auto complement = std::set<unsigned>(indices.begin(), indices.end());

      std::set<unsigned> choiceSet;
      for (auto it = choice.begin(), end = choice.end(); it != end; ++it) {
        complement.erase(**it);
        choiceSet.insert(**it);
      }

      for (auto i : complement) {
        auto relName = generateRelName(rName, choiceSet, i);
        auto relId = AstRelationIdentifier(relName);

        // generate nf_1_2_to_3()
        auto head = std::make_unique<AstAtom>(relId);

        // generate f(a1, a2, x, _, _), f(a1, a2, t, _, _)
        auto a1 = std::make_unique<AstAtom>(R.getName());
        auto a2 = std::make_unique<AstAtom>(R.getName());


        for (unsigned j = 0; j < nArgs; j++) {
          if (j == i) {
            a1->addArgument(std::make_unique<AstVariable>("x"));
            a2->addArgument(std::make_unique<AstVariable>("t"));
          } else if (choiceSet.find(j) != choiceSet.end()) {
            a1->addArgument(std::make_unique<AstVariable>("a_" + std::to_string(j)));
            a2->addArgument(std::make_unique<AstVariable>("a_" + std::to_string(j)));
          } else {
            // add placeholders
            a1->addArgument(std::make_unique<AstUnnamedVariable>());
            a2->addArgument(std::make_unique<AstUnnamedVariable>());
          }
        }

        auto diff = std::make_unique<AstBinaryConstraint>(BinaryConstraintOp::NE,
                                                          std::make_unique<AstVariable>("x"),
                                                          std::make_unique<AstVariable>("t"));

        auto clause = std::make_unique<AstClause>();

        // generate the clause nf_1_2_to_3() :- f(a1, a2, x, _, _), f(a1, a2, t, _, _,), x != t.
        clause->setHead(std::move(head));
        clause->addToBody(std::move(a1));
        clause->addToBody(std::move(a2));
        clause->addToBody(std::move(diff));

        DEBUG(
          clause->print(std::cout);
          std::cout << "\n";
          );

        auto rel = std::make_unique<AstRelation>();
        rel->setName(relId);
        rel->addClause(std::move(clause));

        DEBUG(
          rel->print(std::cout);
          std::cout << "\n";
          );

        auto io = std::make_unique<AstIODirective>();
        io->setAsOutput();
        io->addName(relId);

        rel->addIODirectives(std::move(io));
        clauses.insert(std::make_pair(std::make_pair(choiceSet, i), std::move(rel)));
      }
    } while(choice.next());
  }

  // generate implications of the form:
  // nf_1_to_3 () :- nf_1_2_to_3()
  for (auto &entry : clauses) {
    auto &args = entry.first.first;

    if (args.size() <= 1)
      continue;

    unsigned tgt = entry.first.second;
    auto &rel = entry.second;

    auto argSubsetGen = choose<decltype(entry.first.first)::iterator>(args.begin(), args.end(), args.size() - 1);
    do {
      std::set<unsigned> argSubset;
      for (auto it = argSubsetGen.begin(), end = argSubsetGen.end(); it != end; ++it) {
        argSubset.insert(**it);
      }

      auto body = std::make_unique<AstAtom>(rel->getName());
      auto head = std::make_unique<AstAtom>(generateRelName(rName, argSubset, tgt));

      auto clause = std::make_unique<AstClause>();
      clause->setHead(std::move(head));
      clause->addToBody(std::move(body));

      DEBUG(
        clause->print(std::cout);
        std::cout << "\n";
        );

      auto it = clauses.find(std::make_pair(argSubset, tgt));
      assert(it != clauses.end());
      it->second->addClause(std::move(clause));
    } while(argSubsetGen.next());
  }

  return clauses;
}




bool InsertFuncChecksTransformer::transform(AstTranslationUnit &translationUnit) {
  if (!Global::config().has("func-check"))
    return false;

  auto &dir = Global::config().get("output-dir");

  auto &prog = *translationUnit.getProgram();
  std::vector<std::unique_ptr<AstRelation>> newRelations;


  std::ofstream relMapFile(dir + "/RelMap.csv");

  for (auto *r : prog.getRelations()) {
    if (!r->isInput())
      continue;
    auto funcTestRels = generateFuncTestPredicates(*r);

    // newRelations.insert(newRelations.end(),
    //                     std::make_move_iterator(funcTestRels.begin()),
    //                     std::make_move_iterator(funcTestRels.end()));


    // SymbolTable symbolTable;
    // ErrorReport errorReport;
    // DebugReport debugReport;
    // auto newTU = std::make_unique<AstTranslationUnit>(
    //   std::unique_ptr<AstProgram>(new AstProgram()), symbolTable, errorReport, debugReport);

    auto newProg = std::unique_ptr<AstProgram>(new AstProgram());

    // add the types that are required
    for (const auto *t : prog.getTypes()) {
      newProg->addType(std::unique_ptr<AstType>(t->clone()));
    }

    // add the original relation
    newProg->appendRelation(std::unique_ptr<AstRelation>(r->clone()));
    std::string outFileName = dir + "/nf_" + r->getName().getName() + ".dl";

    // append all the generated relations and log the mappings to a file
    for (auto &newRel : funcTestRels) {
      relMapFile << r->getName().getName() << "\t";
      relMapFile << generateRelName(r->getName().getName(), newRel.first.first, newRel.first.second);
      for (unsigned i = 0; i < r->getArity(); ++i) {
        relMapFile << "\t";
        if (newRel.first.first.count(i))
          relMapFile << "S";
        else if (newRel.first.second == i)
          relMapFile << "T";
        else
          relMapFile << "X";
      }
      relMapFile << "\n";

      newProg->appendRelation(std::move(newRel.second));
    }


    std::ofstream outFile(outFileName);
    newProg->print(outFile);

    std::cout << "Generated " << outFileName << " with " << funcTestRels.size() << " function test relations\n";

  }

  // for (auto &rel : newRelations) {
  //   prog.appendRelation(std::move(rel));
  // }

  std::cout << "\nGenerated " << newRelations.size() << " function test relations\n";

  return false;
}

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
    // std::vector<AstAtom*> currentAtoms;
    // std::transform(joinAtoms.begin(), joinAtoms.end(),
    //    std::back_inserter(currentAtoms), [this](unsigned i) { return atoms[i]; });
    //const auto &joinVars = collectJoinVariables(currentAtoms.begin(), currentAtoms.end());

    // use a set, to easily iterate in increasing order
    std::set<rel_size_t> selectivity;

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
      selectivity.insert(it->second);
    }

    // Multiply all the selectivities, except the smallest one
    // The value of the product can be fairly bing and overflow uint64_t
    // Use double to get a larger range.



    auto selP = std::accumulate(std::next(selectivity.begin()), selectivity.end(), 1.0,
                                std::multiplies<double>());
    auto sizeP = std::accumulate(joinAtoms.begin(), joinAtoms.end(), 1.0,
                                 [this](double f, unsigned i){
                                   return f * relationSize(i);
                                 });
    assert(selP != 0.0);
    auto r = sizeP / selP;
    assert(r < (float)std::numeric_limits<rel_size_t>::max());
    return r;
  }

  unsigned countAtoms() const {
    return atoms.size();
  }
};


/** Given a vector of atoms partition it such that
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
      auto *var = dynamic_cast<AstVariable*>(arg);
      assert(var && "Expecting only variables as arguments");
      argMap[atom].emplace(var->getName());
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

static bool optimizeClause(AstClause &clause,
                           const std::map<ProjDesc, rel_size_t> &projSize) {

  const auto &atoms = clause.getAtoms();
  auto joinSets = getDisjointJoins(atoms);

  std::cout << "=== Optimizing clause:\n";
  clause.print(std::cout);

  std::cout << "\nJoin sets: " << joinSets.size() << "\n";

  for (auto &joinSet : joinSets) {

    if (joinSet.size() == 1)
      continue;

    SimpleCostModel scm(joinSet, projSize);
    JoinOrderOptimizer<SimpleCostModel> jopt(scm);

    JoinOrderOptimizer<SimpleCostModel>::bitset bits(scm.countAtoms(), 0);
    bits.set(0, scm.countAtoms(), true);
    const auto &joinOrderR = jopt.getReverseJoinOrder(bits);


    std::cout << "\n[";
    for (auto i : make_range(joinOrderR.rbegin(), joinOrderR.rend()))
      std::cout << i << " ";
    std::cout << "]\n";

  }

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
      if (clause->getExecutionPlan())
        optimizeClause(*clause, projSize);
    }
  }

  return false;

}


/** Some test code that is run at application startup time */
struct SelfTest {
  std::vector<int> v;

  template<typename T>
  static void print_choose(T &p) {
    do {
      std::cout << "(";
      for (auto it = p.begin(); it != p.end(); ++it)
        std::cout << **it << " ";
      std::cout << ")\n";
    } while (p.next());
  }

  SelfTest() {
    const unsigned N = 5;
    for (unsigned i = 0; i < N; ++i)
      v.push_back(i);

    using ptype = choose<decltype(v)::iterator>;

    auto p1 = ptype(v.begin(), v.end(), 3);
    print_choose(p1);

    auto p2 = ptype(v.begin(), v.end(), 1);
    print_choose(p2);

    auto p3 = ptype(v.begin(), v.end(), N);
    print_choose(p3);

    using stype = subset<decltype(v)::iterator>;
    auto s = stype(v.begin(), v.end());

    print_choose(s);

  }
};

#ifndef NDEBUG
#if 0
SelfTest t;
#endif
#endif
