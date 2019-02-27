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
static std::unique_ptr<AstRelation>
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
      if (!shouldOptimizeClause(*cls))
        continue;

      const auto &atoms = cls->getAtoms();
      auto joinVars = collectJoinVariables(atoms.begin(), atoms.end());

      for (auto *atom : atoms) {
        if (atom->getArity() == 0)
          continue;

        auto subsetGen = make_subset_gen(0, atom->getArity());
        do {
          std::set<unsigned> projIndices(subsetGen.begin(), subsetGen.end());
          auto *relToProj = prog->getRelation(atom->getName());
          generateProj(relToProj, projIndices);
        } while (subsetGen.next());
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

  DEBUG(std::cout << "Generated " << projections.size() << " projection relations.\n";);

  return false;
}
