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

std::set<unsigned> collectVarIndices(const AstAtom *atom,
                                     const std::set<std::string> &joinVars) {
  std::set<unsigned> projIndices;
  for (unsigned i = 0; i < atom->getArity(); ++i) {
    auto *var = dynamic_cast<AstVariable*>(atom->getArgument(i));
    if (var && joinVars.count(var->getName()))
      projIndices.insert(i);
  }
  return projIndices;
}

bool shouldOptimizeClause(const AstClause &cls) {
  if (cls.getExecutionPlan())
    return false;
  for (auto *atom : cls.getAtoms()) {
    for (auto *arg : atom->getArguments()) {
      if (!(dynamic_cast<AstVariable*>(arg)
            || dynamic_cast<AstUnnamedVariable*>(arg)))
        return false;
    }
  }
  return true;
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

  std::cout << "\nGenerated " << newRelations.size() << " function test relations\n";

  return false;
}
