#include "AstTransforms.h"
#include "Global.h"
#include <memory>
#include <string>
#include <numeric>

using namespace souffle;

/** Helper class to generate subsets of k of elements
    out of sets of n elements */
template<class I>
class choose {
  std::vector<I> its;
  I ibegin, iend;
  unsigned k;

public:
  choose(I ibegin, I iend, unsigned k) :
    its(k), ibegin(ibegin), iend(iend), k(k) {
    I it = ibegin;
    std::iota(its.begin(), its.end(), it);
  }

  bool next() {
    unsigned pos = k-1;

    ++its[pos];
    if (its[pos] != iend)
      return true;

    while (pos > 0) {
      pos--;
      auto nit = its[pos];
      unsigned i = pos;
      for (; i < k && nit != iend; ++i) {
        its[i] = ++nit;
      }
      if (i == k && nit != iend)
        return true;
    }
    return false;
  }

  I operator[](unsigned i) const {
    return its[i];
  }

  using iterator = typename decltype(its)::iterator;

  iterator begin() { return its.begin(); }
  iterator end() { return its.end(); }
};

/** for every relation, generate other relations to test for functional relations
    between its columns */
std::vector<std::unique_ptr<AstRelation>> generateFuncTestPredicates(const AstRelation &R) {
  auto rName = R.getName().getName();
  auto nArgs = R.getArity();

  std::vector<unsigned> indices(nArgs);
  std::iota(indices.begin(), indices.end(), 0);

  std::vector<std::unique_ptr<AstRelation>> clauses;

  for (unsigned n = nArgs - 1; n > 0; --n) {
    auto choice = choose<decltype(indices)::iterator>(indices.begin(), indices.end(), n);
    do {
      auto complement = std::set<unsigned>(indices.begin(), indices.end());
      std::string relNamePrefix = "nf_";
      relNamePrefix += rName;

      std::set<unsigned> choiceSet;
      for (auto it = choice.begin(), end = choice.end(); it != end; ++it) {
        relNamePrefix += "_" + std::to_string(**it);
        complement.erase(**it);
        choiceSet.insert(**it);
      }

      relNamePrefix += "_to";

      for (auto i : complement) {
        auto relName = relNamePrefix + "_" + std::to_string(i);
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

        clause->print(std::cout);
        std::cout << "\n";

        auto rel = std::make_unique<AstRelation>();
        rel->setName(relId);
        rel->addClause(std::move(clause));
        rel->setQualifier(OUTPUT_RELATION);

        rel->print(std::cout);
        std::cout << "\n";


        clauses.push_back(std::move(rel));
      }
    } while(choice.next());
  }

  return clauses;
}

bool InsertFuncChecksTransformer::transform(AstTranslationUnit &translationUnit) {
  auto &prog = *translationUnit.getProgram();
  for (auto *r : prog.getRelations()) {
    if (!r->isInput())
      continue;
    auto funcTestRels = generateFuncTestPredicates(*r);
  }

  return false;
}

/** Some test code that is run at application startup time */
struct SelfTest {
  std::vector<int> v;

  static void print_choose(choose<decltype(v)::iterator> &p) {
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
  }
};

#ifndef NDEBUG
SelfTest t;
#endif
