#include "AstTransforms.h"
#include "Global.h"
#include <memory>
#include <string>
#include <numeric>
#include <map>
#include <set>

using namespace souffle;

#ifndef NDEBUG
#define DEBUG(X) do { \
  if (Global::config().has("debug")) { X; } \
  } while (0)
#else
#define DEBUG(X)
#endif


/** TODO:
    - add rules from functions with more arguments to functions with a subset of arguments
    -
 */

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

/** Generator for all the non-empty subsets of a given set */
template<class I>
class subset {
  unsigned n, i;
  choose<I> c;
  I ibegin, iend;
public:
  subset(I ibegin, I iend) : n(std::distance(ibegin, iend)), i(1), c(ibegin, iend, 1), ibegin(ibegin), iend(iend) {
  }

  bool next() {
    bool isNext = c.next();
    if (!isNext) {
      if (i < n) {
        ++i;
        c = choose<I>(ibegin, iend, i);
        return true;
      } else {
        return false;
      }
    }
    return true;
  }

  using iterator = typename decltype(c)::iterator;

  iterator begin() { return c.begin(); }
  iterator end() { return c.end(); }
};


static std::string generateRelName(const std::string &predName, const std::set<unsigned> argSet, unsigned dst) {
  std::string res = "nf_";
  res += predName;
  for (unsigned i : argSet) {
    res += "_" + std::to_string(i);
  }
  res += "_to_" + std::to_string(dst);
  return res;
}

/** for every relation, generate other relations to test for functional relations
    between its columns */
std::vector<std::unique_ptr<AstRelation>> generateFuncTestPredicates(const AstRelation &R) {
  auto rName = R.getName().getName();
  auto nArgs = R.getArity();

  std::vector<unsigned> indices(nArgs);
  std::iota(indices.begin(), indices.end(), 0);

  std::map<std::pair<std::set<unsigned>, unsigned>, std::unique_ptr<AstRelation>> clauses;

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

  // now move all the relations from a map to a vector
  std::vector<std::unique_ptr<AstRelation>> rRelations;
  std::transform(clauses.begin(), clauses.end(), std::back_inserter(rRelations),
                 [](decltype(clauses)::value_type &entry) {
                   return std::move(entry.second);
                 });

  return rRelations;
}

bool InsertFuncChecksTransformer::transform(AstTranslationUnit &translationUnit) {
  if (!Global::config().has("func-checks"))
    return false;


  auto &prog = *translationUnit.getProgram();
  for (auto *r : prog.getRelations()) {
    if (!r->isInput())
      continue;
    auto funcTestRels = generateFuncTestPredicates(*r);

    for (auto &rel : funcTestRels) {
      prog.appendRelation(std::move(rel));
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
SelfTest t;
#endif
