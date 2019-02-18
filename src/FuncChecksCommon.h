#pragma once

#include "AstTransforms.h"
#include "Global.h"
#include <set>
#include <utility>
#include <numeric>
#include <boost/dynamic_bitset.hpp>
#include <cmath>
#include <fstream>
#include <map>
#include <iostream>

/** Debug macros
 */
#ifndef NDEBUG
#define DEBUG(X) do { \
  if (Global::config().has("debug")) { X; } \
  } while (0)
#else
#define DEBUG(X)
#endif

using FunctionalRelationDesc = std::pair<std::set<unsigned>, unsigned>;

using ProjDesc = std::pair<std::string /* original relation name */,
                           std::set<unsigned> /* projection indices */>;


/**
   Collect variables that are common to at least two atoms in the range.
   Return a set containing the names of these variables.
 */
template<typename I>
std::set<std::string> collectJoinVariables(I begin, I end) {
  using namespace souffle;

  std::set<std::string> joinVars;
  std::map<AstAtom*, std::set<std::string>> argMap;
  for (auto *atom : make_range(begin, end)) {
    for (auto *arg : atom->getArguments()) {
      if (auto *var = dynamic_cast<AstVariable*>(arg)) {
        argMap[atom].emplace(var->getName());
      } else {
        assert((dynamic_cast<AstUnnamedVariable*>(arg) ||
               dynamic_cast<AstConstant*>(arg))
               && "Expecting only variables as arguments");
      }
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


/**
   A join order optimizer using dynamic programming:
   cost(A `join` B `join` C) = min(
         size(A `join` B) * log(size(C)) + cost(A `join` B),
         size(B `join` C) * log(size(A)) + cost(B `join` C),
         size(A `join` C) * log(size(B)) + cost(A `join` C)).
 */
using rel_size_t = uint64_t;

template<typename T>
class JoinOrderOptimizer {
public:
  using bitset = boost::dynamic_bitset<>;

private:
  T &costModel;
  // using the boost bitset and not the std one because
  // we need the find_first/find_next methods
  struct JoinInfo {
    bitset pred;
    unsigned size;
    float cost;
  };

  std::map<bitset, JoinInfo> costMap;
public:
  JoinOrderOptimizer(T &costModel) :
    costModel(costModel) {
  }
private:
  rel_size_t joinSize(bitset join) {
    std::vector<unsigned> joinAtoms;
    for (auto i = join.find_first(); i != bitset::npos; i = join.find_next(i)) {
      joinAtoms.push_back(i);
    }
    return costModel.joinSize(joinAtoms);
  }

  static float clampLog(rel_size_t n) {
    // the base here should probably depend on the type of tree
    // structure used to store the relation
    // TODO: put this in accord with the heuristics for the
    // relation structure
    return std::log2(std::max(n, rel_size_t(2u)));
  }
public:
  std::pair<float, rel_size_t> computeCost(bitset join) {
    auto it = costMap.find(join);
    if (it != costMap.end())
      return std::make_pair(it->second.cost, it->second.size);


    if (join.none())
      return std::make_pair(0.0f, 0);

    JoinInfo result;
    if (join.count() == 1) {
      result.pred = bitset(join.size());
      result.size = costModel.relationSize(join.find_first());
      result.cost = 0.0f;
    } else {
      auto costMin = std::numeric_limits<float>::max();
      unsigned iMin = 0;
      for (auto i = join.find_first();
           i != bitset::npos; i = join.find_next(i)) {
        bitset outerJoin = join;
        outerJoin.reset(i);

        auto subsetCostAndSize = computeCost(outerJoin);
        auto innerRelationSize = costModel.relationSize(i);

        auto joinCost = subsetCostAndSize.second * clampLog(innerRelationSize);

        if (costMin > joinCost) {
          iMin = i;
          costMin = joinCost;
        }
      }

      result.pred = join;
      result.pred.reset(iMin);
      result.size = joinSize(join);
      result.cost = costMin;
    }

    costMap.insert(std::make_pair(join, result));
    return std::make_pair(result.cost, result.size);
  }

  std::vector<unsigned> getReverseJoinOrder(bitset join) {
    std::vector<unsigned> ret;
    // force a cost computation, if that was not done already.
    computeCost(join);

    auto it = costMap.find(join);
    while (it != costMap.end()) {
      unsigned i = (it->first & ~it->second.pred).find_first();
      ret.push_back(i);
      it = costMap.find(it->second.pred);
    }
    return ret;
  }
};

/** Helper functions to iterate over all the elements in a tuple. Useless.
 */
template<unsigned i, typename Func, typename... Args>
struct tuple_internal {
private:
  static void apply(const std::tuple<Args...> &tpl, Func &f) {
    f.operator()(std::get<i>(tpl));
    tuple_internal<i + 1, Func, Args...>::apply(tpl, f);
  }
public:
  static void for_each(const std::tuple<Args...> &tpl, Func &f) {
    tuple_internal<sizeof...(Args), Func, Args...>::apply(tpl, f);
  }
};

template<typename Func, typename... Args>
struct tuple_internal<0, Func, Args...> {
private:
  static void apply(const std::tuple<Args...> &, Func &&f) {}
};

template<typename Func, typename... Args>
void tuple_for_each(const std::tuple<Args...> &tpl,  Func &f) {
  tuple_internal<sizeof...(Args), Func, Args...>::for_each(tpl, f);
}

template<typename...Args>
void writeOutSimpleCSV(const std::string &fileName, std::vector<std::tuple<Args...>> &vals) {
  std::ofstream outFile(fileName);
  struct {
    std::ofstream &outFile;
    void operator()(unsigned i) {
      outFile << i << '\t';
    }
    void operator()(const std::string &s) {
      outFile << s << '\t';
    }
  } printer{outFile};

  for (auto &entry : vals) {
    tuple_for_each(entry, printer);
    std::cout << '\n';
  }
}
