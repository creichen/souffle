#pragma once

#include <set>
#include <utility>
#include <numeric>

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
