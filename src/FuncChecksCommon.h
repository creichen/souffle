#pragma once

#include <set>
#include <utility>

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
