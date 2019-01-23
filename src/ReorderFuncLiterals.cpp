#include "AstTransforms.h"
#include "Global.h"
#include "FuncChecksCommon.h"

#include <boost/graph/graph_traits.hpp>
#include <fstream>

using namespace souffle;

std::ostream& operator<<(std::ostream& os, const FunctionalRelationDesc &fr) {
  os << "[";
  for (auto it = fr.first.begin(), end = fr.first.end(); it != end; ++it) {
    os << *it;
    if (std::next(it) != end) {
      os << ", ";
    }
  }
  os << "] -> " << fr.second;
  return os;
}

std::multimap<std::string, FunctionalRelationDesc> readFuncRelInfo(const std::string &csvFileName) {
  auto csvFile = std::ifstream(csvFileName);

  std::multimap<std::string, FunctionalRelationDesc> relMap;

  while (!csvFile.eof()) {
    std::stringstream ss;
    // extract the relation name
    csvFile.get(*ss.rdbuf(), '\t');
    std::string relName = ss.str();

    if (relName.empty())
      continue;

    // 'parse' the source and the targets
    std::stringstream ss2;
    csvFile.get(*ss2.rdbuf());

    FunctionalRelationDesc desc;
    unsigned i = 0;
    for (auto c : ss2.str()) {
      if (c == 'S')
        desc.first.insert(i);
      else if (c == 'T')
        desc.second = i;

      if (c == 'X' || c == 'T' || c == 'S')
        i++;
    }

    // consume the newline
    csvFile.seekg(1, std::ios_base::cur);
    std::cout << relName << " : " << desc << "\n";

    relMap.emplace(relName, desc);
  }

  return relMap;
}

bool ReorderFuncLiteralsTransformer::transform(AstTranslationUnit &translationUnint) {
  if (!Global::config().has("func-opt"))
    return false;

  auto funcRelMap = readFuncRelInfo(Global::config().get("func-opt"));

  // DEBUG(
  //   for (auto &entry : funcRelMap) {
  //     std::cout << entry.first << " : " << entry.second << "\n";
  //   }
  //   );

  return false;
}
