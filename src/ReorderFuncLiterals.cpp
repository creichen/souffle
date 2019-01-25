#include "AstTransforms.h"
#include "Global.h"
#include "FuncChecksCommon.h"

#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/directed_graph.hpp>
#include <boost/algorithm/string.hpp>
#include <fstream>

using namespace souffle;

using EdgeNameT = boost::property<boost::edge_name_t, std::string>;

using Graph = boost::directed_graph<
  std::string,
  EdgeNameT>;

class FuncLiteralOpt {
  AstTranslationUnit &tu;
  std::multimap<std::string, FunctionalRelationDesc> funcRels;
public:
  FuncLiteralOpt(AstTranslationUnit &tu,
                 std::multimap<std::string, FunctionalRelationDesc> &&funcRels)
    : tu(tu), funcRels(std::move(funcRels)) {}

  bool handleClause(AstClause &cls);
  bool handleRelation(AstRelation &rel) {
    for (auto *cls : rel.getClauses()) {
      handleClause(*cls);
    }
    return false;
  }
  bool run() {
    for (auto *rel : tu.getProgram()->getRelations())
      handleRelation(*rel);
    return false;
  }
};



bool FuncLiteralOpt::handleClause(AstClause &cls) {
  Graph g;

  std::map<std::string, Graph::vertex_descriptor> nameToVertex;

  auto getVertex = [&g, &nameToVertex] (const std::string &name) -> Graph::vertex_descriptor {
    auto it = nameToVertex.find(name);
    if (it == nameToVertex.end()) {
      auto v = boost::add_vertex(name, g);
      std::tie(it, std::ignore) = nameToVertex.insert(std::make_pair(name, v));
    }
    return it->second;
  };


  for (auto *atom : cls.getAtoms()) {
    auto range = funcRels.equal_range(atom->getName().getName());
    if (range.first == range.second)
      continue;
    // this atom is a functional relation
    for (auto it = range.first; it != range.second; ++it) {
      AstVariable *dst = dynamic_cast<AstVariable*>(atom->getArgument(it->second.second));
      if (!dst)
        continue;

      auto dstV = getVertex(dst->getName());

      for (auto srcIdx : it->second.first) {
        auto *src = dynamic_cast<AstVariable*>(atom->getArgument(srcIdx));
        if (!src)
          continue;

        auto srcV = getVertex(src->getName());
        EdgeNameT edgeName = atom->getName().getName();
        boost::add_edge(srcV, dstV, edgeName, g);
      }
    }
  }

  // Write out the graph
  DEBUG(
    static unsigned print_count = 0;

    struct {
      Graph &g;

      std::string sanitize(const std::string &s) {
        return boost::algorithm::replace_all_copy(s, "?", "_");
      }

      void operator()(std::ostream &os, Graph::edge_descriptor e) {
        auto pmap = boost::get(boost::edge_name_t(), g);
        os << "[label=" << sanitize(pmap[e]) << "]";
      }
    } wpe{g};

    struct {
      Graph &g;
      std::string sanitize(const std::string &s) {
        return boost::algorithm::replace_all_copy(s, "?", "_");
      }

      void operator()(std::ostream &os, Graph::vertex_descriptor v) {
        os << " [label=" << sanitize(g[v]) << "]" ;
      }
    } wpv{g};


    if (g.num_vertices() > 2) {
      auto gFile = std::ofstream(cls.getHead()->getName().getName() + "_" + std::to_string(print_count++) + ".gv");
      gFile << "/*\n";
      cls.print(gFile);
      gFile << "\n*/\n";
      boost::write_graphviz(gFile, g, wpv, wpe);
    }
    );
  return false;
}

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

    relMap.emplace(relName, desc);
  }

  return relMap;
}

bool ReorderFuncLiteralsTransformer::transform(AstTranslationUnit &translationUnit) {
  if (!Global::config().has("func-opt"))
    return false;

  auto funcRelMap = readFuncRelInfo(Global::config().get("func-opt"));

  DEBUG(
     for (auto &entry : funcRelMap) {
       std::cout << entry.first << " : " << entry.second << "\n";
     }
    );

  FuncLiteralOpt fopt(translationUnit, std::move(funcRelMap));
  fopt.run();

  return false;
}
