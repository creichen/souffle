#include "FuncChecksCommon.h"
#include "test.h"

namespace souffle {
namespace test {
class DummyCostModel {
  const std::vector<rel_size_t> &relSize;
  const std::vector<rel_size_t> &selectivity;

public:
  DummyCostModel(std::vector<rel_size_t> &size,
                 std::vector<rel_size_t> &selectivity) :
    relSize(size), selectivity(selectivity) {}

  rel_size_t relationSize(unsigned i) const {
    return relSize[i];
  }

  rel_size_t joinSize(const std::vector<unsigned> &joinAtoms) const {
    std::vector<rel_size_t> sels;
    for (auto j : joinAtoms)
      sels.push_back(selectivity[j]);

    std::sort(sels.begin(), sels.end());
    auto selP = std::accumulate(std::next(sels.begin()), sels.end(), 1.0,
                                std::multiplies<double>());
    auto sizeP = std::accumulate(joinAtoms.begin(), joinAtoms.end(), 1.0,
                                 [this](double f, unsigned i){
                                   return f * relationSize(i);
                                 });
    auto r = sizeP / selP;

    return r;
  }
};

TEST(JoinCostEstimation, JoinOrder1Rels) {
  std::vector<rel_size_t> size {123};
  std::vector<rel_size_t> selectivity {123};

  DummyCostModel m(size, selectivity);
  JoinOrderOptimizer<DummyCostModel>::bitset joinedRels(size.size(), 0);
  joinedRels.set(0, size.size(), true);
  JoinOrderOptimizer<DummyCostModel> opt(m);
  auto revOrder = opt.getReverseJoinOrder(joinedRels);
  std::vector<unsigned> joinOrder(revOrder.rbegin(), revOrder.rend());

  EXPECT_EQ(joinOrder.size(), 1);
  EXPECT_EQ(joinOrder[0], 0);
}


TEST(JoinCostEstimation, JoinOrder2Rels) {
  std::vector<rel_size_t> size {10, 100};
  std::vector<rel_size_t> selectivity {10, 10};

  DummyCostModel m(size, selectivity);
  JoinOrderOptimizer<DummyCostModel>::bitset joinedRels(size.size(), 0);
  joinedRels.set(0, size.size(), true);
  JoinOrderOptimizer<DummyCostModel> opt(m);
  auto revOrder = opt.getReverseJoinOrder(joinedRels);
  std::vector<unsigned> joinOrder(revOrder.rbegin(), revOrder.rend());

  EXPECT_EQ(joinOrder[0], 0);
  EXPECT_EQ(joinOrder[1], 1);
}


}
}
