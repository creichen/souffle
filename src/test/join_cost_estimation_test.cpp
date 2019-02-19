#include "FuncChecksCommon.h"
#include "test.h"

namespace souffle {
namespace test {
class DummyCostModel {
  const std::vector<rel_size_t> &relSize;
  const std::vector<rel_size_t> &selectivity;

public:
  DummyCostModel(const std::vector<rel_size_t> &size,
                 const std::vector<rel_size_t> &selectivity) :
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

static std::tuple<std::vector<unsigned>,
                  rel_size_t /* join result size*/,
                  float /* join cost */>
getOptJoinOrder(const std::vector<rel_size_t> &size,
                const std::vector<rel_size_t> &selectivity) {
  DummyCostModel m(size, selectivity);
  JoinOrderOptimizer<DummyCostModel>::bitset joinedRels(size.size(), 0);
  joinedRels.set(0, size.size(), true);
  JoinOrderOptimizer<DummyCostModel> opt(m);
  auto revOrder = opt.getReverseJoinOrder(joinedRels);
  std::vector<unsigned> joinOrder(revOrder.rbegin(), revOrder.rend());
  auto cost_size = opt.computeCost(joinedRels);
  return std::make_tuple(joinOrder, cost_size.second, cost_size.first);
}

/**
   Test the trivial case: a join with a single relation
 */
TEST(JoinCostEstimation, JoinOrder1Rels) {
  std::vector<rel_size_t> size {123};
  std::vector<rel_size_t> selectivity {123};

  auto joinOrder = getOptJoinOrder(size, selectivity);

  EXPECT_EQ(std::get<0>(joinOrder).size(), 1);
  EXPECT_EQ(std::get<0>(joinOrder)[0], 0);
}


/**
   Test the simple case: a join with two relations
 */
TEST(JoinCostEstimation, JoinOrder2Rels) {
  std::vector<rel_size_t> size {10, 100};
  std::vector<rel_size_t> selectivity {10, 10};



  auto joinOrder = getOptJoinOrder(size, selectivity);

  EXPECT_EQ(std::get<0>(joinOrder)[0], 0);
  EXPECT_EQ(std::get<0>(joinOrder)[1], 1);
}

/**
   Test a join of 3 relations with size 100, 1000, 1000 and
   selectivities 10, 100, 1000
 */
TEST(JoinCostEstimation, JoinOrder3Rels) {
  std::vector<rel_size_t> size {100, 1000, 1000};
  std::vector<rel_size_t> selectivity {10, 100, 1000};

  auto joinOrderAndCost = getOptJoinOrder(size, selectivity);
  EXPECT_EQ(std::get<1>(joinOrderAndCost), 1000);
  // Expect the cost to be about 100 * log2(1000)
  EXPECT_LT(100 * std::log2(1000) - 1, std::get<2>(joinOrderAndCost));
  EXPECT_LT(std::get<2>(joinOrderAndCost), 100 * std::log2(1000) + 1);

  const auto &joinOrder = std::get<0>(joinOrderAndCost);
  EXPECT_EQ(joinOrder[0], 0);
  EXPECT_EQ(joinOrder[1], 2);
  EXPECT_EQ(joinOrder[2], 1);
}

/**
   Validate the join info of 3 relations with sizes 100, 1000, 1000 and
   selectivities 10, 100, 1000
 */
TEST(JoinCostEstimation, JoinInfo) {
  std::vector<rel_size_t> size {100, 1000, 1000};
  std::vector<rel_size_t> selectivity {10, 100, 1000};
  DummyCostModel m(size, selectivity);
  JoinOrderOptimizer<DummyCostModel>::bitset joinedRels(size.size(), 0);
  joinedRels.set(0, size.size(), true);
  JoinOrderOptimizer<DummyCostModel> opt(m);
  auto revOrder = opt.getReverseJoinInfo(joinedRels);

  EXPECT_EQ(revOrder[0].pred.to_ulong(), 0x5);
  EXPECT_EQ(revOrder[0].size, 1000);
  EXPECT_EPS(revOrder[0].cost, 100 * std::log2(1000), 1.0);

  EXPECT_EQ(revOrder[1].pred.to_ulong(), 0x1);
  EXPECT_EQ(revOrder[1].size, 100);
  EXPECT_EPS(revOrder[1].cost, 100 * std::log2(1000), 1.0);

  EXPECT_EQ(revOrder[2].pred.to_ulong(), 0);
  EXPECT_EQ(revOrder[2].size, 100);
  EXPECT_EQ(revOrder[2].cost, 0);

}
}
}
