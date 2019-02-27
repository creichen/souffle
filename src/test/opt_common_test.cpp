#include "FuncChecksCommon.h"
#include "test.h"

#include <vector>
#include <iterator>

namespace souffle {
namespace test {

static unsigned nChooseK(unsigned n, unsigned k) {
  if (k == 0 || k == n)
    return 1;
  return nChooseK(n - 1, k - 1) + nChooseK(n - 1, k);
}

/*
   Verify that choosing 2 out of 3 from a range produces
   the expected iterators and result size.
 */
TEST(OptCommon, choose2from3) {
  std::array<unsigned, 3> v;
  std::iota(v.begin(), v.end(), 10);

  std::vector<std::vector<unsigned>> result;
  auto choose2from3 = make_choose_gen(v.begin(), v.end(), 2);

  do {
    EXPECT_EQ(std::distance(choose2from3.begin(), choose2from3.end()), 2);
    std::vector<unsigned> tmp;
    for (auto it = choose2from3.begin(), end = choose2from3.end(); it != end; ++it) {
      tmp.push_back(**it);
    }
    result.emplace_back(std::move(tmp));
  } while(choose2from3.next());

  EXPECT_EQ(result.size(), nChooseK(3, 2));
  std::vector<std::vector<unsigned>> expected{{10, 11}, {10, 12}, {11, 12}};
  EXPECT_EQ(result, expected);
}

/*
   Verify that choosing 2 out of 3 from an integer range
   generates the correct values
 */
TEST(OptCommon, choose2from3int) {
  std::vector<std::vector<unsigned>> result;
  auto choose2from3 = make_choose_gen(10, 13, 2);

  do {
    EXPECT_EQ(std::distance(choose2from3.begin(), choose2from3.end()), 2);
    std::vector<unsigned> tmp;
    for (auto it = choose2from3.begin(), end = choose2from3.end(); it != end; ++it) {
      tmp.push_back(*it);
    }
    result.emplace_back(std::move(tmp));
  } while(choose2from3.next());

  EXPECT_EQ(result.size(), nChooseK(3, 2));
  std::vector<std::vector<unsigned>> expected{{10, 11}, {10, 12}, {11, 12}};
  EXPECT_EQ(result, expected);
}

TEST(OptCommon, choose0from3int) {
  std::vector<std::vector<unsigned>> result;
  auto choose0from3 = make_choose_gen(10, 13, 0);

  do {
    std::vector<unsigned> tmp;
    for (auto it = choose0from3.begin(), end = choose0from3.end(); it != end; ++it) {
      tmp.push_back(*it);
    }
    result.emplace_back(std::move(tmp));
  } while(choose0from3.next());

  EXPECT_EQ(result.size(), nChooseK(3, 0));
  std::vector<std::vector<unsigned>> expected{{}};
  EXPECT_EQ(result, expected);
}


TEST(OptCommon, choose5from5int) {
  std::vector<std::vector<int>> result;
  auto choose5from5 = make_choose_gen(-2, 3, 5);

  do {
    std::vector<int> tmp;
    for (auto it = choose5from5.begin(), end = choose5from5.end(); it != end; ++it) {
      tmp.push_back(*it);
    }
    result.emplace_back(std::move(tmp));
  } while(choose5from5.next());

  EXPECT_EQ(result.size(), nChooseK(5, 5));
  std::vector<std::vector<int>> expected{{-2, -1, 0, 1, 2}};
  EXPECT_EQ(result, expected);
}

/**
   Verify that for a range of length n all the 2^n subsets of iterators
   pointing insided that range are generated.
 */
TEST(OptCommon, subset3) {
  std::array<unsigned, 3> v;
  std::iota(v.begin(), v.end(), 10);
  std::vector<std::vector<unsigned>> result;
  auto subset3 = make_subset_gen(v.begin(), v.end(), 0);
  do {
    std::vector<unsigned> tmp;
    for (auto it = subset3.begin(), end = subset3.end(); it != end; ++it) {
      tmp.push_back(**it);
    }
    result.emplace_back(std::move(tmp));
  } while(subset3.next());

  EXPECT_EQ(result.size(), 8);
  std::vector<std::vector<unsigned>> expected{
    {}, {10}, {11}, {12},
    {10, 11}, {10, 12}, {11, 12}, {10, 11, 12}};
  EXPECT_EQ(result, expected);
}

/**
   Verify that subset generation works with integer ranges
 */
TEST(OptCommon, subset3int) {
  auto subset3 = make_subset_gen(0, 3, 1 /*exclude the empty subset*/);
  std::vector<std::vector<unsigned>> result;

  do {
    std::vector<unsigned> tmp;
    for (auto it = subset3.begin(), end = subset3.end(); it != end; ++it) {
      tmp.push_back(*it);
    }
    result.emplace_back(std::move(tmp));
  } while(subset3.next());

  EXPECT_EQ(result.size(), 7);
  std::vector<std::vector<unsigned>> expected{
                {0}, {1}, {2},
                {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}};
  EXPECT_EQ(result, expected);
}

} // namespace test
} // namespace souffle
