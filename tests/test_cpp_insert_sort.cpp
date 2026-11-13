/**
 * Comprehensive C++ verification test suite for insertion sort.
 *
 * Verifies standard insertion_sort and binary_insertion_sort across:
 * - Empty containers
 * - Single element containers
 * - Two elements (sorted, reversed, identical)
 * - All duplicates
 * - Already sorted sequences
 * - Strictly reverse-sorted sequences
 * - Random permutations (multiple seeds and sizes)
 * - Custom comparators (descending order, custom struct predicates)
 * - Stability preservation for equivalent keys
 * - Diverse iterator categories (vector, deque, list, raw array pointers)
 * - Move-only element types (std::unique_ptr)
 * - Container convenience overloads
 */

#include "insert_sort.hpp"
#include "binary_insert_sort.hpp"

#include <algorithm>
#include <chrono>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <memory>
#include <numeric>
#include <random>
#include <string>
#include <utility>
#include <vector>

namespace {

int g_total_tests = 0;
int g_passed_tests = 0;
int g_failed_tests = 0;

#define TEST_CASE(suite, name) \
    void test_##suite##_##name(); \
    struct runner_##suite##_##name { \
        runner_##suite##_##name() { \
            std::cout << "[ RUN      ] " #suite "." #name << "\n"; \
            ++g_total_tests; \
            bool test_ok = true; \
            try { \
                test_##suite##_##name(); \
                ++g_passed_tests; \
                std::cout << "[       OK ] " #suite "." #name << "\n"; \
            } catch (const std::exception& e) { \
                ++g_failed_tests; \
                std::cerr << "[  FAILED  ] " #suite "." #name << " with exception: " << e.what() << "\n"; \
            } catch (...) { \
                ++g_failed_tests; \
                std::cerr << "[  FAILED  ] " #suite "." #name << " with unknown exception\n"; \
            } \
        } \
    }; \
    void test_##suite##_##name()

#define EXPECT_TRUE(cond) \
    do { \
        if (!(cond)) { \
            std::cerr << "  Failure at " << __FILE__ << ":" << __LINE__ << ": expected " #cond "\n"; \
            throw std::runtime_error("Assertion failed: " #cond); \
        } \
    } while (0)

#define EXPECT_FALSE(cond) EXPECT_TRUE(!(cond))

#define EXPECT_EQ(val1, val2) \
    do { \
        if (!((val1) == (val2))) { \
            std::cerr << "  Failure at " << __FILE__ << ":" << __LINE__ << ": expected " #val1 " == " #val2 "\n"; \
            throw std::runtime_error("Assertion failed: " #val1 " == " #val2); \
        } \
    } while (0)

// Helper struct for stability verification
struct StableElement {
    int key;
    int original_index;

    bool operator==(const StableElement& other) const {
        return key == other.key && original_index == other.original_index;
    }
};

struct StableKeyCompare {
    bool operator()(const StableElement& a, const StableElement& b) const {
        return a.key < b.key;
    }
};

} // namespace

void run_all_tests() {
    // 1. Edge Case: Empty Container
    {
        std::cout << "[ RUN      ] EdgeCases.EmptyContainer" << "\n";
        ++g_total_tests;
        std::vector<int> empty_vec;
        insertion_sort(empty_vec.begin(), empty_vec.end());
        EXPECT_TRUE(empty_vec.empty());

        binary_insertion_sort(empty_vec.begin(), empty_vec.end());
        EXPECT_TRUE(empty_vec.empty());

        std::list<std::string> empty_list;
        insertion_sort(empty_list.begin(), empty_list.end());
        EXPECT_TRUE(empty_list.empty());

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.EmptyContainer" << "\n";
    }

    // 2. Edge Case: Single Element
    {
        std::cout << "[ RUN      ] EdgeCases.SingleElement" << "\n";
        ++g_total_tests;
        std::vector<int> single = {42};
        insertion_sort(single.begin(), single.end());
        EXPECT_EQ(single.size(), 1u);
        EXPECT_EQ(single[0], 42);

        binary_insertion_sort(single.begin(), single.end());
        EXPECT_EQ(single[0], 42);

        std::list<int> single_list = {99};
        insertion_sort(single_list.begin(), single_list.end());
        EXPECT_EQ(single_list.front(), 99);

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.SingleElement" << "\n";
    }

    // 3. Edge Case: Two Elements
    {
        std::cout << "[ RUN      ] EdgeCases.TwoElements" << "\n";
        ++g_total_tests;
        std::vector<int> sorted2 = {1, 2};
        insertion_sort(sorted2.begin(), sorted2.end());
        EXPECT_EQ(sorted2[0], 1);
        EXPECT_EQ(sorted2[1], 2);

        std::vector<int> reversed2 = {2, 1};
        insertion_sort(reversed2.begin(), reversed2.end());
        EXPECT_EQ(reversed2[0], 1);
        EXPECT_EQ(reversed2[1], 2);

        std::vector<int> equal2 = {3, 3};
        insertion_sort(equal2.begin(), equal2.end());
        EXPECT_EQ(equal2[0], 3);
        EXPECT_EQ(equal2[1], 3);

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.TwoElements" << "\n";
    }

    // 4. Edge Case: All Duplicates
    {
        std::cout << "[ RUN      ] EdgeCases.AllDuplicates" << "\n";
        ++g_total_tests;
        const size_t n = 128;
        std::vector<int> duplicates(n, 7);
        insertion_sort(duplicates.begin(), duplicates.end());
        EXPECT_EQ(duplicates.size(), n);
        for (int val : duplicates) {
            EXPECT_EQ(val, 7);
        }

        std::vector<int> bin_duplicates(n, 13);
        binary_insertion_sort(bin_duplicates.begin(), bin_duplicates.end());
        for (int val : bin_duplicates) {
            EXPECT_EQ(val, 13);
        }

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.AllDuplicates" << "\n";
    }

    // 5. Edge Case: Already Sorted
    {
        std::cout << "[ RUN      ] EdgeCases.AlreadySorted" << "\n";
        ++g_total_tests;
        const size_t n = 100;
        std::vector<int> sorted_data(n);
        std::iota(sorted_data.begin(), sorted_data.end(), 1);

        std::vector<int> copy1 = sorted_data;
        insertion_sort(copy1.begin(), copy1.end());
        EXPECT_TRUE(std::is_sorted(copy1.begin(), copy1.end()));
        EXPECT_EQ(copy1, sorted_data);

        std::vector<int> copy2 = sorted_data;
        binary_insertion_sort(copy2.begin(), copy2.end());
        EXPECT_TRUE(std::is_sorted(copy2.begin(), copy2.end()));
        EXPECT_EQ(copy2, sorted_data);

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.AlreadySorted" << "\n";
    }

    // 6. Edge Case: Strictly Reverse Sorted
    {
        std::cout << "[ RUN      ] EdgeCases.StrictlyReverseSorted" << "\n";
        ++g_total_tests;
        const size_t n = 100;
        std::vector<int> reverse_data(n);
        std::iota(reverse_data.begin(), reverse_data.end(), 1);
        std::reverse(reverse_data.begin(), reverse_data.end());

        std::vector<int> expected(n);
        std::iota(expected.begin(), expected.end(), 1);

        std::vector<int> copy1 = reverse_data;
        insertion_sort(copy1.begin(), copy1.end());
        EXPECT_TRUE(std::is_sorted(copy1.begin(), copy1.end()));
        EXPECT_EQ(copy1, expected);

        std::vector<int> copy2 = reverse_data;
        binary_insertion_sort(copy2.begin(), copy2.end());
        EXPECT_TRUE(std::is_sorted(copy2.begin(), copy2.end()));
        EXPECT_EQ(copy2, expected);

        ++g_passed_tests;
        std::cout << "[       OK ] EdgeCases.StrictlyReverseSorted" << "\n";
    }

    // 7. Random Permutations
    {
        std::cout << "[ RUN      ] SortingTests.RandomPermutations" << "\n";
        ++g_total_tests;
        std::mt19937 rng(42);
        const std::vector<size_t> test_sizes = {10, 25, 50, 100, 250};

        for (size_t size : test_sizes) {
            std::vector<int> data(size);
            std::iota(data.begin(), data.end(), 0);
            std::shuffle(data.begin(), data.end(), rng);

            std::vector<int> copy_std = data;
            std::vector<int> copy_bin = data;

            insertion_sort(copy_std.begin(), copy_std.end());
            EXPECT_TRUE(std::is_sorted(copy_std.begin(), copy_std.end()));

            binary_insertion_sort(copy_bin.begin(), copy_bin.end());
            EXPECT_TRUE(std::is_sorted(copy_bin.begin(), copy_bin.end()));

            EXPECT_EQ(copy_std, copy_bin);
        }

        ++g_passed_tests;
        std::cout << "[       OK ] SortingTests.RandomPermutations" << "\n";
    }

    // 8. Custom Comparators (Descending Order & Custom Types)
    {
        std::cout << "[ RUN      ] SortingTests.CustomComparators" << "\n";
        ++g_total_tests;
        std::vector<int> data = {3, 1, 4, 1, 5, 9, 2, 6, 5};
        insertion_sort(data.begin(), data.end(), std::greater<int>{});
        EXPECT_TRUE(std::is_sorted(data.begin(), data.end(), std::greater<int>{}));
        EXPECT_EQ(data.front(), 9);
        EXPECT_EQ(data.back(), 1);

        std::vector<std::string> strings = {"banana", "apple", "cherry", "date", "fig"};
        // Sort by length, then lexicographically
        auto length_comp = [](const std::string& a, const std::string& b) {
            if (a.length() != b.length()) {
                return a.length() < b.length();
            }
            return a < b;
        };
        insertion_sort(strings.begin(), strings.end(), length_comp);
        EXPECT_TRUE(std::is_sorted(strings.begin(), strings.end(), length_comp));
        EXPECT_EQ(strings.front(), "fig");
        EXPECT_EQ(strings.back(), "cherry");

        ++g_passed_tests;
        std::cout << "[       OK ] SortingTests.CustomComparators" << "\n";
    }

    // 9. Stability Verification
    {
        std::cout << "[ RUN      ] SortingTests.StabilityVerification" << "\n";
        ++g_total_tests;
        // Construct elements with repeating keys and track original insertion index
        std::vector<StableElement> elements = {
            {3, 0}, {1, 1}, {2, 2}, {3, 3}, {1, 4},
            {2, 5}, {3, 6}, {1, 7}, {2, 8}, {0, 9}
        };

        std::vector<StableElement> copy_std = elements;
        insertion_sort(copy_std.begin(), copy_std.end(), StableKeyCompare{});

        // Verify keys are in non-descending order
        for (size_t i = 1; i < copy_std.size(); ++i) {
            EXPECT_TRUE(copy_std[i - 1].key <= copy_std[i].key);
            // If keys are equal, original_index must be strictly increasing
            if (copy_std[i - 1].key == copy_std[i].key) {
                EXPECT_TRUE(copy_std[i - 1].original_index < copy_std[i].original_index);
            }
        }

        std::vector<StableElement> copy_bin = elements;
        binary_insertion_sort(copy_bin.begin(), copy_bin.end(), StableKeyCompare{});
        for (size_t i = 1; i < copy_bin.size(); ++i) {
            EXPECT_TRUE(copy_bin[i - 1].key <= copy_bin[i].key);
            if (copy_bin[i - 1].key == copy_bin[i].key) {
                EXPECT_TRUE(copy_bin[i - 1].original_index < copy_bin[i].original_index);
            }
        }

        ++g_passed_tests;
        std::cout << "[       OK ] SortingTests.StabilityVerification" << "\n";
    }

    // 10. Diverse Iterator Categories (Deque, List, Raw Array)
    {
        std::cout << "[ RUN      ] IteratorSupport.DiverseContainers" << "\n";
        ++g_total_tests;

        // std::deque (Random Access)
        std::deque<int> deq = {9, 3, 7, 1, 5, 2, 8, 4, 6};
        insertion_sort(deq.begin(), deq.end());
        EXPECT_TRUE(std::is_sorted(deq.begin(), deq.end()));

        // std::list (Bidirectional)
        std::list<int> lst = {9, 3, 7, 1, 5, 2, 8, 4, 6};
        insertion_sort(lst.begin(), lst.end());
        EXPECT_TRUE(std::is_sorted(lst.begin(), lst.end()));

        // Raw array pointers
        int raw_arr[] = {10, -5, 20, 0, 15, -10};
        const size_t raw_size = sizeof(raw_arr) / sizeof(raw_arr[0]);
        insertion_sort(raw_arr, raw_arr + raw_size);
        EXPECT_TRUE(std::is_sorted(raw_arr, raw_arr + raw_size));

        ++g_passed_tests;
        std::cout << "[       OK ] IteratorSupport.DiverseContainers" << "\n";
    }

    // 11. Move-Only Types (std::unique_ptr)
    {
        std::cout << "[ RUN      ] TypeSupport.MoveOnlyElements" << "\n";
        ++g_total_tests;
        std::vector<std::unique_ptr<int>> ptrs;
        ptrs.push_back(std::make_unique<int>(50));
        ptrs.push_back(std::make_unique<int>(10));
        ptrs.push_back(std::make_unique<int>(30));
        ptrs.push_back(std::make_unique<int>(20));
        ptrs.push_back(std::make_unique<int>(40));

        auto deref_comp = [](const std::unique_ptr<int>& a, const std::unique_ptr<int>& b) {
            return *a < *b;
        };

        insertion_sort(ptrs.begin(), ptrs.end(), deref_comp);

        EXPECT_EQ(*ptrs[0], 10);
        EXPECT_EQ(*ptrs[1], 20);
        EXPECT_EQ(*ptrs[2], 30);
        EXPECT_EQ(*ptrs[3], 40);
        EXPECT_EQ(*ptrs[4], 50);

        ++g_passed_tests;
        std::cout << "[       OK ] TypeSupport.MoveOnlyElements" << "\n";
    }

    // 12. Container Convenience Overloads
    {
        std::cout << "[ RUN      ] Interface.ContainerOverloads" << "\n";
        ++g_total_tests;
        std::vector<int> vec = {5, 2, 8, 1, 9};
        insertion_sort(vec);
        EXPECT_TRUE(std::is_sorted(vec.begin(), vec.end()));

        std::vector<int> vec_desc = {5, 2, 8, 1, 9};
        insertion_sort(vec_desc, std::greater<int>{});
        EXPECT_TRUE(std::is_sorted(vec_desc.begin(), vec_desc.end(), std::greater<int>{}));

        std::vector<int> bin_vec = {7, 3, 1, 4, 2};
        binary_insertion_sort(bin_vec);
        EXPECT_TRUE(std::is_sorted(bin_vec.begin(), bin_vec.end()));

        ++g_passed_tests;
        std::cout << "[       OK ] Interface.ContainerOverloads" << "\n";
    }

    // 13. Binary Insertion Sort Comparison Count and Stability
    {
        std::cout << "[ RUN      ] BinaryInsertSort.ComparisonCountAndStability\n";
        ++g_total_tests;

        // Bounded comparison count on random sequence of size 100
        std::vector<int> data(100);
        std::iota(data.begin(), data.end(), 1);
        std::mt19937 g(12345);
        std::shuffle(data.begin(), data.end(), g);

        std::size_t comparisons = binary_insertion_sort_counted(data);
        EXPECT_TRUE(std::is_sorted(data.begin(), data.end()));
        EXPECT_TRUE(comparisons <= 600);

        // Stability test with duplicate keys
        std::vector<StableElement> elements = {
            {2, 0}, {1, 1}, {2, 2}, {1, 3}, {2, 4}, {3, 5}
        };
        binary_insertion_sort_counted(elements, StableKeyCompare{});
        std::vector<StableElement> expected = {
            {1, 1}, {1, 3}, {2, 0}, {2, 2}, {2, 4}, {3, 5}
        };
        EXPECT_EQ(elements, expected);

        ++g_passed_tests;
        std::cout << "[       OK ] BinaryInsertSort.ComparisonCountAndStability\n";
    }
}

int main() {
    std::cout << "[==========] Running C++ insertion sort verification test suite.\n";
    auto start_time = std::chrono::steady_clock::now();

    try {
        run_all_tests();
    } catch (const std::exception& e) {
        std::cerr << "Fatal unhandled exception in test suite: " << e.what() << "\n";
        return 1;
    } catch (...) {
        std::cerr << "Fatal unknown exception in test suite.\n";
        return 1;
    }

    auto end_time = std::chrono::steady_clock::now();
    auto elapsed_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();

    std::cout << "[==========] " << g_total_tests << " tests ran. (" << elapsed_ms << " ms total)\n";
    std::cout << "[  PASSED  ] " << g_passed_tests << " tests.\n";

    if (g_failed_tests > 0) {
        std::cerr << "[  FAILED  ] " << g_failed_tests << " tests.\n";
        return 1;
    }

    return 0;
}
