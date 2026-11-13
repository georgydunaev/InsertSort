#ifndef BINARY_INSERT_SORT_HPP
#define BINARY_INSERT_SORT_HPP

#include <algorithm>
#include <cstddef>
#include <functional>
#include <iterator>
#include <utility>

namespace insert_sort {

/**
 * Comparison counting wrapper to track comparison complexity.
 */
template <typename Compare>
class CountingCompare {
public:
    explicit CountingCompare(Compare comp) : comp_(comp), count_(0) {}

    template <typename T, typename U>
    bool operator()(const T& a, const U& b) {
        ++count_;
        return comp_(a, b);
    }

    std::size_t count() const noexcept {
        return count_;
    }

private:
    Compare comp_;
    std::size_t count_;
};

/**
 * Binary insertion sort algorithm for random-access iterators with comparison tracking.
 *
 * Employs bisect right binary search (via std::upper_bound) to locate target
 * insertion points in O(log n) comparisons per element, achieving O(n log n)
 * comparisons overall while maintaining strict stability.
 *
 * Returns total number of comparisons performed.
 */
template <typename RandomIt, typename Compare = std::less<>>
std::size_t binary_insertion_sort_counted(RandomIt first, RandomIt last, Compare comp = Compare{}) {
    if (first == last) {
        return 0;
    }

    CountingCompare<Compare> counted_comp(comp);

    for (RandomIt cur = std::next(first); cur != last; ++cur) {
        auto val = std::move(*cur);
        RandomIt insert_pos = std::upper_bound(first, cur, val, std::ref(counted_comp));
        for (RandomIt hole = cur; hole != insert_pos; --hole) {
            *hole = std::move(*(hole - 1));
        }
        *insert_pos = std::move(val);
    }

    return counted_comp.count();
}

/**
 * Container overload for binary insertion sort with comparison counting.
 */
template <typename Container, typename Compare = std::less<>>
std::size_t binary_insertion_sort_counted(Container& container, Compare comp = Compare{}) {
    using std::begin;
    using std::end;
    return binary_insertion_sort_counted(begin(container), end(container), comp);
}

/**
 * Binary insertion sort algorithm for random-access iterators.
 *
 * Employs bisect right search to determine target insertion position
 * in O(log n) comparisons per element, for a total of O(n log n) comparisons.
 * Preserves stability by inserting after equivalent elements.
 */
template <typename RandomIt, typename Compare = std::less<>>
void binary_insertion_sort(RandomIt first, RandomIt last, Compare comp = Compare{}) {
    if (first == last) {
        return;
    }

    for (RandomIt cur = std::next(first); cur != last; ++cur) {
        auto val = std::move(*cur);
        RandomIt insert_pos = std::upper_bound(first, cur, val, comp);
        for (RandomIt hole = cur; hole != insert_pos; --hole) {
            *hole = std::move(*(hole - 1));
        }
        *insert_pos = std::move(val);
    }
}

/**
 * Container overload for binary insertion sort.
 */
template <typename Container, typename Compare = std::less<>>
void binary_insertion_sort(Container& container, Compare comp = Compare{}) {
    using std::begin;
    using std::end;
    binary_insertion_sort(begin(container), end(container), comp);
}

} // namespace insert_sort

using insert_sort::binary_insertion_sort;
using insert_sort::binary_insertion_sort_counted;

#endif // BINARY_INSERT_SORT_HPP
