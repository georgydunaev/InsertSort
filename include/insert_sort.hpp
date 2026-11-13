#ifndef INSERT_SORT_HPP
#define INSERT_SORT_HPP

#include "binary_insert_sort.hpp"

#include <algorithm>
#include <functional>
#include <iterator>
#include <utility>

namespace insert_sort {

/**
 * Generic insertion sort algorithm for bidirectional or random-access iterators.
 *
 * Sorts the elements in range [first, last) into non-descending order according
 * to the comparator comp. Stable sort: preserves relative order of equivalent elements.
 *
 * Complexity:
 * - Best case: O(n) comparisons when elements are already sorted.
 * - Worst case: O(n^2) comparisons and moves when elements are reverse-sorted.
 * - Average case: O(n^2) comparisons and moves.
 * - Space complexity: O(1) auxiliary space.
 */
template <typename BidirIt, typename Compare = std::less<>>
void insertion_sort(BidirIt first, BidirIt last, Compare comp = Compare{}) {
    if (first == last) {
        return;
    }

    for (BidirIt cur = std::next(first); cur != last; ++cur) {
        auto val = std::move(*cur);
        BidirIt hole = cur;
        while (hole != first) {
            BidirIt prev = std::prev(hole);
            if (comp(val, *prev)) {
                *hole = std::move(*prev);
                hole = prev;
            } else {
                break;
            }
        }
        *hole = std::move(val);
    }
}

/**
 * Container overload for standard insertion sort.
 */
template <typename Container, typename Compare = std::less<>>
void insertion_sort(Container& container, Compare comp = Compare{}) {
    using std::begin;
    using std::end;
    insertion_sort(begin(container), end(container), comp);
}

} // namespace insert_sort

// Bring into global namespace for standard usage
using insert_sort::insertion_sort;
using insert_sort::binary_insertion_sort;
using insert_sort::binary_insertion_sort_counted;

#endif // INSERT_SORT_HPP
