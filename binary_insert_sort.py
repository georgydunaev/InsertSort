#!/usr/bin/env python3
"""Binary Insertion Sort optimization with bisect insertion point search.

This module provides verified, stable binary insertion sort routines supporting:
- O(n log n) comparison count via bisect-right binary search
- Strict stability preservation by placing duplicates after existing equal keys
- Generic key extractors, custom comparators, and reverse ordering
- Comparison count tracking for theoretical and empirical verification
- Both out-of-place and in-place sorting routines

Doctests:
>>> binary_insertion_sort([3, 1, 4, 1, 5, 9, 2, 6, 5])
[1, 1, 2, 3, 4, 5, 5, 6, 9]

>>> binary_insertion_sort([5, 4, 3, 2, 1])
[1, 2, 3, 4, 5]

>>> binary_insertion_sort([1, 2, 3, 4, 5], reverse=True)
[5, 4, 3, 2, 1]

>>> binary_insertion_sort([])
[]

>>> binary_insertion_sort([42])
[42]

>>> records = [(2, 'alpha'), (1, 'beta'), (2, 'gamma'), (1, 'delta')]
>>> binary_insertion_sort(records, key=lambda x: x[0])
[(1, 'beta'), (1, 'delta'), (2, 'alpha'), (2, 'gamma')]

>>> sorted_items, count = binary_insertion_sort_counted([5, 2, 4, 6, 1, 3])
>>> sorted_items
[1, 2, 3, 4, 5, 6]
>>> count <= 15
True
"""

from typing import Any, Callable, List, Optional, Sequence, Tuple, TypeVar

T = TypeVar("T")


def _compare_values(
    val_a: Any,
    val_b: Any,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
) -> bool:
    """Return True if val_a is strictly less than val_b according to cmp."""
    if cmp is not None:
        res = cmp(val_a, val_b)
        if isinstance(res, bool):
            return res
        return res < 0
    return val_a < val_b


def bisect_right_search(
    seq: Sequence[T],
    item: T,
    low: int = 0,
    high: Optional[int] = None,
    key: Optional[Callable[[T], Any]] = None,
    reverse: bool = False,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
    counter: Optional[List[int]] = None,
) -> int:
    """Locate the insertion index for item in sorted sequence range [low, high).

    Uses binary search to find the insertion point in O(log n) comparisons.
    Preserves stability by returning an index strictly after any existing equal keys.

    Parameters:
        seq: Sorted sequence or prefix.
        item: Element to insert.
        low: Lower bound index of the search range.
        high: Upper bound index (exclusive). Defaults to len(seq).
        key: Optional key extraction function.
        reverse: If True, search assuming descending order; otherwise ascending.
        cmp: Optional custom comparator.
        counter: Optional single-element list [count] incremented on each comparison.

    Returns:
        Index at which item should be inserted.
    """
    if high is None:
        high = len(seq)

    item_key = key(item) if key is not None else item

    while low < high:
        mid = (low + high) // 2
        mid_elem = seq[mid]
        mid_key = key(mid_elem) if key is not None else mid_elem

        if counter is not None:
            counter[0] += 1

        if not reverse:
            # Ascending: to insert after equals, test if item < mid_elem.
            # If item < mid_elem, item must be placed at or before mid.
            # Otherwise (mid_elem <= item), item must be placed after mid.
            if _compare_values(item_key, mid_key, cmp=cmp):
                high = mid
            else:
                low = mid + 1
        else:
            # Descending: to insert after equals, test if mid_elem < item.
            # If mid_elem < item, item must be placed before mid.
            # Otherwise (mid_elem >= item), item must be placed after mid.
            if _compare_values(mid_key, item_key, cmp=cmp):
                high = mid
            else:
                low = mid + 1

    return low


def binary_insertion_sort(
    seq: Sequence[T],
    key: Optional[Callable[[T], Any]] = None,
    reverse: bool = False,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
) -> List[T]:
    """Sort sequence seq using verified stable binary insertion sort.

    Parameters:
        seq: Input sequence of elements.
        key: Function to extract comparison key for each element.
        reverse: If True, sort in descending order; otherwise ascending.
        cmp: Optional custom comparator.

    Returns:
        A new list containing the sorted elements in stable order.
    """
    result: List[T] = []
    for item in seq:
        idx = bisect_right_search(
            result,
            item,
            low=0,
            high=len(result),
            key=key,
            reverse=reverse,
            cmp=cmp,
        )
        result.insert(idx, item)
    return result


def binary_insertion_sort_counted(
    seq: Sequence[T],
    key: Optional[Callable[[T], Any]] = None,
    reverse: bool = False,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
) -> Tuple[List[T], int]:
    """Sort sequence seq with binary insertion sort and count comparisons.

    Returns:
        A tuple of (sorted_list, comparison_count).
    """
    counter = [0]
    result: List[T] = []
    for item in seq:
        idx = bisect_right_search(
            result,
            item,
            low=0,
            high=len(result),
            key=key,
            reverse=reverse,
            cmp=cmp,
            counter=counter,
        )
        result.insert(idx, item)
    return result, counter[0]


def binary_insertion_sort_inplace(
    lst: List[T],
    key: Optional[Callable[[T], Any]] = None,
    reverse: bool = False,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
) -> int:
    """Sort list lst in-place using binary insertion sort.

    Returns:
        Total number of key/element comparisons performed.
    """
    counter = [0]
    n = len(lst)
    for i in range(1, n):
        item = lst[i]
        idx = bisect_right_search(
            lst,
            item,
            low=0,
            high=i,
            key=key,
            reverse=reverse,
            cmp=cmp,
            counter=counter,
        )
        if idx < i:
            lst[idx + 1 : i + 1] = lst[idx:i]
            lst[idx] = item
    return counter[0]


def linear_insertion_sort_counted(
    seq: Sequence[T],
    key: Optional[Callable[[T], Any]] = None,
    reverse: bool = False,
    cmp: Optional[Callable[[Any, Any], Any]] = None,
) -> Tuple[List[T], int]:
    """Sort sequence seq using standard linear insertion sort with comparison count.

    Used for comparing O(n^2) linear comparisons against O(n log n) binary comparisons.

    Returns:
        A tuple of (sorted_list, comparison_count).
    """
    counter = [0]
    result: List[T] = []

    for item in seq:
        item_key = key(item) if key is not None else item
        inserted = False
        for i in range(len(result)):
            existing_key = key(result[i]) if key is not None else result[i]
            counter[0] += 1
            if not reverse:
                if _compare_values(item_key, existing_key, cmp=cmp):
                    result.insert(i, item)
                    inserted = True
                    break
            else:
                if _compare_values(existing_key, item_key, cmp=cmp):
                    result.insert(i, item)
                    inserted = True
                    break
        if not inserted:
            result.append(item)

    return result, counter[0]


if __name__ == "__main__":
    import doctest

    results = doctest.testmod()
    print(f"Doctest results: {results.failed} failures out of {results.attempted} tests.")
