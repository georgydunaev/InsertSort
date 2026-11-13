#!/usr/bin/env python3
"""Verified reference implementation of insertion sort in Python.

This module provides verified, stable insertion sort routines supporting:
- Generic sequence sorting with custom key extractors
- Ascending and descending orders (reverse=False / True)
- Standard linear insertion sort O(n^2) worst-case, O(n) best-case
- Binary insertion sort using bisect for reduced comparisons O(n log n) comparisons
- Stable sorting preservation of relative order for elements with equal keys

Doctests:
>>> insertion_sort([3, 1, 4, 1, 5, 9, 2, 6, 5])
[1, 1, 2, 3, 4, 5, 5, 6, 9]

>>> insertion_sort([5, 4, 3, 2, 1])
[1, 2, 3, 4, 5]

>>> insertion_sort([1, 2, 3, 4, 5], reverse=True)
[5, 4, 3, 2, 1]

>>> insertion_sort([])
[]

>>> insertion_sort([42])
[42]

>>> records = [(2, 'alpha'), (1, 'beta'), (2, 'gamma'), (1, 'delta')]
>>> insertion_sort(records, key=lambda x: x[0])
[(1, 'beta'), (1, 'delta'), (2, 'alpha'), (2, 'gamma')]

>>> binary_insertion_sort([9, 7, 5, 3, 1])
[1, 3, 5, 7, 9]
"""

from typing import Any, Callable, List, Sequence, TypeVar

T = TypeVar("T")


def insert(
    elem: T,
    sorted_list: List[T],
    key: Callable[[T], Any] = lambda x: x,
    reverse: bool = False,
) -> List[T]:
    """Insert elem into a sorted list, maintaining sorted order and stability.

    For ascending sort (reverse=False):
    Place elem after existing elements with key(elem) == key(other) to ensure stability.

    For descending sort (reverse=True):
    Place elem after existing elements with key(elem) == key(other) to ensure stability.
    """
    elem_key = key(elem)
    if not reverse:
        # Ascending: find first index where key(x) > elem_key
        for i, existing in enumerate(sorted_list):
            if key(existing) > elem_key:
                return sorted_list[:i] + [elem] + sorted_list[i:]
        return sorted_list + [elem]
    else:
        # Descending: find first index where key(x) < elem_key
        for i, existing in enumerate(sorted_list):
            if key(existing) < elem_key:
                return sorted_list[:i] + [elem] + sorted_list[i:]
        return sorted_list + [elem]


def insertion_sort(
    seq: Sequence[T],
    key: Callable[[T], Any] = lambda x: x,
    reverse: bool = False,
) -> List[T]:
    """Sort sequence seq using verified stable linear insertion sort.

    Parameters:
        seq: Input sequence of elements.
        key: Function to extract comparison key for each element.
        reverse: If True, sort in descending order; otherwise ascending.

    Returns:
        A new list containing the sorted elements.
    """
    result: List[T] = []
    for item in seq:
        result = insert(item, result, key=key, reverse=reverse)
    return result


def binary_insertion_sort(
    seq: Sequence[T],
    key: Callable[[T], Any] = lambda x: x,
    reverse: bool = False,
) -> List[T]:
    """Sort sequence seq using binary insertion sort.

    Uses binary search to locate insertion index in O(log n) comparisons,
    maintaining stability by inserting after equal elements.
    """
    result: List[T] = []
    for item in seq:
        item_key = key(item)
        low = 0
        high = len(result)
        while low < high:
            mid = (low + high) // 2
            mid_key = key(result[mid])
            if not reverse:
                if mid_key <= item_key:
                    low = mid + 1
                else:
                    high = mid
            else:
                if mid_key >= item_key:
                    low = mid + 1
                else:
                    high = mid
        result.insert(low, item)
    return result


if __name__ == "__main__":
    import doctest

    results = doctest.testmod()
    print(f"Doctest results: {results.failed} failures out of {results.attempted} tests.")
