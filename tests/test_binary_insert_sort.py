#!/usr/bin/env python3
"""Comprehensive unit and property-based tests for binary insertion sort."""

from collections import Counter
import math
import os
import random
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from binary_insert_sort import (
    binary_insertion_sort,
    binary_insertion_sort_counted,
    binary_insertion_sort_inplace,
    bisect_right_search,
    linear_insertion_sort_counted,
)


class TestBinaryInsertSortEdgeCases(unittest.TestCase):
    """Test standard edge cases and functional requirements."""

    def test_empty_list(self):
        self.assertEqual(binary_insertion_sort([]), [])
        sorted_res, count = binary_insertion_sort_counted([])
        self.assertEqual(sorted_res, [])
        self.assertEqual(count, 0)

        data = []
        c = binary_insertion_sort_inplace(data)
        self.assertEqual(data, [])
        self.assertEqual(c, 0)

    def test_single_element_list(self):
        self.assertEqual(binary_insertion_sort([42]), [42])
        sorted_res, count = binary_insertion_sort_counted([42])
        self.assertEqual(sorted_res, [42])
        self.assertEqual(count, 0)

        data = [42]
        c = binary_insertion_sort_inplace(data)
        self.assertEqual(data, [42])
        self.assertEqual(c, 0)

    def test_two_elements(self):
        self.assertEqual(binary_insertion_sort([2, 1]), [1, 2])
        self.assertEqual(binary_insertion_sort([1, 2]), [1, 2])
        self.assertEqual(binary_insertion_sort([2, 2]), [2, 2])

    def test_already_sorted_list(self):
        data = [1, 2, 3, 4, 5, 6, 7]
        self.assertEqual(binary_insertion_sort(data), data)

    def test_reverse_sorted_list(self):
        data = [7, 6, 5, 4, 3, 2, 1]
        expected = [1, 2, 3, 4, 5, 6, 7]
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_homogeneous_all_duplicates(self):
        data = [5, 5, 5, 5, 5, 5]
        self.assertEqual(binary_insertion_sort(data), data)

    def test_duplicate_elements(self):
        data = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
        expected = sorted(data)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_negative_numbers(self):
        data = [-10, 0, 10, -5, 5, -20, 20]
        expected = sorted(data)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_floating_point_values(self):
        data = [3.14, 2.71, -1.414, 0.0, 1.732, -0.5]
        expected = sorted(data)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_reverse_flag(self):
        data = [1, 5, 2, 4, 3]
        expected = [5, 4, 3, 2, 1]
        self.assertEqual(binary_insertion_sort(data, reverse=True), expected)

    def test_custom_key_comparator(self):
        words = ["apple", "pie", "banana", "kiwi", "fig"]
        expected_len = sorted(words, key=len)
        self.assertEqual(binary_insertion_sort(words, key=len), expected_len)

    def test_custom_comparator_function(self):
        data = [5, 1, 9, 3, 7]
        # Custom ascending comparator
        cmp_asc = lambda a, b: a < b
        self.assertEqual(binary_insertion_sort(data, cmp=cmp_asc), [1, 3, 5, 7, 9])
        # Three-way comparator
        def cmp_three_way(a, b):
            return -1 if a < b else (1 if a > b else 0)
        self.assertEqual(binary_insertion_sort(data, cmp=cmp_three_way), [1, 3, 5, 7, 9])


class TestBinaryInsertSortProperties(unittest.TestCase):
    """Property-based invariant tests over randomized sequences."""

    def test_permutation_invariant(self):
        """Multiset of elements must be preserved."""
        rng = random.Random(10101)
        for _ in range(50):
            length = rng.randint(0, 80)
            data = [rng.randint(-100, 100) for _ in range(length)]
            sorted_data = binary_insertion_sort(data)
            self.assertEqual(Counter(sorted_data), Counter(data))

    def test_sortedness_invariant(self):
        """Result must be monotonically non-decreasing or non-increasing."""
        rng = random.Random(20202)
        for _ in range(50):
            length = rng.randint(0, 80)
            data = [rng.randint(-500, 500) for _ in range(length)]

            out = binary_insertion_sort(data)
            self.assertTrue(all(out[i] <= out[i + 1] for i in range(len(out) - 1)))

            out_rev = binary_insertion_sort(data, reverse=True)
            self.assertTrue(all(out_rev[i] >= out_rev[i + 1] for i in range(len(out_rev) - 1)))

    def test_idempotence_invariant(self):
        """Sorting twice must produce identical results."""
        rng = random.Random(30303)
        for _ in range(50):
            length = rng.randint(0, 60)
            data = [rng.randint(-50, 50) for _ in range(length)]
            s1 = binary_insertion_sort(data)
            s2 = binary_insertion_sort(s1)
            self.assertEqual(s1, s2)

    def test_inplace_matches_outofplace(self):
        """In-place binary insertion sort must match out-of-place result."""
        rng = random.Random(40404)
        for _ in range(50):
            length = rng.randint(0, 60)
            data = [rng.randint(-100, 100) for _ in range(length)]
            expected = binary_insertion_sort(data)
            data_copy = list(data)
            binary_insertion_sort_inplace(data_copy)
            self.assertEqual(data_copy, expected)

    def test_extrema_and_length_preservation(self):
        """Length, min, and max must be preserved on non-empty lists."""
        rng = random.Random(50505)
        for _ in range(50):
            length = rng.randint(1, 70)
            data = [rng.randint(-1000, 1000) for _ in range(length)]
            out = binary_insertion_sort(data)
            self.assertEqual(len(out), len(data))
            self.assertEqual(out[0], min(data))
            self.assertEqual(out[-1], max(data))


class TestBinaryInsertSortStability(unittest.TestCase):
    """Verify stability: elements with equal keys maintain input relative order."""

    def test_stability_deterministic(self):
        records = [
            (2, "item1"),
            (1, "item2"),
            (2, "item3"),
            (1, "item4"),
            (2, "item5"),
            (3, "item6"),
        ]
        sorted_records = binary_insertion_sort(records, key=lambda r: r[0])
        expected = [
            (1, "item2"),
            (1, "item4"),
            (2, "item1"),
            (2, "item3"),
            (2, "item5"),
            (3, "item6"),
        ]
        self.assertEqual(sorted_records, expected)

    def test_stability_randomized(self):
        rng = random.Random(60606)
        for _ in range(40):
            length = rng.randint(10, 80)
            data = [(rng.randint(0, 5), idx) for idx in range(length)]

            out = binary_insertion_sort(data, key=lambda x: x[0])

            # For each key, indices must remain in strictly ascending order
            for key_val in range(6):
                orig_indices = [idx for k, idx in data if k == key_val]
                sorted_indices = [idx for k, idx in out if k == key_val]
                self.assertEqual(sorted_indices, orig_indices)

    def test_stability_reverse(self):
        """Stability must also hold when sorting in reverse order."""
        records = [
            (2, "a"),
            (1, "b"),
            (2, "c"),
            (3, "d"),
            (1, "e"),
            (3, "f"),
        ]
        out = binary_insertion_sort(records, key=lambda r: r[0], reverse=True)
        expected = [
            (3, "d"),
            (3, "f"),
            (2, "a"),
            (2, "c"),
            (1, "b"),
            (1, "e"),
        ]
        self.assertEqual(out, expected)


class TestBinaryInsertSortComparisonCount(unittest.TestCase):
    """Verify O(n log n) comparison count behavior."""

    def test_theoretical_upper_bound(self):
        """Comparisons must satisfy count <= sum_{i=1}^{n-1} ceil(log2(i + 1))."""
        rng = random.Random(70707)
        for n in [5, 10, 25, 50, 100]:
            # Maximum possible comparisons for binary search insertion
            max_theoretical = sum(math.ceil(math.log2(i + 1)) for i in range(1, n))

            for _ in range(10):
                data = [rng.randint(-1000, 1000) for _ in range(n)]
                _, count = binary_insertion_sort_counted(data)
                self.assertLessEqual(count, max_theoretical)

                # In-place version should also obey the theoretical bound
                data_copy = list(data)
                count_inplace = binary_insertion_sort_inplace(data_copy)
                self.assertLessEqual(count_inplace, max_theoretical)

    def test_binary_vs_linear_comparisons_worst_case(self):
        """On worst-case linear insertion data, binary comparisons are O(n log n) vs O(n^2) linear."""
        n = 100
        # For forward-scan linear insertion, ascending data traverses the entire prefix before appending
        data = list(range(1, n + 1))

        _, bin_count = binary_insertion_sort_counted(data)
        _, lin_count = linear_insertion_sort_counted(data)

        # Linear comparisons on forward worst case: n*(n-1)/2 = 4950
        self.assertEqual(lin_count, n * (n - 1) // 2)

        # Binary comparisons on n=100 is bounded by ~580
        self.assertLessEqual(bin_count, 600)

        # Binary must be at least 7x fewer comparisons than linear for n=100
        self.assertGreater(lin_count, bin_count * 7)

    def test_binary_vs_linear_comparisons_random_case(self):
        """On random permutations, binary search requires significantly fewer comparisons."""
        rng = random.Random(80808)
        n = 100
        data = [rng.randint(-500, 500) for _ in range(n)]

        _, bin_count = binary_insertion_sort_counted(data)
        _, lin_count = linear_insertion_sort_counted(data)

        # Average linear comparisons is ~ n^2 / 4 = 2500
        self.assertGreater(lin_count, 1500)
        self.assertLessEqual(bin_count, 600)
        self.assertGreater(lin_count, bin_count * 2)


if __name__ == "__main__":
    unittest.main()
