#!/usr/bin/env python3
"""Unit tests for Python insertion sort implementation."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from insert_sort import insertion_sort, binary_insertion_sort


class TestInsertSortUnit(unittest.TestCase):
    """Test standard edge cases and functional requirements."""

    def test_empty_list(self):
        self.assertEqual(insertion_sort([]), [])
        self.assertEqual(binary_insertion_sort([]), [])

    def test_single_element_list(self):
        self.assertEqual(insertion_sort([42]), [42])
        self.assertEqual(binary_insertion_sort([42]), [42])

    def test_already_sorted_list(self):
        data = [1, 2, 3, 4, 5, 6, 7]
        self.assertEqual(insertion_sort(data), data)
        self.assertEqual(binary_insertion_sort(data), data)

    def test_reverse_sorted_list(self):
        data = [7, 6, 5, 4, 3, 2, 1]
        expected = [1, 2, 3, 4, 5, 6, 7]
        self.assertEqual(insertion_sort(data), expected)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_duplicate_elements(self):
        data = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
        expected = sorted(data)
        self.assertEqual(insertion_sort(data), expected)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_negative_numbers(self):
        data = [-10, 0, 10, -5, 5, -20, 20]
        expected = sorted(data)
        self.assertEqual(insertion_sort(data), expected)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_floating_point_values(self):
        data = [3.14, 2.71, -1.414, 0.0, 1.732, -0.5]
        expected = sorted(data)
        self.assertEqual(insertion_sort(data), expected)
        self.assertEqual(binary_insertion_sort(data), expected)

    def test_reverse_flag(self):
        data = [1, 5, 2, 4, 3]
        expected = [5, 4, 3, 2, 1]
        self.assertEqual(insertion_sort(data, reverse=True), expected)
        self.assertEqual(binary_insertion_sort(data, reverse=True), expected)

    def test_custom_key_comparator(self):
        words = ["apple", "pie", "banana", "kiwi", "fig"]
        # Sort by length
        expected_len = sorted(words, key=len)
        self.assertEqual(insertion_sort(words, key=len), expected_len)
        self.assertEqual(binary_insertion_sort(words, key=len), expected_len)

    def test_stability_preservation(self):
        # Items with same key must maintain relative order
        records = [
            (2, "item1"),
            (1, "item2"),
            (2, "item3"),
            (1, "item4"),
            (2, "item5"),
            (3, "item6"),
        ]
        sorted_records = insertion_sort(records, key=lambda r: r[0])
        bin_sorted_records = binary_insertion_sort(records, key=lambda r: r[0])

        expected = [
            (1, "item2"),
            (1, "item4"),
            (2, "item1"),
            (2, "item3"),
            (2, "item5"),
            (3, "item6"),
        ]
        self.assertEqual(sorted_records, expected)
        self.assertEqual(bin_sorted_records, expected)


if __name__ == "__main__":
    unittest.main()
