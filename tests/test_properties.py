#!/usr/bin/env python3
"""Property-based invariant and fuzzing tests for insertion sort."""

from collections import Counter
import os
import random
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from insert_sort import insertion_sort, binary_insertion_sort


class TestInsertSortProperties(unittest.TestCase):
    """Property-based invariant tests over pseudo-random generated sequences."""

    def test_permutation_invariant(self):
        """Output multiset must be identical to input multiset (Counter equality)."""
        rng = random.Random(12345)
        for _ in range(50):
            length = rng.randint(0, 80)
            data = [rng.randint(-100, 100) for _ in range(length)]
            sorted_data = insertion_sort(data)
            bin_sorted_data = binary_insertion_sort(data)

            self.assertEqual(Counter(sorted_data), Counter(data))
            self.assertEqual(Counter(bin_sorted_data), Counter(data))

    def test_sortedness_invariant(self):
        """Output must be monotonically non-decreasing (or non-increasing if reverse)."""
        rng = random.Random(23456)
        for _ in range(50):
            length = rng.randint(0, 80)
            data = [rng.randint(-500, 500) for _ in range(length)]

            out = insertion_sort(data)
            self.assertTrue(all(out[i] <= out[i + 1] for i in range(len(out) - 1)))

            out_rev = insertion_sort(data, reverse=True)
            self.assertTrue(all(out_rev[i] >= out_rev[i + 1] for i in range(len(out_rev) - 1)))

    def test_idempotence_invariant(self):
        """Sorting an already sorted list must yield the exact same list: sort(sort(x)) == sort(x)."""
        rng = random.Random(34567)
        for _ in range(50):
            length = rng.randint(0, 60)
            data = [rng.randint(-50, 50) for _ in range(length)]

            s1 = insertion_sort(data)
            s2 = insertion_sort(s1)
            self.assertEqual(s1, s2)

            bs1 = binary_insertion_sort(data)
            bs2 = binary_insertion_sort(bs1)
            self.assertEqual(bs1, bs2)

    def test_extrema_and_length_preservation(self):
        """Length, min, and max must be strictly preserved on non-empty lists."""
        rng = random.Random(45678)
        for _ in range(50):
            length = rng.randint(1, 70)
            data = [rng.randint(-1000, 1000) for _ in range(length)]

            out = insertion_sort(data)
            self.assertEqual(len(out), len(data))
            self.assertEqual(out[0], min(data))
            self.assertEqual(out[-1], max(data))

    def test_strict_stability_randomized(self):
        """Items with identical keys must preserve their relative input order."""
        rng = random.Random(56789)
        for _ in range(40):
            length = rng.randint(10, 80)
            # Keys between 0 and 5, values are unique serial identifiers
            data = [(rng.randint(0, 5), idx) for idx in range(length)]

            out_lin = insertion_sort(data, key=lambda x: x[0])
            out_bin = binary_insertion_sort(data, key=lambda x: x[0])

            # For each distinct key, check that indices are strictly increasing
            for key_val in range(6):
                indices_orig = [idx for k, idx in data if k == key_val]
                indices_lin = [idx for k, idx in out_lin if k == key_val]
                indices_bin = [idx for k, idx in out_bin if k == key_val]

                self.assertEqual(indices_lin, indices_orig)
                self.assertEqual(indices_bin, indices_orig)

    def test_equivalence_with_builtin_sorted(self):
        """Insertion sort implementations must match Python's built-in sorted for all inputs."""
        rng = random.Random(67890)
        for _ in range(50):
            length = rng.randint(0, 100)
            data = [rng.randint(-1000, 1000) for _ in range(length)]

            expected = sorted(data)
            self.assertEqual(insertion_sort(data), expected)
            self.assertEqual(binary_insertion_sort(data), expected)


if __name__ == "__main__":
    unittest.main()
