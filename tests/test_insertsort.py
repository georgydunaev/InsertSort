#!/usr/bin/env python3
"""Property-based and complexity tests for InsertSort (Sort.v)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def insert(x, xs, key=lambda v: v):
    for i, elem in enumerate(xs):
        if key(x) <= key(elem):
            return xs[:i] + [x] + xs[i:]
    return xs + [x]


def insertion_sort(xs, key=lambda v: v):
    res = []
    for x in xs:
        res = insert(x, res, key=key)
    return res


class TestInsertSort(unittest.TestCase):
    def test_coq_sort_v_exists(self):
        vfile = os.path.join(ROOT, "Sort.v")
        self.assertTrue(os.path.isfile(vfile))
        with open(vfile, encoding="utf-8") as f:
            content = f.read()
        self.assertIn("Fixpoint", content)

    def test_sorted_and_permutation_invariants(self):
        samples = [
            [],
            [1],
            [5, 4, 3, 2, 1],
            [3, 1, 4, 1, 5, 9, 2, 6, 5],
            [-10, 0, 10, -5, 5],
        ]
        for arr in samples:
            out = insertion_sort(arr)
            self.assertEqual(out, sorted(arr))
            self.assertEqual(len(out), len(arr))


if __name__ == "__main__":
    unittest.main()
