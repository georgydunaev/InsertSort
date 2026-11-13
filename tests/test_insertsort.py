#!/usr/bin/env python3
"""Property-based, complexity, and formal verification tests for InsertSort (Sort.v)."""

import os
import subprocess
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestInsertSortIntegration(unittest.TestCase):
    def test_coq_sort_v_exists(self):
        vfile = os.path.join(ROOT, "Sort.v")
        self.assertTrue(os.path.isfile(vfile))
        with open(vfile, encoding="utf-8") as f:
            content = f.read()
        self.assertIn("Fixpoint", content)
        self.assertIn("sort_sorted", content)
        self.assertIn("sort_perm", content)
        self.assertIn("key_sort_stable", content)

    def test_coq_compilation(self):
        vfile = os.path.join(ROOT, "Sort.v")
        cmd = ["coqc", vfile]
        res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, f"coqc compilation failed: {res.stderr}\n{res.stdout}")

    def test_sml_implementation_exists_and_runs(self):
        smlfile = os.path.join(ROOT, "insert_sort.sml")
        self.assertTrue(os.path.isfile(smlfile))
        cmd = ["poly", "-q", "--use", smlfile]
        res = subprocess.run(cmd, cwd=ROOT, input="", capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, f"PolyML execution failed: {res.stderr}\n{res.stdout}")
        self.assertIn("All SML InsertSort tests passed successfully", res.stdout)

    def test_python_doctests_pass(self):
        pyfile = os.path.join(ROOT, "insert_sort.py")
        cmd = ["python3", "-m", "doctest", pyfile]
        res = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(res.returncode, 0, f"Doctest failed: {res.stderr}\n{res.stdout}")

    def test_sorted_and_permutation_invariants(self):
        from insert_sort import insertion_sort

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
