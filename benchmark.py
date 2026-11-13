#!/usr/bin/env python3
"""Benchmark script measuring execution time and operation counts for insertion sort.

Compares:
- Standard insertion sort
- Binary insertion sort
- Python built-in Timsort (sorted)
Over array sizes N = [10, 50, 100, 500, 1000] across:
- Random arrays (average-case)
- Already sorted arrays (best-case O(n))
- Reversed arrays (worst-case O(n^2))
"""

import random
import time
from typing import List, Tuple
from insert_sort import insertion_sort, binary_insertion_sort


def count_insertion_operations(arr: List[int]) -> Tuple[int, int]:
    """Count comparisons and shifts in standard insertion sort."""
    comparisons = 0
    shifts = 0
    a = list(arr)
    for i in range(1, len(a)):
        val = a[i]
        j = i - 1
        while j >= 0:
            comparisons += 1
            if a[j] > val:
                a[j + 1] = a[j]
                shifts += 1
                j -= 1
            else:
                break
        a[j + 1] = val
    return comparisons, shifts


def benchmark_timing(sizes: List[int]) -> None:
    print("=" * 78)
    print(f"{'N':>6} | {'Input Type':>10} | {'InsertSort (ms)':>16} | {'BinarySort (ms)':>16} | {'sorted() (ms)':>14}")
    print("-" * 78)

    for n in sizes:
        inputs = {
            "Sorted": list(range(n)),
            "Reversed": list(range(n, 0, -1)),
            "Random": [random.randint(0, 10000) for _ in range(n)],
        }

        for name, data in inputs.items():
            # Time standard insertion sort
            t0 = time.perf_counter()
            _ = insertion_sort(data)
            t_ins = (time.perf_counter() - t0) * 1000.0

            # Time binary insertion sort
            t0 = time.perf_counter()
            _ = binary_insertion_sort(data)
            t_bin = (time.perf_counter() - t0) * 1000.0

            # Time built-in sorted
            t0 = time.perf_counter()
            _ = sorted(data)
            t_builtin = (time.perf_counter() - t0) * 1000.0

            print(f"{n:>6} | {name:>10} | {t_ins:>16.4f} | {t_bin:>16.4f} | {t_builtin:>14.4f}")


def benchmark_complexity(sizes: List[int]) -> None:
    print("\n" + "=" * 78)
    print(f"{'N':>6} | {'Input Type':>10} | {'Comparisons':>14} | {'Shifts':>14} | {'Complexity Model':>18}")
    print("-" * 78)

    for n in sizes:
        inputs = {
            "Sorted": list(range(n)),
            "Reversed": list(range(n, 0, -1)),
            "Random": [random.randint(0, 10000) for _ in range(n)],
        }

        for name, data in inputs.items():
            cmp_cnt, shift_cnt = count_insertion_operations(data)
            model = "O(n)" if name == "Sorted" else "O(n^2)"
            print(f"{n:>6} | {name:>10} | {cmp_cnt:>14} | {shift_cnt:>14} | {model:>18}")


if __name__ == "__main__":
    test_sizes = [10, 50, 100, 500, 1000]
    benchmark_timing(test_sizes)
    benchmark_complexity([10, 50, 100, 500])
