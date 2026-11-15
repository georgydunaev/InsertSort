# Project Overview: Formally Verified Insertion Sort (`InsertSort`)

## Purpose and Multi-Language Verification

`InsertSort` provides a machine-checked formal verification of insertion sort in Coq ([Sort.v](file:///botworkspace/InsertSort/Sort.v)) alongside verified and cross-validated implementations in OCaml, Standard ML (Poly/ML and CakeML compatible), C++17, and Python.

## Repository Architecture

### 1. Coq Formalization and Extraction
- [Sort.v](file:///botworkspace/InsertSort/Sort.v): Constructive Coq formalization proving:
  - Permutation preservation: `ins_perm` and `sort_perm`.
  - Sortedness preservation: `ins_sorted` and `sort_sorted`.
  - Total correctness: `insertion_sort_correct : forall l, Permutation l (s l) /\ Sorted le (s l)`.
  - Idempotence (`sorted_fix`, `proj`), boolean decision equivalence (`Sorted_bool_equiv`), and key-based sorting stability (`ins_by_stable`).
- [sort.ml](file:///botworkspace/InsertSort/sort.ml) and [sort.mli](file:///botworkspace/InsertSort/sort.mli): Verified OCaml code extracted directly from `Sort.v`.

### 2. Standard ML Implementations (Poly/ML and CakeML Compatible)
- [insert_sort.sml](file:///botworkspace/InsertSort/insert_sort.sml): Portable SML'97 implementation of polymorphic stable insertion sort (`insBy`, `sortBy`, `ins`, `sort`), sortedness verification (`isSortedBy`), and multiset permutation checking.
- [binary_insert_sort.sml](file:///botworkspace/InsertSort/binary_insert_sort.sml): Portable SML'97 binary insertion sort using upper-bound binary search (`bisectRightBy`) to locate insertion positions in $O(\log n)$ comparisons while preserving stability.

### 3. C++17 Template Implementations (`include/`)
- [include/insert_sort.hpp](file:///botworkspace/InsertSort/include/insert_sort.hpp): Generic iterator-based and container-based linear insertion sort with custom comparators.
- [include/binary_insert_sort.hpp](file:///botworkspace/InsertSort/include/binary_insert_sort.hpp): Generic C++17 binary insertion sort using `std::upper_bound`.

### 4. Python Reference Implementations and Benchmarks
- [insert_sort.py](file:///botworkspace/InsertSort/insert_sort.py): Typed Python stable linear insertion sort (`insert`, `insertion_sort`) with custom `key` and `reverse` support.
- [binary_insertion_sort.py](file:///botworkspace/InsertSort/binary_insert_sort.py): Typed Python stable binary insertion sort with comparison-counting instrumentation (`ComparisonCounter`, `count_comparisons_linear`, `count_comparisons_binary`).
- [benchmark.py](file:///botworkspace/InsertSort/benchmark.py): Empirical timing and complexity verification across best-case ($O(n)$), average-case ($O(n^2)$), and worst-case ($O(n^2)$) inputs.

### 5. Verification Suite (`tests/`)
- [tests/test_insert_sort.py](file:///botworkspace/InsertSort/tests/test_insert_sort.py), [tests/test_binary_insert_sort.py](file:///botworkspace/InsertSort/tests/test_binary_insert_sort.py), [tests/test_properties.py](file:///botworkspace/InsertSort/tests/test_properties.py), and [tests/test_insertsort.py](file:///botworkspace/InsertSort/tests/test_insertsort.py): Comprehensive unit and property-based tests checking sortedness, permutation invariance, idempotence, stability, and $O(n \log n)$ comparison bounds.
- [tests/test_cpp_insert_sort.cpp](file:///botworkspace/InsertSort/tests/test_cpp_insert_sort.cpp): C++ test suite.

## Verification Command

```bash
python3 -m unittest discover -s /botworkspace/InsertSort/tests -p "test_*.py"
```
