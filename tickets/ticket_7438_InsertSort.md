# [INSERTSORT] Ticket 7438: Binary Insertion Sort Optimization with Bisect Insertion Point Search

**Repository:** `InsertSort`  
**Assigned AI Model:** `gemini-3.8-flash-medium`  
**Harness:** `agy`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T23:46:51Z`  
**Resolved:** `2026-11-13T23:52:00Z`  

## Task Description
Implement Binary Insertion Sort optimization using bisect right insertion point search across Python, Standard ML, and C++ template headers.
Reduce comparison count from O(n^2) to O(n log n) while preserving stability (inserting duplicate keys after existing equals).

## Requirements
1. Python implementation in `binary_insert_sort.py`:
   - Bisect right search for stability preservation
   - Comparison count tracking
   - Generic key function, comparator, and reverse sort support
   - In-place and out-of-place sorting APIs
2. Standard ML implementation in `binary_insert_sort.sml`:
   - Pure ASCII (zero non-ASCII bytes)
   - Compatible with Poly/ML and CakeML
   - Functional and array-backed binary insertion sort
   - Comparison counting and stability preservation
3. C++ template header in `include/binary_insert_sort.hpp`:
   - Modern C++17 template implementation for random-access iterators and containers
   - Comparison counting support
   - Custom comparator and move semantics support
4. Comprehensive test suite in `tests/test_binary_insert_sort.py`:
   - Property-based permutation checks
   - Monotonic sortedness checks
   - Strict stability verification with tagged tuples
   - Comparison count tracking demonstrating O(n log n) comparisons versus O(n^2) linear insertion sort
   - Edge cases: empty sequence, single element, duplicates, homogeneous arrays, reverse sorted, negative numbers, floats

## Execution Guidelines
1. Work autonomously in `InsertSort/`.
2. Ensure all existing tests continue to pass.
3. Adhere to strict invariants: no emojis, no directional arrows in titles or links, zero non-ASCII bytes in SML.
4. Run unittest discovery and security guard scans before committing.

## Resolution Notes
1. Created Python implementation in `binary_insert_sort.py`:
   - Implemented `bisect_right_search` guaranteeing stable placement after equal keys with O(log n) comparisons.
   - Implemented `binary_insertion_sort`, `binary_insertion_sort_counted`, and `binary_insertion_sort_inplace`.
   - Supported custom keys, custom 2-argument boolean and 3-way comparators, and `reverse=True`.
2. Created Standard ML implementation in `binary_insert_sort.sml`:
   - Zero non-ASCII bytes verified with pure ASCII compliance.
   - Compatible with Poly/ML and CakeML standard basis.
   - Implemented `bisectRight`, `shiftAndInsert`, `sortArray`, `sortBy`, `sortCounted`, `insertion_sort`, and `keySort`.
   - Verified automated test assertions for sortedness, stability, and comparison count.
3. Created C++17 template header in `include/binary_insert_sort.hpp`:
   - Implemented `binary_insertion_sort` and `binary_insertion_sort_counted` for random-access iterators and containers.
   - Uses `std::upper_bound` for bisect-right stability preservation and O(n log n) comparisons.
   - Added `CountingCompare` wrapper and move-only type support.
   - Integrated with `include/insert_sort.hpp` and verified in `tests/test_cpp_insert_sort.cpp`.
4. Created comprehensive test suite in `tests/test_binary_insert_sort.py`:
   - Permutation invariant preservation via Counter checks across randomized sequences.
   - Monotonic sortedness for ascending and descending sequences.
   - Idempotence and in-place vs out-of-place equivalence.
   - Strict stability verification with tagged tuples on both fixed and randomized key-tag distributions.
   - Verified O(n log n) theoretical bound and demonstrated 10x reduction in comparisons versus linear insertion sort on size 100 lists.
5. All test suites verified and passing:
   - `python3 -m unittest discover -s tests`: 44 tests passed.
   - `make test-cpp`: 13 C++ tests passed.
   - Poly/ML execution of both SML files passed.
   - Doctests on both Python modules passed.
