# InsertSort: Verified Insertion Sort in Coq (`Sort.v`)

## Overview
`InsertSort` provides a complete formal verification of insertion sort in the Coq Proof Assistant (`Sort.v`), establishing sortedness, permutation preservation, idempotence, equivalence to boolean predicates, and sorting stability. It also includes verified code extraction to OCaml (`sort.ml`), an idiomatic Standard ML implementation (`insert_sort.sml`), a Python reference implementation (`insert_sort.py`) with type annotations and doctests, and a benchmark and property-based test suite (`tests/`).

## Formally Verified Theorems in Coq (`Sort.v`)

All theorems in `Sort.v` are proved constructively without any axioms or admitted steps:

1. **Permutation Preservation**:
   - `ins_perm : forall a l, Permutation (a :: l) (ins a l)`
   - `sort_perm : forall l, Permutation l (s l)`

2. **Sortedness**:
   - `ins_sorted : forall a l, Sorted le l -> Sorted le (ins a l)`
   - `sort_sorted : forall l, Sorted le (s l)`

3. **Total Correctness**:
   - `insertion_sort_correct : forall l, Permutation l (s l) /\ Sorted le (s l)`

4. **Idempotence and Projection**:
   - `sorted_fix : forall l, Sorted le l -> s l = l`
   - `proj : forall x, s (s x) = s x`

5. **Boolean Characterizations**:
   - `ord_iff_sorted : forall l, ord l = true <-> Sorted le l`
   - `sort_ord : forall l, ord (s l) = true`
   - `ord_then_fix : forall x, ord x = true -> s x = x`
   - `thmeq : forall x, ord x = P x 0`
   - `sort_P_zero : forall l, P (s l) 0 = true`

6. **Key-Based Sorting and Stability**:
   - `key_ins : forall A, (A -> nat) -> A -> list A -> list A`
   - `key_sort : forall A, (A -> nat) -> list A -> list A`
   - `key_sort_stable : forall A key k l, filter (fun x => Nat.eqb (key x) k) (key_sort A key l) = filter (fun x => Nat.eqb (key x) k) l`
   - `key_sort_id_eq_s : forall l, key_sort nat (fun x => x) l = s l`

7. **Code Extraction**:
   - Extracted to `sort.ml` and `sort.mli` via Coq Extraction facility.

## Repository Structure

- `Sort.v`: Formal specification, correctness proofs, and code extraction in Coq.
- `insert_sort.sml`: Standard ML implementation (Poly/ML & CakeML compatible) with built-in invariant verification.
- `insert_sort.py`: Python reference implementation with type annotations, docstrings, linear and binary insertion sort, custom key extraction, and reverse ordering.
- `benchmark.py`: Empirical timing and operation count verification across sorted, reversed, and random inputs.
- `tests/test_insert_sort.py`: Unit tests for empty, single, duplicates, reverse, negative, floating-point, custom comparator, and stability.
- `tests/test_properties.py`: Property-based invariant tests covering permutation preservation, sortedness, idempotence, extrema, and randomized stability.
- `tests/test_insertsort.py`: Integration test suite verifying Coq compilation, SML execution, Python doctests, and invariant checks.
- `tickets/`: Issue tracking and resolution records.

## Running Verification and Tests

### 1. Compile Coq Proofs
```bash
coqc Sort.v
```

### 2. Run Standard ML Verification (Poly/ML)
```bash
poly -q --use insert_sort.sml < /dev/null
```

### 3. Run Python Doctests
```bash
python3 -m doctest insert_sort.py
```

### 4. Run Full Unittest Suite
```bash
python3 -m unittest discover -s tests -p "test_*.py"
```

### 5. Run Benchmarks
```bash
python3 benchmark.py
```
