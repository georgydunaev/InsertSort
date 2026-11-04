# InsertSort — Verified Insertion Sort in Coq (`Sort.v`)

## Overview
`InsertSort` contains a formal verification of insertion sort in Coq (`Sort.v`), proving sortedness and permutation preservation, accompanied by property-based invariant and complexity tests (`tests/test_insertsort.py`).

## Running Verification Tests
```bash
python3 -m unittest discover -s tests -p "test_*.py"
```
