# [INSERTSORT] Ticket 8002: Prove Permutation Preservation and Total Correctness

**Repository:** `InsertSort`  
**Status:** `CLOSED`  
**Created:** `2026-11-13T21:47:12Z`  
**Closed:** `2026-11-13T21:56:00Z`  

## Resolution Summary
1. Proved `ins_perm`: `forall a l, Permutation (a :: l) (ins a l)`.
2. Proved `sort_perm`: `forall l, Permutation l (s l)`.
3. Proved total correctness `insertion_sort_correct`: `forall l, Permutation l (s l) /\ Sorted le (s l)`.
4. Proved `sorted_fix`: `forall l, Sorted le l -> s l = l`.
5. Proved idempotence `proj`: `forall x, s (s x) = s x`.
6. Proved `ord_then_fix`: `forall x, ord x = true -> s x = x`.
7. Zero admitted or aborted lemmas.
