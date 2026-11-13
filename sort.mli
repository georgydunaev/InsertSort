
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

val le_lt_dec : nat -> nat -> sumbool

val le_gt_dec : nat -> nat -> sumbool

val le_dec : nat -> nat -> sumbool

val ins : nat -> nat list -> nat list

val s : nat list -> nat list

val key_ins : ('a1 -> nat) -> 'a1 -> 'a1 list -> 'a1 list

val key_sort : ('a1 -> nat) -> 'a1 list -> 'a1 list
