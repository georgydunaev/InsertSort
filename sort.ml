
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type sumbool =
| Left
| Right

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Left
  | S n0 -> (match m with
             | O -> Right
             | S n1 -> le_lt_dec n0 n1)

(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val ins : nat -> nat list -> nat list **)

let rec ins a = function
| Nil -> Cons (a, Nil)
| Cons (yh, yt) ->
  (match le_dec a yh with
   | Left -> Cons (a, (Cons (yh, yt)))
   | Right -> Cons (yh, (ins a yt)))

(** val s : nat list -> nat list **)

let rec s = function
| Nil -> Nil
| Cons (xh, xt) -> ins xh (s xt)

(** val key_ins : ('a1 -> nat) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec key_ins key a = function
| Nil -> Cons (a, Nil)
| Cons (yh, yt) ->
  (match le_dec (key a) (key yh) with
   | Left -> Cons (a, (Cons (yh, yt)))
   | Right -> Cons (yh, (key_ins key a yt)))

(** val key_sort : ('a1 -> nat) -> 'a1 list -> 'a1 list **)

let rec key_sort key = function
| Nil -> Nil
| Cons (xh, xt) -> key_ins key xh (key_sort key xt)
