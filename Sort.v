(**
 * Sort.v — Formal Verification of Insertion Sort in Coq
 *
 * This file formalizes and verifies insertion sort over lists of natural numbers
 * as well as generic key-based insertion sort.
 *
 * Proven Properties:
 * 1. Correctness: Sorted le (s l) for all lists l
 * 2. Permutation: Permutation l (s l) for all lists l
 * 3. Total Correctness: Permutation l (s l) /\ Sorted le (s l)
 * 4. Idempotence: s (s l) = s l
 * 5. Boolean Characterization: ord l = true <-> Sorted le l
 * 6. Fixpoint Characterization: ord l = true -> s l = l
 * 7. Stability: Key-based insertion sort preserves the relative order
 *    of elements with equal keys.
 *)

Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.

(** Core insertion function for natural numbers *)
Fixpoint ins (a: nat) (y: list nat) {struct y}: list nat :=
  match y with
  | [] => [a]
  | yh :: yt =>
    match le_dec a yh with
    | left _ => a :: yh :: yt
    | right _ => yh :: ins a yt
    end
  end.

(** Core insertion sort function *)
Fixpoint s (x: list nat) {struct x}: list nat :=
  match x with
  | [] => []
  | xh :: xt => ins xh (s xt)
  end.

Definition insertion_sort : list nat -> list nat := s.

(** Boolean accumulator predicate: checks non-decreasing order starting from acc *)
Fixpoint P (y : list nat) (acc: nat) {struct y}: bool :=
  match y with
  | [] => true
  | yh :: yt =>
    match le_dec acc yh with
    | left _ => P yt yh
    | right _ => false
    end
  end.

(** Boolean sortedness predicate *)
Fixpoint ord (x : list nat) {struct x}: bool :=
  match x with
  | [] => true
  | xh :: xt =>
    match xt with
    | [] => true
    | xth :: xtt =>
      match le_dec xh xth with
      | left _ => ord xt
      | right _ => false
      end
    end
  end.

(** ========================================================================= *)
(** SECTION 1: PERMUTATION PRESERVATION                                       *)
(** ========================================================================= *)

Lemma ins_perm : forall (a: nat) (l: list nat),
  Permutation (a :: l) (ins a l).
Proof.
  intros a l. induction l as [| y yt IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (le_dec a y) as [Hle | Hnle].
    + apply Permutation_refl.
    + eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip. apply IH.
Qed.

Theorem sort_perm : forall (l: list nat),
  Permutation l (s l).
Proof.
  intros l. induction l as [| x xt IH].
  - simpl. apply Permutation_refl.
  - simpl. eapply Permutation_trans.
    + apply perm_skip. apply IH.
    + apply ins_perm.
Qed.

(** ========================================================================= *)
(** SECTION 2: SORTEDNESS PRESERVATION                                        *)
(** ========================================================================= *)

Lemma ins_hdrel : forall (a x: nat) (l: list nat),
  x <= a ->
  HdRel le x l ->
  HdRel le x (ins a l).
Proof.
  intros a x l Hxa Hx.
  destruct l as [| y yt].
  - simpl. constructor. exact Hxa.
  - simpl. destruct (le_dec a y) as [Hle | Hnle].
    + constructor. exact Hxa.
    + constructor. inversion Hx as [| ? ? Hxy]; subst. exact Hxy.
Qed.

Lemma ins_sorted : forall (a: nat) (l: list nat),
  Sorted le l ->
  Sorted le (ins a l).
Proof.
  intros a l H. induction H as [| x xs Hxs IH Hx_xs].
  - simpl. constructor; [constructor | constructor].
  - simpl. destruct (le_dec a x) as [Hle | Hnle].
    + constructor.
      * constructor; [exact Hxs | exact Hx_xs].
      * constructor. exact Hle.
    + apply Nat.nle_gt in Hnle.
      assert (Hxa : x <= a) by (apply Nat.lt_le_incl; exact Hnle).
      constructor.
      * apply IH.
      * apply ins_hdrel; [exact Hxa | exact Hx_xs].
Qed.

Theorem sort_sorted : forall (l: list nat),
  Sorted le (s l).
Proof.
  intros l. induction l as [| x xt IH].
  - simpl. constructor.
  - simpl. apply ins_sorted. exact IH.
Qed.

(** Total correctness of insertion sort *)
Theorem insertion_sort_correct : forall (l: list nat),
  Permutation l (s l) /\ Sorted le (s l).
Proof.
  intros l. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.

(** ========================================================================= *)
(** SECTION 3: IDEMPOTENCE AND FIXPOINT THEOREMS                              *)
(** ========================================================================= *)

Lemma ins_sorted_id : forall (x: nat) (l: list nat),
  HdRel le x l ->
  ins x l = x :: l.
Proof.
  intros x l H.
  destruct l as [| y yt].
  - simpl. reflexivity.
  - simpl. inversion H as [| ? ? Hxy]; subst.
    destruct (le_dec x y) as [Hle | Hnle].
    + reflexivity.
    + exfalso. apply Hnle. exact Hxy.
Qed.

Theorem sorted_fix : forall (l: list nat),
  Sorted le l ->
  s l = l.
Proof.
  intros l H. induction H as [| x xs Hxs IH Hx_xs].
  - simpl. reflexivity.
  - simpl. rewrite IH. apply ins_sorted_id. exact Hx_xs.
Qed.

Theorem proj : forall (x: list nat),
  s (s x) = s x.
Proof.
  intros x. apply sorted_fix. apply sort_sorted.
Qed.

(** ========================================================================= *)
(** SECTION 4: EQUIVALENCE OF INDUCTIVE AND BOOLEAN SORTEDNESS                *)
(** ========================================================================= *)

Lemma ord_step : forall (x y: nat) (ys: list nat),
  ord (x :: y :: ys) = (if le_dec x y then ord (y :: ys) else false).
Proof.
  intros. destruct ys; reflexivity.
Qed.

Lemma sorted_to_ord : forall (l: list nat),
  Sorted le l -> ord l = true.
Proof.
  intros l H. induction H as [| x xs Hxs IH Hx_xs].
  - reflexivity.
  - destruct xs as [| y ys].
    + reflexivity.
    + rewrite ord_step. inversion Hx_xs as [| ? ? Hxy]; subst.
      destruct (le_dec x y) as [Hle | Hnle].
      * exact IH.
      * exfalso. apply Hnle. exact Hxy.
Qed.

Lemma ord_to_sorted : forall (l: list nat),
  ord l = true -> Sorted le l.
Proof.
  induction l as [| x xs IH].
  - intros _. constructor.
  - destruct xs as [| y ys].
    + intros _. constructor; [constructor | constructor].
    + rewrite ord_step. destruct (le_dec x y) as [Hle | Hnle].
      * intros Hord. constructor.
        -- apply IH. exact Hord.
        -- constructor. exact Hle.
      * intros H. discriminate H.
Qed.

Theorem ord_iff_sorted : forall (l: list nat),
  ord l = true <-> Sorted le l.
Proof.
  intros l; split.
  - apply ord_to_sorted.
  - apply sorted_to_ord.
Qed.

Theorem sort_ord : forall (l: list nat),
  ord (s l) = true.
Proof.
  intros l. apply sorted_to_ord. apply sort_sorted.
Qed.

Theorem ord_then_fix : forall (x: list nat),
  ord x = true -> s x = x.
Proof.
  intros x H. apply sorted_fix. apply ord_to_sorted. exact H.
Qed.

Theorem head_reduct : forall (xh: nat) (xt: list nat),
  ord (xh :: xt) = true -> ord xt = true.
Proof.
  intros xh xt H.
  apply ord_to_sorted in H.
  inversion H as [| ? ? Hsort_xt Hhd]; subst.
  apply sorted_to_ord. exact Hsort_xt.
Qed.

(** ========================================================================= *)
(** SECTION 5: ACCUMULATOR PREDICATE EQUIVALENCE                              *)
(** ========================================================================= *)

Lemma P_iff_sorted_hd : forall (l: list nat) (acc: nat),
  P l acc = true <-> (Sorted le l /\ HdRel le acc l).
Proof.
  induction l as [| y yt IH]; intros acc.
  - simpl. split.
    + intros _. split; constructor.
    + intros _. reflexivity.
  - simpl. destruct (le_dec acc y) as [Hle | Hnle].
    + rewrite IH. split.
      * intros [Hsort Hhd]. split.
        -- constructor; [exact Hsort | exact Hhd].
        -- constructor. exact Hle.
      * intros [Hsort Hhd]. inversion Hsort; subst. split; assumption.
    + split.
      * intros H; discriminate H.
      * intros [_ Hhd]. inversion Hhd as [| ? ? Hxy]; subst. exfalso. apply Hnle. exact Hxy.
Qed.

Require Import Bool.

Lemma hdrel_zero : forall (l: list nat),
  HdRel le 0 l.
Proof.
  destruct l.
  - constructor.
  - constructor. apply Nat.le_0_l.
Qed.

Theorem thmeq : forall (x: list nat),
  ord x = P x 0.
Proof.
  intros x. apply Bool.eq_true_iff_eq.
  rewrite ord_iff_sorted.
  rewrite P_iff_sorted_hd.
  split.
  - intros Hsort. split.
    + exact Hsort.
    + apply hdrel_zero.
  - intros [Hsort _]. exact Hsort.
Qed.

Theorem sort_P_zero : forall (l: list nat),
  P (s l) 0 = true.
Proof.
  intros l. rewrite <- thmeq. apply sort_ord.
Qed.

(**
 * Note on original aborted 'pred':
 * The original lemma 'pred xh xt : P (s (xh::xt)) xh = true' does not hold
 * unconditionally because xh is not guaranteed to be the minimum of xh::xt.
 * When xh <= all elements of l, P (s l) xh = true does hold.
 *)
Theorem pred_bounded : forall (l: list nat) (g: nat),
  (forall x, In x l -> g <= x) ->
  P (s l) g = true.
Proof.
  intros l g Hbound.
  rewrite P_iff_sorted_hd.
  split.
  - apply sort_sorted.
  - destruct (s l) as [| h t] eqn:Esl.
    + constructor.
    + constructor.
      assert (Hin : In h (s l)) by (rewrite Esl; simpl; left; reflexivity).
      apply (Permutation_in h (Permutation_sym (sort_perm l))) in Hin.
      apply Hbound. exact Hin.
Qed.

(** ========================================================================= *)
(** SECTION 6: KEY-BASED GENERIC INSERTION SORT AND STABILITY PROOF             *)
(** ========================================================================= *)

Section KeySort.
  Variable A : Type.
  Variable key : A -> nat.

  Fixpoint key_ins (a: A) (y: list A) {struct y}: list A :=
    match y with
    | [] => [a]
    | yh :: yt =>
      match le_dec (key a) (key yh) with
      | left _ => a :: yh :: yt
      | right _ => yh :: key_ins a yt
      end
    end.

  Fixpoint key_sort (x: list A) {struct x}: list A :=
    match x with
    | [] => []
    | xh :: xt => key_ins xh (key_sort xt)
    end.

  Lemma filter_key_ins : forall (k: nat) (a: A) (l: list A),
    filter (fun x => Nat.eqb (key x) k) (key_ins a l) =
    if Nat.eqb (key a) k
    then a :: filter (fun x => Nat.eqb (key x) k) l
    else filter (fun x => Nat.eqb (key x) k) l.
  Proof.
    intros k a l. induction l as [| y yt IH].
    - simpl. destruct (Nat.eqb (key a) k); reflexivity.
    - simpl. destruct (le_dec (key a) (key y)) as [Hle | Hnle].
      + simpl. destruct (Nat.eqb (key a) k); reflexivity.
      + simpl. destruct (Nat.eqb (key y) k) eqn:Eyk.
        * apply Nat.eqb_eq in Eyk.
          apply Nat.nle_gt in Hnle.
          assert (Eak: (key a =? k) = false).
          { apply Nat.eqb_neq. intros Heq. subst k.
            rewrite Heq in Hnle.
            apply (Nat.lt_irrefl (key y) Hnle). }
          rewrite Eak. rewrite IH. rewrite Eak. reflexivity.
        * rewrite IH. reflexivity.
  Qed.

  (** Formal Stability Theorem:
      For any key value k, the filtered subsequence of items with key k in
      the sorted list is identical to the filtered subsequence in the original list.
   *)
  Theorem key_sort_stable : forall (k: nat) (l: list A),
    filter (fun x => Nat.eqb (key x) k) (key_sort l) =
    filter (fun x => Nat.eqb (key x) k) l.
  Proof.
    intros k l. induction l as [| x xt IH].
    - simpl. reflexivity.
    - simpl. rewrite filter_key_ins.
      rewrite IH. reflexivity.
  Qed.

End KeySort.

Theorem key_sort_id_eq_s : forall (l: list nat),
  key_sort nat (fun (x: nat) => x) l = s l.
Proof.
  induction l as [| x xt IH].
  - simpl. reflexivity.
  - simpl. rewrite IH.
    assert (Hins: forall a ys, key_ins nat (fun x => x) a ys = ins a ys).
    { clear x xt IH. intros a ys. induction ys as [| y yt IHy].
      - reflexivity.
      - simpl. destruct (le_dec a y); [reflexivity | rewrite IHy; reflexivity]. }
    apply Hins.
Qed.

(** ========================================================================= *)
(** SECTION 7: CODE EXTRACTION                                                *)
(** ========================================================================= *)

Require Extraction.
Extraction Language OCaml.
Extraction "sort.ml" ins s key_ins key_sort.
