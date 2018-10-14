
Require Import List.
Import ListNotations.
Require Import Arith.
Fixpoint ins (a:nat) (y:list nat) {struct y}: list nat.
Proof.
refine (match y with
        | [] => [a] 
        | yh::yt => _
        end).
pose (r:= le_dec a yh).
destruct r as [L|R].
exact (a::yt).
exact (yh::(ins a yt)).
Defined.

Fixpoint s (x:list nat) {struct x}: list nat 
:=     (match x with
        | [] => [] 
        | xh::xt => ins xh (s xt)
        end).

Fixpoint P (y : list nat) (acc:nat) {struct y}: bool.
Proof.
refine (match y with
        | [] => true
        | yh::yt => _
        end).
pose (r:= le_dec acc yh).
destruct r as [L|R].
+ exact (P yt yh).
+ exact false.
Defined.

(*Theorem le_dec xh xh*)

Theorem pred xh xt : P (s (xh::xt)) xh = true.
Proof.
simpl.
induction xt.
+ simpl.
destruct (le_dec xh xh).
reflexivity.
exfalso.
apply n.
reflexivity.
+ simpl.
Abort.
Theorem pred xt :forall g, P (s xt) g = true.
Proof.
simpl.
induction xt.
+ simpl.
(*destruct (le_dec xh xh).*)
reflexivity.
(*exfalso.
apply n.
reflexivity.*)
+ simpl.
intro g.
Abort.

Check le_ge_dec.
Check le_dec.

Theorem proj x : s (s x) = s x.
Proof.
induction x.
+ simpl. reflexivity.
+ simpl.
rewrite <- IHx at 1.
fold s.
(*change (ins a (s (s x))) to (a :: (s x)).
fold (a :: (s x)).
simpl.
compute.*)
Abort.


Fixpoint ord (x : list nat) {struct x}: bool.
Proof.
refine (match x with
        | [] => true
        | xh::xt => _
        end).
refine (match xt with
        | [] => true
        | xth::xtt => _
        end).
pose (r:= le_dec xh xth).
destruct r as [L|R].
+ exact (ord xt).
+ exact false.
Defined.

Theorem thmeq x : ord x = P x 0.
Proof.
induction x.
simpl. reflexivity.
simpl.
induction a.
simpl.
destruct x.
simpl. reflexivity.
apply IHx.
destruct x.
simpl in * |- *. reflexivity.
simpl in * |- *.
destruct (le_dec (S a) n).
exact IHx.
reflexivity.
Defined.

Theorem head_reduct xh xt (H:ord (xh :: xt) = true) : ord xt = true.
Proof.
simpl in H.
destruct xt.
+ simpl. reflexivity.
+ destruct (le_dec xh n).
  * exact H.
  * inversion H.
Defined.

Theorem ord_then_fix x (H: (ord x)=true) : (s x)=x.
Proof.
induction x as [|a b].
+ simpl. reflexivity.
+ destruct b. 
  * simpl. reflexivity.
  * pose (D:= head_reduct _ _ H).
    pose (M:= IHb D).
(*simpl.
 simpl in * |- *. *)
Abort.