Require Import Reals.
Require Import QWIRE.Matrix.

Definition Herm {n: nat} (A : Square n) : Prop :=
  forall i j, (A i j) = Cconj (A j i).

Lemma herm_diag_real {n : nat} (A : Square n) :
  forall (i : nat) (x : C), Herm A -> (i < n)%nat -> A i i = x -> snd x = 0.
Proof. Admitted.

Definition Diagonal {n : nat} (A : Square n) :=
  forall i j, i <> j ->  A i j = 0.

Definition Diagonalization {n : nat} (M D T Tinv : Square n) : Prop :=
  Minv T Tinv /\ M = Tinv × D × T.

(* element-wise exponentiation of a diagonal matrix *)
Definition exp_diag {n : nat} (D : Square n) :=
  (fun i j => if (i <? n) && (i =? j) then exp (fst (D i j)) else 0).

Definition exp_herm {n : nat} (M_exp M : Square n) : Prop :=
  exists (Tinv D T : Square n),
    Diagonalization M D T Tinv /\ Diagonalization M_exp (exp_diag D) T Tinv.

(* technical debt *)

