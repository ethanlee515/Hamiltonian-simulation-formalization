Require Import Reals.
Require Import QWIRE.Matrix.
Require Import Omega.

Definition Herm {n: nat} (A : Square n) : Prop :=
  forall i j, (A i j) = Cconj (A j i).

Lemma real_neg_neq : forall (x : R), x <> 0 -> x <> Ropp x.
Proof.
  intros. intros H1.
  destruct (Rlt_dec x 0).
  - assert (H2 : Ropp x > 0). {
      apply Ropp_gt_lt_0_contravar in r. assumption. }.
    rewrite <- H1 in H2.
    apply Rlt_le in r. apply Rle_not_gt in r. contradiction.
  - apply Rnot_lt_ge in n. apply Rge_le in n.
    assert (H2 : 0 >= Ropp x). {
      apply Ropp_0_le_ge_contravar in n. assumption. }.
    assert (H3 : 0 < x). {
      inversion n. assumption. symmetry in H0. contradiction. }.
    rewrite <- H1 in H2. apply Rge_not_lt in H2.
    contradiction.
Qed.

Lemma herm_diag_real {n : nat} (A : Square n) :
  forall (i : nat) (x : C), Herm A -> (i < n)%nat -> A i i = x -> snd x = 0.
Proof. intros. unfold Herm in H. unfold Cconj in H.
       remember (H i i) as H2.
       clear HeqH2. rewrite surjective_pairing in H1.
       rewrite H1 in H2. inversion H2. 
       destruct (Req_dec (snd x) 0).
       - assumption.
       - apply real_neg_neq in H3. contradiction.
Qed.

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

