Require Import Reals.
Require Import QWIRE.Matrix.


(*
     -----  Definitions  -----
 *)

Definition Herm {n: nat} (A : Square n) : Prop :=
  forall i j, (A i j) = Cconj (A j i).

Definition Diagonal {n : nat} (A : Square n) :=
  forall i j, i <> j ->  A i j = 0.

Definition Diagonalization {n : nat} (M Tinv D T : Square n) : Prop :=
  Diagonal D /\ Minv T Tinv /\ M = Tinv × D × T.

Definition Diagonalizable {n : nat} (A : Square n) :=
  exists (Tinv D T : Square n),
    Diagonalization A Tinv D T.

(* element-wise exponentiation of a diagonal matrix *)
Definition exp_diag {n : nat} (D : Square n) :=
  (fun i j => if (i <? n) && (i =? j) then exp (fst (D i j)) else 0).

Definition exp_herm {n : nat} (M_exp M : Square n) : Prop :=
  exists (Tinv D T : Square n),
    Diagonalization M Tinv D T /\ Diagonalization M_exp Tinv (exp_diag D) T.

(*
Theorem exp_herm {n : nat} (M_exp M D T Tinv : Square n) :
  Diagonalization M Tinv D T ->  
  Diagonalization M_exp Tinv (exp_diag D) T.
 *)

(* Simultaneously diagonalizable *)
Definition Sim_diag {n : nat} (A B : Square n) :=
  exists (T Tinv M1 M2 : Square n),
    Diagonalization M1 Tinv A T /\ Diagonalization M2 Tinv B T.

Definition Mat_commute {n : nat} (A B : Square n) :=
  A × B = B × A.



(*
     -----  Theorems  -----
 *)

Lemma real_neg_neq : forall (x : R), x <> 0 -> x <> Ropp x.
Proof.
  intros. intros H1.
  destruct (Rlt_dec x 0).
  - assert (H2 : Ropp x > 0). {
      apply Ropp_gt_lt_0_contravar in r. assumption. }
    rewrite <- H1 in H2.
    apply Rlt_le in r. apply Rle_not_gt in r. contradiction.
  - apply Rnot_lt_ge in n. apply Rge_le in n.
    assert (H2 : 0 >= Ropp x). {
      apply Ropp_0_le_ge_contravar in n. assumption. }
    assert (H3 : 0 < x). {
      inversion n. assumption. symmetry in H0. contradiction. }
    rewrite <- H1 in H2. apply Rge_not_lt in H2.
    contradiction.
Qed.

Theorem herm_diag_real {n : nat} (A : Square n) :
  forall (i : nat) (x : C), Herm A -> (i < n)%nat -> A i i = x -> snd x = 0.
Proof.
  intros. unfold Herm in H. unfold Cconj in H.
  remember (H i i) as H2.
  clear HeqH2. rewrite surjective_pairing in H1.
  rewrite H1 in H2. inversion H2. 
  destruct (Req_dec (snd x) 0).
  - assumption.
  - apply real_neg_neq in H3. contradiction.
Qed.

Theorem herm_diagonalizable {n : nat} (A : Square n) :
  Herm A -> Diagonalizable A.
Proof.
  Admitted.

(* Diagonal matrices commute *)
Lemma diag_commute {n : nat} :
  forall (D1 D2 : Square n), Diagonal D1 -> Diagonal D2 -> Mat_commute D1 D2.
Proof.
  (* Not 100% sure we'll need this lemma. Might want to wait to complete the proof *)
  Admitted.


(* Commuting diagonalizable matrices are simultaneously diagonalizable *)
Theorem Commute_sim_diag {n : nat} :
  forall (A B : Square n),
  Mat_commute A B ->
  Diagonalizable A ->
  Diagonalizable B ->
  (* We might need the explicit diagonalizations for the proof :
  forall TAinv TBinv DA DB TA TB
  Diagonalization A TAinv DA TA ->
  Diagonalization B TBinv DB TB ->
  *)
  Sim_diag A B.
Proof.
  (* This is gonna be a doozy *)
  Admitted.
