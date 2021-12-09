Require Import Reals.
Require Import QWIRE.Matrix.
Require Import MatrixExponential.
Require Import Init.Tauto.

(*
     -----  Definitions  -----
 *)

Definition Herm {n: nat} (A : Square n) : Prop :=
  forall i j, (A i j) = Cconj (A j i).

Definition Diagonal {n : nat} (A : Square n) :=
  forall i j, i <> j ->  A i j = 0.

Definition Diagonalization {n : nat} (Tinv D T M : Square n) : Prop :=
  Diagonal D /\ Minv T Tinv /\ M = Tinv × D × T.

Definition Diagonalizable {n : nat} (A : Square n) :=
  exists (Tinv D T : Square n),
    Diagonalization Tinv D T A.

(* element-wise exponentiation of a diagonal matrix *)
Definition exp_diag {n : nat} (D : Square n) :=
  (fun i j => if (i <? n) && (i =? j) then exp (fst (D i j)) else 0).

Definition is_exp_diag {n : nat} (M M_exp : Square n) : Prop :=
  exists (Tinv D T : Square n),
    Diagonalization Tinv D T M /\ Diagonalization Tinv (exp_diag D) T M_exp.

(* Simultaneously diagonalizable *)
Definition Sim_diag {n : nat} (A B : Square n) :=
  exists (T Tinv M1 M2 : Square n),
    Diagonalization Tinv A T M1 /\ Diagonalization Tinv B T M2.

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

Lemma herm_diag_real {n : nat} (A : Square n) :
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

Lemma herm_Zero {n : nat} : Herm (@Zero n n).
Proof.
  intros i j. unfold Cconj.  unfold Zero. simpl.
  rewrite Ropp_0. reflexivity.
Qed.

Lemma herm_I {n : nat} : Herm (I n).
Proof.
  unfold Herm. unfold Cconj. unfold I.
  intros i j. rewrite <- (Nat.eqb_sym i j).
  destruct (i =? j) eqn:E.
  - assert (Hij : i = j). apply Nat.eqb_eq. assumption. subst.
    destruct (j <? n); simpl; rewrite Ropp_0; reflexivity.
  - simpl. rewrite Ropp_0; reflexivity.
Qed.

Lemma herm_scale {n : nat} : forall (M : Square n) (c : C),
    Herm M -> Herm (c .* M).
Proof. Admitted.

Lemma herm_plus {n : nat} : forall (A B : Square n), Herm A -> Herm B -> Herm (A .+ B).
Proof. Admitted.

(* The converse of this is also true *)
Lemma herm_mult {n : nat} : forall (A B : Square n),
    Herm A -> Herm B -> Mat_commute A B -> Herm (A × B).
Proof. Admitted.

Lemma herm_kron {n m : nat} : forall (A : Square n) (B : Square m),
    Herm A -> Herm B -> Herm (A ⊗ B).
Proof. Admitted.

Lemma herm_big_kron {n : nat} : forall (L : list (Square n)),
    Forall Herm L -> Herm (⨂ L).
Proof.
  intros L H.
  induction L as [|A L'].
  - apply herm_I.
  - simpl. apply herm_kron.
    + apply Forall_inv in H. assumption.
    + apply IHL'. apply Forall_inv_tail with A. assumption.
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
  Diagonalization TAinv DA TA A ->
  Diagonalization TBinv DB TB B ->
  *)
  Sim_diag A B.
Proof.
  (* This is gonna be a doozy *)
  Admitted.


Theorem exp_diag_correct {n : nat} (M M_exp : Square n) :
    Diagonalizable M -> matrix_exponential M M_exp <-> is_exp_diag M M_exp.
Proof.
    Admitted.


Lemma diag_scale {n : nat} : forall (M : Square n) (c : C),
    Diagonalizable M -> Diagonalizable (c .* M).
Proof. Admitted.

Lemma equivalent_diagonalizations {n : nat}:
  forall (T1inv D1 T1 T2inv D2 T2 M : Square n),
    Diagonalization T1inv D1 T1 M ->
    Diagonalization T2inv D2 T2 M ->
    T1inv × D1 × T1 = T2inv × D2 × T2.
Proof. Admitted.

Lemma exp_diag_preserves_equality {n : nat} :
  forall (A B C D E F : Square n),
    Diagonal B -> Diagonal E ->
    A × B × C = D × E × F ->
    A × (exp_diag B) × C = D × (exp_diag E) × F.
Proof. Admitted.

Lemma mat_exp_unique_herm {n : nat} : forall (M Mexp1 Mexp2 : Square n) (c : C),
    Herm M ->
    matrix_exponential (c .* M) Mexp1 ->
    matrix_exponential (c .* M) Mexp2 ->
    Mexp1 = Mexp2.
Proof.
  intros M Mexp1 Mexp2 c Hdiag H1 H2. apply herm_diagonalizable in Hdiag.
  rewrite (exp_diag_correct (c .* M) Mexp1) in H1.
  - destruct H1 as [T1inv [D1 [T1 [HD1 HeD1]]]].
    rewrite (exp_diag_correct (c .* M) Mexp2) in H2.
    + destruct H2 as [T2inv [D2 [T2 [HD2 HeD2]]]].
      assert (H : T1inv × D1 × T1 = T2inv × D2 × T2). {
        apply equivalent_diagonalizations with (c .* M); assumption.
      }
      assert (H1 : T1inv × (exp_diag D1) × T1 = T2inv × (exp_diag D2) × T2). {
        apply exp_diag_preserves_equality; unfold Diagonalization in *; tauto.
      }
      destruct HeD1 as [_ [_ H2]]. destruct HeD2 as [_ [_ H3]].
      rewrite H2. rewrite H3. auto.
    + apply diag_scale; auto.
  - apply diag_scale; auto.
Qed.

Lemma mat_exp_commute_add_herm {n : nat} : forall (M N SM SN SMN : Square n),
    Herm M ->
    Herm N ->
    matrix_exponential M SM ->
    matrix_exponential N SN ->
    matrix_exponential (M .+ N) SMN ->
    Mat_commute M N ->
    SM × SN = SMN.
Proof. Admitted.
