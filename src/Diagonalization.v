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
  Diagonal D /\ Minv T Tinv /\ M = Tinv × D × T /\
  WF_Matrix Tinv /\ WF_Matrix D /\ WF_Matrix T. 

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

Lemma herm_scale {n : nat} : forall (M : Square n) (r : R),
    Herm M -> Herm (r .* M).
Proof.
  intros M r H. unfold ".*". unfold Herm in *.
  intros i j. rewrite Cconj_mult_distr.
  rewrite <- H. rewrite Cconj_R.
  reflexivity.
Qed.
  
Lemma herm_plus {n : nat} : forall (A B : Square n), Herm A -> Herm B -> Herm (A .+ B).
Proof.
  intros. unfold Herm in *. intros i j.
  unfold ".+". rewrite Cconj_plus_distr.
  rewrite <- H. rewrite <- H0. reflexivity.
Qed.
  
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
Proof. Admitted.

Lemma exp_diag_preserves_WF {n : nat} :
  forall (D : Square n), WF_Matrix D -> Diagonal D -> @WF_Matrix n n (exp_diag D).
Proof.
  intros D HWF HD i j H. unfold exp_diag.
  destruct (i =? j) eqn:E.
  - apply beq_nat_true in E. subst. destruct (j <? n) eqn:F.
    + exfalso. apply Nat.ltb_lt in F. lia.
    + auto.
  - rewrite andb_false_r. auto.
Qed.
  
Lemma exp_diag_preserves_diag {n : nat} :
  forall (D : Square n), Diagonal D -> @Diagonal n (exp_diag D).
Proof.
  intros D H i j Hij. unfold exp_diag. apply eqb_neq in Hij.
  rewrite Hij. rewrite andb_false_r. reflexivity.
Qed.

Lemma diagonal_scale {n : nat} : forall (M : Square n) (c : C),
    Diagonal M -> Diagonal (c .* M).
Proof. 
  intros. unfold Diagonal in *. intros i j Hij.
  unfold ".*". assert (H1 : M i j = 0). apply H. apply Hij.
  rewrite H1. apply Cmult_0_r.
Qed.
  
Lemma diag_scale {n : nat} : forall (M : Square n) (c : C),
    Diagonalizable M -> Diagonalizable (c .* M).
Proof.
  intros. unfold Diagonalizable in *.
  destruct H as [Tinv [D [T [H1 [H2 [H3 [H4 [H5 H6]]]]]]]].
  exists Tinv, (c .* D), T. unfold Diagonalization.
  repeat (split; try tauto).
  - apply diagonal_scale. auto.
  - rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
    rewrite <- H3. reflexivity.
  - apply WF_scale. auto.
Qed.

  
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




Theorem mat_exp_well_defined_diag {n : nat} : forall (M : Square n),
    Diagonalizable M -> exists (Mexp : Square n), matrix_exponential M Mexp.
Proof.
  intros M H. remember H as Hd. clear HeqHd.
  unfold Diagonalizable in Hd.
  destruct Hd as [Tinv [D [T [H1 [H2 [H3 [H4 [H5 H6]]]]]]]].
  exists (Tinv × (exp_diag D) × T).
  rewrite exp_diag_correct; auto.
  unfold is_exp_diag.
  exists Tinv. exists D. exists T. split.
  - unfold Diagonalization; tauto.
  - unfold Diagonalization. repeat (try split; try tauto).
    + apply exp_diag_preserves_diag; auto.
    + apply exp_diag_preserves_WF; auto.
Qed.

Corollary mat_exp_well_defined_herm {n : nat} : forall (M : Square n),
    Herm M -> exists (Mexp : Square n), matrix_exponential M Mexp.
Proof.
  intros M H. apply mat_exp_well_defined_diag. apply herm_diagonalizable. auto.
Qed.

Theorem mat_exp_unique_diag {n : nat} : forall (M Mexp1 Mexp2 : Square n),
    Diagonalizable M ->
    matrix_exponential M Mexp1 ->
    matrix_exponential M Mexp2 ->
    Mexp1 = Mexp2.
Proof.
  intros M Mexp1 Mexp2 Hdiag H1 H2.
  rewrite (exp_diag_correct M Mexp1) in H1.
  - destruct H1 as [T1inv [D1 [T1 [HD1 HeD1]]]].
    rewrite (exp_diag_correct M Mexp2) in H2.
    + destruct H2 as [T2inv [D2 [T2 [HD2 HeD2]]]].
      assert (H : T1inv × D1 × T1 = T2inv × D2 × T2). {
        apply equivalent_diagonalizations with M; assumption.
      }
      assert (H1 : T1inv × (exp_diag D1) × T1 = T2inv × (exp_diag D2) × T2). {
        apply exp_diag_preserves_equality; unfold Diagonalization in *; tauto.
      }
      destruct HeD1 as [_ [_ [H2 [_ [_ _]]]]].
      destruct HeD2 as [_ [_ [H3 [_ [_ _]]]]].
      rewrite H2. rewrite H3. auto.
    + auto.
  - auto.
Qed.


Corollary mat_exp_unique_herm {n : nat} : forall (M Mexp1 Mexp2 : Square n) (c : C),
    Herm M ->
    matrix_exponential (c .* M) Mexp1 ->
    matrix_exponential (c .* M) Mexp2 ->
    Mexp1 = Mexp2.
Proof.
  intros M Mexp1 Mexp2 c Hdiag H1 H2.
  apply mat_exp_unique_diag with (c .* M); auto.
  apply diag_scale. apply herm_diagonalizable. apply Hdiag.
Qed.

Theorem mat_exp_WF_diag {n : nat} : forall (M Mexp : Square n),
    Diagonalizable M -> matrix_exponential M Mexp -> WF_Matrix M -> WF_Matrix Mexp.
Proof.
  intros M Mexp Hherm HM H_WF.
  rewrite (exp_diag_correct M Mexp) in HM.
  - destruct HM as [Tinv [D [T [HD HeD]]]].
    destruct HD as  [H1 [H2 [H3 [H4 [H5 H6]]]]].
    destruct HeD as [H7 [H8 [H9 [H10 [H11 H12]]]]].
    rewrite H9. apply WF_mult; auto.
    apply WF_mult; auto.
  - auto.
Qed.

Corollary mat_exp_WF_herm {n : nat} : forall (M Mexp : Square n) (c : C),
    Herm M -> matrix_exponential (c .* M) Mexp -> WF_Matrix M -> WF_Matrix Mexp.
Proof.
  intros M Mexp c Hherm HM H_WF.
  apply mat_exp_WF_diag with (c .* M); auto.
  - apply diag_scale. apply herm_diagonalizable. auto.
  - apply WF_scale. auto.
Qed.

Theorem mat_exp_commute_add_diag {n : nat} : forall (M N SM SN SMN : Square n),
    Diagonalizable M ->
    Diagonalizable N ->
    matrix_exponential M SM ->
    matrix_exponential N SN ->
    matrix_exponential (M .+ N) SMN ->
    Mat_commute M N ->
    SM × SN = SMN.
Proof. Admitted. (*
  intros M N SM SN SMN c1 c2 HM HN HSM HSN HSMN Hcomm.
  rewrite (exp_diag_correct M SM) in HSM; try apply herm_diagonalizable; auto.
  rewrite (exp_diag_correct N SN) in HSN; try apply herm_diagonalizable; auto.
  rewrite (exp_diag_correct (M .+ N) SMN) in HSMN;
    try (apply herm_diagonalizable; apply herm_plus; auto).  
  destruct HSM as [TMinv [DM [TM [HDM [HeDM [_ [_ _]]]]]]].
  destruct HSN as [TNinv [DN [TN [HDN [HeDN [_ [_ _]]]]]]].
  destruct HSMN as [TMNinv [DMN [TMN [HDMN [HeDMN [_ [_ _]]]]]]].
  Admitted. *)


