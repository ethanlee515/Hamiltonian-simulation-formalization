(** -- MatrixExponential.v -- **)
(**
 * Defines matrix exponentiation and its preliminaries.
 * Proves some basic properties as well.
 *)

Require Import Reals QWIRE.Matrix.
Require Import Complex.
Require Import Lra.
Require Import Coq.Logic.ProofIrrelevance.

(* -- Sequence convergence in metric space -- *)

(* Somehow this isn't in the standard library.
 * We have limit_in, but that's for N goes to an actual value as opposed to infty
 *)
(* Print limit_in. *)

Definition seq_conv (X : Metric_Space) (seq : nat -> Base X) (lim : Base X) :=
    forall eps : R, eps > 0 ->
    exists N : nat, 
        (forall n : nat, (n >= N)%nat -> X.(dist) (seq n) lim < eps).

(* -- Well-formed matrices type -- *)
(* The properties we're interested in require well-formedness *)

Definition WF_Square {n : nat} : Type := { m : (@Square n) | WF_Matrix m }.

Definition zero_wf {n : nat} : (@WF_Square n) := exist WF_Matrix Zero (@WF_Zero n n).

Definition plus_wf {n : nat} (m1 m2 : @WF_Square n) :=
  exist WF_Matrix ((`m1) .+ (`m2)) (WF_plus (`m1) (`m2) (proj2_sig m1) (proj2_sig m2)).

Definition scale_wf {n : nat} (r : C) (m : @WF_Square n) :=
  exist WF_Matrix (scale r (`m)) (WF_scale r (`m) (proj2_sig m)).

Definition mmult_wf {n : nat} (k : nat) (m : @WF_Square n) :=
  exist WF_Matrix (Mmult_n k (`m)) (WF_Mmult_n k (`m) (proj2_sig m)).

Definition mult_wf {n : nat} (m1 m2 : @WF_Square n) :=
  exist WF_Matrix (Mmult (`m1) (`m2)) (WF_mult (`m1) (`m2) (proj2_sig m1) (proj2_sig m2)).

Declare Scope wf_scope.
Open Scope wf_scope.

Infix ".+" := plus_wf (at level 50, left associativity) : wf_scope.
Infix ".*" := scale_wf (at level 40, left associativity) : wf_scope.
Infix "×" := mult_wf (at level 40, left associativity) : wf_scope.
Notation "k ⨉ m" := (mmult_wf k m) (at level 30, no associativity) : wf_scope.

(* -- Showing that matrices form a metric space -- *)

(* We could define operator norm and show that the norm induces a metric...
 * but that's too much real analysis.
 * I think we'll be cheap today and go with infinity norm.
 *
 * We start with taking max over a real matrix, since it will be useful later.
 *)

(* TODO define max? *)

Print Matrix.

Definition RealSquare (n : nat) := nat -> nat -> R.

Definition isWF_ReSq {n : nat} (M : RealSquare n) : Prop :=
  forall (x y : nat), (x >= n \/ y >= n)%nat -> M x y = 0.

Definition WF_RSquare {n : nat} : Type := { m : (@RealSquare n) | isWF_ReSq m }.

Fixpoint rSqMax_aux {n : nat}
                     (mat : RealSquare n)
                     (i : nat)
                     (currentMax : R)
                     (currentR currentC : nat)
                     : R * (nat * nat) :=
  let r := (i / n)%nat in
  let c := (i mod n)%nat in
  let elem := mat r c in
  (* Apparently this works... *)
  let '(newMax, newR, newC) :=
    if Rlt_dec elem currentMax then 
      (currentMax, currentR, currentC)
    else
      (elem, r, c)
    in
  match i with
  | O => (newMax, (newR, newC))
  | S i' => rSqMax_aux mat i' newMax newR newC
  end.

Lemma rSqMax_aux_nonneg :
  forall n mat idx m r c,
    m >= 0 ->
    (forall i j, mat i j >= 0) ->
    fst (@rSqMax_aux n mat idx m r c) >= 0.
Proof.
  intros.
  generalize dependent m.
  generalize dependent r.
  generalize dependent c.
  induction idx.
  + intros.
    unfold rSqMax_aux.
    destruct (Rlt_dec (mat (0 / n)%nat (0 mod n)) m).
    - auto.
    - simpl. lra.
  + simpl.
    intros.
    destruct (Rlt_dec (mat (S idx / n)%nat (S idx mod n)) m).
    - apply IHidx; auto.
    - apply IHidx. lra.
Qed.

Lemma rSqMax_aux_runningMax_monotonic:
  forall n mat i m1 r1 c1 m2 r2 c2,
    m1 >= m2 ->
    fst (@rSqMax_aux n mat i m1 r1 c1) >= fst (@rSqMax_aux n mat i m2 r2 c2).
Proof.
  intros.
  generalize dependent m2.
  generalize dependent m1.
  generalize dependent r2.
  generalize dependent r1.
  generalize dependent c2.
  generalize dependent c1.
  induction i.
  + simpl.
    intros.
    case (Rlt_dec (mat (0 / n)%nat (0 mod n)) m1).
    * intros.
      case (Rlt_dec (mat (0 / n)%nat (0 mod n)) m2).
      - intro. assumption.
      - intro. simpl. lra.
    * intros.
      apply Rnot_lt_ge in n0.
      simpl.
      case_eq (Rlt_dec (mat (0 / n)%nat (0 mod n)) m2).
      - intros.
        simpl. lra.
      - intros.
        simpl.
        apply Rge_refl.
  + simpl.
    intros.
    case (Rlt_dec (mat (S i / n)%nat (S i mod n))).
    * intros.
      case (Rlt_dec (mat (S i / n)%nat (S i mod n)) m2).
      - intros.
        apply IHi. assumption.
      - intros.
        apply IHi.
        apply Rgt_ge.
        apply Rlt_gt.
        assumption.
    * intros.
      case (Rlt_dec (mat (S i / n)%nat (S i mod n)) m2).
      - intros. lra.
      - lra.
Qed.

Lemma rSqMax_aux_running_max_correct:
  forall n mat i m r c y, m >= y -> fst (@rSqMax_aux n mat i m r c) >= y.
Proof.
  intros.
  induction i.
  + simpl.
    case (Rlt_dec (mat (0 / n)%nat (0 mod n)) m).
    - intro. assumption.
    - intro.
      apply Rnot_lt_ge in n0.
      apply Rge_trans with (r2 := m); assumption.
  + simpl.
    apply Rge_trans with (r2 := fst (rSqMax_aux mat i m r c)).
    - simpl.
      Check rSqMax_aux_runningMax_monotonic.
      case_eq (Rlt_dec (mat (S i / n)%nat (S i mod n)) m).
      * intros.
        apply rSqMax_aux_runningMax_monotonic.
        apply Rge_refl.
      * intros.
        apply rSqMax_aux_runningMax_monotonic.
        lra.
    - assumption.
Qed.

Lemma rSqMax_aux_correct:
  forall n mat i I m r c,
    (i <= I)%nat ->
    m >= 0 ->
    (forall x y, mat x y >= 0) ->
    fst (@rSqMax_aux n mat I m r c) >= mat (i / n)%nat (i mod n)%nat.
Proof.
  intros.
  generalize dependent i.
  generalize dependent m.
  generalize dependent r.
  generalize dependent c.
  induction I.
  + intros.
    simpl.
    assert (i = 0%nat).
      lia.
    subst.
    case_eq (Rlt_dec (mat (0 / n)%nat (0 mod n)) m).
    - intros. simpl. lra.
    - intros. simpl. lra.
  + intros.
    simpl.
    case_eq (i =? S I).
    - rewrite Nat.eqb_eq.
      intro. subst.
      case_eq (Rlt_dec (mat (S I / n)%nat (S I mod n)) m).
      * intros.
        apply rSqMax_aux_running_max_correct.
        lra.
      * intros.
        apply rSqMax_aux_running_max_correct.
        lra.
    - intros.
      case_eq (Rlt_dec (mat (S I / n)%nat (S I mod n)) m).
      * intros.
        apply IHI.
        ** assumption.
        ** intros.
           apply Nat.eqb_neq in H2.
           lia.
      * intros.
        apply IHI.
        apply H1.
        apply Nat.eqb_neq in H2.
        lia.
Qed.

(* Max over a real matrix *)
Definition rSqMax {n : nat} (mat : RealSquare n) := rSqMax_aux mat (n * n - 1) 0 0 0.

Definition inftyNorm {n : nat} (m : Square n) :=
  fst (@rSqMax n (fun r c => Cmod (m r c))).

Lemma if_both_nonneg :
  forall a b c d, a >= 0 -> b >= 0 -> (if Rlt_dec c d then a else b) >= 0.
Proof.
  intros.
  case (Rlt_dec c d); intro; assumption.
Qed.

Lemma inftyNorm_nonneg :
  forall n mat, @inftyNorm n mat >= 0.
Proof.
  unfold inftyNorm.
  intros.
  apply rSqMax_aux_nonneg.
  apply Req_ge_sym.
  reflexivity.
  intros.
  apply Rle_ge.
  apply Cmod_ge_0.
Qed.

Definition inftyNorm_wf {n : nat} (m : @WF_Square n) :=
  inftyNorm (proj1_sig m).

Lemma inftyNormwf_nonneg :
  forall (n : nat) (m : @WF_Square n), inftyNorm_wf m >= 0.
Proof.
  intros.
  unfold inftyNorm_wf.
  apply inftyNorm_nonneg.
Qed.

Lemma inftyNormwf_bound :
  forall (n : nat) (m : @WF_Square n) r c, (n > 0)%nat -> inftyNorm_wf m >= Cmod ((`m) r c).
Proof.
  intros.
  destruct m as [val wf].
  unfold inftyNorm_wf.
  simpl.
  unfold inftyNorm.
  case_eq (r <? n).
  + case_eq (c <? n).
    - intros c_bound r_bound.
      apply Nat.ltb_lt in c_bound.
      apply Nat.ltb_lt in r_bound.
      remember (r * n + c)%nat as index.
      assert (r = (index / n)%nat) as r_val.
        rewrite Heqindex.
        rewrite Nat.div_add_l.
        rewrite Nat.div_small.
        rewrite Nat.add_0_r.
        reflexivity.
        assumption.
        lia.
      rewrite r_val.
      assert (c = (index mod n)) as c_val.
        rewrite Heqindex.
        rewrite Nat.add_comm.
        rewrite Nat.mod_add.
        rewrite Nat.mod_small.
        reflexivity.
        assumption.
        lia.
      rewrite c_val.
      apply rSqMax_aux_correct.
        rewrite Heqindex.
        assert (n * n - 1 = (n * (n - 1)) + (n - 1))%nat as split_index.
          rewrite Nat.add_sub_assoc.
          rewrite mult_n_Sm.
          assert (S (n - 1) = n) as minus_then_plus_1.
            lia.
          rewrite minus_then_plus_1.
          reflexivity.
          lia.
        rewrite split_index.
        apply plus_le_compat.
        rewrite mult_comm.
        apply mult_le_compat_l.
        lia.
        lia.
    - intros.
      unfold WF_Matrix in wf.
      apply Nat.ltb_nlt in H0.
      assert (r >= n \/ c >= n)%nat as out_of_bound.
        lia.
      apply wf in out_of_bound.
      rewrite out_of_bound.
      rewrite Cmod_0.
      apply inftyNorm_aux_nonneg.
        apply Rge_refl.
  + intros.
    unfold WF_Matrix in wf.
    apply Nat.ltb_nlt in H0.
    assert (r >= n \/ c >= n)%nat as out_of_bound.
      lia.
    apply wf in out_of_bound.
    rewrite out_of_bound.
    rewrite Cmod_0.
    apply inftyNorm_aux_nonneg.
      apply Rge_refl.
Qed.

Lemma inftyNorm_zero_aux :
  forall (n : nat) (m : @WF_Square n), (n > 0)%nat -> @inftyNorm_wf n m = 0 -> m = zero_wf.
Proof.
  intros.
  unfold zero_wf.
  assert (forall r c, inftyNorm_wf m >= Cmod (`m r c)) as inftyNorm_bound_inst.
    intros.
    apply inftyNormwf_bound.
    assumption.
  destruct m as [val wf].
  unfold inftyNorm_wf in inftyNorm_bound_inst.
  simpl in inftyNorm_bound_inst.
  unfold inftyNorm_wf in H0.
  simpl in H0.
  rewrite H0 in inftyNorm_bound_inst.
  assert (forall r c, Cmod (val r c) = 0) as cmod_is_0.
    intros.
    apply Rge_antisym.
    apply Rle_ge.
    apply Cmod_ge_0.
    apply inftyNorm_bound_inst.
  assert (forall r c, val r c = 0) as entries_zero.
    intros.
    apply Cmod_eq_0.
    apply cmod_is_0.
  assert (val = Zero) as val_zero.
    apply functional_extensionality.
    intro r.
    apply functional_extensionality.
    intro c.
    unfold Zero.
    apply entries_zero.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma inftyNorm_zero :
  forall (n : nat) (m : @WF_Square n), @inftyNorm_wf n m = 0 -> m = zero_wf.
Proof.
  intros.
  case_eq (n =? 0)%nat.
  * intros.
    apply Nat.eqb_eq in H0.
    destruct m as [val wf].
    unfold zero_wf.
    assert (Zero = val) as val_zero.
      apply functional_extensionality.
      intro r.
      apply functional_extensionality.
      intro c.
      unfold Zero.
      unfold WF_Matrix in wf.
      clear H.
      rewrite H0 in wf.
      symmetry.
      apply wf.
      lia.
    destruct val_zero.
    f_equal.
    apply proof_irrelevance.
  * intros.
    assert (n > 0)%nat.
      apply Nat.eqb_neq in H0.
      lia.
    apply inftyNorm_zero_aux; try assumption.
Qed.

Lemma inftyNorm_of_zero :
  forall (n : nat), @inftyNorm_wf n zero_wf = 0.
Proof.
  intros.
  unfold inftyNorm_wf.
  unfold zero_wf.
  simpl.
  unfold inftyNorm.
  induction (n * n - 1)%nat.
  + simpl.
    case_eq (Rlt_dec (Cmod (@Zero n n (0 / n)%nat (0 mod n))) 0).
    - reflexivity.
    - intros.
      unfold Zero.
      apply Cmod_0.
  + simpl.
    case_eq (Rlt_dec (Cmod (@Zero n n (S n0 / n)%nat (S n0 mod n))) 0).
    - intros. assumption.
    - intros.
      assert (Cmod (@Zero n n (S n0 / n)%nat (S n0 mod n)) = 0).
        unfold Zero. apply Cmod_0.
      rewrite H0.
      assumption.
Qed.

Lemma inftyNorm_prod {n : nat} (m1 m2 : @WF_Square n) :
  inftyNorm_wf (m1 × m2) <= INR n * inftyNorm_wf m1 * inftyNorm_wf m2.
Proof.
  (* Arithmetics *)
  Admitted.

Definition dist_mats {n : nat} (m1 m2 : @WF_Square n) : R :=
  inftyNorm_wf (plus_wf m1 (scale_wf (-1) m2)).

Lemma dist_mats_prod {n : nat} (T m1 m2 U: @WF_Square n) :
  dist_mats (T × m1 × U) (T × m2 × U) <=
    INR n * INR n * inftyNorm_wf T * inftyNorm_wf U * dist_mats m1 m2.
Proof.
  (* Use this somehow *)
  Check inftyNorm_prod.
  Admitted.

Lemma dist_mats_pos :
    forall n (m1 m2 : @WF_Square n), dist_mats m1 m2 >= 0.
Proof.
  intros.
  unfold dist_mats.
  unfold inftyNorm.
  apply inftyNorm_nonneg.
Qed.

Lemma dist_mats_sym :
    forall n (m1 m2 : @WF_Square n), dist_mats m1 m2 = dist_mats m2 m1.
Proof.
    Admitted.

Lemma dist_mats_refl :
    forall n (m1 m2 : @WF_Square n), dist_mats m1 m2 = 0 <-> m1 = m2.
Proof.
  intros.
  split.
  + intros.
    unfold dist_mats in H.
    assert (plus_wf m1 (scale_wf (-1) m2) = zero_wf) as diff_0.
      apply inftyNorm_zero.
      assumption.
    destruct m1 as [val1 wf1].
    destruct m2 as [val2 wf2].
    unfold inftyNorm_wf in diff_0.
    unfold plus_wf in diff_0.
    unfold scale_wf in diff_0.
    simpl in diff_0.
    assert (val1 .+ -1 .* val2 = Zero)%M.
    unfold zero_wf in diff_0.
    apply proj1_sig_eq in diff_0.
    simpl in diff_0.
    assumption.
    assert (val1 = val2) as vals_eq.
      apply functional_extensionality.
      intro r.
      apply functional_extensionality.
      intro c.
      apply (f_equal (fun m => m r c)) in H0.
      unfold Zero in H0.
      unfold ".+" in H0.
      unfold ".*" in H0.
      assert (forall (x y : C), (x + -1 * y = 0)%C -> (x = y)%C).
        intros.
        assert (IZR (Zneg xH) = Ropp R1) as minus1_R.
          lra.
        rewrite minus1_R in H0.
        rewrite minus1_R in H1.
        rewrite RtoC_opp in H0.
        rewrite RtoC_opp in H1.
        rewrite <- Copp_mult_distr_l in H1.
        rewrite <- Cminus_unfold in H1.
        rewrite Cmult_1_l in H1.
        apply c_proj_eq.
          apply (f_equal fst) in H1.
          simpl in H1.
          lra.
          apply (f_equal snd) in H1.
          simpl in H1.
          lra.
      apply H1 in H0.
      assumption.
    apply eq_sig_uncurried.
    exists vals_eq.
    apply proof_irrelevance.
  + intros. subst.
    unfold dist_mats.
    assert (plus_wf m2 (scale_wf (-1) m2) = zero_wf) as wf_arg_is_zero.
      unfold plus_wf.
      unfold scale_wf.
      unfold zero_wf.
      simpl.
      assert (`m2 .+ -1 .* `m2 = Zero)%M as arg_is_zero.
        apply functional_extensionality.
        intro r.
        apply functional_extensionality.
        intro c.
        unfold Zero.
        unfold ".+".
        unfold ".*".
        lca.
      apply eq_exist_uncurried.
      exists arg_is_zero.
      apply proof_irrelevance.
   rewrite wf_arg_is_zero.
   apply inftyNorm_of_zero.
Qed.

Lemma dist_mats_tri :
    forall n (m1 m2 m3 : @WF_Square n), dist_mats m1 m2 <= dist_mats m1 m3 + dist_mats m3 m2.
Proof.
    Admitted.

Definition MatrixMetricSpace (n : nat) := Build_Metric_Space (@WF_Square n)
    dist_mats
    (dist_mats_pos n)
    (dist_mats_sym n)
    (dist_mats_refl n)
    (dist_mats_tri n).

(* TODO mat conv iff entrywise? *)

Lemma mat_conv_mult_nonzero {dim : nat} (Ms : nat -> @WF_Square dim) (T M U : @WF_Square dim) :
  T <> zero_wf -> (* I don't wanna deal with degenerate cases yet *)
  U <> zero_wf ->
  seq_conv (MatrixMetricSpace dim) Ms M ->
  seq_conv (MatrixMetricSpace dim) (fun i => T × Ms i × U) (T × M × U).
Proof.
  unfold seq_conv.
  intros T_neq0 U_neq0 conv_Ms_M eps eps_pos.
  remember ((/ (INR dim * inftyNorm_wf T * INR dim * inftyNorm_wf U)) * eps)%R as epsMs.
  assert (epsMs > 0) as epsMs_pos.
    admit.
  specialize (conv_Ms_M epsMs).
  specialize (conv_Ms_M epsMs_pos).
  destruct conv_Ms_M as [N Ms_M_close].
  exists N.
  intro n.
  specialize (Ms_M_close n).
  intro n_large.
  specialize (Ms_M_close n_large).
  subst.
  (* TODO use this *)
  Check dist_mats_prod.
Admitted.

Lemma mat_conv_mult {dim : nat} (Ms : nat -> @WF_Square dim) (T M U : @WF_Square dim) :
  seq_conv (MatrixMetricSpace dim) Ms M ->
  seq_conv (MatrixMetricSpace dim) (fun i => T × Ms i × U) (T × M × U).
Proof.
  (* TODO apply lemma for nonzero case; handle zero cases separately *)
  Check mat_conv_mult_nonzero.
Admitted.

(* -- Matrix exponential -- *)
(**
 * Now we are almost ready to define matrix exponential.
 * First we define partial and infinite sum of matrices.
 *)
Fixpoint mat_psum {dim : nat} (seq : nat -> @WF_Square dim) (N : nat) : @WF_Square dim :=
    match N with
    | O => seq O
    | S pred => plus_wf (mat_psum seq pred) (seq N)
    end.
  
(* The infinite sum is defined as a relation, since a sum may not converge. *)
Definition mat_infinite_sum {dim : nat} (seq : nat -> @WF_Square dim) (result : @WF_Square dim) :=
    seq_conv (MatrixMetricSpace dim) (mat_psum seq) result.

(*
 * Our matrix exponential was defined as a relation.
 * We wanted to brush existence and uniqueness issues under the rug.
 * I regret it more with every passing day.
 * Is it what they call technical debt?
 *)
Definition matrix_exponential {n : nat} (M Mexp : @WF_Square n) :=
    mat_infinite_sum (fun k => scale_wf (/ (INR (fact k))) (mmult_wf k M) ) Mexp.

Lemma matrix_exponential_conjugate {n : nat} (T Tinv D Dexp : @WF_Square n) :
  Minv (`T) (`Tinv) ->
  matrix_exponential D Dexp ->
  matrix_exponential (T × D × Tinv) (T × Dexp × Tinv).
Proof.
  intros Tinv_correct Dexp_def.
  unfold matrix_exponential.
  unfold mat_infinite_sum.
  assert ((mat_psum (fun k : nat => / INR (fact k) .* k ⨉ (T × D × Tinv))) =
    fun k => T ×
      (mat_psum (fun i => / INR (fact i) .* i ⨉ D) k) ×
      Tinv) as factor_T. {
    assert ((fun k : nat => / INR (fact k) .* k ⨉ (T × D × Tinv)) =
      fun k : nat => T × (/ INR (fact k) .* k ⨉ D) × Tinv) as cancel_minvs. {
      apply functional_extensionality.
      intros k.
      (* TODO Matrix algebra *)
      admit.
    }
    rewrite cancel_minvs.
    (* TODO state and use distributivity of mat_psum *)
    admit.
  }
  rewrite factor_T.
  apply mat_conv_mult.
  unfold matrix_exponential in Dexp_def.
  unfold mat_infinite_sum in Dexp_def.
  assumption.
Admitted.

(** Will bring the rest back later.

(* -- Facts on matrix exponential -- *)

Lemma mexp_scale :
  forall (dim : nat) (A expA: @WF_Square dim) (sc : R),
    matrix_exponential A expA ->
    matrix_exponential (scale sc A) (scale (exp sc) expA).
Proof.
  Admitted.
        
Lemma mexp_cscale :
  forall (dim : nat) (A expA : Square dim) (sc : R),
    matrix_exponential A expA ->
    matrix_exponential (scale (Ci * sc) A) (scale (Cexp sc) expA).
Proof.
Admitted.

(* -- Approximation of matrix exponentials -- *)
(* e^((A+B)dt) ~= e^(A dt) e^(B dt) *)
(* but with more matrices than 2 *)

(* Sum of finitely many matrices *)
Fixpoint mat_finite_sum {dim : nat} (Ms : list (Square dim)) : Square dim :=
  match Ms with
  | head :: tail => Mplus head (mat_finite_sum tail)
  | [] => Zero
  end.

(* Product of finitely many matrices *)
Fixpoint mat_finite_prod {dim : nat} (Ms : list (Square dim)) : Square dim :=
  match Ms with
  | head :: tail => Mmult head (mat_finite_prod tail)
  | [] => I dim
  end.

Definition matexp_approx {dim : nat} (Ms : list (Square dim)) :
  let sumMs := mat_finite_sum Ms in
  forall (exp_sumMs : Square dim) (expMdt : nat -> list (Square dim)),
    matrix_exponential sumMs exp_sumMs -> (
    forall (i invDt : nat),
      (0 <= i)%nat ->
      (i < List.length Ms)%nat ->
      matrix_exponential (scale (/ INR invDt) (nth i Ms Zero)) (nth i (expMdt invDt) Zero)
    ) ->
    seq_conv (MatrixMetricSpace dim)
      (fun nSlices => mat_finite_prod (expMdt nSlices))
      exp_sumMs.
Proof.
  intros.
  (* TODO *)
Admitted.

(*
     *** Some lemmas (previously) needed by Semantics.v ***
 *)


(* This lemma is true, but may be difficult to prove *)
Lemma mat_exp_well_defined {n : nat} : forall (M : Square n),
    exists (Mexp : Square n), matrix_exponential M Mexp.
Proof. Admitted.



(* There are all sorts of problems with this, but I don't think we'll end up needing
   it anyways *)
Lemma seq_conv_unique : forall X seq n1 n2,
  seq_conv X seq n1 -> seq_conv X seq n2 -> n1 = n2.
Proof.
  intros X seq n1 n2 H1 H2. unfold seq_conv in *.
  assert (H : forall eps,
             eps > 0 ->
             exists N,
               forall n, (n >= N)%nat ->
                         Rabs ((dist X (seq n) n1) - (dist X (seq n) n2)) < eps). {
    intros. remember (H1 eps H) as H1'. remember (H2 eps H) as H2'. clear HeqH1' HeqH2' H1 H2.
    inversion H1' as [N1 H1'']. inversion H2' as [N2 H2'']. clear H1' H2'.
    destruct (blt_reflect N1 N2) as [HN | HN]. (* we want max(N1, N2) *)
    - exists N2. intros n HN2.
      assert (HN1 : (n >= N1)%nat). lia.
      apply H1'' in HN1. apply H2'' in HN2. clear H1'' H2'' HN.
      unfold Rabs.
      assert (a : dist X (seq n) n1 >= 0). apply dist_pos.
      assert (b : dist X (seq n) n2 >= 0). apply dist_pos.
      destruct (Rcase_abs (dist X (seq n) n1 - dist X (seq n) n2)); lra.
    - exists N1. intros n HN1.
      assert (HN2 : (n >= N2)%nat). lia.
      apply H1'' in HN1. apply H2'' in HN2. clear H1'' H2'' HN.
      unfold Rabs.
      assert (a : dist X (seq n) n1 >= 0). apply dist_pos.
      assert (b : dist X (seq n) n2 >= 0). apply dist_pos.
      destruct (Rcase_abs (dist X (seq n) n1 - dist X (seq n) n2)); lra.
  }  
  clear H1 H2. Print seq_conv.
  assert (HHHH : seq_conv R_met (fun n => Rabs (dist X (seq n) n1 - dist X (seq n) n2)) 0). {
    admit.
  }
  apply dist_refl.
  Admitted.

  **)
  
Lemma mat_exp_unique {n : nat} : forall (M Mexp1 Mexp2 : @WF_Square n),
    matrix_exponential M Mexp1 -> matrix_exponential M Mexp2 -> Mexp1 = Mexp2.
Proof.
  intros M M1 M2 H1 H2.
  unfold matrix_exponential in *. unfold mat_infinite_sum in *.
  (*
  eapply seq_conv_unique with (X := MatrixMetricSpace n).
  apply H1. apply H2.
  *)
Admitted.

(**

Lemma mat_exp_WF {n : nat} : forall (M Mexp : Square n),
    matrix_exponential M Mexp -> WF_Matrix M -> WF_Matrix Mexp.
Proof. Admitted.

(* More matrix exponential facts... *)

(* Padding an operator with no-op on other locations *)
Definition padIs (num_qubits : nat) (g : Square 2) (loc : nat) : Square (2 ^ num_qubits) :=
  kron (kron (I (2 ^ loc)) g) (I (2 ^ (num_qubits - loc - 1))).

(* Output of padIs is a well-formed matrix *)
Lemma padIs_WF :
  forall (num_qubits : nat) (g : Square 2) (loc : nat),
    (WF_Matrix g) ->
    (loc < num_qubits)%nat ->
    WF_Matrix (padIs num_qubits g loc).
Proof.
  intros.
  unfold padIs.
  Search kron.
  apply WF_kron.
  admit. (* arithmetic *)
  admit. (* arithmetic *)
  apply WF_kron.
  reflexivity.
  reflexivity.
  Search WF_Matrix.
  apply WF_I.
  assumption.
  apply WF_I.
Admitted.

(* PadIs and matrix exponentials commute with each others *)
Lemma mexp_padIs :
  forall num_qubits A expA loc,
    matrix_exponential A expA ->
    matrix_exponential (padIs num_qubits A loc) (padIs num_qubits expA loc).
Proof. Admitted.

(* More facts on padIs: it commutes with scalar multiplication. *)
(* Not sure where this lemma belongs *)
Lemma padIs_scale :
  forall num_qubits A sc loc,
    padIs num_qubits (scale sc A) loc = scale sc (padIs num_qubits A loc).
Proof. Admitted.

**)
