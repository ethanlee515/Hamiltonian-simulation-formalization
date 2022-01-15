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

(* -- Showing that matrices form a metric space -- *)

(* We could define operator norm and show that the norm induces a metric...
 * but that's too much real analysis.
 * I think we'll be cheap today and go with infinity norm.
 *)

Fixpoint inftyNorm_aux {n : nat} (mat : Square n) (i : nat) (currentMax : R) : R :=
  let r := (i / n)%nat in
  let c := (i mod n)%nat in
  let elem := Cmod (mat r c) in
  (* Apparently this works... *)
  let newMax := if Rlt_dec elem currentMax then currentMax else elem in
  match i with
  | O => newMax
  | S i' => inftyNorm_aux mat i' newMax
  end.

Lemma if_both_nonneg :
  forall a b c d, a >= 0 -> b >= 0 -> (if Rlt_dec c d then a else b) >= 0.
Proof.
  intros.
  case (Rlt_dec c d); intro; assumption.
Qed.

Lemma inftyNorm_aux_nonneg :
  forall n mat i m, m >= 0 -> @inftyNorm_aux n mat i m >= 0.
Proof.
  intros.
  generalize dependent m.
  induction i.
  + intros.
    unfold inftyNorm_aux.
    apply if_both_nonneg.
    - assumption.
    - apply Rle_ge.
      apply Cmod_ge_0.
  + simpl.
    intros.
    apply IHi.
    apply if_both_nonneg; try assumption.
    apply Rle_ge.
    apply Cmod_ge_0.
Qed.

Lemma inftyNorm_aux_runningMax_monotonic:
  forall n mat i m1 m2, m1 >= m2 -> @inftyNorm_aux n mat i m1 >= @inftyNorm_aux n mat i m2.
Proof.
  intros.
  generalize dependent m2.
  generalize dependent m1.
  induction i.
  + simpl.
    intros.
    case (Rlt_dec (Cmod (mat (0 / n)%nat (0 mod n))) m1).
    * intros.
      case (Rlt_dec (Cmod (mat (0 / n)%nat (0 mod n))) m2).
      - intro. assumption.
      - lra.
    * intros.
      apply Rnot_lt_ge in n0.
      assert (Cmod (mat (0 / n)%nat (0 mod n)) >= m2).
        apply Rge_trans with (r2 := m1); assumption.
      case_eq (Rlt_dec (Cmod (mat (0 / n)%nat (0 mod n))) m2).
      - intros.
        assumption.
      - intros.
        apply Rge_refl.
  + simpl.
    intros.
    case (Rlt_dec (Cmod (mat (S i / n)%nat (S i mod n)))).
    * intros.
      case (Rlt_dec (Cmod (mat (S i / n)%nat (S i mod n))) m2).
      - intros.
        apply IHi. assumption.
      - intros.
        apply IHi.
        apply Rgt_ge.
        apply Rlt_gt.
        assumption.
    * intros.
      case (Rlt_dec (Cmod (mat (S i / n)%nat (S i mod n))) m2).
      - intros. lra.
      - lra.
Qed.

Lemma inftyNorm_aux_running_max_correct:
  forall n mat i m y, m >= y -> @inftyNorm_aux n mat i m >= y.
Proof.
  intros.
  induction i.
  + simpl.
    case (Rlt_dec (Cmod (mat (0 / n)%nat (0 mod n))) m).
    - intro. assumption.
    - intro.
      apply Rnot_lt_ge in n0.
      apply Rge_trans with (r2 := m); assumption.
  + simpl.
    apply Rge_trans with (r2 := inftyNorm_aux mat i m).
    - apply inftyNorm_aux_runningMax_monotonic.
      case (Rlt_dec (Cmod (mat (S i / n)%nat (S i mod n))) m); lra.
    - assumption.
Qed.

Lemma inftyNorm_aux_correct:
  forall n mat i I,
    (i <= I)%nat -> @inftyNorm_aux n mat I 0 >= Cmod (mat (i / n)%nat (i mod n)%nat).
Proof.
  intros.
  generalize dependent i.
  induction I.
  + intros.
    simpl.
    assert (i = 0%nat).
      lia.
    subst.
    case_eq (Rlt_dec (Cmod (mat (0 / n)%nat (0 mod n))) 0).
    - intros. lra.
    - intros. lra.
  + intros.
    simpl.
    case_eq (Rlt_dec (Cmod (mat (S I / n)%nat (S I mod n))) 0).
    - intros.
      assert (0 <= Cmod (mat (S I / n)%nat (S I mod n))).
        Print Cmod_ge_0.
        apply Cmod_ge_0.
      lra.
    - intros.
      case_eq (i =? S I).
      * rewrite Nat.eqb_eq.
        intro. subst.
        apply inftyNorm_aux_running_max_correct.
        apply Rge_refl.
      * intro.
        apply beq_nat_false in H1.
        apply Rge_trans with (r2 := inftyNorm_aux mat I 0).
        ** apply inftyNorm_aux_runningMax_monotonic.
           apply Rle_ge.
           apply Cmod_ge_0.
        ** apply IHI. lia.
Qed.

Definition inftyNorm {n : nat} (m : Square n) :=
  inftyNorm_aux m (n * n - 1) 0.

Lemma inftyNorm_nonneg :
  forall n mat, @inftyNorm n mat >= 0.
Proof.
  unfold inftyNorm.
  intros.
  apply inftyNorm_aux_nonneg.
  apply Req_ge_sym.
  reflexivity.
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
      apply inftyNorm_aux_correct.
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

Definition dist_mats {n : nat} (m1 m2 : @WF_Square n) : R :=
  inftyNorm_wf (plus_wf m1 (scale_wf (-1) m2)).

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
    assert (val1 .+ -1 .* val2 = Zero).
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
      assert (`m2 .+ -1 .* `m2 = Zero) as arg_is_zero.
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
    forall n (m1 m2 m3 : Square n), dist_mats m1 m2 <= dist_mats m1 m3 + dist_mats m3 m2.
Proof.
    Admitted.

Definition MatrixMetricSpace (n : nat) := Build_Metric_Space (Square n)
    dist_mats
    (dist_mats_pos n)
    (dist_mats_sym n)
    (dist_mats_refl n)
    (dist_mats_tri n).

(* -- Matrix exponential -- *)
(**
 * Now we are almost ready to define matrix exponential.
 * First we define partial and infinite sum of matrices.
 *)
Fixpoint mat_psum {dim : nat} (seq : nat -> Square dim) (N : nat) : Square dim :=
    match N with
    | O => seq O
    | S pred => Mplus (mat_psum seq pred) (seq N)
    end.
  
(* The infinite sum is defined as a relation, since a sum may not converge. *)
Definition mat_infinite_sum {dim : nat} (seq : nat -> Square dim) (result : Square dim) :=
    seq_conv (MatrixMetricSpace dim) (mat_psum seq) result.

(*
 * Our matrix exponential was defined as a relation.
 * We wanted to brush existence and uniqueness issues under the rug.
 * I regret it more with every passing day.
 * Is it what they call technical debt?
 *)
Definition matrix_exponential {n : nat} (M Mexp : Square n) :=
    mat_infinite_sum (fun k => scale (/ (INR (fact k))) (Mmult_n k M) ) Mexp.

(* -- Facts on matrix exponential -- *)

Lemma mexp_scale :
  forall (dim : nat) (A expA: Square dim) (sc : R),
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

  
  
Lemma mat_exp_unique {n : nat} : forall (M Mexp1 Mexp2 : Square n),
    matrix_exponential M Mexp1 -> matrix_exponential M Mexp2 -> Mexp1 = Mexp2.
Proof.
  intros M M1 M2 H1 H2.
  unfold matrix_exponential in *. unfold mat_infinite_sum in *. Locate Metric_Space.
  eapply seq_conv_unique with (X := MatrixMetricSpace n).
  apply H1. apply H2.
Qed.  

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
