(** -- MatrixExponential.v -- **)
(**
 * Defines matrix exponentiation and its preliminaries.
 * Proves some basic properties as well.
 *)

Require Import Reals QWIRE.Matrix.
Require Import Complex.
Require Import Lra.

(* -- Sequence convergence in metric space -- *)

(* Somehow this isn't in the standard library.
 * We have limit_in, but that's for N goes to an actual value as opposed to infty
 *)
(* Print limit_in. *)

Definition seq_conv (X : Metric_Space) (seq : nat -> Base X) (lim : Base X) :=
    forall eps : R, eps > 0 ->
    exists N : nat, 
        (forall n : nat, (n >= N)%nat -> X.(dist) (seq n) lim < eps).

(* -- Showing that matrices form a metric space -- *)

(* We could define operator norm and show that the norm induces a metric...
 * but that's too much real analysis.
 * I think we'll be cheap today and go with infinity norm.
 * Where we won't even formalize what a "norm" is because I don't want to formalize a vector space.
 *
 * For infinity norm, we need to take max over a matrix...
 * Unfortunately, reals ordering is not decidable,
 * which is a problem because we need distance to be decidable to call Build_Metric_Space.
 * The only way I can think of to get a decidable max is by calling completeness...
 *)

Definition inftyNorm_lb {n : nat} (m : Square n) (lb : R) :=
    exists i j, lb < Cmod (m i j).  

Lemma ex_inftyNorm_lb {n : nat} (m : Square n) :
    exists lb, inftyNorm_lb m lb.
Proof.
  exists (-1). unfold inftyNorm_lb. unfold Cmod. exists 0%nat, 0%nat.
  assert (H :0 <=  √ (fst (m 0%nat 0%nat) ^ 2 + snd (m 0%nat 0%nat) ^ 2)).
  - apply sqrt_pos.
  - lra.
Qed.

Definition Cmod_elem (f : nat -> nat -> C) (i j : nat) := Cmod (f i j).

Fixpoint matrix_sum {n : nat} (row : nat) (M : Square n) : R :=
  match row with
  | 0 => (Rsum n (Cmod_elem M 0%nat))
  | S row' => (Rsum n (Cmod_elem M row)) + (matrix_sum row' M)
  end.

Lemma inftyNorm_ub {n : nat} (M : Square n) :
    bound (inftyNorm_lb M).
Proof.
  unfold bound.
  exists (matrix_sum (n-1) M).
  assert (Hub : forall i j, Cmod (M i j) <= matrix_sum (n-1) M). {
    intros i j. admit. (* I don't think this is provable without well-formedness :(   *)
  }
  unfold is_upper_bound. intros x.
  unfold inftyNorm_lb. intros [i [j H]].
  remember (Hub i j). lra.
Admitted.

Definition inftyNorm_inst {n : nat} (m : Square n) :=
    completeness (inftyNorm_lb m) (inftyNorm_ub m) (ex_inftyNorm_lb m).

Definition inftyNorm {n : nat} (m : Square n) : R := proj1_sig (inftyNorm_inst m).

Definition dist_mats {n : nat} (m1 m2 : Square n) : R := inftyNorm (Mplus m1 (scale (-1) m2)).

Lemma dist_mats_pos :
    forall n (m1 m2 : Square n), dist_mats m1 m2 >= 0.
Proof.
    Admitted.

Lemma dist_mats_sym :
    forall n (m1 m2 : Square n), dist_mats m1 m2 = dist_mats m2 m1.
Proof.
    Admitted.

Lemma dist_mats_refl :
    forall n (m1 m2 : Square n), dist_mats m1 m2 = 0 <-> m1 = m2.
Proof.
    Admitted.

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
  (* Disgusting. *)
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
