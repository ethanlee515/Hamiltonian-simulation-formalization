Require Import Reals QWIRE.Matrix.
Require Import Complex.

(* -- Showing that matrices form a metric space -- *)

(* We could define operator norm and show that the norm induces a metric...
 * but that's too much real analysis.
 * I think we'll be cheap today and go with infinity norm.
 * Where we won't even formalize what a "norm" is because I don't want to formalize a vector space.
 * Bite me.
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
    (* exists Zero. *)
    Admitted.
    
Lemma inftyNorm_ub {n : nat} (m : Square n) :
    bound (inftyNorm_lb m).
Proof.
    (* This is annoying *)
    Admitted.

Definition inftyNorm_inst {n : nat} (m : Square n) :=
    completeness (inftyNorm_lb m) (inftyNorm_ub m) (ex_inftyNorm_lb m).

(* Why is this so disgusting *)
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

(* Print sum_f_R0. *)
Fixpoint mat_psum {dim : nat} (seq : nat -> Square dim) (N : nat) : Square dim :=
    match N with
    | O => seq O
    | S pred => Mplus (mat_psum seq pred) (seq N)
    end.

(* Can't use the limit_in since it's limit as N goes to an actual value as opposed to infinity *)
(* Print limit_in. *)
(* Print infinite_sum. *)
Fixpoint mat_infinite_sum {dim : nat} (seq : nat -> Square dim) (result : Square dim) :=
    forall eps : R, eps > 0 -> exists N : nat,
    (forall n : nat, (n >= N)%nat -> (MatrixMetricSpace n).(dist) (mat_psum seq n) result < eps).

(* fucking scuffed *)
Definition matrix_exponential {n : nat} (M Mexp : Square n) :=
    mat_infinite_sum (fun k => scale (/ (INR (fact k))) (Mmult_n k M) ) Mexp.
