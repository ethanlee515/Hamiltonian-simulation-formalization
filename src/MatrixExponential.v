Require Import Reals QWIRE.Matrix.
Require Import Complex.

Print Metric_Space.

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

(* TODO https://coq.github.io/doc/v8.9/stdlib/Coq.Reals.Rlimit.html *)

(* Stolen and generalized from real case *)
 Print R_dist. 
Definition C_dist c1 c2 :=
    Cmod (c1 - c2).

Print sum_f_R0. 
Fixpoint sum_f_C0 (f:nat -> C) (N:nat) : C :=
    match N with
        | O => f 0%nat
        | S i => sum_f_C0 f i + f (S i)
    end.

(* Print infinite_sum. *)
Definition infinite_sumC (s : nat -> C) (l : C) :=
    forall eps:R,
        eps > 0 ->
        exists N : nat,
    (forall n:nat, (n >= N)%nat -> C_dist (sum_f_C0 s n) l < eps).

(* fucking scuffed *)
Definition matrix_exponential {n : nat} (M Mexp : Square n) :=
    forall i j,
        infinite_sumC (fun k => ((Mmult_n k M) i j) / (INR (fact k))) (Mexp i j).

Require Import Rlimit.

