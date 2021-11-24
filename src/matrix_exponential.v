Require Import Reals QWIRE.Matrix.
Require Import Complex.

(* Stolen and generalized from real case *)
(* Print R_dist. *)
Definition C_dist c1 c2 :=
    Cmod (c1 - c2).

(* Print sum_f_R0. *)
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

Print Metric_Space.

(* TODO https://coq.github.io/doc/v8.9/stdlib/Coq.Reals.Rlimit.html *)

Definition Mat_met (n : nat) : Metric_space :=
    Build_Metric_Space 
