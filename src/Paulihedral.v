(** Pauli - taken from suzuki.v, possibly originally taken from PauliRotations.v;
            this will need to be fixed **)

Require Import Reals.

Open Scope R_scope.

Inductive Pauli1 :=
| Pauli_I
| Pauli_X
| Pauli_Y
| Pauli_Z.

Record Pauli1_at_loc := make_Pauli1_at_loc
{
  pauli : Pauli1;
  loc : nat;
}.





(* Paulihedral-like implementation *)

Require Import List.
Import ListNotations.
Require Import Mergesort.
Require Import Orders.

Record pauli_string := make_pauli_sting
{
  param : R;
  pauli_list : list Pauli1_at_loc;
}.

(* Assumes 1-indexing of sites *)
Inductive pauli_list_WF : list Pauli1_at_loc -> Prop :=
| pl_WF_singleton (p : Pauli1) :
    pauli_list_WF [make_Pauli1_at_loc p 1]
| pl_WF_cons (p : Pauli1)
             (n : nat)
             (PL : list Pauli1_at_loc)
             (H_WF : pauli_list_WF PL)
             (H_len : length PL = n) :
    pauli_list_WF ((make_Pauli1_at_loc p (n+1)) :: PL).

Definition pauli_string_WF (P : pauli_string) :=
  P.(param) > 0 /\ pauli_list_WF P.(pauli_list).





(* Define an ordering for Paulis (X < Y < Z < I) so strings can be sorted *)
Local Coercion is_true : bool >-> Sortclass.
Module PauliStringOrder <: TotalTransitiveLeBool.

  Definition t := pauli_string.

  Definition compare_paulis (p1 p2 : Pauli1) : comparison :=
    match p1, p2 with
    | Pauli_X, Pauli_X => Eq
    | Pauli_Y, Pauli_Y => Eq
    | Pauli_Z, Pauli_Z => Eq
    | Pauli_I, Pauli_I => Eq
    | Pauli_X, _ => Lt
    | _, Pauli_X => Gt
    | Pauli_Y, _ => Lt
    | _, Pauli_Y => Gt
    | Pauli_Z, _ => Lt
    | _, Pauli_Z => Gt
    end.

  Fixpoint leq_pauli_lists (pl1 pl2 : list Pauli1_at_loc) :=
    match pl1, pl2 with
    | [], [] => true
    | [], _ => true  (* pauli strings not well-formed, should be the same length *)
    | _, [] => false (* pauli strings not well-formed, should be the same length *)
    | p1 :: pl1', p2 :: pl2' => 
      match compare_paulis p1.(pauli) p2.(pauli) with
      | Lt => true
      | Gt => false
      | Eq => leq_pauli_lists pl1' pl2'
      end
    end.
  
  Definition leb (ps1 ps2 : pauli_string) :=
    leq_pauli_lists ps1.(pauli_list) ps2.(pauli_list).

  Theorem leb_total : forall ps1 ps2, leb ps1 ps2 \/ leb ps2 ps1.
  Proof.
    intros. unfold leb.
    remember (pauli_list ps1) as pl1. remember (pauli_list ps2) as pl2. clear Heqpl1 Heqpl2.
    induction pl1 as [|p1 pl1']; induction pl2 as [|p2 pl2']; auto.
    Admitted.
  
  Theorem leb_trans : Transitive leb.
  Proof.
    Admitted.
End PauliStringOrder.

(* Use this to sort pauli strings *)
Module Import PauliStringSort := Sort PauliStringOrder.

