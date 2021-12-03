Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From HSF Require Import src.Semantics.

(*
Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.


From PLF Require Import Stlc.
Import Check.
 *)

Goal True.

idtac "-------------------  commuting_Ham_semantics  --------------------".
idtac " ".

Abort.
Print Assumptions commuting_Ham_semantics.
Goal True.
idtac " ".


Abort.

(* 2021-11-14 17:52 *)

(* 2021-11-14 17:52 *)
