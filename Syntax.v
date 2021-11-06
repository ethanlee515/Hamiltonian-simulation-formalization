Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Reals.

Inductive HType := HQubit | HFock.
Inductive HOp := Id | X | Y | Z | a | c.
Definition HDecl := (HType * string)%type.
Definition HDecls := list HDecl. (* I don't think it parses this way *)
Inductive HScalar :=
    | HScAdd (s1 s2 : HScalar)
    | HScMult (s1 s2 : HScalar)
    | HScSub (s1 s2 : HScalar)
    | HScDiv (s1 s2 : HScalar)
    | HScExp (s : HScalar)
    | HScCos (s : HScalar)
    | HScSin (s : HScalar)
    | HScReal (r : R).
    (* TODO Get library for complex *)
Inductive TIH :=
    | HAdd (h1 h2 : TIH)
    | HMult (h1 h2 : TIH)
    | HMultS (h: TIH) (s : HScalar)
    | HIdOp (id: string) (op: HOp).
Inductive TIH_Seq := . (* TODO *)
Definition H_Program := (HDecls * TIH_Seq)%type.

Declare Custom Entry ham.
Declare Custom Entry decl.
Declare Custom Entry decls.
Declare Scope ham_scope.

Notation "<{ h }>" := h (at level 0, h custom decls at level 0) : ham_scope.
Notation "x" := x (in custom decls at level 0, x custom decl at level 0) : ham_scope.
Notation "'qubit' x" := [(HQubit, x)]
    (in custom decl at level 0,
        x constr at level 0) : ham_scope.
Notation "x y" := (x ++ y)
    (in custom decls at level 0,
        right associativity) : ham_scope.

Definition Q1 : string := "Q1".
Definition Q2 : string := "Q2".

Open Scope ham_scope.
Open Scope string_scope.

Compute <{ qubit Q1 }>.
Compute <{ qubit Q1 qubit Q2 }>.
Compute <{ qubit Q1 qubit "Q3" }>.
