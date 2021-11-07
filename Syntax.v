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
Definition HDecls := list HDecl.
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
    | HMultS (s : HScalar) (h: TIH)
    | HIdOp (id: string) (op: HOp).
Definition TIH_Seq := list (string * R * TIH).
Definition H_Program := (HDecls * TIH_Seq)%type.

Class Ham_Quantity_Add (Q : Type) :=
{
    HQAdd : Q -> Q -> Q
}.

Instance HQScAdd : Ham_Quantity_Add HScalar :=
{
    HQAdd := HScAdd
}.

Instance HQ_TIH_Add : Ham_Quantity_Add TIH :=
{
    HQAdd := HAdd
}.

Class Ham_Quantity_Mult (Q1 : Type) (Q2 : Type) :=
{
    HQMult : Q1 -> Q2 -> Q2
}.

Instance HQ_Sc_Sc_Mult : Ham_Quantity_Mult HScalar HScalar :=
{
    HQMult := HScMult
}.

Instance HQ_Sc_TIH_Mult: Ham_Quantity_Mult HScalar TIH :=
{
    HQMult := HMultS
}.

Instance HQ_TIH_TIH_Mult: Ham_Quantity_Mult TIH TIH :=
{
    HQMult := HMult
}.

Declare Custom Entry decl.
Declare Custom Entry decls.
Declare Custom Entry TIH.
Declare Scope ham_scope.

Notation "<{ h }>" := h (at level 0, h custom TIH) : ham_scope.

Notation "'Site' D ; 'Hamiltonian' S" := (D, S)
    (at level 1, D custom decls, S custom TIH).

Notation "x" := x (in custom decls at level 10, x custom decl) : ham_scope.
Notation "'qubit' x" := [(HQubit, x)]
    (in custom decl at level 10,
        x constr) : ham_scope.
Notation "'fock' x" := [(HFock, x)]
    (in custom decl at level 10,
        x constr) : ham_scope.
Notation "x y" := (x ++ y)
    (in custom decls at level 80,
        right associativity) : ham_scope.

Notation "x" := x (in custom TIH at level 0, x constr at level 0) : ham_scope.

(* Not sure how to get A.O to work without . being parsed as end-of-statement *)
Notation "A > O" := (HIdOp A O)
    (in custom TIH at level 50) : ham_scope.

Notation "( A : t , M )" := [(A, t, M)]
    (in custom TIH at level 30,
        A constr at level 20, t constr at level 30, M custom TIH).

Notation "x y" := (x ++ y)
    (in custom TIH at level 85, right associativity) : ham_scope.

Open Scope ham_scope.
Open Scope string_scope.

Compute <{
    "Q1" > X
}>.

Compute <{
    X
}>.

Compute <{
    ( "H" : 5 , "Q1" > X )
}>.

Compute <{
    X
}>.

Compute <{
    ( "H" : 5 , "Q1" > X )
}>.

Compute <{
    ( "x" : 5 , 10 )
    ( "x" : 5 , 15 )
}>.


Compute <{
    ( "H" : 5 , "Q1" > X )
}>.


Compute (
Site
    qubit "Q1"
    qubit "Q2" ;
Hamiltonian
    ( "H1" : 15 , "Q1" > X )
    ( "H2" : 5 , "Q2" > Y )
).

Compute <{
    ( "H2" : 22 , "Q2" > Y)
}>.
