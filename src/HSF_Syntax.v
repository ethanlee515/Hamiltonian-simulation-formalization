Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Reals.
Require Import PauliRotations.
Require Export QWIRE.Matrix.

Inductive HScalar :=
    | HScAdd (s1 s2 : HScalar)
    | HScMult (s1 s2 : HScalar)
    | HScSub (s1 s2 : HScalar)
    | HScDiv (s1 s2 : HScalar)
    | HScExp (s : HScalar)
    | HScCos (s : HScalar)
    | HScSin (s : HScalar)
    | HScReal (r : R) (literal : string)
        (* Recording the string for trotterization *).

Inductive HPauli := HIdOp (loc : string) (p : Pauli).

Record Summand := makeSummand
{
    hScale : HScalar;
    hPaulis : list HPauli;
}.

Record HSF_Term := makeHSF_Term
{
    TermId : string;
    Duration : HScalar;
    Hamiltonian : list Summand;
}.

Record H_Program := makeHProg
{
    Decls : list string;
    Terms : list HSF_Term;
}.
