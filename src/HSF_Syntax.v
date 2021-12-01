Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import Reals.
Require Export QWIRE.Matrix.

Inductive HOp := HI | HX | HY | HZ.

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

Inductive TIH :=
    | HAdd (h1 h2 : TIH)
    | HMult (h1 h2 : TIH)
    | HMultS (s : HScalar) (h: TIH)
    | HPauli (id: string) (op: HOp).

Record HSF_Term := makeHSF_Term
{
    TermId : string;
    Duration : HScalar;
    Hamiltonian : TIH;
}.

Record H_Program := makeHProg
{
    Decls : list string;
    Terms : list HSF_Term;
}.
