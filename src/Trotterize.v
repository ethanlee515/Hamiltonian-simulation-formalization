Require Import String.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import Qasm.
Require Import Semantics.
Require Import PauliRotations.

Definition trotterize (prog : H_Program) : QasmProgram := makeQasmProg (count_sites prog)
[
    QasmTerm1 (Rx 1) 0 ;
    QasmTerm1 (Ry 1) 2 ;
    QasmTerm2 (Rzz 1) 0 1
].
