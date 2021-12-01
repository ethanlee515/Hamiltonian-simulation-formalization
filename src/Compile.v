Require Import String Extraction ExtrOcamlString.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.
Require Import Qasm.

Open Scope list_scope.
Open Scope string_scope.
Open Scope ham_scope.

Import ListNotations.

Definition program_placeholder := Site
    fock "F1"    
    qubit "Q1"
    qubit "Q2"
    qubit "Q3" ;
Hamiltonian
    ( "H1" : R1 , "Q1" > X * "Q2" > Z + "Q3" > Y )
    ( "H2" : R1 , "Q2" > Y )
    ( "H3" : R1 , "F1" > c ).

Definition parseProgram (program_text : string) : H_Program := program_placeholder.

(* TODO Implement this *)
(* Right now it maps everything to a fixed circuit *)
Definition trotterize (program : H_Program) : QasmProgram := makeQasmProg 3
[
    QasmTerm1 (Rx 1) 0 ;
    QasmTerm1 (Ry 1) 2 ;
    QasmTerm2 (Rzz 1) 0 1
].

Definition compile (program_text : string) :=
    let program := parseProgram program_text in
    let qasm := trotterize program in
    print_qasm_program qasm.

Extraction "extracted/compile_coq.ml" compile.
