Require Import String Extraction ExtrOcamlString.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.
Require Import Qasm.

Open Scope list_scope.
Open Scope string_scope.

Import ListNotations.

Definition parseProgram (program_text : string) : H_Program := makeHProg [] [].

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
