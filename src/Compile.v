Require Import String Extraction ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.
Require Import Qasm.
Require Import Trotterize.

Open Scope list_scope.
Open Scope string_scope.

Import ListNotations.

Definition parseProgram (program_text : string) : H_Program := makeHProg [] [].

Definition compile (program_text : string) (nSlices : nat) :=
    let program := parseProgram program_text in
    let qasm := trotterize program nSlices in
    print_qasm_program qasm.

Extraction "extracted/compile_coq.ml" compile.
