Require Import String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.
Require Import Qasm.
Require Import Trotterize.
Require Import Decimal.

Open Scope list_scope.
Open Scope string_scope.

Import ListNotations.

Definition parseProgram (program_text : string) : H_Program := makeHProg [] [].

Definition compile (program_text : string) (nSlices_text : string) :=
    let nSlices := Nat.of_uint (
        match (NilEmpty.uint_of_string nSlices_text) with
        | Some x => x
        | None => Nil
        end
    ) in
    let program := parseProgram program_text in
    let qasm := (trotterize program nSlices).(output) in
    print_qasm_program qasm.

Extraction "extracted/compile_coq.ml" compile.
