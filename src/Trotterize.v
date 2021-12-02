Require Import String.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import Qasm.
Require Import Semantics.
Require Import PauliRotations.
Require Import MatrixExponential.

Definition QasmSemantics (prog : QasmProgram) : Square (2 ^ prog.(num_qubits)) :=
    (* TODO *) Zero.

Definition trotterize (prog : H_Program) (slices : nat) : QasmProgram := makeQasmProg (count_sites prog)
[
    QasmTerm1 (Rx 1) 0 ;
    QasmTerm1 (Ry 1) 2 ;
    QasmTerm2 (Rzz 1) 0 1
].

Theorem trotterize_correct :
    forall (hprog : H_Program),
        let N := dims hprog in
        exists correct_sem,
            sem_program hprog correct_sem /\
            seq_conv (MatrixMetricSpace N) (fun nSlices => QasmSemantics (trotterize hprog nSlices)) correct_sem. 
Proof.
    Admitted.
