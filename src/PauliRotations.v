Require Import Complex.
Require Import QWIRE.Matrix.
Require Import Matrix_exponential.

Inductive Pauli :=
    | Pauli_I
    | Pauli_X
    | Pauli_Y
    | Pauli_Z.

Definition XGate (i j : nat) :=
    match (i, j) with
    | (0, 1) => RtoC 1
    | (1, 0) => RtoC 1
    | _ => RtoC 0
    end.

Definition YGate (i j : nat) :=
    match (i, j) with
    | (0, 1) => Ci
    | (1, 0) => -Ci
    | _ => RtoC 0
    end.

Definition ZGate (i j : nat) :=
    match (i, j) with
    | (1, 0) => RtoC 1
    | (0, 1) => RtoC (-1)
    | _ => RtoC 0
    end.

Definition PauliToMatrix (p : Pauli) : Square 2 :=
    match p with
    | Pauli_I => I 2
    | Pauli_X => XGate
    | Pauli_Y => YGate
    | Pauli_Z => ZGate
    end.

Definition makeSingleQubitRotation (theta : R) (p : Pauli) : Square 2 :=
    (* TODO *)
    I 2.

Lemma SingleQubitRotation_Correct :
    forall (theta : R) (p : Pauli),
        matrix_exponential (scale theta (PauliToMatrix p)) (makeSingleQubitRotation theta p).
Proof.
    Admitted.

Definition makeTwoQubitRotation (theta : R) (p1 p2 : Pauli) : Square 4 :=
    (* TODO Write as a product of QASM-supported operations so this helps with Trotterization *)
    I 4.

Lemma TwoQubitRotation_Correct :
    forall (theta : R) (p1 p2 : Pauli),
        let p1gate := PauliToMatrix p1 in
        let p2gate := PauliToMatrix p2 in
        let p1p2 := kron p1gate p2gate in
        matrix_exponential (scale theta p1p2) (makeTwoQubitRotation theta p1 p2).
Proof.
    Admitted.

(* Three qubits rotation is nice to have but not top priority *)

(* The following should probably be moved to a different file *)

Inductive QasmOp :=
    | QasmPauli (P : Pauli)
    | QasmU (theta phi : R).

Record QasmTerm := makeQasmTerm {
    operation : QasmOp;
    location : nat;
}.

Record QasmProgram := makeQasmProg {
    num_qubits : nat;
    circuit : list QasmTerm;
}.

Definition interpretQasm (prog : QasmProgram) :=
    (* TODO *) I (prog.(num_qubits)).


        
