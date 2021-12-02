Require Import Complex.
Require Import QWIRE.Matrix.
Require Import MatrixExponential.

Inductive Pauli :=
    | Pauli_I
    | Pauli_X
    | Pauli_Y
    | Pauli_Z.

Definition XGate : Square 2 := fun (i j : nat) =>
    match (i, j) with
    | (0, 1) => RtoC 1
    | (1, 0) => RtoC 1
    | _ => RtoC 0
    end.

Definition YGate : Square 2 := fun (i j : nat) =>
    match (i, j) with
    | (0, 1) => Ci
    | (1, 0) => -Ci
    | _ => RtoC 0
    end.

Definition ZGate : Square 2 := fun (i j : nat) =>
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

(* Implemented by Qiskit *)
Parameter RXGate : R -> Square 2.
Parameter RYGate : R -> Square 2.
Parameter RZGate : R -> Square 2.
Parameter RXXGate : R -> Square 4.
Parameter RZZGate : R -> Square 4.

Axiom RXGate_Correct :
    forall (theta : R),
        matrix_exponential ((scale theta XGate)) (RXGate theta).

Axiom RYGate_Correct :
    forall (theta : R),
        matrix_exponential ((scale theta YGate)) (RYGate theta).

Axiom RZGate_Correct :
    forall (theta : R),
        matrix_exponential ((scale theta ZGate)) (RZGate theta).

Definition RXYGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RXZGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RYYGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

Definition RYZGate (t : R) : Square 4 :=
    (* TODO *) fun (i j : nat) => 0.

(* TODO correctness lemma..... *)

(* Three qubits rotation is nice to have but not top priority *)
