Require Import Complex.
Require Import QWIRE.Matrix.
Require Import MatrixExponential.
Require Import Diagonalization.

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

Definition HGate : Square 2 := fun (i j : nat) =>
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => / sqrt 2
  | (1, 0) => / sqrt 2
  | (1, 1) => - / sqrt 2
  | _ => 0
  end.

Lemma XGateDiagonalization :
  Diagonalization XGate HGate ZGate HGate.
Proof.
  Admitted.

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

(* Universal 1-qubit gate; provided by Qasm *)
Definition UGate (theta phi lambda : R) (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => cos(theta / 2)
  | (0, 1) => - Cexp lambda * sin(theta / 2)
  | (1, 0) => Cexp phi * sin(theta / 2)
  | (1, 1) => Cexp (phi + lambda) * cos(theta / 2)
  | _ => 0
  end.

Definition TYZ_Gate_dag (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => / sqrt 2
  | (1, 0) => Ci / sqrt 2
  | (1, 1) => -Ci / sqrt 2              
  | _ => 0
  end.

Lemma TYZ_Gate_dag_impl :
  TYZ_Gate_dag = UGate (PI / 2) (PI / 2) PI.
Proof.
Admitted.

Definition TYZ_Gate (i j : nat) : C :=
  match (i, j) with
  | (0, 0) => / sqrt 2
  | (0, 1) => -Ci / sqrt 2
  | (1, 0) => / sqrt 2          
  | (1, 1) => Ci / sqrt 2              
  | _ => 0
  end.

Lemma TYZ_Gate_impl :
  TYZ_Gate = UGate (PI / 2) 0 (PI / 2).
Proof.
Admitted.

Lemma TYZ_correct :
  Diagonalization YGate TYZ_Gate_dag ZGate TYZ_Gate.
Proof.
Admitted.
