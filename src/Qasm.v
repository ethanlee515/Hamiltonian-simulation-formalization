Require Import Reals.
Require Import String.
Require Import QWIRE.Matrix.
Require Import DecimalString.
Require Import HSF_Syntax.

Inductive QasmGate1 :=
  | Rx (theta : HScalar)
  | Ry (theta : HScalar)
  | Rz (theta : HScalar).

(* TODO *)
Definition printQasmGate1 (g : QasmGate1) : string :=
    match g with
    | Rx theta => "rx(theta)"
    | Ry theta => "ry(theta)"
    | Rz theta => "rz(theta)"
    end.

Inductive QasmGate2 :=
  | Rxx (theta : HScalar)
  | Rzz (theta : HScalar).

(* TODO *)
Definition printQasmGate2 (g : QasmGate2) : string :=
    match g with
    | Rxx theta => "rxx(theta)"
    | Rzz theta => "rzz(theta)"
    end.

Definition string_of_nat (n : nat) := NilZero.string_of_int (Nat.to_int n).

Inductive QasmTerm :=
| QasmNoOp
| QasmTerm1 (gate : QasmGate1) (loc : nat)
| QasmTerm2 (gate : QasmGate2) (loc1 loc2 : nat).

Definition printQasmTerm (t : QasmTerm) : string :=
  match t with
    | QasmNoOp => ""
    | QasmTerm1 gate loc =>
        printQasmGate1 gate ++ " sites[" ++ string_of_nat loc ++ "];\n"
    | QasmTerm2 gate loc1 loc2 =>
        printQasmGate2 gate ++
            " sites[" ++ string_of_nat loc1 ++ "]," ++
            " sites[" ++ string_of_nat loc2 ++ "];\n"
    end.

Fixpoint print_circuit (circuit : list QasmTerm) : string :=
    match circuit with
    | [] => ""
    | head :: tail => printQasmTerm head ++ (print_circuit tail)
    end.

Record QasmProgram := makeQasmProg {
    num_qubits : nat;
    circuit : list QasmTerm;
}.

(* I would use OPENQASM 3 but Qiskit doesn't fully support it *)
Definition make_qasm_header (numqubits : nat) : string :=
    "OPENQASM 2.0;\n" ++
    "include ""qelib1.inc"";\n" ++
    "qreg sites[" ++ string_of_nat numqubits ++ "];\n" ++
    "reset sites;\n".

Definition make_qasm_footer (numqubits : nat) : string :=
    "creg results[" ++ string_of_nat numqubits ++ "];\n" ++
    "measure sites -> results;\n".

Definition print_qasm_program (prog : QasmProgram) : string :=
    make_qasm_header prog.(num_qubits) ++
    print_circuit prog.(circuit) ++
    make_qasm_footer prog.(num_qubits).

Definition interpretQasm (prog : QasmProgram) :=
    (* TODO *) I (prog.(num_qubits)).
