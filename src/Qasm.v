Require Import Reals.
Require Import String.
Require Import QWIRE.Matrix.
Require Import DecimalString.
Require Import HSF_Syntax.

(* TODO test me against actual Qasm compiler *)
Fixpoint printHScalar (sc : HScalar) : string :=
  match sc with
  | HScAdd sc1 sc2 => "(" ++ printHScalar sc1 ++ ") + (" ++ printHScalar sc2 ++ ")"         
  | HScMult sc1 sc2 => "(" ++ printHScalar sc1 ++ ") * (" ++ printHScalar sc2 ++ ")"
  | HScSub sc1 sc2 => "(" ++ printHScalar sc1 ++ ") - (" ++ printHScalar sc2 ++ ")"
  | HScDiv sc1 sc2 => "(" ++ printHScalar sc1 ++ ") / (" ++ printHScalar sc2 ++ ")"
  | HScExp sc => "exp(" ++ printHScalar sc ++ ")"
  | HScCos sc => "cos(" ++ printHScalar sc ++ ")"
  | HScSin sc => "sin(" ++ printHScalar sc ++ ")"
  | HScReal _ s => s
  end.

Inductive QasmGate1 :=
| Rx (theta : HScalar)
| Ry (theta : HScalar)
| Rz (theta : HScalar)
| QasmH
| QasmU (theta phi lambda : HScalar).

Definition printQasmGate1 (g : QasmGate1) : string :=
    match g with
    | Rx theta => "rx(" ++ printHScalar theta ++ ")"
    | Ry theta => "ry(" ++ printHScalar theta ++ ")"
    | Rz theta => "rz(" ++ printHScalar theta ++ ")"
    | QasmH => "h"
    | QasmU theta phi lambda => "u(" ++ printHScalar theta ++ ", " ++
                                     printHScalar phi ++ ", " ++
                                     printHScalar lambda ++ ")"
    end.

Inductive QasmGate2 :=
  | Rxx (theta : HScalar)
  | Rzz (theta : HScalar).

Definition printQasmGate2 (g : QasmGate2) : string :=
    match g with
    | Rxx theta => "rxx(" ++ printHScalar theta ++ ")"
    | Rzz theta => "rzz(" ++ printHScalar theta ++ ")"
    end.

Definition string_of_nat (n : nat) := NilZero.string_of_int (Nat.to_int n).

Inductive QasmTerm :=
| QasmTerm1 (gate : QasmGate1) (loc : nat)
| QasmTerm2 (gate : QasmGate2) (loc1 loc2 : nat).

Definition printQasmTerm (t : QasmTerm) : string :=
  match t with
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
