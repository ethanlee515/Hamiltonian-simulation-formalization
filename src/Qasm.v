Require Import Reals.
Require Import String.
Require Import QWIRE.Matrix.
Require Import DecimalString.
Require Import HSF_Syntax.
Require Import PauliRotations.
Require Import MatrixExponential.
Require Import Semantics.

(* -- QASM AST -- *)

Inductive QasmGate1 :=
| Rx (theta : HScalar)
| Ry (theta : HScalar)
| Rz (theta : HScalar)
| QasmH
| QasmU (theta phi lambda : HScalar).

Inductive QasmGate2 :=
  | Rxx (theta : HScalar)
  | Rzz (theta : HScalar).


Inductive QasmTerm :=
| QasmTerm1 (gate : QasmGate1) (loc : nat)
| QasmTerm2 (gate : QasmGate2) (loc1 loc2 : nat).


Record QasmProgram := makeQasmProg {
    num_qubits : nat;
    circuit : list QasmTerm;
}.

(* -- QASM Semantics -- *)

Definition padIs (num_qubits : nat) (g : Square 2) (loc : nat) : Square (2 ^ num_qubits) :=
  kron (kron (I (2 ^ loc)) g) (I (2 ^ (num_qubits - loc - 1))).

Definition QasmInstSemantics (num_qubits : nat)
           (inst : QasmTerm) (sem : Square (2 ^ num_qubits)) :=
  match inst with
  | QasmTerm1 gate loc =>
      let u :=
        match gate with
        | Rx theta => RXGate (sem_HScalar theta)
        | Ry theta => RYGate (sem_HScalar theta)
        | Rz theta => RZGate (sem_HScalar theta)
        | QasmH => HGate
        | QasmU theta phi lambda => UGate (sem_HScalar theta) (sem_HScalar phi) (sem_HScalar lambda)
        end
      in
      padIs num_qubits u loc = sem
  | QasmTerm2 gate loc1 loc2 =>
      let g :=
        match gate with
        | Rxx theta => XGate
        | Rzz theta => ZGate
        end
      in
      let t :=
        match gate with
        | Rxx theta => sem_HScalar theta
        | Rzz theta => sem_HScalar theta
        end
      in
      let p1 := padIs num_qubits g loc1 in
      let p2 := padIs num_qubits g loc2 in
      let tp1p2 := scale (- Ci * t / 2) (Mmult p1 p2) in
      matrix_exponential tp1p2 sem
  end.

Fixpoint QasmInstsSemantics (num_qubits : nat)
           (insts : list QasmTerm) (sem : Square (2 ^ num_qubits)) :=
  match insts with
  | head :: tail => exists sem_head sem_tail,
      QasmInstSemantics num_qubits head sem_head /\
        QasmInstsSemantics num_qubits tail sem_tail /\
        sem = Mmult sem_head sem_tail
  | [] => sem = I (2 ^ num_qubits)
  end.

Definition QasmSemantics (prog : QasmProgram) (sem : Square (2 ^ (prog.(num_qubits)))) :=
  QasmInstsSemantics prog.(num_qubits) prog.(circuit) sem.

(* -- QASM Printer -- *)

(* TODO test me against actual Qasm compiler *)

Definition string_of_nat (n : nat) := NilZero.string_of_int (Nat.to_int n).

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

Definition printQasmGate2 (g : QasmGate2) : string :=
    match g with
    | Rxx theta => "rxx(" ++ printHScalar theta ++ ")"
    | Rzz theta => "rzz(" ++ printHScalar theta ++ ")"
    end.

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
