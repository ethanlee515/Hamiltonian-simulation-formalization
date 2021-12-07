Require Import String Extraction ExtrOcamlString.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import DecimalString.

Open Scope list_scope.
Open Scope string_scope.
Open Scope ham_scope.

Import ListNotations.

Definition program_placeholder := Site
    fock "F1"    
    qubit "Q1"
    qubit "Q2"
    qubit "Q3" ;
Hamiltonian
    ( "H1" : R1 , "Q1" > X * "Q2" > Z + "Q3" > Y )
    ( "H2" : R1 , "Q2" > Y )
    ( "H3" : R1 , "F1" > c ).

Definition parseProgram (program_text : string) : H_Program := program_placeholder.

Inductive SupportedGates :=
  | Rx (loc : nat) (theta : R)
  | Ry (loc : nat) (theta : R)
  | Rz (loc : nat) (theta : R).

(* TODO Implement this *)
(* Right now it maps everything to a fixed circuit *)
Definition trotterize (program : H_Program) := [(Rx 0 R1); (Ry 0 R1); (Rz 0 R1)].

Definition string_of_nat (n : nat) := NilZero.string_of_int (Nat.to_int n).

Fixpoint write_circuit (circuit : list SupportedGates) :=
    match circuit with
    | [] => ""
    | head :: tail =>
        (match head with
        | Rx loc theta => "U(1, 0, 0) q[" ++ string_of_nat loc ++ "]\n"
        | Ry loc theta => "U(1, 0, 0) q[" ++ string_of_nat loc ++ "]\n"
        | Rz loc theta => "U(1, 0, 0) q[" ++ string_of_nat loc ++ "]\n"
        end) ++ (write_circuit tail)
    end.

(* TODO *)
Definition count_sites (program : H_Program) : nat := 3.

Definition string_of_real (r : R) := (* TODO I don't even know... *) "0.5".

Definition compile (program_text : string) :=
    let program := parseProgram program_text in
    let circuit := trotterize program in
        "OPENQASM 2.0;\n" ++
        "qreg q[" ++ string_of_nat (count_sites program) ++ "]\n" ++
        write_circuit circuit ++
        "measure_all\n".

Extraction "../extracted/compile_coq.ml" compile.
