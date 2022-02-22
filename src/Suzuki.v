(** Pauli - TODO move back to PauliRotations.v **)

Require Import Reals.

Open Scope R_scope.

Inductive Pauli1 :=
| Pauli_I
| Pauli_X
| Pauli_Y
| Pauli_Z.

Definition reduced_Planck's_constant : R := (6.62607015 / (10 ^ 34)) / (2 * PI).

(** HS_Syntax 1.0 - TODO move to new file **)

Require Import Reals.

Record Pauli1_at_loc := make_Pauli1_at_loc
{
  mPauli1 : Pauli1;
  mLoc : nat;
}.

Record Hamiltonian_Term := make_TIH_Term
{
  mScale : R;
  mPauli : list Pauli1_at_loc;
}.

Record HS_Instruction := make_HS_Instruction
{
  mDuration : R;
  mHamiltonian : list Hamiltonian_Term;
}.

Record HS_Program := make_HS_Program
{
  mNumQubits : nat;
  mInstructions : list HS_Instruction;
}.

(** Synthesis of a single e^{i * alpha * P} **)

Require Import SQIR.
Require Import List.
Require Import Reals.
Import ListNotations.

Open Scope list_scope.
Open Scope com_scope.

Fixpoint make_left_CNOT_tree {dims : nat} (root : nat) (qubits : list nat) : base_com dims :=
  match qubits with
  | [] => skip
  | head :: tail => CNOT head root ; make_left_CNOT_tree root tail
  end.

Definition make_right_CNOT_tree {dims : nat} (root : nat) (qubits : list nat) : base_com dims :=
  make_left_CNOT_tree root (rev qubits).

Definition make_gates1 {dims : nat} (pauli : list Pauli1_at_loc) : base_com dims :=
  match pauli with
  | [] => skip
  | head :: tail =>
    match head.(mPauli1) with
    | Pauli_X => H head.(mLoc)
    | Pauli_Y => Y head.(mLoc)
    | _ => skip
    end
  end.

Fixpoint filterPauli (pauli : list Pauli1_at_loc) : list Pauli1_at_loc :=
  match pauli with
  | [] => []
  | head :: tail =>
    match head.(mPauli1) with
    | Pauli_I => filterPauli tail
    | _ => head :: filterPauli tail
    end
  end.

Definition synthesize {dims : nat} (alpha : R) (pauli : list Pauli1_at_loc) : base_com dims :=
  let p := filterPauli pauli in
  match p with
  | [] => ID 0
  | root :: rest =>
    let root_loc := root.(mLoc) in
    let rest_loc := map mLoc rest in
    let gates1 := make_gates1 p in
      gates1 ;
      make_left_CNOT_tree root_loc rest_loc ;
      Rz (2 * alpha) root_loc ;
      make_right_CNOT_tree root_loc rest_loc ;
      gates1
  end.

(** Suzuki's **)

Fixpoint Suzuki_compile2_aux (numQubits : nat)
    (duration : R)
    (terms : list Hamiltonian_Term)
    : base_com (2 ^ numQubits) :=
  match terms with
  | [] => skip
  | head :: tail =>
    synthesize (- head.(mScale) * (duration / 2) / reduced_Planck's_constant) head.(mPauli) ;
    Suzuki_compile2_aux numQubits duration tail
  end.

Definition Suzuki_compile2_first_half (numQubits : nat)
    (duration : R) (terms : list Hamiltonian_Term)
    : base_com (2 ^ numQubits) :=
  Suzuki_compile2_aux numQubits duration terms.

Definition Suzuki_compile2_second_half (numQubits : nat)
    (duration : R) (terms : list Hamiltonian_Term)
  : base_com (2 ^ numQubits) :=
  Suzuki_compile2_aux numQubits duration (terms).

Definition Suzuki_compile2 (numQubits : nat)
    (duration : R) (terms : list Hamiltonian_Term)
    : base_com (2 ^ numQubits) :=
  Suzuki_compile2_first_half numQubits duration terms ;
  Suzuki_compile2_second_half numQubits duration terms.

Definition u_k (twice_k : nat) : R :=
  1 / (4 - Rpower 4 (1 / (INR twice_k - 1))).

Fixpoint Suzuki_compile_aux (numQubits : nat)
    (duration : R) (terms : list Hamiltonian_Term) (order : nat)
    : base_com (2 ^ numQubits) :=
  match order with
  | 0 => skip (* Malformed *)
  | 1 => skip (* Malformed *)
  | 2 => Suzuki_compile2 numQubits duration terms
  | S (S p) =>
    let uk := u_k order in
    crepeat 2 (Suzuki_compile_aux numQubits (uk * duration) terms p) ;
    Suzuki_compile_aux numQubits ((1 - 4 * uk) * duration) terms p ;
    crepeat 2 (Suzuki_compile_aux numQubits (uk * duration) terms p)
  end.

Definition Suzuki_compile (numQubits : nat) (inst : HS_Instruction) (order : nat)
    : base_com (2 ^ numQubits) :=
  Suzuki_compile_aux numQubits inst.(mDuration) inst.(mHamiltonian) order.

Definition slice_instruction (inst : HS_Instruction) (trotter_number : nat) : HS_Instruction :=
  make_HS_Instruction (inst.(mDuration) / INR trotter_number) inst.(mHamiltonian).

Definition Suzuki_instruction (numQubits : nat)
    (inst : HS_Instruction) (order : nat) (trotter_number : nat) :=
  crepeat trotter_number (Suzuki_compile numQubits (slice_instruction inst trotter_number) order).

Fixpoint Suzuki_program_aux (numQubits : nat)
    (insts : list HS_Instruction) (order : nat) (trotter_number : nat) :=
  match insts with
  | [] => skip
  | head :: tail =>
    Suzuki_instruction numQubits head order trotter_number ;
    Suzuki_program_aux numQubits tail order trotter_number
  end.

Definition Suzuki_program (prog : HS_Program) (order : nat) (trotter_number : nat) :=
  Suzuki_program_aux prog.(mNumQubits) prog.(mInstructions) order trotter_number.

Definition compute_Trotter_number_Suzuki (prog : HS_Program) (order : nat) (eps : R) : nat :=
  (* TODO; Equation 56 on page 22 *) 9999.

Definition Suzuki_main (prog : HS_Program) (order : nat) (eps : R) :=
  let r := compute_Trotter_number_Suzuki prog order eps in
  Suzuki_program prog order r.
