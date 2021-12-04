Require Import String.
Require Import Reals.
Require Import List.
Require Import HSF_Syntax.
Require Import Qasm.
Require Import Semantics.
Require Import PauliRotations.
Require Import MatrixExponential.

Definition find_qubit_opt (decls : list string) (site : string) : option nat :=
  let loc := find_qubit decls site in
  if Nat.eqb loc (List.length decls) then None else Some loc.


Definition makeQT1 (p : Pauli) (theta : HScalar) (loc : nat) :=
  match p with
  | Pauli_I => []
  | Pauli_X => [QasmTerm1 (Rx theta) loc]
  | Pauli_Y => [QasmTerm1 (Ry theta) loc]
  | Pauli_Z => [QasmTerm1 (Rz theta) loc]
  end.

Definition makeQT2_opt (p1 p2 : Pauli) (theta : HScalar) (loc1 loc2 : nat) :=
  (* TODO *) Some [QasmTerm2 (Rxx theta) loc1 loc2].

Definition natToHSc (n : nat) := (* TODO *) HScReal R1 "1".

Definition sliceTerm (decls : list string) (duration : HScalar) (term : TIH_Term) (nSlices : nat) :=
  let theta := HScDiv (HScMult duration term.(hScale)) (natToHSc nSlices) in
  match term.(hPaulis) with
  | [] => Some []
  | [HIdOp site p] =>
      match find_qubit_opt decls site with
      | None => None
      | Some loc => Some (makeQT1 p theta loc)
      end
  | [HIdOp site1 p1; HIdOp site2 p2] =>
      match (find_qubit_opt decls site1, find_qubit_opt decls site2) with
      | (Some loc1, Some loc2) => makeQT2_opt p1 p2 theta loc1 loc2
      | _ => None
      end
  | _ => None (* Too nonlocal *)
  end.


Fixpoint sliceTerms (decls : list string)
         (duration : HScalar)
         (terms : list TIH_Term)
         (nSlices : nat) :=
  match terms with
  | head :: tail =>
      match (sliceTerm decls duration head nSlices, sliceTerms decls duration tail nSlices) with
      | (Some head_insts, Some tail_insts) => Some (head_insts ++ tail_insts)
      | _ => None
      end
  | [] => Some []
  end.

Print HSF_Term.

Definition sliceInst (decls : list string) (inst : HSF_Term) (nSlices : nat) :=
  sliceTerms decls inst.(Duration) inst.(Hamiltonian) nSlices.

Fixpoint accSlices (slice : list QasmTerm) (nSlices : nat) :=
  match nSlices with
  | O => []
  | S pr => slice ++ (accSlices slice pr)
  end.

Definition trotterizeInst (decls : list string) (inst : HSF_Term) (nSlices : nat) :=
  match sliceInst decls inst nSlices with
  | Some slice => Some (accSlices slice nSlices)
  | None => None
  end.

Fixpoint trotterizeInsts (decls : list string) (insts : list HSF_Term) (nSlices : nat) :=
  match insts with
  | head :: tail =>
      match (trotterizeInst decls head nSlices, trotterizeInsts decls tail nSlices) with
      | (Some qasm_head, Some qasm_tail) => Some (qasm_head ++ qasm_tail)
      | _ => None
      end
  | [] => Some []
  end.

Record trotterize_result := makeTrotRes
{
  successful : bool;
  output : QasmProgram;
}.

Definition idProg := makeQasmProg 0 [].

Definition trotterize (prog : H_Program) (nSlices : nat) :=
  match trotterizeInsts prog.(Decls) prog.(Terms) nSlices with
  | Some qasm_insts => makeTrotRes true (makeQasmProg (count_sites prog) qasm_insts)
  | None => makeTrotRes false idProg
  end.

Definition QasmSemantics (prog : QasmProgram) : Square (2 ^ prog.(num_qubits)) :=
    (* TODO *) Zero.

Theorem trotterize_correct :
  forall (hprog : H_Program),
      (forall nSlices, (trotterize hprog nSlices).(successful) = false) (* Cannot Trotterize *) \/
      (forall nSlices, (trotterize hprog nSlices).(successful) = true (* Can Trotterize *) /\
        exists correct_sem,
          sem_program hprog correct_sem /\
          seq_conv (MatrixMetricSpace (dims hprog))
            (fun nSlices => QasmSemantics (trotterize hprog nSlices).(output)) correct_sem
      ).
Proof.
    Admitted.
