Require Import HSF_Syntax.
Require Import Matrix_exponential.
Require Import Diagonalization.
Require Import String.
Require Import PauliRotations.
Open Scope matrix_scope.
Open Scope list_scope.

(*
     -----  Definitions  -----
 *)

Definition sem_HScalar (sc : HScalar) : R := (* TODO *) R1.

(* TODO Rewrite H_Program as record? *)
Definition count_sites (prog : H_Program) := List.length (prog.(Decls)).

(* this works for qubits, not sure about fock spaces... *)
Definition dims (P : H_Program) : nat := 2 ^ (count_sites P).

Definition locate_term (prog : H_Program) (term_id : string) : option HSF_Term :=
    (* TODO *)
    match prog.(Terms) with
    | head :: tail => Some head
    | [] => None
    end.

Fixpoint find_qubit (decls : list string) (label : string) : nat :=
    match decls with
    | [] => 0
    | head :: tail => if String.eqb head label then 0 else 1 + find_qubit tail label
    end.


Print TIH.

Fixpoint interpret_TIH (decls : list string) (term : TIH) : option (Square (2 ^ (List.length decls))%nat) :=
    let dim := ((2 ^ (List.length decls)))%nat in
    match term with
    | HAdd H1 H2 =>
        match (interpret_TIH decls H1, interpret_TIH decls H2) with
        | (Some m1, Some m2) => Some (Mplus m1 m2)
        | _ => None
        end
    | HMult H1 H2 =>
        match (interpret_TIH decls H1, interpret_TIH decls H2) with
        | (Some m1, Some m2) => Some (Mmult m1 m2)
        | _ => None
        end
    | HMultS sc H =>
        match interpret_TIH decls H with
        | Some m => Some (scale (sem_HScalar sc) m)
        | None => None
        end
    | HPauli label p =>
        let num_qubits := List.length decls in
        let loc := find_qubit decls label in
        if loc <? List.length decls then
            Some (kron (kron (I (2 ^ loc)) (PauliToMatrix p)) (I (2 ^ (num_qubits - loc - 1))))
        else
            None
    end.

(* Convert a TIH term into a Hamiltonian operator (an n x n matrix) *)
Definition interpret_term (prog : H_Program) (term : HSF_Term) : Square (dims prog) :=
    (* TODO *) I (dims prog).

(* Relational definition of Hamiltonian semantics *)
Definition sem_term {n : nat} (P : H_Program) (T : HSF_Term) (S : Square n) : Prop :=
    let H := interpret_term P T in
    let dt := sem_HScalar T.(Duration) in
    dims P = n /\ matrix_exponential (scale (-Ci * dt) H) S (* e^{-iHt} =? S *)
.

(* Prop for if label l is used in the declarations D *)

Print H_Program.
Print HSF_Term.

(* Inductive definition for valid programs *)
(* Is the empty program valid? *)
Inductive program_valid : H_Program -> Prop :=
  | program_base (d : string) :
      program_valid (makeHProg [d] [])
  | program_decl (d : string) (D : list string) (T : list HSF_Term)
                 (HP : program_valid (makeHProg D T))
                 (Hd : ~(In d D)) :
      program_valid (makeHProg (d::D) T)
  | program_tih (D : list string) (t : HSF_Term) (T : list HSF_Term)
                (HP : program_valid (makeHProg D T))
                (Ht : In t.(TermId) D):
      program_valid (makeHProg D (t :: T))
.

(* Inductive definition for semantics of programs *)
(* I make use of "dims" here so this should work with both qubits and fock spaces *)
Inductive sem_program (n : nat) : H_Program -> Square n -> Prop :=
  | sem_program_nil (D : list string)
                    (Hvalid : program_valid (makeHProg D []))
                    (Hdims : dims (makeHProg D []) = n) :
      sem_program n (makeHProg D []) (I n)
  | sem_program_cons (D : list string) (t : HSF_Term) (T : list HSF_Term) (St SP : Square n)
                     (Ht : sem_term (makeHProg D T) t St)
                     (HP : sem_program n (makeHProg D T) SP)
                     (Hvalid : program_valid (makeHProg D (t :: T)))
                     (Hdims : dims (makeHProg D (t :: T)) = n) :
      sem_program n (makeHProg D (t :: T)) (St × SP)
.

Definition ham_commute (P : H_Program) (T1 T2 : HSF_Term) : Prop :=
  let H1 := interpret_term P T1 in
  let H2 := interpret_term P T2 in
  Mat_commute H1 H2.

(*
     -----  Theorems  -----
 *)

(* Commuting Hamiltonians have the same semantics *)
Theorem commuting_Ham_semantics {n : nat} (H1 H2 : HSF_Term) :
  forall (P : H_Program) (D : list string) (St1 St2 SP1 SP2 : Square n),
    D = P.(Decls) ->
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program n (makeHProg D [H2; H1]) SP1 -> sem_program n (makeHProg D [H1; H2]) SP2 ->
    ham_commute P H1 H2 ->
    SP1 = SP2.
Proof. Admitted.


(* This theorem statement is not correct,
   but would we want something like this?

Theorem sem_program_correct :
  forall {n : nat} (P : H_Program) (S : Square n),
    sem_program P S <->
    matrix_exponential (interpret_term n (snd P)) S.
    (* not sure how hard this would be to prove *)
*)
