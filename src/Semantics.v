Require Import HSF_Syntax.
Require Import MatrixExponential.
Require Import Diagonalization.
Require Import String.
Require Import PauliRotations.
Open Scope matrix_scope.
Open Scope list_scope.

(*
     -----  Definitions  -----
 *)

Fixpoint sem_HScalar (sc : HScalar) : R :=
    match sc with
    | HScAdd s1 s2 => (sem_HScalar s1) + (sem_HScalar s2)
    | HScMult s1 s2 => (sem_HScalar s1) * (sem_HScalar s2)
    | HScSub s1 s2 => (sem_HScalar s1) - (sem_HScalar s2)
    | HScDiv s1 s2 => (sem_HScalar s1) / (sem_HScalar s2)
    | HScExp s => exp (sem_HScalar s)
    | HScCos s => cos (sem_HScalar s)
    | HScSin s => sin (sem_HScalar s)
    | HScReal v s => v
    end.

(* TODO Rewrite H_Program as record? *)
Definition count_sites (prog : H_Program) := List.length (prog.(Decls)).

(* this works for qubits, not sure about fock spaces... *)
Definition dims (P : H_Program) : nat := 2 ^ (count_sites P).

Fixpoint find_qubit (decls : list string) (label : string) : nat :=
    match decls with
    | [] => 0
    | head :: tail => if String.eqb head label then 0 else 1 + find_qubit tail label
    end.


Fixpoint interpret_HPauli (decls : list string) (p : HPauli)
        : option (Square (2 ^ (List.length decls))%nat) :=
    match p with HIdOp label pauli =>
        let num_qubits := List.length decls in
        let loc := find_qubit decls label in
        if loc <? List.length decls then
            Some (kron (kron (I (2 ^ loc)) (PauliToMatrix pauli)) (I (2 ^ (num_qubits - loc - 1))))
        else
            None
    end.

Fixpoint interpret_HPaulis (decls : list string) (ps : list HPauli)
        : option (Square (2 ^ (List.length decls))%nat) :=
    match ps with
    | head :: tail =>
        match (interpret_HPauli decls head, interpret_HPaulis decls tail) with
        | (Some m1, Some m2) => Some (Mmult m1 m2)
        | _ => None
        end
    | [] => Some (I (2 ^ (List.length decls))%nat)
    end.
        
Fixpoint interpret_Summand (decls : list string) (s : Summand)
        : option (Square (2 ^ (List.length decls))%nat) :=
    let sc_v := sem_HScalar s.(hScale) in
    match interpret_HPaulis decls s.(hPaulis) with
    | Some pauli_v => Some (scale sc_v pauli_v)
    | None => None
    end.

Fixpoint interpret_Summands (decls : list string) (ss : list Summand)
        : option (Square (2 ^ (List.length decls))%nat) :=
    match ss with
    | head :: tail =>
        match (interpret_Summand decls head, interpret_Summands decls tail) with
        | (Some m1, Some m2) => Some (Mplus m1 m2)
        | _ => None
        end
    | [] => Some Zero
    end.

(* Convert a TIH term into a Hamiltonian operator (an n x n matrix) *)
Definition interpret_term (prog : H_Program) (term : HSF_Term) : option (Square (dims prog)) :=
    interpret_Summands prog.(Decls) term.(Hamiltonian).

(* Relational definition of Hamiltonian semantics *)
Definition sem_term {n : nat} (P : H_Program) (T : HSF_Term) (S : Square n) : Prop :=
    match interpret_term P T with
    | Some H =>
        let dt := sem_HScalar T.(Duration) in
        dims P = n /\ matrix_exponential (scale (-Ci * dt) H) S (* e^{-iHt} =? S *)
    | None => False
    end.

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
    match (interpret_term P T1, interpret_term P T2) with
    | (Some H1, Some H2) => Mat_commute H1 H2
    | _ => False
    end.

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
