Require Import HSF_Syntax.
Require Import Matrix_exponential.
Require Import Diagonalization.

(*
     -----  Definitions  -----
 *)


(* Convert a TIH term into a Hamiltonian operator (an n x n matrix) *)
Definition interpret_term (dims : nat) (T_term : TIH_Term) : Square dims :=
  match T_term with
  | (label, duration, T) =>
    I dims
  end.
  (* TODO: actually implement this. *)

(* this works for qubits, not sure about fock spaces... *)
Definition dims (P : H_Program) : nat := 2 ^ (length (fst P)).

(* Relational definition of Hamiltonian semantics *)
Definition sem_term {n : nat} (P : H_Program) (T : TIH_Term) (S : Square n) : Prop :=
  let H := interpret_term (dims P) T in
  let dt := snd (fst T) in
    dims P = n /\ matrix_exponential (scale (-Ci * dt) H) S (* e^{-iHt} =? S *)
.

(* Prop for if label l is used in the declarations D *)
Definition site_declared (l : String.string) (D : HDecls) : Prop :=
  exists (Q : HType), (In (Q, l) D).

Definition label_from_TIH_Term (t : TIH_Term) : String.string :=
  match t with
    (l, _, _) => l
  end.

(* Inductive definition for valid programs *)
(* Is the empty program valid? *)
Inductive program_valid : H_Program -> Prop :=
  | program_base (d : HDecl) :
      program_valid ([d], [])
  | program_decl (d : HDecl) (D : HDecls) (T : TIH_Seq)
                 (HP : program_valid (D, T))
                 (Hd : ~(site_declared (snd d) D)) :
      program_valid (d::D, T)
  | program_tih (D : HDecls) (t : TIH_Term) (T : TIH_Seq)
                (HP : program_valid (D, T))
                (Ht : site_declared (label_from_TIH_Term t) D):
      program_valid (D, t :: T)
.

(* Inductive definition for semantics of programs *)
(* I make use of "dims" here so this should work with both qubits and fock spaces *)
Inductive sem_program (n : nat) : H_Program -> Square n -> Prop :=
  | sem_program_nil (D : HDecls)
                    (Hvalid : program_valid (D, []))
                    (Hdims : dims (D, []) = n) :
      sem_program n (D, []) (I n)
  | sem_program_cons (D : HDecls) (t : TIH_Term) (T : TIH_Seq) (St SP : Square n)
                     (Ht : sem_term (D, T) t St)
                     (HP : sem_program n (D, T) SP)
                     (Hvalid : program_valid (D, t :: T))
                     (Hdims : dims (D, t :: T) = n) :
      sem_program n (D, t :: T) (St × SP)
.

Definition ham_commute (P : H_Program) (T1 T2 : TIH_Term) : Prop :=
  let H1 := interpret_term (dims P) T1 in
  let H2 := interpret_term (dims P) T2 in
  Mat_commute H1 H2.



(*
     -----  Theorems  -----
 *)

(* Commuting Hamiltonians have the same semantics *)
Theorem commuting_Ham_semantics {n : nat} (H1 H2 : TIH_Term) :
  forall (P : H_Program) (D : HDecls) (St1 St2 SP1 SP2 : Square n),
    D = fst P ->
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program n (D, [H2; H1]) SP1 -> sem_program n (D, [H1; H2]) SP2 ->
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
