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


Definition interpret_HPauli (decls : list string) (p : HPauli)
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
        
Definition interpret_TIH_Term (decls : list string) (s : TIH_Term)
        : option (Square (2 ^ (List.length decls))%nat) :=
    let sc_v := sem_HScalar s.(hScale) in
    match interpret_HPaulis decls s.(hPaulis) with
    | Some pauli_v => Some (scale sc_v pauli_v)
    | None => None
    end.

Fixpoint interpret_TIH_Terms (decls : list string) (ss : list TIH_Term)
        : option (Square (2 ^ (List.length decls))%nat) :=
    match ss with
    | head :: tail =>
        match (interpret_TIH_Term decls head, interpret_TIH_Terms decls tail) with
        | (Some m1, Some m2) => Some (Mplus m1 m2)
        | _ => None
        end
    | [] => Some Zero
    end.

(* Convert a HSF term into a Hamiltonian operator (an n x n matrix) *)
Definition interpret_term (prog : H_Program) (term : HSF_Term) : option (Square (dims prog)) :=
    interpret_TIH_Terms prog.(Decls) term.(Hamiltonian).

(* Relational definition of Hamiltonian semantics *)
Definition sem_term {n : nat} (P : H_Program) (T : HSF_Term) (S : Square n) : Prop :=
    match interpret_term P T with
    | Some H =>
        let dt := sem_HScalar T.(Duration) in
        dims P = n /\ matrix_exponential (scale (-Ci * dt) H) S (* e^{-iHt} =? S *)
    | None => False
    end.

(* Lists without duplicates *)
Inductive NoDup {A : Type} : list A -> Prop :=
    | NoDup_nil : NoDup nil
    | NoDup_cons : forall x l, ~ In x l -> NoDup l -> NoDup (x::l).

(* Inductive definition for valid programs *)
(* Is the empty program valid? *)
Definition program_valid (P : H_Program) : Prop :=
  (List.length (Decls P) > 0)%nat /\ NoDup (Decls P) /\
  forall (t : HSF_Term), In t (Terms P) -> In (TermId t) (Decls P).

(* Inductive definition for semantics of programs *)
(* I make use of "dims" here so this should work with both qubits and fock spaces *)
Inductive sem_program {n : nat} : H_Program -> Square n -> Prop :=
  | sem_program_nil (D : list string)
                    (Hvalid : program_valid (makeHProg D []))
                    (Hdims : dims (makeHProg D []) = n) :
      sem_program (makeHProg D []) (I n)
  | sem_program_cons (D : list string) (t : HSF_Term) (T : list HSF_Term) (St SP : Square n)
                     (Ht : sem_term (makeHProg D T) t St)
                     (HP : sem_program (makeHProg D T) SP)
                     (Hvalid : program_valid (makeHProg D (t :: T)))
                     (Hdims : dims (makeHProg D (t :: T)) = n) :
      sem_program (makeHProg D (t :: T)) (St × SP)
.

Definition ham_commute (P : H_Program) (T1 T2 : HSF_Term) : Prop :=
    match (interpret_term P T1, interpret_term P T2) with
    | (Some H1, Some H2) => Mat_commute H1 H2
    | _ => False
    end.

(*
     -----  Theorems  -----
 *)



(* 
   Program Lemmas 
 *)

Lemma semantics_implies_program_valid {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> program_valid P.
Proof. Admitted.

Lemma term_removal_valid : forall P t T,
    program_valid P -> Terms P = t :: T -> program_valid (makeHProg (Decls P) T).
Proof.
  intros P t T HP HT. inversion HP. inversion H0. clear HP H0. split.
  - simpl. assumption.
  - split.
    + simpl. assumption.
    + simpl. intros t' Ht'. apply H2. rewrite HT. right. auto.
Qed.

Lemma no_terms_valid : forall (P : H_Program),
    program_valid P -> program_valid (makeHProg (Decls P) []).
Proof.
  intros P HP. destruct HP as [H1 [H2 H3]]. split; simpl; try auto.
  split; simpl; try auto.
  intros t Ht. contradiction.
Qed.

Lemma semantics_implies_no_terms_valid {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> program_valid (makeHProg (Decls P) []).
Proof.
  intros P S HP. apply no_terms_valid.
  remember (semantics_implies_program_valid P S HP) as goal.
  apply goal.
Qed.

Lemma extract_dims {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> dims P = n.
Proof.
  intros P S HP. inversion HP; subst; auto.
Qed.

(* Term semantics are well-formed *)
Lemma term_semantics_WF {n : nat} : forall (P : H_Program) (T : HSF_Term) (S : Square n),
    sem_term P T S -> WF_Matrix S.
Proof. Admitted.

(* Program semantics are well-formed *)
Lemma prog_semantics_WF {n : nat} : forall (P : H_Program) (S : Square n),
    sem_program P S -> WF_Matrix S.
Proof. Admitted.

Lemma prog_semantics_unique {n : nat} : forall (P : H_Program) (S1 S2 : Square n),
    sem_program P S1 -> sem_program P S2 -> S1 = S2.
Proof. Admitted.

(*
   Commuting Lemmas
 *)

Lemma ham_commute_terms : forall (P : H_Program) (T1 T2 : HSF_Term),
    ham_commute P T1 T2 ->
    exists H1 H2, interpret_term P T1 = Some H1 /\ interpret_term P T2 = Some H2 /\
                  Mat_commute H1 H2.
Proof.
  intros.
  destruct (interpret_term P T1) eqn:E1.
  - destruct (interpret_term P T2) eqn:E2.
    + exists m, m0. unfold ham_commute in H.
      rewrite E1 in H. rewrite E2 in H. auto.
    + exfalso. unfold ham_commute in H.
      rewrite E1 in H. rewrite E2 in H. auto.
  - exfalso. unfold ham_commute in H.
    rewrite E1 in H. auto.
Qed.

(* This probably belongs in MatrixExponential.v *)
Lemma mat_exp_equiv_scalar {n : nat} : forall (c : R) (M S Sc SM : Square n),
    matrix_exponential (scale c M) S ->
    matrix_exponential M SM ->
    S = scale (exp c) SM.
Proof. Admitted.

(* This probably belongs in MatrixExponential.v too *)
Lemma mat_exp_commute_add {n : nat} : forall (M N SM SN SMN : Square n),
    matrix_exponential M SM ->
    matrix_exponential N SN ->
    matrix_exponential (M .+ N) SMN ->
    Mat_commute M N ->
    SM × SN = SMN.
Proof. Admitted.

Lemma ham_commute_term_semantics {n : nat} :
  forall (P : H_Program) (H1 H2 : HSF_Term) (S1 S2 : Square n),
  sem_term P H1 S1 -> sem_term P H2 S2 ->
  ham_commute P H1 H2 -> Mat_commute S1 S2.
Proof.
  intros P H1 H2 S1 S2 HH1 HH2 Hcomm.
  destruct (ham_commute_terms P H1 H2 Hcomm) as [M1 [M2 [HM1 [HM2 HMcomm]]]]. clear Hcomm.
  unfold sem_term in HH1. rewrite HM1 in HH1. inversion HH1 as [Hd HS1]. clear HH1 HM1.
  unfold sem_term in HH2. rewrite HM2 in HH2. inversion HH2 as [Hd2 HS2]. clear HH2 HM2 Hd2.
  Admitted.


(* The semantics of a term depend only on the declarations of the program 
   (not on the Hamiltonian terms) *)
Lemma sem_term_depends_on_D {n : nat} : forall P1 P2 H (S : Square n),
    sem_term P1 H S -> Decls P1 = Decls P2 -> sem_term P2 H S.
Proof.
  intros P1 P2 H S Ht Hd. unfold sem_term in Ht.
  destruct (interpret_term P1 H) eqn:E.
  - inversion Ht. clear Ht.
     unfold sem_term. assert (H2 : interpret_term P2 H = Some m). {
      subst. rewrite <- E. unfold interpret_term. rewrite Hd. reflexivity. }
     assert (H3 : dims P1 = dims P2). {
       unfold dims. unfold count_sites. rewrite Hd. reflexivity. }
    rewrite H2. split.
    + symmetry. subst. assumption.
    + rewrite <- H3. assumption.
  - contradiction.
Qed.

Lemma two_term_program_semantics {n : nat} :
  forall (P : H_Program) (H1 H2 : HSF_Term) (St1 St2 SP : Square n),
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program {| Decls := P.(Decls); Terms := [H2; H1] |} SP ->
    SP = St2 × St1.
Proof.
  intros P H1 H2 St1 St2 SP HSt1 HSt2 HP.
  assert (HP' : sem_program {| Decls := Decls P; Terms := [H1] |} (St1 × I n)). {
    apply sem_program_cons.
    - eapply sem_term_depends_on_D.
      + apply HSt1.
      + reflexivity.
    - apply sem_program_nil. 
      + remember (semantics_implies_no_terms_valid {| Decls := Decls P; Terms := [H2; H1] |}
                                                   SP HP) as HH. clear HeqHH.
        simpl in HH. assumption.
      + remember (extract_dims {| Decls := Decls P; Terms := [H2; H1] |} SP HP) as Hdims.
        clear HeqHdims. unfold dims in *. unfold count_sites in *. simpl in *. assumption.
    - apply semantics_implies_program_valid in HP.
      eapply term_removal_valid with (t := H2) (T := [H1]) in HP.
      + simpl in HP. assumption.
      + reflexivity.
    - apply extract_dims in HP. unfold dims in *. unfold count_sites in *.
      simpl in *. assumption.
  }
  assert (HP'' : sem_program {| Decls := Decls P; Terms := [H2; H1] |} (St2 × (St1 × I n))). {
    apply sem_program_cons.
    - eapply sem_term_depends_on_D.
      + apply HSt2.
      + reflexivity.
    - assumption.
    - apply semantics_implies_program_valid in HP. assumption.
    - apply extract_dims in HP'. unfold dims in *. unfold count_sites in *.
      simpl in *. assumption.
  }
  assert (HMmultI : St1 × I n = St1). {
    apply Mmult_1_r. apply term_semantics_WF in HSt1. assumption.
  }
  rewrite HMmultI in HP''. eapply prog_semantics_unique.
  apply HP. apply HP''.
Qed.

(* Commuting Hamiltonians have the same semantics *)
Theorem commuting_Ham_semantics {n : nat} (H1 H2 : HSF_Term) :
  forall (P : H_Program) (D : list string) (St1 St2 SP1 SP2 : Square n),
    D = P.(Decls) ->
    sem_term P H1 St1 -> sem_term P H2 St2 ->
    sem_program (makeHProg D [H2; H1]) SP1 -> sem_program (makeHProg D [H1; H2]) SP2 ->
    ham_commute P H1 H2 ->
    SP1 = SP2.
Proof.
  intros P D St1 St2 SP1 SP2 HD Ht1 Ht2 HP1 HP2 Hcomm.
  remember (ham_commute_term_semantics P H1 H2 St1 St2 Ht1 Ht2 Hcomm) as H.
  clear HeqH Hcomm. rename H into Hcomm.
  assert (H : SP1 = St2 × St1 -> SP2 = St1 × St2 -> SP1 = SP2).
  { intros HSP1 HSP2. subst. symmetry. apply Hcomm. }
  apply H.
  - subst. apply (two_term_program_semantics P H1 H2 St1 St2 SP1); assumption.
  - subst. apply (two_term_program_semantics P H2 H1 St2 St1 SP2); assumption.
Qed.


(* This theorem statement is not correct,
   but would we want something like this?

Theorem sem_program_correct :
  forall {n : nat} (P : H_Program) (S : Square n),
    sem_program P S <->
    matrix_exponential (interpret_term n (snd P)) S.
    (* not sure how hard this would be to prove *)
*)
