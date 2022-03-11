(** Pauli - taken from suzuki.v, possibly originally taken from PauliRotations.v;
            this will need to be fixed **)

Require Import Reals.
From Coq Require Import Lia.

Open Scope R_scope.

Inductive Pauli1 :=
| Pauli_I
| Pauli_X
| Pauli_Y
| Pauli_Z.

Record Pauli1_at_loc := make_Pauli1_at_loc
{
  pauli : Pauli1;
  loc : nat;
}.





(* Paulihedral-like implementation *)

Require Import List.
Import ListNotations.
Require Import Mergesort.
Require Import Orders.

Record pauli_string := make_pauli_string
{
  param : R;
  pauli_list : list Pauli1_at_loc;
}.

(* Assumes 1-indexing of sites *)
Inductive pauli_list_WF : list Pauli1_at_loc -> Prop :=
| pl_WF_singleton (p : Pauli1) :
    pauli_list_WF [make_Pauli1_at_loc p 1]
| pl_WF_cons (p : Pauli1)
             (n : nat)
             (PL : list Pauli1_at_loc)
             (H_WF : pauli_list_WF PL)
             (H_len : length PL = n) :
    pauli_list_WF ((make_Pauli1_at_loc p (n+1)) :: PL).

Definition pauli_string_WF (P : pauli_string) :=
  P.(param) > 0 /\ pauli_list_WF P.(pauli_list).





(* Define an ordering for Paulis (X < Y < Z < I) so strings can be sorted *)
Local Coercion is_true : bool >-> Sortclass.
Module PauliStringOrder <: TotalTransitiveLeBool.

  Definition t := pauli_string.

  Definition compare_paulis (p1 p2 : Pauli1) : comparison :=
    match p1, p2 with
    | Pauli_X, Pauli_X => Eq
    | Pauli_Y, Pauli_Y => Eq
    | Pauli_Z, Pauli_Z => Eq
    | Pauli_I, Pauli_I => Eq
    | Pauli_X, _ => Lt
    | _, Pauli_X => Gt
    | Pauli_Y, _ => Lt
    | _, Pauli_Y => Gt
    | Pauli_Z, _ => Lt
    | _, Pauli_Z => Gt
    end.

  Fixpoint leq_pauli_lists (pl1 pl2 : list Pauli1_at_loc) :=
    match pl1, pl2 with
    | [], [] => true
    | [], _ => true  (* pauli strings not well-formed, should be the same length *)
    | _, [] => false (* pauli strings not well-formed, should be the same length *)
    | p1 :: pl1', p2 :: pl2' => 
      match compare_paulis p1.(pauli) p2.(pauli) with
      | Lt => true
      | Gt => false
      | Eq => leq_pauli_lists pl1' pl2'
      end
    end.
  
  Definition leb (ps1 ps2 : pauli_string) :=
    leq_pauli_lists ps1.(pauli_list) ps2.(pauli_list).

  Theorem leb_total : forall ps1 ps2, leb ps1 ps2 \/ leb ps2 ps1.
  Proof.
    intros. unfold leb.
    remember (pauli_list ps1) as pl1. remember (pauli_list ps2) as pl2. clear Heqpl1 Heqpl2.
    induction pl1 as [|p1 pl1']; induction pl2 as [|p2 pl2']; auto.
    Admitted.
  
  Theorem leb_trans : Transitive leb.
  Proof.
    Admitted.
End PauliStringOrder.



Definition eqPaulib_nonI (p1 p2 : Pauli1) : bool :=
  match p1, p2 with
  | Pauli_X, Pauli_X => true
  | Pauli_Y, Pauli_Y => true
  | Pauli_Z, Pauli_Z => true
  | _, _ => false
  end.

Locate "+".
Check Init.Nat.add.

(* Compute overlap of two pauli strings (number of non-identity paulis in common) *)
Fixpoint overlap_helper (pl1 pl2 : list Pauli1_at_loc) : option nat :=
  match pl1, pl2 with
  | [], [] => Some 0%nat
  | p1 :: pl1', p2 :: pl2' =>
    match overlap_helper pl1' pl2' with
    | None => None
    | Some x =>
      if eqPaulib_nonI (pauli p1) (pauli p2)
      then Some (1 + x)%nat
      else Some x
    end
  | _, _ => None
  end.

Definition overlap (ps1 ps2 : pauli_string) : option nat :=
  overlap_helper (pauli_list ps1) (pauli_list ps2).

Fixpoint In_bool_nat (x : nat) (L : list nat) : bool :=
  match L with
  | [] => false
  | y :: L' => orb (x =? y) (In_bool_nat x L')
  end.

(* Find the pair (overlap, index) of the consecutive Pauli strings with maximum overlap,
   excluding the strings which are already paired.
   Return None if pss is malformed or if there are no unpaired strings left *)
Fixpoint max_overlap_helper (pss : list pauli_string) (i : nat) (paired : list nat)
  : option (prod nat nat) :=
  (* Defined with many match statements to make Coq happy *)
  match pss with
  | [] => None
  | ps1 :: pss' =>
    (* if string i or i+1 has already been paired *)
    if In_bool_nat i paired || In_bool_nat (i+1) paired
    then max_overlap_helper (pss') (i+1) paired (* skip it *)
    else
      match pss' with
      | [] => None
      | ps2 :: pss'' =>
        match overlap ps1 ps2 with
        | None => None
        | Some ov =>
          match max_overlap_helper (pss') (i+1) paired with
          | None => Some (ov, i)
          | Some (ov', i') => if ov' <? ov then Some (ov, i) else Some (ov', i')
          end
        end
      end
  end.    

(* Find the index of the consecutive Pauli strings with maximum overlap,
   excluding the strings which are already paired.
   Return None if pss is malformed or if there are no unpaired strings left *)
Definition max_overlap_idx (pss : list pauli_string) (paired : list nat) : option nat :=
  match max_overlap_helper pss 0 paired with
  | None => None
  | Some (ov, i) => Some i
  end.


(* Pair up the pauli strings *)
Fixpoint pair_pauli_strings_helper (pss : list pauli_string) (paired : list nat) (fuel : nat)
  : list (prod nat nat) :=
  match fuel with
  | 0 => []
  | S n =>
    match max_overlap_idx pss paired with
    | None => []
    | Some i =>
      (pair i (i+1)%nat) :: pair_pauli_strings_helper pss (i :: (i+1)%nat :: paired) n
    end
  end.



(* Define an ordering for nat pairs (a, b) so nat pairs can be sorted *)
Module PairOrder <: TotalTransitiveLeBool.

  Definition t := prod nat nat.

  Definition leb (p q : prod nat nat) :=
    if fst p =? fst q then snd p <=? snd q else fst p <=? fst q.

  Theorem leb_total : forall p1 p2, leb p1 p2 \/ leb p2 p1.
  Proof.
    assert (totality : forall a1 a2, a1 <=? a2 \/ a2 <=? a1). {
      induction a1; destruct a2; simpl; auto.
    }
    intros. unfold leb. rewrite Nat.eqb_sym.
    destruct (fst p2 =? fst p1) eqn:E; apply totality.
  Qed.
  
  Theorem leb_trans : Transitive leb.
  Proof.
    assert (trans : Transitive Nat.leb). {
      intros x y z H1 H2.
      inversion H1 as [H1']; apply leb_complete in H1'; clear H1.
      inversion H2 as [H2']; apply leb_complete in H2'; clear H2.
      apply leb_correct.
      apply Nat.le_trans with y; auto.
    } 
    intros p1 p2 p3 H1 H2. unfold Transitive in trans.
    unfold leb in *. destruct (fst p1 =? fst p3) eqn:E.
    Admitted.
    
End PairOrder.

(* Use this to sort nat pairs *)
Module Import NatPairSort := Sort PairOrder.


(* Pair pauli strings. Input is a list of pauli strings in the desired order. Output is
   a sorted list of indices to synthesize, where omitted indices represent unpaired strings. 
   There should not be more than one omitted index at a time (prove this?).
   e.g., [(0,1),(2,3),(5,6)].
*)  
Definition pair_pauli_strings (pss : list pauli_string) : list (prod nat nat) :=
  let pairs := pair_pauli_strings_helper pss [] (length pss) in
  sort pairs.



(* Synthesize circuits *)
Require Import SQIR.
Open Scope com_scope.

(* Find indices where 2 pauli strings have common (active) paulis *)
Definition mutual_pos (ps1 ps2 : pauli_string) : list nat :=
  let fix  mutual_pos_aux (pl1 pl2 : list Pauli1_at_loc) (i : nat) : list nat :=
      match pl1, pl2 with
      | p1 :: pl1', p2 :: pl2' =>
        if eqPaulib_nonI (pauli p1) (pauli p2)
        then i :: (mutual_pos_aux pl1' pl2' (i+1)%nat)
        else mutual_pos_aux pl1' pl2' (i+1)%nat
      | _, _ => []
      end
  in
  mutual_pos_aux (pauli_list ps1) (pauli_list ps2) 0%nat.

(* Find indices where a pauli string has non-identiy paulis *)
Definition active_sites (ps : pauli_string) : list nat :=
  let fix  active_sites_aux (pl : list Pauli1_at_loc) (i : nat) : list nat :=
      match pl with
      | [] => []
      | p :: pl' =>
        match pauli p with
        | Pauli_I => active_sites_aux pl' (i+1)%nat
        | _ => i :: active_sites_aux pl' (i+1)%nat
        end
      end
  in
  active_sites_aux (pauli_list ps) 0%nat.

Fixpoint compute_CNOT_tree_aux (locs : list nat) : list (prod nat nat) :=
  match locs with
  | [] => []
  | x :: locs' =>
    match locs' with
    | [] => []
    | y :: _ => (x, y) :: compute_CNOT_tree_aux locs'
    end
  end.


(* l1\l2 -> return l1 with the elements of l2 removed *)
Fixpoint setdiff {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) (l1 l2 : list A) : list A :=
  match l2 with
  | [] => l1
  | x :: l2' => setdiff eq_dec (remove eq_dec x l1) l2'
  end.     

(* Input:
      nodes := list of indices of qubits which need to be connected by CNOT tree
      linked := list of indices of qubits which should be linked in CNOT tree to allow gate 
                cancelation
   Output: description of CNOT tree, (cnotset, root)
      cnotset := ordered list of qubit pairs to connect with CNOTS;
                 of the form [(control, target), ...]
      root := root of CNOT tree
 *)
Definition compute_CNOT_tree (nodes linked : list nat) : prod (list (prod nat nat)) nat :=
  let unlinked := setdiff Nat.eq_dec nodes linked in
  let cnot_order := linked ++ unlinked in
  (compute_CNOT_tree_aux cnot_order, last cnot_order 0%nat).


(* Synthesize the single qubits gates for a pauli string *)
Definition synthesize_single_qubit_gates {dims : nat} (ps : pauli_string) : base_com dims :=
  let fix ssqg_aux {dims : nat} (pl : list Pauli1_at_loc) : base_com dims :=
      match pl with
      | [] => skip
      | p :: pl' =>
        match pauli p with
        | Pauli_X => H (loc p) ; ssqg_aux pl'
        | Pauli_Y => Y (loc p) ; ssqg_aux pl'
        | _ => ssqg_aux pl'
        end
      end
  in
  ssqg_aux (pauli_list ps).

(* Turn cnotset into a sequence of CNOTS *)
Fixpoint synthesize_CNOT_tree {dims : nat} (cnotset : list (prod nat nat)) : base_com dims :=
  match cnotset with
  | [] => skip
  | (c, t) :: cnotset' => CNOT c t ; synthesize_CNOT_tree cnotset'
end.

(* 1) single qubit gates
   2) CNOT tree
   3) rotation gate
   4) reversed CNOT tree
   5) single qubit gates
 *)
Definition synthesize_pauli_string {dims : nat} (ps : pauli_string)
           (cnotset : list (prod nat nat)) (root : nat) : base_com dims :=
  synthesize_single_qubit_gates ps ;
  synthesize_CNOT_tree cnotset ;
  Rz (2*(param ps)) root;
  synthesize_CNOT_tree (rev cnotset) ;
  synthesize_single_qubit_gates ps.

                                
Definition synthesize_single_string {dims : nat} (ps : pauli_string) : base_com dims :=
  let (cnotset, root) := compute_CNOT_tree (active_sites ps) []
  in synthesize_pauli_string ps cnotset root.

Definition synthesize_pair_of_strings {dims : nat} (ps1 ps2 : pauli_string) : base_com dims :=
  let nodes1 := active_sites ps1 in
  let nodes2 := active_sites ps2 in
  let linked := mutual_pos ps1 ps2 in
  let (cnotset1, root1) := compute_CNOT_tree nodes1 linked in
  let (cnotset2, root2) := compute_CNOT_tree nodes2 linked in
  synthesize_pauli_string ps1 cnotset1 root1;
  synthesize_pauli_string ps2 cnotset2 root2.

(* kinda hacky -- might need to simplify to make proofs easier -- maybe change the pairing 
   procedure so that pss is the decreasing argument in this function? *)
Fixpoint synthesize_paulihedral_circuit {dims : nat} (pss : list pauli_string)
         (pairs : list (prod nat nat)) (next : nat) : base_com dims :=
  let default := make_pauli_string 0 [] in
  if length pss <=? next
  then skip (* might want to replace with some other definition of an empty program *)
  else
    match pairs with
      (* There are no more paired strings but there is one last unpaired string *)
    | [] => synthesize_single_string (last pss default)
    | (a, b) :: pairs' =>
      if next <? a (* if there is an unpaired string before a *)
      then synthesize_single_string (nth next pss default) ;
           synthesize_pair_of_strings (nth a pss default) (nth b pss default) ;
           synthesize_paulihedral_circuit pss pairs' (b+1)
      else synthesize_pair_of_strings (nth a pss default) (nth b pss default) ;
           synthesize_paulihedral_circuit pss pairs' (b+1)
    end.



Module Import PauliStringSort := Sort PauliStringOrder. (* For sorting pauli strings *)

Definition run_Paulihedral {dims : nat} (pss : list pauli_string) : base_com dims :=
  let lexico_sorted_pss := sort pss in
  let pairs := pair_pauli_strings lexico_sorted_pss in
  synthesize_paulihedral_circuit pss pairs 0.






Open Scope nat_scope.
Check 0::1::3::4::5::[].
Eval compute in (compute_CNOT_tree (0::1::3::4::5::[]) (1::3::[])).

Definition ps1 : pauli_string := make_pauli_string 0.5 (
                                                     (make_Pauli1_at_loc Pauli_Z 0) ::
                                                       (make_Pauli1_at_loc Pauli_X 1)
                                                       ::[]).

Compute synthesize_single_qubit_gates ps1.

(* TODO:
  1) Check whether I can use param in synthesize_pauli_string or if I need to scale it like Suzuki
  2) Check if Y gate is okay or if I need to use something else in synthesize_single_qubit_gates -- qiskit uses HS^\dagger, Paulihedral uses HS
*)
