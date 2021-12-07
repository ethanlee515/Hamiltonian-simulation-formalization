Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.
Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Definition isPeriod (c : ascii) : bool :=
  let  n:= nat_of_ascii c in (n =? 46).

Inductive chartype := white | alpha | digit | period | ham_name | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else if isPeriod c then 
    period
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.
Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "[" =>
      tk ++ ["["]::(tokenize_helper other [] xs')
    | _, _, "]" =>
      tk ++ ["]"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | digit,period,x => 
      tokenize_helper digit (x::acc) xs'
    |period, digit, x => 
      tokenize_helper period (x::acc) xs' 
    | alpha, digit, x =>
      tokenize_helper alpha (x::acc) xs' 
    | other,other,x =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

(*Example tokenize_ex1 :
    tokenize "abc12=3 2.23*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "2.23";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed. 
Compute tokenize "abc12=3 2.23*(3+(a+c))" %string. *)


Compute tokenize "[ H1 : 2 ; Q2.Y ]"%string.
Compute tokenize "[ H2 : 1 ; Q1.X * Q2.Z + Q3.Y ]"%string. 
Compute tokenize "[H3 : 1.2 ; (3 + 5) / 12 Q3.X ]"%string. 
 

(*Grammer :
Prog := HSF id Sites Decls Hamiltonian Insts ENDHSF
Decls := id*
Insts := Inst*
Inst := [ id : expr ; TIH ]
r_expr := textbook stuff hopefully
TIH := TIH_term [ + TIH_term ]*
TIH_term := [r_expr] HPauli [ * HPauli ]*  
HPauli:= id . [X | Y | Z | I]
 *) 





