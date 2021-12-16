Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Bool BinPos BinNat PeanoNat Nnat Coq.Strings.Byte.
Require Import Reals QWIRE.Matrix.
Set Printing Projections.


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

Definition isSingle_Char (c : ascii) (num :nat)  : bool :=
  let  n:= nat_of_ascii c in (n =? num).

Definition isPauli (c : ascii) : bool:= 
  let n:= nat_of_ascii c in 
    andb (88 <=? n ) (n <=? 90).


Inductive chartype := white | alpha | digit | period |  other.

Inductive token_keyword := dot| left_brac | right_brac | colon | plus | subtr | divide | semicolon |kw_Site | kw_Ham| kw_HPauli. 


(*Inductive token_content := 
 | kw_tok (kw : token_keyword)
 | id_tok (id : string)
 | tok_num (num : R)(raw_s : string).


Record tooken:=
make_tooken 
{
 token_type : token_content;
 token_val : token_content; 
 line_number : nat;
}.
Check (make_tooken (kw_tok dot) (id_tok "."%string) 0). 
Set Printing All. 
Print tooken. 

Definition classifyKeyword (x : list ascii) : token_keyword:= 
  match x with 
  | [] => None
  | x::xs' => 
    match (if isSingle_Char x 81)
  

(*Takes in a part of the input program string,makes it a token *)

Fixpoint handle_token(tk : list (list ascii)) (n :nat) :  list tooken :=
 let tkl := match tk with [] => [] | _::_ => [rev tk] end in 
 match tkl with 
  | [] => tkl 
  | (x::xs') => tkl ++ [make_tooken (kw_tok (findKeyword x)) id_tok x%string tok_num n] :: (handle_token xs' 0)
 end.
Check handle_token. *)



Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else if (isSingle_Char c 46) then 
    period
  (*else if (isSingle_Char c 91) then 
    left_brac
  else if (isSingle_Char c 93) then 
    right_brac
  else if (isSingle_Char c 58) then 
    colon 
  else if (isSingle_Char c 43) then
    plus 
  else if (isSingle_Char c 45) then 
    minus 
  else if (isSingle_Char c 47) then 
    divide
  else if (isSingle_Char c 59) then 
    semicolon*)
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
                       : list  (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" =>
      tk ++ ["("]::(tokenize_helper other [] xs') (*want to handle_token the... tk?*) 
    | _, _, ")" =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _ =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x =>
      tokenize_helper digit (x::acc) xs'
    | digit,period,x => 
      tokenize_helper digit (x::acc) xs'
    | period, digit, x => 
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


Compute tokenize "[ H1 : 2 ; Q2.Y ]"%string.
Compute tokenize "[ H2 : 1 ; Q1.X * Q2.Z + Q3.Y ]"%string. 
Compute tokenize "[H3 : 1.2 ; (3 + 5) / 12 Q3.X ]"%string. 
Compute tokenize "HSF Site
    fock F1
    qubit Q1
    qubit Q2
    qubit Q3 ;
Hamiltonian
    ( H1 : 3.5 , Q1.X * Q2.Z + Q3.Y )
    ( H2 : 4.245 , Q2.Y + Q1.Z )
    ( H3 : 4 , (2.4*3/5)Q1.X )"%string.

(*Grammer :
Prog := HSF id Sites Decls Hamiltonian Insts ENDHSF
Decls := id*
Insts := Inst*
Inst := [ id : expr ; TIH ]
r_expr := textbook stuff hopefully
TIH := TIH_term [ + TIH_term ]*
TIH_term := [r_expr] HPauli [ * HPauli ]*  
HPauli:= id . [X | Y | Z | I]
- Get HPauli  
- Get *) 


Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).


Arguments SomeE {X}.
Arguments NoneE {X}.
(*--------------------------------------------------------------------------------------------------*)
(*Parsing combinator stuff *) 
(*For syntax, makes nesting easier*) 
Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).

Open Scope string_scope.
Definition parser (T : Type) :=
  list token -> optionE (T * list token).


Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(*Step indexed parser, expects 0 or more parser steps*) 
Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(*---------------------------------------------------------------------------------------------*)


Definition parsePauli (xs: list token)
                         : optionE (string * list token) := 
  match xs with 
  | [] => NoneE "Expected Pauli"
  | x::xs' => 
      if forallb isPauli (list_of_string x) then 
        SomeE( x, xs')
      else
        NoneE ("Illegal Pauli: '"  ++ x ++ "'")
  
end.

Compute parsePauli ["Z"%string].

Compute get 0 "hello"%string. 

Compute prefix "Q" "Qello". 
 
Compute  beq_nat (length (list_of_string "hello"%string)) 5.

Compute substring 1 (length (list_of_string "hello"%string)) "hello". 


Definition parseSite (xs : list token) : optionE (string * list token) :=    
  match xs with 
  | [] => NoneE "Expected Site Q[Number]" 
  | x::xs' => if prefix "Q" x && forallb isDigit (list_of_string (substring 1 (length (list_of_string x%string)) x)) then SomeE(x,xs')
              else  NoneE ("Illegal Site: '"  ++ x ++ "'")
  end.

Compute parseSite ["Q2"%string].  
     
Fixpoint add (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.

Compute minus (add (mult 5 10)%nat (nat_of_ascii "5"))%nat 20. 
Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                 ( add (mult 10 n%nat)%nat (minus ((nat_of_ascii d)%nat)
                            ((nat_of_ascii "0"%char)%nat))))
               (list_of_string x) 0%nat, xs')
    else
      NoneE "Expected number"
end.
 
Compute parseNumber ["582"; "stuff"; "more_stuff"].

Local Open Scope list_scope.


