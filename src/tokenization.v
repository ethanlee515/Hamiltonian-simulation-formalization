Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Bool BinPos BinNat PeanoNat Nnat Coq.Strings.Byte.
Require Import Reals QWIRE.Matrix.
Require Import DecimalString.
Set Printing Projections.
(*This file is an incomplete parser. *)

(*Checks whitespace*) 
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32) (* space *)
           (n =? 9)) (* tab *)
      (orb (n =? 10) (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

(*Checks if character is lowercase letter*)
Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

(*checks if character is uppercase letter*)
Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

(*checks if character is an integer*) 
Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

(*checks equivalence arbitrary ascii character given ascii number *) 
Definition isSingle_Char (c : ascii) (num :nat)  : bool :=
  let  n:= nat_of_ascii c in (n =? num).

(*checks if character is a possible Pauli matrix*) 
Definition isPauli (c : ascii) : bool:= 
  let n:= nat_of_ascii c in 
    andb (88 <=? n ) (n <=? 90).

(*turns a string into a list of ascii characters*) 
Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

(*turns a list of ascii characters into a string *) 
Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

(* checks if a string is a valid site, need to change to accept any alpha numeric combination*) 
Definition isSite (x : string) : bool :=
 if prefix "Q" x && forallb isDigit (list_of_string (substring 1 (length (list_of_string x)) x)) then  true
  else false.
Compute index 0 "." "5.5". 

(*modifying string index function*) 
Fixpoint index (n : nat) (s1 s2 : string) {struct s2} : nat :=
  match s2, n with
  | EmptyString, 0 =>
      match s1 with
      | EmptyString => 1000
      | String a s1' => 0
      end
  | EmptyString, S n' => 1000
  | String b s2', 0 =>
      if prefix s1 s2 then 0
      else
        match index 0 s1 s2' with
        |  n =>  (S n)
        end
   | String b s2', S n' =>
      match index n' s1 s2' with
      |  n => (S n) 
      end
  end.
Compute index 0 "." "5.5". 
Compute negb (beq_nat 5 6). 

(*checks if number passed in is one with a decimal*) 
Definition isDecimalDigit (x: string) : bool := 
  if negb (beq_nat (index 0 "." x) 1000) && forallb isDigit (list_of_string (substring 0 (index 0 "." x) x)) && 
forallb isDigit (list_of_string(substring ((index 0 "." x) + 1) (length (list_of_string x)) x) )then true 
else false. 

Compute isDecimalDigit "5". 

(*checks if variable is a hamiltonian, similar to site, will change  to accept any alphanumeric combination*) 
Definition isHam (x : string) : bool :=
 if prefix "H" x && forallb isDigit (list_of_string (substring 1 (length (list_of_string x)) x)) then  true
  else false.

(*character types, classifying characters by character types*) 
Inductive chartype := white | alpha | digit | period |  other.
Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else if (isSingle_Char c 46) then 
    period
  else
    other.

(*possible token keywords*) 
Inductive token_keyword :=  empty | qubit_id | number| dot| left_brac | right_brac | colon | plus | subtr | divide | semicolon |kw_Site | kw_Ham| prog_id| kw_HPauli. 

(*defining what  a token can contain*) 
Inductive token_content := 
 | kw_tok (kw : token_keyword)
 | id_tok (id : string)
 | tok_num (num : option R)(raw_s : string).

(*defining token*) 
Record token:=
make_token 
{
 token_val : token_content; 
 line_number : nat;
}.
Check (make_token (id_tok "."%string) 0). 

Local Open Scope lazy_bool_scope.
Fixpoint eqb_string s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 &&& eqb_string s1' s2'
 | _,_ => false
 end.
Compute eqb_string "hello"%string "helpo"%string .

(*determing what token keyword a given string is*) 
Definition classifyKeyword (cs : string) : token_keyword :=
match list_of_string cs with
|[] => empty
|c::cs' =>
  if forallb isDigit (list_of_string cs) then
    number
  else if (isSingle_Char c 46) then 
    dot
  else if isDecimalDigit cs then
    number
  else if (isSingle_Char c 91) then 
    left_brac
  else if (isSingle_Char c 93) then 
    right_brac
  else if (isSingle_Char c 58) then 
    colon 
  else if (isSingle_Char c 43) then
    plus 
  else if (isSingle_Char c 45) then 
    subtr 
  else if (isSingle_Char c 47) then 
    divide
  else if (isSingle_Char c 59) then 
    semicolon
  else if eqb_string cs "Hamiltonian" then
     kw_Ham
  else if eqb_string cs "Site" then
    kw_Site
  else if eqb_string cs "HSF" then
    prog_id
  else if eqb_string cs "qubit" then
    qubit_id
  else
    empty
end.


(*conversion from a string to a nat*) 
Definition string_to_nat (s : string) : option nat :=
  match NilEmpty.uint_of_string s with
  | None => None
  | Some u => Some (Nat.of_uint u)
  end.

(* turns a string to an option nat, modified from ImpParser*) 
Definition parseNumber (xs : string)
                     : option nat :=
match list_of_string xs with
| [] => None
| x::xs' =>
    if forallb isDigit (list_of_string xs) then
      Some (fold_left
               (fun n d =>
                 ( add (mult 10 n%nat)%nat (minus ((nat_of_ascii d)%nat)
                            ((nat_of_ascii "0"%char)%nat))))
               (list_of_string xs) 0%nat)
    else
      None 
end.
 
Compute parseNumber "30"%string.

(*Compute INR ((exists 30%), (parseNumber "30"%string)). 
function takes in a string an s a token out of it
Definition handle_token (tk : string) (n: nat) : token := 
  match classifyKeyword tk with 
  | number => (make_token (kw_tok (classifyKeyword tk)) (tok_num INR(parseNumber tk%string) (tk%string)) n)
  | _ => (make_token (kw_tok (classifyKeyword tk)) (id_tok tk%string) n)
  end. *)

(*constructs list of substrings*) 
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

(*Deal with decimals later, attempting to convert a string to a real number. Doesn't handle decimals, but could save index of decimal and compute real_number/10^{decimal_index}*) 
Print NilEmpty.int_of_string.
Definition string_to_R (s : string) : option R := 
 match NilEmpty.int_of_string s with 
  | None => None 
  | Some x => Some (IZR (Z.of_int x))
  end. 


(*constructs a single token given classified token_content*) 
Definition handle_token (tk:token_content) (n: nat) : token := 
  match tk with 
  | kw_tok kw =>  make_token (kw_tok kw) n
  | id_tok id => make_token (id_tok id%string) n
  | tok_num num str => make_token (tok_num num str) n
  end. 
 

Compute (handle_token (kw_tok kw_Ham) 0).
(*makes list of tokens from list of substrings, takes same approach as ImpParser*) 
Fixpoint make_token_list (kl: token_keyword) (tk: list string) (acc : list token) : (list token) := 
let tkl := match acc with [] => [] | _ => rev acc end in 
 match tk with 
 | [] => tkl
 | x::xs' => 
    match kl, classifyKeyword x, x with
     | empty, left_brac, x =>
        make_token_list left_brac xs' ((handle_token (id_tok x%string) 0)::acc)
     | _ ,kw_Site, x => 
        make_token_list kw_Site xs' ((handle_token (kw_tok kw_Site) 0)::acc)
     | _ ,qubit_id, x => 
        make_token_list kw_Site xs' ((handle_token (kw_tok qubit_id) 0)::acc)
     |  _, prog_id, x => 
        make_token_list kw_Site xs' ((handle_token (kw_tok prog_id) 0)::acc)
     | _,kw_Ham, x => 
        make_token_list kw_Ham xs' ((handle_token (kw_tok kw_Ham) 0)::acc)
     | empty, right_brac, x =>
        make_token_list right_brac xs' ((handle_token (id_tok x%string) 0)::acc)
     | _,number,x => 
        make_token_list number xs' ((handle_token (tok_num (string_to_R x%string) x%string) 0)::acc)
     | _,dot,x =>
         make_token_list dot xs' ((handle_token (id_tok x%string) 0)::acc)
     |empty, colon, x => 
       make_token_list colon xs' ((handle_token (id_tok x%string) 0)::acc)
     |empty, plus, x => 
       make_token_list plus xs' ((handle_token (id_tok x%string) 0)::acc)
     |empty, subtr, x => 
       make_token_list subtr xs' ((handle_token (id_tok x%string) 0)::acc)
     |empty, divide, x => 
       make_token_list divide xs' ((handle_token (id_tok x%string) 0)::acc)
     |empty, semicolon, x => 
       make_token_list semicolon xs' ((handle_token (id_tok x%string) 0)::acc)
     | _, tp, x => 
        tkl ++ make_token_list tp xs' [(handle_token (id_tok x%string) 0)]
     end
  end.
Compute( make_token_list (left_brac) (tokenize "[5.5]"%string) []).
Compute tokenize "[ H2 : 1 ; Q1.X * Q2.Z + Q3.Y ]"%string. 
Compute tokenize "[H3 : 1.2 ; (3 + 5) / 12 Q3.X ]"%string. 
Compute (make_token_list (prog_id) (tokenize "HSF Site
    qubit Q1
    qubit Q2
    qubit Q3 ;
Hamiltonian
    [ H1 : 3.5 , Q1.X * Q2.Z + Q3.Y ]
    [ H2 : 4.245 , Q2.Y + Q1.Z ]
    [ H3 : 4 , (2.4*3/5)Q1.X ]"%string) []). (*correctly tokenizes a program*) 
(**************************************************************** Parsing ****************************************************************)


(*** This is an attempt to construct parser using same approach as ImpParser. We no longer believe this is the best way to go about this *) 
Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).
Arguments SomeE {X}.
Arguments NoneE {X}.

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

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Compute (make_token_list (prog_id) (tokenize "HSF Site
    qubit Q1
    qubit Q2
    qubit Q3 ;
Hamiltonian
    [ H1 : 3 , Q1.X * Q2.Z + Q3.Y ]
    [ H2 : 4.245 , Q2.Y + Q1.Z ]
    [ H3 : 4 + (2.4*3/5), Q1.X ]"%string) []).



Definition printToken (t : token) : string := 
  match t.(token_val) with
  | id_tok x => x
  | kw_tok x => "token keyword"%string 
  | tok_num x y => y 
  end.


(*checks if two keywords are equivalent*) 
Definition checkKeywordEquiv (x y : token_keyword) : bool :=
  match x, y with 
  | empty, empty  => true
  | qubit_id, qubit_id => true
  | number, number => true
  | dot, dot => true
  | left_brac, left_brac => true 
  | right_brac, right_brac => true 
  | colon, color => true 
  | plus, plus => true 
  | subtr, subtr => true
  | divide, divide => true 
  | semicolon, semicolon => true
  | kw_Site, kw_Site => true 
  | kw_Ham, kw_Ham => true
  | prog_id, prog_id => true
  | kw_HPauli, kw_HPauli => true
  | _, _ => false
  end.

Compute checkKeywordEquiv prog_id kw_Site. 
Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
            match x.(token_val) with 
                | id_tok z => 
                    match t.(token_val) with 
                    | id_tok m => if string_dec z m then p xs' else NoneE ("expected '" ++ printToken t ++ "'.")
                    | _ =>  NoneE("expected '" ++ printToken t ++ " '.")
                    end
                (*| kw_tok z => 
                    match t.(token_val) with 
                    | kw_tok m => if checkKeywordEquiv z m then p xs' else NoneE ("expected '" ++ printToken t ++ "'.")
                    | _ =>  NoneE("expected '" ++ printToken t ++ " '.")
                    end 
               | tok_num z y => 
                    match t.(token_val) with 
                    | tok_num n m => if string_dec y m then p xs' else NoneE ("expected '" ++ printToken t ++ "'.")
                    | _ =>  NoneE("expected '" ++ printToken t ++ " '.")
                    end *)
               | _ =>  NoneE ("expected '" ++ printToken t ++ "'.")

             end
            | [] =>
              NoneE ("expected '" ++ printToken t ++ "'.")
            end.

Definition expect1 (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

Compute expect1 {| token_val := id_tok "Q3"; line_number := 0 |}. 

Record HSF_program  := makeHSFProg {
  prog_name: token_keyword;
  prog_decls : list token_content;
  prog_insts : list string;
}.

(* change to allow any identifier, not just Q[num]* or H[num]* *)
Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
  match x.(token_val) with 
   | id_tok x' =>  if isSite x' || isHam x' then
      SomeE ( (x'), xs')
    else
      NoneE ("Illegal identifier:'" ++ printToken x ++ "'")
   | _ =>  NoneE ("Illegal identifier:'" ++ printToken x ++ "'")
   end
end.

Compute parseIdentifier  [{| token_val := kw_tok prog_id; line_number := 0 |};{| token_val := id_tok "Q2"; line_number := 0 |}]. 

Definition parseNum (xs : list token)
                     : optionE (R * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    match x.(token_val) with 
    | tok_num num str_num => 
      match num with 
      | None =>  NoneE "Expected number" 
      | Some n =>  SomeE ( n, xs')
      end 
    | _ =>  NoneE "Expected number"
    end 
end.
Compute string_to_R "5"%string. 

Compute parseNum [{| token_val := tok_num (Some ((R1 + R1) * (R1 + R1))%R) "4"; line_number := 0 |};{| token_val := id_tok "Q2"; line_number := 0 |}].
(***************************************** optionE version end ****************************************************) 



Inductive compiler_error := makeCompilerError (msg: string). 

(*Definition match_kw (tc : token_content) : 
Definition  match_prog (tokens : list tokens) : HSF_prog := 
  let status: option compiler_error := None in
  let index := 0 in 
  let (tokens1, index1, status1) := 
    match_kw  prog_id tokens index status in
    let (prog_name, tokens2, index2, status2) 
      := match_id tokens1 index1 status1 in
     let (tokens3, index3, status3)
      := match_kw KW::Sites tokens2 index2 status2 in
      let (tokens4, index4, status4)
      := match_kw KW::Hamiltonian tokens3 index3 status3 in
      let (tokens3, index3, status3)
      := match_kw KW::ENDHSF tokens4 index4 status4.
*)

(*checks if a token matches the given keyword. Can be thought of as a "next_token" function commonly used in a parser*) 
Definition expect (tokens : list token) (kw : token_keyword) : option (list token) := 
  match tokens with 
  | head :: tail =>
    match head.(token_val) with 
    | kw_tok kw => Some tail (*match is successful, we can remove the head *) 
    | _ => None (*not correct key word *) 
    end
  | _ => None (* no tokens to match*) 
  end. 



(* Prog := HSF id Sites Decls Hamiltonian Insts ENDHSF *) 

  
 