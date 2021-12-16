
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type int =
| Pos of uint
| Neg of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil0 -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil0

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil0 -> D1 Nil0
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

module Nat =
 struct
  (** val to_little_uint : nat -> uint -> uint **)

  let rec to_little_uint n acc =
    match n with
    | O -> acc
    | S n0 -> to_little_uint n0 (Little.succ acc)

  (** val to_uint : nat -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil0))

  (** val to_int : nat -> int **)

  let to_int n =
    Pos (to_uint n)
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n0 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ ->
            let Pair (g, p) = ggcdn n0 a0 b in
            let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Coq_Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type q = { qnum : z; qden : positive }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = a; qden = _ } = q0 in
  (match a with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

type cReal = (positive -> q)

(** val inject_Q : q -> cReal **)

let inject_Q q0 _ =
  q0

(** val cReal_plus : cReal -> cReal -> cReal **)

let cReal_plus x y n =
  qred (qplus (x (Coq_Pos.mul (XO XH) n)) (y (Coq_Pos.mul (XO XH) n)))

(** val cReal_opp : cReal -> cReal **)

let cReal_opp x n =
  qopp (x n)

(** val qCauchySeq_bound :
    (positive -> q) -> (positive -> positive) -> positive **)

let qCauchySeq_bound qn cvmod =
  match (qn (cvmod XH)).qnum with
  | Z0 -> XH
  | Zpos p -> Coq_Pos.add p XH
  | Zneg p -> Coq_Pos.add p XH

(** val cReal_mult : cReal -> cReal -> cReal **)

let cReal_mult x y n =
  qmult
    (x
      (Coq_Pos.mul
        (Coq_Pos.mul (XO XH)
          (Coq_Pos.max (qCauchySeq_bound x id) (qCauchySeq_bound y id))) n))
    (y
      (Coq_Pos.mul
        (Coq_Pos.mul (XO XH)
          (Coq_Pos.max (qCauchySeq_bound x id) (qCauchySeq_bound y id))) n))

(** val sig_forall_dec : (nat -> sumbool) -> nat sumor **)

let sig_forall_dec =
  failwith "AXIOM TO BE REALIZED"

(** val lowerCutBelow : (q -> bool) -> q **)

let lowerCutBelow f =
  let s =
    sig_forall_dec (fun n ->
      let b = f (qopp { qnum = (Z.of_nat n); qden = XH }) in
      (match b with
       | True -> Right
       | False -> Left))
  in
  (match s with
   | Inleft s0 -> qopp { qnum = (Z.of_nat s0); qden = XH }
   | Inright -> assert false (* absurd case *))

(** val lowerCutAbove : (q -> bool) -> q **)

let lowerCutAbove f =
  let s =
    sig_forall_dec (fun n ->
      let b = f { qnum = (Z.of_nat n); qden = XH } in
      (match b with
       | True -> Left
       | False -> Right))
  in
  (match s with
   | Inleft s0 -> { qnum = (Z.of_nat s0); qden = XH }
   | Inright -> assert false (* absurd case *))

type dReal = (q -> bool)

(** val dRealQlim_rec : (q -> bool) -> nat -> nat -> q **)

let rec dRealQlim_rec f n = function
| O -> assert false (* absurd case *)
| S p0 ->
  let b =
    f
      (qplus (lowerCutBelow f) { qnum = (Z.of_nat p0); qden =
        (Coq_Pos.of_nat (S n)) })
  in
  (match b with
   | True ->
     qplus (lowerCutBelow f) { qnum = (Z.of_nat p0); qden =
       (Coq_Pos.of_nat (S n)) }
   | False -> dRealQlim_rec f n p0)

(** val dRealQlim : dReal -> nat -> q **)

let dRealQlim x n =
  let s = lowerCutAbove x in
  let s0 = qarchimedean (qminus s (lowerCutBelow x)) in
  dRealQlim_rec x n (mul (S n) (Coq_Pos.to_nat s0))

(** val dRealAbstr : cReal -> dReal **)

let dRealAbstr x =
  let h = fun q0 n ->
    let s =
      qlt_le_dec
        (qplus q0 { qnum = (Zpos XH); qden = (Coq_Pos.of_nat (S n)) })
        (x (Coq_Pos.of_nat (S n)))
    in
    (match s with
     | Left -> Right
     | Right -> Left)
  in
  (fun q0 ->
  match sig_forall_dec (h q0) with
  | Inleft _ -> True
  | Inright -> False)

(** val dRealRepr : dReal -> cReal **)

let dRealRepr x n =
  dRealQlim x (Coq_Pos.to_nat n)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  type coq_R = dReal

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 =
    coq_Rabst (inject_Q { qnum = Z0; qden = XH })

  (** val coq_R1 : coq_R **)

  let coq_R1 =
    coq_Rabst (inject_Q { qnum = (Zpos XH); qden = XH })

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus x y =
    coq_Rabst (cReal_plus (coq_Rrepr x) (coq_Rrepr y))

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult x y =
    coq_Rabst (cReal_mult (coq_Rrepr x) (coq_Rrepr y))

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp x =
    coq_Rabst (cReal_opp (coq_Rrepr x))

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

type hType =
| HQubit
| HFock

type hOp =
| Id
| X
| Y
| Z
| A
| C

type hDecl = (hType, char list) prod

type hDecls = hDecl list

type hScalar =
| HScAdd of hScalar * hScalar
| HScMult of hScalar * hScalar
| HScSub of hScalar * hScalar
| HScDiv of hScalar * hScalar
| HScExp of hScalar
| HScCos of hScalar
| HScSin of hScalar
| HScReal of RbaseSymbolsImpl.coq_R

type tIH =
| HAdd of tIH * tIH
| HMult of tIH * tIH
| HMultS of hScalar * tIH
| HIdOp of char list * hOp

type tIH_Seq = ((char list, RbaseSymbolsImpl.coq_R) prod, tIH) prod list

type h_Program = (hDecls, tIH_Seq) prod

type 'q ham_Quantity_Add =
  'q -> 'q -> 'q
  (* singleton inductive, whose constructor was Build_Ham_Quantity_Add *)

(** val hQAdd : 'a1 ham_Quantity_Add -> 'a1 -> 'a1 -> 'a1 **)

let hQAdd ham_Quantity_Add0 =
  ham_Quantity_Add0

(** val hQ_TIH_Add : tIH ham_Quantity_Add **)

let hQ_TIH_Add x x0 =
  HAdd (x, x0)

type ('q1, 'q2) ham_Quantity_Mult =
  'q1 -> 'q2 -> 'q2
  (* singleton inductive, whose constructor was Build_Ham_Quantity_Mult *)

(** val hQMult : ('a1, 'a2) ham_Quantity_Mult -> 'a1 -> 'a2 -> 'a2 **)

let hQMult ham_Quantity_Mult0 =
  ham_Quantity_Mult0

(** val hQ_TIH_TIH_Mult : (tIH, tIH) ham_Quantity_Mult **)

let hQ_TIH_TIH_Mult x x0 =
  HMult (x, x0)

module NilEmpty =
 struct
  (** val string_of_uint : uint -> char list **)

  let rec string_of_uint = function
  | Nil0 -> []
  | D0 d0 -> '0'::(string_of_uint d0)
  | D1 d0 -> '1'::(string_of_uint d0)
  | D2 d0 -> '2'::(string_of_uint d0)
  | D3 d0 -> '3'::(string_of_uint d0)
  | D4 d0 -> '4'::(string_of_uint d0)
  | D5 d0 -> '5'::(string_of_uint d0)
  | D6 d0 -> '6'::(string_of_uint d0)
  | D7 d0 -> '7'::(string_of_uint d0)
  | D8 d0 -> '8'::(string_of_uint d0)
  | D9 d0 -> '9'::(string_of_uint d0)
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> char list **)

  let string_of_uint d = match d with
  | Nil0 -> '0'::[]
  | _ -> NilEmpty.string_of_uint d

  (** val string_of_int : int -> char list **)

  let string_of_int = function
  | Pos d0 -> string_of_uint d0
  | Neg d0 -> '-'::(string_of_uint d0)
 end

(** val program_placeholder : h_Program **)

let program_placeholder =
  Pair
    ((app (Cons ((Pair (HFock, ('F'::('1'::[])))), Nil))
       (app (Cons ((Pair (HQubit, ('Q'::('1'::[])))), Nil))
         (app (Cons ((Pair (HQubit, ('Q'::('2'::[])))), Nil)) (Cons ((Pair
           (HQubit, ('Q'::('3'::[])))), Nil))))),
    (app (Cons ((Pair ((Pair (('H'::('1'::[])), RbaseSymbolsImpl.coq_R1)),
      (hQMult hQ_TIH_TIH_Mult (HIdOp (('Q'::('1'::[])), X))
        (hQAdd hQ_TIH_Add (HIdOp (('Q'::('2'::[])), Z)) (HIdOp
          (('Q'::('3'::[])), Y)))))), Nil))
      (app (Cons ((Pair ((Pair (('H'::('2'::[])), RbaseSymbolsImpl.coq_R1)),
        (HIdOp (('Q'::('2'::[])), Y)))), Nil)) (Cons ((Pair ((Pair
        (('H'::('3'::[])), RbaseSymbolsImpl.coq_R1)), (HIdOp
        (('F'::('1'::[])), C)))), Nil)))))

(** val parseProgram : char list -> h_Program **)

let parseProgram _ =
  program_placeholder

type supportedGates =
| Rx of nat * RbaseSymbolsImpl.coq_R
| Ry of nat * RbaseSymbolsImpl.coq_R
| Rz of nat * RbaseSymbolsImpl.coq_R

(** val trotterize : h_Program -> supportedGates list **)

let trotterize _ =
  Cons ((Rx (O, RbaseSymbolsImpl.coq_R1)), (Cons ((Ry (O,
    RbaseSymbolsImpl.coq_R1)), (Cons ((Rz (O, RbaseSymbolsImpl.coq_R1)),
    Nil)))))

(** val string_of_nat : nat -> char list **)

let string_of_nat n =
  NilZero.string_of_int (Nat.to_int n)

(** val write_circuit : supportedGates list -> char list **)

let rec write_circuit = function
| Nil -> []
| Cons (head, tail) ->
  append
    (match head with
     | Rx (loc, _) ->
       append
         ('U'::('('::('1'::(','::(' '::('0'::(','::(' '::('0'::(')'::(' '::('q'::('['::[])))))))))))))
         (append (string_of_nat loc) (']'::('\\'::('n'::[]))))
     | Ry (loc, _) ->
       append
         ('U'::('('::('1'::(','::(' '::('0'::(','::(' '::('0'::(')'::(' '::('q'::('['::[])))))))))))))
         (append (string_of_nat loc) (']'::('\\'::('n'::[]))))
     | Rz (loc, _) ->
       append
         ('U'::('('::('1'::(','::(' '::('0'::(','::(' '::('0'::(')'::(' '::('q'::('['::[])))))))))))))
         (append (string_of_nat loc) (']'::('\\'::('n'::[])))))
    (write_circuit tail)

(** val count_sites : h_Program -> nat **)

let count_sites _ =
  S (S (S O))

(** val compile : char list -> char list **)

let compile program_text =
  let program = parseProgram program_text in
  let circuit = trotterize program in
  append
    ('O'::('P'::('E'::('N'::('Q'::('A'::('S'::('M'::(' '::('2'::('.'::('0'::(';'::('\\'::('n'::[])))))))))))))))
    (append ('q'::('r'::('e'::('g'::(' '::('q'::('['::[])))))))
      (append (string_of_nat (count_sites program))
        (append (']'::('\\'::('n'::[])))
          (append (write_circuit circuit)
            ('m'::('e'::('a'::('s'::('u'::('r'::('e'::('_'::('a'::('l'::('l'::('\\'::('n'::[])))))))))))))))))
