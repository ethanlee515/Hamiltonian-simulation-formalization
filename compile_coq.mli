
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val id : 'a1 -> 'a1

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

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint
 end

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val to_int : nat -> int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val max : positive -> positive -> positive

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val abs : z -> z

  val of_nat : nat -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

val append : char list -> char list -> char list

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qred : q -> q

type cReal = (positive -> q)

val inject_Q : q -> cReal

val cReal_plus : cReal -> cReal -> cReal

val cReal_opp : cReal -> cReal

val qCauchySeq_bound : (positive -> q) -> (positive -> positive) -> positive

val cReal_mult : cReal -> cReal -> cReal

val sig_forall_dec : (nat -> sumbool) -> nat sumor

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> nat -> nat -> q

val dRealQlim : dReal -> nat -> q

val dRealAbstr : cReal -> dReal

val dRealRepr : dReal -> cReal

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

module RbaseSymbolsImpl :
 RbaseSymbolsSig

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

val hQAdd : 'a1 ham_Quantity_Add -> 'a1 -> 'a1 -> 'a1

val hQ_TIH_Add : tIH ham_Quantity_Add

type ('q1, 'q2) ham_Quantity_Mult =
  'q1 -> 'q2 -> 'q2
  (* singleton inductive, whose constructor was Build_Ham_Quantity_Mult *)

val hQMult : ('a1, 'a2) ham_Quantity_Mult -> 'a1 -> 'a2 -> 'a2

val hQ_TIH_TIH_Mult : (tIH, tIH) ham_Quantity_Mult

module NilEmpty :
 sig
  val string_of_uint : uint -> char list
 end

module NilZero :
 sig
  val string_of_uint : uint -> char list

  val string_of_int : int -> char list
 end

val program_placeholder : h_Program

val parseProgram : char list -> h_Program

type supportedGates =
| Rx of nat * RbaseSymbolsImpl.coq_R
| Ry of nat * RbaseSymbolsImpl.coq_R
| Rz of nat * RbaseSymbolsImpl.coq_R

val trotterize : h_Program -> supportedGates list

val string_of_nat : nat -> char list

val write_circuit : supportedGates list -> char list

val count_sites : h_Program -> nat

val compile : char list -> char list
