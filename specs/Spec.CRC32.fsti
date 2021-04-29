module Spec.CRC32

module BV = FStar.BitVector
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt

let is_rev (a b: U8.t) =
  let av = UInt.to_vec (U8.v a) in
  let bv = UInt.to_vec (U8.v b) in
  Seq.index av 0 == Seq.index bv 7 /\ Seq.index av 1 == Seq.index bv 6 /\
  Seq.index av 2 == Seq.index bv 5 /\ Seq.index av 3 == Seq.index bv 4 /\
  Seq.index av 4 == Seq.index bv 3 /\ Seq.index av 5 == Seq.index bv 2 /\
  Seq.index av 6 == Seq.index bv 1 /\ Seq.index av 7 == Seq.index bv 0

(* Reverse bits in the U8.t. *)
val u8_rev: v: U8.t -> Tot (res: U8.t{is_rev v res})

unfold let gf2_plus (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (+@) #n = gf2_plus #n

unfold let gf2_sub (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (-@) #n = gf2_sub #n

