module Spec.CRC32

module BV = FStar.BitVector
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

unfold let gf2_plus (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (+@) #n = gf2_plus #n

unfold let gf2_sub (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (-@) #n = gf2_sub #n

unfold let is_rev (#n: nat{n > 0}) (a b: UInt.uint_t n) =
  let av = UInt.to_vec a in
  let bv = UInt.to_vec b in
  forall i. {:pattern (Seq.index av i)}
    Seq.index av i == Seq.index bv (n - i - 1)

let is_rev_refl (#n: nat{n > 0}) (a b: UInt.uint_t n): Lemma
  (requires is_rev a b)
  (ensures is_rev b a)
  [SMTPat (is_rev a b)] =
  let av = UInt.to_vec a in
  let bv = UInt.to_vec b in
  assert(forall i. Seq.index bv i == Seq.index av (n - i - 1))

val u8_rev: v: U8.t -> Tot (res: U8.t{is_rev (U8.v v) (U8.v res)})

val u32_rev: v: U32.t -> Tot (res: U32.t{is_rev (U32.v v) (U32.v res)})

let gf2_polynomial = Seq.init #bool 33 (fun i ->
  i = 0 || i = 6 || i = 9 || i = 10 || i = 16 || i = 20 || i = 21 || i = 22 || i = 24 ||
  i = 25 || i = 27 || i = 28 || i = 30 || i = 31 || i = 32)

let gf2_polynomial32 = Seq.tail gf2_polynomial

type crc32_polynomial = res: U32.t{
  let res' = U32.v res in
  forall j. UInt.nth res' j == Seq.index gf2_polynomial (j + 1)
}
