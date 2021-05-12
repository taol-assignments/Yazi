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
  forall i. {:pattern (UInt.nth a i)}
    UInt.nth a i == UInt.nth b (n - i - 1)

let is_rev_refl (#n: nat{n > 0}) (a b: UInt.uint_t n): Lemma
  (requires is_rev a b)
  (ensures is_rev b a)
  [SMTPat (is_rev a b)] =
  assert(forall i. UInt.nth b i == UInt.nth a (n - i - 1))

val u8_rev: v: U8.t -> Tot (res: U8.t{is_rev (U8.v v) (U8.v res)})

val u32_rev: v: U32.t -> Tot (res: U32.t{is_rev (U32.v v) (U32.v res)})

let gf2_polynomial = Seq.init #bool 33 (fun i ->
  i = 0 || i = 1 || i = 2 || i = 4 || i = 5 || i = 7 || i = 8 || i = 10 || i = 11 ||
  i = 12 || i = 16 || i = 22 || i = 23 || i = 26 || i = 32)

let gf2_polynomial32 = Seq.tail gf2_polynomial

type crc32_polynomial = res: U32.t{
  let res' = U32.v res in
  is_rev res' (UInt.from_vec gf2_polynomial32)
}

unfold let zero_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    i < m ==> Seq.index res i == false /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append (BV.zero_vec #m) a

unfold let zero_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    i < n ==> Seq.index res i == Seq.index a i /\ 
    (i >= n /\ i < n + m ==> Seq.index res i == false)
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append a (BV.zero_vec #m)

unfold let ones_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < m ==> Seq.index res i == true) /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append (BV.ones_vec #m) a

unfold let poly (n: nat{n >= 33}): Tot (p: BV.bv_t n{
  Seq.head p == true
}) =
  zero_vec_r #33 (n - 33) gf2_polynomial

unfold let poly_xor (#n: nat{n >= 32}) (a: BV.bv_t n): Tot (res: BV.bv_t n{
  res == Seq.tail ((ones_vec_l 1 a) -@ poly (n + 1))
}) =
  let a' = ones_vec_l 1 a in
  let p = poly (n + 1) in
  let r = a -@ (Seq.tail p) in
  let r' = a' -@ p in
  assert(Seq.equal r (Seq.tail r'));
  r

let rec poly_mod (#n: nat{n > 32}) (a: BV.bv_t n): Tot (BV.bv_t 32) =
  let p = poly n in
  let b = if Seq.head a then a -@ p else a in
  assert(Seq.head b == false);
  if n = 33 then (Seq.tail b) else poly_mod #(n - 1) (Seq.tail b)

unfold let poly_mod_correct (d res: U32.t) =
  let d' = zero_vec_r 1 (UInt.to_vec (U32.v (u32_rev d))) in
  forall i. {:pattern UInt.nth (U32.v res) i}
    UInt.nth (U32.v res) i == Seq.index (poly_mod d') (31 - i)
