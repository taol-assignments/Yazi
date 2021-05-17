module Spec.CRC32.Bits

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module BV = FStar.BitVector
module HS = FStar.HyperStack
module Math = FStar.Math.Lib
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Mul

unfold let zero_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < m ==> Seq.index res i == false) /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append (BV.zero_vec #m) a

unfold let zero_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < n ==> Seq.index res i == Seq.index a i) /\ 
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

unfold let ones_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < n ==> Seq.index res i == Seq.index a i) /\
    (i >= n /\ i < n + m ==> Seq.index res i == true)
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append a (BV.ones_vec #m)

let zero_vec_l_app (#n: nat{n > 0}) (a: BV.bv_t n) (m l: nat): Lemma
  (ensures zero_vec_l l (zero_vec_l m a) == zero_vec_l (m + l) a) =
  assert(Seq.equal (zero_vec_l l (zero_vec_l m a)) (zero_vec_l (m + l) a))

unfold let gf2_plus (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (+@) #n = gf2_plus #n

unfold let gf2_sub (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (-@) #n = gf2_sub #n

unfold let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  forall i.
    Seq.length res == Seq.length s - 1 /\
    (Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)

let gf2_polynomial = Seq.init #bool 33 (fun i ->
  i = 0 || i = 1 || i = 2 || i = 4 || i = 5 || i = 7 || i = 8 || i = 10 || i = 11 ||
  i = 12 || i = 16 || i = 22 || i = 23 || i = 26 || i = 32)

let gf2_polynomial32 = unsnoc gf2_polynomial

type crc32_polynomial = res: U32.t{
  let res' = U32.v res in
  forall i. UInt.nth res' i == Seq.index gf2_polynomial32 i
}

unfold let poly (n: nat{n >= 33}): Tot (p: BV.bv_t n{
  Seq.index p (n - 1) == true
}) =
  assert(Seq.index gf2_polynomial 32 == true);
  zero_vec_l #33 (n - 33) gf2_polynomial

unfold let poly_xor (#n: nat{n >= 32}) (a: BV.bv_t n): Tot (res: BV.bv_t n{
  res == unsnoc ((ones_vec_r 1 a) -@ poly (n + 1))
}) =
  let a' = ones_vec_r 1 a in
  let p = poly (n + 1) in
  let r = a -@ (unsnoc p) in
  let r' = a' -@ p in
  assert(Seq.equal r (unsnoc r'));
  r

let rec poly_mod (#n: nat{n > 32}) (a: BV.bv_t n): Tot (BV.bv_t 32) =
  let p = poly n in
  let b = if Seq.index a (n - 1) then a -@ p else a in
  assert(Seq.index b (n - 1) == false);
  if n = 33 then unsnoc b else poly_mod #(n - 1) (unsnoc b)

val poly_mod_zero: #n: nat{n > 32} -> a: BV.bv_t n {a == BV.zero_vec #n} -> Lemma
  (ensures poly_mod a == BV.zero_vec #32)

val poly_mod_add: #n: nat{n > 32} -> a: BV.bv_t n -> b: BV.bv_t n -> Lemma
  (ensures (poly_mod a) +@ (poly_mod b) == poly_mod (a +@ b))

val poly_mod_zero_prefix: #n: nat{n > 32} -> a: BV.bv_t n -> m: nat{m > 0} -> Lemma
  (ensures poly_mod (zero_vec_l m (poly_mod a)) == poly_mod (zero_vec_l m a))

val poly_mod_zero_suffix: a: BV.bv_t 32 -> m: nat{m > 0} -> Lemma
  (ensures poly_mod (zero_vec_r m a) == a)

unfold let poly_mod_correct (nzeros: nat{nzeros > 0}) (d res: U32.t) =
  let d' = zero_vec_l nzeros (UInt.to_vec (U32.v d)) in
  forall i. {:pattern UInt.nth (U32.v res) i}
    UInt.nth (U32.v res) i == Seq.index (poly_mod d') i

unfold let poly_mod_u32 (nzeros: nat{nzeros > 0}) (d: U32.t) =
  poly_mod (zero_vec_l nzeros (UInt.to_vec (U32.v d)))

val large_table_val_aux:
    i: U32.t{U32.v i < 256}
  -> nzeros: nat{nzeros > 0}
  -> p: U32.t
  -> p': U32.t
  -> p'': U32.t
  -> Lemma
  (requires
    poly_mod_u32 nzeros i == UInt.to_vec (U32.v p) /\
    poly_mod_u32 8 (U32.logand p 0xFFul) == UInt.to_vec (U32.v p') /\
    p'' == U32.shift_right p 8ul)
  (ensures poly_mod_correct (nzeros + 8) i (U32.logxor p' p''))

let poly_mod_correct_eq (nzeros: nat{nzeros > 0}) (d res: U32.t): Lemma
  (requires poly_mod_correct nzeros d res)
  (ensures poly_mod_u32 nzeros d == UInt.to_vec (U32.v res)) =
  let open U32 in
  assert(forall i. UInt.nth (v res) i == Seq.index (UInt.to_vec (v res)) i);
  assert(Seq.equal (poly_mod (zero_vec_l nzeros (UInt.to_vec (U32.v d)))) (UInt.to_vec (v res)))

type table_buf = buf: B.buffer U32.t{B.length buf == 256}

let sub_table_correct
  (j: nat{j <= 256})
  (nzeros: nat{nzeros > 0})
  (h: HS.mem)
  (buf: table_buf) =
  (B.live h buf) /\
  (forall i. i < j ==>
  poly_mod_correct nzeros (U32.uint_to_t i) (Seq.index (B.as_seq h buf) i))

let table_correct
  (nzeros: nat{nzeros > 0})
  (h: HS.mem)
  (buf: B.buffer U32.t{B.length buf == 256}) = sub_table_correct (B.length buf) nzeros h buf

private let rec seq_append_index_l (#t: Type) (a b: Seq.seq t): Lemma
  (ensures forall i. i < Seq.length a ==> Seq.index a i == Seq.index (Seq.append a b) i)
  (decreases Seq.length a) =
  match Seq.length a with
  | 0 -> ()
  | _ -> seq_append_index_l (Seq.tail a) b

private let bit_padding (#len: nat) (buf: Seq.seq U8.t{Seq.length buf == len}):
  Tot (res: Seq.seq U8.t{
    (Seq.length res == len + 4) /\
    (forall i.
      (i < 4 ==> Seq.index res i == 0uy) /\
      (i >= 4 ==> Seq.index res i = Seq.index buf (i - 4)))
  }) =
  let pad = Seq.create 4 0uy in
  let r = Seq.append pad buf in
  seq_append_index_l pad buf;
  r

type crc32_buf_len = n: nat{n == 0 \/ n > 32}

let crc32_append_8bit (#n: crc32_buf_len) (buf: BV.bv_t n) (b: U8.t):
  Tot (BV.bv_t (if n = 0 then 40 else n + 8)) =
  let v' = UInt.to_vec (U8.v b) in
  let open Seq in
  if n = 0 then
    zero_vec_l 8 (gf2_plus (BV.ones_vec #32) (BV.zero_vec #24 @| v'))
  else
    let padding = (BV.zero_vec #24) @| v' @| (BV.zero_vec #(n - 32)) in
    zero_vec_l 8 (buf +@ padding)

let rec crc32_u8_to_bits
  (#m: nat)
  (#n: crc32_buf_len)
  (data: Seq.seq U8.t {Seq.length data == m})
  (buf: BV.bv_t n):
  Tot (BV.bv_t (if m > 0 then
    if n = 0 then 32 + 8 * m else n + 8 * m
  else
    n))
  (decreases m) =
  if m > 1 then
    crc32_u8_to_bits
      #(m - 1)
      #_
      (Seq.tail data)
      (crc32_append_8bit buf (Seq.head data))
  else if m = 1 then
    crc32_append_8bit buf (Seq.head data)
  else
    buf

#set-options "--z3rlimit 120 --z3seed 1"
val crc32_u8_to_bits_append:
    #m1: nat
  -> #m2: nat
  -> #n: crc32_buf_len
  -> s1: Seq.seq U8.t{Seq.length s1 == m1}
  -> s2: Seq.seq U8.t{Seq.length s2 == m2}
  -> buf: BV.bv_t n
  -> Lemma (ensures
    crc32_u8_to_bits #m2 #(if m1 > 0 then
      if n = 0 then 32 + 8 * m1 else n + 8 * m1
    else
      n) s2 (crc32_u8_to_bits #m1 #n s1 buf) ==
    crc32_u8_to_bits #(m1 + m2) #n (Seq.append s1 s2) buf)

private unfold let crc32_to_vec (v: U32.t) =
  UInt.to_vec (UInt.logxor (U32.v v) ((pow2 32) - 1))

let crc32_matched (#n: crc32_buf_len) (buf: BV.bv_t n) (v: U32.t) (xor: bool) =
  let v' = if xor then crc32_to_vec v else UInt.to_vec (U32.v v) in
  (n == 0 ==> v' == (if xor then BV.zero_vec #32 else BV.ones_vec #32)) /\
  (n > 0 ==> v' == poly_mod buf)
