module Spec.CRC32.Matrix

module B = LowStar.Buffer
module BV = FStar.BitVector
module Bits = Spec.CRC32.Bits
module HS = FStar.HyperStack
module Seq = FStar.Seq
module U32 = FStar.UInt32
module UInt = FStar.UInt

let magic_matrix_pattern (nzeros: nat{nzeros > 0}) (i: nat{i < 32}):
  res: BV.bv_t (nzeros + 32){
    forall j.
      (j == nzeros + 31 - i ==> Seq.index res j == true) /\
      (j <> nzeros + 31 - i ==> Seq.index res j == false)
  } =
  let zero_left = BV.zero_vec #(nzeros + 32 - i - 1) in
  let one = Bits.ones_vec_r 1 zero_left in
  Bits.zero_vec_r i one

unfold let is_magic_matrix_elem (nzeros: nat{nzeros > 0}) (i: nat {i < 32}) (v: BV.bv_t 32) =
  Bits.poly_mod (magic_matrix_pattern nzeros i) == v

unfold let is_sub_matrix_buf
  (h: HS.mem)
  (len: nat{len <= 32})
  (nzeros: nat{nzeros > 0})
  (buf: B.buffer U32.t{B.length buf == 32}) =
  B.live h buf /\
  (forall (i: nat{i < len}).
    is_magic_matrix_elem nzeros i (UInt.to_vec (U32.v (Seq.index (B.as_seq h buf) i))))

unfold let is_matrix_buf
  (h: HS.mem)
  (nzeros: nat{nzeros > 0})
  (buf: B.buffer U32.t{B.length buf == 32}) = is_sub_matrix_buf h 32 nzeros buf

let bit_extract
  (#len: nat{len > 0})
  (n: BV.bv_t len)
  (i: nat{0 <= i /\ i <= len - 1}):
  Tot (res: BV.bv_t len {
    forall j.
      (j == len - i - 1 ==> Seq.index res j == Seq.index n j) /\
      (j <> len - i - 1 ==> Seq.index res j == false)
  }) =
  let zero_left = if i = len - 1 then Seq.empty #bool else BV.zero_vec #(len - i - 1) in
  let bit = Seq.snoc zero_left (Seq.index n (len - i - 1)) in
  Bits.zero_vec_r #(len - i) i bit
  
let rec bit_sum
  (#len: nat{len > 0})
  (n: BV.bv_t len)
  (i: nat{0 <= i /\ i <= len - 1}):
  Tot (res: BV.bv_t len {
    forall j.
      (j >= len - i - 1 ==> Seq.index res j == Seq.index n j) /\
      (j < len - i - 1 ==> Seq.index res j == false)
  }) =
  match i with
  | 0 -> bit_extract n i
  | _ -> Bits.gf2_plus (bit_extract n i) (bit_sum n (i - 1))

let bit_extract_eq_pattern
  (#len: nat{len > 32})
  (n: BV.bv_t len)
  (i: nat{i < 32}): Lemma
  (requires Seq.index n (len - 1 - i) == true)
  (ensures bit_extract n i == magic_matrix_pattern (len - 32) i) =
  assert(Seq.equal (bit_extract n i) (magic_matrix_pattern (len - 32) i))

type sub_matrix_times_product (nzeros: nat{nzeros > 0}) (i: nat{i < 32}) (vec: U32.t) = 
  res: U32.t{
    let vec' = Bits.zero_vec_l nzeros (UInt.to_vec (U32.v vec)) in
    UInt.to_vec (U32.v res) == Bits.poly_mod (bit_sum vec' i)
  }

type matrix_times_product (nzeros: nat{nzeros > 0}) (vec: U32.t) =
  sub_matrix_times_product nzeros 31 vec

type matrix_buf = m: B.buffer U32.t{B.length m == 32}
