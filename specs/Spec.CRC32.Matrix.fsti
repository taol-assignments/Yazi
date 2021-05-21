module Spec.CRC32.Matrix

module BV = FStar.BitVector
module Seq = FStar.Seq
module Bits = Spec.CRC32.Bits

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

type matrix_seq = s:Seq.seq (BV.bv_t 32) {Seq.length s <= 32}

type sub_matrix_t (nzeros: nat{nzeros > 0}) = m: matrix_seq{
   forall i. {:pattern (Seq.index m i)}
     i < Seq.length m ==> is_magic_matrix_elem nzeros i (Seq.index m i)
}

type matrix_t (nzeros: nat{nzeros > 0}) = m: sub_matrix_t nzeros{Seq.length m == 32}
