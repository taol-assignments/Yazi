module Spec.CRC32.Matrix

module B = LowStar.Buffer
module BV = FStar.BitVector
module Bits = Spec.CRC32.Bits
module HS = FStar.HyperStack
module Seq = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module UInt = FStar.UInt

open FStar.Seq
open FStar.Mul
open Lib.Seq
open Lib.UInt

type matrix_buf = B.lbuffer U32.t 32

let magic_matrix_pattern (nzeros: pos) (i: nat{i < 32}):
  Tot (res: BV.bv_t (nzeros + 32){
    forall j.
      (j == nzeros + 31 - i ==> res.[j] == true) /\
      (j <> nzeros + 31 - i ==> res.[j] == false)
  }) =
  let zero_left = BV.zero_vec #(nzeros + 32 - i - 1) in
  let one = Bits.ones_vec_r 1 zero_left in
  Bits.zero_vec_r i one

/// An element in the magic matrix is the CRC-32 checksum of the magic matrix pattern.
unfold let is_magic_matrix_elem (nzeros: pos) (i: nat {i < 32}) (v: BV.bv_t 32) =
  Bits.poly_mod (magic_matrix_pattern nzeros i) == v

unfold let is_sub_matrix_buf
  (h: HS.mem) (len: nat{len <= 32}) (nzeros: pos) (buf: matrix_buf) =
  B.live h buf /\
  (forall (i: nat{i < len}).
    is_magic_matrix_elem nzeros i (UInt.to_vec (U32.v (B.as_seq h buf).[i])))

unfold let is_matrix_buf (h: HS.mem) (nzeros: pos) (buf: matrix_buf) =
  is_sub_matrix_buf h 32 nzeros buf

/// Extract the bit in the position len - i - 1.
/// The result bit is wrapped with zeros.
[@"opaque_to_smt"]
let bit_extract (#len: pos) (n: BV.bv_t len) (i: nat{i < len}):
 Tot (res: BV.bv_t len {
    forall j.
      (j == len - i - 1 ==> res.[j] == n.[j]) /\
      (j <> len - i - 1 ==> res.[j] == false)
  }) =
  let zero_left = if i = len - 1 then Seq.empty #bool else BV.zero_vec #(len - i - 1) in
  let bit = Seq.snoc zero_left n.[len - i - 1] in
  Bits.zero_vec_r #(len - i) i bit

/// Keep last i + 1 bits the same as the sequence n, and add zero to the left of the
/// result sequence.
[@"opaque_to_smt"]
let rec bit_sum (#len: pos) (n: BV.bv_t len) (i: nat{i < len}):
  Tot (res: BV.bv_t len {
    forall j.
      (j >= len - i - 1 ==> res.[j] == n.[j]) /\
      (j < len - i - 1 ==> res.[j] == false)
  }) =
  match i with
  | 0 -> bit_extract n i
  | _ -> Bits.gf2_plus (bit_extract n i) (bit_sum n (i - 1))

let bit_extract_eq_pattern (#len: nat{len > 32}) (n: BV.bv_t len) (i: nat{i < 32}): Lemma
  (requires n.[len - 1 - i] == true)
  (ensures bit_extract n i == magic_matrix_pattern (len - 32) i) =
  assert(Seq.equal (bit_extract n i) (magic_matrix_pattern (len - 32) i))

type sub_matrix_times_product (nzeros: pos) (i: nat{i < 32}) (vec: U32.t) = 
  res: U32.t{
    let vec' = Bits.zero_vec_l nzeros (UInt.to_vec (U32.v vec)) in
    UInt.to_vec (U32.v res) == Bits.poly_mod (bit_sum vec' i)
  }

type matrix_times_product (nzeros: pos) (vec: U32.t) =
  sub_matrix_times_product nzeros 31 vec

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
private let crc32_expand_aux
  (m: pos) (n: pos) (dm dn: Seq.seq U8.t): Lemma
  (requires Seq.length dm == m /\ Seq.length dn == n)
  (ensures (
    let open Bits in
    let mask_m = zero_vec_r (m * 8) (BV.ones_vec #32) in
    let mask_n = zero_vec_r (n * 8) (BV.ones_vec #32) in
    let mask_m' = zero_vec_l (m * 8) (BV.ones_vec #32) in
    let mask_n' = zero_vec_l (n * 8) (BV.ones_vec #32) in
    (zero_vec_l (n * 8) (mask_m' +@ zero_vec_l 32 (data_bits_rev dm))) +@
    (zero_vec_l (n * 8) mask_m) +@
    (zero_vec_r (m * 8) (mask_n' +@ zero_vec_l 32 (data_bits_rev dn))) +@
    zero_vec_r (m * 8) mask_n ==
    crc32_data_to_bits (n + m) (dm @| dn) +@
    zero_vec_r ((n + m) * 8) (BV.ones_vec #32))) =
  let open Bits in
  let mask_m = zero_vec_r (m * 8) (BV.ones_vec #32) in
  let mask_n = zero_vec_r (n * 8) (BV.ones_vec #32) in
  let mask_m' = zero_vec_l (m * 8) (BV.ones_vec #32) in
  let mask_n' = zero_vec_l (n * 8) (BV.ones_vec #32) in
  calc (==) {
    (zero_vec_l (n * 8) (mask_m' +@ zero_vec_l 32 (data_bits_rev dm))) +@
    (zero_vec_l (n * 8) mask_m) +@
    (zero_vec_r (m * 8) (mask_n' +@ zero_vec_l 32 (data_bits_rev dn))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      assert(Seq.equal
        (zero_vec_l (n * 8) (mask_m' +@ zero_vec_l 32 (data_bits_rev dm)))
        ((zero_vec_l (n * 8) mask_m') +@
         (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm)))));
      assert(Seq.equal
        (zero_vec_r (m * 8) (mask_n' +@ zero_vec_l 32 (data_bits_rev dn)))
        ((zero_vec_r (m * 8) mask_n') +@
         (zero_vec_r (m * 8) (zero_vec_l 32 (data_bits_rev dn)))))
    }
    (zero_vec_l (n * 8) mask_m') +@
    (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm))) +@
    (zero_vec_l (n * 8) mask_m) +@
    (zero_vec_r (m * 8) mask_n') +@
    (zero_vec_r (m * 8) (zero_vec_l 32 (data_bits_rev dn))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      assert(Seq.equal (zero_vec_l (n * 8) mask_m) (zero_vec_r (m * 8) mask_n'));
      Bits.logxor_vec_assoc
        (zero_vec_l (n * 8) mask_m')
        (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm)))
        ((zero_vec_l (n * 8) mask_m) +@ (zero_vec_r (m * 8) mask_n'));
      Bits.logxor_vec_self (zero_vec_l (n * 8) mask_m) (zero_vec_r (m * 8) mask_n');
      Bits.logxor_vec_zero (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm)))
    }
    (zero_vec_l (n * 8) mask_m') +@
    (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm))) +@
    (zero_vec_r (m * 8) (zero_vec_l 32 (data_bits_rev dn))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      assert(Seq.equal
        (zero_vec_l (n * 8) (zero_vec_l 32 (data_bits_rev dm)))
        (zero_vec_l 32 (zero_vec_l (n * 8) (data_bits_rev dm))));
      assert(Seq.equal
        (zero_vec_r (m * 8) (zero_vec_l 32 (data_bits_rev dn)))
        (zero_vec_l 32 (zero_vec_r (m * 8) (data_bits_rev dn))))
    }
    (zero_vec_l (n * 8) mask_m') +@
    ((zero_vec_l 32 (zero_vec_l (n * 8) (data_bits_rev dm))) +@
      (zero_vec_l 32 (zero_vec_r (m * 8) (data_bits_rev dn)))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      assert(Seq.equal
        ((zero_vec_l 32 (zero_vec_l (n * 8) (data_bits_rev dm))) +@
          (zero_vec_l 32 (zero_vec_r (m * 8) (data_bits_rev dn))))
        (zero_vec_l 32 (
          (zero_vec_l (n * 8) (data_bits_rev dm)) +@
          (zero_vec_r (m * 8) (data_bits_rev dn))
        )))
    }
    (zero_vec_l (n * 8) mask_m') +@
    (zero_vec_l 32 (
      (zero_vec_l (n * 8) (data_bits_rev dm)) +@
      (zero_vec_r (m * 8) (data_bits_rev dn)))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      assert(Seq.equal
        ((zero_vec_l (n * 8) (data_bits_rev dm)) +@ (zero_vec_r (m * 8) (data_bits_rev dn)))
        ((data_bits_rev dn) @| data_bits_rev dm))
    }
    (zero_vec_l (n * 8) mask_m') +@
    (zero_vec_l #((n + m) * 8) 32 ((data_bits_rev dn) @| data_bits_rev dm)) +@
    zero_vec_r (m * 8) mask_n;
    =={
      data_bits_rev_app dm dn;
      zero_vec_l_app (BV.ones_vec #32) (m * 8) (n * 8)
    }
    (zero_vec_l ((n + m) * 8) (BV.ones_vec #32)) +@
    (zero_vec_l #((n + m) * 8) 32 (data_bits_rev (dm @| dn))) +@
    zero_vec_r (m * 8) mask_n;
    =={
      crc32_data_to_bits_rev (n + m) (dm @| dn);
      assert(Seq.equal
        (zero_vec_r (m * 8) mask_n)
        (zero_vec_r ((n + m) * 8) (BV.ones_vec #32)))
    }
    crc32_data_to_bits (n + m) (dm @| dn) +@ zero_vec_r ((n + m) * 8) (BV.ones_vec #32);
  }

private let crc32_matched_append_aux
  (m: pos) (n: pos) (dm dn: Seq.seq U8.t) (cm cn: U32.t)
  (cm': matrix_times_product (n * 8) cm): Lemma
  (requires
    Seq.length dm == m /\ Seq.length dn == n /\
    Bits.crc32_matched m dm cm true /\ Bits.crc32_matched n dn cn true)
  (ensures Bits.crc32_matched (m + n) (dm @| dn) (U32.logxor cm' cn) true) =
  let open Spec.CRC32.Bits in
  let vcm' = Bits.zero_vec_l (n * 8) (UInt.to_vec (U32.v cm)) in
  let bm = crc32_data_to_bits m dm in
  let bn = crc32_data_to_bits n dn in
  let mask_m = zero_vec_r (m * 8) (BV.ones_vec #32) in
  let mask_n = zero_vec_r (n * 8) (BV.ones_vec #32) in
  let mask_m' = zero_vec_l (m * 8) (BV.ones_vec #32) in
  let mask_n' = zero_vec_l (n * 8) (BV.ones_vec #32) in
  let pm = zero_vec_l (n * 8) (bm +@ mask_m) in
  let pn = zero_vec_r (m * 8) (bn +@ mask_n) in
  calc (==) {
    UInt.to_vec (U32.v cm');
    =={assert(Seq.equal (bit_sum vcm' 31) vcm')}
    poly_mod vcm';
    =={crc32_matched_xor_inv_3 m dm cm}
    poly_mod (zero_vec_l (n * 8) (poly_mod (bm +@ mask_m)));
    =={poly_mod_zero_prefix (bm +@ mask_m) (n * 8)}
    poly_mod pm;
  };
  UInt.logxor_lemma_1 (U32.v cn);
  assert(U32.v cn `UInt.logxor` 0 == U32.v cn);
  
  UInt.logxor_self (UInt.ones 32);
  assert(
    (U32.v cn) `UInt.logxor` 0 ==
    (U32.v cn) `UInt.logxor` ((UInt.ones 32) `UInt.logxor` (UInt.ones 32)));

  calc (==) {
    UInt.to_vec (U32.v cn);
    =={
      UInt.logxor_associative (U32.v cn) (UInt.ones 32) (UInt.ones 32);
      pow2_mask 32
    }
    poly_mod bn +@ BV.ones_vec #32;
    =={
      poly_mod_small mask_n;
      assert(Seq.equal (BV.ones_vec #32) (slice mask_n 0 32))
    }
    poly_mod bn +@ poly_mod mask_n;
    =={poly_mod_add bn mask_n}
    poly_mod (bn +@ mask_n);
  };

  assert(UInt.to_vec (U32.v cm' `UInt.logxor` U32.v cn) ==
    poly_mod pm +@ poly_mod (bn +@ mask_n));

  calc (==) {
    poly_mod pm +@ poly_mod (bn +@ mask_n);
    =={poly_mod_zero_suffix (bn +@ mask_n) (m * 8)}
    poly_mod pm +@ poly_mod pn;
    =={poly_mod_add pm pn}
    poly_mod (pm +@ pn);
    =={
      assert(Seq.equal
        (zero_vec_l (n * 8) (bm +@ mask_m))
        ((zero_vec_l (n * 8) bm) +@ zero_vec_l (n * 8) mask_m));
      assert(Seq.equal
        (zero_vec_r (m * 8) (bn +@ mask_n))
        ((zero_vec_r (m * 8) bn) +@ zero_vec_r (m * 8) mask_n))
    }
    poly_mod (
      (zero_vec_l (n * 8) bm) +@ (zero_vec_l (n * 8) mask_m) +@
      ((zero_vec_r (m * 8) bn) +@ zero_vec_r (m * 8) mask_n));
    =={
      Bits.logxor_vec_assoc
        (zero_vec_l (n * 8) mask_m)
        (zero_vec_r (m * 8) bn)
        (zero_vec_r (m * 8) mask_n)
    }
    poly_mod (
      (zero_vec_l (n * 8) bm) +@
      (zero_vec_l (n * 8) mask_m) +@
      (zero_vec_r (m * 8) bn) +@
      zero_vec_r (m * 8) mask_n);
    =={
      crc32_data_to_bits_rev m dm;
      crc32_data_to_bits_rev n dn
    }
    poly_mod (
      (zero_vec_l (n * 8) (mask_m' +@ zero_vec_l 32 (data_bits_rev dm))) +@
      (zero_vec_l (n * 8) mask_m) +@
      (zero_vec_r (m * 8) (mask_n' +@ zero_vec_l 32 (data_bits_rev dn))) +@
      zero_vec_r (m * 8) mask_n);
    =={crc32_expand_aux m n dm dn}
    poly_mod (
      crc32_data_to_bits (n + m) (dm @| dn) +@
      zero_vec_r ((n + m) * 8) (BV.ones_vec #32));
    =={
      poly_mod_add
        (crc32_data_to_bits (n + m) (dm @| dn))
        (zero_vec_r ((n + m) * 8) (BV.ones_vec #32))
    }
    poly_mod (crc32_data_to_bits (n + m) (dm @| dn)) +@
    poly_mod (zero_vec_r ((n + m) * 8) (BV.ones_vec #32));
    =={
      poly_mod_zero_suffix (BV.ones_vec #32) ((n + m) * 8)
    }
    poly_mod (crc32_data_to_bits (n + m) (dm @| dn)) +@ BV.ones_vec #32;
  }

let crc32_matched_append
  (m: nat) (n: pos) (dm dn: Seq.seq U8.t) (cm cn: U32.t)
  (cm': matrix_times_product (n * 8) cm): Lemma
  (requires
    Seq.length dm == m /\ Seq.length dn == n /\
    Bits.crc32_matched m dm cm true /\ Bits.crc32_matched n dn cn true)
  (ensures Bits.crc32_matched (m + n) (dm @| dn) (U32.logxor cm' cn) true) =
  if m = 0 then begin
    let vcm' = Bits.zero_vec_l (n * 8) (UInt.to_vec (U32.v cm)) in
    assert(Seq.equal (dm @| dn) dn);
    calc (==) {
      U32.v cm';
      =={}
      UInt.from_vec (UInt.to_vec (U32.v cm'));
      =={}
      UInt.from_vec (Bits.poly_mod (bit_sum vcm' 31));
      =={
        calc (==) {
          vcm' <: BV.bv_t (n * 8 + 32);
          =={}
          (Bits.zero_vec_l (n * 8) (UInt.to_vec (U32.v cm))) <: BV.bv_t (n * 8 + 32);
          =={
            calc (==) {
              UInt.to_vec (U32.v cm);
              =={
                Bits.crc32_matched_zero cm true;
                assert(Seq.equal (UInt.to_vec (UInt.zero 32)) (UInt.to_vec (U32.v cm)))
              }
              UInt.to_vec (UInt.zero 32);
              =={
                assert(
                  UInt.from_vec (UInt.to_vec (UInt.zero 32)) ==
                  UInt.from_vec (BV.zero_vec #32))
              }
              BV.zero_vec #32;
            }
          }
          (Bits.zero_vec_l (n * 8) (BV.zero_vec #32)) <: BV.bv_t (n * 8 + 32);
          =={
            assert(Seq.equal
              (Bits.zero_vec_l (n * 8) (BV.zero_vec #32))
              (BV.zero_vec #(n * 8 + 32)))
          }
          BV.zero_vec #(n * 8 + 32);
        }
      }
      UInt.from_vec (Bits.poly_mod (bit_sum (BV.zero_vec #(n * 8 + 32)) 31));
      =={
        assert(Seq.equal
          (bit_sum (BV.zero_vec #(n * 8 + 32)) 31)
          (BV.zero_vec #(n * 8 + 32)))
      }
      UInt.from_vec (Bits.poly_mod (BV.zero_vec #(n * 8 + 32)));
      =={Bits.poly_mod_zero (BV.zero_vec #(n * 8 + 32))}
      UInt.from_vec (BV.zero_vec #32);
      =={}
      0;
    }
  end else
    crc32_matched_append_aux m n dm dn cm cn cm'
