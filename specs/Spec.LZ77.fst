module Spec.LZ77

module Cast = FStar.Int.Cast
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Mul
open Lib.UInt

unfold let (^) #n = UInt.logxor #n
unfold let (&@) #n = UInt.logand #n
unfold let (<<) #n = UInt.shift_left #n

#set-options "--fuel 4 --ifuel 4"
let triple_shift_zero
  (#n: hash_bits)
  (shift: hash_shift n)
  (mask: hash_mask n)
  (a: U8.t): Lemma
  (ensures (((U16.v (Cast.uint8_to_uint16 a)) << (3 * shift)) &@ mask) == 0) =
  assert(3 * shift >= n);
  hash_mask_ones n;
  let a' = (U16.v (Cast.uint8_to_uint16 a)) << (3 * shift) in
  assert(Seq.equal (UInt.to_vec (a' &@ mask)) (UInt.to_vec (UInt.zero 16)))

#set-options "--fuel 0 --ifuel 0"
let roll_hash_eq bits m s a b c d h =
  let open U16 in
  let m' = v m in
  let s' = v s in
  let a' = Cast.uint8_to_uint16 a in
  let b' = Cast.uint8_to_uint16 b in
  let c' = Cast.uint8_to_uint16 c in
  let d' = Cast.uint8_to_uint16 d in
  let a'' = v a' in
  let b'' = v b' in
  let c'' = v c' in
  let d'' = v d' in
  let h' = ((h <<^ (Cast.uint16_to_uint32 s)) ^^ d') &^ m in
  UInt.shift_left_logand_lemma (((a'' << (2 * s')) ^ (b'' << s')) ^ c'') m' s';
  UInt.shift_left_logxor_lemma ((a'' << (2 * s')) ^ (b'' << s')) c'' s';
  UInt.shift_left_logxor_lemma (a'' << (2 * s')) (b'' << s') s';
  logxor_logand_distr
    ((((a'' << (3 * s')) ^ (b'' << (2 * s'))) ^ (c'' << s')) &@ (m' << s'))
    d''
    m';
  UInt.logand_associative
    (((a'' << (3 * s')) ^ (b'' << (2 * s'))) ^ (c'' << s'))
    (m' << s')
    m';
  UInt.logand_commutative (m' << s') m';
  UInt.logand_associative
    (((a'' << (3 * s')) ^ (b'' << (2 * s'))) ^ (c'' << s'))
    m'
    (m' << s');
  logxor_logand_distr
    ((a'' << (3 * s')) ^ (b'' << (2 * s')))
    (c'' << s')
    m';
  logxor_logand_distr (a'' << (3 * s')) (b'' << (2 * s')) m';
  triple_shift_zero #bits s' m' a;
  UInt.logxor_commutative 0 ((b'' << (2 * s')) &@ m');
  UInt.logxor_lemma_1 ((b'' << (2 * s')) &@ m');
  logxor_logand_distr (b'' << (2 * s')) (c'' << s') m';
  shift_left_append b'' s' s';
  UInt.shift_left_logxor_lemma (b'' << s') c'' s';
  UInt.logand_associative (((b'' << s') ^ c'') << s') m' (m' << s');
  UInt.logand_associative (((b'' << s') ^ c'') << s') (m' << s') m';
  UInt.shift_left_logand_lemma ((b'' << s') ^ c'') m' s';
  logxor_logand_distr ((((b'' << s') ^ c'') &@ m') << s') d'' m';
  assert(forall (i: nat{i < 16}).
    UInt.nth (((((b'' << s') ^ c'') &@ m') << s') &@ m') i ==
    UInt.nth ((((b'' << s') ^ c'') << s') &@ m') i);
  UInt.to_vec_lemma_2
    (((((b'' << s') ^ c'') &@ m') << s') &@ m')
    ((((b'' << s') ^ c'') << s') &@ m');
  logxor_logand_distr (((b'' << s') ^ c'') << s') d'' m'
