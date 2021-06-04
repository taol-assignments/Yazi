module Spec.LZ77

module Cast = FStar.Int.Cast
module U8 = FStar.UInt8
module U16 = FStar.UInt16

open FStar.Mul
open Lib.UInt

let min_match = 3
let max_match = 258

unfold let is_hash_bits (b: nat) = b >= 8 /\ b <= 16
type hash_bits = b: nat{is_hash_bits b}

unfold let is_hash_mask (bits: hash_bits) (m: nat) = m == (pow2 bits) - 1
type hash_mask (bits: hash_bits) = m: nat{is_hash_mask bits m}

unfold let is_hash_size (bits: hash_bits) (s: nat) = s == pow2 bits
type hash_size (bits: hash_bits) = s: nat{is_hash_size bits s}

unfold let is_hash_shift (bits: hash_bits) (s: nat) = s == (bits + min_match - 1) / min_match
type hash_shift (bits: hash_bits) = s: nat{is_hash_shift bits s}

unfold let is_window_bits (b: nat) = b >= 8 /\ b <= 15
type window_bits = b: nat{is_window_bits b}

unfold let is_window_mask (b: window_bits) (m: nat) = m == (pow2 b) - 1
type window_mask (bits: window_bits) = m: nat{is_window_mask bits m}

unfold let is_window_size (b: window_bits) (s: nat) = s == pow2 b
type window_size (bits: window_bits) = s: nat{is_window_size bits s}

#set-options "--z3rlimit 120 --fuel 4 --ifuel 4"
let is_rolling_hash (bits: hash_bits) (a b c: U8.t) (h: U16.t) =
  let open FStar.Mul in
  let shift = (bits + min_match - 1) / min_match in
  let mask = (pow2 bits) - 1 in
  let a' = Cast.uint8_to_uint16 a in
  let b' = Cast.uint8_to_uint16 b in
  let c' = Cast.uint8_to_uint16 c in
  let a'' = UInt.shift_left (U16.v a') (shift * 2) in
  let b'' = UInt.shift_left (U16.v b') shift in
  U16.v h == UInt.logand (UInt.logxor (UInt.logxor a'' b'') (U16.v c')) mask

#set-options "--fuel 16 --ifuel 16"
let hash_mask_ones (n: hash_bits): Lemma
  (ensures forall (i: nat{i < 16}).
    (i < 16 - n ==> UInt.nth #16 ((pow2 n) - 1) i == false) /\
    (i >= 16 - n ==> UInt.nth #16 ((pow2 n) - 1) i == true)) = ()

val roll_hash_eq:
    bits: hash_bits
  -> mask: U16.t{is_hash_mask bits (U16.v mask)}
  -> shift: U16.t{is_hash_shift bits (U16.v shift)}
  -> a: U8.t
  -> b: U8.t
  -> c: U8.t
  -> d: U8.t
  -> h: U16.t {is_rolling_hash bits a b c h}
  -> Lemma
  (ensures is_rolling_hash bits b c d (
    U16.logand (U16.logxor (U16.shift_left h (Cast.uint16_to_uint32 shift)) (Cast.uint8_to_uint16 d)) mask
  ))
