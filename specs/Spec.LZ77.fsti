module Spec.LZ77

module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CFlags = Yazi.CFlags
module HS = FStar.HyperStack
module I32 = FStar.Int32
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open FStar.Mul
open Lib.UInt
open Lib.Seq

let min_match = 3
let max_match = 258
let min_lookhead = max_match + min_match + 1

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

let window_size_upper_bound (b: window_bits) (w_size: window_size b): Lemma
  (ensures w_size <= 32768) = assert_norm(w_size == pow2 b)

#set-options "--z3rlimit 120 --fuel 8 --ifuel 8"
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

unfold let slided_window
  (w_size: U32.t)
  (w_range: U32.t{U32.v w_size <= U32.v w_range /\ U32.v w_range <= 2 * U32.v w_size})
  (window: B.lbuffer U8.t (2 * U32.v w_size)) =
  let open U32 in
  B.gsub window w_size (w_range -^ w_size)
  
unfold let sub_head_valid
  (h: HS.mem)
  (h_bits: U16.t {is_hash_bits (U16.v h_bits)})
  (w_size: U32.t)
  (w_range: U32.t{U32.v w_range <= 2 * U32.v w_size})
  (h_size: U32.t{is_hash_size (U16.v h_bits) (U32.v h_size)})
  (range: (i: nat) -> (p:Type0{p ==> i < U32.v h_size}))
  (head: B.lbuffer U16.t (U32.v h_size))
  (window: B.buffer U8.t{B.length window >= U32.v w_range}) =
  let open U32 in
  let head' = B.as_seq h head in
  let window' = B.as_seq h window in
  B.live h head /\ B.live h window /\ B.disjoint head window /\
  (forall (i: nat{range i /\ U16.v head'.[i] <> 0}).
    U16.v head'.[i] <= v w_range - min_match /\
    is_rolling_hash
      (U16.v h_bits)
      window'.[U16.v head'.[i]]
      window'.[1 + U16.v head'.[i]]
      window'.[2 + U16.v head'.[i]]
      (U16.uint_to_t i))
  
unfold let head_valid
  (h: HS.mem)
  (h_bits: U16.t {is_hash_bits (U16.v h_bits)})
  (w_size: U32.t)
  (w_range: U32.t{U32.v w_range <= 2 * U32.v w_size})
  (h_size: U32.t{is_hash_size (U16.v h_bits) (U32.v h_size)})
  (head: B.lbuffer U16.t (U32.v h_size))
  (window: B.buffer U8.t{B.length window >= U32.v w_range}) =
  sub_head_valid
    h h_bits w_size w_range h_size
    (fun j -> j < U32.v h_size)
    head window

#set-options "--z3rlimit 120 --fuel 0 --ifuel 0"
unfold let sub_prev_valid
  (h: HS.mem)
  (w_bits: U16.t {is_window_bits (U16.v w_bits)})
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)})
  (w_range: U32.t{U32.v w_range <= 2 * U32.v w_size})
  (range: (i: nat) -> (p: Type0{p ==> i < U32.v w_size}))
  (prev: B.lbuffer U16.t (U32.v w_size))
  (window: B.lbuffer U8.t (U32.v w_range)) =
  let open U32 in
  let open Lib.Seq in
  let prev' = B.as_seq h prev in
  let window' = B.as_seq h window in
  B.live h prev /\ B.live h window /\ B.disjoint prev window /\
  (forall (i: nat{range i}).
    (i + v w_size < v w_range ==>
      (U16.v prev'.[i] < i + v w_size /\
      (U16.v prev'.[i] <> 0 ==> window'.[U16.v prev'.[i]] == window'.[i + v w_size]))) /\
    (i + v w_size >= v w_range /\ i < v w_range /\ i >= min_match ==>
      (U16.v prev'.[i] < i /\
      (U16.v prev'.[i] <> 0 ==> window'.[U16.v prev'.[i]] == window'.[i]))))

let prev_valid
  (h: HS.mem)
  (w_bits: U16.t {is_window_bits (U16.v w_bits)})
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)})
  (w_range: U32.t{U32.v w_range <= 2 * U32.v w_size})
  (prev: B.lbuffer U16.t (U32.v w_size))
  (window: B.lbuffer U8.t (U32.v w_range)) =
  sub_prev_valid h w_bits w_size w_range (fun j -> j < U32.v w_size) prev window

unfold let hash_chain_valid
  (h: HS.mem)
  (w_bits: U16.t {is_window_bits (U16.v w_bits)})
  (h_bits: U16.t {is_hash_bits (U16.v h_bits)})
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)})
  (h_size: U32.t{is_hash_size (U16.v h_bits) (U32.v h_size)})
  (head: B.lbuffer U16.t (U32.v h_size))
  (prev: B.lbuffer U16.t (U32.v w_size))
  (w_range: U32.t{U32.v w_range <= 2 * U32.v w_size})
  (window: B.lbuffer U8.t (U32.v w_range)) =
  B.length window >= U32.v w_range /\
  (CFlags.fastest == false ==>
    prev_valid h w_bits w_size w_range prev window) /\
  head_valid h h_bits w_size w_range h_size head window

type lz77_state = s:Seq.seq U32.t{Seq.length s == 8}

open Lib.Seq

unfold let ins_h (s: lz77_state) = U32.v s.[0]
unfold let match_length (s: lz77_state) = U32.v s.[1]
unfold let match_start (s: lz77_state) = U32.v s.[2]
unfold let prev_match (s: lz77_state) = U32.v s.[3]
unfold let prev_length (s: lz77_state) = U32.v s.[4]
unfold let strstart (s: lz77_state) = U32.v s.[5]
unfold let lookahead (s: lz77_state) = U32.v s.[6]
unfold let insert (s: lz77_state) = U32.v s.[7]

unfold let ins_h_unchange (s0 s1: lz77_state) = ins_h s0 == ins_h s1
unfold let match_length_unchange (s0 s1: lz77_state) = match_length s0 == match_length s1
unfold let match_start_unchange (s0 s1: lz77_state) = match_start s0 == match_start s1
unfold let prev_match_unchange (s0 s1: lz77_state) = prev_match s0 == prev_match s1
unfold let prev_length_unchange (s0 s1: lz77_state) = prev_length s0 == prev_length s1
unfold let strstart_unchange (s0 s1: lz77_state) = strstart s0 == strstart s1
unfold let lookahead_unchange (s0 s1: lz77_state) = lookahead s0 == lookahead s1
unfold let insert_unchange (s0 s1: lz77_state) = insert s0 == insert s1

let strstart_lookahead_valid
  (s: lz77_state)
  (w_bits: U16.t{is_window_bits (U16.v w_bits)})
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)}) =
  strstart s + lookahead s <= 2 * U32.v w_size

unfold let slided_window_space_valid (s: lz77_state) (w_size more: U32.t) =
  let open U32 in
  (strstart s >= v w_size ==>
    v more == 2 * v w_size - lookahead s - strstart s + v w_size) /\
  (strstart s < v w_size ==>
    v more == 2 * v w_size - lookahead s - strstart s)

// TODO: verify block_start's lower bound
unfold let slide_window_pre
  (h: HS.mem)
  (w_bits: U16.t {is_window_bits (U16.v w_bits)})
  (state: B.lbuffer U32.t 8)
  (block_start: B.pointer I32.t)
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)})
  (window: B.lbuffer U8.t (2 * U32.v w_size)) =
  let open U32 in
  let state' = B.as_seq h state in
  B.live h block_start /\ B.live h window /\ B.live h state /\
  B.disjoint state window /\ B.disjoint state block_start /\ B.disjoint window block_start /\
  match_start state' >= v w_size /\
  match_start state' < 2 * v w_size /\
  strstart state' >= v w_size /\
  strstart state' < 2 * v w_size /\
  insert state' <= strstart state' - v w_size /\
  strstart_lookahead_valid state' w_bits w_size /\
  I32.v (B.get h block_start 0) >= -8454144

unfold let slide_window_buf_post
  (h0 h1: HS.mem)
  (w_bits: U16.t{is_window_bits (U16.v w_bits)})
  (state: B.lbuffer U32.t 8)
  (block_start: B.pointer I32.t)
  (w_size: U32.t{is_window_size (U16.v w_bits) (U32.v w_size)})
  (window: B.lbuffer U8.t (2 * U32.v w_size))
  (len: U32.t{U32.v len <= U32.v w_size}) =
  let s0 = B.as_seq h0 state in
  let s1 = B.as_seq h1 state in
  let w0 = B.as_seq h0 window in
  let w1 = B.as_seq h1 window in
  let w_size' = U32.v w_size in
  ins_h_unchange s0 s1 /\ match_length_unchange s0 s1 /\
  prev_match_unchange s0 s1 /\ prev_length_unchange s0 s1 /\
  lookahead_unchange s0 s1 /\ insert_unchange s0 s1 /\
  strstart s0 - U32.v w_size == strstart s1 /\
  match_start s0 - U32.v w_size == match_start s1 /\
  strstart_lookahead_valid s1 w_bits w_size /\
  I32.v (B.get h0 block_start 0) - U32.v w_size == I32.v (B.get h1 block_start 0) /\
  Seq.slice w0 w_size' (w_size' + U32.v len) == Seq.slice w1 0 (U32.v len) /\
  B.as_seq h0 (B.gsub window w_size len) == B.as_seq h1 (B.gsub window 0ul len)
