module Spec.LZ77

module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module HS = FStar.HyperStack
module I32 = FStar.Int32
module LB = Lib.Buffer
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open FStar.Mul
open Lib.UInt
open Lib.Seq
open Yazi.LZ77.Types

let min_match = 4
let max_match = 258
let min_lookhead = max_match + min_match + 1

unfold let is_hash_bits (b: nat) = b >= 8 /\ b <= 16
type hash_bits = b: nat{is_hash_bits b}

unfold let is_hash_mask (bits: hash_bits) (m: nat) = m == (pow2 bits) - 1
type hash_mask (bits: hash_bits) = m: nat{is_hash_mask bits m}

unfold let is_hash_size (bits: hash_bits) (s: nat) = s == pow2 bits
type hash_size (bits: hash_bits) = s: nat{is_hash_size bits s}

unfold let is_window_bits (b: nat) = b >= 8 /\ b <= 15
type window_bits = b: nat{is_window_bits b}

unfold let is_window_mask (b: window_bits) (m: nat) = m == (pow2 b) - 1
type window_mask (bits: window_bits) = m: nat{is_window_mask bits m}

unfold let is_window_size (b: window_bits) (s: nat) = s == pow2 b
type window_size (bits: window_bits) = s: nat{is_window_size bits s}

let window_size_upper_bound (b: window_bits) (w_size: window_size b): Lemma
  (ensures w_size <= 32768) = assert_norm(w_size == pow2 b)

let context_valid (h: HS.mem) (ctx: lz77_context_p) =
  let open U16 in
  CB.length ctx == 1 /\
  (let c = B.get h (CB.as_mbuf ctx) 0 in
  is_window_bits (v c.w_bits) /\
  is_window_mask (v c.w_bits) (v c.w_mask) /\
  is_window_size (v c.w_bits) (U32.v c.w_size) /\
  U32.v c.window_size == (U32.v c.w_size) * 2 /\
  B.length c.window == U32.v c.window_size /\
  B.length c.prev == U32.v c.w_size /\
  is_hash_bits (v c.h_bits) /\
  is_hash_size (v c.h_bits) (U32.v c.h_size) /\
  is_hash_mask (v c.h_bits) (v c.h_mask) /\
  U32.v c.window_size - min_match + 1 > U32.v c.w_size /\
  B.length c.head == U32.v c.h_size /\
  CB.live h ctx /\ B.live h c.prev /\ B.live h c.window /\ B.live h c.head /\ B.live h c.prev /\
  B.disjoint c.window c.prev /\ B.disjoint c.window c.head /\ B.disjoint c.prev c.head /\
  B.frameOf c.window == B.frameOf c.prev /\ B.frameOf c.prev == B.frameOf c.head /\
  B.frameOf (CB.as_mbuf ctx) <> B.frameOf c.prev /\
  HS.disjoint (B.frameOf (CB.as_mbuf ctx)) (B.frameOf c.prev))

noextract private type valid_context_p (h: HS.mem) =
  ctx: lz77_context_p{context_valid h ctx}

let window_index_upper_bound (h: HS.mem) (ctx: valid_context_p h) (i: nat): Lemma
  (requires i < (U32.v (B.get h (CB.as_mbuf ctx) 0).window_size))
  (ensures i < pow2 16) =
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  calc (<) {
    i;
    <{}
    U32.v ctx'.window_size;
    =={}
    2 * pow2 (U16.v ctx'.w_bits);
    <={Math.Lemmas.pow2_le_compat 15 (U16.v ctx'.w_bits)}
    2 * pow2 15;
    =={Math.Lemmas.pow2_double_mult 15}
    pow2 16;
  }

#set-options "--z3rlimit 120 --fuel 0 --ifuel 0"
let window_mask_aux
  (w_bits: window_bits)
  (w_size: window_size w_bits)
  (w_mask: window_mask w_bits)
  (i: UInt.uint_t 32): Lemma
  (requires i < 2 * w_size)
  (ensures
    (i < w_size ==> UInt.logand i (UInt.to_uint_t 32 w_mask) == i) /\
    (i >= w_size ==> UInt.logand i (UInt.to_uint_t 32 w_mask) == i - w_size)) =
  UInt.logand_mask i w_bits;

  if i < w_size then
    ()
  else
    calc (==) {
      UInt.logand i (UInt.to_uint_t 32 w_mask);
      =={}
      i % (pow2 w_bits);
      =={Math.Lemmas.lemma_mod_sub i w_size 1}
      (i - w_size) % w_size;
      =={Math.Lemmas.small_mod (i - w_size) w_size}
      i - w_size;
    }

assume val hash: (bits: hash_bits) -> U8.t -> U8.t -> U8.t -> U8.t -> Tot (res: U32.t{
  U32.v res < pow2 bits
})

let hash_neq (bits: hash_bits) (a b c d: U8.t): Lemma
  (ensures forall (a' b' c' d': U8.t). hash bits a b c d <> hash bits a' b' c' d' ==>
    a <> a' \/ b <> b' \/ c <> c' \/ d <> d') = ()

let hash_loc_buffer (h: HS.mem) (ctx: valid_context_p h) =
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  (B.loc_buffer ctx'.head) `B.loc_union`
  (if CFlags.fastest then B.loc_none else B.loc_buffer ctx'.prev)

type hash_range (h: HS.mem) (ctx: valid_context_p h) =
  hr: U32.t {U32.v hr <= U32.v (B.get h (CB.as_mbuf ctx) 0).window_size - min_match + 1}

type slided_flag (#h: HS.mem) (#ctx: valid_context_p h) (hr: hash_range h ctx) = b: bool{
  b == true ==> U32.v hr >= U32.v (B.get h (CB.as_mbuf ctx) 0).w_size
}

let slided_value
  (#h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (slided: slided_flag h_range) =
  let open U32 in
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let h_range' = if slided then h_range -^ ctx'.w_size else h_range in
  let window' = if slided then 
    B.as_seq h (B.gsub ctx'.window ctx'.w_size ctx'.w_size)
  else
    B.as_seq h ctx'.window
  in
  (U32.v h_range', window')

unfold let sub_head_valid
  (h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (range: (i: nat) -> (p:Type0{p ==> i < U32.v (B.get h (CB.as_mbuf ctx) 0).h_size}))
  (slided: slided_flag h_range) =
  let open U32 in
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let head' = B.as_seq h ctx'.head in
  let (h_range', window') = slided_value ctx h_range slided in
  (forall (i: nat{range i /\ U16.v head'.[i] <> 0}).
    let h_bits = U16.v ctx'.h_bits in
    let head = U16.v head'.[i] in
    head < h_range' /\
    i == v (hash
      h_bits
      window'.[head]
      window'.[head + 1]
      window'.[head + 2]
      window'.[head + 3]))

unfold let head_valid
  (h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (slided: slided_flag h_range) =
  sub_head_valid h ctx h_range (fun j -> j < U32.v (B.get h (CB.as_mbuf ctx) 0).h_size) slided

let sub_prev_valid
  (h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (range: (i: nat) -> (p:Type0{p ==> i < U32.v (B.get h (CB.as_mbuf ctx) 0).w_size}))
  (slided: slided_flag h_range) =
  let open U32 in let open Lib.Seq in
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let prev' = B.as_seq h ctx'.prev in
  let (h_range', w) = slided_value ctx h_range slided in
  let hash = hash (U16.v ctx'.h_bits) in
  (h_range' > 0 ==> (forall (i: nat{range i}).
    let b = U16.v prev'.[i] in
    let b' = i + v ctx'.w_size in
    b < h_range' /\
    (b <> 0 ==>
      ((b' < h_range' ==>
        (b < i + v ctx'.w_size /\
        hash w.[b] w.[b + 1] w.[b + 2] w.[b + 3] ==
        hash w.[b'] w.[b' + 1] w.[b' + 2] w.[b' + 3]))) /\
      (h_range' <= b' /\ i < h_range' ==>
        (b < i /\
        hash w.[b] w.[b + 1] w.[b + 2] w.[b + 3] ==
        hash w.[i] w.[i + 1] w.[i + 2] w.[i + 3])))))

let prev_valid
  (h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (slided: slided_flag h_range) =
  sub_prev_valid h ctx h_range (fun j ->
    let open U32 in
    let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    if v h_range >= v ctx'.w_size then
      j < U32.v (B.get h (CB.as_mbuf ctx) 0).w_size
    else
      j < U32.v h_range)
    slided

unfold let hash_chain_valid
  (h: HS.mem)
  (ctx: valid_context_p h)
  (h_range: hash_range h ctx)
  (slided: slided_flag h_range) =
  (CFlags.fastest == false ==> prev_valid h ctx h_range slided) /\
  head_valid h ctx h_range slided

type lz77_state = s:Seq.seq U32.t{Seq.length s == 7}

unfold let match_length (s: lz77_state) = U32.v s.[0]
unfold let match_start (s: lz77_state) = U32.v s.[1]
unfold let prev_match (s: lz77_state) = U32.v s.[2]
unfold let prev_length (s: lz77_state) = U32.v s.[3]
unfold let strstart (s: lz77_state) = U32.v s.[4]
unfold let lookahead (s: lz77_state) = U32.v s.[5]
unfold let insert (s: lz77_state) = U32.v s.[6]
unfold let window_end (s: lz77_state) = strstart s + lookahead s
unfold let max_hash_end (s: lz77_state) = window_end s - min_match + 1

unfold let match_length_unchange (s0 s1: lz77_state) = match_length s0 == match_length s1
unfold let match_start_unchange (s0 s1: lz77_state) = match_start s0 == match_start s1
unfold let prev_match_unchange (s0 s1: lz77_state) = prev_match s0 == prev_match s1
unfold let prev_length_unchange (s0 s1: lz77_state) = prev_length s0 == prev_length s1
unfold let strstart_unchange (s0 s1: lz77_state) = strstart s0 == strstart s1
unfold let lookahead_unchange (s0 s1: lz77_state) = lookahead s0 == lookahead s1
unfold let insert_unchange (s0 s1: lz77_state) = insert s0 == insert s1

// This condition should hold in all acases for all LZ77 states.
let state_valid (h: HS.mem) (ctx: lz77_context_p) (s: lz77_state_t) =
  context_valid h ctx /\ B.live h s /\
  B.disjoint (CB.as_mbuf ctx) s /\
  (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let s' = B.as_seq h s in
  HS.disjoint (B.frameOf s) (B.frameOf ctx'.head) /\
  
  strstart s' + lookahead s' <= 2 * U32.v ctx'.w_size /\
  insert s' <= strstart s' /\
  match_length s' <= min_match /\
  prev_length s' <= min_match /\
  match_start s' <= 2 * U32.v ctx'.w_size - min_match /\
  prev_match s' <= 2 * U32.v ctx'.w_size - min_match)

let do_init_input_hash_pre
  (h: HS.mem)
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (i lk: U32.t)
  (ins: UInt.uint_t 32) =
    let open U32 in
    let state' = B.as_seq h state in
    state_valid h ctx state /\
    strstart state' - insert state' == v i /\
    v i < strstart state' /\
    lookahead state' + insert state' >= min_match /\
    hash_chain_valid h ctx i false /\
    v lk == lookahead state' /\
    ins == insert state'

let do_init_input_hash_post (h0 h1: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let s0 = B.as_seq h0 state in
  let s1 = B.as_seq h1 state in
  let e0 = max_hash_end s1 in
  let e1 = strstart s1 in
  state_valid h0 ctx state /\
  B.modifies ((B.loc_buffer state) `B.loc_union` hash_loc_buffer h0 ctx) h0 h1 /\
  LB.unchange_except h0 h1 state 6 /\
  state_valid h1 ctx state /\
  (e0 >= 0 /\ e1 >= 0 ==>
    (e0 < e1 ==> hash_chain_valid h1 ctx (U32.uint_to_t e0) false) /\
    (e1 <= e0 ==> hash_chain_valid h1 ctx (U32.uint_to_t e1) false))

let init_input_hash_pre (h: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let state' = B.as_seq h state in
  B.live h state /\
  (lookahead state' + insert state' >= min_match ==>
    state_valid h ctx state /\
    hash_chain_valid h ctx (U32.uint_to_t (strstart state' - insert state')) false)

let init_input_hash_post (h0 h1: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let s0 = B.as_seq h0 state in
  (lookahead s0 + insert s0 >= min_match ==> do_init_input_hash_post h0 h1 ctx state) /\
  (lookahead s0 + insert s0 < min_match ==> B.modifies B.loc_none h0 h1)

let do_init_dict_hash_pre
  (h: HS.mem)
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (i: U32.t)
  (h_end: UInt.uint_t 32) =
    let open U32 in
    let state' = B.as_seq h state in
    state_valid h ctx state /\
    lookahead state' >= min_match /\
    strstart state' <= v i /\ v i < max_hash_end state' /\
    hash_chain_valid h ctx i false /\
    h_end == max_hash_end state'

let do_init_dict_hash_post (h0 h1: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let state' = B.as_seq h0 state in
  state_valid h0 ctx state /\
  lookahead state' >= min_match /\
  B.modifies (hash_loc_buffer h0 ctx) h0 h1 /\
  state_valid h1 ctx state /\
  hash_chain_valid h1 ctx (U32.uint_to_t (max_hash_end state')) false
  
unfold let init_dict_hash_pre (h: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let state' = B.as_seq h state in
  B.live h state /\
  state_valid h ctx state /\
  lookahead state' >= min_match /\
  hash_chain_valid h ctx (U32.uint_to_t (strstart state')) false

unfold let init_dict_hash_post (h0 h1: HS.mem) (ctx: lz77_context_p) (state: lz77_state_t) =
  let state' = B.as_seq h1 state in
  init_dict_hash_pre h0 ctx state /\
  B.modifies (hash_loc_buffer h0 ctx) h0 h1 /\
  state_valid h1 ctx state /\
  hash_chain_valid h1 ctx (U32.uint_to_t (max_hash_end state')) false

// TODO: verify block_start's lower bound
unfold let slide_window_pre
  (h: HS.mem)
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t) =
  let open U32 in
  let state' = B.as_seq h state in
  state_valid h ctx state /\
  (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  B.live h block_start /\
  B.disjoint (CB.as_mbuf ctx) block_start /\ B.disjoint state block_start /\
  HS.disjoint (B.frameOf block_start) (B.frameOf ctx'.head) /\
    
  match_start state' >= v ctx'.w_size /\
  strstart state' >= v ctx'.w_size /\
  insert state' <= strstart state' - v ctx'.w_size /\
  strstart state' - insert state' < v ctx'.window_size - min_match + 1 /\
  I32.v (B.get h block_start 0) >= -8454144)

private unfold let slide_window_buf_post'
  (h0 h1: HS.mem)
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t)
  (len: nat) =
  state_valid h0 ctx state /\
  (let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
  let s0 = B.as_seq h0 state in
  let s1 = B.as_seq h1 state in
  let w0 = B.as_seq h0 ctx'.window in
  let w1 = B.as_seq h1 ctx'.window in
  let w_size' = U32.v ctx'.w_size in
  match_length_unchange s0 s1 /\
  prev_match_unchange s0 s1 /\ prev_length_unchange s0 s1 /\
  lookahead_unchange s0 s1 /\ insert_unchange s0 s1 /\
  
  strstart s0 - U32.v ctx'.w_size == strstart s1 /\
  match_start s0 - U32.v ctx'.w_size == match_start s1 /\

  len <= U32.v ctx'.w_size /\
  I32.v (B.get h0 block_start 0) - U32.v ctx'.w_size == I32.v (B.get h1 block_start 0) /\
  Seq.slice w0 w_size' (w_size' + len) == Seq.slice w1 0 len)

let slide_window_buf_post
  (h0 h1: HS.mem)
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t)
  (len: nat) =
  slide_window_buf_post' h0 h1 ctx state block_start len /\
  B.modifies (
    B.loc_buffer block_start `B.loc_union`
    B.loc_buffer state `B.loc_union`
    B.loc_buffer (B.get h0 (CB.as_mbuf ctx) 0).window) h0 h1 /\
  state_valid h1 ctx state

unfold let slide_window_post
  (h0: HS.mem) (more: U32.t) (h1: HS.mem)
  (ctx: lz77_context_p{context_valid h0 ctx})
  (state: lz77_state_t)
  (block_start: B.pointer I32.t) =
  let open U32 in
  let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
  let s0 = B.as_seq h0 state in
  let s1 = B.as_seq h1 state in
  slide_window_pre h0 ctx state block_start /\
  
  (strstart s0 < v ctx'.w_size ==> 
    v more == 2 * v ctx'.w_size - lookahead s0 - strstart s0 /\
    B.modifies B.loc_none h0 h1) /\
  (strstart s0 >= U32.v ctx'.w_size ==>
    v more == 2 * v ctx'.w_size - lookahead s0 - strstart s0 + v ctx'.w_size /\
    B.modifies (
      B.loc_buffer block_start `B.loc_union`
      B.loc_buffer state `B.loc_union`
      B.loc_buffer ctx'.window `B.loc_union`
      hash_loc_buffer h0 ctx) h0 h1 /\
    (let len = strstart s1 + lookahead s1 in
    slide_window_buf_post' h0 h1 ctx state block_start len /\
    len <= v ctx'.w_size /\
    hash_chain_valid h1 ctx (uint_to_t (strstart s1 - insert s1)) false /\
    state_valid h1 ctx state))
