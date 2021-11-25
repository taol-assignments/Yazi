module Yazi.LZ77

module Adler32 = Yazi.Adler32
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module CRC32 = Yazi.CRC32
module HS = FStar.HyperStack
module I32 = FStar.Int32
module LB = Lib.Buffer
module Math = FStar.Math.Lemmas
module S = Spec.LZ77
module SS = Spec.Stream
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Util = Yazi.Util

open LowStar.BufferOps
open FStar.Mul
open Lib.Seq
open Lib.Buffer
open Yazi.LZ77.State
open Yazi.Stream.Types
open Yazi.Stream.State

/// Declaration of the load functions. They simply copy 4 bytes or 8 bytes data
/// to the given pointer. The result depends on the machine endianness.
[@ (CPrologue "#ifdef _MSC_VER
#include <intrin.h>
#endif

#ifndef __GNUC__
#include <string.h>
#define load32(dst, buf) memcpy(dst, buf, sizeof(*dst))
#define load64(dst, buf) memcpy(dst, buf, sizeof(*dst))
#else
#define load32(dst, buf) __builtin_memcpy(dst, buf, sizeof(*dst))
#define load64(dst, buf) __builtin_memcpy(dst, buf, sizeof(*dst))
#endif

#if 0") (CEpilogue "#endif")]
assume val load32: dst: B.pointer U32.t -> buf: B.buffer U8.t -> ST.Stack unit
  (requires fun h -> B.live h dst /\ B.live h buf /\ B.length buf >= 4)
  (ensures fun h0 _ h1 ->
    let open FStar.Seq in
    B.modifies (B.loc_buffer dst) h0 h1 /\
    S.load_post_cond h1 4 buf (UInt.to_vec (U32.v (B.get h1 dst 0))))

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val load64: dst: B.pointer U64.t -> buf: B.buffer U8.t -> ST.Stack unit
  (requires fun h -> B.live h dst /\ B.live h buf /\ B.length buf >= 8)
  (ensures fun h0 _ h1 ->
    let open FStar.Seq in
    B.modifies (B.loc_buffer dst) h0 h1 /\
    S.load_post_cond h1 8 buf (UInt.to_vec (U64.v (B.get h1 dst 0))))

#push-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let hash_load32_aux (h: HS.mem) (dst: B.pointer U32.t) (buf: B.buffer U8.t): Lemma
  (requires
    B.live h buf /\ B.length buf >= 4 /\
    S.load_post_cond h 4 buf (UInt.to_vec (U32.v (B.get h dst 0))))
  (ensures (
    let open FStar.Seq in
    let w = B.as_seq h buf in
    let vec t = UInt.to_vec (U8.v t) in
    let d = UInt.to_vec (U32.v (B.get h dst 0)) in
    (Util.is_little_endian () <> 0uy ==>
      d == vec w.[3] @| vec w.[2] @| vec w.[1] @| vec w.[0]) /\
    (Util.is_little_endian () == 0uy ==> 
      d == vec w.[0] @| vec w.[1] @| vec w.[2] @| vec w.[3]))) =
  let open FStar.Seq in
  let w = B.as_seq h buf in
  let vec t = UInt.to_vec (U8.v t) in
  let k = UInt.to_vec (U32.v (B.get h dst 0)) in
  if Util.is_little_endian () <> 0uy then begin
    let d = vec w.[3] @| vec w.[2] @| vec w.[1] @| vec w.[0] in
    assert(equal k d)
  end else
    let d = vec w.[0] @| vec w.[1] @| vec w.[2] @| vec w.[3] in
    assert(equal k d)

[@CInline]
let hash (ctx: lz77_context_p) (state: Ghost.erased lz77_state_t) (i: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    let state' = B.as_seq h state in
    S.state_valid h ctx state /\
    U32.v i <= S.strstart state' + S.lookahead state' - S.min_match)
  (ensures fun h0 res h1 ->
    let i' = U32.v i in
    let ctx' = (CB.as_seq h0 ctx).[0] in
    let w = B.as_seq h0 ((CB.as_seq h0 ctx).[0]).window in
    let hv = S.hash (U16.v ctx'.h_bits) w.[i'] w.[i' + 1] w.[i' + 2] w.[i' + 3] in
    B.modifies B.loc_none h0 h1 /\ res == hv) =
  ST.push_frame ();
  let w = B.sub (CB.index ctx 0ul).window i 4ul in
  let bits = (CB.index ctx 0ul).h_bits in
  let k = B.alloca 0ul 1ul in
  load32 k w;

  hash_load32_aux (ST.get ()) k w;
  
  let k' = k.(0ul) `U32.mul_mod` 0x1E35A7BDul in
  ST.pop_frame ();
  k' `U32.shift_right` Cast.uint16_to_uint32 (32us `U16.sub` bits)
#pop-options

[@@ CMacro ]
let min_match = 4ul

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0 --z3refresh"
inline_for_extraction
let insert_hash (ctx: lz77_context_p) (state: lz77_state_t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let state' = B.as_seq h state in
    S.state_valid h ctx state /\
    S.insert state' > 0 /\
    U32.v i <= S.window_end state' - S.min_match /\
    U32.v i == S.hash_end state' /\
    S.hash_chain_valid h ctx state false)
  (ensures fun h0 _ h1 ->
    let s0 = B.as_seq h0 state in
    let s1 = B.as_seq h1 state in
    S.state_valid h0 ctx state /\
    B.modifies (
      S.hash_loc_buffer h0 ctx `B.loc_union`
      B.loc_buffer state) h0 h1 /\
    S.state_valid h1 ctx state /\
    LB.unchange_except h0 h1 state 6 /\
    S.insert s0 - 1 == S.insert s1 /\
    S.hash_chain_valid h1 ctx state false) =
  let open U32 in
  let head = (CB.index ctx 0ul).head in
  let prev = (CB.index ctx 0ul).prev in
  let w_mask = (CB.index ctx 0ul).w_mask in
  let h0 = ST.get () in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let h = hash ctx state i in
  
  S.window_index_upper_bound h0 ctx (v i);
  S.window_mask_aux (U16.v ctx'.w_bits) (v ctx'.w_size) (U16.v ctx'.w_mask) (v i);
  
  if CFlags.fastest then
    head.(h) <- Cast.uint32_to_uint16 i
  else begin
    UInt.logand_mask (v i) (U16.v ctx'.w_bits);
    prev.(i &^ Cast.uint16_to_uint32 w_mask) <- head.(h);
    head.(h) <- Cast.uint32_to_uint16 i
  end;
  decr_insert state

[@@ CInline ]
let rec do_init_input_hash
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (i lookahead: U32.t)
  (insert: Ghost.erased (UInt.uint_t 32)):
  ST.Stack unit
  (requires fun h ->
    S.do_init_input_hash_pre h ctx state i lookahead insert)
  (ensures fun h0 _ h1 -> S.do_init_input_hash_post h0 h1 ctx state)
  (decreases U32.v lookahead + insert) =
  let open U32 in
  insert_hash ctx state i;

  let insert = get_insert state in
  if (lookahead +^ insert <^ min_match) || (insert = 0ul) then
    ()
  else
    do_init_input_hash ctx state (i +^ 1ul) lookahead (U32.v insert)

let init_input_hash ctx state =
  let open U32 in
  let lookahead = get_lookahead state in
  let insert = get_insert state in
  if insert >^ 0ul && lookahead +^ insert >=^ min_match then
    do_init_input_hash ctx state (get_strstart state -^ insert) lookahead (v insert)
  else
    ()

inline_for_extraction let read_buf 
  (ss: stream_state_t)
  (block_data: Ghost.erased (Seq.seq U8.t))
  (window: B.buffer U8.t)
  (window_size: Ghost.erased U32.t)
  (next_in: input_buffer)
  (from size: U32.t)
  (wrap: wrap_t):
  ST.Stack (U32.t & Ghost.erased (Seq.seq U8.t))
  (requires fun h ->
    SS.read_buf_pre h ss block_data window next_in window_size from size wrap)
  (ensures fun h0 res h1 ->
    SS.read_buf_post h0 res h1 ss block_data window next_in window_size from size wrap) =
  let open U32 in
  let h0 = ST.get() in
  let avail_in = get_avail_in ss in
  let len = if avail_in >^ size then
    size
  else
    avail_in
  in
  let next_in' = !*next_in in
  let ulen = Ghost.hide (Seq.length block_data) in
    
  B.blit (CB.cast next_in') 0ul window from len;
  let h1 = ST.get () in
  let buf' = CB.sub next_in' 0ul (Ghost.hide len) in
  if wrap = 1l then
    set_adler ss (Adler32.adler32 #ulen (Ghost.reveal block_data) (get_adler ss) buf' len)
  else if CFlags.gzip then
    if wrap = 2l then
      set_adler ss (CRC32.crc32 block_data (get_adler ss) buf' len)
    else
      ()
  else
    ();
  next_in *= (CB.sub next_in' len (avail_in -^ len));
  set_avail_in ss (avail_in -^ len);
  set_total_in ss (U32.add_underspec (get_total_in ss) len);

  let h1 = ST.get () in
  let w0 = Ghost.hide (B.as_seq h0 window) in
  let w1 = Ghost.hide (B.as_seq h1 window) in
  let block_data' = Ghost.hide (Seq.append block_data (CB.as_seq h1 buf')) in
  let total_in = Ghost.hide (Seq.length block_data + v len)in
  let w_len = Ghost.hide (v from + v len) in
  assert(forall (i: nat{i < v from}).
    let _1 = Seq.lemma_index_slice w0 0 (v from) i in
    let _2 = Seq.lemma_index_slice w1 0 (v from) i in
    (Seq.slice w0 0 (v from)).[i] == w0.[i] /\
    (Seq.slice w1 0 (v from)).[i] == w1.[i] /\
    (Seq.slice w0 0 (v from)).[i] == (Seq.slice w1 0 (v from)).[i]);
  assert(forall (i: nat). i < v from ==> w0.[i] == w1.[i]);

  assert(forall (i: nat{v from < i /\ i < v from + v len}).
    w1.[i] == block_data'.[total_in - w_len + i]);
  
  (len, block_data')

inline_for_extraction
let slide_index (buf: B.buffer U16.t) (offset i: U32.t):
  ST.Stack unit
  (requires fun h -> B.live h buf /\ U32.v i < B.length buf)
  (ensures fun h0 _ h1 ->
    let open U32 in
    let value = U16.v (B.as_seq h0 buf).[v i] in
    let value' = U16.v (B.as_seq h1 buf).[v i] in
    (value > v offset ==> value' = value - v offset) /\
    (value <= v offset ==> value' = 0) /\
    B.modifies (B.loc_buffer buf) h0 h1 /\
    LB.unchange_except h0 h1 buf (v i)) =
  let open U32 in
  let h0 = ST.get () in
  let value = buf.(i) in
  [@inline_let] let value' = Cast.uint16_to_uint32 value in
  [@inline_let] let value'' =
    Cast.uint32_to_uint16 (if value' >^ offset then value' -^ offset else 0ul)
  in
  buf.(i) <- value''

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0 --z3seed 25 --z3refresh"
[@@ CInline ]
let rec slide_head
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (h_size: Ghost.erased U32.t)
  (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    S.state_valid h ctx state /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    U32.v i <= U32.v ctx'.h_size /\
    U32.v h_size == U32.v ctx'.h_size /\
    S.sub_head_valid h ctx state (fun j -> j >= U32.v i /\ j < U32.v ctx'.h_size) false /\
    S.sub_head_valid h ctx state (fun j -> j < U32.v i) true))
  (ensures fun h0 _ h1 ->
    let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    B.modifies (B.loc_buffer ctx'.head) h0 h1 /\
    S.state_valid h1 ctx state /\
    S.head_valid h1 ctx state true)
  (decreases U32.v h_size - U32.v i) =
  let open U32 in
  let h0 = ST.get () in
  let head = (CB.index ctx 0ul).head in
  let w_size = (CB.index ctx 0ul).w_size in
  if i <^ (CB.index ctx 0ul).h_size then begin
    slide_index head w_size i;

    let h1 = ST.get () in
    let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
    assert(S.state_valid h1 ctx state);
    assert(forall (i: nat). {:pattern (B.as_seq h1 (B.gsub ctx'.window ctx'.w_size ctx'.w_size)).[i]}
      i < v ctx'.w_size ==>
        (B.as_seq h1 (B.gsub ctx'.window ctx'.w_size ctx'.w_size)).[i] ==
        (B.as_seq h1 ctx'.window).[i + v ctx'.w_size]);
    assert(S.head_index_valid #h1 #ctx state true (v i));

    slide_head ctx state h_size (i +^ 1ul)
  end else
    ()

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0 --z3seed 25 --z3refresh"
[@ (CPrologue "#ifndef FASTEST")
   (CEpilogue "#endif")
   CInline]
let rec slide_prev
  (ctx: lz77_context_p) (state: lz77_state_t) (w_size: Ghost.erased U32.t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    S.state_valid h ctx state /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    CFlags.fastest == false /\
    U32.v i <= U32.v ctx'.w_size /\
    U32.v w_size == U32.v ctx'.w_size /\
    S.sub_prev_valid h ctx state (fun j -> v i <= j /\ j < v w_size) false /\
    S.sub_prev_valid h ctx state (fun j -> j < v i) true))
  (ensures fun h0 _ h1 ->
    let open U32 in
    S.state_valid h1 ctx state /\
    B.modifies (B.loc_buffer (B.get h0 (CB.as_mbuf ctx) 0).prev) h0 h1 /\
    S.prev_valid h1 ctx state true)
  (decreases U32.v w_size - U32.v i) =
  let open U32 in
  let prev = (CB.index ctx 0ul).prev in
  let w_size' = (CB.index ctx 0ul).w_size in
  if i <^ w_size' then begin
    slide_index prev w_size' i;
    slide_prev ctx state w_size (i +^ 1ul)
  end else
    ()

let slide_hash ctx state =
  ST.push_frame ();
  let open U32 in
  let head = (CB.index ctx 0ul).head in
  let w_size = (CB.index ctx 0ul).w_size in
  let h_size = (CB.index ctx 0ul).h_size in
  let h_range = get_strstart state -^ get_insert state in
  if h_range >^ w_size then
    if CFlags.fastest then
      slide_head ctx state h_size 0ul
    else begin
      slide_head ctx state h_size 0ul;
      slide_prev ctx state w_size 0ul
    end
  else begin
    B.fill (CB.index ctx 0ul).head 0us h_size;
    let h1 = ST.get () in
    assert(Seq.equal (Seq.slice (B.as_seq h1 head) 0 (v h_size)) (B.as_seq h1 head));
    assert(forall (i: nat). i < v h_size ==> U16.v (B.as_seq h1 head).[i] == 0)
  end;
  ST.pop_frame ()

[@@ CInline ]
inline_for_extraction
let slide_window_buf
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t)
  (block_data: Ghost.erased (Seq.seq U8.t)):
  ST.Stack unit
  (requires fun h ->
    S.slide_window_pre h ctx state block_start block_data /\
    S.strstart (B.as_seq h state) >= U32.v (B.get h (CB.as_mbuf ctx) 0).w_size)
  (ensures fun h0 _ h1 -> S.slide_window_buf_post h0 h1 ctx state block_start block_data) =
  let open U32 in
  let w_size = (CB.index ctx 0ul).w_size in
  let window = (CB.index ctx 0ul).window in
  let w_bits = Ghost.hide (CB.index ctx 0ul).w_bits in
  
  let left = B.sub window 0ul w_size in
  let right = B.sub window w_size w_size in
  let h0 = ST.get () in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let w0 = Ghost.hide (B.as_seq h0 ctx'.window) in
  
  let len = get_lookahead state +^ get_strstart state -^ w_size in
  B.blit right 0ul left 0ul len;

  set_match_start (U16.v w_bits) (v w_size) state ((get_match_start state) -^ w_size);
  set_strstart (U16.v w_bits) (v w_size) state ((get_strstart state) -^ w_size);

  if get_insert state >^ get_strstart state then
    set_insert state (get_strstart state)
  else
    ();
  block_start *= I32.sub (!*block_start) (Cast.uint32_to_int32 w_size);
  let h1 = ST.get () in
  let w1 = Ghost.hide (B.as_seq h1 ctx'.window) in
  let w_end0 = Ghost.hide (S.window_end (B.as_seq h0 state)) in
  let w_end1 = Ghost.hide (S.window_end (B.as_seq h1 state)) in
  assert(forall (i: nat{i < U32.v len}).
    (B.as_seq h0 (B.gsub ctx'.window ctx'.w_size len)).[i] == w0.[i + v w_size] /\
    (B.as_seq h1 (B.gsub ctx'.window 0ul len)).[i] ==
    (B.as_seq h0 (B.gsub ctx'.window ctx'.w_size len)).[i] /\
    (B.as_seq h1 (B.gsub ctx'.window 0ul len)).[i] == w1.[i]);
  assert(forall i. {:pattern (w1.[i])} i < v len ==>
    w0.[i + v w_size] == w1.[i] /\
    w0.[i + v w_size] == block_data.[Seq.length block_data - w_end1 + i]);
  assert(forall i.{:pattern (block_data.[Seq.length block_data - w_end1 + i])} i < v len ==>
    w1.[i] == block_data.[Seq.length block_data - w_end1 + i]);
  assert(forall i. {:pattern (w1.[i])} i < v len ==>
    (B.as_seq h0 (B.gsub window w_size w_size)).[i] == w1.[i])

inline_for_extraction
let min_lookahead (ctx: lz77_context_p):
  ST.Stack U32.t
  (requires fun h -> S.context_valid h ctx)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res = S.min_lookahead (B.get h1 (CB.as_mbuf ctx) 0)) =
  if (CB.index ctx 0ul).w_bits = 8us then 128ul else 258ul

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0 --z3seed 1"
[@@ CInline ]
inline_for_extraction
let slide_window
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t)
  (block_data: Ghost.erased (Seq.seq U8.t)):
  ST.Stack U32.t
  (requires fun h ->
    S.slide_window_pre h ctx state block_start block_data /\
    S.hash_chain_valid h ctx state false)
  (ensures fun h0 more h1 -> S.slide_window_post h0 more h1 ctx state block_start block_data) =
  let open U32 in
  let strstart = get_strstart state in
  let w_size = (CB.index ctx 0ul).w_size in
  let window_size = (CB.index ctx 0ul).window_size in
  let more = (CB.index ctx 0ul).window_size -^ get_lookahead state -^ strstart in
  if strstart >=^ window_size -^ min_lookahead ctx then begin
    slide_hash ctx state;
    slide_window_buf ctx state block_start block_data;
    more +^ w_size
  end else
    more

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0 --z3seed 7 --z3refresh"
[@@ CInline ]
let rec do_fill_window
  (ss:stream_state_t)
  (ctx: lz77_context_p)
  (ls: lz77_state_t)
  (next_in: input_buffer)
  (wrap: wrap_t)
  (avail_in: Ghost.erased (UInt.uint_t 32))
  (block_data: Ghost.erased (Seq.seq U8.t)):
  ST.Stack (Ghost.erased (Seq.seq U8.t))
  (requires fun h -> S.do_fill_window_pre h ss ctx ls next_in wrap avail_in block_data)
  (ensures fun h0 res h1 ->
    S.do_fill_window_post h0 res h1 ss ctx ls next_in wrap avail_in block_data)
  (decreases avail_in) =
    let open U32 in
    let h0 = ST.get () in
    let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
    let w_bits = Ghost.hide (U16.v ctx'.w_bits) in
    let w_size = Ghost.hide (v ctx'.w_size) in
    
    let window = (CB.index ctx 0ul).window in
    let window_size = (CB.index ctx 0ul).window_size in
    let lookahead = get_lookahead ls in
    let strstart = get_strstart ls in
    
    let w_end = strstart +^ lookahead in
    
    [@inline_let] let more = window_size -^ w_end in

    let (len, block_data') =
      read_buf ss block_data window window_size next_in w_end more wrap
    in
    
    set_lookahead w_bits w_size ls (lookahead +^ len);
    init_input_hash ctx ls;

    let lookahead' = get_lookahead ls in
    let avail_in' = get_avail_in ss in
    let ml = min_lookahead ctx in

    if lookahead' <^ ml && avail_in' >^ 0ul then
      do_fill_window ss ctx ls next_in wrap (U32.v avail_in') block_data'
    else
      block_data'

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0 --z3seed 13 --z3refresh"
let fill_window ss ctx ls next_in wrap block_start block_data =
  let h0 = ST.get () in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let ls0 = Ghost.hide (B.as_seq h0 ls) in
  let open U32 in

  let avail_in = get_avail_in ss in
  if avail_in >^ 0ul then begin
    let more = slide_window ctx ls block_start block_data in
    do_fill_window ss ctx ls next_in wrap (v avail_in) block_data
  end else
    block_data

let builtin_count_zero_32_pre (a: U32.t) =
  (CFlags.__gnuc__ \/ CFlags.__compcert__) /\ U32.v a <> 0

let builtin_count_zero_64_pre (a: U64.t) =
  (CFlags.__gnuc__ \/ CFlags.__compcert__) /\ U64.v a <> 0
  
/// Declaration of the gcc builtin ctz/clz. Zero as the input argument is a undifined
/// behavior.
[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val __builtin_ctz: a: U32.t -> Pure I32.t
  (requires builtin_count_zero_32_pre a)
  (ensures fun res -> S.ctz (UInt.to_vec (U32.v a)) == I32.v res)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val __builtin_ctzll: a: U64.t -> Pure I32.t
  (requires builtin_count_zero_64_pre a)
  (ensures fun res -> S.ctz (UInt.to_vec (U64.v a)) == I32.v res)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val __builtin_clz: a: U32.t -> Pure I32.t
  (requires builtin_count_zero_32_pre a)
  (ensures fun res -> S.clz (UInt.to_vec (U32.v a)) == I32.v res)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val __builtin_clzll: a: U64.t -> Pure I32.t
  (requires builtin_count_zero_64_pre a)
  (ensures fun res -> S.clz (UInt.to_vec (U64.v a)) == I32.v res)

let bit_scan_32_pre (h: HS.mem) (index: B.pointer U32.t) =
  CFlags._msc_ver /\ B.live h index

let bit_scan_32_post
  (h0: HS.mem) (res: U8.t) (h1: HS.mem)
  (index: B.pointer U32.t) (mask: U32.t) (forward: bool) =
  (U8.v res == 0 <==> U32.v mask == 0 /\ B.modifies B.loc_none h0 h1) /\
  (U8.v res <> 0 ==>
    B.modifies (B.loc_buffer index) h0 h1 /\
    (forward ==> S.ctz (UInt.to_vec (U32.v mask)) == U32.v (B.get h1 index 0)) /\
    (forward == false ==> S.clz (UInt.to_vec (U32.v mask)) == U32.v (B.get h1 index 0)))

let bit_scan_64_pre (h: HS.mem) (index: B.pointer U32.t) =
  CFlags._msc_ver /\ (CFlags._m_arm64 \/ CFlags._m_x64) /\ B.live h index

let bit_scan_64_post
  (h0: HS.mem) (res: U8.t) (h1: HS.mem)
  (index: B.pointer U32.t) (mask: U64.t) (forward: bool) =
  (U8.v res == 0 <==> U64.v mask == 0 /\ B.modifies B.loc_none h0 h1) /\
  (U8.v res <> 0 ==>
    B.modifies (B.loc_buffer index) h0 h1 /\
    (forward ==> S.ctz (UInt.to_vec (U64.v mask)) == U32.v (B.get h1 index 0)) /\
    (forward == false ==> S.clz (UInt.to_vec (U64.v mask)) == U32.v (B.get h1 index 0)))

/// Declaration of the MSVC bit scan functions.
[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val _BitScanForward: index: B.pointer U32.t -> mask: U32.t -> ST.Stack U8.t
  (requires fun h -> bit_scan_32_pre h index)
  (ensures fun h0 res h1 -> bit_scan_32_post h0 res h1 index mask true)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val _BitScanForward64: index: B.pointer U32.t -> mask: U64.t -> ST.Stack U8.t
  (requires fun h -> bit_scan_64_pre h index)
  (ensures fun h0 res h1 -> bit_scan_64_post h0 res h1 index mask true)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val _BitScanReverse: index: B.pointer U32.t -> mask: U32.t -> ST.Stack U8.t
  (requires fun h -> bit_scan_32_pre h index)
  (ensures fun h0 res h1 -> bit_scan_32_post h0 res h1 index mask false)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
assume val _BitScanReverse64: index: B.pointer U32.t -> mask: U64.t -> ST.Stack U8.t
  (requires fun h -> bit_scan_64_pre h index)
  (ensures fun h0 res h1 -> bit_scan_64_post h0 res h1 index mask false)

let count_zero_32_pre = CFlags.__gnuc__ \/ CFlags.__compcert__ \/ CFlags._msc_ver

let count_zero_64_pre =
  CFlags.__gnuc__ \/ CFlags.__compcert__ \/
  (CFlags._msc_ver /\ (CFlags._m_arm64 \/ CFlags._m_x64))

let count_zero_32_post (h0: HS.mem) (res: U32.t) (h1: HS.mem) (a: U32.t) (forward: bool) =
  B.modifies B.loc_none h0 h1 /\
  (forward ==> U32.v res == S.ctz (UInt.to_vec (U32.v a))) /\
  (forward == false ==> U32.v res == S.clz (UInt.to_vec (U32.v a)))

unfold let count_zero_64_post (h0: HS.mem) (res: U32.t) (h1: HS.mem) (a: U64.t) (forward: bool) =
  B.modifies B.loc_none h0 h1 /\
  (forward ==> U32.v res == S.ctz (UInt.to_vec (U64.v a))) /\
  (forward == false ==> U32.v res == S.clz (UInt.to_vec (U64.v a)))

inline_for_extraction
let ctz (a: U32.t): ST.Stack U32.t
  (requires fun _ -> count_zero_32_pre)
  (ensures fun h0 res h1 -> count_zero_32_post h0 res h1 a true) =
  if CFlags.__gnuc__ then
    if a `U32.eq` 0ul then 32ul else Cast.int32_to_uint32 (__builtin_ctz a)
  else if CFlags.__compcert__ then
    if a `U32.eq` 0ul then 32ul else Cast.int32_to_uint32 (__builtin_ctz a)
  else begin
    ST.push_frame ();
    let index = B.alloca 0ul 1ul in
    let res = _BitScanForward index a in
    let cres = index.(0ul) in
    ST.pop_frame ();
    if res `U8.eq` 0uy then 32ul else cres
  end

inline_for_extraction
let clz (a: U32.t): ST.Stack U32.t
  (requires fun _ -> count_zero_32_pre)
  (ensures fun h0 res h1 -> count_zero_32_post h0 res h1 a false) =
  if CFlags.__gnuc__ then
    if a `U32.eq` 0ul then 32ul else Cast.int32_to_uint32 (__builtin_clz a)
  else if CFlags.__compcert__ then
    if a `U32.eq` 0ul then 32ul else Cast.int32_to_uint32 (__builtin_clz a)
  else begin
    ST.push_frame ();
    let index = B.alloca 0ul 1ul in
    let res = _BitScanReverse index a in
    let cres = index.(0ul) in
    ST.pop_frame ();
    if res `U8.eq` 0uy then 32ul else cres
  end

inline_for_extraction
let ctzll (a: U64.t): ST.Stack U32.t
  (requires fun _ -> count_zero_64_pre)
  (ensures fun h0 res h1 -> count_zero_64_post h0 res h1 a true) =
  if CFlags.__gnuc__ then
    if a `U64.eq` 0uL then 64ul else Cast.int32_to_uint32 (__builtin_ctzll a)
  else if CFlags.__compcert__ then
    if a `U64.eq` 0uL then 64ul else Cast.int32_to_uint32 (__builtin_ctzll a)
  else begin
    ST.push_frame ();
    let index = B.alloca 0ul 1ul in
    let res = _BitScanForward64 index a in
    let cres = index.(0ul) in
    ST.pop_frame ();
    if res `U8.eq` 0uy then 64ul else cres
  end

inline_for_extraction
let clzll (a: U64.t): ST.Stack U32.t
  (requires fun _ -> count_zero_64_pre)
  (ensures fun h0 res h1 -> count_zero_64_post h0 res h1 a false) =
  if CFlags.__gnuc__ then
    if a `U64.eq` 0uL then 64ul else Cast.int32_to_uint32 (__builtin_clzll a)
  else if CFlags.__compcert__ then
    if a `U64.eq` 0uL then 64ul else Cast.int32_to_uint32 (__builtin_clzll a)
  else begin
    ST.push_frame ();
    let index = B.alloca 0ul 1ul in
    let res = _BitScanReverse64 index a in
    let cres = index.(0ul) in
    ST.pop_frame ();
    if res `U8.eq` 0uy then 64ul else cres
  end

#push-options "--z3refresh --z3rlimit 1024 --fuel 0 --ifuel 0"
let count_zero_compare_pre (n: nat{n == 4 \/ n == 8}) (h: HS.mem) (s m: B.buffer U8.t) =
  B.live h s /\ B.live h m /\ B.length s >= n /\ B.length m >= n /\
  (n == 4 ==> count_zero_32_pre) /\
  (n == 8 ==> count_zero_64_pre)


let count_zero_compare_post
  (n: nat{n == 4 \/ n == 8}) (h0: HS.mem) (res: U32.t) (h1: HS.mem) (s m: B.buffer U8.t) =
  let s = B.as_seq h1 s in
  let m = B.as_seq h1 m in
  B.modifies B.loc_none h0 h1 /\
  Seq.length s >= n /\ Seq.length m >= n /\
  U32.v res <= n /\
  (forall i. i < U32.v res ==> s.[i] == m.[i]) /\
  (U32.v res < n ==> s.[U32.v res] <> m.[U32.v res])

inline_for_extraction
let count_zero_compare_4 (s m: B.buffer U8.t): ST.Stack U32.t
  (requires fun h -> count_zero_compare_pre 4 h s m)
  (ensures fun h0 res h1 -> count_zero_compare_post 4 h0 res h1 s m) =
  ST.push_frame ();
  let s' = B.alloca 0ul 1ul in
  let m' = B.alloca 0ul 1ul in
  load32 s' s;
  load32 m' m;
  let x = s'.(0ul) `U32.logxor` m'.(0ul) in
  let res = if Util.is_little_endian () <> 0uy then ctz x else clz x in
  
  let h = ST.get () in
  let s'' = Ghost.hide (U32.v (B.get h s' 0)) in
  let m'' = Ghost.hide (U32.v (B.get h m' 0)) in
  Classical.forall_intro (Classical.move_requires
    (S.lemma_load_xor_equal #32 h s m s'' m'' (U32.v x) (U32.v res)));
  if res `U32.lt` 32ul then
    S.lemma_load_xor_not_equal #32 h s m s'' m'' (U32.v x) (U32.v res);

  ST.pop_frame ();
  res `U32.div` 8ul

#push-options "--z3seed 112"
inline_for_extraction
let count_zero_compare_8 (s m: B.buffer U8.t): ST.Stack U32.t
  (requires fun h -> count_zero_compare_pre 8 h s m)
  (ensures fun h0 res h1 -> count_zero_compare_post 8 h0 res h1 s m) =
  ST.push_frame ();
  let s' = B.alloca 0uL 1ul in
  let m' = B.alloca 0uL 1ul in
  load64 s' s;
  load64 m' m;
  let x = s'.(0ul) `U64.logxor` m'.(0ul) in
  let res = if Util.is_little_endian () <> 0uy then ctzll x else clzll x in
  
  let h = ST.get () in
  let s'' = Ghost.hide (U64.v (B.get h s' 0)) in
  let m'' = Ghost.hide (U64.v (B.get h m' 0)) in
  Classical.forall_intro (Classical.move_requires
    (S.lemma_load_xor_equal #64 h s m s'' m'' (U64.v x) (U32.v res)));
  if res `U32.lt` 64ul then
    S.lemma_load_xor_not_equal #64 h s m s'' m'' (U64.v x) (U32.v res);

  ST.pop_frame ();
  res `U32.div` 8ul
#pop-options

let naive_compare_pre (n: nat{n == 4 \/ n == 8}) (h: HS.mem) (s m: B.buffer U8.t) =
  B.live h s /\ B.live h m /\  B.length s >= n /\ B.length m >= n

let naive_compare_post
  (n: nat{n == 4 \/ n == 8}) (h0: HS.mem) (res: U32.t) (h1: HS.mem) (s m: B.buffer U8.t) =
  let s = B.as_seq h1 s in
  let m = B.as_seq h1 m in
  B.modifies B.loc_none h0 h1 /\
  U32.v res <= n /\ n <= Seq.length s /\ n <= Seq.length m /\
  (forall i. i < U32.v res ==> s.[i] == m.[i]) /\
  (U32.v res < n ==> s.[U32.v res] <> m.[U32.v res])

inline_for_extraction
let naive_compare_4 (s m: B.buffer U8.t): ST.Stack U32.t
  (requires fun h -> naive_compare_pre 4 h s m)
  (ensures fun h0 res h1 -> naive_compare_post 4 h0 res h1 s m) =
  if s.(0ul) <> m.(0ul) then
    0ul
  else if s.(1ul) <> m.(1ul) then
    1ul
  else if s.(2ul) <> m.(2ul) then
    2ul
  else if s.(3ul) <> m.(3ul) then
    3ul
  else
    4ul

inline_for_extraction
let naive_compare_8 (s m: B.buffer U8.t): ST.Stack U32.t
  (requires fun h -> naive_compare_pre 8 h s m)
  (ensures fun h0 res h1 -> naive_compare_post 8 h0 res h1 s m) =
  if s.(0ul) <> m.(0ul) then
    0ul
  else if s.(1ul) <> m.(1ul) then
    1ul
  else if s.(2ul) <> m.(2ul) then
    2ul
  else if s.(3ul) <> m.(3ul) then
    3ul
  else if s.(4ul) <> m.(4ul) then
    4ul
  else if s.(5ul) <> m.(5ul) then
    5ul
  else if s.(6ul) <> m.(6ul) then
    6ul
  else if s.(7ul) <> m.(7ul) then
    7ul
  else
    8ul

inline_for_extraction
let string_match (s m: B.buffer U8.t) (len i: U32.t): ST.Stack U32.t
  (requires fun h -> S.ctz_compare_pre h len s m i)
  (ensures fun h0 res h1 -> S.ctz_compare_post h0 res h1 len s m i) =
  let s' = B.sub s i len in
  let m' = B.sub m i len in
  let h = ST.get () in
  assert(forall j. U32.v i <= j /\ j < U32.v i + U32.v len ==>
    (B.as_seq h s).[j] == (B.as_seq h s').[j - U32.v i]);
  assert(forall j. U32.v i <= j /\ j < U32.v i + U32.v len ==>
    (B.as_seq h s).[j] == (B.as_seq h s').[j - U32.v i]);

  if CFlags.__gnuc__ then
    if len = 4ul then
      count_zero_compare_4 s' m'
    else
      count_zero_compare_8 s' m'
  else if CFlags.__compcert__ then
    if len = 4ul then
      count_zero_compare_4 s' m'
    else
      count_zero_compare_8 s' m'
  else if CFlags._msc_ver then
    if len = 4ul then
      count_zero_compare_4 s' m'
    else if CFlags._m_arm64 then
      count_zero_compare_8 s' m'
    else if CFlags._m_x64 then
      count_zero_compare_8 s' m'
    else begin
      let res = count_zero_compare_4 s' m' in
      if res = 4ul then begin
        let s'' = B.sub s' 4ul 4ul in
        let m'' = B.sub m' 4ul 4ul in
        assert(forall j. 4 <= j /\ j < 8 ==>
          (B.as_seq h s').[j] == (B.as_seq h s'').[j - 4]);
        assert(forall j. 4 <= j /\ j < 8 ==>
          (B.as_seq h s').[j] == (B.as_seq h s'').[j - 4]);
        assert(forall j. j < 4 ==> (B.as_seq h s').[j] == (B.as_seq h m').[j]);
        let res' = count_zero_compare_4 s'' m'' in

        assert(forall j. j < 4 + U32.v res' ==>
          (B.as_seq h s').[j] == (B.as_seq h m').[j]);

        4ul `U32.add` res'
      end else
        res
    end
  else
    if len = 4ul then
      naive_compare_4 s' m'
    else
      naive_compare_8 s' m'
#pop-options

[@ CInline ]
let rec match_iteration_1 (s m: B.buffer U8.t) (i tail: U32.t):
  ST.Stack U32.t
  (requires fun h -> S.string_compare_ite_pre h s m i tail /\ U32.v tail < 4)
  (ensures fun h0 len h1 -> S.string_compare_ite_post h0 len h1 s m i tail) =
  let open U32 in
  if i <^ tail then
    if s.(i) = m.(i) then
      match_iteration_1 s m (i +^ 1ul) tail
    else
      i
  else
    i

[@ CInline ]
let rec match_iteration_8 (s m: B.buffer U8.t) (i tail: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    S.string_compare_ite_pre h s m i tail /\
    (U32.v tail - U32.v i) % 8 == 0)
  (ensures fun h0 len h1 -> S.string_compare_ite_post h0 len h1 s m i tail)
  (decreases (U32.v tail - U32.v i)) =
  let open U32 in
  if U32.lt i tail then begin
    let len = string_match s m 8ul i in
    if len = 8ul then
      match_iteration_8 s m (i +^ len) tail
    else
      i +^ len
  end else
    i

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
[@ CInline ]
let match_iteration (s m: B.buffer U8.t) (tail: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    B.live h s /\ B.live h m /\
    B.length s <= B.length m /\
    U32.v tail <= B.length s /\
    U32.v tail <= S.max_match)
  (ensures fun h0 len h1 ->
    let s' = B.as_seq h0 s in
    let m' = B.as_seq h0 m in
    let len' = U32.v len in
    let tail' = U32.v tail in
    B.modifies B.loc_none h0 h1 /\
    len' <= tail' /\
    (len' < tail' ==> s'.[len'] <> m'.[len']) /\
    (forall (j: nat{j < len'}). s'.[j] == m'.[j])) =
  let open U32 in
  let r1 = tail %^ 4ul in
  let l1 = if r1 = 0ul then 0ul else match_iteration_1 s m 0ul r1 in
  let t4 = tail -^ r1 in
  if l1 = r1 && t4 >^ 0ul then
    let r4 = t4 %^ 8ul in
    if r4 = 0ul then
      match_iteration_8 s m l1 tail
    else
      let l4 = string_match s m 4ul l1 in
      if l4 = 4ul then begin
        match_iteration_8 s m (l1 +^ 4ul) tail
      end else
        l1 +^ l4
  else
    l1

[@ (CEpilogue "#ifdef __GNUC__
  #define Yazi_LZ77_fast_compare(s1, s2, len) __builtin_memcmp(s1, s2, (__SIZE_TYPE__)len)
#else
  #define Yazi_LZ77_fast_compare(s1, s2, len) memcmp(s1, s2, (size_t)len)
#endif")]
assume val fast_compare: 
    s1: B.buffer U8.t
  -> s2: B.buffer U8.t
  -> len: U32.t
  -> ST.Stack I32.t
  (requires fun h ->
    B.live h s1 /\ B.live h s2 /\
    B.length s1 >= U32.v len /\ B.length s2 >= U32.v len)
  (ensures fun h0 res h1 ->
    let s1' = B.as_seq h0 s1 in
    let s2' = B.as_seq h0 s2 in
    B.modifies B.loc_none h0 h1 /\
    (I32.v res == 0 <==> (forall (i: nat{i < U32.v len}). s1'.[i] == s2'.[i])))

unfold let slow_match_pre_cond
  (h: HS.mem)
  (ctx: lz77_context_p)
  (s: lz77_state_t)
  (scan_end limit fuel cur_match: U32.t) =
  let open U32 in
  let s' = B.as_seq h s in
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  CFlags.fastest == false /\
  S.longest_match_pre h ctx s cur_match /\
  v scan_end + S.min_match <= S.window_end s' /\
  S.strstart s' <= v scan_end /\
  (S.strstart s' >= v ctx'.w_size ==> v limit == S.strstart s' - v ctx'.w_size) /\
  (S.strstart s' < v ctx'.w_size ==> v limit == 0) /\
  v fuel >= 1

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0 --z3seed 13 --z3refresh"
[@ (CPrologue "#ifndef FASTEST")
   (CEpilogue "#endif")
   CInline]
let rec search_hash_chain
  (ctx: lz77_context_p) (s: lz77_state_t) (scan_end limit fuel i: U32.t):
  ST.Stack (U32.t & U32.t & bool)
  (requires fun h -> slow_match_pre_cond h ctx s scan_end limit fuel i)
  (ensures fun h0 res h1 ->
    let open U32 in
    let (cur_match, fuel', cont) = res in
    let w = B.as_seq h1 (B.get h1 (CB.as_mbuf ctx) 0).window in
    let strstart = S.strstart (B.as_seq h1 s) in
    let scan_end = U32.v scan_end in
    let i = U32.v i in
    B.modifies B.loc_none h0 h1 /\
    U32.v fuel' <= U32.v fuel /\
    (cont == true ==>
      v cur_match < strstart /\
      (forall (k: nat{k < S.min_match}). w.[v cur_match + k] == w.[strstart + k])))
  (decreases U32.v fuel) =
  let open U32 in
  let h0 = ST.get () in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let window = (CB.index ctx 0ul).window in
  let strstart = get_strstart s in
  let s1 = B.sub window strstart min_match in
  let s2 = B.sub window i min_match in
  let e1 = B.sub window scan_end min_match in
  let e2 = B.sub window (scan_end -^ strstart +^ i) min_match in
  let c1 = fast_compare s1 s2 min_match in
  let c2 = fast_compare e1 e2 min_match in
  if c1 = 0l && c2 = 0l then begin
    let w = Ghost.hide (B.as_seq h0 window) in
    let d = Ghost.hide (v strstart - v i) in
    let s1' = Ghost.hide (B.as_seq h0 (B.gsub window strstart min_match)) in
    let s2' = Ghost.hide (B.as_seq h0 (B.gsub window i min_match)) in
    let e1' = Ghost.hide (B.as_seq h0 (B.gsub window scan_end min_match)) in
    let e2' = Ghost.hide (B.as_seq h0 (B.gsub window (scan_end -^ strstart +^ i) min_match)) in
    let strstart' = Ghost.hide (v strstart) in
    let scan_end' = Ghost.hide (v scan_end) in
    assert(forall (j: nat{j < S.min_match}).
      s1'.[j] == s2'.[j] /\
      s1'.[j] == w.[strstart' + j] /\
      s2'.[j] == w.[v i + j] /\
      e1'.[j] == e2'.[j] /\
      e1'.[j] == w.[scan_end' + j] /\
      e2'.[j] == w.[scan_end' - strstart' + v i + j]);
    assert(forall (j: nat{j < S.min_match}). w.[v i + j] == w.[strstart' + j]);
    (i, fuel, true)
  end else if fuel >^ 1ul then begin
    let prev = (CB.index ctx 0ul).prev in
    let w_mask = (CB.index ctx 0ul).w_mask in
    [@inline_let] let w_mask' = Cast.uint16_to_uint32 w_mask in
    UInt.logand_mask #32 (v i) (U16.v ctx'.w_bits);
    let i' = prev.(i &^ w_mask') in
    let i'' = Cast.uint16_to_uint32 i' in
    if i'' >^ limit then begin
      search_hash_chain ctx s scan_end limit (fuel -^ 1ul) i''
    end else
      (0ul, 0ul, false)
  end else
    (0ul, 0ul, false)

[@ (CPrologue "#ifndef FASTEST")
   (CEpilogue "#endif")
   CInline]
let rec do_longest_match_slow
  (ctx: lz77_context_p)
  (s: lz77_state_t)
  (nice_match scan_end limit fuel cur_match best_len: U32.t):
  ST.Stack (U32.t & U32.t)
  (requires fun h ->
    let open U32 in
    let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    let s' = B.as_seq h s in
    let w = B.as_seq h ctx'.window in
    slow_match_pre_cond h ctx s scan_end limit fuel cur_match /\
    v best_len < v nice_match /\
    (S.prev_length s' >= S.good_match s' ==>
      v fuel <= UInt.shift_right (S.max_fuel s') 2) /\
    (S.nice_match s' < S.lookahead s' ==> v nice_match == S.nice_match s') /\
    (S.nice_match s' >= S.lookahead s' ==> v nice_match == S.lookahead s') /\
    (v best_len > 0 ==>
      v best_len >= S.min_match /\
      v cur_match < S.strstart s' /\
      S.strstart s' + v best_len <= S.window_end s' /\
      (forall (i: nat{i < v best_len}). {:pattern (w.[v cur_match + i])}
        w.[v cur_match + i] == w.[S.strstart s' + i])))
  (ensures fun h0 res h1 ->
    let open U32 in
    let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    let s' = B.as_seq h1 s in
    let w = B.as_seq h1 ctx'.window in
    let (bl, cm) = res in
    B.modifies B.loc_none h0 h1 /\
    v bl >= v best_len /\
    (v bl >= S.min_match ==>
      v cm < S.strstart s' /\
      S.strstart s' + v bl <= S.window_end s' /\
      (forall (i: nat{i < v bl}). w.[v cm + i] == w.[S.strstart s' + i])))
  (decreases U32.v fuel) =
  let open U32 in
  let h = ST.get () in
  let (cm, cl, cont) = search_hash_chain ctx s scan_end limit fuel cur_match in
  if cont then begin
    let w_bits = (CB.index ctx 0ul).w_bits in
    let window = (CB.index ctx 0ul).window in
    let strstart = get_strstart s in
    let lookahead = get_lookahead s in
    let max_lookahead = if w_bits = 8us then 256ul else 258ul in
    let max_offset = 
      (if lookahead <^ max_lookahead then lookahead else max_lookahead) -^ min_match in
    let sbuf = B.sub window (strstart +^ min_match) (Ghost.hide max_offset) in
    let mbuf = B.sub window (cm +^ min_match) (Ghost.hide max_offset) in
    let l' = match_iteration sbuf mbuf max_offset in
    let l = min_match +^ l' in

    let h = ST.get () in
    let w = Ghost.hide (B.as_seq h window) in
    assert(forall (i: nat{S.min_match <= i /\ i < S.min_match + v l'}).
      (B.as_seq h sbuf).[i - S.min_match] == (B.as_seq h mbuf).[i - S.min_match] /\
      (B.as_seq h sbuf).[i - S.min_match] == w.[v strstart + i] /\
      (B.as_seq h mbuf).[i - S.min_match] == w.[v cm + i]);
    assert(forall (i:nat{i < v l}).
      {:pattern (w.[v cm + i]); (w.[v strstart + i])}
      w.[v cm + i] == w.[v strstart + i]);

    if l >^ best_len then
      if nice_match >^ l && cl >^ 1ul && cm >^ 0ul then
        do_longest_match_slow
          ctx s nice_match (strstart +^ l -^ 4ul) limit (cl -^ 1ul) cm l
      else
        (l, cm)
    else
      if cl >^ 1ul then
        do_longest_match_slow
          ctx s nice_match scan_end limit (cl -^ 1ul) cur_match best_len
      else
        (best_len, cur_match)
  end else
    (best_len, cur_match)

[@ (CPrologue "#ifdef FASTEST")
   (CEpilogue "#endif")
   CInline]
let do_longest_match_fast (ctx: lz77_context_p) (s: lz77_state_t) (cur_match: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    S.longest_match_pre h ctx s cur_match /\
    CFlags.fastest == true)
  (ensures fun h0 res h1 ->
    let open U32 in
    let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    let s' = B.as_seq h1 s in
    let w = B.as_seq h1 ctx'.window in
    B.modifies B.loc_none h0 h1 /\
    (v res >= S.min_match ==>
      S.strstart s' + v res <= S.window_end s' /\
      (forall (i: nat{i < v res}). w.[v cur_match + i] == w.[S.strstart s' + i]))) =
  let open U32 in
  let w_bits = (CB.index ctx 0ul).w_bits in
  let window = (CB.index ctx 0ul).window in
  let strstart = get_strstart s in
  let lookahead = get_lookahead s in
  
  let max_lookahead = if w_bits = 8us then 256ul else 258ul in
  let max_offset = if lookahead <^ max_lookahead then lookahead else max_lookahead in

  let sbuf = B.sub window strstart (Ghost.hide max_offset) in
  let mbuf = B.sub window cur_match (Ghost.hide max_offset) in

  let h = ST.get () in
  let w = Ghost.hide (B.as_seq h window) in
  
  let l = match_iteration sbuf mbuf max_offset in
  assert(forall (i: nat{i < v l}).
    (B.as_seq h sbuf).[i] == (B.as_seq h mbuf).[i] /\
    (B.as_seq h sbuf).[i] == w.[v strstart + i] /\
    (B.as_seq h mbuf).[i] == w.[v cur_match + i]);
  assert(forall (i:nat{i < v l}).
    {:pattern (w.[v cur_match + i]); (w.[v strstart + i])}
    w.[v cur_match + i] == w.[v strstart + i]);
  l

let longest_match ctx s cur_match =
  let open U32 in
  let strstart = get_strstart s in
  let prev_length = get_prev_length s in
  let w_size = (CB.index ctx 0ul).w_size in
  let limit = if strstart >^ w_size then strstart -^ w_size else 0ul in

  let h0 = ST.get () in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in

  if CFlags.fastest then
    let len = do_longest_match_fast ctx s cur_match in
    if len <=^ prev_length then
      min_match -^ 1ul
    else begin
      set_match_start (U16.v ctx'.w_bits) (v ctx'.w_size) s cur_match;
      len
    end
  else
    let nm = get_nice_match s in
    let lookahead = get_lookahead s in
    let nice_match = if nm <^ lookahead then nm else lookahead in
    let limit = if strstart >^ w_size then strstart -^ w_size else 0ul in
    let good_match = get_good_match s in
    let mcl = get_max_fuel s in
    let fuel = if prev_length >=^ good_match then mcl >>^ 2ul else mcl in
    let se1 = strstart +^ prev_length -^ (min_match -^ 1ul) in
    let se2 = strstart +^ lookahead -^ min_match in
    let scan_end = if se1 >^ se2 then se2 else se1 in
    if fuel >^ 0ul then
      let (bl, cm) = do_longest_match_slow
        ctx s nice_match scan_end
        limit fuel cur_match 0ul in
      if bl >^ prev_length then begin
        set_match_start (U16.v ctx'.w_bits) (v ctx'.w_size) s cm;
        bl
      end else
        min_match -^ 1ul
    else
      min_match -^ 1ul
