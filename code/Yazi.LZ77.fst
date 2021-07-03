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
module UInt = FStar.UInt

open LowStar.BufferOps
open FStar.Mul
open Lib.Seq
open Lib.Buffer
open Yazi.LZ77.State
open Yazi.Stream.Types
open Yazi.Stream.State

[@
  (CPrologue "#include <string.h>
static inline uint32_t lz77_hash(uint16_t h_bits, const unsigned char *buf) {
  uint32_t n;
  memcpy(&n, buf, sizeof(n));
  return (n * 0x1E35A7BD) >> (32 - h_bits);\n}")
  (CEpilogue "#define Yazi_LZ77_hash(ctx, i) lz77_hash((ctx)->h_bits, &((ctx)->window[i]))")]
assume val hash:
    ctx: lz77_context_p
  -> state: Ghost.erased lz77_state_t
  -> i: U32.t
  -> ST.Stack U32.t
  (requires fun h ->
    S.state_valid h ctx state /\
    (let state' = B.as_seq h state in
    U32.v i <= S.strstart state' + S.lookahead state' - S.min_match))
  (ensures fun h0 res h1 ->
    let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    let w = B.as_seq h0 ctx'.window in
    let i' = U32.v i in
    let hv = U32.v (S.hash (U16.v ctx'.h_bits) w.[i'] w.[i' + 1] w.[i' + 2] w.[i' + 3]) in
    B.modifies B.loc_none h0 h1 /\
    U32.v res == hv)

[@@ CMacro ]
let min_match = 4ul

[@@ CInline ]
inline_for_extraction
let clear_hash (ctx: lz77_context_p):
  ST.StackInline unit
  (requires fun h -> S.context_valid h ctx)
  (ensures fun h0 _ h1 ->
    S.context_valid h1 ctx /\
    B.modifies (B.loc_buffer (B.get h1 (CB.as_mbuf ctx) 0).head) h0 h1 /\
    S.hash_chain_valid h1 ctx 0ul false) =
  let head = (CB.index ctx 0ul).head in
  let h_size = (CB.index ctx 0ul).h_size in
  B.fill head 0us h_size

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0"
inline_for_extraction
let insert_hash (ctx: lz77_context_p) (state: Ghost.erased lz77_state_t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let state' = B.as_seq h state in
    S.state_valid h ctx state /\
    U32.v i <= S.strstart state' + S.lookahead state' - S.min_match /\
    S.hash_chain_valid h ctx i false)
  (ensures fun h0 _ h1 ->
    B.modifies (S.hash_loc_buffer h0 ctx) h0 h1 /\
    S.state_valid h1 ctx state /\
    S.hash_chain_valid h1 ctx (U32.add i 1ul) false) =
  let open U32 in
  let head = (CB.index ctx 0ul).head in
  let prev = (CB.index ctx 0ul).prev in
  let w_mask = (CB.index ctx 0ul).w_mask in
  let h0 = Ghost.hide (ST.get ()) in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let h = hash ctx state i in
  
  S.window_index_upper_bound h0 ctx (v i);
  S.window_mask_aux (U16.v ctx'.w_bits) (v ctx'.w_size) (U16.v ctx'.w_mask) (v i);
  
  if CFlags.fastest then begin
    head.(h) <- Cast.uint32_to_uint16 i
  end else begin
    UInt.logand_mask (v i) (U16.v ctx'.w_bits);
    prev.(i &^ Cast.uint16_to_uint32 w_mask) <- head.(h);
    head.(h) <- Cast.uint32_to_uint16 i
  end

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
  decr_insert state;

  let insert = get_insert state in
  if (lookahead +^ insert <^ min_match) || (insert = 0ul) then
    ()
  else
    do_init_input_hash ctx state (i +^ 1ul) lookahead (U32.v insert)

[@@ CInline ]
inline_for_extraction
let init_input_hash (ctx: lz77_context_p) (state: lz77_state_t):
  ST.Stack unit
  (requires fun h -> S.init_input_hash_pre h ctx state)
  (ensures fun h0 _ h1 -> S.init_input_hash_post h0 h1 ctx state) =
  let open U32 in
  let lookahead = get_lookahead state in
  let insert = get_insert state in
  if insert >^ 0ul && lookahead +^ insert >=^ min_match then
    do_init_input_hash ctx state (get_strstart state -^ insert) lookahead (v insert)
  else
    ()

[@@ CInline ]
let rec do_init_dict_hash (ctx: lz77_context_p) (state: lz77_state_t) (i h_end: U32.t):
  ST.Stack unit
  (requires fun h -> S.do_init_dict_hash_pre h ctx state i (U32.v h_end))
  (ensures fun h0 _ h1 -> S.do_init_dict_hash_post h0 h1 ctx state) =
  let open U32 in
  insert_hash ctx state i;
  if i +^ 1ul <^ h_end then
    do_init_dict_hash ctx state (i +^ 1ul) h_end
  else
    ()

let init_dict_hash ctx state =
  let open U32 in
  do_init_dict_hash ctx state
    (get_strstart state)
    (get_strstart state +^ get_lookahead state -^ (min_match -^ 1ul))

inline_for_extraction let read_buf 
  (ss: stream_state_t)
  (block_data: Ghost.erased (Seq.seq U8.t))
  (next_in: io_buffer)
  (buf: B.buffer U8.t)
  (size: U32.t)
  (wrap: wrap_t):
  ST.Stack (U32.t & Ghost.erased (B.buffer U8.t))
  (requires fun h -> SS.read_buf_pre h ss block_data next_in buf size wrap)
  (ensures fun h0 res h1 -> SS.read_buf_post h0 res h1 ss block_data next_in buf size wrap) =
  let open U32 in
  let avail_in = get_avail_in ss in
  let len = if avail_in >^ size then
    size
  else
    avail_in
  in
  let avail_in' = B.sub ss 0ul 1ul in
  let next_in' = !*next_in in
  let ulen = Ghost.hide (Seq.length block_data) in
    
  B.blit next_in' 0ul buf 0ul len;
  let buf' = B.sub next_in' 0ul (Ghost.hide len) in
  if wrap = 1l then
    set_adler ss (Adler32.adler32 #ulen (Ghost.reveal block_data) (get_adler ss) buf' len)
  else if CFlags.gzip then
    if wrap = 2l then
      set_adler ss (CRC32.crc32 block_data (get_adler ss) buf' len)
    else
      ()
  else
    ();
  next_in *= (B.sub next_in' len (avail_in -^ len));
  set_avail_in ss (avail_in -^ len);
  set_total_in ss (U32.add_underspec (get_total_in ss) len);
  (len, Ghost.hide buf')

let w_size_fit_u32 (w_size: U32.t{U32.v w_size < pow2 15}): Lemma
  (ensures 2 * U32.v w_size < pow2 32)
  [SMTPat (2 * U32.v w_size)] = 
  Math.pow2_double_mult 15

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0"
[@@ CInline ]
let rec slide_head (ctx: lz77_context_p) (h_size h_range: Ghost.erased U32.t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    S.context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    U32.v i <= U32.v ctx'.h_size /\
    U32.v h_size == U32.v ctx'.h_size /\
    hash_range_pre_cond ctx' h_range /\
    S.sub_head_valid h ctx h_range (fun j -> j >= U32.v i /\ j < U32.v ctx'.h_size) false /\
    S.sub_head_valid h ctx h_range (fun j -> j < U32.v i) true))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer (B.get h0 (CB.as_mbuf ctx) 0).head) h0 h1 /\
    S.head_valid h1 ctx h_range true)
  (decreases U32.v h_size - U32.v i) =
  let open U32 in
  let head = (CB.index ctx 0ul).head in
  let w_size = (CB.index ctx 0ul).w_size in
  if i <^ (CB.index ctx 0ul).h_size then begin
    let m = head.(i) in
    [@inline_let] let m' = Cast.uint16_to_uint32 m in
    head.(i) <- Cast.uint32_to_uint16 (if m' >=^ w_size then m' -^ w_size else 0ul);
    slide_head ctx h_size h_range (i +^ 1ul)
  end else
    ()

[@@ CInline ]
#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0 --z3seed 25"
let rec slide_prev (ctx: lz77_context_p) (w_size h_range: Ghost.erased U32.t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    S.context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    CFlags.fastest == false /\
    U32.v i <= U32.v ctx'.w_size /\
    U32.v w_size == U32.v ctx'.w_size /\
    hash_range_pre_cond ctx' h_range /\
    S.sub_prev_valid h ctx h_range (fun j -> v i <= j /\ j < v w_size) false /\
    S.sub_prev_valid h ctx h_range (fun j -> j < v i) true))
  (ensures fun h0 _ h1 ->
    let open U32 in
    S.context_valid h1 ctx /\
    B.modifies (B.loc_buffer (B.get h0 (CB.as_mbuf ctx) 0).prev) h0 h1 /\
    hash_range_pre_cond (B.get h1 (CB.as_mbuf ctx) 0) h_range /\
    S.prev_valid h1 ctx h_range true)
  (decreases U32.v w_size - U32.v i) =
  let open U32 in
  let prev = (CB.index ctx 0ul).prev in
  let w_size' = (CB.index ctx 0ul).w_size in
  if i <^ w_size' then begin
    let m = prev.(i) in
    [@inline_let] let m' = Cast.uint16_to_uint32 m in
    prev.(i) <- Cast.uint32_to_uint16 (if m' >=^ w_size' then m' -^ w_size' else 0ul);
    let h = Ghost.hide (ST.get ()) in
    assert(forall (j: nat{U32.v w_size <= j /\ j < U32.v h_range}).
      let ctx' = Ghost.hide (B.get h (CB.as_mbuf ctx) 0) in
      let window' = Ghost.hide (B.gsub ctx'.window w_size (h_range -^ w_size)) in
      let s0 = B.as_seq h ctx'.window in
      let s1 = B.as_seq h window' in
      s0.[j] == s1.[j - U32.v w_size]);
    slide_prev ctx w_size h_range (i +^ 1ul)
  end else
    ()

let slide_hash ctx h_range =
  ST.push_frame ();
  let open U32 in
  let w_size = (CB.index ctx 0ul).w_size in
  let h_size = (CB.index ctx 0ul).h_size in
  if CFlags.fastest then
    if h_range >^ w_size then begin
      slide_head ctx h_size h_range 0ul;
      let h = ST.get () in assert(S.head_valid h ctx h_range true)
    end else
      clear_hash ctx
  else
    if h_range >^ w_size then begin
      slide_head ctx h_size h_range 0ul;
      slide_prev ctx w_size h_range 0ul
    end else
      clear_hash ctx;
  ST.pop_frame ()

[@@ CInline ]
inline_for_extraction
let slide_window_buf
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t)
  (len: U32.t):
  ST.Stack unit
  (requires fun h ->
    S.slide_window_pre h ctx state block_start /\
    U32.v len <= U32.v (B.get h (CB.as_mbuf ctx) 0).w_size)
  (ensures fun h0 _ h1 ->
    S.slide_window_buf_post h0 h1 ctx state block_start (U32.v len)) =
  let open U32 in
  let w_size = (CB.index ctx 0ul).w_size in
  let w_size' = Ghost.hide (U32.v w_size) in
  let window = (CB.index ctx 0ul).window in
  let w_bits = Ghost.hide (CB.index ctx 0ul).w_bits in
  S.window_size_upper_bound (U16.v w_bits) (v w_size);
  let left = B.sub window 0ul w_size in
  let right = B.sub window w_size w_size in
  let h0 = Ghost.hide (ST.get ()) in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let w0 = Ghost.hide (B.as_seq h0 ctx'.window) in
  
  B.blit right 0ul left 0ul len;
  set_match_start (U16.v w_bits) (v w_size) state ((get_match_start state) -^ w_size);
  set_strstart (U16.v w_bits) (v w_size) state ((get_strstart state) -^ w_size);
  block_start *= I32.sub (!*block_start) (Cast.uint32_to_int32 w_size);
  let h1 = Ghost.hide (ST.get ()) in
  let w1 = Ghost.hide (B.as_seq h1 ctx'.window) in
  assert(forall (i: nat{i < U32.v len}).
    (B.as_seq h0 (B.gsub ctx'.window ctx'.w_size len)).[i] == w0.[i + w_size'] /\
    (B.as_seq h1 (B.gsub ctx'.window 0ul len)).[i] ==
    (B.as_seq h0 (B.gsub ctx'.window ctx'.w_size len)).[i] /\
    (B.as_seq h1 (B.gsub ctx'.window 0ul len)).[i] == w1.[i]);
  assert(forall (i: nat{i < U32.v len}). w0.[i + w_size'] == w1.[i])

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0"
[@@ CInline ]
inline_for_extraction
let slide_window
  (ctx: lz77_context_p)
  (state: lz77_state_t)
  (block_start: B.pointer I32.t):
  ST.StackInline U32.t
  (requires fun h ->
    let open U32 in
    let state' = B.as_seq h state in
    S.slide_window_pre h ctx state block_start /\
    S.hash_chain_valid h ctx (U32.uint_to_t (S.hash_end state')) false)
  (ensures fun h0 more h1 -> S.slide_window_post h0 more h1 ctx state block_start) =
  let open U32 in
  let h0 = Ghost.hide (ST.get ()) in
  let strstart = get_strstart state in
  let w_size = (CB.index ctx 0ul).w_size in
  let h_range = strstart -^ get_insert state in
  let window = Ghost.hide (CB.index ctx 0ul).window in
  let more = (CB.index ctx 0ul).window_size -^ get_lookahead state -^ strstart in
  if strstart >=^ w_size then begin
    slide_hash ctx h_range;
    slide_window_buf ctx state block_start (w_size -^ more);
    let h1 = Ghost.hide (ST.get ()) in
    LB.as_seq_gsub_eq h0 h1 window window
      w_size 0ul (w_size -^ more) (h_range -^ w_size +^ (min_match -^ 1ul));
    more +^ w_size
  end else
    more

inline_for_extraction
let min_lookahead (ctx: lz77_context_p):
  ST.Stack U32.t
  (requires fun h -> S.context_valid h ctx)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res = S.min_lookahead (B.get h1 (CB.as_mbuf ctx) 0)) =
  if (CB.index ctx 0ul).w_bits = 8us then 256ul else 258ul

#set-options "--z3rlimit 8192 --fuel 0 --ifuel 1 --z3seed 13"
[@@ CInline ]
let rec do_fill_window
  (ss:stream_state_t)
  (ctx: lz77_context_p)
  (ls: lz77_state_t)
  (next_in: io_buffer)
  (wrap: wrap_t)
  (avail_in: Ghost.erased (UInt.uint_t 32))
  (block_data: Ghost.erased (Seq.seq U8.t)):
  ST.Stack (Ghost.erased (Seq.seq U8.t))
  (requires fun h -> S.do_fill_window_pre h ss ctx ls next_in wrap avail_in block_data)
  (ensures fun h0 res h1 ->
    S.do_fill_window_post h0 res h1 ss ctx ls next_in wrap avail_in block_data)
  (decreases avail_in) =
    let open U32 in let open FStar.Seq in
    let h0 = Ghost.hide (ST.get ()) in
    let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
    let w_bits = Ghost.hide (U16.v ctx'.w_bits) in
    let w_size = Ghost.hide (v ctx'.w_size) in
    S.window_size_lower_bound (U16.v ctx'.w_bits) (U32.v ctx'.w_size);
    S.window_size_upper_bound (U16.v ctx'.w_bits) (U32.v ctx'.w_size);
    
    let window = (CB.index ctx 0ul).window in
    let window_size = (CB.index ctx 0ul).window_size in
    let lookahead = get_lookahead ls in
    let strstart = get_strstart ls in
    
    let w_end = strstart +^ lookahead in
    let w_end' = Ghost.hide (U32.v w_end) in
    let w_left = Ghost.hide (B.gsub window 0ul w_end) in
    
    [@inline_let] let more = window_size -^ w_end in
    let w_right= B.sub window w_end more in

    let (len, rbuf) = read_buf ss block_data next_in w_right more wrap in
    let h1 = Ghost.hide (ST.get ()) in
    let rbuf' = Ghost.hide (B.as_seq h0 rbuf) in
    assert(forall (i: nat{i < S.hash_end (B.as_seq h0 ls) + S.min_match - 1}).
      (B.as_seq h0 window).[i] == (B.as_seq h1 w_left).[i] /\
      (B.as_seq h1 window).[i] == (B.as_seq h1 w_left).[i]);

    let total_in = Ghost.hide (Seq.length block_data) in
    assert(forall (i: nat{i < U32.v len}). 
       (B.as_seq h1 rbuf).[i] == (B.as_seq h1 window).[i + w_end']);
    assert(forall (i: nat{i < w_end'}).
      block_data.[total_in - w_end' + i] == (B.as_seq h1 w_left).[i] /\
      (B.as_seq h1 w_left).[i] == (B.as_seq h1 window).[i]);
    assert(forall (i: nat{i < w_end'}).
      block_data.[total_in - w_end' + i] == (B.as_seq h1 window).[i]);
    assert((forall (i: nat{i < Seq.length block_data}).
      (block_data @| rbuf').[i] == block_data.[i]));
    
    set_lookahead w_bits w_size ls (lookahead +^ len);
    let lookahead' = get_lookahead ls in
    let avail_in' = get_avail_in ss in
    init_input_hash ctx ls;

    let min_lookahead = min_lookahead ctx in
    S.min_lookahead_upper_bound h0 ctx;
    
    if lookahead' <^ min_lookahead && avail_in' >^ 0ul then
      do_fill_window ss ctx ls next_in wrap (U32.v avail_in') (block_data @| rbuf')
    else
      Ghost.hide (block_data @| rbuf')

#set-options "--z3rlimit 8192 --fuel 0 --ifuel 0"
let fill_window ss ctx ls next_in wrap block_start block_data =
  ST.push_frame ();
  let open U32 in
  let more = slide_window ctx ls block_start in
  let avail_in = get_avail_in ss in
  let res = if avail_in>^ 0ul then
    do_fill_window ss ctx ls next_in wrap (U32.v avail_in) block_data
  else
    block_data
  in
  ST.pop_frame ();
  res
