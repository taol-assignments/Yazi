module Yazi.LZ77

module Adler32 = Yazi.Adler32
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module CRC32 = Yazi.CRC32
module I32 = FStar.Int32
module LB = Lib.Buffer
module Math = FStar.Math.Lemmas
module S = Spec.LZ77
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open LowStar.BufferOps
open FStar.Mul
open Lib.Seq
open Lib.Buffer

type context_p = ctx: CB.const_buffer lz77_context {CB.length ctx == 1}

let context_valid (h: HS.mem) (ctx: context_p) =
  let open U16 in
  CB.length ctx == 1 /\
  (let c = B.get h (CB.as_mbuf ctx) 0 in
  S.is_window_bits (v c.w_bits) /\
  S.is_window_mask (v c.w_bits) (v c.w_mask) /\
  S.is_window_size (v c.w_bits) (U32.v c.w_size) /\
  U32.v c.window_size == (U32.v c.w_size) * 2 /\
  B.length c.window == U32.v c.window_size /\
  B.length c.prev == U32.v c.w_size /\
  S.is_hash_bits (v c.h_bits) /\
  S.is_hash_size (v c.h_bits) (U32.v c.h_size) /\
  S.is_hash_mask (v c.h_bits) (v c.h_mask) /\
  S.is_hash_shift (v c.h_bits) (v c.shift) /\
  B.length c.head == U32.v c.h_size /\
  CB.live h ctx /\ B.live h c.prev /\ B.live h c.window /\ B.live h c.head /\ B.live h c.prev /\
  B.disjoint c.window c.prev /\ B.disjoint c.window c.head /\ B.disjoint c.prev c.head /\
  B.frameOf c.window == B.frameOf c.prev /\ B.frameOf c.prev == B.frameOf c.head /\
  B.frameOf (CB.as_mbuf ctx) <> B.frameOf c.prev /\
  HS.disjoint (B.frameOf (CB.as_mbuf ctx)) (B.frameOf c.prev))

#set-options "--fuel 0 --ifuel 0"
inline_for_extraction
let update_hash
  (a b c: Ghost.erased U8.t)
  (ctx: context_p)
  (ins_h: B.pointer U16.t)
  (d: U8.t):
  ST.StackInline unit
  (ensures fun h ->
    let open U16 in
    context_valid h ctx /\
    B.live h ins_h /\ B.disjoint ins_h (CB.as_mbuf ctx) /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    HS.disjoint (B.frameOf ins_h) (B.frameOf ctx'.head) /\
    S.is_rolling_hash (v ctx'.h_bits) a b c (B.get h ins_h 0)))
  (requires fun h0 _ h1 ->
    let open U16 in
    let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    let hash = B.get h1 ins_h 0 in
    B.modifies (B.loc_buffer ins_h) h0 h1 /\
    S.is_rolling_hash (v ctx'.h_bits) b c d (B.get h1 ins_h 0)) =
  let open U16 in
  [@inline_let] let d' = Cast.uint8_to_uint16 d in
  let bits = (CB.index ctx 0ul).h_bits in
  let bits': Ghost.erased S.hash_bits = Ghost.hide (v bits) in
  let s = (CB.index ctx 0ul).shift in
  let m = (CB.index ctx 0ul).h_mask in
  [@inline_let] let s' = Cast.uint16_to_uint32 s in
  let hash = !*ins_h in
  S.roll_hash_eq bits' m s a b c d hash;
  ins_h *= (((hash <<^ s') ^^ d') &^ m)

#set-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let read_buf ss uncompressed next_in buf size wrap =
  let open U32 in
  let avail_in = ss.(0ul) in
  let len = if avail_in >^ size then
    size
  else
    avail_in
  in
  let avail_in' = B.sub ss 0ul 1ul in
  let next_in' = !*next_in in
  let ulen = Ghost.hide (Seq.length uncompressed) in
    
  B.blit next_in' 0ul buf 0ul len;
  let buf' = B.sub next_in' 0ul (Ghost.hide len) in
  if wrap = 1l then begin
    ss.(4ul) <- (Adler32.adler32 #ulen (Ghost.reveal uncompressed) ss.(4ul) buf' len)
  end else if CFlags.gzip then
    if wrap = 2l then
      ss.(4ul) <- (CRC32.crc32 uncompressed ss.(4ul) buf' len)
    else
      ()
  else
    ();
  next_in *= (B.sub next_in' len (avail_in -^ len));
  ss.(0ul) <- avail_in -^ len;
  ss.(1ul) <- U32.add_underspec ss.(1ul) len;
  (len, Ghost.hide buf')

let w_size_fit_u32 (w_size: U32.t{U32.v w_size < pow2 15}): Lemma
  (ensures 2 * U32.v w_size < pow2 32)
  [SMTPat (2 * U32.v w_size)] = 
  Math.pow2_double_mult 15

#set-options "--z3rlimit 2048 --fuel 0 --ifuel 0"
inline_for_extraction
let rec slide_head (ctx: context_p) (h_size w_range: Ghost.erased U32.t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    U32.v i <= U32.v ctx'.h_size /\
    U32.v h_size == U32.v ctx'.h_size /\
    U32.v ctx'.w_size <= U32.v w_range /\ U32.v w_range <= 2 * U32.v ctx'.w_size /\
    S.sub_head_valid
      h ctx'.h_bits ctx'.w_size w_range ctx'.h_size
      (fun j -> j >= U32.v i /\ j < U32.v ctx'.h_size)
      ctx'.head ctx'.window /\
    S.sub_head_valid
      h ctx'.h_bits ctx'.w_size (w_range -^ ctx'.w_size) ctx'.h_size
      (fun j -> j < U32.v i)
      ctx'.head (S.slided_window ctx'.w_size w_range ctx'.window)))
  (ensures fun h0 _ h1 ->
    let open U32 in
    context_valid h1 ctx /\
    (let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    let ctx'' = B.get h1 (CB.as_mbuf ctx) 0 in
    B.modifies (B.loc_buffer ctx'.head) h0 h1 /\
    S.head_valid
      h1 ctx'.h_bits ctx'.w_size (w_range -^ ctx'.w_size) ctx'.h_size
      ctx'.head (S.slided_window ctx'.w_size w_range ctx'.window)))
  (decreases U32.v h_size - U32.v i) =
  let open U32 in
  let head = (CB.index ctx 0ul).head in
  let w_size = (CB.index ctx 0ul).w_size in
  if i <^ (CB.index ctx 0ul).h_size then begin
    let m = head.(i) in
    [@inline_let] let m' = Cast.uint16_to_uint32 m in
    head.(i) <- Cast.uint32_to_uint16 (if m' >=^ w_size then m' -^ w_size else 0ul);
    slide_head ctx h_size w_range (i +^ 1ul)
  end else
    ()

inline_for_extraction
let rec slide_prev (ctx: context_p) (w_size w_range: Ghost.erased U32.t) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    CFlags.fastest == false /\
    U32.v i <= U32.v ctx'.w_size /\
    U32.v w_size == U32.v ctx'.w_size /\
    U32.v ctx'.w_size <= U32.v w_range /\ U32.v w_range <= 2 * U32.v ctx'.w_size /\
    S.sub_prev_valid h
      ctx'.w_bits ctx'.w_size
      (fun j -> v i <= j /\ j < v w_size)
      ctx'.prev (B.gsub ctx'.window 0ul w_range) /\
    S.sub_prev_valid h
      ctx'.w_bits ctx'.w_size
      (fun j -> j < v i)
      ctx'.prev (S.slided_window ctx'.w_size w_range ctx'.window)))
  (ensures fun h0 _ h1 ->
    context_valid h1 ctx /\
    (let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    B.modifies (B.loc_buffer ctx'.prev) h0 h1 /\
    S.prev_valid h1
      ctx'.w_bits ctx'.w_size
      ctx'.prev (S.slided_window ctx'.w_size w_range ctx'.window)))
  (decreases U32.v w_size - U32.v i) =
  let open U32 in
  let prev = (CB.index ctx 0ul).prev in
  let w_size' = (CB.index ctx 0ul).w_size in
  if i <^ w_size' then begin
    let m = prev.(i) in
    [@inline_let] let m' = Cast.uint16_to_uint32 m in
    prev.(i) <- Cast.uint32_to_uint16 (if m' >=^ w_size' then m' -^ w_size' else 0ul);
    slide_prev ctx w_size w_range (i +^ 1ul)
  end else
    ()

inline_for_extraction
let slide_window_buf
  (ctx: context_p)
  (state: lz77_state)
  (block_start: B.pointer I32.t)
  (len: U32.t):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    v len <= v ctx'.w_size /\
    S.slide_window_pre h ctx'.w_bits state block_start ctx'.w_size ctx'.window))
  (ensures fun h0 _ h1 -> 
    context_valid h0 ctx /\
    (let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    B.modifies (
      B.loc_buffer block_start `B.loc_union`
      B.loc_buffer state `B.loc_union`
      B.loc_buffer ctx'.window) h0 h1 /\
    S.slide_window_buf_post h0 h1
      ctx'.w_bits state block_start ctx'.w_size ctx'.window len)) =
  let open U32 in
  let w_size = (CB.index ctx 0ul).w_size in
  let window = (CB.index ctx 0ul).window in
  let w_bits = Ghost.hide (CB.index ctx 0ul).w_bits in
  S.window_size_upper_bound (U16.v w_bits) (v w_size);
  let left = B.sub window 0ul w_size in
  let right = B.sub window w_size w_size in
  B.blit right 0ul left 0ul len;
  set_match_start (U16.v w_bits) (v w_size) state ((get_match_start state) -^ w_size);
  set_strstart (U16.v w_bits) (v w_size) state ((get_strstart state) -^ w_size);
  block_start *= I32.sub (!*block_start) (Cast.uint32_to_int32 w_size)

#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0"
inline_for_extraction
let slide_window
  (ctx: context_p)
  (state: lz77_state)
  (block_start: B.pointer I32.t):
  ST.Stack U32.t
  (requires fun h ->
    let open U32 in
    let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    let state' = B.as_seq h state in
    context_valid h ctx /\
    B.disjoint (CB.as_mbuf ctx) state /\ B.disjoint (CB.as_mbuf ctx) block_start /\
    HS.disjoint (B.frameOf state) (B.frameOf ctx'.head) /\
    HS.disjoint (B.frameOf block_start) (B.frameOf ctx'.head) /\

    S.slide_window_pre h ctx'.w_bits state block_start ctx'.w_size ctx'.window /\
    (let w_range = U32.uint_to_t (S.strstart state' - S.insert state') in
    S.hash_chain_valid h
      ctx'.w_bits ctx'.h_bits
      ctx'.w_size ctx'.h_size
      ctx'.head ctx'.prev (B.gsub ctx'.window 0ul w_range)
      w_range))
  (ensures fun h0 more h1 ->
    let open U32 in
    let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    let ctx1 = B.get h1 (CB.as_mbuf ctx) 0 in
    let s0 = B.as_seq h0 state in
    let s1 = B.as_seq h1 state in
    S.slided_window_space_valid s0 ctx'.w_size more /\
    (S.strstart s0 < U32.v ctx'.w_size ==> B.modifies B.loc_none h0 h1) /\
    (S.strstart s0 >= U32.v ctx'.w_size ==>
      S.lookahead s1 + S.strstart s1 <= U32.v ctx'.w_size /\
      (let len = uint_to_t (S.lookahead s1 + S.strstart s1) in
      B.modifies (
        B.loc_buffer block_start `B.loc_union`
        B.loc_buffer state `B.loc_union`
        B.loc_buffer ctx'.window `B.loc_union`
        B.loc_buffer ctx'.head `B.loc_union`
        (if CFlags.fastest then B.loc_none else B.loc_buffer ctx'.prev)) h0 h1 /\
      S.slide_window_buf_post h0 h1
        ctx'.w_bits state block_start
        ctx'.w_size ctx'.window len /\
      (let w_range = uint_to_t (S.strstart s1 - S.insert s1) in
      B.as_seq h0 (B.gsub ctx'.window ctx'.w_size w_range) ==
      B.as_seq h1 (B.gsub ctx'.window 0ul w_range) /\
      S.hash_chain_valid h1
        ctx'.w_bits ctx'.h_bits
        ctx'.w_size ctx'.h_size
        ctx'.head ctx'.prev ctx'.window
        w_range
      )))) =
  let h0 = Ghost.hide (ST.get ()) in
  let open U32 in
  let strstart = get_strstart state in
  let w_size = (CB.index ctx 0ul).w_size in
  let w_bits = Ghost.hide (CB.index ctx 0ul).w_bits in
  let w_range = Ghost.hide (strstart -^ get_insert state) in
  let h_size = Ghost.hide (CB.index ctx 0ul).h_size in
  let h_bits = Ghost.hide (CB.index ctx 0ul).h_bits in
  let window = Ghost.hide (CB.index ctx 0ul).window in
  let head = Ghost.hide (CB.index ctx 0ul).head in
  let more = (CB.index ctx 0ul).window_size -^ get_lookahead state -^ strstart in
  if strstart >=^ w_size then begin
    slide_head ctx h_size w_range 0ul;
    if CFlags.fastest then () else slide_prev ctx w_size w_range 0ul;
    slide_window_buf ctx state block_start (w_size -^ more);

    let h1 = Ghost.hide (ST.get ()) in
    LB.as_seq_gsub_eq h0 h1 window window w_size 0ul (w_size -^ more) (w_range -^ w_size);
    more +^ w_size
  end else
    more
