module Yazi.LZ77

module Adler32 = Yazi.Adler32
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module CRC32 = Yazi.CRC32
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open LowStar.BufferOps
open FStar.Mul
open Spec.LZ77
open Lib.Seq

let context_valid (c: lz77_context) =
  let open U16 in
  is_window_bits (v c.w_bits) /\
  is_window_mask (v c.w_bits) (v c.w_mask) /\
  is_window_size (v c.w_bits) (U32.v c.w_size) /\
  (U32.v c.window_size) == (U32.v c.w_size) * 2 /\
  B.length c.window == U32.v c.window_size /\
  B.length c.prev == U32.v c.w_size /\
  is_hash_bits (v c.h_bits) /\
  is_hash_size (v c.h_bits) (U32.v c.h_size) /\
  is_hash_mask (v c.h_bits) (v c.h_mask) /\
  is_hash_shift (v c.h_bits) (v c.shift) /\
  B.length c.head == U32.v c.h_size

#set-options "--fuel 0 --ifuel 0"
inline_for_extraction
let update_hash
  (a b c: Ghost.erased U8.t)
  (ctx: CB.const_buffer lz77_context)
  (ins_h: B.pointer U16.t)
  (d: U8.t):
  ST.StackInline unit
  (ensures fun h ->
    let open U16 in
    CB.length ctx == 1 /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    CB.live h ctx /\ B.live h ins_h /\ B.disjoint ins_h (CB.as_mbuf ctx) /\
    context_valid ctx' /\
    is_rolling_hash (v ctx'.h_bits) a b c (B.get h ins_h 0)))
  (requires fun h0 _ h1 ->
    let open U16 in
    let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    let hash = B.get h1 ins_h 0 in
    B.modifies (B.loc_buffer ins_h) h0 h1 /\
    is_rolling_hash (v ctx'.h_bits) b c d (B.get h1 ins_h 0)) =
  let open U16 in
  [@inline_let] let d' = Cast.uint8_to_uint16 d in
  let bits = (CB.index ctx 0ul).h_bits in
  let bits': Ghost.erased hash_bits = Ghost.hide (v bits) in
  let s = (CB.index ctx 0ul).shift in
  let m = (CB.index ctx 0ul).h_mask in
  [@inline_let] let s' = Cast.uint16_to_uint32 s in
  let hash = !*ins_h in
  roll_hash_eq bits' m s a b c d hash;
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
  [@inline_let] let avail_in' = B.sub ss 0ul 1ul in
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

