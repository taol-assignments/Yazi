module Yazi.LZ77

module Adler32 = Spec.Adler32
module B = LowStar.Buffer
module CFlags = Yazi.CFlags
module CRC32 = Spec.CRC32
module HS = FStar.HyperStack
module I32 = FStar.Int32
module S = Spec.State
module Seq = FStar.Seq
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Util = Yazi.Util

noeq type lz77_context = {
  w_size: U32.t;        (* LZ77 window size (32K by default) *)
  w_bits: U16.t;        (* log2 w_size  (8..16) *)
  w_mask: U16.t;        (* w_size - 1 *)

  (* Sliding window. Input bytes are read into the second half of the window,
   * and move to the first half later to keep a dictionary of at least wSize
   * bytes. With this organization, matches are limited to a distance of
   * wSize-MAX_MATCH bytes, but this ensures that IO is always
   * performed with a length multiple of the block size. Also, it limits
   * the window size to 64K, which is quite useful on MSDOS.
   * To do: use the user input buffer as sliding window. *)
  window: B.buffer U8.t;

  (* Actual size of window: 2 * w_size, except when the user input buffer
   * is directly used as sliding window. *)
  window_size: U32.t;
     
  (* Link to older string with same hash index. To limit the size of this
   * array to 64K, this link is maintained only for the last 32K strings.
   * An index in this array is thus a window index modulo 32K.*)
  prev: B.buffer U16.t;

  head: B.buffer U16.t; (* Heads of the hash chains or NIL. *)

  h_size: U32.t;        (* number of elements in hash table *)
  h_bits: U16.t;        (* log2 h_size *)
  h_mask: U16.t;        (* h_size - 1 *)

  (* Number of bits by which ins_h must be shifted at each input
   * step. It must be such that after MIN_MATCH steps, the oldest
   * byte no longer takes part in the hash key, that is:
   *   shift * MIN_MATCH >=h_bits *)
  shift: U16.t;
}

noeq type lz77_state = {
  (* Window position at the beginning of the current output block. Gets
   * negative when the window is moved backwards. *)
  block_start: I32.t;

  ins_h: U32.t;        (* hash index of string to be inserted *)
  match_length: U32.t; (* length of best match *)
  prev_match: U32.t;   (* previous match *)
  strstart: U32.t;     (* start of string to insert *)
  match_start: U32.t;  (* start of matching string *)
  lookahead: U32.t;    (* number of valid bytes ahead in window *)

  (* Length of the best match at previous step. Matches not greater than this
   * are discarded. This is used in the lazy match evaluation. *)
  prev_length: U32.t;
  match_available: bool; (* set if previous match exists *)
}

type stream_state = B.lbuffer U32.t 5

val read_buf:
    ss: stream_state
  -> uncompressed: Ghost.erased (Seq.seq U8.t)
  -> next_in: B.pointer (B.buffer U8.t)
  -> buf: B.buffer U8.t
  -> size: U32.t
  -> wrap: I32.t
  -> ST.Stack (U32.t & Ghost.erased (B.buffer U8.t))
  (requires fun h -> 
    let len = if U32.v size > S.avail_in (B.as_seq h ss) then
      S.avail_in (B.as_seq h ss)
    else
      U32.v size
    in
    len > 0 /\
    B.live h ss /\ ~(B.g_is_null ss) /\
    B.live h buf /\ ~(B.g_is_null buf) /\
    HS.disjoint (B.frameOf ss) (B.frameOf buf) /\
    B.length buf == U32.v size /\
    S.next_in_valid h ss next_in /\
    S.adler_valid h ss wrap uncompressed)
  (ensures fun h0 res h1 ->
  let (len', read) = res in
  let next_in0 = B.get h0 next_in 0 in
  let next_in1 = B.get h1 next_in 0 in
  let s0 = B.as_seq h0 ss in
  let s1 = B.as_seq h1 ss in
  let len = if U32.v size > S.avail_in s0 then
    S.avail_in s0
  else
    U32.v size
  in
  len == U32.v len' /\
  B.modifies (B.loc_union
    (B.loc_buffer ss)
    (B.loc_union (B.loc_buffer next_in) (B.loc_buffer buf))) h0 h1 /\
  Seq.equal (B.as_seq h1 read) (B.as_seq h0 (B.gsub next_in0 0ul len')) /\
  S.avail_in s0 - len == S.avail_in s1 /\
  S.next_in_valid h1 ss next_in /\
  S.adler_valid h1 ss wrap (Seq.append uncompressed (B.as_seq h1 read)) /\
  S.avail_out s0 == S.avail_out s1 /\
  S.total_out s0 == S.total_out s1)
