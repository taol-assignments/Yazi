module Yazi.LZ77.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module I32 = FStar.Int32
module LB = Lib.Buffer
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

noeq type lz77_context = {
  w_size: U32.t; (* LZ77 window size (32K by default) *)
  w_bits: U16.t; (* log2 w_size  (8..16) *)
  w_mask: U16.t; (* w_size - 1 *)

  (* Sliding window. Input bytes are read into the second half of the window,
   * and move to the first half later to keep a dictionary of at least wSize
   * bytes. With this organization, matches are limited to a distance of
   * wSize-MAX_MATCH bytes, but this ensures that IO is always
   * performed with a length multiple of the block size. Also, it limits
   * the window size to 64K.
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

  (* To speed up deflation, hash chains are never searched beyond this
   * length.  A higher limit improves compression ratio but degrades the
   * speed. *)
  max_chain_length: U32.t;

  (* Attempt to find a better match only when the current match is strictly
   * smaller than this value. This mechanism is used only for compression
   * levels >= 4. *)
  max_lazy_match: U32.t;
  (* Use a faster search when the previous match is longer than this *)
  good_match: U32.t;
  nice_match: U32.t; (* Stop searching when current match exceeds this *)
}

type lz77_context_p = ctx: CB.const_buffer lz77_context {CB.length ctx == 1}

type lz77_state_t = B.lbuffer U32.t 13
