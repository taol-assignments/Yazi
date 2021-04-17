module Yazi.Types

module B = LowStar.Buffer
module I32 = FStar.Int32
module I64 = FStar.Int64
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open Yazi.Deflate.Constants
open Yazi.Huffman
open Spec.Deflate.Params

noeq
type gz_header = {
    text: I32.t;              (* true if compressed data believed to be text *)
    time: U32.t;              (* modification time *)
    xflags: I32.t;            (* extra flags (not used when writing a gzip file) *)
    os: I32.t;                (* operating system *)
    extra: B.buffer U8.t;     (* pointer to extra field or Z_NULL if none *)
    extra_len: U32.t;         (* extra field length (valid if extra != Z_NULL) *)
    extra_max: U32.t;         (* space at extra (only when reading header) *)
    name: B.buffer U8.t;      (* pointer to zero-terminated file name or Z_NULL *)
    name_max: U32.t;          (* space at name (only when reading header) *)
    comment: B.buffer U8.t;   (* pointer to zero-terminated comment or Z_NULL *)
    comm_max: U32.t;          (* space at comment (only when reading header) *)
    hcrc: I32.t;              (* true if there was or will be a header crc *)
    done: I32.t;              (* true when done reading gzip header (not use)
                               * when writing a gzip file) *)
}

type wrap_t = w: I32.t {
 (CFlags.gzip /\ 0 <= I32.v w /\ I32.v w <= 2 ) \/
 (~CFlags.gzip /\ 0 <= I32.v w /\ I32.v w <= 1)
}

type window_bits_t = w: I32.t{
  window_bits_range w /\
  pow2 (I32.v w) <= pow2 16
}
type mem_level_t = m: I32.t{mem_level_valid m}
type strategy_t = s: I32.t{strategy_valid s}

type data_type_t = data: I32.t {
  data == Util.z_binary \/
  data == Util.z_text \/
  data == Util.z_ascii \/
  data == Util.z_unknown
}

noeq
type deflate_state = {
  status: I32.t;              (* as the name implies *)
  pending_buf: B.buffer U8.t; (* output still pending *)
  pending_buf_size: U32.t;    (* size of pending_buf *)
  pending_out: B.buffer U8.t; (* next pending type to output to the stream *)
  pending: U32.t;
  wrap: wrap_t;

  gzhead: B.pointer_or_null gz_header; (* gzip header information to write *)
  gzindex: U32.t;              (* where in extra, name, or comment *)
  last_flush: I32.t;           (* value of flush param for previous deflate call *)

  (* used by deflate.c: *)
  w_size: U32.t; (* LZ77 window size (32K by default) *)
  w_bits: U32.t; (* log2(w_size)  (8..16) *)
  w_mask: U32.t; (* w_size - 1 *)

  window: B.buffer U8.t;
  (* Sliding window. Input bytes are read into the second half of the window,
   * and move to the first half later to keep a dictionary of at least wSize
   * bytes. With this organization, matches are limited to a distance of
   * wSize-MAX_MATCH bytes, but this ensures that IO is always
   * performed with a length multiple of the block size. Also, it limits
   * the window size to 64K, which is quite useful on MSDOS.
   * To do: use the user input buffer as sliding window. *)

  window_size: U32.t;
  (* Actual size of window: 2*wSize, except when the user input buffer
   * is directly used as sliding window. *)

  prev: B.buffer U16.t;
  (* Link to older string with same hash index. To limit the size of this
   * array to 64K, this link is maintained only for the last 32K strings.
   * An index in this array is thus a window index modulo 32K. *)

  head: B.buffer U16.t; (* Heads of the hash chains of NIL. *)

  ins_h: U32.t;     (* hash index of string to be inserted *)
  hash_size: U32.t; (* number of elements in the hash table *)
  hash_bits: U32.t; (* log2(hash_size) *)
  hash_mask: U32.t; (* hash_size-1 *)

  hash_shift: U32.t;
  (* Number of bits by which ins_h must be shifted at each input
   * step. It must be such that after MIN_MATCH steps, the oldest
   * byte no longer takes part in the hash key, that is:
   *   hash_shift * MIN_MATCH >= hash_bits *)

  block_start: I64.t;
  (* Window position at the beginning of the current output block. Gets
   * negative when the window is moved backwards. *)

  match_length: U32.t;    (* length of the best match *)
  prev_match: U32.t;      (* previous match *)
  match_available: I32.t; (* set if previous match exists *)
  strstart: U32.t;        (* start of string to insert *)
  match_start: U32.t;     (* start of matching string *)
  lookahead: U32.t;       (* number of valid bytes ahead in window *)

  prev_length: U32.t;
  (* Length of the best match at previous step. Matches not greater than this
   * are discarded. This is used in the lazy match evaluation. *)
   
  max_chain_length: U32.t;
  (* To speed up deflation, hash chains are never searched beyond this
   * length.  A higher limit improves compression ratio but degrades the
   * speed.
   *)
   
  max_lazy_length: U32.t;
  (* Attempt to find a better match only when the current match is strictly
   * smaller than this value. This mechanism is used only for compression
   * levels >= 4. *)

  level: I32.t; (* compression level (1..9) *)
  strategy: I32.t; (* favor or force Huffman coding *)

  good_match: U32.t;
  (* Use a faster search when the previous match is longer than this *)

  nice_match: I32.t;
  (* Stop searching when current match exceeds this *)

  (* Used by Huffman trees *)
  dyn_ltree: dyn_ltree_t; (* literal and length tree *)
  dyn_dtree: dyn_dtree_t; (* distance tree *)
  bl_tree: bl_tree_t;     (* Huffman tree for bit lengths *)

  l_desc: tree_desc; (* desc. for literal tree *)
  d_desc: tree_desc; (* desc. for distance tree *)
  bl_desc: tree_desc;(* desc. for bit length tree *)

  bl_count: bl_count_t;
  (* number of codes at each bit length for an optimal tree *)

  heap: tree_heap_t; (* head used to build the Huffman trees *)
  heap_len: U32.t;   (* number of elements in the heap *)
  heap_max: U32.t;   (* element of largest frequency *)
  (* The sons of heap[n] are heap[2*n] and heap[2*n+1]. heap[0] is not used.
   * The same heap array is used to build all trees.
   *)

  depth: tree_depth_t;
  (* Depth of each subtree used as tie breaker for trees of equal frequency *)

  l_buf: B.buffer U8.t; (* buffer for literals or lengths *)

  lit_bufsize: U32.t;
  (* Size of match buffer for literals/lengths.  There are 4 reasons for
   * limiting lit_bufsize to 64K:
   *   - frequencies can be kept in 16 bit counters
   *   - if compression is not successful for the first block, all input
   *     data is still in the window so we can still emit a stored block even
   *     when input comes from standard input.  (This can also be done for
   *     all blocks if lit_bufsize is not greater than 32K.)
   *   - if compression is not successful for a file smaller than 64K, we can
   *     even emit a stored file instead of a stored block (saving 5 bytes).
   *     This is applicable only for zip (not gzip or zlib).
   *   - creating new Huffman trees less frequently may not provide fast
   *     adaptation to changes in the input data statistics. (Take for
   *     example a binary file with poorly compressible code followed by
   *     a highly compressible string table.) Smaller buffer sizes give
   *     fast adaptation but have of course the overhead of transmitting
   *     trees more frequently.
   *   - I can't count above 4 *)

  last_list: U32.t; (* running index in l_buf *)

  d_buf: B.buffer U16.t;
  (* Buffer for distances. To simplify the code, d_buf and l_buf have
   * the same number of elements. To use different lengths, an extra flag
   * array would be necessary. *)

  opt_len: U32.t;      (* bit length of current block with optimal trees *)
  static_len: U32.t;   (* bit length of current block with static trees *)
  matches: U32.t;      (* number of string matches in current block *)
  insert: U32.t;       (* bytes at end of window left to insert *)

  bi_buf: U16.t;
  (* Output buffer. bits are inserted starting at the bottom (least
   * significant bits). *)
   
  bi_valid: U32.t;
  (* Number of valid bits in bi_buf.  All bits above the last valid bit
   * are always zero. *)

  high_water: U32.t;
  (* High water mark offset in window for initialized bytes -- bytes above
   * this are set to zero in order to avoid memory check warnings when
   * longest match routines access bytes past the input.  This is then
   * updated to the new high water mark. *)
}

noeq
type z_stream = {
  next_in: B.buffer U8.t;	(* next input byte *)
  avail_in: U32.t;		(* number of bytes available at next_in *)
  total_in: U32.t;		(* total number of input bytes read so far *)

  next_out: B.buffer U8.t;	(* next output byte will go here *)
  avail_out: U32.t;		(* remaining free space at next_out *)
  total_out: U32.t;		(* total number of bytes output so far *)

  msg: B.buffer U8.t;	                  (* last error message, NULL if no error *)
  state: B.pointer_or_null deflate_state; (* not visible by applications *)

  (* Custom allocator will be inserted by the Makefile *)

  data_type: data_type_t;	(* best guess about the data type: binary or text
                       	         * for deflate, or the decoding state for inflate *)

  adler: U32.t;		(* Adler-32 or CRC-32 value of the uncompressed data *)
  reserved: U32.t;	(* reserved for future use *)
}
