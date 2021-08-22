module Yazi.Tree.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open Yazi.Deflate.Constants

noeq
type ct_data = {
  freq_or_code: U16.t;
  dad_or_len: U16.t;
}

type dyn_ltree_t = B.lbuffer ct_data (U32.v heap_size)

type dyn_dtree_t = B.lbuffer ct_data (2 * U32.v d_codes + 1)

type bl_tree_t = B.lbuffer ct_data (2 * U32.v bl_codes + 1)

noeq
type static_tree_desc = {
  static_tree: CB.const_buffer ct_data;
  extra_bits: CB.const_buffer U32.t;
  extra_base: U32.t;
  elems: U32.t;
  max_length: U32.t;
}

noeq
type tree_desc = {
  max_code: U32.t;
  stat_desc: CB.const_buffer static_tree_desc;
}

type bl_count_t = B.lbuffer U16.t (U32.v max_bits + 1)

type tree_heap_t = B.lbuffer U32.t (2 * U32.v l_codes + 1)

type heap_len_t = l: U32.t{0 < U32.v l /\ U32.v l < U32.v heap_size}

type heap_index_t (hl: heap_len_t) = i: U32.t{
  0 < U32.v i /\ U32.v i <= U32.v hl
}

type heap_internal_index_t (hl: heap_len_t) = i: U32.t{
  0 < U32.v i /\ U32.v i <= U32.v hl / 2
}

noextract
type tree_len_t = tl: Ghost.erased nat{tl <= U32.v heap_size}

type tree_depth_t = B.lbuffer U8.t (2 * U32.v l_codes + 1)

type lit_bufsize_t = s: U32.t {
  let open U32 in
  v s == pow2 7 \/ v s == pow2 8 \/
  v s == pow2 9 \/ v s == pow2 10 \/
  v s == pow2 11 \/ v s == pow2 12 \/
  v s == pow2 13 \/ v s == pow2 14 \/
  v s == pow2 15 \/ v s == pow2 16
}

noeq
type tree_context = {
  dyn_ltree: dyn_ltree_t;
  dyn_dtree: dyn_dtree_t;
  bl_tree: dyn_ltree_t;

  l_desc: tree_desc;
  d_desc: tree_desc;
  bl_desc: tree_desc;

  bl_count: bl_count_t;
  heap: tree_heap_t;
  depth: tree_depth_t;

  l_buf: B.buffer U8.t;
  d_buf: B.buffer U8.t;
  pending_buf: B.buffer U8.t;

  lit_bufsize: lit_bufsize_t;
  pending_buf_size: U32.t;
}
