module Yazi.Tree.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Yazi.Deflate.Constants

noeq
type ct_data = {
  freq_or_dad: U16.t;
  code_or_len: U16.t;
}

type dyn_ltree_t = tree: B.buffer ct_data{
  B.len tree == heap_size
}

type dyn_dtree_t = tree: B.buffer ct_data{
  let open U32 in
  B.length tree == U32.v (2ul *^ d_codes +^ 1ul)
}

type bl_tree_t = tree: B.buffer ct_data{
  let open U32 in
  B.len tree == 2ul *^ bl_codes +^ 1ul
}

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

type bl_count_t = count: B.buffer U16.t{
  let open U32 in
  B.len count == max_bits +^ 1ul
}

type tree_heap_t = heap: B.buffer U32.t{
  let open U32 in
  B.len heap == 2ul *^ l_codes +^ 1ul
}

type tree_depth_t = depth: B.buffer U8.t{
  let open U32 in
  B.len depth == 2ul *^ l_codes +^ 1ul
}

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
