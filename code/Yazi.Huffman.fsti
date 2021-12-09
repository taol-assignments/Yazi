module Yazi.Huffman

module B = LowStar.Buffer
module I32 = FStar.Int32
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open Yazi.Deflate.Constants

noeq
type ct_data = {
  freq_or_dad: U16.t;
  code_or_len: U16.t;
}

noeq
type static_tree_desc = {
  static_tree: B.pointer_or_null ct_data;
  extra_bits: B.buffer I32.t;
  extra_base: I32.t;
  elems: I32.t;
  max_length: I32.t;
}

noeq
type tree_desc = {
  dyn_tree: B.buffer ct_data;
  max_code: I32.t;
  stat_desc: B.pointer_or_null static_tree_desc;
}

type dyn_ltree_t = tree: B.buffer ct_data{
  B.len tree == heap_size
}

type dyn_dtree_t = tree: B.buffer ct_data{
  let open U32 in
  B.len tree == 2ul *^ d_codes +^ 1ul
}

type bl_tree_t = tree: B.buffer ct_data{
  let open U32 in
  B.len tree == 2ul *^ bl_codes +^ 1ul
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

val static_l_desc: B.pointer static_tree_desc

val static_d_desc: B.pointer static_tree_desc

val static_bl_desc: B.pointer static_tree_desc

[@CMacro]
let end_block = 256ul

