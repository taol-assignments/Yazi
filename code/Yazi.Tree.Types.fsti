module Yazi.Tree.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module Seq = FStar.Seq
module ST = FStar.HyperStack.ST
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

noextract
type tree_len_t = tl: Ghost.erased nat{tl <= U32.v heap_size}

type tree_depth_t = B.lbuffer U8.t (2 * U32.v l_codes + 1)

// noextract
// type cmp_spec_t =
//     tree_len: nat 
//   -> tree: Seq.seq ct_data{Seq.length tree == tree_len}
//   -> depth: Seq.seq U8.t{Seq.length depth == 2 * U32.v l_codes + 1}
//   -> i: U32.t
//   -> j: U32.t
//   -> Pure bool
//   (requires (
//     let open U32 in
//     v i < tree_len /\ v i < Seq.length depth /\
//     v j < tree_len /\ v j < Seq.length depth))
//   (ensures fun _ -> True)

// type cmp_impl (spec: cmp_spec_t) =
//     tree_len: tree_len_t
//   -> tree: B.lbuffer ct_data (Ghost.reveal tree_len)
//   -> depth: tree_depth_t
//   -> n: U32.t
//   -> m: U32.t
//   -> ST.Stack bool
//   (requires fun h ->
//     U32.v n < tree_len /\ U32.v m < tree_len /\ B.live h tree /\ B.live h depth)
//   (ensures fun h0 res h1 ->
//     B.modifies B.loc_none h0 h1 /\
//     (res == true <==> spec tree_len (B.as_seq h1 tree) (B.as_seq h1 depth) n m))

type heap_index_t (hl: heap_len_t) = i: U32.t{
  0 < U32.v i /\ U32.v i <= U32.v hl
}

type heap_internal_index_t (hl: heap_len_t) = i: U32.t{
  0 < U32.v i /\ U32.v i <= U32.v hl / 2
}

noeq type sort_ctx_t = {
  // cmp_spec: Ghost.erased cmp_spec_t;
  // cmp: cmp_impl cmp_spec;
  
  heap: tree_heap_t;
  tree_len: tree_len_t;
  tree: B.buffer ct_data;

  depth: tree_depth_t;
}

type sort_ctx = ctx: CB.const_buffer sort_ctx_t{
  ~ (B.g_is_null (CB.as_mbuf ctx)) /\ CB.length ctx == 1
}

type sort_state = B.lbuffer U32.t 2

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

  // bl_count: bl_count_t;
  // heap: tree_heap_t;
  // depth: tree_depth_t;

  l_buf: B.buffer U8.t;
  d_buf: B.buffer U8.t;
  pending_buf: B.buffer U8.t;

  lit_bufsize: lit_bufsize_t;
  pending_buf_size: U32.t;
}
