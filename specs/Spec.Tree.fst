module Spec.Tree

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open FStar.Seq
open Lib.Seq
open Spec.Heap
open Yazi.Tree.Types
include Spec.Tree.Lemmas

/// Merge two trees that have the lowest frequencies after the call of pqremove.
#push-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 1"
let pqmerge (ts: heap_wf_ts) (node: nat): Pure tree_state_wf
  (requires pqmerge_pre ts node)
  (ensures fun ts' -> pqmerge_post ts node ts') =
  let il = U32.v ts.heap.[ts.heap_max] in
  let hl = U8.v ts.depth.[il] in
  let l = ts.forest.[il] in
  let t1 = ts.tree.(il) <- ({
    (ts.tree).[il] with
    dad_or_len = U16.uint_to_t node;
  }) in
 
  let ir = U32.v ts.heap.[1] in
  let hr = U8.v ts.depth.[ir] in
  let r = ts.forest.[ir] in
  let t2 = t1.(ir) <- ({
    (ts.tree).[ir] with
    dad_or_len = U16.uint_to_t node;
  }) in

  let t' = Node l node (freq l + freq r) r in
  lemma_is_max_id_map ts node 1;
  lemma_is_max_id_map ts node ts.heap_max;
  lemma_pqmerge_no_dup ts ts.heap_max 1;

  let dt' = (1 + (if hl >= hr then hl else hr)) % pow2 8 in

  lemma_forest_freq_plus ts 0 1;
  let t3 = t2.(node) <- ({
    t2.[node] with
    freq_or_code = (t2.[il]).freq_or_code `U16.add` (t2.[ir]).freq_or_code;
  }) in

  let heap_max' = ts.heap_max - 1 in
  let heap' = ts.heap.(heap_max') <- U32.uint_to_t ir in
  let heap'' = heap'.(1) <- U32.uint_to_t node in
  let ts': tree_state_wf = {
    ts with
    heap = heap'';
    heap_max = heap_max';
    forest = ts.forest.(node) <- t';
    depth = ts.depth.(node) <- U8.uint_to_t dt';
    tree = t3;
  } in
  lemma_pqmerge_main ts node ts' t';
  admit();
  ts'

#push-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 1"
/// Merge the two trees that have the lowest frequencies.
let merge_tree (ts: forest_wf_ts) (node: nat):
  Ghost forest_wf_ts
  (requires
    ts.heap_len > 1 /\
    // (forall i. i >= node ==> U8.v (ts.depth).[i] == 0) /\
    is_max_id ts node)
  (ensures fun ts' ->
    ts' == {
      ts with
      heap = ts'.heap;
      heap_len = ts.heap_len - 1;
      heap_max = ts.heap_max - 2;
      forest = ts'.forest;
      depth = ts'.depth;
      tree = ts'.tree;
    } /\
    (forall s. U32.v s <> node ==>
      count s (element_seq ts) == count s (element_seq ts')) /\
    count (U32.uint_to_t node) (element_seq ts') == 1 /\
    permutation nat (forest_symbols ts) (forest_symbols ts')) =
  let ts' = pqremove ts in

  let il = U32.v (ts'.heap).[ts'.heap_max] in
  let hl = U8.v (ts'.depth).[il] in
  let l = (ts'.forest).[il] in
  let t1 = ts.tree.(il) <- ({
    (ts.tree).[il] with
    dad_or_len = U16.uint_to_t node;
  }) in
 
  let ir = U32.v (ts'.heap).[1] in
  let hr = U8.v (ts'.depth).[ir] in
  let r = (ts'.forest).[ir] in
  let t2 = t1.(ir) <- ({
    (ts.tree).[ir] with
    dad_or_len = U16.uint_to_t node;
  }) in
 
  let t' = Node l node (freq l + freq r) r in
  let dt' = (1 + (if hl >= hr then hl else hr)) % pow2 8 in
  let t3 = t2.(node) <- ({
    freq_or_code = (t2.[ir]).freq_or_code `U16.add` (t2.[ir]).freq_or_code;
    dad_or_len = U16.uint_to_t node;
  }) in
  admit();
  // lemma_wf_forest_symbols_disjoint ts' ts'.heap_max 1;

  let heap_max' = ts'.heap_max - 1 in
  let heap' = upd ts'.heap heap_max' (U32.uint_to_t ir) in
 
  let ts'' = {
    ts' with
    heap = heap';
    heap_max = heap_max';
    forest = upd ts'.forest node t';
    depth = ts'.depth.(node) <- (U8.uint_to_t dt');
    tree = t3;
  } in
  pqdownheap ts'' 1ul
