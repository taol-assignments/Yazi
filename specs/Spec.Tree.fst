module Spec.Tree

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas

open FStar.Seq
open Lib.Seq
open Yazi.Tree.Types
open Yazi.Deflate.Constants

include Spec.Heap
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
    ts.tree.[il] with
    dad_or_len = U16.uint_to_t node;
  }) in
 
  let ir = U32.v ts.heap.[1] in
  let hr = U8.v ts.depth.[ir] in
  let r = ts.forest.[ir] in
  let t2 = t1.(ir) <- ({
    ts.tree.[ir] with
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
  assert(freq_corr ts 1 /\ freq_corr ts ts.heap_max);
  assert(freq_corr ts' ts'.heap_max /\ freq_corr ts' ts.heap_max);
  assert(freq t' == U16.v (t3.[il]).freq_or_code + U16.v (t3.[ir]).freq_or_code);
  lemma_pqmerge_main ts node ts' t';
  ts'

#set-options "--z3refresh --z3rlimit 1024 --z3seed 6 --fuel 0 --ifuel 0 --query_stats"
let build_tree_term (ts: forest_wf_ts) (node: nat):
  Ghost (partial_wf_ts 2ul)
  (requires build_tree_pre ts node)
  (ensures fun ts' -> build_tree_term_post ts node ts') =
  lemma_pqremove_forest ts node;
  let ts1 = pqremove ts in
  let hs = heap_seq ts in
  let hs1 = intermediate_fseq ts1 in
  lemma_forest_freq_perm ts hs ts1 hs1;
  lemma_forest_symbols_perm ts hs ts1 hs1;
  let ts' = pqmerge ts1 node in
  calc (==) {
    ts'.heap_max + 2;
    =={}
    ts1.heap_max - 1 + 2;
    =={}
    ts.heap_max - 1 - 1 + 2;
    =={Math.Lemmas.subtraction_is_distributive ts.heap_max 1 1}
    ts.heap_max - (1 + 1) + 2;
    =={}
    ts.heap_max - 2 + 2;
    =={}
    ts.heap_max;
  };
  ts'

#set-options "--z3seed 1"
let build_tree_rec (ts: forest_wf_ts) (node: nat):
  Ghost forest_wf_ts
  (requires build_tree_pre ts node /\ 2 < ts.heap_len)
  (ensures fun ts' ->
    let hs = heap_seq ts in
    let hs' = heap_seq ts' in
    forest_freq ts hs == forest_freq ts' hs' /\
    permutation nat (forest_symbols ts hs) (forest_symbols ts' hs') /\
    build_tree_pre ts' (node + 1)) =
  let ts1 = build_tree_term ts node in
  let ts2 = pqdownheap ts1 1ul in
  lemma_build_tree_rec ts ts1 ts2 node;
  ts2

let rec build_tree (ts: forest_wf_ts) (node: nat):
  Ghost forest_wf_ts
  (requires build_tree_pre ts node)
  (ensures fun ts' -> build_tree_post ts node ts')
  (decreases ts.heap_len) =
  if 2 < ts.heap_len then
    let ts1 = build_tree_rec ts node in
    build_tree ts1 (node + 1)
  else
    build_tree_term ts node

#push-options "--fuel 1 --ifuel 1"
let rec insert_symbols (ts: heap_elems_wf_ts) (i: symbol_index ts):
  Ghost heap_elems_wf_ts
  (requires insert_symbols_pre ts i)
  (ensures fun ts' -> insert_symbols_post ts ts')
  (decreases ts.tree_len / 2 - i) =
  let ts' = if U16.v (ts.tree.[i]).freq_or_code > 0 then {
    ts with
    heap = ts.heap.(ts.heap_len + 1) <- U32.uint_to_t i;
    heap_len = ts.heap_len + 1
  } else
    ts
  in
  if i + 1 < ts.tree_len / 2 then begin
    if U16.v (ts.tree.[i]).freq_or_code > 0 then
      lemma_insert_symbols_rec ts i;
    insert_symbols ts' (i + 1)
  end else begin
    if U16.v (ts.tree.[i]).freq_or_code > 0 then
      lemma_insert_symbols_term ts i;
    ts'
  end
