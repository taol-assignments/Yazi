module Spec.Tree.Lemmas

module Cast = FStar.Int.Cast
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Seq
open Lib.Seq
open Yazi.Deflate.Constants
open Yazi.Tree.Types
open Spec.Heap

noextract
type non_leaf = t: tree{Leaf? t == false}

unfold let left (t: non_leaf) =
  match t with
  | Node l _ _ _ -> l

unfold let right (t: non_leaf) =
  match t with
  | Node _ _ _ r -> r

type heap_index (ts: tree_state_wf) = i: nat{
  1 <= i /\ i <= ts.heap_len \/ ts.heap_max <= i /\ i < U32.v heap_size
}

let rec height (t: tree): Tot nat =
  match t with
  | Node l _ _ r ->
    if height l >= height r then
      1 + height l
    else
      1 + height r
  | Leaf _ _ -> 0

private type intermediate_ts = ts: heap_elems_wf_ts{
  heap_not_empty ts
}

/// The field freq_or_code is correspond to the root frequency of the tree.
let freq_corr (ts: heap_elems_wf_ts) (i: heap_index ts) =
  let i' = U32.v (ts.heap).[i] in
  U16.v (ts.tree.[i']).freq_or_code == freq ts.forest.[i']

/// If the tree of ts.forest.[i'] is not a leaf, it should have two corresponding
/// children on the ts.tree array, and these children should in the sorted area.
private (*unfold*) let child_corr (ts: intermediate_ts) (i: heap_index ts) =
  let i' = U32.v ts.heap.[i] in
  let t = ts.forest.[i'] in
  assert(id ts.forest.[U32.v ts.heap.[i]] == U32.v ts.heap.[i]);
  Node? t ==>
    ts.forest.[id (left t)] == left t /\ ts.forest.[id (right t)] == right t /\
    U16.v (ts.tree.[id (left t)]).dad_or_len == i' /\
    U16.v (ts.tree.[id (right t)]).dad_or_len == i'

private let parent_corr (ts: intermediate_ts) (i: heap_index ts) =
  let i' = U32.v (ts.heap).[i] in
  let dad = Cast.uint16_to_uint32 (ts.tree.[i']).dad_or_len in
  ts.heap_max <= i ==>
    mem dad (element_seq ts) /\
    index_of (element_seq ts) dad < i - (ts.heap_max - ts.heap_len)

private unfold let tree_corr (ts: intermediate_ts) (i: heap_index ts) =
  (* let t = ts.forest.[U32.v ts.heap.[i]] in
  id t == U32.v ts.heap.[i] /\ *) child_corr ts i /\ parent_corr ts i

type tree_id_seq (ts: heap_elems_wf_ts) = s: seq U32.t{
  forall i. {:pattern s.[i]} is_tree_index ts s.[i]
}

let rec forest_symbols (ts: heap_elems_wf_ts) (s: tree_id_seq ts): Tot (seq nat)
  (decreases length s) =
  if length s = 0 then
    empty #nat
  else
    symbols ts.forest.[U32.v s.[0]] @| forest_symbols ts (tail s)

let rec forest_freq (ts: heap_elems_wf_ts) (s: tree_id_seq ts): Tot nat
  (decreases length s) =
  if length s = 0 then
    0
  else
    freq ts.forest.[U32.v s.[0]] + forest_freq ts (tail s)

/// Tree state that have well-formed forest sequence. All sub trees in the
/// sorted area and the heap area have corresponding depth and tree structure.
let is_forest_wf (ts: intermediate_ts) =
  no_dup (element_seq ts) /\
  no_dup (forest_symbols ts (heap_seq ts)) /\
  0 < forest_freq ts (heap_seq ts) /\ forest_freq ts (heap_seq ts) < pow2 15 /\
  (forall i. freq_corr ts i /\ tree_corr ts i)

type forest_wf_ts = ts: heap_wf_ts{is_forest_wf ts}

/// The node parameter is the upper bound of the node IDs in the forest. This
/// predicate is used in pqmerge() to construct new well-formed trees.
let is_max_id (ts: intermediate_ts) (node: nat) =
  node <= ts.tree_len /\
  (forall i. id ts.forest.[U32.v (element_seq ts).[i]] < node)

val lemma_forest_symbols_perm:
    ts0: heap_elems_wf_ts
  -> s0: tree_id_seq ts0
  -> ts1: heap_elems_wf_ts
  -> s1: tree_id_seq ts1
  -> Lemma
  (requires ts0.forest == ts1.forest /\ permutation U32.t s0 s1)
  (ensures permutation nat (forest_symbols ts0 s0) (forest_symbols ts1 s1))
  (decreases length s0)

/// The intermediate forest node ID sequence after the pqremove call.
let intermediate_fseq (ts: heap_wf_ts{sorted_not_empty ts}) =
  cons ts.heap.[ts.heap_max] (heap_seq ts)

/// Auxiliary lemmas for lemma_pqremove_forest and pqmerge_post.
let lemma_element_seq_tree_index (ts: heap_elems_wf_ts) (i: nat): Lemma
  (requires heap_not_empty ts /\ i < length (element_seq ts))
  (ensures is_tree_index ts (element_seq ts).[i]) = ()

let lemma_intermediate_fseq_tree_index (ts: heap_wf_ts): Lemma
  (requires sorted_not_empty ts)
  (ensures (
    let cs = intermediate_fseq ts in
    forall i. {:pattern cs.[i]} is_tree_index ts cs.[i])) = ()

let lemma_heap_seq_tree_index (ts: heap_elems_wf_ts): Lemma
  (requires heap_not_empty ts)
  (ensures (
    let hs = heap_seq ts in
    forall i. {:pattern hs.[i]} is_tree_index ts hs.[i])) = ()

let pqmerge_pre (ts: heap_wf_ts) (node: nat) =
  sorted_not_empty ts /\ node < ts.tree_len /\ is_max_id ts node /\
  ts.heap_len < ts.heap_max - 1 /\
  (let s = intermediate_fseq ts in
  let ff = forest_freq ts s in
  0 < ff /\ ff < pow2 15 /\
  no_dup (element_seq ts) /\
  no_dup (forest_symbols ts s) /\
  (forall (i: heap_index ts).
    freq_corr ts i /\
    // id ts.forest.[U32.v ts.heap.[i]] == U32.v ts.heap.[i] /\
    (ts.heap_max == i ==> child_corr ts i) /\
    (ts.heap_max <> i ==> tree_corr ts i)))

val lemma_is_max_id_map: ts: heap_wf_ts -> node: nat -> i: heap_index ts -> Lemma
  (requires pqmerge_pre ts node)
  (ensures U32.v ts.heap.[i] < node)

/// The pre-condition of pqmerge is hold after the call of pqremove.
val lemma_pqremove_forest: ts: forest_wf_ts -> node: nat -> Lemma
  (requires
    1 < ts.heap_len /\ ts.heap_len < ts.heap_max - 1 /\
    node < ts.tree_len /\ is_max_id ts node)
  (ensures pqmerge_pre (pqremove ts) node)

val lemma_forest_freq_plus:
    ts: heap_elems_wf_ts
  -> i: nat{i < ts.heap_len + 1}
  -> j: nat{j < ts.heap_len + 1}
  -> Lemma
  (requires (
    i <> j /\
    heap_not_empty ts /\
    sorted_not_empty ts /\
    length (cons ts.heap.[ts.heap_max] (heap_seq ts)) > 1 /\
    (forall k. freq_corr ts k)))
  (ensures (
    let s = cons ts.heap.[ts.heap_max] (heap_seq ts) in
    U16.v (ts.tree.[U32.v s.[i]]).freq_or_code +
    U16.v (ts.tree.[U32.v s.[j]]).freq_or_code <=
    forest_freq ts s))

/// Post-condition of pqmerge. The resulting tree state's heap is partial well-formed.
/// The heap root is the newly added tree ID. It may not be the smallest element
/// in the heap.
#push-options "--z3refresh --z3seed 17 --z3rlimit 256 --fuel 0 --ifuel 0"
unfold let pqmerge_post (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf): Pure Type0
  (requires pqmerge_pre ts node)
  (ensures fun _ -> True) =
  (* The heap should be partial well-formed, and the root element may not be the
     minimum element. *)
  partial_wf ts' 2ul /\ heap_not_empty ts' /\
  heap_sorted ts' /\ sorted_not_empty ts' /\ sorted_lt_heap ts' /\
  
  (let (es, es') = (element_seq ts, element_seq ts') in
  let n = es'.[0] in
  let hs = intermediate_fseq ts in
  lemma_element_seq_tree_index ts' ts'.heap_len;
  lemma_intermediate_fseq_tree_index ts;
  lemma_heap_seq_tree_index ts';

  (* The forest symbols should be the permutation of the previous forest symbols,
     and the forest frequencies should be identical as well. *)
  forest_symbols ts hs == forest_symbols ts' (heap_seq ts') /\
  forest_freq ts hs == forest_freq ts' (heap_seq ts') /\

  (* The new node is in the new heap, not the old heap. *)
  count n es' == 1 /\ mem n es == false /\

  (* Trees in the old heap should be in the new heap as well. *)
  (forall m. m <> n ==> count m es' == count m es) /\

  (* The newly created tree's ID should equal to node, and all node ID in the
     tree sequence should smaller than node + 1. *)
  id ts'.forest.[U32.v n] == node /\ is_max_id ts' (node + 1) /\

  (forall i. freq_corr ts' i /\ tree_corr ts' i))

let pqmerge_no_dup_pre (ts: heap_elems_wf_ts) (i j: pos) =
  heap_not_empty ts /\
  sorted_not_empty ts /\
  no_dup (element_seq ts) /\
  no_dup (forest_symbols ts (cons ts.heap.[ts.heap_max] (heap_seq ts))) /\
  (i <= ts.heap_len \/ i == ts.heap_max) /\
  (j <= ts.heap_len \/ j == ts.heap_max) /\
  i <> j

/// The symbols of a union of two trees has no duplicate symbols.
val lemma_pqmerge_no_dup: ts: heap_elems_wf_ts -> i: pos -> j: pos -> Lemma
  (requires pqmerge_no_dup_pre ts i j)
  (ensures (
    let i' = U32.v ts.heap.[i] in
    let j' = U32.v ts.heap.[j] in
    no_dup (symbols ts.forest.[i'] @| symbols ts.forest.[j'])
  ))

let pqmerge_main_pre (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf) (t': wf_tree) =
  pqmerge_pre ts node /\
  node < ts.tree_len /\

  heap_not_empty ts' /\
  ts'.heap_len == ts.heap_len /\
  ts'.heap_max == ts.heap_max - 1 /\
  ts'.heap_len < ts'.heap_max /\
  ts'.tree_len == ts.tree_len /\

  ts'.heap.[1] == U32.uint_to_t node /\
  ts'.heap.[ts'.heap_max] == ts.heap.[1] /\
  (forall i. {:pattern (ts'.heap.[i]) \/ (ts.heap.[i])} i <> 1 /\ i <> ts'.heap_max ==>
    ts'.heap.[i] == ts.heap.[i]) /\

  Node? t' == true /\
  id (left t') == U32.v ts'.heap.[ts.heap_max] /\
  id (right t') == U32.v ts'.heap.[ts'.heap_max] /\

  (let lt = ts'.tree.[id (left t')] in
  let rt = ts'.tree.[id (right t')] in
  let l = ts'.forest.[U32.v ts'.heap.[ts.heap_max]] in
  let r = ts'.forest.[U32.v ts'.heap.[ts'.heap_max]] in

  U32.v (element_seq ts').[0] == node /\

  freq l + freq r > 0 /\
  t' == Node l node (freq l + freq r) r /\

  ts'.forest.[node] == t' /\
  freq t' == U16.v lt.freq_or_code + U16.v rt.freq_or_code /\
  (forall i. i <> node ==> ts'.forest.[i] == ts.forest.[i]) /\

  U16.v lt.dad_or_len == node /\
  U16.v rt.dad_or_len == node /\
  (forall i. i <> id (left t') /\ i <> id (right t') ==>
    (ts'.tree.[i]).dad_or_len == (ts.tree.[i]).dad_or_len) /\

  (forall i. i <> node ==> ts.depth.[i] == ts'.depth.[i]) /\

  U16.v (ts'.tree.[node]).freq_or_code == freq t' /\
  (forall i. i <> node ==> (ts'.tree.[i]).freq_or_code == (ts.tree.[i]).freq_or_code))

val lemma_pqmerge_main: 
    ts: heap_wf_ts
  -> node: nat
  -> ts': tree_state_wf
  -> t': wf_tree
  -> Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures pqmerge_post ts node ts')
