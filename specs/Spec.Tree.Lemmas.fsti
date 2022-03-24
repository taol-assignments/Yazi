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

private unfold let child_in_sorted (ts: intermediate_ts) (i: heap_index ts{
  Node? ts.forest.[U32.v ts.heap.[i]]
}) =
  exists (j: heap_index ts).
    let t = ts.forest.[U32.v ts.heap.[i]] in
    j > i /\ j >= ts.heap_max /\ j + 1 < U32.v heap_size /\
    U32.v ts.heap.[j] == id (right t) /\
    U32.v ts.heap.[j + 1] == id (left t)

/// If the tree of ts.forest.[i'] is not a leaf, it should have two corresponding
/// children on the ts.tree array, and these children should in the sorted area.
private let child_corr (ts: intermediate_ts) (i: heap_index ts) =
  let i' = U32.v ts.heap.[i] in
  let t = ts.forest.[i'] in
  assert(id ts.forest.[U32.v ts.heap.[i]] == U32.v ts.heap.[i]);
  Node? t ==>
    ts.forest.[id (left t)] == left t /\ ts.forest.[id (right t)] == right t /\
    U16.v (ts.tree.[id (left t)]).dad_or_len == i' /\
    U16.v (ts.tree.[id (right t)]).dad_or_len == i' /\
    child_in_sorted ts i

private let parent_corr (ts: intermediate_ts) (i: heap_index ts) =
  let i' = U32.v (ts.heap).[i] in
  ts.heap_max <= i ==> (exists (j: heap_index ts{j < i}).
    U16.v (ts.tree.[i']).dad_or_len == U32.v ts.heap.[j])

unfold let tree_corr (ts: intermediate_ts) (i: heap_index ts) =
  child_corr ts i /\ parent_corr ts i

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
  (forall i. 1 <= i /\ i <= ts.heap_len ==>
    U16.v (ts.tree.[U32.v ts.heap.[i]]).dad_or_len == 0) /\
  (forall i. freq_corr ts i /\ tree_corr ts i)

type forest_wf_ts = ts: heap_wf_ts{is_forest_wf ts}

/// The node parameter is the upper bound of the node IDs in the forest. This
/// predicate is used in pqmerge() to construct new well-formed trees.
let is_max_id (ts: intermediate_ts) (node: nat) =
  node <= ts.tree_len /\
  (forall i. id ts.forest.[U32.v (element_seq ts).[i]] < node)

/// The intermediate forest node ID sequence after the pqremove call.
let intermediate_fseq (ts: heap_wf_ts{sorted_not_empty ts}) =
  cons ts.heap.[ts.heap_max] (heap_seq ts)

val lemma_forest_symbols_perm:
    ts0: heap_elems_wf_ts
  -> s0: tree_id_seq ts0
  -> ts1: heap_elems_wf_ts
  -> s1: tree_id_seq ts1
  -> Lemma
  (requires ts0.forest == ts1.forest /\ permutation U32.t s0 s1)
  (ensures permutation nat (forest_symbols ts0 s0) (forest_symbols ts1 s1))
  (decreases length s0)

/// Auxiliary lemmas for lemma_pqremove_forest and pqmerge_post.
let lemma_element_seq_tree_index (ts: heap_elems_wf_ts) (i: nat): Lemma
  (requires heap_not_empty ts /\ i < length (element_seq ts))
  (ensures is_tree_index ts (element_seq ts).[i])
  [SMTPat (element_seq ts).[i]] = ()

let lemma_intermediate_fseq_tree_index (ts: heap_wf_ts): Lemma
  (requires sorted_not_empty ts)
  (ensures (
    let cs = intermediate_fseq ts in
    forall i. {:pattern cs.[i]} is_tree_index ts cs.[i]))
  [SMTPat (intermediate_fseq ts)] = ()

let lemma_heap_seq_tree_index (ts: heap_elems_wf_ts): Lemma
  (requires heap_not_empty ts)
  (ensures (
    let hs = heap_seq ts in
    forall i. {:pattern hs.[i]} is_tree_index ts hs.[i]))
  [SMTPat (heap_seq ts)] = ()

/// For all root nodes in the heap area, and the node whose ID is not smaller than
/// the maximum available node, their parent IDs should be zero.
let dad_zero (ts: heap_elems_wf_ts) (node: nat) =
  (forall i. 1 <= i /\ i <= ts.heap_len ==>
    U16.v (ts.tree.[U32.v ts.heap.[i]]).dad_or_len == 0) /\
  (forall i. node <= i ==> U16.v (ts.tree.[i]).dad_or_len == 0)

let pqmerge_pre (ts: heap_wf_ts) (node: nat) =
  sorted_not_empty ts /\ node < ts.tree_len /\ is_max_id ts node /\
  ts.heap_len < ts.heap_max - 1 /\
  (let s = intermediate_fseq ts in
  let ff = forest_freq ts s in
  0 < ff /\ ff < pow2 15 /\
  no_dup (element_seq ts) /\
  no_dup (forest_symbols ts s) /\
  dad_zero ts node /\
  U16.v (ts.tree.[U32.v ts.heap.[ts.heap_max]]).dad_or_len == 0 /\
  (forall (i: heap_index ts).
    freq_corr ts i /\
    (ts.heap_max == i ==> child_corr ts i) /\
    (ts.heap_max <> i ==> tree_corr ts i)))

val lemma_is_max_id_map: ts: heap_wf_ts -> node: nat -> i: heap_index ts -> Lemma
  (requires pqmerge_pre ts node)
  (ensures U32.v ts.heap.[i] < node)

val lemma_forest_freq_perm:
    ts0: heap_elems_wf_ts
  -> s0: tree_id_seq ts0
  -> ts1: heap_elems_wf_ts
  -> s1: tree_id_seq ts1
  -> Lemma
  (requires ts0.forest == ts1.forest /\ permutation U32.t s0 s1)
  (ensures forest_freq ts0 s0 == forest_freq ts1 s1)
  (decreases length s0)

/// The pre-condition of pqmerge is hold after the call of pqremove.
val lemma_pqremove_forest: ts: forest_wf_ts -> node: nat -> Lemma
  (requires
    1 < ts.heap_len /\ ts.heap_len < ts.heap_max - 1 /\
    node < ts.tree_len /\ is_max_id ts node /\
    dad_zero ts node)
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
let pqmerge_post (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf): Pure Type0
  (requires pqmerge_pre ts node)
  (ensures fun _ -> True) =
  (* The heap should be partial well-formed, and the root element may not be the
     minimum element. *)
  ts'.heap_len == ts.heap_len /\
  partial_wf ts' 2ul /\ heap_not_empty ts' /\
  heap_sorted ts' /\ sorted_not_empty ts' /\ sorted_lt_heap ts' /\
  ts'.heap_max == ts.heap_max - 1 /\
  ts'.tree_len == ts.tree_len /\
  
  (let (es, es') = (element_seq ts, element_seq ts') in
  let n = es'.[0] in
  let hs = intermediate_fseq ts in
  let t' = ts'.forest.[U32.v n] in
  let l = ts'.forest.[U32.v ts'.heap.[ts.heap_max]] in
  let r = ts'.forest.[U32.v ts'.heap.[ts'.heap_max]] in

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
  id t' == node /\
  is_max_id ts' (node + 1) /\
  freq l + freq r > 0 /\
  t' == Node l node (freq l + freq r) r /\

  (* All nodes whose ID are larger than node parameter should be zero. *)
  dad_zero ts' (node + 1) /\

  (* Only a new tree is created. *)
  (forall i. i <> node ==> ts.forest.[i] == ts'.forest.[i]) /\

  ts.heap.[1] == ts'.heap.[ts'.heap_max] /\
  (forall i. i <> 1 /\ i <> ts'.heap_max ==> ts'.heap.[i] == ts.heap.[i]) /\

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

#pop-options
let rec node_count (t: tree): Tot nat  =
  match t with
  | Node l _ _ r -> 1 + node_count l + node_count r
  | _ -> 0

let rec leaf_count (t: tree): Tot nat  =
  match t with
  | Node l _ _ r -> leaf_count l + leaf_count r
  | _ -> 1

val lemma_node_leaf_count: t: tree -> Lemma
  (ensures node_count t == leaf_count t - 1)
  [SMTPatOr [[SMTPat (node_count t)]; [SMTPat (leaf_count t)]]]

private let rec forest_node_count' (ts: intermediate_ts) (i: pos{i <= ts.heap_len}): Tot nat =
  let t = ts.forest.[U32.v ts.heap.[i]] in
  match i with
  | 1 -> node_count t
  | _ -> node_count t + forest_node_count' ts (i - 1)

unfold let forest_node_count (ts: intermediate_ts) = forest_node_count' ts ts.heap_len

private let rec forest_leaf_count' (ts: intermediate_ts) (i: pos{i <= ts.heap_len}): Tot nat =
  let t = ts.forest.[U32.v ts.heap.[i]] in
  match i with
  | 1 -> leaf_count t
  | _ -> leaf_count t + forest_leaf_count' ts (i - 1)

unfold let forest_leaf_count (ts: intermediate_ts) = forest_leaf_count' ts ts.heap_len

val lemma_forest_node_leaf_count: ts: intermediate_ts -> Lemma
  (ensures forest_node_count ts == forest_leaf_count ts - ts.heap_len)
  [SMTPatOr [[SMTPat (forest_node_count ts)]; [SMTPat (forest_leaf_count ts)]]]

let build_tree_pre (ts: forest_wf_ts) (node: nat): Tot Type0 =
  let flc = forest_leaf_count ts in
  let fnc = forest_node_count ts in
  ts.heap_len > 1 /\
  flc <= ts.tree_len / 2 /\
  U32.v heap_size - ts.heap_max + ts.heap_len == flc + fnc /\
  node == ts.tree_len / 2 + fnc + 1 /\
  node < ts.tree_len /\
  is_max_id ts node /\
  dad_zero ts node

#push-options "--z3refresh --z3seed 17 --z3rlimit 256 --fuel 0 --ifuel 0 --query_stats"
let build_tree_post (ts: forest_wf_ts) (node: nat) (ts': forest_wf_ts): Pure Type0
  (requires build_tree_pre ts node)
  (ensures fun _ -> True) =
  let hs = heap_seq ts in
  let hs' = heap_seq ts' in
  ts'.heap_len == 1 /\

  permutation nat (forest_symbols ts hs) (forest_symbols ts' hs') /\
  forest_freq ts hs == forest_freq ts' hs'

let build_tree_term_post (ts: forest_wf_ts) (node: nat) (ts': partial_wf_ts 2ul): Pure Type0
  (requires build_tree_pre ts node)
  (ensures fun _ -> True) =
    ts'.tree_len == ts.tree_len /\
    ts'.heap_len + 1 == ts.heap_len /\
    ts'.heap_max + 2 == ts.heap_max /\
    heap_not_empty ts' /\ is_forest_wf ts' /\
    heap_sorted ts' /\ sorted_lt_heap ts' /\
    is_max_id ts' (node + 1) /\
    dad_zero ts' (node + 1) /\
    (let hs = heap_seq ts in let hs' = heap_seq ts' in
    forest_freq ts hs == forest_freq ts' hs' /\
    permutation nat (forest_symbols ts hs) (forest_symbols ts' hs'))

val lemma_build_tree_rec:
    ts0: forest_wf_ts
  -> ts1: partial_wf_ts 2ul
  -> ts2: heap_wf_ts
  -> node: nat
  -> Lemma
  (requires
    2 < ts0.heap_len /\
    build_tree_pre ts0 node /\
    build_tree_term_post ts0 node ts1 /\
    ts2 == pqdownheap ts1 1ul)
  (ensures (
    let hs0 = heap_seq ts0 in
    let hs2 = heap_seq ts2 in
    let flc2 = forest_leaf_count ts2 in
    let fnc2 = forest_node_count ts2 in
    is_forest_wf ts2 /\ is_max_id ts2 (node + 1) /\ dad_zero ts2 (node + 1) /\
    permutation nat (forest_symbols ts0 hs0) (forest_symbols ts2 hs2) /\
    forest_freq ts0 hs0 == forest_freq ts2 hs2 /\
    U32.v heap_size - ts2.heap_max + ts2.heap_len == flc2 + fnc2 /\
    node + 1 == ts2.tree_len / 2 + fnc2 + 1))

type symbol_index (tree: seq ct_data) = i: nat{i < length tree / 2}

/// The sum of frequencies of the symbols in the tree array.
let rec tree_symbols_freq (tree: seq ct_data) (i: symbol_index tree) : Tot nat =
  if i = 0 then
    U16.v (tree.[i]).freq_or_code 
  else
    U16.v (tree.[i]).freq_or_code + tree_symbols_freq tree (i - 1)

private let tree_heap_surjective (ts: heap_elems_wf_ts{heap_not_empty ts}) =
  forall (j: symbol_index ts.tree).
    U16.v (ts.tree.[j]).freq_or_code > 0 <==>
    mem (U32.uint_to_t j) (heap_seq ts)

/// The initial forest state before building the prefix-free code tree.
/// All elements in the forest are leaves, and they don't have parents.
private let forest_init_state (ts: heap_elems_wf_ts) =
  forall j.
    Leaf? ts.forest.[j] /\
    id ts.forest.[j] == j /\
    (U16.v (ts.tree.[j]).freq_or_code > 0 ==>
      freq ts.forest.[j] == U16.v (ts.tree.[j]).freq_or_code) /\
    (U16.v (ts.tree.[j]).freq_or_code == 0 ==>
      freq ts.forest.[j] == 1) /\
    U16.v (ts.tree.[j]).dad_or_len == 0

type max_code_t (#ts: heap_elems_wf_ts) (i: symbol_index ts.tree) = n: nat{
  (i > 0 ==> n < i) /\ (i == 0 ==> n == 0)
}

let insert_symbols_pre
  (ts: heap_elems_wf_ts) (i: symbol_index ts.tree) (max_code: max_code_t i) =
  let tsf = tree_symbols_freq ts.tree (ts.tree_len / 2 - 1) in
  ts.heap_len <= i /\ ts.heap_max == U32.v heap_size /\
  0 < tsf /\ tsf < pow2 15 /\
  forest_init_state ts /\
  (ts.heap_len == 0 /\ i > 0 ==> tree_symbols_freq ts.tree (i - 1) == 0) /\
  (heap_not_empty ts ==>
    forest_freq ts (heap_seq ts) == tree_symbols_freq ts.tree (i - 1) /\
    is_forest_wf ts /\
    length (forest_symbols ts (heap_seq ts)) == length (element_seq ts) /\
    (forall j. (forest_symbols ts (heap_seq ts)).[j] == U32.v (element_seq ts).[j]) /\
    (forall j. mem j (heap_seq ts) ==> U32.v j <= max_code) /\
    (forall (j: nat{j < i}).
      U16.v (ts.tree.[j]).freq_or_code > 0 <==>
      mem (U32.uint_to_t j) (heap_seq ts)))

let insert_symbols_post (ts: heap_elems_wf_ts) (res: (heap_elems_wf_ts & nat)) =
  let (ts', max_code) = res in
  ts' == {
    ts with
    heap = ts'.heap;
    heap_len = ts'.heap_len
  } /\
  ts'.heap_len <= ts'.tree_len / 2 /\
  forest_init_state ts' /\
  (heap_not_empty ts' ==> 
    is_forest_wf ts' /\
    tree_heap_surjective ts' /\
    length (forest_symbols ts' (heap_seq ts')) == length (element_seq ts') /\
    (forall j. mem j (heap_seq ts') ==> U32.v j < ts'.tree_len / 2) /\
    (forall j. mem j (heap_seq ts') ==> U32.v j <= max_code))

val lemma_insert_symbols_rec:
    ts: heap_elems_wf_ts
  -> i: symbol_index ts.tree
  -> max_code: max_code_t i
  -> Lemma
  (requires
    insert_symbols_pre ts i max_code /\
    i + 1 < ts.tree_len / 2 /\
    U16.v (ts.tree.[i]).freq_or_code > 0)
  (ensures (
    let ts' = {
      ts with
      heap = ts.heap.(ts.heap_len + 1) <- U32.uint_to_t i;
      heap_len = ts.heap_len + 1
    } in
    insert_symbols_pre ts' (i + 1) i
  ))

val lemma_insert_symbols_term:
    ts: heap_elems_wf_ts
  -> i: symbol_index ts.tree
  -> max_code: max_code_t i
  -> Lemma
  (requires
    insert_symbols_pre ts i max_code /\
    i + 1 = ts.tree_len / 2 /\
    U16.v (ts.tree.[i]).freq_or_code > 0)
  (ensures (
    let ts' = {
      ts with
      heap = ts.heap.(ts.heap_len + 1) <- U32.uint_to_t i;
      heap_len = ts.heap_len + 1
    } in
    insert_symbols_post ts (ts', i)
  ))

let sort_symbols_pre (ts: heap_elems_wf_ts) (i: U32.t{is_internal_index ts i}) =
  ts.heap_max == U32.v heap_size /\
  ts.heap_len <= ts.tree_len / 2 /\
  length (forest_symbols ts (heap_seq ts)) == length (element_seq ts) /\
  heap_not_empty ts /\ partial_wf ts (i `U32.add` 1ul) /\
  is_forest_wf ts /\ tree_heap_surjective ts /\ forest_init_state ts /\
  (forall j. mem j (heap_seq ts) ==> U32.v j < ts.tree_len / 2)

let sort_symbols_post (ts: heap_elems_wf_ts) (ts': forest_wf_ts) =
  ts' == {ts with heap = ts'.heap;} /\ tree_heap_surjective ts' /\
  build_tree_pre ts' (ts.tree_len / 2 + 1)

#set-options "--fuel 1 --ifuel 1"
val lemma_sort_symbols:
    ts: heap_elems_wf_ts
  -> i: U32.t{is_internal_index ts i}
  -> Lemma
  (requires sort_symbols_pre ts i)
  (ensures (
    let ts' = pqdownheap ts i in
    is_forest_wf ts' /\
    (1 < U32.v i ==> sort_symbols_pre (pqdownheap ts i) (i `U32.sub` 1ul)) /\
    (1 == U32.v i ==> sort_symbols_post ts (pqdownheap ts i))))

#set-options "--fuel 1 --ifuel 1"
let rec is_sub_tree (a b: wf_tree): Tot bool =
  match (a = b, a) with
  | (true, _) -> true
  | (_, Node l _ _ r) ->
    (match l = b || r = b with
    | true -> true
    | false -> is_sub_tree l b || is_sub_tree r b)
  | _ -> false

type sub_wf_tree (p: wf_tree) = t: wf_tree{is_sub_tree p t}

let rec sub_tree_depth (p: wf_tree) (c: sub_wf_tree p): Tot nat =
  match (p = c, p) with
  | (true, _) -> 0
  | (_, Node l _ _ r) ->
    match (l = c || r = c, is_sub_tree l c, is_sub_tree r c) with
    | (true, _, _) -> 1
    | (_, true, _) -> 1 + sub_tree_depth l c
    | _ -> 1 + sub_tree_depth r c

let is_parent_child (p c: wf_tree) = Node? p /\ (left p == c \/ right p == c)

let rec lemma_is_sub_tree_trans (t p c: wf_tree): Lemma
  (requires is_sub_tree t p /\ is_parent_child p c)
  (ensures is_sub_tree t c)
  [SMTPat (is_sub_tree t p); SMTPat (is_parent_child p c)] =
  match t = p with
  | true -> ()
  | _ ->
    match (is_sub_tree (left t) p, is_sub_tree (right t) p) with
    | (true, _) -> lemma_is_sub_tree_trans (left t) p c
    | _ -> lemma_is_sub_tree_trans (right t) p c

#set-options "--fuel 2 --ifuel 2"
let rec lemma_sub_tree_depth (t p c: wf_tree): Lemma
  (requires is_sub_tree t p /\ is_parent_child p c)
  (ensures sub_tree_depth t c == sub_tree_depth t p + 1) =
  match t = p with
  | true -> ()
  | _ -> 
    assume(is_sub_tree (left t) p <> is_sub_tree (right t) p);
    assume(left t <> c /\ right t <> c);
    match (is_sub_tree (left t) p, is_sub_tree (right t) p) with
    | (true, _) ->
      lemma_sub_tree_depth (left t) p c;
      lemma_is_sub_tree_trans (left t) p c
    | _ -> admit(); lemma_sub_tree_depth (right t) p c
