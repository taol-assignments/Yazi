module Spec.Heap.Lemmas

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Yazi.Tree.Types
open Yazi.Deflate.Constants

/// Well-formed tree state. We don't use the tree_state type in the following code.
type tree_state_wf = ts: tree_state{
  length ts.heap == U32.v heap_size /\
  length ts.tree == ts.tree_len /\
  length ts.forest == ts.tree_len /\
  length ts.depth == U32.v heap_size /\
  ts.tree_len <= U32.v heap_size
}

/// The heap indexes: heap_len and heap_max are well-formed.
let heap_indexes_wf (ts: tree_state) =
  ts.heap_len < ts.heap_max /\ ts.heap_max <= U32.v heap_size

/// The heap area is not empty.
unfold let heap_not_empty (ts: tree_state_wf) = 0 < ts.heap_len

/// The sorted area is empty.
unfold let sorted_not_empty (ts: tree_state_wf) = ts.heap_max < U32.v heap_size

/// Get the sorted area sequence.
let sorted_seq (ts: tree_state_wf): Ghost (Seq.seq U32.t)
  (requires ts.heap_max <= U32.v heap_size)
  (ensures fun s -> Seq.length s == U32.v heap_size - ts.heap_max) =
  Seq.slice ts.heap ts.heap_max (U32.v heap_size)

/// Get the heap area sequence.
let heap_seq (ts: tree_state_wf): Ghost (Seq.seq U32.t)
  (requires heap_not_empty ts /\ heap_indexes_wf ts)
  (ensures fun s -> Seq.length s == ts.heap_len) =
  Seq.slice ts.heap 1 (ts.heap_len + 1)

/// Get the concatenation of the heap area and sorted area.
let element_seq (ts: tree_state_wf): Ghost (Seq.seq U32.t)
  (requires heap_not_empty ts /\ heap_indexes_wf ts)
  (ensures fun s ->
    Seq.length s == ts.heap_len + U32.v heap_size - ts.heap_max) =
  heap_seq ts @| sorted_seq ts

/// The heap stores the well-formed elements. A heap's elements are well-formed if
/// all elements in the heap less than tree_len and heap_size.
let heap_elems_wf (ts: tree_state_wf) =
  heap_indexes_wf ts /\
  (forall i.
    0 < i /\ i <= ts.heap_len \/ ts.heap_max <= i /\ i < U32.v heap_size ==>
    U32.v ts.heap.[i] < ts.tree_len /\ U32.v ts.heap.[i] < 2 * U32.v l_codes + 1)

type heap_elems_wf_ts = ts: tree_state_wf{heap_elems_wf ts}

/// Tree index can be used to index on the tree and depth array.
let is_tree_index (ts: heap_elems_wf_ts) (i: U32.t) = U32.v i < ts.tree_len
type tree_index (ts: heap_elems_wf_ts) = i: U32.t{is_tree_index ts i}

/// Tree comparison function. This function is a total order relation.
let smaller (ts: heap_elems_wf_ts) (i j: tree_index ts): GTot bool =
  let open U32 in
  let fi = U16.v (ts.tree.[v i]).freq_or_code in
  let fj = U16.v (ts.tree.[v j]).freq_or_code in
  fi < fj ||
  (fi = fj && U8.v ts.depth.[v i] < U8.v ts.depth.[v j]) ||
  (fi = fj && U8.v ts.depth.[v i] = U8.v ts.depth.[v j] && v i <= v j)

/// Partial well-formed heap. All elements whose index is large than i should
/// smaller than their children.
let partial_wf (ts: tree_state_wf) (i: U32.t{0 < U32.v i}) =
  heap_elems_wf ts /\
  (let smaller = smaller ts in
  let heap = ts.heap in
  forall (k: nat). U32.v i <= k /\ k <= ts.heap_len / 2 ==> (
    (heap.[k] `smaller` heap.[k * 2]) /\
    (k * 2 + 1 <= ts.heap_len ==> heap.[k] `smaller` heap.[k * 2 + 1])))

type partial_wf_ts (root: U32.t{0 < U32.v root}) = ts: tree_state_wf{
  partial_wf ts root
}

/// Determine if the index is a non-leaf index in the heap.
let is_internal_index (ts: tree_state_wf) (i: U32.t) =
  0 < U32.v i /\ U32.v i <= ts.heap_len / 2

/// Non-heap areas are not modified.
let non_heap_unmodified (h1 h2: seq U32.t) (heap_len: nat) =
  forall i. {:pattern (h1.[i]) \/ (h2.[i])} (i = 0 \/ i > heap_len) ==> h1.[i] == h2.[i]

/// The elements in the sorted area are sorted.
let rec heap_sorted' (ts: heap_elems_wf_ts) (i: nat{
  ts.heap_max <= i /\ i <= U32.v heap_size
}): GTot bool
  (decreases U32.v heap_size - i) =
  let heap = ts.heap in
  if U32.v heap_size - i <= 1 then
    true
  else if smaller ts heap.[i + 1] heap.[i] then
    heap_sorted' ts (i + 1)
  else
    false

let heap_sorted (ts: heap_elems_wf_ts) = heap_sorted' ts ts.heap_max

/// The first element in the sorted area is smaller than all elements in the heap.
let sorted_lt_heap (ts: heap_elems_wf_ts) =
  sorted_not_empty ts ==> (forall i. 1 <= i /\ i <= ts.heap_len ==>
    smaller ts ts.heap.[ts.heap_max] ts.heap.[i])

/// Heap well-formed tree status. The heap is complete well-formed, which root
/// element is the smallest element in the heap area. Elements in the sorted area
/// are sorted as well, and the tree status should satisfy with sorted_lt_heap as
/// well.
let heap_wf (ts: tree_state_wf) =
  partial_wf ts 1ul /\ heap_sorted ts /\ heap_not_empty ts /\ sorted_lt_heap ts
  
type heap_wf_ts = ts: tree_state_wf{heap_wf ts}

/// At the end of the do_pqdownheap call, the two heap areas of ts0 and ts1 should
/// be a permutation after the assignment.
private val lemma_heap_seq_upd_perm:
    ts0: heap_elems_wf_ts{heap_not_empty ts0}
  -> ts1: heap_elems_wf_ts{ts1 == {ts0 with heap = ts1.heap}}
  -> Lemma
  (requires
    permutation U32.t ts0.heap ts1.heap /\
    non_heap_unmodified ts0.heap ts1.heap ts0.heap_len)
  (ensures permutation U32.t (heap_seq ts0) (heap_seq ts1))
  [SMTPat (permutation U32.t (heap_seq ts0) (heap_seq ts1))]

private val lemma_non_heap_unmodified:
    ts0: heap_elems_wf_ts
  -> ts1: heap_elems_wf_ts
  -> Lemma
  (requires
    ts1 == {ts0 with heap = ts1.heap} /\
    non_heap_unmodified ts0.heap ts1.heap ts0.heap_len /\
    heap_sorted ts0)
  (ensures heap_sorted ts1 /\ sorted_seq ts0 == sorted_seq ts1)
  [SMTPatOr [
    [SMTPat (heap_sorted ts0); SMTPat (heap_sorted ts1)];
    [SMTPat (sorted_seq ts0); SMTPat (sorted_seq ts1)]
  ]]

/// If a heap is well-formed, its elements should not larger than the root.
val lemma_heap_wf: ts: partial_wf_ts 1ul -> j: pos{j <= ts.heap_len} -> Lemma
  (ensures smaller ts ts.heap.[1] ts.heap.[j])

let lemma_heap_wf_forall (ts: partial_wf_ts 1ul): Lemma
  (ensures forall j. 0 < j /\ j <= ts.heap_len ==>
    smaller ts ts.heap.[1] ts.heap.[j]) =
  let open FStar.Classical in
  forall_intro (move_requires (lemma_heap_wf ts))

/// Move the root element from the heap area to the top of sorted area will keep
/// area sorted.
val lemma_heap_wf_pqremove: ts: heap_wf_ts -> Lemma
  (requires ts.heap_len > 1)
  (ensures (
    let ts' = {
      ts with
      heap = upd (upd ts.heap (ts.heap_max - 1) ts.heap.[1]) 1 ts.heap.[ts.heap_len];
      heap_max = ts.heap_max - 1;
      heap_len = ts.heap_len - 1;
    } in
    heap_sorted ts' /\
    sorted_lt_heap ts' /\
    partial_wf ts' 2ul /\
    permutation U32.t (heap_seq ts) (cons ts'.heap.[ts'.heap_max] (heap_seq ts')) /\
    permutation U32.t (element_seq ts) (element_seq ts')))

let pqremove_post (ts: heap_wf_ts) (ts': heap_wf_ts): Pure Type0
  (requires ts.heap_len > 1)
  (ensures fun _ -> True) =
  ts' == {
    ts with
    heap = ts'.heap;
    heap_len = ts.heap_len - 1;
    heap_max = ts.heap_max - 1;
  } /\
  heap_not_empty ts' /\
  sorted_not_empty ts' /\
  sorted_seq ts' `equal` (cons ts.heap.[1] (sorted_seq ts)) /\
  permutation U32.t (heap_seq ts) (cons ts'.heap.[ts'.heap_max] (heap_seq ts')) /\
  permutation U32.t (element_seq ts) (element_seq ts') /\
  (forall k. k >= ts.heap_len ==> (element_seq ts).[k] == (element_seq ts').[k])
