module Spec.Heap

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Yazi.Tree.Types
open Yazi.Deflate.Constants
include Spec.Heap.Lemmas

/// Live tree states definition.
let tree_state_live (h: HS.mem) (ts: tree_state_t) =
  (* The sorting context pointer should be live and its length should be one. *)
  CB.live h ts.ctx /\ B.g_is_null (CB.as_mbuf ts.ctx) == false /\ CB.length ts.ctx == 1 /\
  (let ctx' = (CB.as_seq h ts.ctx).[0] in
  B.live h ctx'.state /\
  (let heap_len = U32.v (B.as_seq h ctx'.state).[0] in
  let heap_max = U32.v (B.as_seq h ctx'.state).[1] in
  let heap = B.as_seq h ctx'.heap in
  let tree = B.as_seq h ctx'.tree in
  let depth = B.as_seq h ctx'.depth in
  (* All three buffers should be live and disjoint with each other. *)
  B.live h ctx'.heap /\ B.live h ctx'.tree /\ B.live h ctx'.depth /\
  ~ (B.g_is_null ctx'.heap) /\ ~ (B.g_is_null ctx'.tree) /\ ~ (B.g_is_null ctx'.depth) /\

  (let ctx = CB.as_mbuf ts.ctx in
  B.disjoint ctx ctx'.state /\ B.disjoint ctx ctx'.tree /\ B.disjoint ctx ctx'.heap /\
  B.disjoint ctx ctx'.depth /\ B.disjoint ctx'.state ctx'.tree /\
  B.disjoint ctx'.state ctx'.heap /\ B.disjoint ctx'.state ctx'.depth /\
  B.disjoint ctx'.tree ctx'.heap /\ B.disjoint ctx'.tree ctx'.depth /\
  B.disjoint ctx'.heap ctx'.depth) /\

  (* The length of the tree buffer should equal to the tree_len. *)
  B.length ctx'.tree == Ghost.reveal ts.tree_len /\
  Seq.length ts.forest == Ghost.reveal ts.tree_len))

type live_tree_state (h: HS.mem) = s: tree_state_t{
  tree_state_live h s
}

/// Convert the C struct to specification record type.
unfold let g_tree_state (h: HS.mem) (ts: live_tree_state h): GTot (res: tree_state_wf{
  let ctx = (CB.as_seq h ts.ctx).[0] in
  res.heap_len == U32.v (B.as_seq h ctx.state).[0] /\
  res.heap_max == U32.v (B.as_seq h ctx.state).[1] /\
  res.tree_len == Ghost.reveal ((ts <: tree_state_t).tree_len)
}) =
  let ctx = (CB.as_seq h ts.ctx).[0] in {
    heap = B.as_seq h ctx.heap;
    tree = B.as_seq h ctx.tree;
    depth = B.as_seq h ctx.depth;
    heap_len = U32.v (B.as_seq h ctx.state).[0];
    heap_max = U32.v (B.as_seq h ctx.state).[1];
    tree_len = Ghost.reveal (ts <: tree_state_t).tree_len;
    forest = Ghost.reveal (ts <: tree_state_t).forest;
  }

/// Getter for heap_len and heap_max.
unfold let get_heap_len (h: HS.mem) (ts: live_tree_state h) =
  (g_tree_state h ts).heap_len

unfold let get_heap_max (h: HS.mem) (ts: live_tree_state h) =
  (g_tree_state h ts).heap_max
  
/// Pre-condition before i is inserted to the heap.
let insertion_pre_cond (ts: heap_elems_wf_ts) (root i hole: U32.t) =
  let open U32 in
  let heap = ts.heap in
  is_tree_index ts i /\
  is_internal_index ts root /\
  U32.v root <= U32.v hole /\ U32.v hole <= ts.heap_len /\
  heap_not_empty ts /\
    
  (* heap.[v hole] `smaller` i *)
  smaller ts heap.[U32.v hole] i /\

  (* Initial state, elements after root form a partial heap and i is in the root. *)
  (root == hole ==> partial_wf ts (root +^ 1ul) /\ heap.[v root] == i) /\

  (* Intermediate state, elements start from root form a partial heap.
     The element i has not been inserted to the partial heap. *)
  (v root < v hole ==> partial_wf ts root)

/// Determine the smallest element among i, heap[hole * 2], and heap[hole * 2 + 1]
/// (if the right child of hole exists). If i is the smallest element, then we can
/// insert i into heap[hole] because heap[hole / 2] == heap[hole] or hole == root.
let smallest (ts: heap_elems_wf_ts) (root i hole: U32.t): Ghost U32.t 
  (requires
    insertion_pre_cond ts root i hole /\
    U32.v hole <= ts.heap_len / 2)
  (ensures fun res ->
    let res = U32.v res in
    let root = U32.v root in
    let hole = U32.v hole in
    let heap = ts.heap in
    let smaller = smaller ts in

    (* The returned result should be zero or hole's child.*)
    res <= ts.heap_len /\
    (res == 0 \/ res == hole * 2 \/ res == hole * 2 + 1) /\

    (* If the result is zero then i is the smallest element among i, the left
       child of hole, and the right child of hole (if it exists). *)
    (let k = if res = 0 then i else heap.[res] in
    (* The index should be the smallest one among the three indexes. *)
    k `smaller` i /\
    k `smaller` heap.[hole * 2] /\
    (hole * 2 + 1 <= ts.heap_len ==> k `smaller` heap.[hole * 2 + 1]) /\
    
    (root == hole ==> k `smaller` heap.[hole]) /\
    (root < hole ==> heap.[hole] `smaller` k) /\
    res > 0 ==> res > hole)) =
  let open U32 in
  let smaller = smaller ts in
  let heap = ts.heap in
  let l = hole *^ 2ul in let r = l +^ 1ul in
  let le = heap.[v l] in
  
  if v r > ts.heap_len then
    if i `smaller` le then 0ul else l
  else
    let re = heap.[v r] in
    if i `smaller` le then
      if i `smaller` re then 0ul else r
    else
      if le `smaller` re then l else r

/// Count invariant during the do_pqdownheap iteration. After the iteration,
/// this invariant will not hold and partial_wf will hold.
let count_inv (h1 h2: seq U32.t) (root i hole: U32.t) =
  let root = U32.v root in let hole = U32.v hole in
  (* h1 is the initial heap and the root of h1 is the element to be inserted to
     the heap.*)
  length h1 == length h2 /\
  root <= hole /\ hole < length h1 /\

  (* At the beginning, the new element is in the root. *)
  h1.[root] == i /\

  (* If we haven't done anything on h2, they should be the same.*)
  (hole == root ==> h1 == h2) /\
  
  (hole <> root ==> 
    (* Intermediate state. *)
    (h2.[hole] <> h1.[root] ==>
      (* The count of the root element in h2 is one less than h1 because h2.[root]
         is replaced with a smaller child. *)
      count h1.[root] h2 + 1 == count h1.[root] h1 /\
      (* Conversely, since h2.[hole / 2] == h2.[hole], so we have one more h2.[hole]
         in h2. *)
      count h2.[hole] h2 == count h2.[hole] h1 + 1) /\

    (* If they are equal, then there the previous do_pqdownheap iteration did not
       change the count of the root element. *)
    (h2.[hole] == h1.[root] ==> count h1.[root] h2 == count h1.[root] h1) /\
    
    (* For other elements, thier counts are unchanged. *)
    (forall (x: U32.t). {:pattern (count x h1) \/ (count x h2)}
      x <> h1.[root] /\ x <> h2.[hole] ==> count x h1 == count x h2))

let do_pqdownheap_pre (ts0 ts1: tree_state_wf) (root i hole: U32.t) =
  let heap0 = ts0.heap in
  let heap1 = ts1.heap in
  let heap_len = ts1.heap_len in
  heap_elems_wf ts0 /\ heap_elems_wf ts1 /\
  ts1 == {ts0 with heap = ts1.heap} /\
  insertion_pre_cond ts1 root i hole /\
  count_inv heap0 heap1 root i hole /\
  non_heap_unmodified heap0 heap1 heap_len /\
  (U32.v root == 1 ==> heap_sorted ts1 /\ sorted_lt_heap ts1)

#push-options "--z3refresh --z3rlimit 512 --fuel 0 --ifuel 0 --z3seed 1"
let rec do_pqdownheap
  (ts0 ts1: heap_elems_wf_ts)
  (root: U32.t{0 < U32.v root}) (i hole: U32.t):
  Ghost (partial_wf_ts root)
  (requires do_pqdownheap_pre ts0 ts1 root i hole)
  (ensures fun ts2 ->
     ts2 == {ts1 with heap = ts2.heap} /\
     non_heap_unmodified ts1.heap ts2.heap ts2.heap_len /\
     permutation U32.t ts0.heap ts2.heap /\
     permutation U32.t (heap_seq ts0) (heap_seq ts2) /\
     sorted_seq ts1 == sorted_seq ts2 /\
     (U32.v root == 1 ==> heap_wf ts2))
  (decreases ts1.heap_len - U32.v hole) =
  let open U32 in
  if v hole > ts1.heap_len / 2 then
    {ts1 with heap = ts1.heap.(v hole) <- i}
  else
    let s = smallest ts1 root i hole in
    if s = 0ul then
      {ts1 with heap = ts1.heap.(v hole) <- i}
    else
      let ts1' = {ts1 with heap = ts1.heap.(v hole) <- ts1.heap.[v s]} in
      do_pqdownheap ts0 ts1' root i s
#pop-options

unfold let pqdownheap_pre (ts: tree_state_wf) (i: U32.t{is_internal_index ts i}) =
  heap_elems_wf ts /\
  partial_wf ts (i `U32.add` 1ul) /\
  (U32.v i == 1 ==> heap_sorted ts /\ sorted_lt_heap ts)

/// Move the root element to keep heap's invariant.
let pqdownheap (ts: tree_state_wf) (i: U32.t{is_internal_index ts i}):
  Ghost (partial_wf_ts i)
  (requires pqdownheap_pre ts i)
  (ensures fun ts' ->
    ts' = {ts with heap = ts'.heap} /\
    non_heap_unmodified ts.heap ts'.heap ts.heap_len /\
    permutation U32.t ts.heap ts'.heap /\
    permutation U32.t (heap_seq ts) (heap_seq ts') /\
    sorted_seq ts == sorted_seq ts' /\
    permutation U32.t (element_seq ts) (element_seq ts') /\
    (U32.v i == 1 ==> heap_wf ts')) =
  let ts' = do_pqdownheap ts ts i ts.heap.[U32.v i] i in
  lemma_append_count (heap_seq ts) (sorted_seq ts);
  lemma_append_count (heap_seq ts') (sorted_seq ts');
  ts'

#push-options "--z3refresh --z3rlimit 256 --z3seed 11 --fuel 1 --ifuel 1"
/// Move the root of the heap to the sorted area.
let pqremove (ts: heap_wf_ts):
  Ghost heap_wf_ts
  (requires ts.heap_len > 1)
  (ensures fun ts' -> pqremove_post ts ts') =
  lemma_heap_wf_pqremove ts;
  let ts1 = {
    ts with
    heap = upd (upd ts.heap (ts.heap_max - 1) ts.heap.[1]) 1 ts.heap.[ts.heap_len];
    heap_len = ts.heap_len - 1;
    heap_max = ts.heap_max - 1;
  } in
  assert(sorted_seq ts1 `equal` (cons ts.heap.[1] (sorted_seq ts)));
  if ts1.heap_len >= 2 then begin
    let ts2 = pqdownheap ts1 1ul in
    assert(ts1.heap.[ts1.heap_max] == ts2.heap.[ts2.heap_max]);
    lemma_append_count (create 1 ts1.heap.[ts1.heap_max]) (heap_seq ts1);
    lemma_append_count (create 1 ts2.heap.[ts2.heap_max]) (heap_seq ts2);
    lemma_trans_perm
      (heap_seq ts)
      (cons ts1.heap.[ts1.heap_max] (heap_seq ts1))
      (cons ts2.heap.[ts2.heap_max] (heap_seq ts2))
      0 (ts.heap_len);
    ts2
  end else
    ts1
#pop-options
