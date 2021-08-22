module Spec.Heap

module B = LowStar.Buffer
module HS = FStar.HyperStack
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Yazi.Tree.Types

let smaller (h: HS.mem)
  (tl: nat) (tree: B.lbuffer ct_data tl)
  (depth: tree_depth_t) (i j: U32.t) =
  let open U32 in
  let tree = B.as_seq h tree in
  let depth = B.as_seq h depth in
  v i < tl /\ v j < tl /\ v i < length depth /\ v j < length depth /\
  (let fi = U16.v (tree.[v i]).freq_or_code in
  let fj = U16.v (tree.[v j]).freq_or_code in
  (fi < fj \/ (fi == fj /\ U8.v depth.[v i] <= U8.v depth.[v j])))

let element_in_range (h: HS.mem) (heap: tree_heap_t) (hl: heap_len_t) (tl: nat) =
  let heap = B.as_seq h heap in
  (forall (j: pos). {:pattern heap.[j]} j <= U32.v hl ==> U32.v heap.[j] < tl)

let partial_well_formed
  (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: nat) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: heap_index_t hl) =
  let open U32 in
  let heap' = B.as_seq h heap in
  element_in_range h heap hl tl /\
  (forall (k: nat). (v i <= k /\ k <= v hl) ==> (
    (k * 2 <= v hl ==> smaller h tl tree depth heap'.[k] heap'.[k * 2]) /\
    (k * 2 + 1 <= v hl ==> smaller h tl tree depth heap'.[k] heap'.[k * 2 + 1])))

let well_formed
  (h: HS.mem) (heap: tree_heap_t) (hl: heap_len_t)
  (tl: nat) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t) =
  U32.v hl > 1 ==> partial_well_formed h heap hl tl tree depth 1ul

unfold let permutation_partial (h1 h2: seq U32.t) (root hole: U32.t) =
  let root = U32.v root in let hole = U32.v hole in
  length h1 == length h2 /\
  root <= hole /\ hole < length h1 /\
  (hole == root ==> Seq.permutation U32.t h1 h2 /\ h1 == h2) /\
  (hole <> root ==> 
    (h2.[hole] <> h1.[root] ==>
      count h1.[root] h2 + 1 == count h1.[root] h1 /\
      count h2.[hole] h2 == count h2.[hole] h1 + 1) /\
    (h2.[hole] == h1.[root] ==> count h1.[root] h2 == count h1.[root] h1) /\
    (forall (x: U32.t). {:pattern (count x h1) \/ (count x h2)}
      (x <> h1.[root] /\ x <> h2.[hole]) ==> count x h1 == count x h2))
