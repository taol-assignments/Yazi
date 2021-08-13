module Yazi.Tree

module B = LowStar.Buffer
module HS = FStar.HyperStack
module Seq = FStar.Seq
module SH = Spec.Heap
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open Lib.Seq
open LowStar.BufferOps
open Yazi.Tree.Types

let htd_seperate
  (h: HS.mem) (heap: tree_heap_t)
  (tree: B.buffer ct_data) (depth: tree_depth_t) =
  B.live h heap /\ B.live h tree /\ B.live h depth /\
  B.disjoint heap tree /\ B.disjoint heap depth /\ B.disjoint tree depth

inline_for_extraction
let smaller
  (tl: tree_len_t) (tree: B.lbuffer ct_data (Ghost.reveal tl))
  (depth: tree_depth_t) (n m: U32.t):
  ST.Stack bool
  (requires fun h ->
    U32.v n < tl /\ U32.v m < tl /\
    B.live h tree /\ B.live h depth)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    (res <==> SH.smaller h1 tl tree depth n m)) =
  let nfd = (tree.(n)).freq_or_dad in
  let mfd = (tree.(m)).freq_or_dad in
  if nfd `U16.lt` mfd then
    true
  else if nfd `U16.eq` mfd then
    let dn = depth.(n) in
    let dm = depth.(m) in
    dn `U8.lte` dm
  else
    false

#set-options "--z3refresh --z3rlimit 32768 --fuel 0 --ifuel 0"
inline_for_extraction
let smallest
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl)
  (depth: tree_depth_t) (i: U32.t{U32.v i < tl})
  (root: Ghost.erased (heap_internal_index_t hl))
  (j: heap_internal_index_t hl):
  ST.Stack U32.t
  (requires fun h ->
    let open U32 in
    v root <= v j /\
    htd_seperate h heap tree depth /\
    SH.element_in_range h heap hl tl /\
    SH.smaller h tl tree depth (B.as_seq h heap).[v j] i /\
    SH.partial_well_formed h heap hl tl tree depth root)
  (ensures fun h0 res h1 ->
    let heap = B.as_seq h1 heap in let hl = U32.v hl in
    let j = U32.v j in let res = U32.v res in
    let smaller' = SH.smaller h1 tl tree depth in
    
    B.modifies B.loc_none h0 h1 /\
    res <= hl /\ (res == 0 \/ res == j * 2 \/ res == j * 2 + 1) /\
    (let k = if res = 0 then i else heap.[res] in
    k `smaller'` i /\
    k `smaller'` heap.[j * 2] /\
    (j * 2 + 1 <= hl ==> k `smaller'` heap.[j * 2 + 1]) /\
    heap.[j] `smaller'` k)) =
  let open U32 in
  let l = j *^ 2ul in
  let r = l +^ 1ul in
  let le = heap.(l) in
  let smaller' = smaller tl tree depth in
  if r >^ hl then
    if i `smaller'` le then 0ul else l
  else
    let re = heap.(r) in
    if i `smaller'` le then
      if i `smaller'` re then 0ul else r
    else
      if le `smaller'` re then l else r

#set-options "--z3refresh --z3rlimit 32768 --fuel 0 --ifuel 0"
[@CInline]
let rec do_pqdownheap
  (h_init: Ghost.erased HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl)
  (depth: tree_depth_t)
  (i: U32.t{U32.v i < tl})
  (k: Ghost.erased (heap_internal_index_t hl))
  (j: heap_index_t hl):
  ST.Stack unit
  (requires fun h ->
    let open U32 in
    v k <= v j /\
    (B.as_seq h_init heap).[v k] == i /\
    htd_seperate h heap tree depth /\
    SH.smaller h tl tree depth (B.as_seq h heap).[U32.v j] i /\
    SH.partial_well_formed h heap hl tl tree depth k /\
    SH.permutation_partial (B.as_seq h_init heap) (B.as_seq h heap) k j)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer heap) h0 h1 /\
    SH.partial_well_formed h1 heap hl tl tree depth k)
  (decreases U32.v hl / 2 - U32.v j) =
  let open U32 in
  let internal = hl /^ 2ul in
  if j >^ internal then
    heap.(j) <- i
  else
    let s = smallest heap hl tl tree depth i k j in
    if s = 0ul then
      heap.(j) <- i
    else begin
      let h0 = ST.get () in
      let s' = heap.(s) in
      heap.(j) <- s';
      let h1 = ST.get () in
      upd_count (B.as_seq h0 heap) (B.as_seq h1 heap) (v j) s';
      do_pqdownheap h_init heap hl tl tree depth i k s
    end
