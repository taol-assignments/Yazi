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
open Spec.Tree
open Yazi.Deflate.Constants
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
  let nfd = (tree.(n)).freq_or_code in
  let mfd = (tree.(m)).freq_or_code in
  if nfd `U16.lt` mfd then
    true
  else if nfd `U16.eq` mfd then
    let dn = depth.(n) in
    let dm = depth.(m) in
    dn `U8.lte` dm
  else
    false

let heap_common_pre_cond
  (h: HS.mem) (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl)
  (depth: tree_depth_t)
  (i: U32.t{U32.v i < tl})
  (root: Ghost.erased (heap_internal_index_t hl))
  (hole: heap_index_t hl) =
  let open U32 in
  let partial_well_formed = SH.partial_well_formed h heap hl tl tree depth in
  v root <= v hole /\
  htd_seperate h heap tree depth /\
  SH.smaller h tl tree depth (B.as_seq h heap).[v hole] i /\
  (v root == v hole ==>
    partial_well_formed (root +^ 1ul) /\
    (B.as_seq h heap).[v root] == i) /\
  (v root < v hole ==> partial_well_formed root)

inline_for_extraction
let smallest
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl)
  (depth: tree_depth_t)
  (i: U32.t{U32.v i < tl})
  (root: Ghost.erased (heap_internal_index_t hl))
  (hole: heap_internal_index_t hl):
  ST.Stack U32.t
  (requires fun h -> heap_common_pre_cond h heap hl tl tree depth i root hole)
  (ensures fun h0 res h1 ->
    let heap = B.as_seq h1 heap in let hl = U32.v hl in
    let root = U32.v root in let hole = U32.v hole in
    let res = U32.v res in
    let smaller' = SH.smaller h1 tl tree depth in
    
    B.modifies B.loc_none h0 h1 /\
    res <= hl /\ (res == 0 \/ res == hole * 2 \/ res == hole * 2 + 1) /\
    (let k = if res = 0 then i else heap.[res] in
    k `smaller'` i /\
    k `smaller'` heap.[hole * 2] /\
    (hole * 2 + 1 <= hl ==> k `smaller'` heap.[hole * 2 + 1]) /\
    (root == hole ==> k `smaller'` heap.[hole]) /\
    (root < hole ==> heap.[hole] `smaller'` k))) =
  let open U32 in
  let l = hole *^ 2ul in
  let r = l +^ 1ul in
  let le = heap.(l) in
  let smaller' = smaller tl tree depth in
  let h = ST.get () in
  if r >^ hl then
    if i `smaller'` le then 0ul else l
  else
    let re = heap.(r) in
    if i `smaller'` le then
      if i `smaller'` re then 0ul else r
    else
      if le `smaller'` re then l else r

#set-options "--z3refresh --z3rlimit 4096 --fuel 0 --ifuel 0"
inline_for_extraction
let rec do_pqdownheap
  (h_init: Ghost.erased HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: U32.t{U32.v i < tl})
  (root: Ghost.erased (heap_internal_index_t hl))
  (hole: heap_index_t hl):
  ST.Stack unit
  (requires fun h ->
    (B.as_seq h_init heap).[U32.v root] == i /\
    heap_common_pre_cond h heap hl tl tree depth i root hole /\
    SH.permutation_partial (B.as_seq h_init heap) (B.as_seq h heap) root hole)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer heap) h0 h1 /\
    SH.partial_well_formed h1 heap hl tl tree depth root /\
    Seq.permutation U32.t (B.as_seq h_init heap) (B.as_seq h1 heap))
  (decreases U32.v hl / 2 - U32.v hole) =
  let open U32 in
  if hole >^ hl /^ 2ul then
    heap.(hole) <- i
  else
    let s = smallest heap hl tl tree depth i root hole in
    if s = 0ul then
      heap.(hole) <- i
    else begin
      heap.(hole) <- heap.(s);
      do_pqdownheap h_init heap hl tl tree depth i root s
    end

inline_for_extraction
let pqdownheap
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: heap_internal_index_t hl):
  ST.Stack unit
  (requires fun h ->
    htd_seperate h heap tree depth /\
    SH.partial_well_formed h heap hl tl tree depth (U32.add i 1ul))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer heap) h0 h1 /\
    SH.partial_well_formed h1 heap hl tl tree depth i /\
    Seq.permutation U32.t (B.as_seq h0 heap) (B.as_seq h1 heap)) =
  do_pqdownheap (ST.get ()) heap hl tl tree depth heap.(i) i i

unfold let init_heap_common_cond
  (h: HS.mem)
  (heap: tree_heap_t) (hl: U32.t)
  (tree: B.buffer ct_data) (depth: tree_depth_t)
  (j: U32.t) (max_code: U32.t) (elems: U32.t) =
  let open U32 in
  let heap = B.as_seq h heap in
  let tree = B.as_seq h tree in
  let depth = B.as_seq h depth in
  let j = U32.v j in
  let hl = U32.v hl in
  let max_code = U32.v max_code in
  let elems = U32.v elems in
  Seq.length tree >= elems /\ j <= elems /\
  hl < U32.v heap_size /\
  hl < j + 1 /\ max_code < j /\ elems <= v l_codes /\
  (hl == 0 ==> max_code == 0) /\
  (forall i. {:pattern (heap.[i]) \/ ((tree.[v heap.[i]]).freq_or_code)}
    0 < i /\ i <= hl ==> v heap.[i] < j /\ U16.v (tree.[v heap.[i]]).freq_or_code > 0) /\
  (forall i. (i >= j \/ U16.v (tree.[i]).freq_or_code == 0) ==>
    Seq.count (uint_to_t i) (Seq.slice heap 1 (hl + 1)) == 0) /\
  (forall i. (i < j /\ U16.v (tree.[i]).freq_or_code > 0) ==>
    Seq.count (uint_to_t i) (Seq.slice heap 1 (hl + 1)) == 1) /\
  (forall i. {:pattern (tree.[i]).freq_or_code}
    (i < j /\ U16.v (tree.[i]).freq_or_code == 0) ==> U16.v (tree.[i]).dad_or_len == 0) /\
  (forall i. {:pattern (depth.[i])}
    (i < j /\ U16.v (tree.[i]).freq_or_code > 0) ==> U8.v depth.[i] = 0) /\
  (forall i. {:pattern (tree.[i]).freq_or_code}
    (max_code < i /\ i < j) ==> U16.v (tree.[i]).dad_or_len == 0)

#set-options "--z3refresh --z3rlimit 4096 --fuel 1 --ifuel 1"
[@ CInline ]
let rec init_heap
  (heap: tree_heap_t) (hl: U32.t{U32.v hl < U32.v heap_size})
  (tree: B.buffer ct_data) (depth: tree_depth_t)
  (j: U32.t) (max_code: U32.t) (elems: U32.t):
  ST.Stack (U32.t & U32.t)
  (requires fun h ->
    htd_seperate h heap tree depth /\
    U32.v j < U32.v elems /\
    init_heap_common_cond h heap hl tree depth j max_code elems)
  (ensures fun h0 res h1 ->
    let open U32 in
    let (hl, max_code) = res in
    let t0 = B.as_seq h0 tree in
    let t1 = B.as_seq h1 tree in
    B.modifies
      (B.loc_buffer heap `B.loc_union`
      B.loc_buffer tree `B.loc_union`
      B.loc_buffer depth)
      h0 h1 /\
    (forall i. {:pattern ((t1.[i]).freq_or_code) \/ ((t0.[i]).freq_or_code)}
      (t1.[i]).freq_or_code == (t0.[i]).freq_or_code) /\
    init_heap_common_cond h1 heap hl tree depth elems max_code elems /\
    (v hl == 0 ==> v max_code == 0 /\ U16.v (t1.[0]).freq_or_code == 0))
  (decreases U32.v elems - U32.v j) =
  let open U32 in
  let f = (tree.(j)).freq_or_code in
  if f = 0us then begin
    tree.(j) <- {tree.(j) with dad_or_len = 0us};
    if j +^ 1ul <^ elems then
      init_heap heap hl tree depth (j +^ 1ul) max_code elems
    else
      (hl, max_code)
  end else begin
    heap.(hl +^ 1ul) <- j;
    depth.(j) <- 0uy;

    let h = ST.get () in
    let tree' = Ghost.hide (B.as_seq h tree) in
    let heap' = Ghost.hide (B.as_seq h heap) in
    assert(Seq.equal
      (Seq.slice heap' 1 (v hl + 2))
      (Seq.append (Seq.slice heap' 1 (v hl + 1)) (Seq.create 1 j)));
    count_neq (Seq.slice heap' 1 (v hl + 1)) j;
    Seq.lemma_append_count (Seq.slice heap' 1 (v hl + 1)) (Seq.create 1 j);
    assert_norm(forall i. i < v j ==> Seq.count (uint_to_t i) (Seq.create 1 j) == 0);
    assert(forall i. (i > v j \/ U16.v (tree'.[i]).freq_or_code == 0) ==>
      normalize_term (Seq.count (uint_to_t i) (Seq.create 1 j)) == 0);

    if j +^ 1ul <^ elems then
      init_heap heap (hl +^ 1ul) tree depth (j +^ 1ul) j elems
    else
      (hl +^ 1ul, j)
  end

#set-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0"
[@ CInline ]
let rec sort_leaves
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: heap_internal_index_t hl):
  ST.Stack unit
  (requires fun h ->
    htd_seperate h heap tree depth /\
    SH.partial_well_formed h heap hl tl tree depth (U32.add i 1ul))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer heap) h0 h1 /\
    SH.well_formed h1 heap hl tl tree depth /\
    Seq.permutation U32.t (B.as_seq h0 heap) (B.as_seq h1 heap)) =
  let open U32 in
  pqdownheap heap hl tl tree depth i;
  if i >^ 1ul then
    sort_leaves heap hl tl tree depth (i -^ 1ul)
  else
    ()

let encoder_seperate
  (h: HS.mem) (heap: tree_heap_t)
  (tree: B.buffer ct_data) (depth: tree_depth_t)
  (opt_len static_len: B.pointer U32.t) =
  htd_seperate h heap tree depth /\
  B.live h opt_len /\ B.live h static_len /\
  B.disjoint opt_len static_len /\
  B.disjoint opt_len heap /\ B.disjoint opt_len tree /\ B.disjoint opt_len depth /\
  B.disjoint static_len heap /\ B.disjoint static_len tree /\ B.disjoint static_len depth

    // while (s->heap_len < 2) {
    //     node = s->heap[++(s->heap_len)] = (max_code < 2 ? ++max_code : 0);
    //     tree[node].Freq = 1;
    //     s->depth[node] = 0;
    //     s->opt_len--; if (stree) s->static_len -= stree[node].Len;
    //     /* node is 0 or 1 so it does not have extra bits */
    // }

#set-options "--fuel 4 --ifuel 4"
let build_small_tree
  (hl: heap_len_t) (max_code: U32.t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl):
  ST.Stack (Ghost.erased optimal_tree)
  (requires fun h ->
    let hl = U32.v hl in
    let max_code = U32.v max_code in
    let tree' = B.as_seq h tree in
    B.live h tree /\ hl < 2 /\ max_code < tl /\ 2 < tl /\
    (hl == 0 ==>
      max_code == 0 /\
      (forall i. U16.v (tree'.[i]).freq_or_code == 0)) /\
    (hl > 0 ==>
      U16.v (tree'.[max_code]).freq_or_code > 0 /\
      (forall i. i <> max_code ==> U16.v (tree'.[i]).freq_or_code == 0)))
  (ensures fun h0 t h1 ->
    B.modifies (B.loc_buffer tree) h0 h1 /\
    height t == 1 /\ Root? t /\
    tree_correspond h0 h1 t tree max_code) =
  if hl = 0ul then begin
    tree.(0ul) <- {
      freq_or_code = 0us;
      dad_or_len = 1us;
    };
    tree.(1ul) <- {
      freq_or_code = 0us;
      dad_or_len = 1us;
    };
    Root 0 (Leaf 0 1 0) (Leaf 0 1 1)
  end else
    let f = (tree.(max_code)).freq_or_code in
    if max_code = 0ul then begin
      tree.(max_code) <- {
        freq_or_code = 0us;
        dad_or_len = 1us
      };
      tree.(1ul) <- {
        freq_or_code = 1us;
        dad_or_len = 1us;
      };
      Root (U16.v f) (Leaf (U16.v f) 1 0) (Leaf 0 1 1)
    end else begin
      tree.(0ul) <- {
        freq_or_code = 0us;
        dad_or_len = 1us;
      };
      tree.(max_code) <- {
        freq_or_code = 1us;
        dad_or_len = 1us;
      };
      Root (U16.v f) (Leaf 0 1 0) (Leaf (U16.v f) 1 (U32.v max_code))
    end
