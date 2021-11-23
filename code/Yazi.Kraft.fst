module Yazi.Kraft

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module Seq = FStar.Seq
module SH = Spec.Heap
module SK = Spec.Kraft
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open Lib.Seq
open LowStar.BufferOps
open Yazi.Deflate.Constants
open Yazi.Tree.Types

inline_for_extraction
let get_heap_len (state: sort_state): ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res == SH.get_heap_len h1 state) =
  state.(0ul)

inline_for_extraction
let set_heap_len (state: sort_state) (a: U32.t): ST.Stack unit
  (requires fun h -> B.live h state)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    SH.get_heap_len h1 state == U32.v a /\
    SH.get_heap_max h0 state == SH.get_heap_max h1 state) =
  state.(0ul) <- a

inline_for_extraction
let get_heap_max (state: sort_state): ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res == SH.get_heap_max h1 state) =
  state.(1ul)

inline_for_extraction
let set_heap_max (state: sort_state) (a: U32.t): ST.Stack unit
  (requires fun h -> B.live h state)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    SH.get_heap_max h1 state == U32.v a /\
    SH.get_heap_len h0 state == SH.get_heap_len h1 state) =
  state.(1ul) <- a

val node_smaller:
    tree_len: tree_len_t
  -> tree: B.lbuffer ct_data (Ghost.reveal tree_len)
  -> depth: tree_depth_t
  -> n: U32.t
  -> m: U32.t
  -> ST.Stack bool
  (requires fun h ->
    U32.v n < tree_len /\ U32.v m < tree_len /\ B.live h tree /\ B.live h depth)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    (res == true <==> SH.node_smaller tree_len (B.as_seq h1 tree) (B.as_seq h1 depth) n m))
let node_smaller = fun tree_len tree depth n m ->
  ST.push_frame ();
  let nfd = (tree.(n)).freq_or_code in
  let mfd = (tree.(m)).freq_or_code in
  let res = if nfd `U16.lt` mfd then
    true
  else if nfd `U16.eq` mfd then
    let dn = depth.(n) in
    let dm = depth.(m) in
    if dn `U16.lt` dm then
      true
    else if dn `U16.eq` dm then
      n `U32.lte` m
    else
      false
  else
    false
  in
  ST.pop_frame ();
  res

let heap_common_pre_cond
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state)
  (root: Ghost.erased U32.t) (i hole: U32.t) =
  let open U32 in
  SH.context_live h ctx state /\
  (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h ctx'.heap in
  let tree = B.as_seq h ctx'.tree in
  let depth = B.as_seq h ctx'.depth in
  let heap_len = SH.get_heap_len h state in
  
  v i < ctx'.tree_len /\
  0 < v root /\
  v root <= heap_len / 2 /\
  v root <= v hole /\
  v hole <= heap_len /\
  
  (* heap.[v hole] `smaller` i *)
  SH.node_smaller ctx'.tree_len tree depth heap.[v hole] i /\
  
  (* Initial state, elements after root form a partial heap. *)
  (v root == v hole ==>
    SH.partial_well_formed h ctx state (root +^ 1ul) /\ heap.[v root] == i) /\

  (* Intermediate state, elements start from root form a partial heap.
     The element i has not inserted to the partial heap. *)
  (v root < v hole ==> SH.partial_well_formed h ctx state root))

#push-options "--z3refresh --z3rlimit 16 --fuel 0 --ifuel 0"
unfold let heap_smallest_post_cond
  (h0: HS.mem) (res: U32.t) (h1: HS.mem)
  (ctx: sort_ctx) (state: sort_state)
  (root: Ghost.erased U32.t) (i hole: U32.t) =
  let open U32 in
  SH.context_live h1 ctx state /\
  (let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h1 ctx'.heap in
  let tree = B.as_seq h1 ctx'.tree in
  let depth = B.as_seq h1 ctx'.depth in
  let smaller = SH.node_smaller ctx'.tree_len tree depth in
  let root = v root in
  let hole = v hole in
  let res = v res in
  let heap_len = SH.get_heap_len h1 state in
  
  B.modifies B.loc_none h0 h1 /\
  v i < ctx'.tree_len /\
  0 < root /\ root <= heap_len / 2 /\
  0 < hole /\ hole <= heap_len / 2 /\

  res <= heap_len /\ (res == 0 \/ res == hole * 2 \/ res == hole * 2 + 1) /\
  (let k = if res = 0 then i else heap.[res] in
  k `smaller` i /\
  k `smaller` heap.[hole * 2] /\
  (hole * 2 + 1 <= heap_len ==> k `smaller` heap.[hole * 2 + 1]) /\
  (root == hole ==> k `smaller` heap.[hole]) /\
  (root < hole ==> heap.[hole] `smaller` k)))
#pop-options

#push-options "--z3refresh --z3rlimit 1024 --fuel 0 --ifuel 0"
inline_for_extraction
let smallest
  (ctx: sort_ctx) (state: sort_state)
  (root: Ghost.erased U32.t) (i hole: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    heap_common_pre_cond h ctx state root i hole /\
    0 < U32.v hole /\ U32.v hole <= SH.get_heap_len h state / 2)
  (ensures fun h0 res h1 -> heap_smallest_post_cond h0 res h1 ctx state root i hole) =
  let open U32 in
  let h = ST.get () in
  let l = hole *^ 2ul in let r = l +^ 1ul in
  let le = (CB.index ctx 0ul).heap.(l) in

  let heap_len = get_heap_len state in
  let ctx' = CB.index ctx 0ul in
  [@inline_let] let smaller = node_smaller ctx'.tree_len ctx'.tree ctx'.depth in
  if r >^ heap_len then
    if i `smaller` le then 0ul else l
  else
    let re = (CB.index ctx 0ul).heap.(r) in
    if i `smaller` le then
      if i `smaller` re then 0ul else r
    else
      if le `smaller` re then l else r
#pop-options

#set-options "--z3refresh --z3rlimit 4096 --fuel 0 --ifuel 0 --z3seed 111"
inline_for_extraction
let rec do_pqdownheap
  (h0: Ghost.erased HS.mem)
  (ctx: sort_ctx) (state: sort_state) (heap_len: Ghost.erased (UInt.uint_t 32))
  (root: Ghost.erased U32.t) (i hole: U32.t):
  ST.Stack unit
  (requires fun h1 ->
    let ctx' = B.get h1 (CB.as_mbuf ctx) 0 in
    let heap0 = B.as_seq h0 ctx'.heap in
    let heap1 = B.as_seq h1 ctx'.heap in
    SH.modifies_heap_only h0 h1 ctx state /\
    (Ghost.reveal heap_len) == SH.get_heap_len h1 state /\
    heap_common_pre_cond h1 ctx state root i hole /\
    heap0.[U32.v root] == i /\
    SH.non_heap_unmodified h0 h1 ctx state /\
    SH.permutation_partial heap0 heap1 root hole /\
    (U32.v root == 1 ==> SH.heap_sorted h1 ctx state))
  (ensures fun h1 _ h2 ->
    SH.modifies_heap_only h1 h2 ctx state /\
    SH.non_heap_unmodified h1 h2 ctx state /\
    SH.partial_well_formed h2 ctx state root /\
    SH.whole_heap_perm h0 h2 ctx state /\
    SH.heap_seq_perm h0 h2 ctx state /\
    (U32.v root == 1 ==> SH.heap_sorted h2 ctx state))
  (decreases heap_len / 2 - U32.v hole) =
  let open U32 in
  let h1 = ST.get () in
  let heap_len = get_heap_len state in
  if hole >^ heap_len /^ 2ul then begin
    (CB.index ctx 0ul).heap.(hole) <- i;
    let h2 = ST.get () in
    if root =^ 1ul then SH.lemma_non_heap_unmodified h1 h2 ctx state;
    SH.lemma_heap_seq_upd_perm h0 h2 ctx state root i
  end else 
    let s = smallest ctx state root i hole in
    if s = 0ul then begin
      (CB.index ctx 0ul).heap.(hole) <- i;
      let h2 = ST.get () in
      if root =^ 1ul then SH.lemma_non_heap_unmodified h1 h2 ctx state;
      SH.lemma_heap_seq_upd_perm h0 h2 ctx state root i
    end else begin
      (CB.index ctx 0ul).heap.(hole) <- (CB.index ctx 0ul).heap.(s);
      let h2 = ST.get () in
      if root =^ 1ul then SH.lemma_non_heap_unmodified h1 h2 ctx state;
      do_pqdownheap h0 ctx state (v heap_len) root i s
    end

inline_for_extraction
let pqdownheap (ctx: sort_ctx) (state: sort_state) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    SH.context_live h ctx state /\
    0 < U32.v i /\ U32.v i <= SH.get_heap_len h state / 2 /\
    SH.partial_well_formed h ctx state (U32.add i 1ul) /\
    (U32.v i == 1 ==> SH.heap_sorted h ctx state))
  (ensures fun h0 _ h1 ->
    SH.modifies_heap_only h0 h1 ctx state /\
    SH.non_heap_unmodified h0 h1 ctx state /\
    SH.partial_well_formed h1 ctx state i /\
    SH.whole_heap_perm h0 h1 ctx state /\
    SH.heap_seq_perm h0 h1 ctx state /\
    SH.element_seq_perm h0 h1 ctx state /\
    (U32.v i == 1 ==> SH.heap_sorted h1 ctx state)) =
  let h0 = ST.get () in
  let heap_len = Ghost.hide (SH.get_heap_len h0 state) in
  do_pqdownheap h0 ctx state heap_len i (CB.index ctx 0ul).heap.(i) i;
  let h1 = ST.get () in
  SH.lemma_sorted_seq_unmodified_perm h0 h1 ctx state;
  SH.lemma_element_seq_perm_append h0 h1 ctx state

#push-options "--fuel 1"
inline_for_extraction
let pqremove (ctx: sort_ctx) (state: sort_state): ST.Stack U32.t
  (requires fun h ->
    SH.context_live h ctx state /\
    SH.well_formed h ctx state /\
    SH.heap_sorted h ctx state /\
    1 < SH.get_heap_len h state)
  (ensures fun h0 res h1 -> SH.heap_moved h0 h1 ctx state) =
  let open U32 in
  let h0 = ST.get () in
  let heap = (CB.index ctx 0ul).heap in
  let top = heap.(1ul) in
  let heap_len = get_heap_len state in
  let heap_max = get_heap_max state in
  heap.(1ul) <- heap.(heap_len);
  heap.(heap_max -^ 1ul) <- top;

  let h1 = ST.get () in
  SH.lemma_heap_max h0 ctx state;
  SH.lemma_non_heap_unmodified h0 h1 ctx state;

  set_heap_len state (heap_len -^ 1ul);
  set_heap_max state (heap_max -^ 1ul);

  let h2 = ST.get () in
  SH.lemma_element_seq_swap h0 h2 ctx state;

  if heap_len >^ 2ul then pqdownheap ctx state 1ul;
  top
#pop-options

inline_for_extraction
let pqreplace (ctx: sort_ctx) (state: sort_state) (node: U32.t): ST.Stack unit
  (requires fun h ->
    let c = B.get h (CB.as_mbuf ctx) 0 in
    SH.context_live h ctx state /\
    SH.well_formed h ctx state /\
    SH.heap_sorted h ctx state /\
    SH.get_heap_max h state < U32.v heap_size /\
    SH.get_heap_len h state - 1 <= B.length c.tree - U32.v node /\
    SH.forest_leaf_count h ctx state true <= U32.v l_codes /\
    SH.tree_freq_inv h ctx state /\
    SH.depth_inv h ctx state /\
    U32.v node < c.tree_len)
  (ensures fun h0 _ h1 ->
    let c1 = B.get h1 (CB.as_mbuf ctx) 0 in
    B.modifies (B.loc_buffer c1.tree `B.loc_union` B.loc_buffer c1.heap) h0 h1 /\
    SH.context_live h1 ctx state /\
    SH.well_formed h1 ctx state /\
    SH.heap_sorted h1 ctx state /\
    SH.tree_freq_inv h1 ctx state /\
    SH.depth_inv h1 ctx state /\
    SH.get_heap_len h0 state == SH.get_heap_max h1 state /\
    SH.get_heap_max h0 state == SH.get_heap_max h1 state + 1 /\
    SH.forest_leaf_count h0 ctx state true ==
    SH.forest_leaf_count h1 ctx state false) =
  let h0 = ST.get () in
  let heap = (CB.index ctx 0ul).heap in
  let tree = (CB.index ctx 0ul).tree in
  let depth = (CB.index ctx 0ul).depth in
  let heap_max = get_heap_max state in
  let m = heap.(1ul) in
  let n = heap.(heap_max) in
  SH.lemma_tree_freq_inv h0 ctx state 1;
  tree.(node) <- {
    tree.(node) with
    freq_or_code = U16.add (tree.(m)).freq_or_code (tree.(n)).freq_or_code;
  };

  SH.lemma_forest_height_upper_bound h0 ctx state;
  depth.(node) <-
    (if depth.(n) `U16.gt` depth.(m) then depth.(n) else depth.(m)) `U16.add` 1us;

  admit()

let init_heap_common_cond
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state)
  (j max_code elems: U32.t) =
  let open U32 in
  let ctx = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h ctx.heap in
  let tree = B.as_seq h ctx.tree in
  let depth = B.as_seq h ctx.depth in
  let j = U32.v j in
  let heap_len = SH.get_heap_len h state in
  let heap_max = SH.get_heap_max h state in
  let max_code = U32.v max_code in
  let elems = U32.v elems in
  Seq.length tree >= elems /\ j <= elems /\
  heap_len < U32.v heap_size /\
  heap_len < j + 1 /\
  heap_max == U32.v heap_size /\
  max_code < j /\
  elems <= v l_codes /\
  (heap_len == 0 ==> max_code == 0) /\

  (forall i. {:pattern U16.v (tree.[i]).freq_or_code} i >= elems ==>
    U16.v (tree.[i]).freq_or_code == 0) /\
  
  (* The frequencies of all leaves in the heap are greater than 0. *)
  (forall i. {:pattern (heap.[i]) \/ ((tree.[v heap.[i]]).freq_or_code)}
    0 < i /\ i <= heap_len ==> v heap.[i] < j /\ U16.v (tree.[v heap.[i]]).freq_or_code > 0) /\

  (* If a leaf's id is not smaller than j or its frequency is 0, it shouldn't in
     the heap. *)
  (forall i. (i >= j \/ U16.v (tree.[i]).freq_or_code == 0) ==>
    Seq.count (uint_to_t i) (Seq.slice heap 1 (heap_len + 1)) == 0) /\

  (* If a leaf's id is smaller than j and its frequency is larger than 0, it
     should in the heap.*)
  (forall i. (i < j /\ U16.v (tree.[i]).freq_or_code > 0) ==>
    Seq.count (uint_to_t i) (Seq.slice heap 1 (heap_len + 1)) == 1) /\

  (* For all non-leaves, their dad_or_len field should be 0. *)
  (forall i. {:pattern (tree.[i]).freq_or_code}
    i < j /\ U16.v (tree.[i]).freq_or_code == 0 ==> U16.v (tree.[i]).dad_or_len == 0) /\

  (* Forall leaves, its depth should be 0. *)
  (forall i. {:pattern (depth.[i])}
    i < j /\ U16.v (tree.[i]).freq_or_code > 0 ==> U16.v depth.[i] = 0) /\

  (* For all non-leaves, their dad_or_len field should be 0. *)
  (forall i. {:pattern (tree.[i]).dad_or_len}
    max_code < i /\ i < j ==> U16.v (tree.[i]).dad_or_len == 0)

#set-options "--z3refresh --z3rlimit 2048 --fuel 1 --ifuel 1 --z3seed 11"
[@ CInline ]
let rec init_heap (ctx: sort_ctx) (state: sort_state) (j max_code elems: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    U32.v j < U32.v elems /\
    SH.context_live h ctx state /\
    init_heap_common_cond h ctx state j max_code elems)
  (ensures fun h0 max_code h1 ->
    let open U32 in
    let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    let tree = ctx'.tree in
    let heap = ctx'.heap in
    let depth = ctx'.depth in
    let heap_len = SH.get_heap_len h1 state in
    let t0 = B.as_seq h0 tree in
    let t1 = B.as_seq h1 tree in
    B.modifies (
      B.loc_buffer heap `B.loc_union`
      B.loc_buffer tree `B.loc_union`
      B.loc_buffer depth `B.loc_union`
      B.loc_buffer state)
      h0 h1 /\
    (forall i. {:pattern ((t1.[i]).freq_or_code) \/ ((t0.[i]).freq_or_code)}
      (t1.[i]).freq_or_code == (t0.[i]).freq_or_code) /\
    init_heap_common_cond h1 ctx state elems max_code elems /\
    (heap_len == 0 ==> v max_code == 0 /\ U16.v (t1.[0]).freq_or_code == 0))
  (decreases U32.v elems - U32.v j) =
  let open U32 in
  let tree = (CB.index ctx 0ul).tree in
  let f = (tree.(j)).freq_or_code in
  if f = 0us then begin
    tree.(j) <- {tree.(j) with dad_or_len = 0us};
    if j +^ 1ul <^ elems then
      init_heap ctx state (j +^ 1ul) max_code elems
    else
      max_code
  end else begin
    let heap = (CB.index ctx 0ul).heap in
    let depth = (CB.index ctx 0ul).depth in
    let heap_len = get_heap_len state in
    heap.(heap_len +^ 1ul) <- j;
    depth.(j) <- 0us;

    let h = ST.get () in
    let tree' = Ghost.hide (B.as_seq h tree) in
    let heap' = Ghost.hide (B.as_seq h heap) in
    assert(Seq.equal
      (Seq.slice heap' 1 (v heap_len + 2))
      (Seq.append (Seq.slice heap' 1 (v heap_len + 1)) (Seq.create 1 j)));
    count_neq (Seq.slice heap' 1 (v heap_len + 1)) j;
    Seq.lemma_append_count (Seq.slice heap' 1 (v heap_len + 1)) (Seq.create 1 j);
    assert_norm(forall i. i < v j ==> Seq.count (uint_to_t i) (Seq.create 1 j) == 0);
    assert(forall i. (i > v j \/ U16.v (tree'.[i]).freq_or_code == 0) ==>
      normalize_term (Seq.count (uint_to_t i) (Seq.create 1 j)) == 0);

    set_heap_len state (heap_len +^ 1ul);
    if j +^ 1ul <^ elems then
      init_heap ctx state (j +^ 1ul) j elems
    else
      j
  end

#set-options "--z3refresh --fuel 1 --ifuel 0"
inline_for_extraction
let rec sort_leaves (ctx: sort_ctx) (state: sort_state) (i: U32.t):
  ST.Stack unit
  (requires fun h ->
    SH.context_live h ctx state /\
    0 < U32.v i /\ U32.v i < SH.get_heap_len h state / 2 /\
    SH.partial_well_formed h ctx state (U32.add i 1ul) /\
    SH.get_heap_max h state == U32.v heap_size)
  (ensures fun h0 _ h1 ->
    let heap = (B.get h0 (CB.as_mbuf ctx) 0).heap in
    B.modifies (B.loc_buffer heap) h0 h1 /\
    SH.well_formed h1 ctx state /\
    Seq.permutation U32.t (B.as_seq h0 heap) (B.as_seq h1 heap)) =
  let open U32 in
  pqdownheap ctx state i;
  if i >^ 1ul then sort_leaves ctx state (i -^ 1ul)

