module Yazi.Tree

module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module Seq = FStar.Seq
module SH = Spec.Tree
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
let get_heap_len (ts: tree_state_t): ST.Stack U32.t
  (requires fun h -> SH.tree_state_live h ts)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res == SH.get_heap_len h1 ts) =
  (CB.index ts.ctx 0ul).state.(0ul)

inline_for_extraction
let set_heap_len (ts: tree_state_t) (a: U32.t): ST.Stack unit
  (requires fun h -> SH.tree_state_live h ts)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ((CB.as_seq h0 ts.ctx).[0]).state) h0 h1 /\
    SH.get_heap_len h1 ts == U32.v a /\
    SH.get_heap_max h0 ts == SH.get_heap_max h1 ts) =
  (CB.index ts.ctx 0ul).state.(0ul) <- a

inline_for_extraction
let get_heap_max (ts: tree_state_t): ST.Stack U32.t
  (requires fun h -> SH.tree_state_live h ts)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    U32.v res == SH.get_heap_max h0 ts) =
  (CB.index ts.ctx 0ul).state.(1ul)

inline_for_extraction
let set_heap_max (ts: tree_state_t) (a: U32.t): ST.Stack unit
  (requires fun h -> SH.tree_state_live h ts)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ((CB.as_seq h0 ts.ctx).[0]).state) h0 h1 /\
    SH.get_heap_max h1 ts == U32.v a /\
    SH.get_heap_len h0 ts == SH.get_heap_len h1 ts) =
  (CB.index ts.ctx 0ul).state.(1ul) <- a

inline_for_extraction
let smaller (ts: tree_state_t) (n m: U32.t): ST.Stack bool
  (requires fun h ->
    SH.tree_state_live h ts /\
    (let ts = SH.g_tree_state h ts in
    SH.heap_elems_wf ts /\ SH.is_tree_index ts n /\ SH.is_tree_index ts m))
  (ensures fun h0 res h1 ->
    let ts = SH.g_tree_state h0 ts in
    B.modifies B.loc_none h0 h1 /\
    res == SH.smaller ts n m) =
  let tree = (CB.index ts.ctx 0ul).tree in
  let nfc = (tree.(n)).freq_or_code in
  let mfc = (tree.(m)).freq_or_code in
  if nfc `U16.lt` mfc then
    true
  else if nfc `U16.eq` mfc then
    let depth = (CB.index ts.ctx 0ul).depth in
    let dn = depth.(n) in
    let dm = depth.(m) in
    if dn `U8.lt` dm then
      true
    else if dn `U8.eq` dm then
      n `U32.lte` m
    else
      false
  else
    false

#push-options "--z3refresh --z3rlimit 256 --fuel 1 --ifuel 0 --z3seed 111"
inline_for_extraction
let smallest (ts: tree_state_t) (root: Ghost.erased U32.t) (i hole: U32.t): ST.Stack U32.t
  (requires fun h ->
    SH.tree_state_live h ts /\
    SH.heap_elems_wf (SH.g_tree_state h ts) /\
    SH.insertion_pre_cond (SH.g_tree_state h ts) root i hole /\
    U32.v hole <= SH.get_heap_len h ts / 2)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    res == SH.smallest (SH.g_tree_state h0 ts) root i hole) =
  let open U32 in
  let l = hole *^ 2ul in let r = l +^ 1ul in
  let le = (CB.index ts.ctx 0ul).heap.(l) in

  let heap_len = get_heap_len ts in
  [@inline_let] let smaller = smaller ts in
  if r >^ heap_len then begin
    if i `smaller` le then 0ul else l
  end else begin
    let re = (CB.index ts.ctx 0ul).heap.(r) in
    if i `smaller` le then
      if i `smaller` re then 0ul else r
    else
      if le `smaller` re then l else r
  end
#pop-options

#push-options "--z3refresh --z3rlimit 128 --fuel 1 --ifuel 0 --z3seed 111"
[@ CInline]
let rec do_pqdownheap
  (h0: Ghost.erased HS.mem) (ts: tree_state_t)
  (root: Ghost.erased U32.t) (i hole: U32.t):
  ST.Stack unit
  (requires fun h1 ->
    SH.tree_state_live h0 ts /\ SH.tree_state_live h1 ts /\
    B.modifies (B.loc_buffer ((CB.as_seq h1 ts.ctx).[0]).heap) h0 h1 /\
    SH.do_pqdownheap_pre (SH.g_tree_state h0 ts) (SH.g_tree_state h1 ts) root i hole)
  (ensures fun h1 _ h2 ->
    let open SH in
    let ts0 = SH.g_tree_state h0 ts in
    let ts1 = SH.g_tree_state h1 ts in
    SH.tree_state_live h2 ts /\
    B.modifies (B.loc_buffer ((CB.as_seq h1 ts.ctx).[0]).heap) h1 h2 /\
    SH.g_tree_state h2 ts == SH.do_pqdownheap ts0 ts1 root i hole)
  (decreases SH.get_heap_len h0 ts / 2 - U32.v hole) =
  let open U32 in
  let heap_len = get_heap_len ts in
  let heap = (CB.index ts.ctx 0ul).heap in
  if hole >^ heap_len /^ 2ul then
    heap.(hole) <- i
  else
    let s = smallest ts root i hole in
    if s = 0ul then
      heap.(hole) <- i
    else begin
      heap.(hole) <- heap.(s);
      do_pqdownheap h0 ts root i s
    end

inline_for_extraction
let pqdownheap (ts: tree_state_t) (i: U32.t): ST.Stack unit
  (requires fun h ->
    SH.tree_state_live h ts /\
    SH.is_internal_index (SH.g_tree_state h ts) i /\
    SH.pqdownheap_pre (SH.g_tree_state h ts) i)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer ((CB.as_seq h0 ts.ctx).[0]).heap) h0 h1 /\
    SH.g_tree_state h1 ts == SH.pqdownheap (SH.g_tree_state h0 ts) i) =
  do_pqdownheap (ST.get ()) ts i (CB.index ts.ctx 0ul).heap.(i) i
#pop-options

#push-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0"
inline_for_extraction
let pqremove (ts: tree_state_t):
  ST.Stack U32.t
  (requires fun h ->
    SH.tree_state_live h ts /\
    SH.heap_wf (SH.g_tree_state h ts) /\
    SH.get_heap_len h ts > 1)
  (ensures fun h0 top h1 ->
    B.modifies (
      B.loc_buffer ((CB.as_seq h0 ts.ctx).[0]).heap `B.loc_union`
      B.loc_buffer ((CB.as_seq h0 ts.ctx).[0]).state
    ) h0 h1 /\
    SH.tree_state_live h1 ts /\
    SH.g_tree_state h1 ts == SH.pqremove (SH.g_tree_state h0 ts) /\
    (SH.g_tree_state h0 ts <: tree_state).heap.[1] == top) =
  let h0 = ST.get () in
  SH.lemma_heap_wf_pqremove (SH.g_tree_state h0 ts);
  let open U32 in
  let heap_len = get_heap_len ts in
  let heap_max = get_heap_max ts in
  let heap = (CB.index ts.ctx 0ul).heap in
  let top = heap.(1ul) in
  let bot = heap.(heap_len) in
  heap.(heap_max -^ 1ul) <- top;
  heap.(1ul) <- bot;
  set_heap_len ts (heap_len -^ 1ul);
  set_heap_max ts (heap_max -^ 1ul);
  if heap_len -^ 1ul >=^ 2ul then pqdownheap ts 1ul;
  top
#pop-options

#push-options "--z3refresh --z3seed 1 --z3rlimit 1024 --fuel 1 --ifuel 1 --query_stats"
inline_for_extraction
let pqmerge (ts: tree_state_t) (node: U32.t):
  ST.Stack tree_state_t
  (requires fun h ->
    SH.tree_state_live h ts /\
    SH.heap_wf (SH.g_tree_state h ts) /\
    SH.pqmerge_pre (SH.g_tree_state h ts) (U32.v node))
  (ensures fun h0 ts' h1 ->
    let ctx = (CB.as_seq h0 ts.ctx).[0] in
    B.modifies (
      B.loc_buffer ctx.heap `B.loc_union`
      B.loc_buffer ctx.state `B.loc_union`
      B.loc_buffer ctx.depth `B.loc_union`
      B.loc_buffer ctx.tree
    ) h0 h1 /\
    SH.tree_state_live h1 ts' /\
    SH.g_tree_state h1 ts' == SH.pqmerge (SH.g_tree_state h0 ts) (U32.v node)) =
  let h0 = ST.get () in
  let ctx = CB.index ts.ctx 0ul in
  let t0 = Ghost.hide (SH.g_tree_state h0 ts) in

  let il = ctx.heap.(get_heap_max ts) in
  ctx.tree.(il) <- ({
    ctx.tree.(il) with
    dad_or_len = Cast.uint32_to_uint16 node;
  });

  let ir = ctx.heap.(1ul) in
  ctx.tree.(ir) <- ({
    ctx.tree.(ir) with
    dad_or_len = Cast.uint32_to_uint16 node;
  });

  SH.lemma_forest_freq_plus t0 0 1;
  ctx.tree.(node) <- ({
    ctx.tree.(node) with
    freq_or_code = (ctx.tree.(il)).freq_or_code `U16.add`
      (ctx.tree.(ir)).freq_or_code
  });

  let dl = ctx.depth.(il) in
  let dr = ctx.depth.(ir) in
  ctx.depth.(node) <- 1uy `U8.add_mod` (if dl `U8.gte` dr then dl else dr);

  let heap_max' = get_heap_max ts `U32.sub` 1ul in
  ctx.heap.(heap_max') <- ir;
  ctx.heap.(1ul) <- node;
  set_heap_max ts heap_max';

  let node' = Ghost.hide (U32.v node) in
  let l = Ghost.hide ts.forest.[U32.v il] in
  let r = Ghost.hide ts.forest.[U32.v ir] in
  SH.lemma_is_max_id_map t0 node' 1;
  SH.lemma_is_max_id_map t0 node' t0.heap_max;
  SH.lemma_pqmerge_no_dup t0 t0.heap_max 1;
  let t' = Ghost.hide (Node l node' (freq l + freq r) r) in
  let f' = Ghost.hide (Seq.upd ts.forest node' t') in
  {
    ts with
    forest = f'
  }
