module Spec.Heap

module B = LowStar.Buffer
module C = Yazi.Deflate.Constants
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module Math = FStar.Math.Lemmas
module Seq = FStar.Seq
module SK = Spec.Kraft
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Yazi.Deflate.Constants
open Yazi.Tree.Types

private let heap_elem (tree_len: tree_len_t) (a: U32.t) =
  U32.v a < tree_len && U32.v a < 2 * U32.v l_codes + 1

let node_smaller
  (tree_len: nat{tree_len <= U32.v heap_size})
  (tree: Seq.seq ct_data{Seq.length tree == tree_len})
  (depth: Seq.seq U16.t{Seq.length depth == 2 * U32.v l_codes + 1})
  (i: U32.t{heap_elem tree_len i})
  (j: U32.t{heap_elem tree_len j}):
  Tot bool =
  let open U32 in
  let fi = U16.v (tree.[v i]).freq_or_code in
  let fj = U16.v (tree.[v j]).freq_or_code in
  (fi < fj ||
  (fi = fj && U16.v depth.[v i] < U16.v depth.[v j]) ||
  (fi = fj && U16.v depth.[v i] = U16.v depth.[v j] && v i <= v j))

unfold let get_heap_len (h: HS.mem) (state: sort_state) = U32.v (B.get h state 0)
unfold let get_heap_max (h: HS.mem) (state: sort_state) = U32.v (B.get h state 1)

let context_live (h: HS.mem) (ctx: sort_ctx) (state: sort_state) =
  CB.live h ctx /\ ~ (B.g_is_null (CB.as_mbuf ctx)) /\ B.live h state /\
  (let ctx' = (CB.as_seq h ctx).[0] in
  let heap_len = get_heap_len h state in
  let heap_max = get_heap_max h state in
  let heap = B.as_seq h ctx'.heap in
  let tree = B.as_seq h ctx'.tree in
  let depth = B.as_seq h ctx'.depth in
  B.live h ctx'.heap /\ B.live h ctx'.tree /\ B.live h ctx'.depth /\
  ~ (B.g_is_null ctx'.heap) /\ ~ (B.g_is_null ctx'.tree) /\ ~ (B.g_is_null ctx'.depth) /\

  (let ctx = CB.as_mbuf ctx in
  B.disjoint ctx state /\ B.disjoint ctx ctx'.tree /\ B.disjoint ctx ctx'.heap /\
  B.disjoint ctx ctx'.depth /\ B.disjoint state ctx'.tree /\
  B.disjoint state ctx'.heap /\ B.disjoint state ctx'.depth /\
  B.disjoint ctx'.tree ctx'.heap /\ B.disjoint ctx'.tree ctx'.depth /\
  B.disjoint ctx'.heap ctx'.depth) /\

  B.length ctx'.tree == Ghost.reveal ctx'.tree_len /\
  Seq.length (Ghost.reveal ctx'.forest) == Ghost.reveal ctx'.tree_len /\
  heap_len < heap_max /\ heap_max <= U32.v heap_size /\
  (forall i. {:pattern (heap.[i])}
    (0 < i /\ i <= heap_len \/ heap_max <= i /\ i < U32.v heap_size) ==>
    heap_elem ctx'.tree_len heap.[i]))

unfold let heap_not_empty (h: HS.mem) (state: sort_state): Tot Type0 =
  0 < get_heap_len h state

unfold let sorted_not_empty (h: HS.mem) (state: sort_state): Tot Type0 =
  get_heap_max h state < U32.v heap_size

unfold let heap_len_well_formed (h: HS.mem) (state: sort_state): Tot Type0 =
  0 < get_heap_len h state /\ get_heap_len h state < U32.v heap_size

let heap_seq (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Ghost (Seq.seq U32.t)
  (requires heap_len_well_formed h state)
  (ensures fun s -> Seq.length s == get_heap_len h state) =
  let heap = B.as_seq h (B.get h (CB.as_mbuf ctx) 0).heap in
  Seq.slice heap 1 (get_heap_len h state + 1)

let sorted_seq (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Ghost (Seq.seq U32.t)
  (requires get_heap_max h state <= U32.v heap_size)
  (ensures fun s -> Seq.length s == U32.v heap_size - get_heap_max h state) =
  let heap = B.as_seq h (B.get h (CB.as_mbuf ctx) 0).heap in
  Seq.slice heap (get_heap_max h state) (U32.v heap_size)

let element_seq (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Ghost (Seq.seq U32.t)
  (requires
    heap_len_well_formed h state /\
    get_heap_max h state <= U32.v heap_size)
  (ensures fun s ->
    let heap_len = get_heap_len h state in
    let heap_max = get_heap_max h state in
    Seq.length s == heap_len + U32.v heap_size - heap_max) =
  heap_seq h ctx state @| sorted_seq h ctx state

unfold let modifies_heap_only (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state) =
  let c = B.get h0 (CB.as_mbuf ctx) 0 in
  B.modifies (B.loc_buffer c.heap) h0 h1 /\
  context_live h0 ctx state /\ context_live h1 ctx state

let whole_heap_perm (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state): Tot Type0 =
  let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
  Seq.permutation U32.t (B.as_seq h0 c0.heap) (B.as_seq h1 c0.heap)

let heap_seq_perm (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state):
  Pure Type0
  (requires
    0 < get_heap_len h0 state /\ get_heap_len h0 state < U32.v heap_size /\
    0 < get_heap_len h1 state /\ get_heap_len h1 state < U32.v heap_size)
  (ensures fun _ -> True) =
  Seq.permutation U32.t (heap_seq h0 ctx state) (heap_seq h1 ctx state)

let sorted_seq_perm (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state): Pure Type0
  (requires
    get_heap_max h0 state <= U32.v heap_size /\
    get_heap_max h1 state <= U32.v heap_size)
  (ensures fun _ -> True) =
  Seq.permutation U32.t (sorted_seq h0 ctx state) (sorted_seq h1 ctx state)

private unfold let element_seq_perm_pre (h0 h1: HS.mem) (state: sort_state) =
  0 < get_heap_len h0 state /\ get_heap_len h0 state < U32.v heap_size /\
  0 < get_heap_len h1 state /\ get_heap_len h1 state < U32.v heap_size /\
  get_heap_max h0 state <= U32.v heap_size /\
  get_heap_max h1 state <= U32.v heap_size

let element_seq_perm (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state):
  Pure Type0
  (requires element_seq_perm_pre h0 h1 state)
  (ensures fun _ -> True) =
  Seq.permutation U32.t (element_seq h0 ctx state) (element_seq h1 ctx state)

let non_heap_unmodified (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state) =
  let heap = (B.get h1 (CB.as_mbuf ctx) 0).heap in
  let heap0 = B.as_seq h0 heap in
  let heap1 = B.as_seq h1 heap in
  let heap_len = get_heap_len h0 state in
  heap0.[0] == heap1.[0] /\
  (forall i. i > heap_len ==> heap0.[i] == heap1.[i])

let lemma_heap_seq_upd_perm
  (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state) (root i: U32.t): Lemma
  (requires
    (let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
    let heap0 = B.as_seq h0 c0.heap in
    let heap_len = get_heap_len h0 state in
    modifies_heap_only h0 h1 ctx state /\
    whole_heap_perm h0 h1 ctx state /\
    0 < heap_len /\
    0 < U32.v root /\ U32.v root <= heap_len / 2 /\
    i == heap0.[U32.v root] /\
    non_heap_unmodified h0 h1 ctx state))
  (ensures heap_seq_perm h0 h1 ctx state) =
  let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
  let c1 = B.get h1 (CB.as_mbuf ctx) 0 in
  let heap0 = B.as_seq h0 c0.heap in
  let heap1 = B.as_seq h1 c1.heap in
  let heap_len = get_heap_len h0 state in
  let heap_size = U32.v heap_size in
  assert(equal
    (Seq.slice heap0 (heap_len + 1) heap_size)
    (Seq.slice heap1 (heap_len + 1) heap_size));
  permutation_split heap0 heap1 1 (heap_len + 1)

let lemma_sorted_seq_unmodified_perm
  (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state): Lemma
  (requires
    modifies_heap_only h0 h1 ctx state /\
    non_heap_unmodified h0 h1 ctx state)
  (ensures sorted_seq_perm h0 h1 ctx state) =
  assert(equal (sorted_seq h0 ctx state) (sorted_seq h1 ctx state))

let lemma_element_seq_perm_append
  (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state): Lemma
  (requires
    modifies_heap_only h0 h1 ctx state /\
    0 < get_heap_len h1 state /\
    heap_seq_perm h0 h1 ctx state /\
    sorted_seq_perm h0 h1 ctx state)
  (ensures element_seq_perm h0 h1 ctx state) =
  lemma_append_count (heap_seq h0 ctx state) (sorted_seq h0 ctx state);
  lemma_append_count (heap_seq h1 ctx state) (sorted_seq h1 ctx state)

private let rec heap_sorted'
  (tree_len: nat{tree_len <= U32.v heap_size})
  (tree: Seq.seq ct_data{Seq.length tree == tree_len})
  (depth: Seq.seq U16.t{Seq.length depth == 2 * U32.v l_codes + 1})
  (i: nat{i <= U32.v heap_size})
  (heap: Seq.seq U32.t{
    Seq.length heap == U32.v heap_size /\
    (forall j. j >= i ==> heap_elem tree_len heap.[j])
  }):
  Tot bool
  (decreases U32.v heap_size - i) =
  if U32.v heap_size - i <= 1 then
    true
  else
    if node_smaller tree_len tree depth heap.[i + 1] heap.[i] then
      heap_sorted' tree_len tree depth (i + 1) heap
    else
      false

let rec lemma_heap_sorted'
  (tree_len: nat{tree_len <= U32.v heap_size})
  (tree: Seq.seq ct_data{Seq.length tree == tree_len})
  (depth: Seq.seq U16.t{Seq.length depth == 2 * U32.v l_codes + 1})
  (i: nat{i <= U32.v heap_size})
  (heap0: Seq.seq U32.t{
    Seq.length heap0 == U32.v heap_size /\
    (forall j. j >= i ==> heap_elem tree_len heap0.[j])
  })
  (heap1: Seq.seq U32.t{
    Seq.length heap1 == U32.v heap_size /\
    (forall j. j >= i ==> heap0.[j] == heap1.[j])
  }):
  Lemma
  (requires heap_sorted' tree_len tree depth i heap0)
  (ensures heap_sorted' tree_len tree depth i heap1)
  (decreases U32.v heap_size - i) =
  match U32.v heap_size - i with
  | 0 -> ()
  | _ -> lemma_heap_sorted' tree_len tree depth (i + 1) heap0 heap1

unfold let heap_sorted (h: HS.mem) (ctx: sort_ctx) (state: sort_state):
  Pure Type0
  (requires context_live h ctx state)
  (ensures fun _ -> True) =
  let open U32 in
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h ctx'.heap in
  let depth = B.as_seq h ctx'.depth in
  let tree = B.as_seq h ctx'.tree in
  let heap_len = get_heap_len h state in
  let heap_max = get_heap_max h state in
  
  heap_max <= U32.v heap_size /\
  (* All elements in heap area is smaller than the first element in the sorted area. *)
  (heap_len >= 1 /\ heap_max < U32.v heap_size ==> (forall j. 0 < j /\ j <= heap_len ==>
    node_smaller ctx'.tree_len tree depth heap.[heap_max] heap.[j])) /\

  (* All elements in the sorted area are sorted. *)
  heap_sorted' ctx'.tree_len tree depth heap_max heap

#push-options "--z3rlimit 1024 --ifuel 1"
private let rec lemma_heap_sorted_aux
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state) (i j: pos): Lemma
  (requires (
    context_live h ctx state /\ (
    let heap_max = get_heap_max h state in
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let tree = B.as_seq h ctx.tree in
    let depth = B.as_seq h ctx.depth in
    let heap = B.as_seq h ctx.heap in
    heap_max <= i /\
    i <= j /\ j < U32.v heap_size /\
    heap_sorted' ctx.tree_len tree depth i heap)))
  (ensures (
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let tree = B.as_seq h ctx.tree in
    let depth = B.as_seq h ctx.depth in
    let heap = B.as_seq h ctx.heap in
    heap_sorted' ctx.tree_len tree depth j heap))
  (decreases j - i) =
  match j - i with
  | 0 | 1 -> ()
  | _ ->
    let heap_max = get_heap_max h state in
    let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    let tree = B.as_seq h ctx'.tree in
    let depth = B.as_seq h ctx'.depth in
    let heap = B.as_seq h ctx'.heap in
    lemma_heap_sorted_aux h ctx state (i + 1) j

let rec lemma_heap_sorted
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state) (i j: pos): Lemma
  (requires
    context_live h ctx state /\
    heap_sorted h ctx state /\
    get_heap_max h state <= i /\ i <= j /\ j < U32.v heap_size)
  (ensures (
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h ctx.heap in
    let depth = B.as_seq h ctx.depth in
    let tree = B.as_seq h ctx.tree in
    node_smaller ctx.tree_len tree depth heap.[j] heap.[i]
  ))
  (decreases j - i) =
  let ctx' = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h ctx'.heap in
  let depth = B.as_seq h ctx'.depth in
  let tree = B.as_seq h ctx'.tree in
  let heap_max = get_heap_max h state in
  match j - i with
  | 0 -> ()
  | _ ->
    lemma_heap_sorted_aux h ctx state heap_max i;
    lemma_heap_sorted_aux h ctx state i j;
    lemma_heap_sorted h ctx state (i + 1) j
#pop-options

let partial_well_formed
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state) (i: U32.t): Pure Type0
  (requires context_live h ctx state)
  (ensures fun _ -> True) =
  let open U32 in
  let ctx = B.get h (CB.as_mbuf ctx) 0 in
  let heap_len = get_heap_len h state in
  let heap = B.as_seq h ctx.heap in
  let tree = B.as_seq h ctx.tree in
  let depth = B.as_seq h ctx.depth in
  let smaller = node_smaller ctx.tree_len tree depth in

  0 < v i /\ v i <= heap_len /\
  (forall (k: nat). v i <= k /\ k <= heap_len / 2 ==> (
    (heap.[k] `smaller` heap.[k * 2]) /\
    (k * 2 + 1 <= heap_len ==> heap.[k] `smaller` heap.[k * 2 + 1]))) /\

  (forall a. a `smaller` a) /\
  (forall a b. a `smaller` b /\ b `smaller` a ==> a == b) /\
  (forall a b c. a `smaller` b /\ b `smaller` c ==> a `smaller` c) /\
  (forall a b. a `smaller` b \/ b `smaller` a)

let well_formed (h: HS.mem) (ctx: sort_ctx) (state: sort_state) =
  context_live h ctx state /\ partial_well_formed h ctx state 1ul

let permutation_partial (h1 h2: seq U32.t) (root hole: U32.t) =
  let root = U32.v root in let hole = U32.v hole in
  (* h1 is the initial heap and the root of h1 is the element to be inserted to
     the heap.*)
  length h1 == length h2 /\
  root <= hole /\ hole < length h1 /\
  (hole == root ==> Seq.permutation U32.t h1 h2 /\ h1 == h2) /\
  (hole <> root ==> 
    (* Intermediate state. *)
    (h2.[hole] <> h1.[root] ==>
      count h1.[root] h2 + 1 == count h1.[root] h1 /\
      count h2.[hole] h2 == count h2.[hole] h1 + 1) /\

    (* The initial status, the counts should be the same. *)
    (h2.[hole] == h1.[root] ==> count h1.[root] h2 == count h1.[root] h1) /\
    
    (* For other non-root elements, thier counts are unchanged. *)
    (forall (x: U32.t). {:pattern (count x h1) \/ (count x h2)}
      x <> h1.[root] /\ x <> h2.[hole] ==> count x h1 == count x h2))

private let rec forest_leaf_count'
  (tree_len: tree_len_t)
  (forest: Seq.seq SK.tree{Seq.length forest == Ghost.reveal tree_len})
  (heap: Seq.seq U32.t{Seq.length heap == U32.v heap_size})
  (heap_len: nat{
    heap_len < Seq.length heap /\
    (forall i. 0 < i /\ i <= heap_len ==> heap_elem tree_len heap.[i])
  })
  (i: pos{i <= heap_len}): Tot nat (decreases heap_len - i) =
  SK.leaf_count forest.[U32.v heap.[i]] + (if i = heap_len then
    0
  else
    forest_leaf_count' tree_len forest heap heap_len (i + 1))

let forest_leaf_count (h: HS.mem) (ctx: sort_ctx) (state: sort_state) (with_hm: bool):
  Ghost nat
  (requires
    context_live h ctx state /\
    heap_not_empty h state /\
    (with_hm ==> sorted_not_empty h state))
  (ensures fun _ -> True) =
  let c = (CB.as_seq h ctx).[0] in
  let f = Ghost.reveal c.forest in
  let heap = B.as_seq h c.heap in
  let heap_len = get_heap_len h state in
  let heap_max = get_heap_max h state in
  let fc = forest_leaf_count' c.tree_len f heap heap_len 1 in
  if with_hm then SK.leaf_count f.[U32.v heap.[heap_max]] + fc else fc

/// Pre-condition for pqreplace()'s forest leaf count.
let pqreplace_flc_pre (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Pure Type0
  (requires
    context_live h ctx state /\
    heap_not_empty h state /\
    sorted_not_empty h state)
  (ensures fun _ -> True) =
  forest_leaf_count h ctx state true <= U32.v l_codes

// let forest_inv (h0 h1: HS.mem) (ctx: sort_ctx) (state:sort_state): Pure Type0
//   (requires
//     context_live h0 ctx state /\
//     context_live h1 ctx state /\
//     get_heap_len h0 state > 0 /\
//     get_heap_max h0 state < U32.v heap_size /\
//     get_heap_len h1 state > 0)
//   (ensures fun _ -> True) =
//   let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
//   let c1 = B.get h1 (CB.as_mbuf ctx) 0 in
//   let f0 = Ghost.reveal c0.forest in
//   let f1 = Ghost.reveal c1.forest in
//   let heap0 = B.as_seq h0 c0.heap in
//   let heap1 = B.as_seq h1 c1.heap in
//   let fc0 = forest_leaf_count' c0.tree_len f0 heap0 (get_heap_len h0 state) 1 in
//   let fc1 = forest_leaf_count' c1.tree_len f1 heap1 (get_heap_len h1 state) 1 in
//   fc0 == fc1 /\ fc0 <= U32.v l_codes

#push-options "--fuel 1 --ifuel 1"
private let rec lemma_forest_height_upper_bound'
  (h: HS.mem) (ctx: sort_ctx) (state:sort_state) (j: pos): Lemma
  (requires (
    let c = (CB.as_seq h ctx).[0] in
    let f = Ghost.reveal c.forest in
    let heap = B.as_seq h c.heap in
    context_live h ctx state /\
    heap_not_empty h state /\
    sorted_not_empty h state /\
    j <= get_heap_len h state /\
    SK.leaf_count f.[U32.v heap.[get_heap_max h state]] +
    forest_leaf_count' c.tree_len f heap (get_heap_len h state) j <= U32.v l_codes
  ))
  (ensures (
    let c = (CB.as_seq h ctx).[0] in
    let heap = B.as_seq h c.heap in
    let f = Ghost.reveal c.forest in
    let heap_max = get_heap_max h state in
    SK.leaf_count f.[U32.v heap.[heap_max]] <= U32.v l_codes /\
    SK.height f.[U32.v heap.[heap_max]] <= U32.v l_codes /\
    (forall i. j <= i /\ i <= get_heap_len h state ==>
      SK.leaf_count f.[U32.v heap.[i]] <= U32.v l_codes /\
      SK.height f.[U32.v heap.[i]] < U32.v l_codes)))
  (decreases (get_heap_len h state) - j) =
  let c = (CB.as_seq h ctx).[0] in
  let heap = B.as_seq h c.heap in
  let heap_len = get_heap_len h state in
  if j < heap_len then lemma_forest_height_upper_bound' h ctx state (j + 1)
#pop-options

let lemma_forest_height_upper_bound
  (h: HS.mem) (ctx: sort_ctx) (state:sort_state): Lemma
  (requires
    context_live h ctx state /\
    heap_not_empty h state /\
    sorted_not_empty h state /\
    forest_leaf_count h ctx state true <= U32.v l_codes)
  (ensures (
    let c = (CB.as_seq h ctx).[0] in
    let heap = B.as_seq h c.heap in
    let f = Ghost.reveal c.forest in
    let heap_max = get_heap_max h state in
    SK.leaf_count f.[U32.v heap.[heap_max]] <= U32.v l_codes /\
    SK.height f.[U32.v heap.[heap_max]] <= U32.v l_codes /\
    (forall i. 1 <= i /\ i <= get_heap_len h state ==>
      SK.leaf_count f.[U32.v heap.[i]] <= U32.v l_codes /\
      SK.height f.[U32.v heap.[i]] < U32.v l_codes))) =
  lemma_forest_height_upper_bound' h ctx state 1

private let rec tree_freq_sum
  (tree_len: tree_len_t)
  (tree: Seq.seq ct_data{Seq.length tree == Ghost.reveal tree_len})
  (heap: Seq.seq U32.t{Seq.length heap == U32.v heap_size})
  (heap_len: pos{
    heap_len < U32.v heap_size /\
    (forall i. 0 < i /\ i <= heap_len ==> heap_elem tree_len heap.[i])
  })
  (i: pos{i <= heap_len}): Tot nat (decreases heap_len - i) =
  U16.v (tree.[U32.v heap.[i]]).freq_or_code + (if i < heap_len then
    tree_freq_sum tree_len tree heap heap_len (i + 1)
  else
    0)

private let rec tree_freq_sum_lt tree_len tree heap heap_len i j: Lemma
  (requires i <= j /\ j <= heap_len)
  (ensures
    U16.v (tree.[U32.v heap.[j]]).freq_or_code <=
    tree_freq_sum tree_len tree heap heap_len i)
  (decreases j - i) =
  match j - i with
  | 0 -> ()
  | _ -> tree_freq_sum_lt tree_len tree heap heap_len (i + 1) j

let tree_freq_inv (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Pure Type0
  (requires context_live h ctx state)
  (ensures fun _ -> True) =
  let c = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h c.heap in
  let tree = B.as_seq h c.tree in
  let heap_len = get_heap_len h state in
  let heap_max = get_heap_max h state in
  0 < heap_len /\ 0 < heap_max /\ heap_max < U32.v heap_size /\
  U16.v (tree.[U32.v heap.[heap_max]]).freq_or_code +
  tree_freq_sum c.tree_len tree heap heap_len 1 <= pow2 15

let lemma_tree_freq_inv (h: HS.mem) (ctx: sort_ctx) (state: sort_state) (i: pos): Lemma
  (requires
    context_live h ctx state /\ tree_freq_inv h ctx state /\
    i <= get_heap_len h state)
  (ensures (
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h ctx.heap in
    let tree = B.as_seq h ctx.tree in
    let heap_max = get_heap_max h state in
    let sum = U16.v (tree.[U32.v heap.[i]]).freq_or_code +
      U16.v (tree.[U32.v heap.[heap_max]]).freq_or_code
    in
    sum <= pow2 15 /\ pow2 15 < pow2 16)) =
  Math.pow2_lt_compat 16 15;
  let ctx = B.get h (CB.as_mbuf ctx) 0 in
  let heap = B.as_seq h ctx.heap in
  let tree = B.as_seq h ctx.tree in
  let heap_len = get_heap_len h state in
  tree_freq_sum_lt ctx.tree_len tree heap heap_len 1 i

let depth_inv (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Pure Type0
  (requires context_live h ctx state)
  (ensures fun _ -> True) =
  let ctx = B.get h (CB.as_mbuf ctx) 0 in
  let depth = B.as_seq h ctx.depth in
  let heap = B.as_seq h ctx.heap in
  let heap_len = get_heap_len h state in
  let heap_max = get_heap_max h state in
  forall i. 0 < i /\ i <= heap_len \/ heap_max <= i /\ i < U32.v heap_size ==>
    U16.v depth.[U32.v heap.[i]] == SK.height ctx.forest.[U32.v heap.[i]]

private let rec log2 (a: pos): Tot (n: nat{
  pow2 n <= a /\ a < pow2 (n + 1)
}) = if a = 1 then 0 else 1 + log2 (a / 2)

private let rec log2_pow2_lt (a: pos) (n: nat): Lemma
  (requires n < log2 a)
  (ensures pow2 n < a) =
  match n with
  | 0 -> ()
  | _ -> log2_pow2_lt (a / 2) (n - 1)

private let rec log2_pow2_gt (a: pos) (n: pos): Lemma
  (requires a < pow2 n)
  (ensures log2 a < n) =
  match (a, n) with
  | (1, _) | (_, 1) -> ()
  | _ -> log2_pow2_gt (a / 2) (n - 1)

private let rec parent (a: pos) (i: pos{i <= log2 a}): Tot (res: pos{res < a}) =
  if i > 1 then parent (a / 2) (i - 1) else a / 2

private let rec lemma_parent_next (a: pos) (i: pos{1 < i /\ i <= log2 a}): Lemma
  (ensures parent a i == parent a (i - 1) / 2) =
  match i with
  | 2 -> ()
  | _ -> lemma_parent_next (a / 2) (i - 1)

private let lemma_div2 (a b: nat): Lemma
  (requires a / 2 == b)
  (ensures b * 2 == a \/ b * 2 + 1 == a) = ()

#set-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 0 --z3seed 11"
private let rec lemma_partial_well_formed_max
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state)
  (height: nat) (j: pos) : Lemma
  (requires
    context_live h ctx state /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    height < log2 j /\ j <= get_heap_len h state /\ pow2 height < j /\
    partial_well_formed h ctx state (U32.uint_to_t (pow2 height))))
  (ensures (
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h ctx.heap in
    let depth = B.as_seq h ctx.depth in
    let tree = B.as_seq h ctx.tree in
    let pj = parent j (log2 j - height) in
    pow2 height <= pj /\ pj < pow2 (height + 1) /\
    node_smaller ctx.tree_len tree depth heap.[pj] heap.[j]))
  (decreases get_heap_len h state - pow2 height) =
  if j < pow2 (height + 2) then begin
    log2_pow2_lt j height;
    log2_pow2_gt j (height + 2);
    lemma_div2 j (parent j (log2 j - height))
  end else begin
    lemma_partial_well_formed_max h ctx state (height + 1) j;
    lemma_parent_next j (log2 j - height);
    Math.subtraction_is_distributive (log2 j) height 1;
    lemma_div2 (parent j (log2 j - (height + 1))) (parent j (log2 j - height))
  end

private let lemma_heap_max'
  (h: HS.mem) (ctx: sort_ctx) (state: sort_state)
  (i: pos{1 < i /\ i <= get_heap_len h state}) : Lemma
  (requires well_formed h ctx state)
  (ensures (
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h ctx.heap in
    let depth = B.as_seq h ctx.depth in
    let tree = B.as_seq h ctx.tree in
    node_smaller ctx.tree_len tree depth heap.[1] heap.[i])) =
  lemma_partial_well_formed_max h ctx state 0 i

let lemma_heap_max (h: HS.mem) (ctx: sort_ctx) (state: sort_state): Lemma
  (requires well_formed h ctx state)
  (ensures forall i.
    let ctx = B.get h (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h ctx.heap in
    let depth = B.as_seq h ctx.depth in
    let tree = B.as_seq h ctx.tree in
    1 < i /\ i <= get_heap_len h state ==>
       node_smaller ctx.tree_len tree depth heap.[1] heap.[i])
  [SMTPat (well_formed h ctx state)] =
  Classical.forall_intro (Classical.move_requires (lemma_heap_max' h ctx state))

let lemma_non_heap_unmodified
  (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state):
  Lemma 
  (requires (
    let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
    let heap0 = B.as_seq h0 c0.heap in
    let heap1 = B.as_seq h1 c0.heap in
    modifies_heap_only h0 h1 ctx state /\
    (forall i. i >= get_heap_max h0 state ==> heap0.[i] == heap1.[i]) /\
    heap_sorted h0 ctx state))
  (ensures (
    let c1 = B.get h1 (CB.as_mbuf ctx) 0 in
    let heap = B.as_seq h1 c1.heap in
    let tree = B.as_seq h1 c1.tree in
    let depth = B.as_seq h1 c1.depth in
    let heap_max = get_heap_max h1 state in
    heap_sorted' c1.tree_len tree depth (heap_max) heap
  )) =
  let heap_max = get_heap_max h0 state in
  match U32.v heap_size - heap_max with
  | 0 -> ()
  | _ ->
    let c0 = B.get h0 (CB.as_mbuf ctx) 0 in
    let c1 = B.get h1 (CB.as_mbuf ctx) 0 in
    let tree = B.as_seq h0 c0.tree in
    let depth = B.as_seq h0 c0.depth in
    let heap0 = B.as_seq h0 c0.heap in
    let heap1 = B.as_seq h1 c1.heap in
    lemma_heap_sorted' c0.tree_len tree depth heap_max heap0 heap1

let heap_moved (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state) =
  let c = B.get h0 (CB.as_mbuf ctx) 0 in
  B.modifies (B.loc_buffer c.heap `B.loc_union` B.loc_buffer state) h0 h1 /\
  context_live h0 ctx state /\ context_live h1 ctx state /\
  well_formed h0 ctx state /\ well_formed h1 ctx state /\
  get_heap_len h0 state - 1 == get_heap_len h1 state /\
  get_heap_max h0 state - 1 == get_heap_max h1 state /\
  heap_sorted h1 ctx state /\
  element_seq_perm h0 h1 ctx state

let lemma_element_seq_swap (h0 h1: HS.mem) (ctx: sort_ctx) (state: sort_state): Lemma
  (requires (
    let heap = (B.get h0 (CB.as_mbuf ctx) 0).heap in
    let heap0 = B.as_seq h0 heap in
    let heap1 = B.as_seq h1 heap in
    B.modifies (B.loc_buffer heap `B.loc_union` B.loc_buffer state) h0 h1 /\
    context_live h0 ctx state /\ context_live h1 ctx state /\
    element_seq_perm_pre h0 h1 state /\
    get_heap_len h0 state - 1 == get_heap_len h1 state /\
    get_heap_max h0 state - 1 == get_heap_max h1 state /\
    (forall i. i <> 1 /\ i <> get_heap_max h1 state ==> heap0.[i] == heap1.[i]) /\
    heap1.[1] == heap0.[get_heap_len h0 state] /\ heap1.[get_heap_max h1 state] == heap0.[1]))
  (ensures element_seq_perm h0 h1 ctx state) =
  let heap = (B.get h0 (CB.as_mbuf ctx) 0).heap in
  let heap0 = B.as_seq h0 heap in
  let heap1 = B.as_seq h1 heap in
  let hs0 = heap_seq h0 ctx state in
  let hs1 = heap_seq h1 ctx state in
  let ss0 = sorted_seq h0 ctx state in
  let ss1 = sorted_seq h1 ctx state in
  let es0 = element_seq h0 ctx state in
  let es1 = element_seq h1 ctx state in
  let heap_len = get_heap_len h0 state in
  let heap_max = get_heap_max h0 state in
  assert(forall i. {:pattern hs0.[i]} hs0.[i] == heap0.[i + 1]);
  assert(forall i. {:pattern hs1.[i]} hs1.[i] == heap1.[i + 1]);
  assert(forall i. {:pattern hs1.[i] \/ hs0.[i]} 0 < i ==> hs1.[i] == hs0.[i]);
  assert(forall i. {:pattern ss0.[i]} ss0.[i] == heap0.[i + heap_max]);
  assert(forall i. {:pattern ss1.[i]} ss1.[i] == heap1.[i + heap_max - 1]);
  assert(forall i. i > 0 ==> ss0.[i - 1] == ss1.[i]);
  assert(forall i. {:pattern es0.[i]}
    (i < heap_len ==> es0.[i] == hs0.[i]) /\
    (heap_len <= i ==> es0.[i] == ss0.[i - heap_len]));
  assert(forall i. {:pattern es1.[i]}
    (i < heap_len - 1 ==> es1.[i] == hs1.[i]) /\
    (heap_len - 1 <= i ==> es1.[i] == ss1.[i - (heap_len - 1)]));
  assert(forall i. {:pattern es0.[i] \/ es1.[i]}
    i <> 0 /\ i <> heap_len - 1 ==> es0.[i] == es1.[i]);
  swap_equal es0 es1 0 (heap_len - 1);
  Seq.lemma_swap_permutes es0 0 (heap_len - 1)
