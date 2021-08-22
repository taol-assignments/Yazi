module Spec.Tree

module B = LowStar.Buffer
module BV = FStar.BitVector
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module U16 = FStar.UInt16
module U32 = FStar.UInt32

open Lib.Rational
open Lib.Seq
open FStar.Mul
open FStar.Seq
open Yazi.Tree.Types
open Yazi.Deflate.Constants

type tree =
  | Root: freq: nat -> left: tree -> right: tree -> tree
  | Internal: freq: nat -> len: pos -> left: tree -> right: tree -> tree
  | Leaf: freq: nat -> len: pos -> symbol: nat -> tree

let freq (t: tree{Root? t == false}): nat =
  match t with
  | Internal freq _ _ _ -> freq
  | Leaf freq _ _ -> freq

let length (t: tree): nat =
  match t with
  | Root _ _ _ -> 0
  | Internal _ len _ _ -> len
  | Leaf _ len _ -> len

let rec symbol_seq (t: tree): Seq.seq nat =
  match t with
  | Root _ l r -> symbol_seq l @| symbol_seq r
  | Internal _ _ l r -> symbol_seq l @| symbol_seq r
  | Leaf _ _ symbol -> create 1 symbol

let rec well_formed (t: tree): Type0 =
  if Leaf? t then
    True
  else
    let (l, r) = (match t with
    | Root _ l r -> (l, r)
    | Internal _ _ l r -> (l, r))
    in
    let len = length t in
    Root? l == false /\ Root? r == false /\
    length l == len + 1 /\ length r == len + 1 /\
    no_dup (symbol_seq t) /\
    well_formed l /\ well_formed r

private let rec optimal' (t: tree{well_formed t}): Type0 =
  match t with
  | Root f l r -> freq l + freq r == f /\ optimal' l /\ optimal' r
  | Internal f len l r -> freq l + freq r == f /\ optimal' l /\ optimal' r
  | Leaf _ _ _ -> True

type optimal_tree = t: tree{well_formed t /\ optimal' t}

type well_formed_tree = t: tree{well_formed t}

type root = t: well_formed_tree{Root? t == true}

type internal = t: well_formed_tree{Internal? t == true}

type leaf = t: well_formed_tree{Leaf? t == true}

type non_leaf = t: well_formed_tree{Leaf? t == false}

let left (t: non_leaf): well_formed_tree =
  match t with
  | Root _ l _ -> l
  | Internal _ _ l _ -> l

let right (t: non_leaf): well_formed_tree =
  match t with
  | Root _ _ r -> r
  | Internal _ _ _ r -> r

let symbol (t: leaf): nat = 
  match t with
  | Leaf _ _ symbol -> symbol

let rec height (t: well_formed_tree): Tot nat =
  match t with
  | Root _ l r ->
    let ld = height l in
    let rd = height r in
    1 + (if ld > rd then ld else rd)
  | Internal _ _ l r ->
    let ld = height l in
    let rd = height r in
    1 + (if ld > rd then ld else rd)
  | Leaf _ len _ -> 0

type tree_symbol (t: well_formed_tree) = s: nat{Seq.mem s (symbol_seq t)}

let symbol_seq_aux (t: non_leaf) (s: tree_symbol t): Lemma
  (ensures
    disjoint (symbol_seq (left t)) (symbol_seq (right t)) /\
    (Seq.mem s (symbol_seq (left t)) \/ Seq.mem s (symbol_seq (right t))))
  [SMTPatOr
    [[SMTPat (Seq.mem s (symbol_seq (left t)))];
    [SMTPat (Seq.mem s (symbol_seq (right t)))]]] =
    lemma_mem_append (symbol_seq (left t)) (symbol_seq (right t))

let rec code_len (t: non_leaf) (s: tree_symbol t): Tot pos =
  let l = left t in let r = right t in
  if Seq.mem s (symbol_seq l) then
    if Leaf? l then 1 else 1 + code_len l s
  else
    if Leaf? r then 1 else 1 + code_len r s

#set-options "--z3rlimit 128 --ifuel 1 --fuel 1"
let rec code_partial
  (t: non_leaf) (s: tree_symbol t) (depth: pos{
    depth <= code_len t s
  }): Tot (BV.bv_t depth) =
  let l = left t in let r = right t in
  if Seq.mem s (symbol_seq l) then
    let zero = Seq.create 1 false in
    if depth = 1 then zero else zero @| code_partial l s (depth - 1)
  else
    let one = Seq.create 1 true in
    if depth = 1 then one else one @| code_partial r s (depth - 1)

#reset-options
unfold let code (t: non_leaf) (s: tree_symbol t): Tot (BV.bv_t (code_len t s)) =
  code_partial t s (code_len t s)

let rec encode (t: non_leaf) (s: seq nat{
  forall i. mem s.[i] (symbol_seq t)
}):
  Tot (Seq.seq bool)
  (decreases Seq.length s) =
  let l = left t in let r = right t in
  if Seq.length s > 0 then code t (head s) @| encode t (tail s) else empty #bool

private let rec do_decode (r: root) (t: well_formed_tree) (s: seq bool):
  Tot (o: option (seq nat){
    match o with
    | Some s -> Seq.length s > 0
    | None -> True
  })
  (decreases %[Seq.length s; if Leaf? t && Seq.length s > 0 then 1 else 0]) =
  if Leaf? t then
    if Seq.length s > 0 then
      match do_decode r r s with
      | Some res -> Some ((create 1 (symbol t)) @| res)
      | None -> None
    else
      Some (create 1 (symbol t))
  else
    match Seq.length s with
    | 0 -> None
    | _ ->
      if head s then
        do_decode r (right t) (tail s)
      else
        do_decode r (left t) (tail s)

let decode (r: root) (s: seq bool):
  Tot (option (seq nat))
  (decreases Seq.length s) = do_decode r r s

let rec leaf_count (t: well_formed_tree) (h: nat): Tot nat =
  match t with
  | Root _ l r -> 
    if h > 0 then leaf_count l (h - 1) + leaf_count r (h - 1) else 0
  | Internal _ _ l r ->
    if h > 0 then leaf_count l (h - 1) + leaf_count r (h - 1) else 0
  | Leaf _ len' _ ->
    if h = 0 then 1 else 0

private let rec do_total_leaf_count (t: well_formed_tree) (h: nat): Tot nat =
  leaf_count t h + (if h > 0 then do_total_leaf_count t (h - 1) else 0)

let total_leaf_count (t: well_formed_tree) = do_total_leaf_count t (height t)

val height_one: (t: well_formed_tree) -> Lemma
  (requires height t  == 1)
  (ensures Leaf? t == false /\ Leaf? (left t) /\ Leaf? (right t))
  [SMTPat (height t)]

val height_gt_one: (t: well_formed_tree) -> Lemma
  (requires height t > 1)
  (ensures Leaf? t == false /\ (Leaf? (left t) == false \/ Leaf? (right t) == false))
  [SMTPat (height t)]

val leaf_count_gt_height: (t: well_formed_tree) -> (h: nat{h > height t}) -> Lemma
  (ensures leaf_count t h == 0)
  [SMTPat (leaf_count t h)]

val total_leaf_count_lr: (t: non_leaf) -> Lemma
  (ensures total_leaf_count t = total_leaf_count (left t) + total_leaf_count (right t))
  [SMTPatOr
    [[SMTPat (total_leaf_count t)];
    [SMTPat (total_leaf_count (left t))];
    [SMTPat (total_leaf_count (right t))]]]

val total_leaf_count_lower_bound: (t: well_formed_tree) -> Lemma
  (ensures total_leaf_count t >= 1 + height t)
  [SMTPat (total_leaf_count t)]

val total_leaf_count_upper_bound: (t: well_formed_tree) -> Lemma
  (ensures total_leaf_count t <= pow2 (height t))
  [SMTPat (total_leaf_count t)]

private let rec do_leaf_count_seq
  (t: root)
  (h: nat{h <= height t}) :
  s: Seq.seq nat{
    Seq.length s == h + 1 /\ (forall i. {:pattern (s.[i])} s.[i] == leaf_count t i)
  } =
  if h > 0 then
    do_leaf_count_seq t (h - 1) `snoc` leaf_count t h
  else
    Seq.create 1 (leaf_count t h)

type lc_seq (t: root) = s: Seq.seq nat{
  Seq.length s == height t + 1 /\
  (forall i. {:pattern (s.[i]); (leaf_count t i)} s.[i] == leaf_count t i)
}
  
let leaf_count_seq (t: root): lc_seq t =
  do_leaf_count_seq t (height t)

let rec min_leaf_depth (t: well_formed_tree): d: nat{
  d <= height t /\
  (forall (i: nat). {:pattern (leaf_count t i)} i < d ==> leaf_count t i == 0)
} =
  if Leaf? t then
    0
  else
    let l = min_leaf_depth (left t) in
    let r = min_leaf_depth (right t) in
    1 + (if l < r then l else r)

let min_leaf_depth_aux (t: root): Lemma
  (ensures forall (i: nat). {:pattern (leaf_count_seq t).[i]}
    i < min_leaf_depth t ==> (leaf_count_seq t).[i] == 0)
  [SMTPat (min_leaf_depth t)] = ()

val min_leaf_depth_leaf_count: (t: well_formed_tree) -> Lemma
  (ensures leaf_count t (min_leaf_depth t) > 0)
  [SMTPat (min_leaf_depth t)]

val min_leaf_depth_lt_pow2: (t: well_formed_tree) -> (h: nat) -> Lemma
  (requires total_leaf_count t < pow2 h)
  (ensures min_leaf_depth t < h)

val encode_decode_cancel: (r: root) -> (s: seq nat{
  forall i. Seq.mem s.[i] (symbol_seq r)
}) -> Lemma
  (requires Seq.length s > 0)
  (ensures decode r (encode r s) == Some s)
  (decreases Seq.length s)

val code_height: (t: non_leaf) -> (s: tree_symbol t) -> Lemma
  (ensures Seq.length (code t s) <= height t)
  [SMTPat (Seq.length (code t s))]

let rec canonical (t: well_formed_tree) =
  if Leaf? t then
    True
  else
    let l = left t in let r = right t in
    let s = symbol_seq t in
    (forall i j. // {:pattern
      // (code_len t s.[i] < code_len t s.[j]) \/
      // (code_len t s.[i] == code_len t s.[j] /\ s.[i] < s.[j])}
      i < j ==>
        code_len t s.[i] < code_len t s.[j] \/
        (code_len t s.[i] == code_len t s.[j] /\ s.[i] < s.[j])) /\
    canonical l /\ canonical r

type canonical_tree = t: well_formed_tree{canonical t}

type canonical_non_leaf = t: canonical_tree{Leaf? t == false}

#set-options "--z3refresh --z3rlimit 256"
val symbol_seq_len_aux: (t: non_leaf) -> Lemma
  (ensures Seq.length (symbol_seq t) == total_leaf_count t)
  [SMTPatOr [[SMTPat (Seq.length (symbol_seq t))]; [SMTPat (total_leaf_count t)]]]

val leftmost_code_vec: (t: non_leaf) -> Lemma
  (ensures code t (symbol_seq t).[0] == BV.zero_vec #(code_len t (symbol_seq t).[0]))
  [SMTPat (code t (symbol_seq t).[0])]

let leftmost_code_val (t: non_leaf): Lemma
  (ensures UInt.from_vec #(code_len t (symbol_seq t).[0]) (code t (symbol_seq t).[0]) == 0)
  [SMTPat (UInt.from_vec #(code_len t (symbol_seq t).[0]) (code t (symbol_seq t).[0]))] =
  leftmost_code_vec t

val rightmost_code_vec: (t: non_leaf) -> Lemma
  (ensures code t (last (symbol_seq t)) == BV.ones_vec #(code_len t (last (symbol_seq t))))
  [SMTPat (code t (last (symbol_seq t)))]

let rightmost_code_val (t: non_leaf): Lemma
  (ensures UInt.from_vec
    #(code_len t (last (symbol_seq t)))
    (code t (last (symbol_seq t))) == pow2 (code_len t (last (symbol_seq t))) - 1)
  [SMTPat (UInt.from_vec
    #(code_len t (last (symbol_seq t)))
    (code t (last (symbol_seq t))))] =
  rightmost_code_vec t

val code_partial_next: (t: non_leaf) -> (i: nat) -> (depth: pos) -> Lemma
  (requires
    i < total_leaf_count t - 1 /\
    depth == code_len t (symbol_seq t).[i] /\
    depth == code_len t (symbol_seq t).[i + 1])
  (ensures
    UInt.from_vec #depth (code t (symbol_seq t).[i]) + 1 ==
    UInt.from_vec #depth (code t (symbol_seq t).[i + 1]))

unfold let tree_correspond
  (h0 h1: HS.mem) (t: root) (tree: B.buffer ct_data)
  (max_code: U32.t) =
  let max_code = U32.v max_code in
  let t0 = B.as_seq h0 tree in
  let t1 = B.as_seq h1 tree in
  height t <= 16 /\
  max_code < B.length tree /\
  (forall (i: nat{i < max_code /\ U16.v (t0.[i]).freq_or_code > 0}).
    mem i (symbol_seq t) /\
    U16.v (t1.[i]).dad_or_len == Seq.length (code t i) /\
    U16.v (t1.[i]).freq_or_code == UInt.from_vec #(Seq.length (code t i)) (code t i))

unfold let kraft_term (n: nat): rat = (1, pow2 n)

let kraft_term_plus (n: pos): Lemma
  (ensures kraft_term n +$ kraft_term n =$ kraft_term (n - 1))
  [SMTPat (kraft_term n +$ kraft_term n)] = ()

let rec term_times (l: pos) (n: nat): rat =
  match n with
  | 0 -> zero
  | _ -> kraft_term l +$ term_times l (n - 1)

let rec kraft_sum (t: well_formed_tree): rat =
  match t with
  | Root _ l r -> kraft_sum l +$ kraft_sum r
  | Internal _ _ l r -> kraft_sum l +$ kraft_sum r
  | Leaf _ len _ -> kraft_term len  

val kraft_sum_non_root: (t: well_formed_tree) -> Lemma
  (requires Root? t == false)
  (ensures kraft_sum t =$ kraft_term (length t))
  [SMTPat (kraft_sum t)]

val kraft_sum_root: (t: root) -> Lemma
  (ensures kraft_sum t =$ one)
  [SMTPat (kraft_sum t)]

let rec kraft_sum_lc_seq (#t: root) (s: lc_seq t) (i: nat{i <= height t}):
  Tot rat
  (decreases (height t - i)) =
  if i < height t then
    (s.[i], pow2 i) +$ kraft_sum_lc_seq s (i + 1)
  else
    zero

let tree_context_valid (h: HS.mem) (c: CB.const_buffer tree_context) =
  CB.length c == 1 /\ CB.live h c /\
  (let ctx = B.get h (CB.as_mbuf c) 0 in
  B.live h ctx.dyn_ltree /\ B.live h ctx.dyn_dtree /\ B.live h ctx.bl_tree /\
  B.live h ctx.bl_count /\ B.live h ctx.heap /\ B.live h ctx.depth /\ B.live h ctx.l_buf /\
  B.live h ctx.d_buf /\ B.live h ctx.pending_buf /\
  CB.live h ctx.l_desc.stat_desc /\ CB.live h ctx.d_desc.stat_desc /\
  CB.live h ctx.bl_desc.stat_desc /\

  B.frameOf ctx.dyn_dtree == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.bl_tree == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.bl_count == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.heap == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.depth == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.l_buf == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.d_buf == B.frameOf ctx.dyn_ltree /\
  B.frameOf ctx.pending_buf == B.frameOf ctx.dyn_ltree /\

  B.frameOf (CB.as_mbuf ctx.l_desc.stat_desc) ==
  B.frameOf (CB.as_mbuf ctx.d_desc.stat_desc) /\
  B.frameOf (CB.as_mbuf ctx.bl_desc.stat_desc) ==
  B.frameOf (CB.as_mbuf ctx.d_desc.stat_desc) /\

  HS.disjoint (B.frameOf (CB.as_mbuf ctx.d_desc.stat_desc)) (B.frameOf ctx.dyn_ltree) /\
  
  B.disjoint ctx.dyn_ltree ctx.dyn_dtree /\ B.disjoint ctx.dyn_ltree ctx.bl_tree /\
  B.disjoint ctx.dyn_ltree ctx.bl_count /\ B.disjoint ctx.dyn_ltree ctx.heap /\
  B.disjoint ctx.dyn_ltree ctx.depth /\ B.disjoint ctx.dyn_ltree ctx.l_buf /\
  B.disjoint ctx.dyn_ltree ctx.d_buf /\ B.disjoint ctx.dyn_ltree ctx.pending_buf /\
  B.disjoint ctx.dyn_dtree ctx.bl_tree /\ B.disjoint ctx.dyn_dtree ctx.bl_count /\
  B.disjoint ctx.dyn_dtree ctx.heap /\ B.disjoint ctx.dyn_dtree ctx.depth /\
  B.disjoint ctx.dyn_dtree ctx.l_buf /\ B.disjoint ctx.dyn_dtree ctx.d_buf /\
  B.disjoint ctx.dyn_dtree ctx.pending_buf /\ B.disjoint ctx.bl_tree ctx.bl_count /\
  B.disjoint ctx.bl_tree ctx.heap /\ B.disjoint ctx.bl_tree ctx.depth /\
  B.disjoint ctx.bl_tree ctx.l_buf /\ B.disjoint ctx.bl_tree ctx.d_buf /\
  B.disjoint ctx.bl_tree ctx.pending_buf /\ B.disjoint ctx.bl_count ctx.heap /\
  B.disjoint ctx.bl_count ctx.depth /\ B.disjoint ctx.bl_count ctx.l_buf /\
  B.disjoint ctx.bl_count ctx.d_buf /\ B.disjoint ctx.bl_count ctx.pending_buf /\
  B.disjoint ctx.heap ctx.depth /\ B.disjoint ctx.heap ctx.l_buf /\
  B.disjoint ctx.heap ctx.d_buf /\ B.disjoint ctx.heap ctx.pending_buf /\ 
  B.disjoint ctx.depth ctx.l_buf /\ B.disjoint ctx.depth ctx.d_buf /\
  B.disjoint ctx.depth ctx.pending_buf /\ B.disjoint ctx.l_buf ctx.d_buf /\
  B.disjoint ctx.l_buf ctx.pending_buf /\ B.disjoint ctx.d_buf ctx.pending_buf /\
  
  4 * U32.v ctx.lit_bufsize == U32.v ctx.pending_buf_size /\
  B.length ctx.l_buf == U32.v ctx.lit_bufsize /\
  B.length ctx.d_buf == U32.v ctx.lit_bufsize /\
  B.length ctx.pending_buf == U32.v ctx.pending_buf_size /\
  CB.length ctx.l_desc.stat_desc == 1 /\
  CB.length ctx.d_desc.stat_desc == 1 /\
  CB.length ctx.bl_desc.stat_desc == 1 /\
  
  (let l_stat_desc = B.get h (CB.as_mbuf ctx.l_desc.stat_desc) 0 in
  let d_stat_desc = B.get h (CB.as_mbuf ctx.d_desc.stat_desc) 0 in
  let bl_stat_desc = B.get h (CB.as_mbuf ctx.bl_desc.stat_desc) 0 in
  U32.v l_stat_desc.extra_base == U32.v literals + 1 /\
  U32.v d_stat_desc.extra_base == 0 /\
  U32.v bl_stat_desc.extra_base == 0 /\
  U32.v l_stat_desc.elems == U32.v l_codes /\
  U32.v d_stat_desc.elems == U32.v d_codes /\
  U32.v bl_stat_desc.elems == U32.v bl_codes /\
  U32.v l_stat_desc.max_length == 15 /\
  U32.v d_stat_desc.max_length == 15 /\
  U32.v bl_stat_desc.max_length == 7))
