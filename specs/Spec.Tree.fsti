module Spec.Tree

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module HS = FStar.HyperStack
module U32 = FStar.UInt32

open Lib.Rational
open Lib.Seq
open FStar.Mul
open FStar.Seq
open Yazi.Tree.Types

type tree =
  | Root: freq: pos -> left: tree -> right: tree -> tree
  | Internal: freq: pos -> len: pos -> left: tree -> right: tree -> tree
  | Leaf: freq: pos -> len: pos -> symbol: nat -> tree

let freq (t: tree{Root? t == false}): pos =
  match t with
  | Internal freq _ _ _ -> freq
  | Leaf freq _ _ -> freq

let length (t: tree): nat =
  match t with
  | Root _ _ _ -> 0
  | Internal _ len _ _ -> len
  | Leaf _ len _ -> len

let rec well_formed (t: tree): Type0 =
  match t with
  | Root f l r ->
    Root? l == false /\ Root? r == false /\
    length l == 1 /\ length r == 1 /\
    well_formed l /\ well_formed r
  | Internal f len l r ->
    Root? l == false /\ Root? r == false /\
    length l == len + 1 /\ length r == len + 1 /\
    well_formed l /\ well_formed r
  | _ -> True

private let rec optimal' (t: tree{well_formed t}): Type0 =
  match t with
  | Root f l r -> freq l + freq r == f /\ optimal' l /\ optimal' r
  | Internal f len l r -> freq l + freq r == f /\ optimal' l /\ optimal' r
  | Leaf _ _ _ -> True

let optimal (t: tree): Type0 = well_formed t /\ optimal' t

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
  [SMTPat (total_leaf_count t)]

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

#set-options "--z3rlimit 200"
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
  CB.length ctx.bl_desc.stat_desc == 1)
