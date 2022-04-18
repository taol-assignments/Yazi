module Spec.Package

open FStar.Mul
open FStar.Seq
open Lib.Rational
open Lib.Seq

type item_t = 
  | Leaf: id: nat -> exp: pos -> weight: pos -> item_t
  | Package: i1: item_t -> i2: item_t -> item_t

let rec exp i : Tot int =
  match i with
  | Leaf _ e _ -> e
  | Package i1 _ -> exp i1 - 1

let rec item_weight i : Tot pos =
  match i with
  | Leaf _ _ w -> w
  | Package i1 i2 -> item_weight i1 + item_weight i2

let rec item_wf (i: item_t) =
  match i with
  | Leaf _ _ _ -> true
  | Package i1 i2 -> exp i1 = exp i2 && item_wf i1 && item_wf i2

let item_id (i: item_t{Leaf? i}) = match i with | Leaf id _ _ -> id

type item = i: item_t{item_wf i}

let item_width (i: item): Tot rat = qpow2 (exp i)

type item_seq (e: pos) = s: seq item{forall i. exp s.[i] == e}

let rec wseq_sorted (w: seq pos): Tot bool (decreases length w) =
  match length w with
  | 0 | 1 -> true
  | _ -> w.[0] <= w.[1] && wseq_sorted (tail w)

type weight_seq = w: seq pos{wseq_sorted w /\ length w >= 2}

type base_set (e: pos) (w: weight_seq) = s: item_seq e{
  length w == length s /\
  (forall i. Leaf? s.[i] /\ item_id s.[i] == i /\ item_weight s.[i] == w.[i] /\ exp s.[i] == e)
}

[@"opaque_to_smt"] 
let make_base_set (e: pos) (w: weight_seq): Tot (base_set e w) =
  init #item (length w) (fun i -> Leaf i e w.[i])

let rec weight_sorted (w: seq item): Tot bool (decreases length w) =
  match length w with
  | 0 | 1 -> true
  | _ -> item_weight w.[0] <= item_weight w.[1] && weight_sorted (tail w)

unfold let id_monotone (s: seq item) (w: weight_seq) (i: index_t s{Leaf? s.[i]}) =
  item_id s.[i] < length w /\
  (item_id s.[i] > 0 ==>
    mem (Leaf (item_id s.[i] - 1) (exp s.[i]) (w.[item_id s.[i] - 1])) s)

unfold let exp_bound (s: seq item) (hi lo: pos) (i: index_t s{Leaf? s.[i]}) =
  hi >= exp s.[i] /\ exp s.[i] >= lo

unfold let exp_monotone (s: seq item) (hi lo: pos) (i: index_t s{Leaf? s.[i]}) =
  lo < exp s.[i] /\ exp s.[i] <= hi ==>
    mem (Leaf (item_id s.[i]) (exp s.[i] - 1) (item_weight s.[i])) s

unfold let weight_corr (s: seq item) (w: weight_seq) (i: index_t s{Leaf? s.[i]}) =
  item_id s.[i] < length w /\ w.[item_id s.[i]] == item_weight s.[i]

unfold let monotone_elem (s: seq item) (w: weight_seq) (hi lo: pos) (i: index_t s) =
  Leaf? s.[i] /\ id_monotone s w i /\
  exp_bound s hi lo i /\ exp_monotone s hi lo i /\
  weight_corr s w i

let monotone (s: seq item) (w: weight_seq) (hi lo: pos) =
  no_dup s /\ hi >= lo /\ (forall i. monotone_elem s w hi lo i)

let rec filter_leaves (s: seq item):
  Tot (s': seq item{forall i. Leaf? s'.[i]})
  (decreases length s) =
  match length s with
  | 0 -> empty #item
  | _ ->
    match Leaf? s.[0] with
    | true -> cons s.[0] (filter_leaves (tail s))
    | false -> filter_leaves (tail s)

let rec unfold_packages (s: seq item): Tot (seq item) (decreases length s) =
  match length s with
  | 0 -> empty #item
  | _ ->
    match s.[0] with
    | Package i1 i2 -> cons i1 (cons i2 (unfold_packages (tail s)))
    | _ -> unfold_packages (tail s)

let rec unfold_solution (s: seq item) (i: nat):
  Tot (s': seq item{forall i. Leaf? s'.[i]})
  (decreases i) =
  match i with
  | 0 -> filter_leaves s
  | _ -> (unfold_solution (unfold_packages s) (i - 1)) @| filter_leaves s

val lemma_weight_seq_slice: w: weight_seq -> i: nat -> j: nat -> Lemma
  (requires i <= j /\ j <= length w)
  (ensures wseq_sorted (slice w i j))
  (decreases j)
  [SMTPat (wseq_sorted (slice w i j))]

private let rec solution_sum' (s: seq item): Tot rat (decreases length s) =
  match length s with
  | 0 -> zero
  | _ -> qpow2 (-exp s.[0]) +$ solution_sum' (tail s)

let solution_sum (hi: pos) (lo: pos{hi >= lo}) (s: seq item{
  length (unfold_solution s (hi - lo)) > 0
}): Tot rat = solution_sum' (unfold_solution s (hi - lo))

unfold let solution_wf
  (hi: pos) (lo: pos{hi >= lo}) (w: weight_seq)
  (s: item_seq lo{length s >= 2}) (i: nat{2 <= i /\ i <= length s}): Tot Type0 =
  let s' = slice s 0 i in
  let l = length (filter_leaves s') in
  2 <= l /\ l <= length w /\
  filter_leaves s' == make_base_set lo (slice w 0 l) /\
  solution_sum hi lo s' =$ qpow2 (-lo) *$ (of_int i) /\
  monotone (unfold_solution s' (hi - lo)) (slice w 0 l) hi lo

unfold let top2_leaf (#e: pos) (s: item_seq e) (w: weight_seq) =
  (length s > 0 /\ length w > 0 ==> s.[0] == Leaf 0 e w.[0]) /\
  (length s > 1 /\ length w > 1 ==> s.[1] == Leaf 1 e w.[1])

type solution (hi: pos) (lo: pos{hi >= lo}) (w: weight_seq) = s: item_seq lo {
  length (filter_leaves s) == length w /\
  weight_sorted s /\
  top2_leaf s w /\
  (forall i. solution_wf hi lo w s i)
}

type leaf_index_t (w: weight_seq) (lt: bool) = i: pos{
  2 <= i /\
  (lt == true ==> i < length w) /\
  (lt == false ==> i <= length w)
}

type package_index_t (prev: seq item) (lt: bool) = j: nat{
  j % 2 == 0 /\
  (lt == true ==> j < length prev - 1) /\
  (lt == false ==> j <= length prev)
}

let merge_invariant 
  (e: pos) (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w false) (j: package_index_t prev false) (s: seq item{length s > 0}) =
  (i < length w ==>
    item_weight (last s) <= item_weight (make_base_set e w).[i]) /\
  (j < length prev - 1 ==>
    item_weight (last s) <= item_weight prev.[j] + item_weight prev.[j + 1])

type intermidiate_exp (hi: pos) = lo: pos{hi >= lo /\ lo > 1}

type intermidiate_solution
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false) =
  s: solution hi (lo - 1) (slice w 0 i) {
    length s == i + j / 2 /\
    unfold_packages s == slice prev 0 j /\
    merge_invariant (lo - 1) w prev i j s
  }

let leaf_smaller
  (e: pos) (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w true) (j: package_index_t prev false) =
  let base = make_base_set e w in
  j < length prev - 1 ==>
    item_weight base.[i] <= item_weight prev.[j] + item_weight prev.[j + 1]

val lemma_snoc_leaf:
  #hi: pos -> #lo: intermidiate_exp hi -> #w: weight_seq -> prev: solution hi lo w ->
  i: leaf_index_t w true -> j: package_index_t prev false ->
  x: intermidiate_solution prev i j -> Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    let w' = slice w 0 (i + 1) in
    length (filter_leaves x') == i + 1 /\
    weight_sorted x' /\
    top2_leaf #(lo - 1) x' w' /\
    (forall k. solution_wf hi (lo - 1) w' x' k) /\
    length x' == (i + 1) + j / 2 /\
    unfold_packages x' == slice prev 0 j /\
    merge_invariant (lo - 1) w prev (i + 1) j x'))

let package_smaller
  (e: pos) (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w false) (j: package_index_t prev true) =
  let base = make_base_set e w in
  i < length w ==>
    item_weight base.[i] > item_weight prev.[j] + item_weight prev.[j + 1]

#set-options "--fuel 1 --ifuel 1 --z3rlimit 128"
val lemma_snoc_package:
  #hi: pos -> #lo: intermidiate_exp hi -> #w: weight_seq -> prev: solution hi lo w ->
  i: leaf_index_t w false -> j: package_index_t prev true ->
  x: intermidiate_solution prev i j -> Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    let w' = slice w 0 i in
    length (filter_leaves x') == i /\
    weight_sorted x' /\
    top2_leaf #(lo - 1) x' w' /\
    (forall k. solution_wf hi (lo - 1) w' x' k) /\
    length x' == i + (j + 2) / 2 /\
    unfold_packages x' == slice prev 0 (j + 2) /\
    merge_invariant (lo - 1) w prev i (j + 2) x'))

let rec merge
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j):
  Tot (s: solution hi (lo - 1) w {
    length s == length w + length prev / 2
  }) (decreases %[length w - i; length prev - j]) =
  match (i < length w, j + 1 < length prev) with
  | (true, true) ->
    let l = Leaf i (lo - 1) w.[i] in
    let p = Package prev.[j] prev.[j + 1] in
    (match item_weight p < item_weight l with
    | true ->
      lemma_snoc_package prev i j x;
      merge prev i (j + 2) (snoc x p)
    | false ->
      lemma_snoc_leaf prev i j x;
      merge prev (i + 1) j (snoc x l))
  | (false, true) -> 
    lemma_snoc_package prev i j x;
    merge prev i (j + 2) (snoc x (Package prev.[j] prev.[j + 1]))
  | (true, false) ->
    lemma_snoc_leaf prev i j x;
    merge prev (i + 1) j (snoc x (Leaf i (lo - 1) w.[i]))
  | (false, false) -> x
