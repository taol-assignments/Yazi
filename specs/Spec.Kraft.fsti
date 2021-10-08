module Spec.Kraft

module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Lib.Rational

type tree = 
  | Node: left: tree -> right: tree -> tree
  | Leaf: symbol: nat -> tree

type non_leaf = t: tree{Leaf? t == false}

unfold let left (t: non_leaf) =
  match t with
  | Node l _ -> l

unfold let right (t: non_leaf) =
  match t with
  | Node _ r -> r

let rec height (t: tree): Tot nat =
  match t with
  | Node l r ->
    let lh = height l in let rh = height r in
    1 + (if lh > rh then lh else rh)
  | _ -> 0

let rec leaf_count (t: tree): Tot pos = 
  match t with
  | Node l r -> leaf_count l + leaf_count r
  | _ -> 1

let max_leaf_count (t: tree): Tot pos = pow2 (height t)

let rec bit_length (t: tree) (h: nat): Tot nat =
  match t with
  | Node l r ->
    if h = 0 then 0 else bit_length l (h - 1) + bit_length r (h - 1)
  | _ ->
    if h = 0 then 1 else 0

val lemma_max_leaf_count: (t: tree) -> Lemma
  (ensures leaf_count t <= max_leaf_count t)

val lemma_non_full_bit_length: (t: tree) -> (h: nat) -> Lemma
  (requires leaf_count t < pow2 h)
  (ensures exists i. i < h /\ bit_length t i > 0)

let kraft_sum (len: seq pos): Tot rat =
  if length len = 0 then
    zero
  else
    sigma 0 (length len - 1) (fun j -> 1, pow2 len.[j])

type sym_seq = sym: seq nat{
  length sym >= 2 /\ no_dup sym
}

type len_seq = len: seq pos{
  length len >= 2 /\ kraft_sum len <=$ one
}

let rec kraft_sorted
  (sym: seq nat) (len: seq pos{length sym == length len}):
  Tot bool (decreases length sym) =
  if length sym <= 1 then
    true
  else
    let (s1, s2) = (head sym, sym.[1]) in
    let (l1, l2) = (head len, len.[1]) in
    (l1 < l2 || l1 = l2 && s1 < s2) && kraft_sorted (tail sym) (tail len)

let kraft_cond (sym: sym_seq) (len: len_seq) =
  length sym == length len /\ kraft_sorted sym len

val lemma_kraft_sorted: sym: seq nat -> len: seq pos -> i: nat -> j: nat -> Lemma
  (requires length sym == length len /\ kraft_sorted sym len /\ i <= j /\ j < length len)
  (ensures len.[i] <= len.[j])
  (decreases length len)

private let rec do_kraft_code (sym: sym_seq) (len: len_seq) (i j: nat): Pure nat
  (requires kraft_cond sym len /\ i < j /\ j < length len)
  (ensures fun _ -> True)
  (decreases j - i) =
  lemma_kraft_sorted sym len i j;
  if i + 1 = j then
    pow2 (len.[j] - len.[i])
  else
    pow2 (len.[j] - len.[i]) + do_kraft_code sym len (i + 1) j

let kraft_code (sym: sym_seq) (len: len_seq) (i: nat): Pure nat
  (requires kraft_cond sym len /\ i < length len)
  (ensures fun _ -> True) =
  if i = 0 then 0 else do_kraft_code sym len 0 i

val lemma_kraft_code_upper_bound:
    (sym: sym_seq)
  -> (len: len_seq)
  -> (i: nat)
  -> Lemma
  (requires kraft_cond sym len /\ i < length len)
  (ensures kraft_code sym len i < pow2 len.[i])
  [SMTPat (kraft_code sym len i)]

val lemma_kraft_code_next: sym: sym_seq -> len: len_seq -> i: pos -> Lemma
  (requires kraft_cond sym len /\ i < length len)
  (ensures
    len.[i] >= len.[i - 1] /\
    kraft_code sym len i ==
    (kraft_code sym len (i - 1) + 1) * pow2 (len.[i] - len.[i - 1]))

#push-options "--fuel 0"
let kraft_code_uint (sym: sym_seq) (len: len_seq) (i: nat{i < length len}):
  Pure (UInt.uint_t len.[i])
  (requires kraft_cond sym len)
  (ensures fun c -> c == kraft_code sym len i) =
  if i = 0 then
    0
  else begin
    lemma_kraft_sorted sym len (i - 1) i;
    lemma_kraft_code_upper_bound sym len i;
    lemma_kraft_code_next sym len i;
    let c = UInt.shift_left
      #len.[i]
      (kraft_code sym len (i - 1) + 1)
      (len.[i] - len.[i - 1])
    in
    calc (==) {
      kraft_code sym len i;
      =={
        Math.modulo_lemma (kraft_code sym len i) (pow2 len.[i])
      }
      (kraft_code sym len i) % pow2 len.[i];
      =={lemma_kraft_code_next sym len i}
      ((kraft_code sym len (i - 1) + 1) * pow2 (len.[i] - len.[i - 1])) % pow2 len.[i];
      =={
        UInt.shift_left_value_lemma
          #len.[i]
          (kraft_code sym len (i - 1) + 1)
          (len.[i] - len.[i - 1])
      }
      c;
    };
    c
  end
#pop-options

let prefix (#n #m: nat) (a: UInt.uint_t n) (b: UInt.uint_t m): bool =
  if n > m then
    false
  else
    let a' = UInt.to_vec a in
    let b' = UInt.to_vec b in
    slice a' 0 n = slice b' 0 n

// val kraft_code_prefix: sym: sym_seq -> len: len_seq -> i: nat -> j: nat -> Lemma
//   (requires kraft_cond sym len /\ i < j /\ j < length len)
//   (ensures prefix a b == false)
