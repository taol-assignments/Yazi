module Spec.Heap

module B = LowStar.Buffer
module C = Yazi.Deflate.Constants
module HS = FStar.HyperStack
module Math = FStar.Math.Lemmas
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Yazi.Deflate.Constants
open Yazi.Tree.Types

type cmp_spec =
    tl: nat 
  -> tree: Seq.seq ct_data{Seq.length tree == tl}
  -> depth: Seq.seq U8.t{Seq.length depth == 2 * U32.v C.l_codes + 1}
  -> i: U32.t{U32.v i < tl /\ U32.v i < length depth}
  -> j: U32.t{U32.v j < tl /\ U32.v j < length depth}
  -> Tot bool

val build_cmp: cmp_spec
let build_cmp tl tree depth i j =
  let open U32 in
  let fi = U16.v (tree.[v i]).freq_or_code in
  let fj = U16.v (tree.[v j]).freq_or_code in
  (fi < fj ||
  (fi = fj && U8.v depth.[v i] < U8.v depth.[v j]) ||
  (fi = fj && U8.v depth.[v i] = U8.v depth.[v j] && v i <= v j))

let heap_elem (tl: tree_len_t) (depth: tree_depth_t) (a: U32.t) =
  U32.v a < tl /\ U32.v a < B.length depth

let partial_well_formed
  (cmp: cmp_spec) (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: heap_index_t hl) =
  let open U32 in
  let hl = v hl in
  let heap_elem = heap_elem tl depth in
  let heap = B.as_seq h heap in
  let tree = B.as_seq h tree in
  let depth = B.as_seq h depth in
  let smaller = cmp tl tree depth in
  (forall a. a `smaller` a) /\
  (forall a b. a `smaller` b /\ b `smaller` a ==> a == b) /\
  (forall a b c. a `smaller` b /\ b `smaller` c ==> a `smaller` c) /\
  (forall a b. a `smaller` b \/ b `smaller` a) /\
  (forall (j: pos). j <= hl ==> v heap.[j] < tl) /\
  (forall (k: nat). (v i <= k /\ k <= hl) ==> (
    heap_elem heap.[k] /\
    (k * 2 <= hl ==>
      heap_elem heap.[k * 2] /\ heap.[k] `smaller` heap.[k * 2]) /\
    (k * 2 + 1 <= hl ==>
      heap_elem heap.[k * 2 + 1] /\ heap.[k] `smaller` heap.[k * 2 + 1])))

let well_formed
  (cmp: cmp_spec) (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t) =
  partial_well_formed cmp h heap hl tl tree depth 1ul

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

private let rec parent_next (a: pos) (i: pos{1 < i /\ i <= log2 a}): Lemma
  (ensures parent a i == parent a (i - 1) / 2) =
  match i with
  | 2 -> ()
  | _ -> parent_next (a / 2) (i - 1)

#set-options "--z3refresh --z3rlimit 512 --fuel 1 --ifuel 0"
private let rec partial_well_formed_max
  (cmp: cmp_spec) (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: nat) (j: pos) : Lemma
  (requires
    i < log2 j /\ j <= U32.v hl /\ pow2 i < j /\
    partial_well_formed cmp h heap hl tl tree depth (U32.uint_to_t (pow2 i)))
  (ensures
    pow2 i <= parent j ((log2 j) - i) /\
    parent j ((log2 j) - i) < pow2 (i + 1) /\
    cmp tl (B.as_seq h tree) (B.as_seq h depth)
      (B.as_seq h heap).[parent j ((log2 j) - i)] (B.as_seq h heap).[j])
  (decreases U32.v hl - pow2 i) =
  if j < pow2 (i + 2) then begin
    log2_pow2_lt j i;
    log2_pow2_gt j (i + 2)
  end else begin
    partial_well_formed_max cmp h heap hl tl tree depth (i + 1) j;
    parent_next j ((log2 j) - i)
  end

private let heap_max'
  (cmp: cmp_spec) (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t)
  (i: pos{1 < i /\ i <= U32.v hl}) : Lemma
  (requires well_formed cmp h heap hl tl tree depth)
  (ensures cmp tl (B.as_seq h tree) (B.as_seq h depth)
    (B.as_seq h heap).[1] (B.as_seq h heap).[i]) =
  partial_well_formed_max cmp h heap hl tl tree depth 0 i

let heap_max
  (cmp: cmp_spec) (h: HS.mem)
  (heap: tree_heap_t) (hl: heap_len_t)
  (tl: tree_len_t) (tree: B.lbuffer ct_data tl) (depth: tree_depth_t): Lemma
  (requires well_formed cmp h heap hl tl tree depth)
  (ensures forall i.
    let tree = B.as_seq h tree in
    let depth = B.as_seq h depth in
    let heap = B.as_seq h heap in
    1 < i /\ i < U32.v hl ==> cmp tl tree depth heap.[1] heap.[i]) =
  Classical.forall_intro (Classical.move_requires (heap_max' cmp h heap hl tl tree depth))
