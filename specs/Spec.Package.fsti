module Spec.Package

module UInt = FStar.UInt

open FStar.Mul
open FStar.Seq
open Lib.Rational
open Lib.Seq
open Spec.Kraft

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

let rec weight_sum (s: seq pos{length s > 0}): Tot pos (decreases length s) =
  match length s with
  | 1 -> s.[0]
  | _ -> s.[0] + weight_sum (tail s)

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

val lemma_filter_leaves_len_gt: s: seq item -> Lemma
  (ensures length s >= length (filter_leaves s))
  (decreases length s)

let rec unfold_packages (s: seq item): Tot (seq item) (decreases length s) =
  match length s with
  | 0 -> empty #item
  | _ ->
    match s.[0] with
    | Package i1 i2 -> cons i1 (cons i2 (unfold_packages (tail s)))
    | _ -> unfold_packages (tail s)

type leaf_seq = s: seq item{forall i. Leaf? s.[i]}

let rec unfold_solution (s: seq item) (i: nat):
  Tot leaf_seq
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
  (s: item_seq lo{2 <= length s /\ length s < 2 * length w})
  (i: nat{2 <= i /\ i <= length s}): Tot Type0 =
  let s' = slice s 0 i in
  let l = length (filter_leaves s') in
  2 <= l /\ l <= length w /\
  filter_leaves s' == make_base_set lo (slice w 0 l) /\
  solution_sum hi lo s' =$ qpow2 (-lo) *$ (of_int i) /\
  monotone (unfold_solution s' (hi - lo)) (slice w 0 l) hi lo

unfold let top2_leaf (#e: pos) (s: item_seq e) (w: weight_seq) =
  length s >= 2 /\ s.[0] == Leaf 0 e w.[0] /\ s.[1] == Leaf 1 e w.[1]

let package_gt_div2 (w: weight_seq) (s: seq item{
  length s < 2 * length w
 }) (j: index_t s) =
  j % 2 == 0 /\ j + 1 < length s ==> item_weight (Package s.[j] s.[j + 1]) > w.[j / 2 + 1]

type solution (hi: pos) (lo: pos{hi >= lo}) (w: weight_seq) = s: item_seq lo {
  length (filter_leaves s) == length w /\
  length s < 2 * length w /\
  weight_sorted s /\
  top2_leaf s w /\
  (forall j. package_gt_div2 w s j) /\
  (forall i. solution_wf hi lo w s i)
}

let rec solution_weight_sum (s: seq item{length s > 0}): Tot pos (decreases length s) =
  match length s with
  | 1 -> item_weight s.[0]
  | _ -> item_weight s.[0] + solution_weight_sum (tail s)

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

type intermediate_exp (hi: pos) = lo: pos{hi >= lo /\ lo > 1}

let solution_weight_sum_invariant
  (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w false) (j: package_index_t prev false)
  (s: seq item) =
  length s > 0 ==> solution_weight_sum s == (
  match (i, j) with
  | (0, 0) -> 0
  | (_, 0) -> weight_sum (slice w 0 i)
  | (0, _) -> solution_weight_sum (slice prev 0 j)
  | _ -> weight_sum (slice w 0 i) + solution_weight_sum (slice prev 0 j))

type intermediate_solution
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false) =
  s: solution hi (lo - 1) (slice w 0 i) {
    length s == i + j / 2 /\
    item_weight (last s) >= w.[i - 1] /\
    unfold_packages s == slice prev 0 j /\
    merge_invariant (lo - 1) w prev i j s /\
    (Leaf? (last s) ==> item_weight (last s) == w.[i - 1]) /\
    (j == length prev / 2 * 2 ==> mem (Package prev.[j - 2] prev.[j - 1]) s) /\
    solution_weight_sum_invariant w prev i j s
  }

let leaf_smaller
  (e: pos) (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w true) (j: package_index_t prev false) =
  let base = make_base_set e w in
  j < length prev - 1 ==>
    item_weight base.[i] <= item_weight prev.[j] + item_weight prev.[j + 1]

#set-options "--fuel 1 --ifuel 1 --z3refresh --z3rlimit 128"
val lemma_snoc_leaf:
  #hi: pos -> #lo: intermediate_exp hi -> #w: weight_seq -> prev: solution hi lo w ->
  i: leaf_index_t w true -> j: package_index_t prev false ->
  x: intermediate_solution prev i j -> Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    let w' = slice w 0 (i + 1) in
    length (filter_leaves x') == i + 1 /\
    weight_sorted x' /\
    top2_leaf #(lo - 1) x' w' /\
    (forall k. package_gt_div2 w' x' k) /\
    (forall k. solution_wf hi (lo - 1) w' x' k) /\
    Leaf? (last x') /\
    item_weight (last x') == w.[i] /\
    (j == length prev / 2 * 2 ==> mem (Package prev.[j - 2] prev.[j - 1]) x') /\
    length x' == (i + 1) + j / 2 /\
    unfold_packages x' == slice prev 0 j /\
    merge_invariant (lo - 1) w prev (i + 1) j x' /\
    solution_weight_sum_invariant w prev (i + 1) j x'))

let package_smaller
  (e: pos) (w: weight_seq) (prev: seq item)
  (i: leaf_index_t w false) (j: package_index_t prev true) =
  let base = make_base_set e w in
  i < length w ==>
    item_weight base.[i] > item_weight prev.[j] + item_weight prev.[j + 1]

val lemma_snoc_package:
  #hi: pos -> #lo: intermediate_exp hi -> #w: weight_seq -> prev: solution hi lo w ->
  i: leaf_index_t w false -> j: package_index_t prev true ->
  x: intermediate_solution prev i j -> Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    let w' = slice w 0 i in
    length (filter_leaves x') == i /\
    length x' < 2 * length w' /\
    weight_sorted x' /\
    top2_leaf #(lo - 1) x' w' /\
    (forall k. package_gt_div2 w' x' k) /\
    (forall k. solution_wf hi (lo - 1) w' x' k) /\
    Leaf? (last x') == false /\
    length x' == i + (j + 2) / 2 /\
    mem (Package prev.[j] prev.[j + 1]) x' /\
    unfold_packages x' == slice prev 0 (j + 2) /\
    merge_invariant (lo - 1) w prev i (j + 2) x' /\
    solution_weight_sum_invariant w prev i (j + 2) x'))

#push-options "--fuel 1 --ifuel 0 --z3seed 2 --z3rlimit 1024 --query_stats"
let rec merge
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false)
  (x: intermediate_solution prev i j):
  Tot (s: solution hi (lo - 1) w {
    length s == length w + length prev / 2 /\
    (Leaf? (last s) ==> item_weight (last s) == last w) /\
    mem (Package prev.[length prev / 2 * 2 - 2] prev.[length prev / 2 * 2 - 1]) s /\
    unfold_packages s == slice prev 0 (length prev / 2 * 2) /\
    solution_weight_sum s == weight_sum w +
      solution_weight_sum (slice prev 0 (length prev / 2 * 2))
  }) (decreases %[length w - i; length prev - j]) =
  let n = length w in
  match (i < n, j + 1 < length prev) with
  | (false, false) ->
    assert(slice w 0 i == w);
    x
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
#pop-options

let rec max_exp (s: leaf_seq) (i: nat): Tot (e: nat{
  (forall l. mem l s /\ item_id l == i ==> exp l <= e) /\
  (e > 0 ==> (exists j. exp s.[j] == e /\ item_id s.[j] == i))
}) (decreases length s) =
  match length s with
  | 0 -> 0
  | _ ->
    if item_id s.[0] = i then
      Math.Lib.max (exp s.[0]) (max_exp (tail s) i)
    else
      max_exp (tail s) i

val lemma_max_exp_range:
    #hi: pos
  -> #lo: pos{hi >= lo}
  -> #w: weight_seq
  -> s: solution hi lo w
  -> id: index_t w
  -> Lemma
  (ensures (
    let e = max_exp (unfold_solution s (hi - lo)) id in
    0 < e /\ e <= hi))

type exp_seq #hi #w (s: solution hi 1 w) = l: seq nat{
  length l == length w /\
  (forall i.
    l.[i] > 0 /\ l.[i] <= hi /\
    l.[i] == max_exp (unfold_solution s (hi - 1)) i)
}

[@"opaque_to_smt"] 
let solution_len
  (#hi: pos) (#w: weight_seq) (s: solution hi 1 w): Tot (exp_seq s) =
  let open FStar.Classical in
  let res = init (length w) (fun i -> max_exp (unfold_solution s (hi - 1)) i) in
  forall_intro (lemma_max_exp_range s);
  res

val lemma_init_merge_seq:
    #hi: pos
  -> #lo: pos{1 < lo /\ lo <= hi}
  -> #w: weight_seq
  -> prev: solution hi lo w
  -> Lemma
  (ensures (
    let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
    let w' = slice w 0 2 in
    length x == 2 /\
    filter_leaves x == x /\
    weight_sorted x /\
    top2_leaf #(lo - 1) x w' /\
    package_gt_div2 w x 0 /\
    solution_wf hi (lo - 1) w' x 2 /\
    unfold_packages x == empty #item /\
    merge_invariant (lo - 1) w prev 2 0 x /\
    solution_weight_sum_invariant w prev 2 0 x))

let merge_solution
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w):
  Tot (solution hi (lo - 1) w) =
  let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
  lemma_init_merge_seq prev;
  merge prev 2 0 x

let rec do_package_merge
  #hi (#lo: pos{lo <= hi}) #w (prev: solution hi lo w) (fuel: nat{fuel < lo}):
  Tot (solution hi (lo - fuel) w) (decreases fuel) =
  match fuel with
  | 0 -> prev
  | _ -> do_package_merge (merge_solution prev) (fuel - 1)

let rec log2 (a: pos): Tot (e: nat{
  pow2 e >= a /\ (forall e'. pow2 e' >= a ==> e' >= e)
}) =
  match (a, a % 2) with
  | (1, _) -> 0
  | (_, 0) -> 1 + log2 (a / 2)
  | (_, 1) -> 1 + log2 (a / 2 + 1)

val lemma_do_package_merge_len_lower_bound:
  #hi: pos -> #lo: pos{lo <= hi} -> #w: weight_seq -> prev: solution hi lo w -> Lemma
  (requires (
    let n = length w in
    let e = Math.Lib.max 0 ((log2 n) - (hi - lo)) in
    n <= pow2 hi /\ length prev >= 2 * n - pow2 e))
  (ensures length (do_package_merge prev (lo - 1)) >= 2 * length w - 2)
  (decreases lo)

val lemma_do_package_merge_len_upper_bound:
  #hi: pos -> #lo: pos{lo <= hi} -> #w: weight_seq ->
  x: solution hi lo w -> fuel: nat{fuel < lo} -> Lemma
  (requires length x <= 2 * length w - 1)
  (ensures length (do_package_merge x fuel) <= 2 * length w - 1)
  (decreases fuel)
  [SMTPat (do_package_merge #hi #lo #w x fuel)]

val lemma_base_set_solution: hi: pos -> w: weight_seq -> Lemma
  (ensures (
    let x = make_base_set hi w in
    length (filter_leaves x) == length w /\
    length x < 2 * length w /\
    weight_sorted x /\
    top2_leaf x w /\
    (forall j. package_gt_div2 w x j) /\
    (forall i. solution_wf hi hi w x i)
  )) [SMTPat (make_base_set hi w)]

val lemma_do_package_merge_slice: max_len: pos -> w: weight_seq -> Lemma
  (requires (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) (max_len - 1) in
    length w <= pow2 max_len /\
    length s == 2 * length w - 1))
  (ensures (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) (max_len - 1) in
    let s' = slice s 0 (2 * length w - 2) in
    length (filter_leaves s') == length w /\
    weight_sorted s' /\
    top2_leaf #1 s' w /\
    (forall j. package_gt_div2 w s' j) /\
    (forall i. solution_wf max_len 1 w s' i)
  ))

type valid_weight_seq (max_len: pos) = w: weight_seq{
  length w <= pow2 max_len
}

let package_merge (max_len: pos) (w: valid_weight_seq max_len):
  Tot (s: solution max_len 1 w{
    length s == 2 * length w - 2
  }) =
  let n = length w in
  let x = make_base_set max_len w in
  let s = do_package_merge #max_len #max_len #w x (max_len - 1) in
  lemma_do_package_merge_len_lower_bound #max_len #max_len #w x;
  if length s = 2 * n - 1 then begin
    lemma_do_package_merge_slice max_len w;
    slice s 0 (2 * n - 2)
  end else
    s

val lemma_package_merge: max_len: pos -> w: valid_weight_seq max_len -> Lemma
  (ensures (
    let s = solution_len (package_merge max_len w) in
    kraft_sum s =$ one /\ (forall i. s.[i] <= max_len)))

val lemma_do_package_merge_weight_upper_bound:
    max_len: pos
  -> w: valid_weight_seq max_len
  -> fuel: nat{fuel < max_len}
  -> Lemma
  (ensures (
    let x = make_base_set max_len w in
    let s = do_package_merge #max_len #max_len #w x fuel in
    (forall i. item_weight s.[i] <= weight_sum w * (fuel + 1))
  ))

type item_bit_map (nbits max_len lo: pos) (w: valid_weight_seq max_len) =
  s: seq (UInt.uint_t nbits) {
    let b: solution max_len max_len w = make_base_set max_len w in
    max_len <= nbits /\ lo <= max_len /\
    length s == 2 * length w - 1 /\
    (forall (j: nat{j <= max_len - lo}).
      let x = do_package_merge b j in
      (forall (i: index_t x). (UInt.to_vec s.[i]).[j] == Leaf? x.[i]))
  }

let rec solution_row (s: seq item) (depth: nat): Tot (seq item) (decreases depth) =
  match depth with
  | 0 -> s
  | _ -> solution_row (unfold_packages s) (depth - 1)

let leaf_row (s: seq item) (depth: nat): Tot leaf_seq =
  filter_leaves (solution_row s depth)

type col_index max_len w depth = i: nat{
  i <= length (solution_row (package_merge max_len w) depth) /\
  length (solution_row (package_merge max_len w) depth) <= 2 * length w - 1
}

type col_leaf_count max_len w depth (i: col_index max_len w depth) = j: nat{
  let s = package_merge max_len w in
  j == length (filter_leaves (slice (solution_row s depth) 0 i)) /\
  j <= length w
}

type col_package_count max_len w depth i (j: col_leaf_count max_len w depth i) = k: nat{
  let s = package_merge max_len w in
  k == length (unfold_packages (slice (solution_row s depth) 0 i)) /\
  k < 2 * length w - 1 /\
  k % 2 == 0 /\
  j + k / 2 == i
}

type depth_t (max_len: pos) = d: nat{
  d < max_len
}

type exp_seq' (max_len: pos) w (depth: depth_t max_len) = l: seq nat{
  let s = package_merge max_len w in
  length l == length w /\
  (forall i. l.[i] == max_exp (unfold_solution s depth) i)
}

type intermediate_exp_seq'
  (max_len: pos) (w: valid_weight_seq max_len)
  (depth: nat{depth < max_len}) (j: nat{j <= length w}) =
  l: seq nat {
    let s = package_merge max_len w in
    length l == length w /\
    (depth == 0 ==> (forall i. {:pattern l.[i]}
      (i < j ==> l.[i] == max_exp (unfold_solution s depth) i) /\
      (i >= j ==> l.[i] == 0))) /\
    (depth > 0 ==> (forall i. {:pattern l.[i]}
      (i < j ==> l.[i] == max_exp (unfold_solution s depth) i) /\
      (i >= j ==> l.[i] == max_exp (unfold_solution s (depth - 1)) i)))
  }

val lemma_analyze_row_terminate:
    #nbits: pos
  -> #max_len: pos
  -> #w: valid_weight_seq max_len
  -> bits: item_bit_map nbits max_len 1 w
  -> depth: depth_t max_len
  -> i: col_index max_len w depth
  -> j: col_leaf_count max_len w depth i
  -> k: col_package_count max_len w depth i j
  -> s: intermediate_exp_seq' max_len w depth j
  -> Lemma
  (requires i = length (solution_row (package_merge max_len w) depth))
  (ensures
    (forall l. s.[l] == max_exp (unfold_solution (package_merge max_len w) depth) l) /\
    k == length (solution_row (package_merge max_len w) (depth + 1)))

val lemma_analyze_row_set:
    #nbits: pos
  -> #max_len: pos
  -> #w: valid_weight_seq max_len
  -> bits: item_bit_map nbits max_len 1 w
  -> depth: depth_t max_len
  -> i: col_index max_len w depth
  -> j: col_leaf_count max_len w depth i
  -> k: col_package_count max_len w depth i j
  -> s: intermediate_exp_seq' max_len w depth j
  -> Lemma
  (requires
    i < length (solution_row (package_merge max_len w) depth) /\
    (UInt.to_vec bits.[i]).[max_len - 1 - depth])
  (ensures (
    let sol = package_merge max_len w in
    j < length w /\
    j + 1 == length (filter_leaves (slice (solution_row sol depth) 0 (i + 1))) /\
    i + 1 <= 2 * length w - 1 /\
    k == length (unfold_packages (slice (solution_row sol depth) 0 (i + 1))) /\
    s.[j] + 1 == max_exp (unfold_solution sol depth) j))

val lemma_analyze_row_skip:
    #nbits: pos
  -> #max_len: pos
  -> #w: valid_weight_seq max_len
  -> bits: item_bit_map nbits max_len 1 w
  -> depth: depth_t max_len
  -> i: col_index max_len w depth
  -> j: col_leaf_count max_len w depth i
  -> k: col_package_count max_len w depth i j
  -> s: intermediate_exp_seq' max_len w depth j
  -> Lemma
  (requires
    i < length (solution_row (package_merge max_len w) depth) /\
    (UInt.to_vec bits.[i]).[max_len - 1 - depth] == false)
  (ensures (
    let sol = package_merge max_len w in
    j == length (filter_leaves (slice (solution_row sol depth) 0 (i + 1))) /\
    k + 2 == length (unfold_packages (slice (solution_row sol depth) 0 (i + 1))) /\
    k + 2 < 2 * length w - 1
  ))

type analyze_pair #max_len (w: valid_weight_seq max_len) (depth: depth_t max_len) =
  p: (nat & exp_seq' max_len w depth) {
    fst p == length (solution_row (package_merge max_len w) (depth + 1))
  }

let rec analyze_row
  #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w) (depth: depth_t max_len)
  i j (k: col_package_count max_len w depth i j)
  (s: intermediate_exp_seq' max_len w depth j):
  Tot (analyze_pair w depth)
  (decreases length (solution_row (package_merge max_len w) depth) - i) =
  if i = length (solution_row (package_merge max_len w) depth) then begin
    lemma_analyze_row_terminate bits depth i j k s;
    (k, s)
  end else if (UInt.to_vec bits.[i]).[max_len - 1 - depth] then begin
    lemma_analyze_row_set bits depth i j k s;
    analyze_row bits depth (i + 1) (j + 1) k (s.(j) <- s.[j] + 1)
  end else begin
    lemma_analyze_row_skip bits depth i j k s;
    analyze_row bits depth (i + 1) j (k + 2) s
  end

val lemma_do_analyze:
    #max_len: pos
  -> #w: valid_weight_seq max_len
  -> i: depth_t max_len
  -> p: analyze_pair w (max_len - 1 - i)
  -> Lemma
  (requires i > 0)
  (ensures (let depth' = max_len - i in
    length (solution_row (package_merge max_len w) depth') <= 2 * length w - 1))

let rec do_analyze
  #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w)
  (i: depth_t max_len) (p: analyze_pair w (max_len - 1 - i)):
  Tot (exp_seq' max_len w (max_len - 1))
  (decreases i) =
  match i with
  | 0 -> snd p
  | _ ->
    let depth = max_len - 1 - i in
    let depth' = max_len - i in
    let s = package_merge max_len w in
    lemma_do_analyze i p;
    do_analyze bits (i - 1) (analyze_row bits (max_len - i) 0 0 0 (snd p))

val lemma_analyze_init:
    #max_len: pos
  -> w: valid_weight_seq max_len
  -> Lemma
  (ensures forall (i: index_t w).
    max_exp (unfold_solution (package_merge max_len w) 0) i == 1)

let analyze #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w):
  Tot(exp_seq' max_len w (max_len - 1)) =
  let s = package_merge max_len w in
  let a: seq nat = create (length w) 1 in
  lemma_analyze_init w;
  do_analyze bits (max_len - 1) (length (solution_row s 1) , a)