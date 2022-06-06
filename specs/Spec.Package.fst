module Spec.Package

open FStar.Seq
open FStar.Classical
open FStar.Squash
open Spec.Kraft

let rec lemma_filter_leaves_len_gt s =
  match length s with
  | 0 -> ()
  | _ -> lemma_filter_leaves_len_gt (tail s)

let rec lemma_weight_seq_lt (w: weight_seq) (i j: index_t w): Lemma
  (requires i < j)
  (ensures w.[i] <= w.[j])
  (decreases %[length w; j - i]) =
  match i with
  | 0 -> if j > 1 then lemma_weight_seq_lt (tail w) 0 (j - 1)
  | _ -> lemma_weight_seq_lt (tail w) (i - 1) (j - 1)

#set-options "--fuel 3 --ifuel 3 --z3rlimit 128"
let rec lemma_wseq_snoc (w: weight_seq) (i: pos): Lemma
  (requires last w <= i)
  (ensures wseq_sorted (snoc w i))
  (decreases length w) =
  match length w with
  | 2 -> ()
  | _ ->
    calc (==) {
      wseq_sorted (snoc w i);
      =={}
      wseq_sorted (tail (snoc w i));
      =={assert(tail (snoc w i) `equal` (snoc (tail w) i))}
      wseq_sorted (snoc (tail w) i);
      =={lemma_wseq_snoc (tail w) i}
      true;
    }

let rec lemma_weight_seq_slice w i j =
  match (i, j - i) with
  | (0, 0) | (0, 1) | (0, 2) -> ()
  | (0, _) ->
    lemma_weight_seq_slice w i (j - 1);
    lemma_weight_seq_lt w (j - 2) (j - 1);
    lemma_wseq_snoc (slice w i (j - 1)) w.[j - 1]
  | _ -> if length w > 2 then lemma_weight_seq_slice (tail w) (i - 1) (j - 1)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let rec lemma_filter_leaves_snoc_leaf (s: seq item) (i: item): Lemma
  (requires Leaf? i)
  (ensures filter_leaves (snoc s i) == snoc (filter_leaves s) i)
  (decreases length s) =
  match length s with
  | 0 -> lemma_empty s
  | _ ->
    match Leaf? s.[0] with
    | true ->
      calc (==) {
        filter_leaves (snoc s i);
        =={}
        cons s.[0] (filter_leaves (tail (snoc s i)));
        =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
        cons s.[0] (filter_leaves (snoc (tail s) i));
        =={lemma_filter_leaves_snoc_leaf (tail s) i}
        cons s.[0] (snoc (filter_leaves (tail s)) i);
        =={}
        create 1 s.[0] @| ((filter_leaves (tail s)) @| create 1 i);
        =={append_assoc (create 1 s.[0]) (filter_leaves (tail s)) (create 1 i)}
        (create 1 s.[0] @| (filter_leaves (tail s))) @| create 1 i;
        =={}
        (filter_leaves s) @| create 1 i;
      }
    | false ->
      calc (==) {
        filter_leaves (snoc s i);
        =={}
        filter_leaves (tail (snoc s i));
        =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
        filter_leaves (snoc (tail s) i);
        =={lemma_filter_leaves_snoc_leaf (tail s) i}
        snoc (filter_leaves (tail s)) i;
        =={}
        snoc (filter_leaves s) i;
      }

let rec lemma_filter_leaves_snoc_package (s: seq item) (i: item): Lemma
  (requires Package? i)
  (ensures filter_leaves (snoc s i) == filter_leaves s)
  (decreases length s) =
  match length s with
  | 0 -> lemma_empty s
  | _ ->
    calc (==) {
      filter_leaves (tail (snoc s i));
      =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
      filter_leaves (snoc (tail s) i);
      =={lemma_filter_leaves_snoc_package (tail s) i}
      filter_leaves (tail s);
    }

let rec lemma_unfold_packages_snoc_leaf (s: seq item) (i: item): Lemma
  (requires Leaf? i)
  (ensures unfold_packages (snoc s i) == unfold_packages s)
  (decreases length s) =
  match length s with
  | 0 -> lemma_empty s
  | _ ->
    match s.[0] with
    | Package i1 i2 ->
      calc (==) {
        unfold_packages (snoc s i);
        =={}
        cons i1 (cons i2 (unfold_packages (tail (snoc s i))));
        =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
        cons i1 (cons i2 (unfold_packages (snoc (tail s) i)));
        =={lemma_unfold_packages_snoc_leaf (tail s) i}
        cons i1 (cons i2 (unfold_packages (tail s)));
        =={}
        unfold_packages s;
      }
    | _ ->
      calc (==) {
        unfold_packages (snoc s i);
        =={}
        unfold_packages (tail (snoc s i));
        =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
        unfold_packages (snoc (tail s) i);
        =={lemma_unfold_packages_snoc_leaf (tail s) i}
        unfold_packages (tail s);
      }

#push-options "--fuel 2 --ifuel 2"
let rec lemma_unfold_packages_snoc_package (s: seq item) (i1 i2: item): Lemma
  (requires exp i1 == exp i2)
  (ensures
    unfold_packages (snoc s (Package i1 i2)) ==
    snoc (snoc (unfold_packages s) i1) i2)
  (decreases length s) =
  let p = Package i1 i2 in
  match length s with
  | 0 ->
    assert(
      unfold_packages (snoc s p) `equal`
      snoc (snoc (unfold_packages s) i1) i2)
  | _ ->
    match s.[0] with
    | Package j1 j2 ->
      calc (==) {
        unfold_packages (snoc s p);
        =={}
        cons j1 (cons j2 (unfold_packages (tail (snoc s p))));
        =={assert(tail (snoc s p) `equal` snoc (tail s) p)}
        cons j1 (cons j2 (unfold_packages (snoc (tail s) p)));
        =={lemma_unfold_packages_snoc_package (tail s) i1 i2}
        cons j1 (cons j2 (snoc (snoc (unfold_packages (tail s)) i1) i2));
        =={
          assert(
            cons j1 (cons j2 (snoc (snoc (unfold_packages (tail s)) i1) i2)) `equal`
            snoc (snoc (unfold_packages s) i1) i2)
        }
        snoc (snoc (unfold_packages s) i1) i2;
      }
    | _ ->
      calc (==) {
        unfold_packages (snoc s p);
        =={}
        unfold_packages (tail (snoc s p));
        =={assert(tail (snoc s p) `equal` snoc (tail s) p)}
        unfold_packages (snoc (tail s) p);
        =={lemma_unfold_packages_snoc_package (tail s) i1 i2}
        snoc (snoc (unfold_packages (tail s)) i1) i2;
        =={}
        snoc (snoc (unfold_packages s) i1) i2;
      }
#pop-options

let lemma_unfold_solution_snoc_leaf (s: seq item) (i: item) (j: nat): Lemma
  (requires Leaf? i)
  (ensures unfold_solution (snoc s i) j == snoc (unfold_solution s j) i)
  (decreases j) =
  match j with
  | 0 ->
    calc (==) {
      unfold_solution (snoc s i) j;
      =={}
      filter_leaves (snoc s i);
      =={lemma_filter_leaves_snoc_leaf s i}
      snoc (filter_leaves s) i;
      =={}
      snoc (unfold_solution s j) i;
    }
  | _ ->
    calc (==) {
      unfold_solution (snoc s i) j;
      =={}
      (unfold_solution (unfold_packages (snoc s i)) (j - 1)) @| filter_leaves (snoc s i);
      =={
        lemma_filter_leaves_snoc_leaf s i;
        lemma_unfold_packages_snoc_leaf s i
      }
      (unfold_solution (unfold_packages s) (j - 1)) @| snoc (filter_leaves s) i;
      =={
        append_assoc
          (unfold_solution (unfold_packages s) (j - 1))
          (filter_leaves s)
          (create 1 i)
      }
      ((unfold_solution (unfold_packages s) (j - 1)) @| (filter_leaves s)) @| (create 1 i);
      =={}
      snoc (unfold_solution s j) i;
    }

let rec lemma_unfold_packages_all_leaves (s: seq item): Lemma
  (requires forall i. Leaf? s.[i])
  (ensures unfold_packages s == empty #item)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> lemma_unfold_packages_all_leaves (tail s)

let rec lemma_unfold_solution_empty (i: nat): Lemma
  (ensures unfold_solution (empty #item) i == empty #item) =
  match i with
  | 0 -> ()
  | _ -> lemma_unfold_solution_empty (i - 1)

let rec lemma_filter_leaves_equal (s: seq item): Lemma
  (requires forall i. Leaf? s.[i])
  (ensures filter_leaves s == s)
  (decreases length s) =
  match length s with
  | 0 -> lemma_empty s
  | _ -> lemma_filter_leaves_equal (tail s)

let lemma_unfold_solution_leaf (s: seq item) (i: nat): Lemma
  (requires forall j. Leaf? s.[j])
  (ensures unfold_solution s i == s) = 
  match i with
  | 0 -> lemma_filter_leaves_equal s
  | _ ->
    calc (==) {
      unfold_solution s i;
      =={}
      (unfold_solution (unfold_packages s) (i - 1)) @| filter_leaves s;
      =={
        lemma_unfold_packages_all_leaves s;
        lemma_unfold_solution_empty (i - 1)
      }
      empty #item @| filter_leaves s;
      =={append_empty_l (filter_leaves s)}
      filter_leaves s;
      =={lemma_filter_leaves_equal s}
      s;
    }

#push-options "--fuel 1 --ifuel 0 --query_stats --z3refresh --z3rlimit 1024 --z3seed 7"
let lemma_snoc_leaf_monotone_elem
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: solution hi (lo - 1) (slice w 0 i){length x >= 2})
  (k: index_t (unfold_solution (snoc x (Leaf i (lo - 1) w.[i])) (hi - lo + 1))): Lemma
  (ensures (
    let l = Leaf i (lo - 1) w.[i] in
    let sol' = unfold_solution (snoc x l) (hi - lo + 1) in
    monotone_elem sol' (slice w 0 (i + 1)) hi (lo - 1) k /\
    count sol'.[k] sol' == 1)) =
  let l = Leaf i (lo - 1) w.[i] in
  let x' = snoc x (Leaf i (lo - 1) w.[i]) in
  let sol = unfold_solution x (hi - lo + 1) in
  let sol' = unfold_solution x' (hi - lo + 1) in
  lemma_unfold_solution_snoc_leaf x l (hi - lo + 1);
  lemma_mem_append (unfold_solution x (hi - lo + 1)) (create 1 l);
  assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x));
  if k = length sol' - 1 && length sol > 0 then
    assert(last sol == (make_base_set (lo - 1) (slice w 0 i)).[i - 1]);

  assert(forall t. t < length sol ==> sol'.[t] <> l);
  if k < length sol then begin
    lemma_append_count_aux #item sol'.[k] sol (create 1 l);
    count_create #item 1 l sol'.[k]
  end else begin
    lemma_append_count_aux #item sol'.[k] sol (create 1 l);
    count_neq #item sol l;
    count_create #item 1 l l
  end

let lemma_snoc_leaf_filter
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j): Lemma
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    filter_leaves x' == make_base_set (lo - 1) (slice w 0 (i + 1)))) =
  let l = Leaf i (lo - 1) w.[i] in
  let x' = snoc x l in
  let base = make_base_set (lo - 1) (slice w 0 i) in
  let base' = make_base_set (lo - 1) (slice w 0 (i + 1)) in
  calc (==) {
    filter_leaves x';
    =={lemma_filter_leaves_snoc_leaf x l}
    snoc (filter_leaves x) l;
    =={assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x))}
    base @| (create 1 l);
    =={assert(snoc base l `equal` base')}
    base';
  }

#push-options "--fuel 1 --ifuel 1"
let rec lemma_solution_sum'_append (s1 s2: seq item): Lemma
  (ensures solution_sum' s1 +$ solution_sum' s2 =$ solution_sum' (s1 @| s2))
  (decreases length s1) =
  match length s1 with
  | 0 -> lemma_empty s1; append_empty_l s2
  | _ ->
    calc (=$) {
      solution_sum' s1 +$ solution_sum' s2;
      =${}
      (qpow2 (-exp s1.[0]) +$ (solution_sum' (tail s1)) +$ solution_sum' s2);
      =${plus_assoc (qpow2 (-exp s1.[0])) (solution_sum' (tail s1)) (solution_sum' s2)}
      qpow2 (-exp s1.[0]) +$ (solution_sum' (tail s1) +$ solution_sum' s2);
      =${lemma_solution_sum'_append (tail s1) s2}
      qpow2 (-exp s1.[0]) +$ (solution_sum' ((tail s1) @| s2));
      =${assert(((tail s1) @| s2) `equal` (tail (s1 @| s2)))}
      qpow2 (-exp s1.[0]) +$ (solution_sum' (tail (s1 @| s2)));
      =${}
      solution_sum' (s1 @| s2);
    }
#pop-options

#push-options "--fuel 2 --ifuel 2"
let lemma_solution_sum'_single (i: item): Lemma
  (ensures solution_sum' (create 1 i) =$ qpow2 (-exp i)) = ()
#pop-options

let rec lemma_solution_sum'_perm (s1 s2: seq item): Lemma
  (requires permutation item s1 s2)
  (ensures solution_sum' s1 =$ solution_sum' s2)
  (decreases length s1) =
  match length s1 with
  | 0 -> ()
  | _ ->
    let i = index_of s2 s1.[0] in
    calc (=$) {
      solution_sum' s1;
      =${}
      qpow2 (-exp s1.[0]) +$ solution_sum' (tail s1);
      =${
        permutation_middle s1 s2;
        lemma_solution_sum'_perm
          (tail s1)
          (slice s2 0 i @| slice s2 (i + 1) (length s2))
      }
      qpow2 (-exp s1.[0]) +$ solution_sum' (slice s2 0 i @| slice s2 (i + 1) (length s2));
      =${lemma_solution_sum'_single s2.[i]}
      solution_sum' (create 1 s2.[i]) +$
      solution_sum' (slice s2 0 i @| slice s2 (i + 1) (length s2));
      =${lemma_solution_sum'_append (slice s2 0 i) (slice s2 (i + 1) (length s2))}
      solution_sum' (create 1 s2.[i]) +$
      (solution_sum' (slice s2 0 i) +$
      solution_sum' (slice s2 (i + 1) (length s2)));
      =${
        plus_assoc
          (solution_sum' (create 1 s2.[i]))
          (solution_sum' (slice s2 0 i))
          (solution_sum' (slice s2 (i + 1) (length s2)))
      }
      solution_sum' (slice s2 0 i) +$
      solution_sum' (create 1 s2.[i]) +$
      solution_sum' (slice s2 (i + 1) (length s2));
      =${
        lemma_solution_sum'_append (slice s2 0 i) (create 1 s2.[i]);
        assert(snoc (slice s2 0 i) s2.[i] `equal` slice s2 0 (i + 1))
      }
      solution_sum' (slice s2 0 (i + 1)) +$
      solution_sum' (slice s2 (i + 1) (length s2));
      =${
        lemma_solution_sum'_append
          (slice s2 0 (i + 1))
          (slice s2 (i + 1) (length s2));
        assert((slice s2 0 (i + 1) @| slice s2 (i + 1) (length s2)) `equal` s2)
      }
      solution_sum' s2;
    }

let lemma_solution_sum_snoc_leaf
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j): Lemma
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    solution_sum hi (lo - 1) x' =$ qpow2 (-(lo - 1)) *$ (of_int (length x')))) =
  let l = Leaf i (lo - 1) w.[i] in
  let x' = snoc x l in
  let sol = unfold_solution x (hi - (lo - 1)) in
  let sol' = unfold_solution x' (hi - (lo - 1)) in
  lemma_filter_leaves_snoc_leaf x l;
  calc (=$) {
    solution_sum hi (lo - 1) x' ;
    =${}
    solution_sum' sol';
    =${lemma_unfold_solution_snoc_leaf x l (hi - (lo - 1))}
    solution_sum' (sol @| (create 1 l));
    =${lemma_solution_sum'_append sol (create 1 l)}
    solution_sum' sol +$ solution_sum' (create 1 l);
    =${lemma_solution_sum'_single l}
    (qpow2 (-(lo - 1)) *$ (of_int (length x))) +$ qpow2 (-(lo - 1));
    =${}
    (qpow2 (-(lo - 1)) *$ (of_int (length x))) +$ (qpow2 (-(lo - 1)) *$ one);
    =${distributivity_add_left (qpow2 (-(lo - 1))) (of_int (length x)) one}
    qpow2 (-(lo - 1)) *$ (of_int (length x) +$ one);
    =${mul_eq_r (qpow2 (-(lo - 1))) (of_int (length x) +$ one) (of_int (length x + 1))}
    qpow2 (-(lo - 1)) *$ (of_int (length x + 1));
    =${}
    qpow2 (-(lo - 1)) *$ (of_int (length x'));
  }

let lemma_snoc_leaf_solution_wf
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j)
  (k: nat{2 <= k /\ k <= length x + 1}) : Lemma
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    solution_wf hi (lo - 1) (slice w 0 (i + 1)) x' k)) =
  let x' = snoc x (Leaf i (lo - 1) w.[i]) in
  let sol' = unfold_solution x' (hi - lo + 1) in
  if k = length x' then begin
    forall_intro (move_requires (lemma_snoc_leaf_monotone_elem prev i j x));
    no_dup_count_one sol';
    lemma_snoc_leaf_filter prev i j x;
    lemma_solution_sum_snoc_leaf prev i j x
  end else
    assert(slice x' 0 k `equal` slice x 0 k)

let lemma_snoc_leaf_package_gt_div2
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j)
  (k: index_t (snoc x (Leaf i (lo - 1) w.[i]))): Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    package_gt_div2 w x' k)) =
  let x' = snoc x (Leaf i (lo - 1) w.[i]) in
  if k % 2 = 0 && k + 1 < length x' then
    if k = length x' - 2 then
      if k / 2 + 1 < i then
        lemma_weight_seq_lt w (k / 2 + 1) i
      else
        assert(k == 2 * (i - 1))
    else 
      assert(package_gt_div2 (slice w 0 i) x k)

let rec lemma_weight_sorted_snoc (s: seq item) (i: item): Lemma
  (requires weight_sorted s /\ (length s > 0 ==> item_weight (last s) <= item_weight i))
  (ensures weight_sorted (snoc s i))
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ ->
    calc (==) {
      weight_sorted (snoc s i);
      =={}
      weight_sorted (tail (snoc s i));
      =={assert(tail (snoc s i) `equal` snoc (tail s) i)}
      weight_sorted (snoc (tail s) i);
      =={lemma_weight_sorted_snoc (tail s) i}
      true;
    }

#push-options "--ifuel 1"
let lemma_snoc_leaf_merge_invariant
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j): Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    merge_invariant (lo - 1) w prev (i + 1) j x')) =
  if i < length w - 1 then lemma_weight_seq_lt w i (i + 1)

#push-options "--fuel 2 --ifuel 2"
let rec lemma_solution_weight_sum_snoc_item (x: seq item) (l: item): Lemma
  (requires length x >= 1)
  (ensures solution_weight_sum (snoc x l) == solution_weight_sum x + item_weight l)
  (decreases length x) =
  match length x with
  | 1 -> ()
  | _ ->
    calc (==) {
      solution_weight_sum (snoc x l);
      =={}
      item_weight x.[0] + solution_weight_sum (tail (snoc x l));
      =={assert(tail (snoc x l) `equal` snoc (tail x) l)}
      item_weight x.[0] + solution_weight_sum (snoc (tail x) l);
      =={lemma_solution_weight_sum_snoc_item (tail x) l}
      item_weight x.[0] + solution_weight_sum (tail x) + item_weight l;
      =={}
      solution_weight_sum x + item_weight l;
    }

let rec lemma_weight_sum_snoc (w: seq pos) (i: pos): Lemma
  (requires length w >= 1)
  (ensures weight_sum w + i == weight_sum (snoc w i))
  (decreases length w) =
  match length w with
  | 1 -> ()
  | _ ->
    calc (==) {
      weight_sum (snoc w i);
      =={}
      w.[0] + weight_sum (tail (snoc w i));
      =={assert(tail (snoc w i) `equal` snoc (tail w) i)}
      w.[0] + weight_sum (snoc (tail w) i);
      =={lemma_weight_sum_snoc (tail w) i}
      w.[0] + weight_sum (tail w) + i;
      =={}
       weight_sum w + i;
    }
#pop-options

let lemma_snoc_leaf_solution_weight_sum_inv
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermediate_solution prev i j): Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    solution_weight_sum_invariant w prev (i + 1) j x')) =
  lemma_solution_weight_sum_snoc_item x (Leaf i (lo - 1) w.[i]);
  lemma_weight_sum_snoc (slice w 0 i) w.[i]

let lemma_snoc_leaf #hi #lo #w prev i j x =
  let l = Leaf i (lo - 1) w.[i] in
  lemma_mem_append x (create 1 l);
  lemma_snoc_leaf_filter prev i j x;
  forall_intro (move_requires (lemma_snoc_leaf_package_gt_div2 prev i j x));
  forall_intro (move_requires (lemma_snoc_leaf_solution_wf prev i j x));
  lemma_unfold_packages_snoc_leaf x l;
  lemma_weight_sorted_snoc x l;
  lemma_snoc_leaf_merge_invariant prev i j x;
  lemma_snoc_leaf_solution_weight_sum_inv prev i j x

let last_leaf_id (s: seq item{length (filter_leaves s) > 0}): Tot (id: nat{
   item_id (last (filter_leaves s)) == id
}) = item_id (last (filter_leaves s))

let rec lemma_filter_leaves_map (s: seq item) (i: index_t (filter_leaves s)): Lemma
  (ensures exists j. s.[j] == (filter_leaves s).[i])
  (decreases %[length s; i]) =
  match length s with
  | 0 -> ()
  | _ -> match (i, Leaf? s.[0]) with
    | (0, true) -> ()
    | (_, true) -> lemma_filter_leaves_map (tail s) (i - 1)
    | _ -> lemma_filter_leaves_map (tail s) i

let lemma_last_leaf_index
  #hi (#lo: intermediate_exp hi) #w
  (prev: solution hi lo w) (j: package_index_t prev true): Lemma
  (ensures (
    let k = last_leaf_id (slice prev 0 (j + 2)) in
    exists i. i <= j + 1 /\ prev.[i] == Leaf k lo w.[k])) =
  let prev' = slice prev 0 (j + 2) in
  let k = last_leaf_id prev' in
  lemma_filter_leaves_map prev' k

let rec lemma_weight_sorted_lt (w: seq item) (i j: index_t w): Lemma
  (requires i < j /\ weight_sorted w)
  (ensures item_weight w.[i] <= item_weight w.[j])
  (decreases %[length w; j - i]) =
  match i with
  | 0 -> if j > 1 then lemma_weight_sorted_lt (tail w) 0 (j - 1)
  | _ -> lemma_weight_sorted_lt (tail w) (i - 1) (j - 1)

let lemma_package_lt_leaf
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures length (filter_leaves (slice prev 0 (j + 2))) <= length (filter_leaves x)) =
  let prev' = slice prev 0 (j + 2) in
  let lp = last_leaf_id prev' in
  let lx = last_leaf_id x in
  assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x));
  if lp > lx && i < length w then
    let base = make_base_set (lo - 1) w in
    let last_leaf = Leaf lp lo w.[lp] in 
    lemma_last_leaf_index prev j;
    exists_elim
      (item_weight prev.[j] + item_weight prev.[j + 1] > item_weight base.[i])
      (get_proof (exists k. k <= j + 1 /\ prev.[k] == last_leaf))
      (fun k->
        if j <= k then
          lemma_weight_seq_lt w i lp
        else begin
          lemma_weight_sorted_lt prev k j;
          lemma_weight_seq_lt w i lp
        end)

#set-options "--z3seed 212"
let lemma_snoc_package_monotone_elem
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j)
  (k: index_t (unfold_solution (snoc x (Package prev.[j] prev.[j + 1])) (hi - lo + 1))):
  Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let p = Package prev.[j] prev.[j + 1] in
    let sol' = unfold_solution (snoc x p) (hi - lo + 1) in
    monotone_elem sol' (slice w 0 i) hi (lo - 1) k)) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  let sol' = unfold_solution x' (hi - lo + 1) in
  let prev' = slice prev 0 (j + 2) in
  calc (==) {
    unfold_packages x';
    =={lemma_unfold_packages_snoc_package x prev.[j] prev.[j + 1]}
    snoc (snoc (unfold_packages x) prev.[j]) prev.[j + 1];
    =={}
    snoc (snoc (slice prev 0 j) prev.[j]) prev.[j + 1];
    =={assert(snoc (snoc (slice prev 0 j) prev.[j]) prev.[j + 1] `equal` prev')}
    prev';
  };
  assert(solution_wf hi lo w prev (j + 2));
  assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x));
  lemma_filter_leaves_snoc_package x p;

  let sol = unfold_solution prev' (hi - lo) in
  lemma_mem_append sol (filter_leaves x');
  lemma_package_lt_leaf prev i j x

let lemma_snoc_package_count_one
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j)
  (k: index_t (unfold_solution (snoc x (Package prev.[j] prev.[j + 1])) (hi - lo + 1))):
  Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let p = Package prev.[j] prev.[j + 1] in
    let sol' = unfold_solution (snoc x p) (hi - lo + 1) in
    count sol'.[k] sol' == 1
  )) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  let prev' = slice prev 0 (j + 2) in
  let sol = unfold_solution prev' (hi - lo) in
  let sol' = unfold_solution x' (hi - lo + 1) in
  let base' = filter_leaves x' in
  lemma_unfold_packages_snoc_package x prev.[j] prev.[j + 1];
  lemma_append_count_aux sol'.[k] sol (filter_leaves x');
  assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x));
  lemma_filter_leaves_snoc_package x p;
  if k < length sol then
    count_neq base' sol'.[k]
  else
    count_neq sol sol'.[k]

#push-options "--fuel 1 --ifuel 0"
let rec lemma_solution_sum'_base_set #e #w (b: base_set e w): Lemma
  (ensures solution_sum' b =$ qpow2 (-e) *$ of_int (length w))
  (decreases length b) =
  match length b with
  | 0 | 1 -> ()
  | 2 ->
    calc (=$) {
      solution_sum' b;
      =={}
      qpow2 (-e) +$ solution_sum' (tail b);
      =={}
      qpow2 (-e) +$ qpow2 (-e) +$ solution_sum' (tail (tail b));
      =={lemma_empty (tail (tail b))}
      qpow2 (-e) +$ qpow2 (-e);
      =${}
      qpow2 (-e) *$ of_int 2;
    }
  | _ ->
    let b' = slice b 0 (length b - 1) in
    calc (=$) {
      solution_sum' b;
      =={assert(b `equal` (b' @| create 1 (last b)))}
      solution_sum' (b' @| create 1 (last b));
      =${lemma_solution_sum'_append b' (create 1 (last b))}
      solution_sum' b' +$ solution_sum' (create 1 (last b));
      =${lemma_solution_sum'_single (last b)}
      solution_sum' b' +$ qpow2 (-e);
      =${lemma_solution_sum'_base_set #e #(slice w 0 (length b - 1)) b'}
      (qpow2 (-e) *$ of_int (length b - 1)) +$ (qpow2 (-e) *$ one);
      =${distributivity_add_left (qpow2 (-e)) (of_int (length b - 1)) one}
      qpow2 (-e) *$ of_int (length b);
    }

let lemma_solution_sum_snoc_package
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j): Lemma
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    solution_sum hi (lo - 1) x' =$ qpow2 (-(lo - 1)) *$ (of_int (length x')))) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  let prev' = slice prev 0 (j + 2) in
  calc (=$) {
    solution_sum hi (lo - 1) x';
    =={}
    solution_sum' (unfold_solution x' (hi - (lo - 1)));
    =={lemma_unfold_packages_snoc_package x prev.[j] prev.[j + 1]}
    solution_sum' ((unfold_solution prev' (hi - lo)) @| filter_leaves x');
    =${lemma_solution_sum'_append (unfold_solution prev' (hi - lo)) (filter_leaves x')}
    solution_sum' (unfold_solution prev' (hi - lo)) +$
    solution_sum' (filter_leaves x');
    =${}
    (qpow2 (-lo) *$ of_int (j + 2)) +$ solution_sum' (filter_leaves x');
    =={lemma_filter_leaves_snoc_package x p}
    (qpow2 (-lo) *$ of_int (j + 2)) +$ solution_sum' (filter_leaves x);
    =={assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x))}
    (qpow2 (-lo) *$ of_int (j + 2)) +$
    solution_sum' (make_base_set (lo - 1) (slice w 0 i));
    =${lemma_solution_sum'_base_set (make_base_set (lo - 1) (slice w 0 i))}
    (qpow2 (-lo) *$ of_int (j + 2)) +$ (qpow2 (-(lo - 1)) *$ of_int i);
    =${qpow2_mult_even (-lo) (j + 2)}
    (qpow2 (-(lo - 1)) *$ of_int ((j + 2) / 2)) +$ (qpow2 (-(lo - 1)) *$ of_int i);
    =${distributivity_add_left (qpow2 (-(lo - 1))) (of_int ((j + 2) / 2)) (of_int i)}
    (qpow2 (-(lo - 1)) *$ of_int (i + (j + 2) / 2));
    =={}
    (qpow2 (-(lo - 1)) *$ of_int (i + (j + 1 * 2) / 2));
    =={Math.Lemmas.lemma_div_plus j 1 2}
    (qpow2 (-(lo - 1)) *$ of_int (length x'));
  }
#pop-options

let lemma_snoc_package_solution_wf
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j)
  (k: nat{2 <= k /\ k <= length x + 1}): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    assert(package_gt_div2 w prev j);
    solution_wf hi (lo - 1) (slice w 0 i) x' k)) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  let sol' = unfold_solution x' (hi - lo + 1) in
  assert(package_gt_div2 w prev j);
  if k = length x' then begin
    forall_intro (move_requires (lemma_snoc_package_monotone_elem prev i j x));
    forall_intro (move_requires (lemma_snoc_package_count_one prev i j x));
    no_dup_count_one #item sol';
    assert(solution_wf hi (lo - 1) (slice w 0 i) x (length x));
    lemma_filter_leaves_snoc_package x p;
    lemma_solution_sum_snoc_package prev i j x
  end else
    assert (slice x' 0 k `equal` slice x 0 k)

let lemma_snoc_package_merge_invariant
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    merge_invariant (lo - 1) w prev i (j + 2) x')) =
  let x' = snoc x (Package prev.[j] prev.[j + 1]) in
  if j + 2 < length prev - 1 then begin
    lemma_weight_sorted_lt prev j (j + 2);
    lemma_weight_sorted_lt prev (j + 1) (j + 3)
  end

let lemma_snoc_package_gt_div2
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j)
  (k: index_t (snoc x (Package prev.[j] prev.[j + 1]))): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    assert(package_gt_div2 w prev j);
    package_gt_div2 (slice w 0 i) x' k)) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  if k % 2 = 0 && k + 1 < length x' then
    if k = length x' - 2 then begin
      assert(k / 2 + 1 == (i + j / 2 + 1) / 2);
      if k / 2 + 1 = i then begin
        assert(j / 2 + 1 == i /\ length x' == 2 * i);
        assert(package_gt_div2 w prev j);
        assert(item_weight p > w.[i])
      end else if k / 2 + 1 < i - 1 then
        lemma_weight_seq_lt w (k / 2 + 1) (i - 1)
    end else 
      assert(package_gt_div2 (slice w 0 i) x k)

let lemma_snoc_package_solution_weight_sum_inv
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermediate_solution prev i j): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    solution_weight_sum_invariant w prev i (j + 2) x')) =
  let prev' = slice prev 0 j in
  let prev'' = slice prev 0 (j + 1) in
  lemma_solution_weight_sum_snoc_item x (Package prev.[j] prev.[j + 1]);
  if length prev' > 0 then lemma_solution_weight_sum_snoc_item prev' prev.[j];
  lemma_solution_weight_sum_snoc_item prev'' prev.[j + 1]

let lemma_snoc_package #hi #lo #w prev i j x =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  assert(package_gt_div2 w prev j);
  lemma_mem_append x (create 1 p);
  forall_intro (move_requires (lemma_snoc_package_gt_div2 prev i j x));
  forall_intro (move_requires (lemma_snoc_package_solution_wf prev i j x));
  lemma_snoc_package_merge_invariant prev i j x;
  lemma_filter_leaves_snoc_package x p;
  lemma_weight_sorted_snoc x p;
  lemma_unfold_packages_snoc_package x prev.[j] prev.[j + 1];
  lemma_snoc_package_solution_weight_sum_inv prev i j x

let rec make_leaf_col
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j: pos{lo <= j /\ j <= hi}):
  Tot (s': seq item{
    length s' == j - lo + 1 /\
    (forall k.
      Leaf? s'.[k] /\
      item_id s'.[k] == i /\
      exp s'.[k] == j - k /\
      item_weight s'.[k] == w.[i])
  }) (decreases j) =
  let l = Leaf i j w.[i] in
  let x = create 1 l in
  if j = lo then
    x
  else begin
    let xs = make_leaf_col s i (j - 1) in
    lemma_mem_append x xs;
    cons l xs
  end

let rec lemma_make_leaf_col_count_one
  #hi (#lo: pos{hi >= lo}) #w (prev: solution hi lo w)
  (i: index_t w) (j: pos{lo <= j /\ j <= hi})
  (k: index_t (make_leaf_col prev i j)): Lemma
  (ensures count (make_leaf_col prev i j).[k] (make_leaf_col prev i j) == 1)
  (decreases j) =
  if j > lo then 
    let col = make_leaf_col prev i j in
    let col' = make_leaf_col prev i (j - 1) in
    if k = 0 then begin
      assert(forall l. l <> k ==> col.[l] <> col.[k]);
      count_neq col' col.[k];
      lemma_append_count (create 1 col.[0]) col'
    end else begin
      lemma_tl col.[0] col';
      lemma_make_leaf_col_count_one prev i (j - 1) (k - 1)
    end

let lemma_make_leaf_col_no_dup
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j: pos{lo <= j /\ j <= hi}): Lemma
  (ensures no_dup (make_leaf_col s i j)) =
  forall_intro (lemma_make_leaf_col_count_one s i j);
  no_dup_count_one (make_leaf_col s i j)

let rec lemma_max_exp_gt_zero_aux
  (s: seq item) (i: index_t s) (id: nat) (e: pos): Lemma
  (requires (forall j. Leaf? s.[j]) /\ item_id s.[i] == id /\ exp s.[i] == e)
  (ensures max_exp s id > 0)
  (decreases i) =
  match i with
  | 0 -> ()
  | _ -> lemma_max_exp_gt_zero_aux (tail s) (i - 1) id e

let lemma_solution_len_gt_two
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w): Lemma
  (ensures length s >= 2) =
  lemma_filter_leaves_len_gt s

let lemma_max_exp_gt_zero #hi #lo #w (s: solution hi lo w) (id: index_t w): Lemma
  (ensures max_exp (unfold_solution s (hi - lo)) id > 0) =
  let sol = unfold_solution s (hi - lo) in
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));
  if hi = lo then
    lemma_max_exp_gt_zero_aux sol id id hi
  else
    let offset = length (unfold_solution (unfold_packages s) (hi - lo - 1)) in
    lemma_max_exp_gt_zero_aux sol (id + offset) id lo

let lemma_max_exp_range #hi #lo #w s id =
  let e = max_exp (unfold_solution s (hi - lo)) id in
  lemma_max_exp_gt_zero s id;
  assert(solution_wf hi lo w s (length s))

let rec make_monotone_array
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w) (i: index_t w):
  Tot (seq item) (decreases length w - i) =
  let sol = unfold_solution s (hi - lo) in

  lemma_max_exp_gt_zero s i;
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));

  if i = length w - 1 then
    make_leaf_col s i (max_exp sol i)
  else
    make_leaf_col s i (max_exp sol i) @| make_monotone_array s (i + 1)

let rec lemma_monotone_array
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j: index_t (make_monotone_array s i)): Lemma
  (ensures (
    let s' = make_monotone_array s i in
    Leaf? s'.[j] /\
    i <= item_id s'.[j] /\ item_id s'.[j] < length w /\
    item_weight s'.[j] == w.[item_id s'.[j]]))
  (decreases length w - i) =
  let s' = make_monotone_array s i in
  let sol = unfold_solution s (hi - lo) in
  lemma_max_exp_gt_zero s i;
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));
  let maxe = max_exp sol i in

  if i < length w - 1 then
    let col = make_leaf_col s i maxe in
    if j >= length col then lemma_monotone_array s (i + 1) (j - length col)

let rec lemma_monotone_col_mem
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j k: pos): Lemma
  (requires
    hi >= j /\ j >= k /\ k >= lo /\
    mem (Leaf i j w.[i]) (unfold_solution s (hi - lo)))
  (ensures mem (Leaf i k w.[i]) (unfold_solution s (hi - lo)))
  (decreases j - k) =
  let sol = unfold_solution s (hi - lo) in
  lemma_max_exp_gt_zero s i;
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));
  if j > k then begin
    mem_index (Leaf i j w.[i]) sol;
    lemma_monotone_col_mem s i (j - 1) k
  end

let rec lemma_make_leaf_col_not_mem
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j: pos{lo <= j /\ j <= hi}) (l: item): Lemma
  (requires mem l (make_leaf_col s i j) == false)
  (ensures
    Leaf? l == false \/
    item_id l <> i \/
    exp l < lo \/ exp l > j \/
    item_weight l <> w.[i])
  (decreases j) =
  let col = make_leaf_col s i j in
  if lo < j then begin
    lemma_mem_append (create 1 (Leaf i j w.[i])) (make_leaf_col s i (j - 1));
    lemma_make_leaf_col_not_mem s i (j - 1) l
  end

let rec lemma_make_monotone_array_count
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (l: item): Lemma
  (requires Leaf? l ==> item_id l >= i)
  (ensures count l (make_monotone_array s i) == count l (unfold_solution s (hi - lo)))
  (decreases length w - i) =
  let sol = unfold_solution s (hi - lo) in
  let sol' = make_monotone_array s i in
  lemma_max_exp_gt_zero s i;
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));
  let maxe = max_exp sol i in

  lemma_make_leaf_col_no_dup s i maxe;
  let col = make_leaf_col s i maxe in
  if Leaf? l = false then begin
    forall_intro (move_requires (lemma_monotone_array s i));
    count_neq sol' l;
    count_neq sol l
  end else if item_id l = i then  begin
    if i < length w - 1 then begin
      forall_intro (move_requires (lemma_monotone_array s (i + 1)));
      lemma_append_count_aux l col (make_monotone_array s (i + 1))
    end;
    if count l sol' = 1 then begin
      mem_index l sol';
      lemma_monotone_col_mem s i maxe (exp l)
    end else begin
      if i < length w - 1 then
        count_neq (make_monotone_array s (i + 1)) l;
      lemma_make_leaf_col_not_mem s i maxe l;
      if count l sol = 1 then mem_index l sol
    end
  end else
    if mem l col then
      mem_index l col
    else if i < length w - 1 then begin
      lemma_append_count_aux l col (make_monotone_array s (i + 1));
      lemma_make_monotone_array_count s (i + 1) l
    end else begin
      lemma_make_leaf_col_not_mem s i maxe l;
      if count l sol = 1 then mem_index l sol
    end

let lemma_make_monotone_array_perm
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w): Lemma
  (ensures permutation item (make_monotone_array s 0) (unfold_solution s (hi - lo))) =
  forall_intro (move_requires (lemma_make_monotone_array_count s 0))

let rec lemma_make_leaf_col_sum #hi #w (s: solution hi 1 w) (i: index_t w) (j: pos): Lemma
  (requires j <= max_exp (unfold_solution s (hi - 1)) i)
  (ensures (
    assert(solution_wf hi 1 w s (length s));
    solution_sum' (make_leaf_col s i j) =$ one -$ qpow2 (-j))) =
  assert(solution_wf hi 1 w s (length s));
  let s' = make_leaf_col s i j in
  match j with
  | 1 ->
    calc (=$) {
      solution_sum' s';
      =${}
      qpow2 (-exp s'.[0]) +$ solution_sum' (tail s');
      =${}
      qpow2 (-j);
      =${}
      qpow2 0 -$ qpow2 (-j);
      =${assert_norm(qpow2 0 =$ one)}
      one -$ qpow2 (-j);
    }
  | _ -> 
    calc (=$) {
      solution_sum' s';
      =${}
      qpow2 (-exp s'.[0]) +$ solution_sum' (tail s');
      =${lemma_tl s'.[0] (make_leaf_col s i (j - 1))}
      qpow2 (-exp s'.[0]) +$ solution_sum' (make_leaf_col s i (j - 1));
      =${lemma_make_leaf_col_sum s i (j - 1)}
      qpow2 (-j) +$ (one -$ qpow2 (-(j - 1)));
      =${sub_comm (qpow2 (-j)) one (qpow2 (-(j - 1)))}
      one +$ (qpow2 (-j) -$ qpow2 (-(j - 1)));
      =${sub_neg one (qpow2 (-j)) (qpow2 (-(j - 1)))}
      one -$ (qpow2 (-(j - 1)) -$ qpow2 (-j));
      =${qpow2_minus (-(j - 1))}
      one -$ qpow2 (-j);
    }

let rec lemma_monotone_array_kraft_sum
  #hi #w (s: solution hi 1 w) (i: index_t w): Lemma
  (ensures
    solution_sum' (make_monotone_array s i) =$
    of_int (length w - i) -$ kraft_sum (slice (solution_len s) i (length w)))
  (decreases length w - i) =
  let sol = unfold_solution s (hi - 1) in
  let mexp = max_exp sol i in
  lemma_solution_len_gt_two s;
  assert(solution_wf hi 1 w s (length s));
  lemma_max_exp_gt_zero s i;

  if i = length w - 1 then
    calc (=$) {
      solution_sum' (make_monotone_array s i);
      =${}
      solution_sum' (make_leaf_col s i mexp);
      =${lemma_make_leaf_col_sum s i mexp}
      one -$ qpow2 (-mexp);
      =${}
      of_int (length w - i) -$ qpow2 (-mexp);
      =${}
      of_int (length w - i) -$ (qpow2 (-mexp) +$ kraft_sum (empty #nat));
      =${lemma_tl mexp (empty #nat)}
      of_int (length w - i) -$ (kraft_sum (cons mexp (empty #nat)));
      =${}
      of_int (length w - i) -$ (kraft_sum (create 1 mexp));
      =${assert(slice (solution_len s) i (length w) `equal` create 1 mexp)}
      of_int (length w - i) -$ kraft_sum (slice (solution_len s) i (length w));
    }
  else
    let ks = kraft_sum (slice (solution_len s) i (length w)) in
    let ks' = kraft_sum (slice (solution_len s) (i + 1) (length w)) in
    let n' = of_int (length w - (i + 1)) in
    calc (=$) {
      solution_sum' (make_monotone_array s i);
      =${}
      solution_sum' (make_leaf_col s i mexp @| make_monotone_array s (i + 1));
      =${
        lemma_solution_sum'_append
          (make_leaf_col s i mexp) (make_monotone_array s (i + 1))
      }
      solution_sum' (make_leaf_col s i mexp) +$
      solution_sum' (make_monotone_array s (i + 1));
      =${
        lemma_make_leaf_col_sum s i mexp;
        lemma_monotone_array_kraft_sum s (i + 1)
      }
      (one -$ qpow2 (-mexp)) +$ (n' -$ ks');
      =${sub_plus_l one (qpow2 (-mexp)) (n' -$ ks')}
      one -$ ((qpow2 (-mexp)) -$ (n' -$ ks'));
      =${sub_plus_l (qpow2 (-mexp)) n' ks'}
      one -$ ((qpow2 (-mexp) -$ n') +$ ks');
      =${plus_comm ((qpow2 (-mexp)) -$ n') ks'}
      one -$ (ks' +$ ((qpow2 (-mexp)) -$ n'));
      =${sub_plus_r ks' (qpow2 (-mexp)) n'}
      one -$ ((ks' +$ (qpow2 (-mexp))) -$ n');
      =${}
      one -$ (ks -$ n');
      =${}
      one +$ (n' -$ ks);
      =${sub_plus_r one n' ks}
      (one +$ n') -$ ks;
      =${}
      of_int (length w - i) -$ ks;
    }

#push-options "--fuel 3 --ifuel 2 --z3rlimit 1024 --z3seed 3"
let lemma_init_merge_seq #hi #lo #w prev =
  let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
  let w' = slice w 0 2 in
  assert(filter_leaves x `equal` x);
  assert(filter_leaves x `equal` make_base_set (lo - 1) (slice w 0 2));
  lemma_unfold_packages_all_leaves x;
  lemma_unfold_solution_leaf x (hi - (lo - 1));
  lemma_empty (unfold_packages x);
  assert(length (unfold_packages x) = 0);
  assert(unfold_packages x == empty #item)
#pop-options

#push-options "--ifuel 0 --z3seed 111 --z3rlimit 1024"
let rec lemma_do_package_merge_len_lower_bound #hi #lo #w prev =
  let n = length w in
  match lo with
  | 1 -> ()
  | _ ->
    let e = Math.Lib.max 0 ((log2 n) - (hi - lo)) in
    let e' = Math.Lib.max 0 ((log2 n) - (hi - (lo - 1))) in
    let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
    lemma_init_merge_seq prev;
    let x' = merge prev 2 0 x in
    lemma_do_package_merge_len_lower_bound x'

let rec lemma_do_package_merge_len_upper_bound #hi #lo #w x fuel =
  match fuel with
  | 0 -> ()
  | _ -> 
    let x' = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
    lemma_init_merge_seq x;
    lemma_do_package_merge_len_upper_bound (merge x 2 0 x') (fuel - 1)
#pop-options

let lemma_merge_last_not_package
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false)
  (x: intermediate_solution prev i j): Lemma
  (requires length (merge prev i j x) > 2 * length w - 2)
  (ensures Package? (last (merge prev i j x))) =
  let x' = merge prev i j x in
  let n = length w in
  if Leaf? (last x') then begin
    let p = Package prev.[2 * n - 4] prev.[2 * n - 3] in
    assert(package_gt_div2 w prev (2 * n - 4));
    mem_index p x';
    exists_elim
      (False)
      (get_proof (exists k. x'.[k] == p))
      (fun k -> if k < length x' - 1 then
        lemma_weight_sorted_lt x' k (length x' - 1))
  end

let rec lemma_do_package_merge_last_not_package
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w) (i: pos{i < lo}): Lemma
  (requires length (do_package_merge prev i) > 2 * length w - 2)
  (ensures Package? (last (do_package_merge prev i)))
  (decreases i) =
  let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
  lemma_init_merge_seq prev;
  match i with
  | 1 -> 
    calc (==) {
      do_package_merge prev i;
      =={}
      do_package_merge #hi #(lo - 1) #w (merge_solution prev) (i - 1);
      =={}
      merge prev 2 0 x;
    };
    lemma_merge_last_not_package prev 2 0 x
  | _ ->
    lemma_do_package_merge_last_not_package #hi #(lo - 1) #w (merge_solution prev) (i - 1)

let rec lemma_weight_sorted_base_seq (e: pos) (w: weight_seq) (i: index_t w): Lemma
  (ensures (
    let w' = make_base_set e w in
    weight_sorted (slice w' i (length w'))))
  (decreases length w - i) =
  let w' = make_base_set e w in
  if i < length w' - 1 then begin
    lemma_weight_seq_lt w i (i + 1);
    lemma_weight_sorted_base_seq e w (i + 1)
  end

let lemma_base_set_package_gt_div2 (e: pos) (w: weight_seq) (i: index_t w): Lemma
  (ensures package_gt_div2 w (make_base_set e w) i) =
  if i > 0 && i % 2 = 0 && i + 1 < length w then
    lemma_weight_seq_lt w (i / 2 + 1) (i + 1)

let rec lemma_filter_leaves_base_set (e: pos) (w: weight_seq) (i: nat): Lemma
  (requires 2 <= i /\ i <= length w)
  (ensures (
    let w' = make_base_set e w in
    let w'' = slice w' 0 i in
    filter_leaves w'' == make_base_set e (slice w 0 i)))
  (decreases i) =
  let w' = make_base_set e w in
  let w'' = slice w' 0 i in
  match i with
  | 2 ->
    calc (==) {
      filter_leaves w'';
      =={}
      cons w''.[0] (filter_leaves (tail w''));
      =={}
      cons w''.[0] (cons w''.[1] (filter_leaves (empty #item)));
      =={}
      cons w''.[0] (cons w''.[1] (empty #item));
      =={append_empty_r (create 1 w''.[1])}
      cons w''.[0] (create 1 w''.[1]);
    };
    assert(make_base_set e (slice w 0 i) `equal` filter_leaves w'')
  | _ ->
    calc (==) {
      filter_leaves w'';
      =={}
      filter_leaves (snoc (slice w' 0 (i - 1)) (last w''));
      =={lemma_filter_leaves_snoc_leaf (slice w' 0 (i - 1)) (last w'')}
      snoc (filter_leaves (slice w' 0 (i - 1))) (last w'');
      =={lemma_filter_leaves_base_set e w (i - 1)}
      snoc (make_base_set e (slice w 0 (i - 1))) (last w'');
      =={
        assert(
          snoc (make_base_set e (slice w 0 (i - 1))) (last w'') `equal`
          make_base_set e (slice w 0 i))
      }
      make_base_set e (slice w 0 i);
    }

let rec lemma_solution_sum'_base_set_slice (e: pos) (w: weight_seq) (i: nat{
    i <= length (make_base_set e w)
  }): Lemma
  (ensures solution_sum' (slice (make_base_set e w) 0 i) =$ qpow2 (-e) *$ of_int i)
  (decreases i) =
  let w' = make_base_set e w in
  match i with
  | 0 -> ()
  | _ ->
    calc (=$) {
      solution_sum' (slice w' 0 i);
      =${}
      solution_sum' (snoc (slice w' 0 (i - 1)) w'.[i - 1]);
      =${lemma_solution_sum'_append (slice w' 0 (i - 1)) (create 1 w'.[i - 1])}
      solution_sum' (slice w' 0 (i - 1)) +$ solution_sum' (create 1 w'.[i - 1]);
      =${lemma_solution_sum'_single w'.[i - 1]}
      solution_sum' (slice w' 0 (i - 1)) +$ qpow2 (-e);
      =${lemma_solution_sum'_base_set_slice e w (i - 1)}
      (qpow2 (-e) *$ of_int (i - 1)) +$ qpow2 (-e) *$ one;
      =${distributivity_add_left (qpow2 (-e)) (of_int (i - 1)) one}
      qpow2 (-e) *$ of_int i;
    }

let rec lemma_base_set_count_one (e: pos) (w: weight_seq)
  (i: nat{i <= length (make_base_set e w)}) (j: nat{j < i}): Lemma
  (ensures (
    let w' = slice (make_base_set e w) 0 i in
    count w'.[j] w' == 1))
  (decreases i - j) =
  let w' = slice (make_base_set e w) 0 i in
  if j + 1 = i then
    if i = 1 then
      count_create 1 w'.[j] w'.[j]
    else begin
      let w'' = slice w' 0 (i - 1) in
      count_neq w'' w'.[j];
      lemma_append_count_aux w'.[j] w'' (create 1 w'.[j]);
      assert(snoc w'' w'.[j] `equal` w')
    end
  else begin
    let w'' = slice w' 0 (i - 1) in
    count_create 1 w'.[i - 1] w'.[j];
    lemma_base_set_count_one e w (i - 1) j;
    lemma_append_count_aux w'.[j] w'' (create 1 w'.[i - 1]);
    assert(snoc w'' w'.[i - 1] `equal` w')
  end

let lemma_base_set_monotone_elem (e: pos) (w: weight_seq) 
  (i: nat{2 <= i /\ i <= length (make_base_set e w)}) (j: nat{j < i}): Lemma
  (ensures (
    let w' = slice (make_base_set e w) 0 i in
    monotone_elem w' (slice w 0 i) e e j)) =
  let w' = make_base_set e w in
  let w'' = slice w' 0 i in
  if j > 0 then
    assert(w'.[j - 1] == w''.[j - 1])
  else
    assert(item_id w''.[j] == 0)

#set-options "--z3seed 88"
let lemma_monotone_base_set (e: pos) (w: weight_seq) (i: nat{
    2 <= i /\ i <= length (make_base_set e w)
  }): Lemma
  (ensures (
    let w' = slice (make_base_set e w) 0 i in
    monotone (unfold_solution w' 0) (slice w 0 i) e e
  )) =
  let w' = slice (make_base_set e w) 0 i in
  lemma_filter_leaves_equal w';
  forall_intro (lemma_base_set_count_one e w i);
  no_dup_count_one w';
  forall_intro (lemma_base_set_monotone_elem e (slice w 0 i) i)

let lemma_base_set_solution_wf (e: pos) (w: weight_seq) (i: nat{
    2 <= i /\ i <= length (make_base_set e w)
  }): Lemma
  (ensures solution_wf e e w (make_base_set e w) i) =
  let w' = make_base_set e w in
  let w'' = slice w' 0 i in
  lemma_filter_leaves_equal w'';
  lemma_filter_leaves_base_set e w i;
  lemma_solution_sum'_base_set_slice e w i;
  lemma_monotone_base_set e w i

let lemma_base_set_solution hi w =
  let x = make_base_set hi w in
  lemma_filter_leaves_equal x;
  lemma_weight_sorted_base_seq hi w 0;
  forall_intro (lemma_base_set_package_gt_div2 hi w);
  forall_intro (move_requires (lemma_base_set_solution_wf hi w))

let lemma_do_package_merge_div2_gt
  (max_len: pos) (w: weight_seq)
  (fuel: nat{fuel < max_len}) (j: nat{j < length w * 2 - 2}): Lemma
  (requires (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) fuel in
    length w <= pow2 max_len /\ length s == 2 * length w - 1))
  (ensures (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) fuel in
    let s' = slice s 0 (length s - 1) in
    package_gt_div2 w s' j
  )) =
  let s = do_package_merge #max_len #max_len #w
    (make_base_set max_len w) fuel in
  let s' = slice s 0 (length s - 1) in
  if j % 2 = 0 && j + 1 < length s' then
    assert(package_gt_div2 w s j)

let lemma_do_package_merge_solution_wf
  (max_len: pos) (w: weight_seq)
  (fuel: nat{fuel < max_len}) (j: pos{2 <= j /\ j <= length w * 2 - 2}) : Lemma
  (requires (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) fuel in
    length w <= pow2 max_len /\ length s == 2 * length w - 1))
  (ensures (
    let s = do_package_merge #max_len #max_len #w
      (make_base_set max_len w) fuel in
    let s' = slice s 0 (length s - 1) in
    solution_wf max_len (max_len - fuel) w s' j
  )) = 
  let s = do_package_merge #max_len #max_len #w
    (make_base_set max_len w) fuel in
  let s' = slice s 0 (length s - 1) in
  assert(solution_wf max_len (max_len - fuel) w s j)

let rec lemma_weight_sorted_head (s: seq item) (i: nat{i <= length s}): Lemma
  (requires weight_sorted s)
  (ensures weight_sorted (slice s 0 i))
  (decreases i) =
  match i with
  | 0 -> ()
  | _ ->
    lemma_weight_sorted_head s (i - 1);
    if i - 2 >= 0 then lemma_weight_sorted_lt s (i - 2) (i - 1);
    lemma_weight_sorted_snoc (slice s 0 (i - 1)) s.[i - 1]

let lemma_do_package_merge_slice max_len w =
  let w' = make_base_set max_len w in
  let s = do_package_merge #max_len #max_len #w w' (max_len - 1) in
  let s' = slice s 0 (length s - 1) in
  let fuel = max_len - 1 in
  lemma_do_package_merge_last_not_package #max_len #max_len #w w' fuel;
  lemma_filter_leaves_snoc_package s' (last s);
  forall_intro (move_requires (lemma_do_package_merge_div2_gt max_len w fuel));
  forall_intro (move_requires (lemma_do_package_merge_solution_wf max_len w fuel));
  lemma_weight_sorted_head s (length s - 1)

let lemma_package_merge max_len w =
  let n = length w in
  let s = package_merge max_len w in
  let sl = solution_len s in
  let us = unfold_solution s (max_len - 1) in
  let ma = make_monotone_array s 0 in
  calc (=$) {
    of_int n -$ one;
    =${assert_norm(of_int (n - 1) =$ of_int n -$ one)}
    of_int (n - 1);
    =${assert_norm(of_int (n - 1) =$ qpow2 (-1) *$ of_int (2 * n - 2))}
    qpow2 (-1) *$ of_int (2 * n - 2);
    =${assert(solution_wf max_len 1 w s (length s))}
    solution_sum max_len 1 s;
    =${
      lemma_make_monotone_array_perm s;
      lemma_solution_sum'_perm us ma
    }
    solution_sum' ma;
    =${lemma_monotone_array_kraft_sum s 0}
    of_int n -$ kraft_sum sl;
  }

#set-options "--z3seed 21 --fuel 1 --ifuel 0"
let lemma_do_package_merge_weight_upper_bound_aux (s: seq item): Lemma
  (requires length s >= 2)
  (ensures solution_weight_sum (slice s 0 (length s / 2 * 2)) <= solution_weight_sum s) =
  let s' = slice s 0 (length s / 2 * 2) in
  if length s / 2 * 2 < length s then
    lemma_solution_weight_sum_snoc_item s' (last s)

let rec lemma_do_package_merge_weight_sum_upper_bound
  #hi (#lo: pos{lo <= hi}) #w (prev: solution hi lo w) (fuel: nat{fuel < lo}): Lemma
  (ensures (
    let s = do_package_merge prev fuel in
    solution_weight_sum s <= solution_weight_sum prev + fuel * weight_sum w
  )) (decreases fuel) =
  match fuel with
  | 0 -> ()
  | _ ->
    let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
    lemma_init_merge_seq prev;
    let x' = merge prev 2 0 x in
    let prev' = slice prev 0 (length prev / 2 * 2) in
    let ps' = solution_weight_sum prev' in
    let ps = solution_weight_sum prev in
    let ws = weight_sum w in
    let ws' = (fuel - 1) * weight_sum w in
    lemma_do_package_merge_weight_sum_upper_bound #hi #(lo - 1) #w x' (fuel - 1);
    assert(solution_weight_sum (do_package_merge x' (fuel - 1)) <=
      solution_weight_sum x' + ws');
    calc (==) {
      solution_weight_sum x' + ws';
      =={}
      ws + ps' + ws';
      =={Math.Lemmas.paren_add_right ws ps' ws'}
      ws + (ps' + ws');
      =={}
      ws + (ws' + ps');
      =={
        Math.Lemmas.paren_add_right ws ws' ps';
        Math.Lemmas.paren_add_left ws ws' ps'
      }
      (ws + ws') + ps';
      =={assert_norm(1 * ws == ws)}
      (1 * ws + ws') + ps';
      =={Math.Lemmas.distributivity_add_left 1 (fuel - 1) (weight_sum w)}
      fuel * weight_sum w + ps';
    };
    lemma_do_package_merge_weight_upper_bound_aux prev

let rec lemma_solution_weight_sum (s: seq item{length s > 0}) (i: index_t s): Lemma
  (ensures item_weight s.[i] <= solution_weight_sum s)
  (decreases i) =
  match i with
  | 0 -> ()
  | _ -> lemma_solution_weight_sum (tail s) (i - 1)

#push-options "--fuel 2 --ifuel 2"
let rec lemma_solution_weight_base_set
  (e: pos) (w: weight_seq) (i: pos): Lemma
  (requires i <= length w)
  (ensures solution_weight_sum (slice (make_base_set e w) 0 i) == weight_sum (slice w 0 i))
  (decreases i) =
  match i with
  | 1 -> ()
  | _ ->
    let b = make_base_set e w in
    calc (==) {
      solution_weight_sum (slice b 0 i);
      =={}
      solution_weight_sum (snoc (slice b 0 (i - 1)) b.[i - 1]);
      =={lemma_solution_weight_sum_snoc_item (slice b 0 (i - 1)) b.[i - 1]}
      solution_weight_sum (slice b 0 (i - 1)) + item_weight b.[i - 1];
      =={lemma_solution_weight_base_set e w (i - 1)}
      weight_sum (slice w 0 (i - 1)) + w.[i - 1];
      =={lemma_weight_sum_snoc (slice w 0 (i - 1)) w.[i - 1]}
      weight_sum (snoc (slice w 0 (i - 1)) w.[i - 1]);
      =={}
      weight_sum (slice w 0 i);
    }
#pop-options

#set-options "--z3seed 4"
let lemma_do_package_merge_weight_upper_bound max_len w fuel =
  let n = length w in
  let x = make_base_set max_len w in
  let s = do_package_merge #max_len #max_len #w x fuel in
  assert(slice w 0 (length w) `equal` w);
  assert(slice x 0 (length x) `equal` x);
  lemma_do_package_merge_weight_sum_upper_bound #max_len #max_len #w x fuel;
  lemma_solution_weight_base_set max_len w (length w);
  forall_intro (lemma_solution_weight_sum s)

let rec lemma_leaf_row_unfold (s: seq item) (depth: pos): Lemma
  (ensures
    unfold_solution s depth ==
    leaf_row s depth @| unfold_solution s (depth - 1))
  (decreases depth) =
  match depth with
  | 1 ->
    calc (==) {
      leaf_row s depth @| unfold_solution s (depth - 1);
      =={}
      leaf_row (unfold_packages s) 0 @| filter_leaves s;
      =={}
      filter_leaves (unfold_packages s) @| filter_leaves s;
      =={}
      unfold_solution (unfold_packages s) 0 @| filter_leaves s;
      =={}
      unfold_solution s 1;
    }
  | _ ->
    calc (==) {
      unfold_solution s depth;
      =={}
      (unfold_solution (unfold_packages s) (depth - 1)) @| filter_leaves s;
      =={lemma_leaf_row_unfold (unfold_packages s) (depth - 1)}
      (leaf_row (unfold_packages s) (depth - 1) @|
      unfold_solution (unfold_packages s) (depth - 2)) @|
      filter_leaves s;
      =={
        append_assoc
          (leaf_row (unfold_packages s) (depth - 1))
          (unfold_solution (unfold_packages s) (depth - 2))
          (filter_leaves s)
      }
      leaf_row (unfold_packages s) (depth - 1) @|
      (unfold_solution (unfold_packages s) (depth - 2) @| filter_leaves s);
      =={}
      leaf_row s depth @| unfold_solution s (depth - 1);
    }

let rec lemma_max_exp_append (s1 s2: leaf_seq) (i: nat): Lemma
  (ensures max_exp (s1 @| s2) i == Math.Lib.max (max_exp s1 i) (max_exp s2 i))
  (decreases length s1) =
  match length s1 with
  | 0 ->
    calc (==) {
      (max_exp (s1 @| s2) i) <: nat;
      =={
        lemma_empty s1;
        append_empty_l s2
      }
      max_exp s2 i;
      =={}
      Math.Lib.max (max_exp s1 i) (max_exp s2 i);
    }
  | _ ->
    assert(tail (s1 @| s2) `equal` ((tail s1) @| s2));
    lemma_max_exp_append (tail s1) s2 i

let rec lemma_leaf_row_empty (s: seq item) (i: nat): Lemma
  (requires length s == 0)
  (ensures leaf_row s i == empty #item) =
  lemma_empty s;
  match i with
  | 0 -> ()
  | _ -> lemma_leaf_row_empty s (i - 1)

let rec lemma_do_package_merge_cont
  #hi #lo #w (prev: solution hi lo w) (fuel: nat{fuel < lo - 1}): Lemma
  (ensures
    merge_solution (do_package_merge prev fuel) ==
    do_package_merge prev (fuel + 1))
  (decreases fuel) =
  match fuel with
  | 0 ->
    calc (==) {
      do_package_merge prev (fuel + 1);
      =={}
      do_package_merge prev 1;
      =={}
      do_package_merge (merge_solution prev) fuel;
      =={}
      merge_solution prev;
      =={}
      merge_solution (do_package_merge prev 0);
    }
  | _ ->
    calc (==) {
      do_package_merge prev (fuel + 1);
      =={}
      do_package_merge (merge_solution prev) fuel;
      =={lemma_do_package_merge_cont (merge_solution prev) (fuel - 1)}
      merge_solution (do_package_merge (merge_solution prev) (fuel - 1));
      =={}
      merge_solution (do_package_merge prev fuel);
    }

#push-options "--fuel 2 --ifuel 2"
let rec lemma_unfold_packages_prefix (a b: seq item): Lemma
  (requires a `prefix` b)
  (ensures unfold_packages a `prefix` unfold_packages b)
  (decreases length b - length a) =
  let a' = unfold_packages a in
  if length a = 0 then
    lemma_empty a
  else if length a < length b then begin
    lemma_unfold_packages_prefix (snoc a b.[length a]) b;
    match b.[length a] with
    | Leaf _ _ _ -> lemma_unfold_packages_snoc_leaf a b.[length a]
    | Package i1 i2 ->
      calc (==) {
        unfold_packages (snoc a b.[length a]);
        =={lemma_unfold_packages_snoc_package a i1 i2}
        snoc (snoc a' i1) i2;
      };
      prefix_alt a' (snoc a' i1);
      prefix_alt (snoc a' i1) (snoc (snoc a' i1) i2)
  end
#pop-options

let lemma_merge_unpack
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev false)
  (x: intermediate_solution prev i j) (s: seq item): Lemma
  (requires s `prefix` merge prev i j x)
  (ensures solution_row s 1 `prefix` prev)
  (decreases %[length w - i; length prev - j]) =
  let x' = merge prev i j x in
  calc (==) {
    solution_row x' 1;
    =={}
    solution_row (unfold_packages x') 0;
    =={}
    unfold_packages x';
  };
  calc (==) {
    solution_row s 1;
    =={}
    solution_row (unfold_packages s) 0;
    =={}
    unfold_packages s;
  };
  lemma_unfold_packages_prefix s x'

#push-options "--fuel 0 --ifuel 0"
let lemma_merge_solution_unpack
  #hi (#lo: intermediate_exp hi) #w (prev: solution hi lo w) (s: seq item): Lemma
  (requires s `prefix` merge_solution prev)
  (ensures solution_row s 1 `prefix` prev) =
  let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
  lemma_init_merge_seq prev;
  lemma_merge_unpack prev 2 0 x s
#pop-options

let rec lemma_filter_leaves_prefix (a b: seq item): Lemma
  (requires a `prefix` b)
  (ensures filter_leaves a `prefix` filter_leaves b)
  (decreases length b - length a) =
  if length a > 0 && length a < length b then begin
    let t = b.[length a] in
    lemma_filter_leaves_prefix (snoc a t) b;
    if Leaf? t then begin
      calc (==) {
        filter_leaves (snoc a t);
        =={lemma_filter_leaves_snoc_leaf a t}
        snoc (filter_leaves a) t;
      };
      prefix_alt (filter_leaves a) (snoc (filter_leaves a) t)
    end else
      lemma_filter_leaves_snoc_package a t
  end

let rec lemma_pack_unpack_aux
  #max_len (w: valid_weight_seq max_len) (row: seq item) (i: pos{i < max_len}): Lemma
  (requires (
    let s: solution max_len max_len w = make_base_set max_len w in
    row `prefix` do_package_merge s i))
  (ensures (
    let b: solution max_len max_len w = make_base_set max_len w in
    let s' = do_package_merge b (i - 1) in
    let s = do_package_merge b i in
    leaf_row row 1 `prefix` filter_leaves s'
  )) (decreases length row) =
  let b: solution max_len max_len w = make_base_set max_len w in
  let s' = do_package_merge b (i - 1) in
  let s = do_package_merge b i in
  let row' = leaf_row row 1 in
  match length row with
  | 0 -> lemma_leaf_row_empty row 1
  | _ ->
    lemma_pack_unpack_aux w (unsnoc row) i;
    if Leaf? (last row) then
      lemma_unfold_packages_snoc_leaf (unsnoc row) (last row)
    else begin
      lemma_do_package_merge_cont b (i - 1);
      lemma_merge_solution_unpack s' row;
      lemma_filter_leaves_prefix (solution_row row 1) s'
    end

let rec lemma_solution_row
  #max_len (w: valid_weight_seq max_len) (row: seq item) (i j: nat): Lemma
  (requires (
    let b: solution max_len max_len w = make_base_set max_len w in
    i < max_len /\ j <= i /\ row `prefix` do_package_merge b i))
  (ensures (
    let b: solution max_len max_len w = make_base_set max_len w in
    let s' = do_package_merge b (i - j) in
    solution_row row j `prefix` s'
  )) (decreases j) =
  let b: solution max_len max_len w = make_base_set max_len w in
  if j > 0 then begin
    lemma_do_package_merge_cont b (i - 1);
    lemma_merge_solution_unpack (do_package_merge b (i - 1)) row;
    lemma_solution_row w (solution_row row 1) (i - 1) (j - 1);
    calc (==) {
      solution_row (solution_row row 1) (j - 1);
      =={}
      solution_row (solution_row (unfold_packages row) 0) (j - 1);
      =={}
      solution_row (unfold_packages row) (j - 1);
      =={}
      solution_row row j;
    }
  end

let lemma_leaf_row
  #max_len (w: valid_weight_seq max_len) (row: seq item) (i j: nat): Lemma
  (requires (
    let b: solution max_len max_len w = make_base_set max_len w in
    i < max_len /\ j <= i /\ row `prefix` do_package_merge b i))
  (ensures leaf_row row j `prefix` make_base_set (max_len - i + j) w) =
  lemma_solution_row w row i j;
  let b: solution max_len max_len w = make_base_set max_len w in
  let s' = do_package_merge b (i - j) in
  assert(solution_wf max_len (max_len - i + j) w s' (length s'));
  lemma_filter_leaves_prefix (solution_row row j) s'

let rec lemma_max_exp_leaf_row_aux
  #max_len (w: valid_weight_seq max_len) (row: seq item) (e: pos) (i: index_t row): Lemma
  (requires row `prefix` make_base_set e w)
  (ensures max_exp row i == e)
  (decreases length row) =
  assert(((unsnoc row) @| create 1 (last row)) `equal` row);
  if i = length row - 1 then begin
    calc (==) {
      (max_exp row i) <: nat;
      =={}
      max_exp ((unsnoc row) @| create 1 (last row)) i;
      =={lemma_max_exp_append (unsnoc row) (create 1 (last row)) i}
      Math.Lib.max 0 (max_exp (create 1 (last row)) i);
      =={}
      Math.Lib.max 0 (Math.Lib.max (exp (last row)) 0);
      =={}
      e;
    }
  end else
    calc (==) {
      (max_exp row i) <: nat;
      =={}
      max_exp ((unsnoc row) @| create 1 (last row)) i;
      =={lemma_max_exp_append (unsnoc row) (create 1 (last row)) i}
      Math.Lib.max (max_exp (unsnoc row) i) 0;
      =={lemma_max_exp_leaf_row_aux w (unsnoc row) e i}
      Math.Lib.max e 0;
      =={}
      e;
    }

let lemma_max_exp_leaf_row
  #max_len (w: valid_weight_seq max_len) (row: seq item) (i j k: nat): Lemma
  (requires (
    let b: solution max_len max_len w = make_base_set max_len w in
    i < max_len /\ j <= i /\ 
    row `prefix` do_package_merge b i))
  (ensures (
    let row' = leaf_row row j in
    let l = length row' in
    (k >= l ==> max_exp row' k == 0) /\
    (k < l ==> max_exp row' k == max_len - i + j)))
  (decreases length row) =
  let row' = leaf_row row j in
  let l = length row' in
  if k >= l then begin
    let e = max_exp row' k in
    if e > 0 then
      exists_elim False
        (get_proof (exists l. exp row'.[l] == e /\ item_id row'.[l] == k))
        (fun l -> lemma_leaf_row w row i j)
  end else begin
    lemma_leaf_row w row i j;
    lemma_max_exp_leaf_row_aux w row' (max_len - i + j) k
  end

let lemma_analyze_row_term_max
  #nbits #max_len #w
  (bits: item_bit_map nbits max_len 1 w) (depth: depth_t max_len)
  i j (k: col_package_count max_len w depth i j)
  (s: intermediate_exp_seq' max_len w depth j) (l: index_t s) : Lemma
  (requires i = length (solution_row (package_merge max_len w) depth))
  (ensures s.[l] == max_exp (unfold_solution (package_merge max_len w) depth) l) =
  let t = package_merge max_len w in
  if depth > 0 then begin
    calc (==) {
      (max_exp (unfold_solution t depth) l) <: nat;
      =={lemma_leaf_row_unfold t depth}
      max_exp (leaf_row t depth @| unfold_solution t (depth - 1)) l;
      =={lemma_max_exp_append (leaf_row t depth) (unfold_solution t (depth - 1)) l}
      Math.Lib.max
        (max_exp (leaf_row t depth) l) 
        (max_exp (unfold_solution t (depth - 1)) l);
    };
    if l >= j then lemma_max_exp_leaf_row w t (max_len - 1) depth l
  end

let rec lemma_solution_row_cont (s: seq item) (i: nat): Lemma
  (ensures unfold_packages (solution_row s i) == solution_row s (i + 1))
  (decreases i) =
  match i with
  | 0 ->
    calc (==) {
      unfold_packages (solution_row s i);
      =={}
      unfold_packages s;
      =={}
      solution_row (unfold_packages s) 0;
      =={}
      solution_row s 1;
    }
  | _ ->
    calc (==) {
      unfold_packages (solution_row s i);
      =={}
      unfold_packages (solution_row (unfold_packages s) (i - 1));
      =={lemma_solution_row_cont (unfold_packages s) (i - 1)}
      solution_row (unfold_packages s) i;
      =={}
      solution_row s (i + 1);
    }

let lemma_analyze_row_terminate #nbits #max_len #w bits depth i j k s =
  forall_intro (move_requires (lemma_analyze_row_term_max bits depth i j k s));
  lemma_solution_row_cont (package_merge max_len w) depth

let lemma_analyze_row_set_leaf
  #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w) (depth: depth_t max_len)
  i j (k: col_package_count max_len w depth i j): Lemma
  (requires
    i < length (solution_row (package_merge max_len w) depth) /\
    (UInt.to_vec bits.[i]).[max_len - 1 - depth])
  (ensures Leaf? (solution_row (package_merge max_len w) depth).[i]) =
  let sol = package_merge max_len w in
  let row = solution_row sol depth in
  let b: solution max_len max_len w = make_base_set max_len w in
  lemma_solution_row w sol (max_len - 1) depth;
  let d = max_len - 1 - depth in
  let x = do_package_merge b d in
  assert(forall (k: index_t x). (UInt.to_vec bits.[k]).[d] == Leaf? x.[k]);
  assert((UInt.to_vec bits.[i]).[d] == Leaf? x.[i])

#push-options "--fuel 0"
let lemma_analyze_row_set_idx
  #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w) (depth: depth_t max_len)
  i j (k: col_package_count max_len w depth i j): Lemma
  (requires
    i < length (solution_row (package_merge max_len w) depth) /\
    (UInt.to_vec bits.[i]).[max_len - 1 - depth])
  (ensures (
    let sol = package_merge max_len w in
    let row = solution_row sol depth in
    let row'' = slice row 0 (i + 1) in
    j < length w /\
    j + 1 == length (filter_leaves row'') /\
    i + 1 <= 2 * length w - 1 /\
    k == length (unfold_packages row''))) =
  let sol = package_merge max_len w in
  let row = solution_row sol depth in
  let b: solution max_len max_len w = make_base_set max_len w in
  let d = max_len - 1 - depth in
  let x = do_package_merge b d in
  lemma_solution_row w sol (max_len - 1) depth;
  lemma_analyze_row_set_leaf bits depth i j k;

  let row' = slice row 0 i in
  let row'' = slice row 0 (i + 1) in
  prefix_alt row' row'';
  prefix_alt row'' row;
  lemma_filter_leaves_prefix row' x;
  assert(row.[i] == x.[i]);
  lemma_filter_leaves_snoc_leaf row' row.[i];

  lemma_do_package_merge_len_upper_bound b d;
  lemma_unfold_packages_snoc_leaf row' row.[i]
#pop-options

let rec lemma_unfold_solution_leaf_row (s: seq item) (depth: nat): Lemma
  (ensures
    leaf_row s (depth + 1) @| unfold_solution s depth ==
    unfold_solution s (depth + 1))
  (decreases depth) =
  let s' = unfold_packages s in
  match depth with
  | 0 ->
    calc (==) {
      leaf_row s (depth + 1) @| unfold_solution s depth;
      =={}
      (filter_leaves (solution_row s 1)) @| filter_leaves s;
      =={}
      (filter_leaves (solution_row s' 0)) @| filter_leaves s;
      =={}
      (filter_leaves s') @| filter_leaves s;
      =={}
      (unfold_solution s' 0) @| filter_leaves s;
      =={}
      unfold_solution s (depth + 1);
    }
  | _ ->
    calc (==) {
      leaf_row s (depth + 1) @| unfold_solution s depth;
      =={}
      (filter_leaves (solution_row s (depth + 1))) @|
      unfold_solution s' (depth - 1) @|
      filter_leaves s;
      =={}
      (leaf_row s' depth) @| unfold_solution s' (depth - 1) @| filter_leaves s;
      =={append_assoc (leaf_row s' depth) (unfold_solution s' (depth - 1)) (filter_leaves s)}
      ((leaf_row s' depth) @| unfold_solution s' (depth - 1)) @| filter_leaves s;
      =={lemma_unfold_solution_leaf_row s' (depth - 1)}
      unfold_solution s' depth @| filter_leaves s;
      =={}
      unfold_solution s (depth + 1);
    }

let rec leaf_row_sum (s: seq item) (depth: nat): Tot leaf_seq =
  match depth with
  | 0 -> leaf_row s 0
  | _ -> leaf_row s depth @| leaf_row_sum s (depth - 1)

let rec lemma_leaf_row_sum (s: seq item) (depth: nat): Lemma
  (ensures leaf_row_sum s depth == unfold_solution s depth)
  (decreases depth) =
  match depth with
  | 0 ->
    calc (==) {
      leaf_row_sum s depth;
      =={}
      filter_leaves s;
      =={}
      unfold_solution s depth;
    }
  | _ ->
    calc (==) {
      leaf_row_sum s depth;
      =={}
      leaf_row s depth @| leaf_row_sum s (depth - 1);
      =={lemma_leaf_row_sum s (depth - 1)}
      leaf_row s depth @| unfold_solution s (depth - 1);
      =={lemma_unfold_solution_leaf_row s (depth - 1)}
      unfold_solution s depth;
    }

let lemma_leaf_row_sum_prefix (s: seq item) (depth: nat): Lemma
  (ensures leaf_row s depth `prefix` leaf_row_sum s depth) =
  prefix_alt (leaf_row s depth) (leaf_row_sum s depth)

let rec lemma_solution_row_plus (s: seq item) (a b: nat): Lemma
  (ensures solution_row (solution_row s a) b == solution_row s (a + b))
  (decreases a) =
  match a with
  | 0 ->
    calc (==) {
      solution_row (solution_row s a) b;
      =={}
      solution_row s b;
    }
  | _ ->
    calc (==) {
      solution_row (solution_row s a) b;
      =={}
      solution_row (solution_row (unfold_packages s) (a - 1)) b;
      =={lemma_solution_row_plus (unfold_packages s) (a - 1) b}
      solution_row (unfold_packages s) (a + b - 1);
      =={}
      solution_row s (a + b);
    }

let rec lemma_unfold_solution_split (s: seq item) (a b: nat): Lemma
  (ensures
    unfold_solution (solution_row s (b + 1)) a @| unfold_solution s b ==
    unfold_solution s (a + b + 1))
  (decreases a) =
  match a with
  | 0 ->
    calc (==) {
      unfold_solution (solution_row s (b + 1)) a @| unfold_solution s b;
      =={}
      leaf_row s (b + 1) @| unfold_solution s b;
      =={lemma_unfold_solution_leaf_row s b}
      unfold_solution s (b + 1);
    }
  | _ ->
    let s' = solution_row s (b + 1) in
    calc (==) {
      unfold_solution s' a @| unfold_solution s b;
      =={lemma_unfold_solution_leaf_row s' (a - 1)}
      (leaf_row s' a @| unfold_solution s' (a - 1)) @| unfold_solution s b;
      =={append_assoc
        (leaf_row s' a) (unfold_solution s' (a - 1)) (unfold_solution s b)}
      leaf_row s' a @| (unfold_solution s' (a - 1) @| unfold_solution s b);
      =={lemma_unfold_solution_split s (a - 1) b}
      leaf_row s' a @| (unfold_solution s (a + b));
      =={lemma_solution_row_plus s (b + 1) a}
      leaf_row s (a + b + 1) @| (unfold_solution s (a + b));
      =={lemma_unfold_solution_leaf_row s (a + b)}
      unfold_solution s (a + b + 1);
    }

let rec lemma_leaf_row_sum_exp_range_aux
  #max_len (w: valid_weight_seq max_len) (row: seq item)
  (fuel depth: depth_t max_len) (i: index_t (leaf_row_sum row depth)): Lemma
  (requires (
    let b: solution max_len max_len w = make_base_set max_len w in
    let s = do_package_merge b fuel in
    row `prefix` s /\ depth <= fuel))
  (ensures (
    let row' = leaf_row_sum row depth in
    max_len - fuel <= exp row'.[i] /\ exp row'.[i] <= max_len - fuel + depth))
  (decreases depth) =
  let b: solution max_len max_len w = make_base_set max_len w in
  let s = do_package_merge b fuel in
  if i < length (leaf_row row depth) then begin
    lemma_leaf_row_sum_prefix row depth;
    lemma_leaf_row w row fuel depth
  end else
    lemma_leaf_row_sum_exp_range_aux
      w row fuel (depth - 1) (i - length (leaf_row row depth))

let lemma_leaf_row_sum_exp_range
  #max_len (w: valid_weight_seq max_len) (row: seq item)
  (fuel depth: depth_t max_len): Lemma
  (requires (
    let b: solution max_len max_len w = make_base_set max_len w in
    let s = do_package_merge b fuel in
    row `prefix` s /\ depth <= fuel))
  (ensures (
    let row' = leaf_row_sum row depth in
    (forall i.
      max_len - fuel <= exp row'.[i] /\
      exp row'.[i] <= max_len - fuel + depth))) =
  forall_intro (move_requires (lemma_leaf_row_sum_exp_range_aux w row fuel depth))

let rec lemma_filter_leaves_mem (s: seq item) (i: item): Lemma
  (requires Leaf? i /\ mem i s)
  (ensures mem i (filter_leaves s))
  (decreases length s) =
  if length s > 0 && s.[0] <> i then begin
    lemma_filter_leaves_mem (tail s) i;
    if Leaf? s.[0] then lemma_mem_append (create 1 s.[0]) (filter_leaves (tail s))
  end

let rec lemma_leaf_row_sum_last (s: seq item) (depth: pos): Lemma
  (ensures
    leaf_row_sum s depth ==
    leaf_row_sum (unfold_packages s) (depth - 1) @| leaf_row s 0)
  (decreases depth) =
  match depth with
  | 1 -> 
    calc (==) {
      leaf_row_sum s depth;
      =={}
      leaf_row s 1 @| leaf_row_sum s 0;
      =={}
      (filter_leaves (solution_row (unfold_packages s) 0)) @| leaf_row s 0;
      =={}
      (filter_leaves (unfold_packages s)) @| leaf_row s 0;
    }
  | _ ->
    calc (==) {
      leaf_row_sum s depth;
      =={}
      leaf_row s depth @| leaf_row_sum s (depth - 1);
      =={lemma_leaf_row_sum_last s (depth - 1)}
      leaf_row s depth @| (leaf_row_sum (unfold_packages s) (depth - 2) @| leaf_row s 0);
      =={
        append_assoc
          (leaf_row s depth)
          (leaf_row_sum (unfold_packages s) (depth - 2))
          (leaf_row s 0)
      }
      (leaf_row s depth @| leaf_row_sum (unfold_packages s) (depth - 2)) @| leaf_row s 0;
      =={}
      (leaf_row (unfold_packages s) (depth -1) @|
      leaf_row_sum (unfold_packages s) (depth - 2)) @|
      leaf_row s 0;
    }

let lemma_leaf_next_row
  #max_len (w: valid_weight_seq max_len) (depth: depth_t max_len) (i j: nat): Lemma
  (requires (
    let sr = solution_row (package_merge max_len w) depth in
    depth > 0 /\ i < length sr /\ j < length w /\
    sr.[i] = Leaf j (depth + 1) w.[j] /\
    mem sr.[i] (filter_leaves (slice sr 0 (i + 1)))))
  (ensures (
    let s = package_merge max_len w in
    let us = unfold_solution s (depth - 1) in
    mem (Leaf j depth w.[j]) us)) =
  let s = package_merge max_len w in
  let sr = slice (solution_row s depth) 0 (i + 1) in
  let lr = filter_leaves sr in
  lemma_filter_leaves_prefix sr (solution_row s depth);
  lemma_leaf_row w s (max_len - 1) depth;
  if depth > 1 then begin
    let fuel = max_len - 1 - depth in
    let row = leaf_row_sum (solution_row s depth) fuel in
    let s' = unfold_solution s (max_len - 1) in
    calc (==) {
      s';
      =={lemma_unfold_solution_split s (max_len - depth - 1) (depth - 1)}
      unfold_solution (solution_row s depth) (max_len - depth - 1) @|
      unfold_solution s (depth - 1);
      =={lemma_leaf_row_sum (solution_row s depth) (max_len - depth - 1)}
      row @| unfold_solution s (depth - 1);
    };
    let bottom = Leaf j depth w.[j] in
    lemma_solution_row w s (max_len - 1) depth;
    lemma_leaf_row_sum_exp_range w (solution_row s depth) fuel fuel;
    if mem bottom row then mem_index bottom row;

    lemma_filter_leaves_map sr (index_of lr sr.[i]);
    lemma_filter_leaves_mem (solution_row s depth) sr.[i];
    assert(mem sr.[i] (leaf_row s depth));

    if fuel > 0 then begin
      lemma_leaf_row_sum_last (solution_row s depth) fuel;
      lemma_mem_append 
        (leaf_row_sum (unfold_packages (solution_row s depth)) (fuel - 1))
        (leaf_row (solution_row s depth) 0);
      assert(leaf_row (solution_row s depth) 0 == leaf_row s depth);
      assert(mem sr.[i] row)
    end;
    lemma_mem_append row (unfold_solution s (depth - 1));
    assert(solution_wf max_len 1 w s (length s));
    assert(monotone_elem s' w max_len 1 (index_of s' sr.[i]))
  end

let rec lemma_max_exp_unfold_solution 
  #max_len (w: valid_weight_seq max_len) (depth: depth_t max_len) (i: nat): Lemma
  (ensures max_exp (unfold_solution (package_merge max_len w) depth) i <= depth + 1)
  (decreases depth) =
  let s = package_merge max_len w in
  match depth with
  | 0 -> lemma_leaf_row w s (max_len - 1) depth
  | _ ->
    calc (==) {
      (max_exp (unfold_solution s depth) i) <: nat;
      =={lemma_unfold_solution_leaf_row s (depth - 1)}
      max_exp ((leaf_row s depth) @| unfold_solution s (depth - 1)) i;
      =={lemma_max_exp_append (leaf_row s depth) (unfold_solution s (depth - 1)) i}
      Math.Lib.max
        (max_exp (leaf_row s depth) i)
        (max_exp (unfold_solution s (depth - 1)) i);
    };
    lemma_leaf_row w s (max_len - 1) depth;
    lemma_max_exp_unfold_solution w (depth - 1) i

let lemma_analyze_row_set_max_exp
  #nbits #max_len #w (bits: item_bit_map nbits max_len 1 w) (depth: depth_t max_len)
  i j (k: col_package_count max_len w depth i j)
  (s: intermediate_exp_seq' max_len w depth j): Lemma
  (requires (
    let sol = package_merge max_len w in
    i < length (solution_row (package_merge max_len w) depth) /\
    j + 1 == length (filter_leaves (slice (solution_row sol depth) 0 (i + 1))) /\
    j < length w /\
    (UInt.to_vec bits.[i]).[max_len - 1 - depth]))
  (ensures (
    let sol = package_merge max_len w in
    s.[j] + 1 == max_exp (unfold_solution sol depth) j
  )) =
  let sol = package_merge max_len w in
  let b: solution max_len max_len w = make_base_set max_len w in
  if depth > 0 then begin
    let sr = solution_row sol depth in
    let sr' = slice sr 0 (i + 1) in
    let us = unfold_solution sol (depth - 1) in
    lemma_filter_leaves_prefix sr' sr;
    lemma_max_exp_unfold_solution w (depth - 1) j;
    lemma_solution_row w sol (max_len - 1) depth;
    lemma_leaf_row w sol (max_len - 1) depth;
    lemma_filter_leaves_snoc_leaf (slice sr 0 i) sr.[i];
    assert((filter_leaves sr').[j] == sr.[i]);
    assert(filter_leaves sr' `prefix` filter_leaves sr);
    assert(filter_leaves sr `prefix` make_base_set (depth + 1) w);
    assert(Leaf? sr.[i] /\ sr.[i] = Leaf j (depth + 1) w.[j]);
    lemma_leaf_next_row w depth i j;
    calc (==) {
      (max_exp (unfold_solution sol depth) j) <: nat;
      =={lemma_unfold_solution_leaf_row sol (depth - 1)}
      max_exp (leaf_row sol depth @| us) j;
      =={lemma_max_exp_append (leaf_row sol depth) us j}
      Math.Lib.max (max_exp (leaf_row sol depth) j) (max_exp us j);
      =={lemma_max_exp_leaf_row w sol (max_len - 1) depth j}
      Math.Lib.max (depth + 1) (max_exp us j);
      =={}
      depth + 1;
    }
  end else
    lemma_leaf_row w sol (max_len - 1) 0

let lemma_analyze_row_set #nbits #max_len #w bits depth i j k s =
  lemma_analyze_row_set_idx bits depth i j k;
  lemma_analyze_row_set_max_exp bits depth i j k s

let lemma_analyze_row_skip #nbits #max_len #w bits depth i j k s =
  let s = package_merge max_len w in
  let row = solution_row s depth in
  let row' = slice row 0 i in
  let row'' = slice row 0 (i + 1) in
  assert(row'' `equal` snoc row' row.[i]);

  lemma_solution_row w s (max_len - 1) depth;
  lemma_filter_leaves_snoc_package row' row.[i];

  match row.[i] with
  | Package i1 i2 -> lemma_unfold_packages_snoc_package row' i1 i2;
  lemma_unfold_packages_prefix row'' row;
  assert(unfold_packages row'' `prefix` unfold_packages row);
  lemma_solution_row_cont s depth;
  lemma_solution_row w s (max_len - 1) (depth + 1)

let lemma_do_analyze #max_len #w i p =
  let depth = max_len - i in
  let s = package_merge max_len w in
  lemma_solution_row w s (max_len - 1) depth

let lemma_analyze_init_aux #max_len (w: valid_weight_seq max_len) (i: index_t w): Lemma
  (ensures max_exp (unfold_solution (package_merge max_len w) 0) i == 1) =
  let s = package_merge max_len w in
  let row = unfold_solution s 0 in
  lemma_leaf_row w s (max_len - 1) 0;
  lemma_max_exp_leaf_row w s (max_len - 1) 0 i

let lemma_analyze_init #max_len w =
  forall_intro (lemma_analyze_init_aux w)
