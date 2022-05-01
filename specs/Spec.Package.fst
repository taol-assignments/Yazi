module Spec.Package

open FStar.Seq
open FStar.Classical
open FStar.Squash
open Spec.Kraft

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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j): Lemma
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j): Lemma
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j)
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j): Lemma
  (requires leaf_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    merge_invariant (lo - 1) w prev (i + 1) j x')) =
  if i < length w - 1 then lemma_weight_seq_lt w i (i + 1)

let lemma_snoc_leaf #hi #lo #w prev i j x =
  let l = Leaf i (lo - 1) w.[i] in
  lemma_snoc_leaf_filter prev i j x;
  forall_intro (move_requires (lemma_snoc_leaf_solution_wf prev i j x));
  lemma_unfold_packages_snoc_leaf x l;
  lemma_weight_sorted_snoc x l;
  lemma_snoc_leaf_merge_invariant prev i j x

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
  #hi (#lo: intermidiate_exp hi) #w
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j): Lemma
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

#set-options "--z3seed 88"
let lemma_snoc_package_monotone_elem
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j)
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j)
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j): Lemma
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j)
  (k: nat{2 <= k /\ k <= length x + 1}): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    solution_wf hi (lo - 1) (slice w 0 i) x' k)) =
  let p = Package prev.[j] prev.[j + 1] in
  let x' = snoc x p in
  let sol' = unfold_solution x' (hi - lo + 1) in
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
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j): Lemma
  (requires package_smaller (lo - 1) w prev i j)
  (ensures (
    let x' = snoc x (Package prev.[j] prev.[j + 1]) in
    merge_invariant (lo - 1) w prev i (j + 2) x')) =
  let x' = snoc x (Package prev.[j] prev.[j + 1]) in
  if j + 2 < length prev - 1 then begin
    lemma_weight_sorted_lt prev j (j + 2);
    lemma_weight_sorted_lt prev (j + 1) (j + 3)
  end

let lemma_snoc_package #hi #lo #w prev i j x =
  let p = Package prev.[j] prev.[j + 1] in
  forall_intro (move_requires (lemma_snoc_package_solution_wf prev i j x));
  lemma_snoc_package_merge_invariant prev i j x;
  lemma_filter_leaves_snoc_package x p;
  lemma_weight_sorted_snoc x p;
  lemma_unfold_packages_snoc_package x prev.[j] prev.[j + 1]

let rec make_leaf_col
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w)
  (i: index_t w) (j: pos{lo <= j /\ j <= hi}):
  Tot (s: seq item{
    length s == j - lo + 1 /\
    (forall k.
      Leaf? s.[k] /\
      item_id s.[k] == i /\
      exp s.[k] == j - k /\
      item_weight s.[k] == w.[i])
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

let rec lemma_filter_leaves_len_gt (s: seq item): Lemma
  (ensures length s >= length (filter_leaves s))
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> lemma_filter_leaves_len_gt (tail s)

let lemma_solution_len_gt_two
  #hi (#lo: pos{hi >= lo}) #w (s: solution hi lo w): Lemma
  (ensures length s >= 2) =
  lemma_filter_leaves_len_gt s

let lemma_max_exp_gt_zero #hi #lo #w s id =
  let sol = unfold_solution s (hi - lo) in
  lemma_solution_len_gt_two s;
  assert(solution_wf hi lo w s (length s));
  if hi = lo then
    lemma_max_exp_gt_zero_aux sol id id hi
  else
    let offset = length (unfold_solution (unfold_packages s) (hi - lo - 1)) in
    lemma_max_exp_gt_zero_aux sol (id + offset) id lo

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
  assert(
    length x == 2 /\
    filter_leaves x == x /\
    weight_sorted x /\
    top2_leaf #(lo - 1) x w' /\
    solution_wf hi (lo - 1) w' x 2 /\
    unfold_packages x == empty #item /\
    merge_invariant (lo - 1) w prev 2 0 x)
#pop-options

let rec log2 (a: pos): Tot (e: nat{
  pow2 e >= a /\ (forall e'. pow2 e' >= a ==> e' >= e)
}) =
  match (a, a % 2) with
  | (1, _) -> 0
  | (_, 0) -> 1 + log2 (a / 2)
  | (_, 1) -> 1 + log2 (a / 2 + 1)

#push-options "--ifuel 0 --z3seed 111 --z3rlimit 1024"
let rec lemma_merge_len
  #hi (#lo: pos{lo <= hi}) #w (prev: solution hi lo w): Lemma
  (requires (
    let n = length w in
    let e = Math.Lib.max 0 ((log2 n) - (hi - lo)) in
    n <= pow2 hi /\ length prev >= 2 * n - pow2 e))
  (ensures length (package_merge prev) >= 2 * length w - 2)
  (decreases lo) =
  let n = length w in
  match lo with
  | 1 -> ()
  | _ ->
    let e = Math.Lib.max 0 ((log2 n) - (hi - lo)) in
    let e' = Math.Lib.max 0 ((log2 n) - (hi - (lo - 1))) in
    let x = cons (Leaf 0 (lo - 1) w.[0]) (create 1 (Leaf 1 (lo - 1) w.[1])) in
    lemma_init_merge_seq prev;
    let x' = merge prev 2 0 x in
    lemma_merge_len x'
#pop-options

// let lemma_solution_slice #hi #w (s: solution hi 1 w) (i: nat): Lemma
//   (requires i <= length s)
//   (ensures (
//   ))
  
// let rec lemma_merge_kraft_series #hi #w (s: solution hi 1 w): Lemma
//   (ensures (
//     let s' = slice s 0 (2 * length w - 2) in
//     kraft_sum (solution_len s) =$ one)) =
//   admit()
