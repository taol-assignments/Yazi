module Spec.Package

open FStar.Seq
open FStar.Classical
open FStar.Squash

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

#push-options "--fuel 1 --ifuel 0 --query_stats --z3refresh --z3rlimit 512 --z3seed 8"
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

let lemma_snoc_leaf_solution_wf
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w true) (j: package_index_t prev false)
  (x: intermidiate_solution prev i j)
  (k: nat{k <= length x + 1}) : Lemma
  (ensures (
    let x' = snoc x (Leaf i (lo - 1) w.[i]) in
    solution_wf hi (lo - 1) (slice w 0 (i + 1)) x' k)) =
  let x' = snoc x (Leaf i (lo - 1) w.[i]) in
  let sol' = unfold_solution x' (hi - lo + 1) in
  if k = length x' then begin
    forall_intro (move_requires (lemma_snoc_leaf_monotone_elem prev i j x));
    no_dup_count_one sol';
    lemma_snoc_leaf_filter prev i j x
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

#set-options "--z3seed 111"
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

let lemma_snoc_package_solution_wf
  #hi (#lo: intermidiate_exp hi) #w (prev: solution hi lo w)
  (i: leaf_index_t w false) (j: package_index_t prev true)
  (x: intermidiate_solution prev i j)
  (k: nat{k <= length x + 1}): Lemma
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
    lemma_filter_leaves_snoc_package x p
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
