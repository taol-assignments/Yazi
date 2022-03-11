module Spec.Tree.Lemmas

module Math = FStar.Math.Lemmas

open FStar.Classical
open FStar.Mul
open FStar.Squash

let lemma_subtraction_cancel (a b c: int): Lemma
  (requires b = a - c)
  (ensures b + c == a) = ()

#set-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0"
let lemma_heap_seq (ts: heap_elems_wf_ts) (i: heap_index ts): Lemma
  (requires i <= ts.heap_len)
  (ensures
    (element_seq ts).[i - 1] == ts.heap.[i] /\
    (heap_seq ts).[i - 1] == ts.heap.[i]) =
  let es = element_seq ts in
  let i' = i - 1 in
  assert(forall (j: nat). {:pattern es.[j]} j < ts.heap_len ==>
    ts.heap.[j + 1] == es.[j]);
  assert(es.[i'] == ts.heap.[i' + 1]);
  lemma_subtraction_cancel i i' 1

let lemma_sorted_seq (ts: heap_elems_wf_ts) (i: heap_index ts): Lemma
  (requires i >= ts.heap_max /\ heap_not_empty ts)
  (ensures
    (element_seq ts).[i - (ts.heap_max - ts.heap_len)] == ts.heap.[i] /\
    (sorted_seq ts).[i - ts.heap_max] == ts.heap.[i]) =
  let es = element_seq ts in
  let i' = i - (ts.heap_max - ts.heap_len) in
  assert(forall j. {:pattern es.[j]} j >= ts.heap_len ==>
    ts.heap.[j - ts.heap_len + ts.heap_max] == es.[j]);
  assert(es.[i'] == ts.heap.[i' + (ts.heap_max - ts.heap_len)]);
  lemma_subtraction_cancel i i' (ts.heap_max - ts.heap_len)

let lemma_pqremove_index
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (ensures (
    let ts' = pqremove ts in
    (mem ts'.heap.[i] (element_seq ts')) /\
    ((exists j. (heap_seq ts).[j] == ts'.heap.[i]) \/
    (exists j. (sorted_seq ts).[j] == ts'.heap.[i])))) =
  let ts' = pqremove ts in
  let es' = element_seq ts' in
  if i <= ts'.heap_len then
    lemma_heap_seq ts' i
  else
    lemma_sorted_seq ts' i;
  assert(mem ts'.heap.[i] es');
  assert(mem ts'.heap.[i] (element_seq ts));
  lemma_mem_append (heap_seq ts) (sorted_seq ts);
  if mem ts'.heap.[i] (heap_seq ts) then
    mem_index ts'.heap.[i] (heap_seq ts)
  else
    mem_index ts'.heap.[i] (sorted_seq ts)

#push-options "--z3seed 14 --z3rlimit 1024 --fuel 0 --ifuel 0"
let lemma_pqremove_heap_index
  (ts: heap_wf_ts{ts.heap_len > 1}) (i: heap_index (pqremove ts)): Lemma
  (requires no_dup (element_seq ts))
  (ensures (
    let ts' = pqremove ts in
    (1 <= i /\ i < ts.heap_len ==> (exists (j: nat{1 <= j /\ j <= ts.heap_len}).
      ts.heap.[j] == ts'.heap.[i])) /\
    (i == ts'.heap_max ==> ts.heap.[1] == ts'.heap.[i]) /\
    (i > ts'.heap_max ==> ts.heap.[i] == ts'.heap.[i]))) =
  let ts' = pqremove ts in
  if i > ts'.heap_max then
    calc (==) {
      ts.heap.[i];
      =={}
      ts.heap.[i - ts.heap_max + ts.heap_max];
      =={}
      (sorted_seq ts).[i - ts.heap_max];
      =={}
      (sorted_seq ts').[i + 1 - ts.heap_max];
      =={}
      (sorted_seq ts').[i - (ts.heap_max - 1)];
      =={}
      (sorted_seq ts').[i - ts'.heap_max];
      =={}
      ts'.heap.[i - ts'.heap_max + ts'.heap_max];
      =={lemma_subtraction_cancel i (i - ts'.heap_max) ts'.heap_max}
      ts'.heap.[i];
    }
  else if i = ts'.heap_max then
    assert((sorted_seq ts').[0] == ts'.heap.[ts'.heap_max])
  else begin
    let hs = heap_seq ts in
    let hs' = heap_seq ts' in
    let es' = element_seq ts' in
    no_dup_alt es' (i - 1) ts'.heap_len;
    calc (==) {
      count ts'.heap.[i] hs;
      =={}
      count ts'.heap.[i] (cons ts'.heap.[ts'.heap_max] hs');
      =={lemma_append_count_aux ts'.heap.[i] (create 1 ts'.heap.[ts'.heap_max]) hs'}
      count ts'.heap.[i] (create 1 ts'.heap.[ts'.heap_max]) +
      count ts'.heap.[i] hs';
      ={}
      count ts'.heap.[i - 1 + 1] (create 1 ts'.heap.[ts'.heap_max]) +
      count ts'.heap.[i - 1 + 1] hs';
      =={}
      count hs'.[i - 1] (create 1 ts'.heap.[ts'.heap_max]) +
      count hs'.[i - 1] hs';
      =={
        calc (==) {
          ts'.heap.[ts'.heap_max];
          =={}
          ts'.heap.[ts'.heap_max - ts'.heap_max + ts'.heap_max];
          =={}
          (sorted_seq ts').[ts'.heap_max - ts'.heap_max];
          =={}
          (sorted_seq ts').[0];
          =={}
          ts.heap.[1];
        }
      }
      count hs'.[i - 1] (create 1 ts.heap.[1]) +
      count hs'.[i - 1] hs';
      =={count_create 1 ts.heap.[1] hs'.[i - 1]}
      count hs'.[i - 1] hs';
      =={}
      1;
    };

    mem_index ts'.heap.[i] hs
  end

let lemma_pqremove_heap_index_rev
  (ts: forest_wf_ts{ts.heap_len > 1}) (i: heap_index ts): Lemma
  (ensures (
    let ts' = pqremove ts in
    1 < i /\ i <= ts.heap_len ==> (exists (j: nat{1 <= j /\ j <= ts'.heap_len}).
      ts.heap.[i] == ts'.heap.[j]))) =
  let ts' = pqremove ts in
  let hs = heap_seq ts in
  let hs' = heap_seq ts' in
  let es' = element_seq ts' in
  if 1 < i && i <= ts.heap_len then begin
    no_dup_alt hs 0 (i - 1);
    lemma_heap_seq ts i;
    lemma_pqremove_heap_index ts ts'.heap_max;
    count_create 1 ts'.heap.[ts'.heap_max] ts.heap.[i];
    calc (==) {
      1;
      =={}
      count ts.heap.[i] hs;
      =={}
      count ts.heap.[i] (intermediate_fseq ts');
      =={lemma_append_count_aux ts.heap.[i] (create 1 ts'.heap.[ts'.heap_max]) hs'}
      count ts.heap.[i] (create 1 ts'.heap.[ts'.heap_max]) +
      count ts.heap.[i] hs';
      =={}
      count ts.heap.[i] hs';
    };
    mem_index ts.heap.[i] hs'
  end
#pop-options

#set-options "--z3refresh --z3rlimit 1024 --fuel 0 --ifuel 0"
let lemma_pqremove_parent_corr
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (requires (pqremove ts).heap_max < i)
  (ensures parent_corr (pqremove ts) i) =
  let ts' = pqremove ts in
  let i' = U32.v ts.heap.[i] in
  let dad = U16.v (ts.tree.[i']).dad_or_len in
  assert(parent_corr ts i);
  exists_elim
    (parent_corr ts' i)
    (get_proof (exists (j: heap_index ts{j < i}). dad == U32.v ts.heap.[j]))
    (fun j ->
      lemma_pqremove_heap_index ts i;
      if j = 1 then
        lemma_pqremove_heap_index ts ts'.heap_max
      else if ts.heap_max <= j then
        lemma_pqremove_heap_index ts j
      else
        lemma_pqremove_heap_index_rev ts j)

#push-options "--fuel 1 --ifuel 1"
let rec lemma_forest_symbols_append
  (ts: heap_elems_wf_ts) (s0 s1: tree_id_seq ts): Lemma
  (ensures forest_symbols ts s0 @| forest_symbols ts s1 == forest_symbols ts (s0 @| s1))
  (decreases length s0) =
  match length s0 with
  | 0 ->
    calc (==) {
      forest_symbols ts s0 @| forest_symbols ts s1;
      =={}
      empty #nat @| forest_symbols ts s1;
      =={append_empty_l (forest_symbols ts s1)}
      forest_symbols ts s1;
      =={
        lemma_empty s0;
        append_empty_l s1
      }
      forest_symbols ts (s0 @| s1);
    }
  | _ ->
    calc (==) {
      forest_symbols ts s0 @| forest_symbols ts s1;
      =={}
      (symbols ts.forest.[U32.v s0.[0]] @| forest_symbols ts (tail s0)) @|
      forest_symbols ts s1;
      =={
        append_assoc
          (symbols ts.forest.[U32.v s0.[0]])
          (forest_symbols ts (tail s0))
          (forest_symbols ts s1)
      }
      symbols ts.forest.[U32.v s0.[0]] @|
      (forest_symbols ts (tail s0) @| forest_symbols ts s1);
      =={lemma_forest_symbols_append ts (tail s0) s1}
      symbols ts.forest.[U32.v s0.[0]] @| forest_symbols ts ((tail s0) @| s1);
      =={assert(((tail s0) @| s1) `equal` (tail (s0 @| s1)))}
      symbols ts.forest.[U32.v s0.[0]] @| forest_symbols ts (tail (s0 @| s1));
      =={}
      forest_symbols ts (s0 @| s1);
    }

#push-options "--fuel 0 --ifuel 0"
let lemma_forest_symbols_middle
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s) (n: nat): Lemma
  (ensures
    count n (forest_symbols ts (slice s 0 i)) +
    count n (forest_symbols ts (create 1 s.[i])) +
    count n (forest_symbols ts (slice s (i + 1) (length s))) =
    count n (forest_symbols ts s)) =
  calc (==) {
    count n (forest_symbols ts s);
    =={slice_middle s i}
    count n (forest_symbols ts (
      slice s 0 i @|
      create 1 s.[i] @|
      slice s (i + 1) (length s)));
    =={append_assoc (slice s 0 i) (create 1 s.[i]) (slice s (i + 1) (length s))}
    count n (forest_symbols ts ((
      slice s 0 i @|
      create 1 s.[i]) @|
      slice s (i + 1) (length s)));
    =={
      lemma_forest_symbols_append ts
        (slice s 0 i @| create 1 s.[i])
        (slice s (i + 1) (length s))
    }
    count n (
      (forest_symbols ts (slice s 0 i @| create 1 s.[i])) @|
      (forest_symbols ts (slice s (i + 1) (length s))));
    =={lemma_forest_symbols_append ts (slice s 0 i) (create 1 s.[i])}
    count n (
      ((forest_symbols ts (slice s 0 i)) @|
      (forest_symbols ts (create 1 s.[i]))) @|
      (forest_symbols ts (slice s (i + 1) (length s))));
    =={
      lemma_append_count_aux n
        (forest_symbols ts (slice s 0 i) @| forest_symbols ts (create 1 s.[i]))
        (forest_symbols ts (slice s (i + 1) (length s)))
    }
    count n (forest_symbols ts (slice s 0 i) @| forest_symbols ts (create 1 s.[i])) +
    count n (forest_symbols ts (slice s (i + 1) (length s)));
    =={
      lemma_append_count_aux n
        (forest_symbols ts (slice s 0 i))
        (forest_symbols ts (create 1 s.[i]))
    }
    count n (forest_symbols ts (slice s 0 i)) +
    count n (forest_symbols ts (create 1 s.[i])) +
    count n (forest_symbols ts (slice s (i + 1) (length s)));
  }
#pop-options
  
#push-options "--fuel 2 --ifuel 2"
let lemma_forest_symbols_single
  (ts: heap_elems_wf_ts) (s: U32.t{is_tree_index ts s}): Lemma
  (ensures symbols ts.forest.[U32.v s] == forest_symbols ts (create 1 s)) = ()
#pop-options

#push-options "--z3seed 1 --fuel 1 --ifuel 0"
let rec lemma_forest_symbols_perm_aux
  (ts0: heap_elems_wf_ts) (s0: tree_id_seq ts0)
  (ts1: heap_elems_wf_ts) (s1: tree_id_seq ts1)
  (s: nat): Lemma
  (requires ts0.forest == ts1.forest /\ permutation U32.t s0 s1)
  (ensures count s (forest_symbols ts0 s0) == count s (forest_symbols ts1 s1))
  (decreases length s0) =
  match length s0 with
  | 0 -> ()
  | _ ->
    let i = index_of s1 s0.[0] in
    let hd0 = symbols ts0.forest.[U32.v s0.[0]] in
    let hd1 = symbols ts1.forest.[U32.v s1.[i]] in
    let s1' = slice s1 0 i @| slice s1 (i + 1) (length s1) in
    perm_len s0 s1;
    calc (==) {
      count s (forest_symbols ts0 s0);
      =={}
      count s (hd1 @| forest_symbols ts0 (tail s0));
      =={lemma_append_count_aux s hd1 (forest_symbols ts0 (tail s0))}
      count s hd1 + count s (forest_symbols ts0 (tail s0));
      =={
        permutation_middle s0 s1;
        lemma_forest_symbols_perm_aux ts0 (tail s0) ts1 s1' s
      }
      count s hd1 + count s (forest_symbols ts1 s1');
      =={
        lemma_forest_symbols_append ts1
          (slice s1 0 i)
          (slice s1 (i + 1) (length s1))
      }
      count s hd1 +
      count s (
        forest_symbols ts1 (slice s1 0 i) @|
        forest_symbols ts1 (slice s1 (i + 1) (length s1)));
      =={
        lemma_append_count_aux s
          (forest_symbols ts1 (slice s1 0 i))
          (forest_symbols ts1 (slice s1 (i + 1) (length s1)))
      }
      count s (forest_symbols ts1 (slice s1 0 i)) +
      count s hd1 +
      count s (forest_symbols ts1 (slice s1 (i + 1) (length s1)));
      =={lemma_forest_symbols_single ts1 s1.[i]}
      count s (forest_symbols ts1 (slice s1 0 i)) +
      count s (forest_symbols ts1 (create 1 s1.[i])) +
      count s (forest_symbols ts1 (slice s1 (i + 1) (length s1)));
      =={lemma_forest_symbols_middle ts1 s1 i s}
      count s (forest_symbols ts1 s1);
    }

let lemma_forest_symbols_perm ts0 s0 ts1 s1 =
  forall_intro (move_requires (lemma_forest_symbols_perm_aux ts0 s0 ts1 s1))
#pop-options

let lemma_is_max_id_map ts node i =
  let es = element_seq ts in
  if i <= ts.heap_len then
    lemma_heap_seq ts i
  else
    lemma_sorted_seq ts i;
  mem_index ts.heap.[i] es

#push-options "--fuel 2 --ifuel 2"
let lemma_wf_tree_id_unfold (t: wf_tree): Lemma
  (requires Node? t == true)
  (ensures id (left t) < id t /\ id (right t) < id t) = ()
#pop-options

#push-options "--z3seed 14 --fuel 0 --ifuel 0"
let lemma_pqremove_sorted_inv (ts: heap_wf_ts) (i j: heap_index ts): Lemma
  (requires 
    ts.heap_len > 1 /\ (
    let ts' = pqremove ts in
    j >= ts.heap_max /\
    no_dup (element_seq ts) /\
    ts'.heap.[j] == ts.heap.[i]))
  (ensures i == j) =
  let ts' = pqremove ts in
  let es = element_seq ts in
  let es' = element_seq ts' in
  let j' = j - (ts.heap_max - ts.heap_len) in 
  calc (==) {
    ts.heap.[i];
    =={}
    ts'.heap.[j];
    =={lemma_sorted_seq ts' j}
    es'.[j - (ts'.heap_max - ts'.heap_len)];
    =={}
    es.[j - (ts'.heap_max - ts'.heap_len)];
    =={}
    es.[j'];
  };
  if i <> j then
    if i >= ts.heap_max then begin
      let i' = i - (ts.heap_max - ts.heap_len) in 
      lemma_sorted_seq ts i;
      no_dup_index_of es i' es.[j'];
      no_dup_index_of es j' es.[j']
    end else begin
      let i' = i - 1 in 
      lemma_heap_seq ts i;
      no_dup_index_of es i' es.[j'];
      no_dup_index_of es j' es.[j']
    end

let lemma_pqremove_child_corr
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (ensures child_corr (pqremove ts) i) =
  let ts' = pqremove ts in
  let i' = U32.v ts'.heap.[i] in
  let t = ts'.forest.[i'] in
  lemma_pqremove_heap_index ts i;
  if Node? t then begin
    lemma_wf_tree_id_unfold t;
    exists_elim
      (child_corr ts' i)
      (get_proof (exists (j: heap_index ts).
        ts.heap.[j] == ts'.heap.[i] /\ child_corr ts j))
      (fun j -> exists_elim
        (child_in_sorted ts' i)
        (get_proof (child_in_sorted ts j))
        (fun k ->
          lemma_pqremove_heap_index ts k;
          lemma_pqremove_heap_index ts (k + 1);
          if i > ts'.heap_max then
            lemma_pqremove_sorted_inv ts j i))
  end
#pop-options

#push-options "--z3seed 1"
let lemma_pqremove_heap_seq_index
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: index_t (element_seq ts)): Lemma
  (requires 0 < i /\ i < ts.heap_len)
  (ensures (
    let ts' = pqremove ts in
    index_of (element_seq ts') (element_seq ts).[i] < ts'.heap_len)) =
  let ts' = pqremove ts in
  let es = element_seq ts in
  let es' = element_seq ts' in
  if index_of es' es.[i] = ts'.heap_len then
    no_dup_alt es i 0
  else if ts'.heap_len < index_of es' es.[i] then
    calc (==) {
      count es.[i] es';
      =={
        calc (==) {
          es';
          =={}
          heap_seq ts' @| sorted_seq ts';
          =={assert(equal (cons es.[0] (sorted_seq ts)) (sorted_seq ts'))}
          heap_seq ts' @| cons es.[0] (sorted_seq ts);
          =={}
          heap_seq ts' @| (create 1 es.[0] @| sorted_seq ts);
          =={append_assoc (heap_seq ts') (create 1 es.[0]) (sorted_seq ts)}
          (heap_seq ts' @| create 1 es.[0]) @| sorted_seq ts;
        }
      }
      count es.[i] ((heap_seq ts' @| create 1 es.[0]) @| sorted_seq ts);
      =={lemma_append_count_aux es.[i] (heap_seq ts' @| create 1 es.[0]) (sorted_seq ts)}
      count es.[i] (heap_seq ts' @| create 1 es.[0]) + count es.[i] (sorted_seq ts);
      =={lemma_append_count_aux es.[i] (heap_seq ts) (sorted_seq ts)}
      count es.[i] (heap_seq ts) + count es.[i] (sorted_seq ts);
    }
  else
    assert(index_of es' es.[i] < ts'.heap_len)
#pop-options

#push-options "--z3seed 8 --fuel 0 --ifuel 0"
let lemma_pqremove_forest'
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (ensures (
    let ts' = pqremove ts in
    freq_corr ts' i /\
    id ts'.forest.[U32.v ts'.heap.[i]] == U32.v ts'.heap.[i] /\
    (ts'.heap_max == i ==> child_corr ts' i) /\
    (ts'.heap_max <> i ==> tree_corr ts' i))) =
  lemma_pqremove_index ts i;
  lemma_pqremove_child_corr ts i;
  let ts' = pqremove ts in
  let es = element_seq ts in
  let es' = element_seq ts' in
  let j = index_of es ts'.heap.[i] in
  let dad = Cast.uint16_to_uint32 (ts'.tree.[U32.v ts'.heap.[i]]).dad_or_len in
  assert(exists (j: heap_index ts). ts.heap.[j] == ts'.heap.[i] /\ freq_corr ts j);
  assert(child_corr ts' i);
  assert(id ts'.forest.[U32.v ts'.heap.[i]] == U32.v ts'.heap.[i]);
  if ts'.heap_max < i then
    lemma_pqremove_parent_corr ts i
#pop-options

let lemma_pqremove_id'
  (ts: forest_wf_ts{ts.heap_len > 1})
  (node: nat{is_max_id ts node})
  (i: index_t (element_seq ts)): Lemma
  (ensures id (pqremove ts).forest.[U32.v (element_seq (pqremove ts)).[i]] < node) =
  let ts' = pqremove ts in
  let (es, es') = (element_seq ts, element_seq ts') in
  count_index es';
  mem_index es'.[i] es

#push-options "--z3seed 6 --fuel 0 --ifuel 0"
let lemma_pqremove_id
  (ts: forest_wf_ts{ts.heap_len > 1}) (node: nat{is_max_id ts node}): Lemma
  (ensures is_max_id (pqremove ts) node) =
  FStar.Classical.forall_intro (lemma_pqremove_id' ts node);
  perm_len (element_seq ts) (element_seq (pqremove ts))
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_forest_freq_unsnoc (ts: heap_elems_wf_ts) (s: tree_id_seq ts): Lemma
  (requires length s > 0)
  (ensures
    forest_freq ts s ==
    forest_freq ts (unsnoc s) + freq ts.forest.[U32.v (last s)])
  (decreases length s) =
  match length s with
  | 1 -> ()
  | _ ->
    assert(cons s.[0] (unsnoc (tail s)) `equal` unsnoc s);
    lemma_forest_freq_unsnoc ts (tail s)

let rec lemma_forest_freq_middle
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s): Lemma
  (requires length s > 0)
  (ensures forest_freq ts s ==
    forest_freq ts (slice s 0 i) +
    freq ts.forest.[U32.v s.[i]] +
    forest_freq ts (slice s (i + 1) (length s)))
  (decreases i) =
  if i > 0 then lemma_forest_freq_middle ts (tail s) (i - 1)

let rec lemma_forest_freq_append
  (ts: heap_elems_wf_ts) (s0 s1: tree_id_seq ts): Lemma
  (ensures forest_freq ts s0 + forest_freq ts s1 == forest_freq ts (s0 @| s1))
  (decreases length s0) =
  match length s0 with
  | 0 ->
    calc (==) {
      forest_freq ts s0 + forest_freq ts s1;
      =={}
      forest_freq ts s1;
      =={
        lemma_empty s0;
        append_empty_l s1
     }
     forest_freq ts (s0 @| s1);
    }
  | _ ->
    calc (==) {
      forest_freq ts s0 + forest_freq ts s1;
      =={}
      freq ts.forest.[U32.v s0.[0]] + (forest_freq ts (tail s0) + forest_freq ts s1);
      =={lemma_forest_freq_append ts (tail s0) s1}
      freq ts.forest.[U32.v s0.[0]] + forest_freq ts ((tail s0) @| s1);
      =={assert(((tail s0) @| s1) `equal` tail (s0 @| s1))}
      freq ts.forest.[U32.v s0.[0]] + forest_freq ts (tail (s0 @| s1));
      =={}
      forest_freq ts (s0 @| s1);
    }

let rec lemma_forest_freq_perm ts0 s0 ts1 s1 =
  perm_len s0 s1;
  if length s0 > 0 then
    let i = index_of s1 s0.[0] in
    calc (==) {
      forest_freq ts0 s0;
      =={}
      freq ts1.forest.[U32.v s1.[i]] + forest_freq ts0 (tail s0);
      =={
        permutation_middle s0 s1;
        lemma_forest_freq_perm
          ts0 (tail s0)
          ts1 (slice s1 0 i @| slice s1 (i + 1) (length s1))
      }
      freq ts1.forest.[U32.v s1.[i]] +
      forest_freq ts1 (slice s1 0 i @| slice s1 (i + 1) (length s1));
      =={lemma_forest_freq_append ts1 (slice s1 0 i) (slice s1 (i + 1) (length s1))}
      freq ts1.forest.[U32.v s1.[i]] +
      forest_freq ts1 (slice s1 0 i) +
      forest_freq ts1 (slice s1 (i + 1) (length s1));
      =={lemma_forest_freq_middle ts1 s1 i}
      forest_freq ts1 s1;
    }
#pop-options

#push-options "--fuel 1 --ifuel 1"
let lemma_pqremove_heap_dad_zero (ts: forest_wf_ts{1 < ts.heap_len}) (node: nat) (i: nat{
  1 <= i /\ i <= (pqremove ts).heap_len
}): Lemma
  (requires forall j. 1 <= j /\ j <= ts.heap_len ==>
    U16.v (ts.tree.[U32.v ts.heap.[j]]).dad_or_len == 0)
  (ensures (
    let ts' = pqremove ts in
    U16.v (ts'.tree.[U32.v ts'.heap.[i]]).dad_or_len == 0)) =
  let ts' = pqremove ts in
  let hs' = heap_seq ts' in
  let es' = element_seq ts' in
  let ifs' = intermediate_fseq ts' in
  let i' = ts'.heap.[i] in
  lemma_heap_seq ts' i;
  lemma_sorted_seq ts' ts'.heap_max;
  no_dup_alt es' (i - 1) ts'.heap_len;
  calc (==) {
    count i' (heap_seq ts);
    =={}
    count i' ifs';
    =={lemma_append_count_aux i' (create 1 ts'.heap.[ts'.heap_max]) hs'}
    count i' (create 1 ts'.heap.[ts'.heap_max]) + count i' hs';
    =={
      count_create 1 ts'.heap.[ts'.heap_max] i'
    }
    count i' hs';
  };
  mem_index i' (heap_seq ts)

let lemma_pqremove_max_dad_zero (ts: forest_wf_ts{1 < ts.heap_len}) (node: nat): Lemma
  (requires forall j. 1 <= j /\ j <= ts.heap_len ==>
    U16.v (ts.tree.[U32.v ts.heap.[j]]).dad_or_len == 0)
  (ensures (
    let ts' = pqremove ts in
    U16.v (ts'.tree.[U32.v ts'.heap.[ts'.heap_max]]).dad_or_len == 0)) =
  let ts' = pqremove ts in
  lemma_sorted_seq ts' ts'.heap_max;
  assert(ts'.heap.[ts'.heap_max] == ts.heap.[1])
#pop-options

#push-options "--fuel 0 --ifuel 0"
let lemma_pqremove_forest ts node =
  let ts' = pqremove ts in
  let s = intermediate_fseq ts' in
  let open FStar.Classical in
  lemma_pqremove_id ts node;
  lemma_pqremove_max_dad_zero ts node;
  forall_intro (move_requires (lemma_pqremove_heap_dad_zero ts node));
  forall_intro (lemma_pqremove_forest' ts);

  lemma_heap_seq_tree_index ts;
  lemma_intermediate_fseq_tree_index ts';

  lemma_forest_symbols_perm ts (heap_seq ts) ts' s;
  lemma_forest_freq_perm ts (heap_seq ts) ts' s
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_forest_freq_plus_aux
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i j: index_t s): Lemma
  (requires
    i <> j /\
    length s > 1 /\
    heap_not_empty ts /\
    (forall k. freq_corr ts k) /\
    (forall k. mem s.[k] (element_seq ts)))
  (ensures
    U16.v (ts.tree.[U32.v s.[i]]).freq_or_code +
    U16.v (ts.tree.[U32.v s.[j]]).freq_or_code <=
    forest_freq ts s)
  (decreases i) =
  let min = if i < j then i else j in
  let max = if i < j then j else i in
  let fi = U16.v (ts.tree.[U32.v s.[i]]).freq_or_code in
  let fj = U16.v (ts.tree.[U32.v s.[j]]).freq_or_code in
  let m1 = U16.v (ts.tree.[U32.v s.[min]]).freq_or_code in
  let m2 = U16.v (ts.tree.[U32.v s.[max]]).freq_or_code in
  match min with
  | 0 ->
    calc (<=) {
      fi + fj;
      =={}
      m1 + m2;
      <={}
      m1 + forest_freq ts (slice (tail s) 0 (max - 1)) +
      m2 + forest_freq ts (slice (tail s) max (length (tail s)));
      =={
        mem_index (tail s).[max - 1] (element_seq ts);
        assert(exists (j: heap_index ts). ts.heap.[j] == s.[max])
      }
      m1 +
      (forest_freq ts (slice (tail s) 0 (max - 1)) +
      freq ts.forest.[U32.v (tail s).[max - 1]] +
      forest_freq ts (slice (tail s) max (length (tail s))));
      =={lemma_forest_freq_middle ts (tail s) (max - 1)}
      m1 + forest_freq ts (tail s);
      =={
        mem_index s.[0] (element_seq ts);
        assert(exists (j: heap_index ts). ts.heap.[j] == s.[min])
      }
      forest_freq ts s;
    }
  | _ -> lemma_forest_freq_plus_aux ts (tail s) (i - 1) (j - 1)
#pop-options

let lemma_forest_freq_plus ts i j =
  let es = element_seq ts in
  let s = cons ts.heap.[ts.heap_max] (heap_seq ts) in
  assert(s.[0] == es.[ts.heap_len]);
  assert(forall k. {:pattern s.[k]} k > 0 ==> s.[k] == es.[k - 1]);
  assert(forall k. mem s.[k] (element_seq ts));
  lemma_forest_freq_plus_aux ts s i j

let rec fs_begin (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s):
  Tot nat (decreases i) =
  match i with
  | 0 -> 0
  | _ ->
    length (symbols ts.forest.[U32.v s.[0]]) + fs_begin ts (tail s) (i - 1)

let rec fs_end (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s):
  Tot (res: nat{res <= length (forest_symbols ts s)}) (decreases i) =
  match i with
  | 0 -> length (symbols ts.forest.[U32.v s.[0]])
  | _ -> length (symbols ts.forest.[U32.v s.[0]]) + fs_end ts (tail s) (i - 1)

#push-options "--fuel 1 --ifuel 1"
let rec lemma_symbols_length_gt_zero (t: tree): Lemma
  (ensures length (symbols t) > 0)
  [SMTPat (length (symbols t))] =
  match t with
  | Node l _ _ r ->
    lemma_symbols_length_gt_zero l;
    lemma_symbols_length_gt_zero r
  | Leaf s _ -> ()

let rec lemma_fs_begin_lt_end_1
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s): Lemma
  (ensures fs_begin ts s i < fs_end ts s i)
  (decreases i)
  [SMTPat (fs_begin ts s i); SMTPat (fs_end ts s i)] =
  match i with
  | 0 -> ()
  | _ -> lemma_fs_begin_lt_end_1 ts (tail s) (i - 1)

let rec lemma_fs_begin_lt_end_2
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i j: index_t s): Lemma
  (requires i < j)
  (ensures fs_end ts s i <= fs_begin ts s j)
  (decreases i)
  [SMTPat (fs_end ts s i); SMTPat (fs_begin ts s j)] =
  match i with
  | 0 -> ()
  | _ -> lemma_fs_begin_lt_end_2 ts (tail s) (i - 1) (j - 1)

let rec lemma_fs_begin_ascending
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i j: index_t s): Lemma
  (requires i < j)
  (ensures fs_begin ts s i < fs_begin ts s j)
  (decreases i)
  [SMTPat (fs_begin ts s i); SMTPat (fs_begin ts s j)] =
  match i with
  | 0 -> ()
  | _ -> lemma_fs_begin_ascending ts (tail s) (i - 1) (j - 1)

let rec lemma_fs_end_ascending
  (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i j: index_t s): Lemma
  (requires i < j)
  (ensures fs_end ts s i < fs_end ts s j)
  (decreases i)
  [SMTPat (fs_end ts s i); SMTPat (fs_end ts s j)] =
  match i with
  | 0 ->
    calc (<) {
      0;
      <{}
      length (symbols ts.forest.[U32.v s.[0]]);
      =={}
      fs_end ts s i;
      <{}
      length (symbols ts.forest.[U32.v s.[0]]) + fs_end ts (tail s) (j - 1);
    }
  | _ -> lemma_fs_end_ascending ts (tail s) (i - 1) (j - 1)

let rec lemma_fs_slice (ts: heap_elems_wf_ts) (s: tree_id_seq ts) (i: index_t s): Lemma
  (ensures
    slice (forest_symbols ts s) (fs_begin ts s i) (fs_end ts s i) ==
    symbols ts.forest.[U32.v s.[i]])
  (decreases i) =
  let a = slice (forest_symbols ts s) (fs_begin ts s i) (fs_end ts s i) in
  let a' = symbols ts.forest.[U32.v s.[i]] in
  match i with
  | 0 -> assert(a `equal` a')
  | _ ->
    let hd = symbols ts.forest.[U32.v s.[0]] in
    calc (==) {
      slice (forest_symbols ts s) (fs_begin ts s i) (fs_end ts s i);
      =={}
      slice
        (hd @| forest_symbols ts (tail s))
        (length hd + fs_begin ts (tail s) (i - 1))
        (length hd + fs_end ts (tail s) (i - 1));
      =={append_slices hd (forest_symbols ts (tail s))}
      slice
        (forest_symbols ts (tail s))
        (fs_begin ts (tail s) (i - 1))
        (fs_end ts (tail s) (i - 1));
      =={lemma_fs_slice ts (tail s) (i - 1)}
      symbols ts.forest.[U32.v (tail s).[i - 1]];
      =={}
      symbols ts.forest.[U32.v s.[i]];
    }

#push-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let lemma_pqmerge_disjoint' (ts: heap_elems_wf_ts) (i j: pos): Lemma
  (requires
    pqmerge_no_dup_pre ts i j /\
    ((i < j /\ j <> ts.heap_max) \/ i == ts.heap_max))
  (ensures (
    let i' = U32.v ts.heap.[i] in
    let j' = U32.v ts.heap.[j] in
    no_dup (symbols ts.forest.[i']) /\
    no_dup (symbols ts.forest.[j']) /\
    disjoint (symbols ts.forest.[i']) (symbols ts.forest.[j'])
  )) =
  let cs = cons ts.heap.[ts.heap_max] (heap_seq ts) in
  let ci = if i = ts.heap_max then 0 else i in
  let cj = if j = ts.heap_max then 0 else j in
  let fs = forest_symbols ts cs in
  let bi = fs_begin ts cs ci in let ei = fs_end ts cs ci in
  let bj = fs_begin ts cs cj in let ej = fs_end ts cs cj in
  let fs' = slice fs bi ej in
  lemma_fs_slice ts cs ci;
  lemma_fs_slice ts cs cj;
  no_dup_slice fs bi ej;
  no_dup_slice fs' (ei - bi) (bj - bi)

let lemma_pqmerge_no_dup ts i j =
  if i < j && j <> ts.heap_max || i = ts.heap_max then
    lemma_pqmerge_disjoint' ts i j
  else
    lemma_pqmerge_disjoint' ts j i

let lemma_pqmerge_heap_wf
  (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf) (t': wf_tree): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures heap_elems_wf ts') = ()

let lemma_pqmerge_smaller_heap
  (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf) (t': wf_tree)
  (i j: pos): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    2 <= i /\ 2 <= j /\ i <= ts'.heap_len /\ j <= ts'.heap_len)
  (ensures (
    lemma_pqmerge_heap_wf ts node ts' t';
    smaller ts' ts'.heap.[i] ts'.heap.[j] ==
    smaller ts ts.heap.[i] ts.heap.[j])) =
  let es = element_seq ts in
  assert(forall i. id ts.forest.[U32.v es.[i]] == U32.v es.[i]);
  assert(forall i. 2 <= i /\ i <= ts.heap_len ==>
    es.[i - 1] == ts.heap.[i] /\ ts'.heap.[i] == ts.heap.[i]);
  assert(forall i. 2 <= i /\ i <= ts'.heap_len ==> U32.v ts'.heap.[i] < node);
  assert(forall i. i <> node ==> (ts'.tree.[i]).freq_or_code == (ts.tree.[i]).freq_or_code)

let lemma_pqmerge_smaller_sorted
  (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf) (t': wf_tree)
  (i j: pos): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    ts'.heap_max < i /\ ts'.heap_max < j /\
    i < U32.v heap_size /\ j < U32.v heap_size)
  (ensures (
    lemma_pqmerge_heap_wf ts node ts' t';
    smaller ts' ts'.heap.[i] ts'.heap.[j] ==
    smaller ts ts.heap.[i] ts.heap.[j])) =
  let es = element_seq ts in
  assert(forall i. id ts.forest.[U32.v es.[i]] == U32.v es.[i]);
  assert(forall i. ts.heap_max <= i /\ i <= U32.v heap_size ==>
    es.[i - ts.heap_max + ts.heap_len] == ts.heap.[i] /\ ts'.heap.[i] == ts.heap.[i]);
  assert(forall i. ts.heap_max <= i /\ i <= U32.v heap_size ==> U32.v ts'.heap.[i] < node);
  assert(forall i. i <> node ==> (ts'.tree.[i]).freq_or_code == (ts.tree.[i]).freq_or_code)

#push-options "--fuel 1 --ifuel 1"
let rec lemma_pqmerge_heap_sorted_aux
  (ts: heap_wf_ts) (node: nat) (ts': tree_state_wf) (t': wf_tree) (i: nat): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    ts.heap_max <= i /\ i <= U32.v heap_size)
  (ensures heap_sorted' ts i)
  (decreases i - ts.heap_max) =
  if ts.heap_max < i then lemma_pqmerge_heap_sorted_aux ts node ts' t' (i - 1)

let rec lemma_pqmerge_heap_sorted
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree) (i: nat): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    ts'.heap_max <= i /\ i <= U32.v heap_size)
  (ensures heap_sorted' ts' i)
  (decreases U32.v heap_size - i) = 
  if U32.v heap_size - i <= 1 then
    ()
  else if ts'.heap_max < i then begin
    lemma_pqmerge_heap_sorted_aux ts node ts' t' i;
    lemma_pqmerge_heap_sorted ts node ts' t' (i + 1);
    lemma_pqmerge_smaller_sorted ts node ts' t' (i + 1) i
  end else begin
    let k = ts.heap.[ts.heap_max] in
    let l = ts.heap.[1] in
    let es = element_seq ts in
    assert(es.[ts.heap_len] == k /\ es.[0] == l);
    lemma_pqmerge_heap_sorted ts node ts' t' (i + 1)
  end
#pop-options

let lemma_pqmerge_partial_wf
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: pos{2 <= i /\ i <= ts'.heap_len / 2}): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures
    smaller ts' ts'.heap.[i] ts'.heap.[i * 2] /\
    (i * 2 + 1 <= ts'.heap_len ==> smaller ts' ts'.heap.[i] ts'.heap.[i * 2 + 1])) =
  lemma_pqmerge_smaller_heap ts node ts' t' i (i * 2);
  if i * 2 + 1 <= ts'.heap_len then
    lemma_pqmerge_smaller_heap ts node ts' t' i (i * 2 + 1)

let lemma_pqmerge_sorted_lt_heap 
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: pos{i <= ts'.heap_len}): Lemma
  (requires pqmerge_main_pre ts node ts' t' /\ sorted_not_empty ts')
  (ensures smaller ts' ts'.heap.[ts'.heap_max] ts'.heap.[i]) =
  let hd = U32.v ts'.heap.[ts'.heap_max] in
  let r = U32.v ts'.heap.[i] in
  let es = element_seq ts in
  assert(U32.v es.[0] == hd);
  if 1 < i then begin
    assert(U32.v es.[i - 1] == r);
    lemma_heap_wf ts i
  end else begin
    let hd' = U32.v ts'.heap.[ts'.heap_max + 1] in
    assert(freq_corr ts ts.heap_max);
    assert(U16.v (ts'.tree.[hd]).freq_or_code == freq ts'.forest.[hd]);
    assert(U16.v (ts'.tree.[hd']).freq_or_code == freq ts'.forest.[hd']);
    assert(U16.v (ts'.tree.[r]).freq_or_code > U16.v (ts'.tree.[hd]).freq_or_code)
  end

let lemma_pqmerge_max_id
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: nat{i < ts'.heap_len - 1}): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures U32.v (tail (heap_seq ts')).[i] < node) =
  let tl = tail (heap_seq ts') in
  assert(tl.[i] == (heap_seq ts).[i + 1] /\ tl.[i] == (element_seq ts).[i + 1])

#push-options "--z3seed 2 --fuel 1 --ifuel 1"
let rec lemma_pqmerge_forest_symbols_aux
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (s: tree_id_seq ts'): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    (forall i. U32.v s.[i] < node))
  (ensures forest_symbols ts s == forest_symbols ts' s)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> lemma_pqmerge_forest_symbols_aux ts node ts' t' (tail s)

let lemma_pqmerge_forest_symbols
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures forest_symbols ts (intermediate_fseq ts) == forest_symbols ts' (heap_seq ts')) =
  let open FStar.Classical in
  let tl = tail (heap_seq ts') in
  calc (==) {
    forest_symbols ts (intermediate_fseq ts);
    ={lemma_forest_symbols_append ts (create 1 ts.heap.[ts.heap_max]) (heap_seq ts)}
    forest_symbols ts (create 1 ts.heap.[ts.heap_max]) @|
    forest_symbols ts (heap_seq ts);
    =={lemma_forest_symbols_single ts ts.heap.[ts.heap_max]}
    symbols ts.forest.[U32.v ts.heap.[ts.heap_max]] @|
    forest_symbols ts (heap_seq ts);
    =={}
    symbols ts.forest.[U32.v ts.heap.[ts.heap_max]] @|
    (symbols ts.forest.[U32.v ts.heap.[1]] @|
    forest_symbols ts (tail (heap_seq ts)));
    =={
      append_assoc
        (symbols ts.forest.[U32.v ts.heap.[ts.heap_max]])
        (symbols ts.forest.[U32.v ts.heap.[1]])
        (forest_symbols ts (tail (heap_seq ts)))
    }
    (symbols ts.forest.[U32.v ts.heap.[ts.heap_max]] @|
    symbols ts.forest.[U32.v ts.heap.[1]]) @|
    forest_symbols ts (tail (heap_seq ts));
    =={}
    (symbols ts'.forest.[U32.v ts'.heap.[ts.heap_max]] @|
    symbols ts'.forest.[U32.v ts'.heap.[ts'.heap_max]]) @|
    forest_symbols ts (tail (heap_seq ts));
    =={assert((tail (heap_seq ts)) `equal` tl)}
    (symbols ts'.forest.[U32.v ts'.heap.[ts.heap_max]] @|
    symbols ts'.forest.[U32.v ts'.heap.[ts'.heap_max]]) @|
    forest_symbols ts tl;
    =={
      forall_intro (move_requires (lemma_pqmerge_max_id ts node ts' t'));
      lemma_pqmerge_forest_symbols_aux ts node ts' t' tl
    }
    (symbols ts'.forest.[U32.v ts'.heap.[ts.heap_max]] @|
    symbols ts'.forest.[U32.v ts'.heap.[ts'.heap_max]]) @|
    forest_symbols ts' tl;
    =={}
    symbols t' @| forest_symbols ts' tl;
    =={}
    forest_symbols ts' (heap_seq ts');
  }

let rec lemma_pqmerge_forest_freq_aux
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (s: tree_id_seq ts'): Lemma
  (requires
    pqmerge_main_pre ts node ts' t' /\
    (forall i. U32.v s.[i] < node))
  (ensures forest_freq ts s == forest_freq ts' s)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> lemma_pqmerge_forest_freq_aux ts node ts' t' (tail s)
#pop-options

#push-options "--fuel 2 --ifuel 2"
let lemma_forest_freq_single
  (ts: heap_elems_wf_ts) (s: U32.t{is_tree_index ts s}): Lemma
  (ensures freq ts.forest.[U32.v s] == forest_freq ts (create 1 s)) = ()
#pop-options

#push-options "--z3seed 7 --fuel 1 --ifuel 0"
let lemma_pqmerge_forest_freq
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures forest_freq ts (intermediate_fseq ts) == forest_freq ts' (heap_seq ts')) =
  let open FStar.Classical in
  let tl = tail (heap_seq ts') in
  calc (==) {
    forest_freq ts (intermediate_fseq ts);
    =={}
    forest_freq ts (create 1 ts.heap.[ts.heap_max] @| heap_seq ts);
    =={lemma_forest_freq_append ts (create 1 ts.heap.[ts.heap_max]) (heap_seq ts)}
    forest_freq ts (create 1 ts.heap.[ts.heap_max]) + forest_freq ts (heap_seq ts);
    =={lemma_tl ts.heap.[1] (tail (heap_seq ts))}
    forest_freq ts (create 1 ts.heap.[ts.heap_max]) +
    forest_freq ts (create 1 ts.heap.[1] @| tail (heap_seq ts));
    =={lemma_forest_freq_append ts (create 1 ts.heap.[1]) (tail (heap_seq ts))}
    forest_freq ts (create 1 ts.heap.[ts.heap_max]) +
    forest_freq ts (create 1 ts.heap.[1]) +
    forest_freq ts (tail (heap_seq ts));
    =={
      lemma_forest_freq_single ts ts.heap.[1];
      lemma_forest_freq_single ts ts.heap.[ts.heap_max]
    }
    freq ts.forest.[U32.v ts.heap.[ts.heap_max]] +
    freq ts.forest.[U32.v ts.heap.[1]] +
    forest_freq ts (tail (heap_seq ts));
    =={}
    freq t' + forest_freq ts (tail (heap_seq ts));
    =={assert((tail (heap_seq ts)) `equal` tl)}
    freq t' + forest_freq ts (tail (heap_seq ts'));
    =={
      forall_intro (move_requires (lemma_pqmerge_max_id ts node ts' t'));
      lemma_pqmerge_forest_freq_aux ts node ts' t' tl
    }
    freq t' + forest_freq ts' (tail (heap_seq ts'));
    =={}
    forest_freq ts' (heap_seq ts');
  }
#pop-options

#push-options "--z3seed 0 --fuel 1 --ifuel 1"
let lemma_pqmerge_count_aux_1
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures (
    let es = element_seq ts in
    let es' = element_seq ts' in
    U32.v es'.[0] == node /\
    (forall i.{:pattern es'.[i]} 1 <= i /\ i < ts.heap_len ==> es.[i] == es'.[i]) /\
    es'.[ts.heap_len] == es.[0] /\
    (forall i.{:pattern es'.[i]} ts.heap_len + 1 <= i ==> es'.[i] == es.[i - 1]) /\
    (forall i.{:pattern es.[i]} id ts.forest.[U32.v es.[i]] == U32.v es.[i]) /\

    (forall i. {:pattern es.[i]} U32.v es.[i] < node) /\
    (forall i. {:pattern es'.[i]} 1 < i ==> U32.v es'.[i] < node))) =
  let es = element_seq ts in
  let es' = element_seq ts' in
  assert(U32.v es'.[0] == node);
  assert(forall i.{:pattern es'.[i]} 1 <= i /\ i < ts.heap_len ==> es.[i] == es'.[i]);
  assert(es'.[ts.heap_len] == es.[0]);
  assert(forall i.{:pattern es'.[i]} ts.heap_len + 1 <= i ==> es'.[i] == es.[i - 1]);
  assert(forall i.{:pattern es.[i]} id ts.forest.[U32.v es.[i]] == U32.v es.[i]);
  assert(no_dup es);
  assert(forall i. {:pattern es.[i]} U32.v es.[i] < node);
  assert(forall i. {:pattern es'.[i]} 1 < i ==> U32.v es'.[i] < node)
#pop-options

#push-options "--z3seed 0 --fuel 0 --ifuel 0"
let lemma_pqmerge_count_aux_2
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures (
    let es = element_seq ts in
    let es' = element_seq ts' in
    tail es' `equal` (slice es 1 ts.heap_len @| create 1 es.[0] @| sorted_seq ts))) =
  lemma_pqmerge_count_aux_1 ts node ts' t'
#pop-options

#push-options "--z3seed 0 --fuel 1 --ifuel 0"
let lemma_pqmerge_count
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (n: U32.t): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures (
    let es = element_seq ts in
    let es' = element_seq ts' in
    (U32.v n == node ==> count n es' == 1 /\ mem n es == false) /\
    (U32.v n <> node ==> count n es' == count n es))) =
  let es = element_seq ts in
  let es' = element_seq ts' in
  if U32.v n = node then begin
    lemma_pqmerge_count_aux_1 ts node ts' t';
    if mem n es then mem_index n es;
    if mem n (tail es') then mem_index n (tail es');
    calc (==) {
      count n es';
      =={}
      1 + count n (tail es');
    }
  end else
    calc (==) {
      count n es';
      =={}
      count n (tail es');
      =={lemma_pqmerge_count_aux_2 ts node ts' t'}
      count n (slice es 1 ts.heap_len @| create 1 es.[0] @| sorted_seq ts);
      =={append_assoc (slice es 1 ts.heap_len) (create 1 es.[0]) (sorted_seq ts)}
      count n ((slice es 1 ts.heap_len @| create 1 es.[0]) @| sorted_seq ts);
      =={
        lemma_append_count (slice es 1 ts.heap_len @| create 1 es.[0]) (sorted_seq ts)
      }
      count n (slice es 1 ts.heap_len @| create 1 es.[0]) + count n (sorted_seq ts);
      =={lemma_append_count (slice es 1 ts.heap_len) (create 1 es.[0])}
      count n (create 1 es.[0]) +
      count n (slice es 1 ts.heap_len) +
      count n (sorted_seq ts);
      =={lemma_append_count (create 1 es.[0]) (slice es 1 ts.heap_len)}
      count n (create 1 es.[0] @| slice es 1 ts.heap_len) + count n (sorted_seq ts);
      =={
        calc (==) {
          slice es 1 ts.heap_len;
          =={}
          slice (slice es 0 ts.heap_len) 1 ts.heap_len;
          =={assert((slice es 0 ts.heap_len) `equal` (heap_seq ts))}
          tail (heap_seq ts);
        }
      }
      count n (create 1 es.[0] @| tail (heap_seq ts)) + count n (sorted_seq ts);
      =={assert((create 1 es.[0] @| tail (heap_seq ts)) `equal` heap_seq ts)}
      count n (heap_seq ts) + count n (sorted_seq ts);
      =={lemma_append_count (heap_seq ts) (sorted_seq ts)}
      count n (heap_seq ts @| sorted_seq ts);
      =={}
      count n es;
    }
#pop-options

let lemma_pqmerge_id_max
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts{
    heap_not_empty ts'
  }) (t': wf_tree) (i: nat{
    i < length (element_seq ts')
  }) : Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures id ts'.forest.[U32.v (element_seq ts').[i]] < node + 1) =
  let open FStar.Classical in
  let es = element_seq ts in
  let es' = element_seq ts' in
  if i = 0 then
    assert(id ts'.forest.[U32.v es'.[i]] == node)
  else begin
    forall_intro (move_requires (lemma_pqmerge_count ts node ts' t'));
    no_dup_alt es' i 0;
    mem_index es'.[i] es
  end

let lemma_pqmerge_child_corr
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: heap_index ts'): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures child_corr ts' i) =
  let es = element_seq ts in
  let es' = element_seq ts' in
  if i = 1 then begin
    let t = ts'.forest.[U32.v ts'.heap.[1]] in
    exists_intro (fun j ->
      let t = ts'.forest.[U32.v ts'.heap.[1]] in
      j > 1 /\ j >= ts'.heap_max /\ j + 1 < U32.v heap_size /\
      U32.v ts'.heap.[j] == id (right t) /\
      U32.v ts'.heap.[j + 1] == id (left t)) ts'.heap_max
  end else if i = ts'.heap_max then begin
    let t = ts'.forest.[U32.v ts'.heap.[i]] in
    assert(child_corr ts 1);
    if Node ? t then begin
      lemma_wf_tree_id_unfold t;
      lemma_is_max_id_map ts node 1
    end
  end else begin
    let t = ts.forest.[U32.v ts.heap.[i]] in
    lemma_is_max_id_map ts node i;
    if i <= ts'.heap_len then
      lemma_heap_seq ts' i
    else
      lemma_sorted_seq ts' i;
    assert(child_corr ts i);
    if Node? t then lemma_wf_tree_id_unfold t
  end

let lemma_pqmerge_parent_corr
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: heap_index ts'): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures parent_corr ts' i) =
  if ts.heap_max < i then assert(parent_corr ts i)

let lemma_pqmerge_freq_corr
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: heap_index ts'): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures freq_corr ts' i) =
  let i' = U32.v ts'.heap.[i] in
  if i = 1 then
    lemma_pqmerge_child_corr ts node ts' t' i
  else if ts'.heap_max = i then begin
    lemma_is_max_id_map ts node 1;
    assert(freq_corr ts 1)
  end else if ts'.heap_max < i then
    assert(freq_corr ts i)
  else begin
    let es = element_seq ts in
    let es' = element_seq ts' in
    lemma_heap_seq ts' i;
    forall_intro (move_requires (lemma_pqmerge_count ts node ts' t'));
    lemma_pqmerge_count ts node ts' t' ts'.heap.[i];
    no_dup_alt es' 0 (i - 1);
    assert(mem ts'.heap.[i] es');
    mem_index ts'.heap.[i] es;
    exists_elim
      (freq_corr ts' i)
      (get_proof (exists j. es.[j] == ts'.heap.[i]))
      (fun j ->
        if j >= ts.heap_len then begin
          assert(es.[j] == ts.heap.[j + (ts.heap_max - ts.heap_len)]);
          assert(freq_corr ts (j + (ts.heap_max - ts.heap_len)))
        end else begin
          assert((ts'.tree.[i']).freq_or_code == (ts.tree.[i']).freq_or_code);
          assert(ts'.forest.[i'] == ts.forest.[i']);
          assert(freq_corr ts (j + 1))
        end)
  end

#set-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0"
let lemma_pqmerge_dad_zero
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: pos{i <= ts'.heap_len}): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures U16.v (ts'.tree.[U32.v ts'.heap.[i]]).dad_or_len == 0) =
  let i' = U32.v ts'.heap.[i] in
  let es' = element_seq ts' in
  lemma_heap_seq ts' i;
  lemma_sorted_seq ts' ts'.heap_max;
  lemma_sorted_seq ts' ts.heap_max;

  forall_intro (move_requires (lemma_pqmerge_count ts node ts' t'));
  no_dup_alt es' (i - 1) ts'.heap_len;
  no_dup_alt es' (i - 1) (ts'.heap_len + 1)

#set-options "--z3refresh --z3rlimit 256 --fuel 1 --ifuel 1"
let lemma_pqmerge_main ts node ts' t' =
  lemma_pqmerge_heap_wf ts node ts' t';
  lemma_pqmerge_heap_sorted ts node ts' t' ts'.heap_max;
  forall_intro (move_requires (lemma_pqmerge_partial_wf ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_sorted_lt_heap ts node ts' t'));
  lemma_pqmerge_forest_symbols ts node ts' t';
  lemma_pqmerge_forest_freq ts node ts' t';
  forall_intro (move_requires (lemma_pqmerge_count ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_id_max ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_dad_zero ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_child_corr ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_parent_corr ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_freq_corr ts node ts' t'))

#set-options "--z3refresh --z3rlimit 256 --fuel 1 --ifuel 1"
let rec lemma_node_leaf_count t =
  match t with
  | Node l _ _ r ->
    lemma_node_leaf_count l;
    lemma_node_leaf_count r
  | _ -> ()

let rec forest_node_leaf_count' (ts: intermediate_ts) (i: pos): Lemma
  (requires i <= ts.heap_len)
  (ensures forest_node_count' ts i == (forest_leaf_count' ts i) - i) =
  match i with
  | 1 -> ()
  | _ -> forest_node_leaf_count' ts (i - 1)

let lemma_forest_node_leaf_count ts = forest_node_leaf_count' ts ts.heap_len

#set-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0 --z3seed 7 --query_stats"
let lemma_pqdownheap_max_id
  (ts0 ts1: intermediate_ts) (node: nat)
  (i: index_t (element_seq ts1)): Lemma
  (requires
    is_max_id ts0 node /\
    ts0.forest == ts1.forest /\
    permutation U32.t (element_seq ts0) (element_seq ts1))
  (ensures id ts1.forest.[U32.v (element_seq ts1).[i]] < node) =
  let es0 = element_seq ts0 in
  let es1 = element_seq ts1 in
  count_index es1;
  mem_index es1.[i] es0

let pqdownheap_comm_cond (ts0: tree_state_wf) (ts1: heap_wf_ts) =
  1 < ts0.heap_len /\ pqdownheap_pre ts0 1ul /\ ts1 == pqdownheap ts0 1ul /\
  no_dup (element_seq ts0) /\ no_dup (element_seq ts1)

let lemma_pqdownheap_freq_corr
  (ts0: tree_state_wf) (ts1: heap_wf_ts) (i: heap_index ts1): Lemma
  (requires pqdownheap_comm_cond ts0 ts1 /\ (forall j. freq_corr ts0 j))
  (ensures freq_corr ts1 i) =
  let es0 = element_seq ts0 in
  let es1 = element_seq ts1 in
  count_index es1;
  if i <= ts1.heap_len then begin
    lemma_heap_seq ts1 i;
    mem_index es1.[i - 1] es0
  end else begin
    lemma_sorted_seq ts1 i;
    mem_index es1.[i - (ts1.heap_max - ts1.heap_len)] es0
  end;
  exists_elim
    (freq_corr ts1 i)
    (get_proof (exists j. 
      (i <= ts1.heap_len ==> es0.[j] == es1.[i - 1]) /\
      (ts1.heap_len < i ==> es0.[j] == es1.[i - (ts1.heap_max - ts1.heap_len)])))
    (fun j -> 
      if j < ts0.heap_len then
        lemma_heap_seq ts0 (j + 1)
      else
        lemma_sorted_seq ts0 (j + (ts0.heap_max - ts0.heap_len)))

let lemma_pqdownheap_parent_corr
  (ts0: tree_state_wf) (ts1: heap_wf_ts) (i: heap_index ts1): Lemma
  (requires pqdownheap_comm_cond ts0 ts1 /\ (forall j. tree_corr ts0 j))
  (ensures parent_corr ts1 i) =
  if ts1.heap_max <= i then begin
    assert(parent_corr ts0 i);
    exists_elim
      (parent_corr ts1 i)
      (get_proof (exists (j: heap_index ts0{j < i}).
        U16.v (ts0.tree.[U32.v (ts0.heap).[i]]).dad_or_len == U32.v ts0.heap.[j]))
      (fun j ->
        if j <= ts0.heap_len then begin
          let hs0 = heap_seq ts0 in let hs1 = heap_seq ts1 in
          let es0 = element_seq ts0 in let es1 = element_seq ts1 in
          lemma_heap_seq ts0 j;
          count_index hs0;
          mem_index hs0.[j - 1] hs1;
          count_index es0;
          mem_index es0.[j - 1] es1
        end else
          lemma_sorted_seq ts0 j)
  end

let lemma_pqdownheap_child_corr
  (ts0: tree_state_wf) (ts1: heap_wf_ts) (i: heap_index ts1): Lemma
  (requires pqdownheap_comm_cond ts0 ts1 /\ (forall j. child_corr ts0 j))
  (ensures child_corr ts1 i) =
  let i' = U32.v ts1.heap.[i] in let t = ts1.forest.[i'] in
  let es0 = element_seq ts0 in let es1 = element_seq ts1 in
  let hs0 = heap_seq ts0 in let hs1 = heap_seq ts1 in
  let ss0 = sorted_seq ts0 in let ss1 = sorted_seq ts1 in
  if Node? t then begin
    lemma_wf_tree_id_unfold t;
    if i <= ts1.heap_len then begin
      lemma_heap_seq ts1 i;
      count_index es1;
      mem_index es1.[i - 1] es0;
      exists_elim
        (exists (j: heap_index ts0). ts0.heap.[j] == ts1.heap.[i])
        (get_proof (exists j. es0.[j] == es1.[i - 1]))
        (fun j ->
          if j < ts0.heap_len then
            lemma_heap_seq ts0 (j + 1)
          else
            lemma_sorted_seq ts0 (j + (ts0.heap_max - ts0.heap_len)))
    end else
      lemma_sorted_seq ts0 i;
    exists_elim
      (child_corr ts1 i)
      (get_proof (exists (j: heap_index ts0). ts0.heap.[j] == ts1.heap.[i]))
      (fun j -> 
        assert(child_corr ts0 j);
        let j'' = j - (ts0.heap_max - ts0.heap_len) in
        if i <= ts1.heap_len then begin
          if j > ts0.heap_len then begin
            lemma_sorted_seq ts0 j;
            lemma_heap_seq ts1 i;
            no_dup_alt es1 (i - 1) j''
          end;
          assert(j <= ts0.heap_len)
        end else begin
          let i'' = i - (ts1.heap_max - ts1.heap_len) in
          lemma_sorted_seq ts1 i;
          if j <> i then
            if j <= ts0.heap_len then begin
              lemma_heap_seq ts0 j;
              no_dup_alt es0 (j - 1) i''
            end else begin
              lemma_sorted_seq ts0 j;
              no_dup_alt es0 j'' i''
            end;
          assert(i == j)
        end;
        exists_elim
          (child_corr ts1 i)
          (get_proof (child_in_sorted ts0 j))
          (fun k -> assert(child_in_sorted ts1 i)))
  end

let lemma_pqdownheap_dad_zero
  (ts0: tree_state_wf) (ts1: heap_wf_ts) (i: heap_index ts1): Lemma
  (requires pqdownheap_comm_cond ts0 ts1 /\
    (forall j. 1 <= j /\ j <= ts0.heap_len ==>
      U16.v (ts0.tree.[U32.v ts0.heap.[j]]).dad_or_len == 0))
  (ensures 1 <= i /\ i <= ts1.heap_len ==>
    U16.v (ts1.tree.[U32.v ts1.heap.[i]]).dad_or_len == 0) =
  let hs0 = heap_seq ts0 in let hs1 = heap_seq ts1 in
  if 1 <= i && i <= ts1.heap_len then begin
    lemma_heap_seq ts1 i;
    count_index hs1;
    mem_index hs1.[i - 1] hs0;
    exists_elim
      (exists j. j <= ts0.heap_len /\ ts0.heap.[j] == ts1.heap.[i])
      (get_proof (exists j. hs0.[j] == hs1.[i - 1]))
      (fun j -> lemma_heap_seq ts0 (j + 1))
  end

#set-options "--z3refresh --ifuel 1 --fuel 1"
let rec lemma_symbol_leaf_count (t: tree): Lemma
  (ensures length (symbols t) == leaf_count t) =
  match t with
  | Node l _ _ r ->
    lemma_symbol_leaf_count l;
    lemma_symbol_leaf_count r
  | Leaf _ _ -> ()

let rec forest_symbols' (ts: heap_elems_wf_ts) (s: tree_id_seq ts): Tot (seq nat)
  (decreases length s) =
  if length s = 0 then
    empty #nat
  else
    forest_symbols' ts (unsnoc s) @| symbols ts.forest.[U32.v (last s)] 

let rec lemma_forest_symbols_rev (ts: heap_elems_wf_ts) (s: tree_id_seq ts): Lemma
  (ensures forest_symbols' ts s == forest_symbols ts s)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ ->
    calc (==) {
      forest_symbols' ts s;
      =={}
      forest_symbols' ts (unsnoc s) @| symbols ts.forest.[U32.v (last s)] ;
      =={lemma_forest_symbols_rev ts (unsnoc s)}
      forest_symbols ts (unsnoc s) @| symbols ts.forest.[U32.v (last s)];
      =={lemma_forest_symbols_single ts (last s)}
      forest_symbols ts (unsnoc s) @|
      forest_symbols ts (create 1 (last s));
      =={
        lemma_forest_symbols_append ts (unsnoc s) (create 1 (last s));
        assert(equal ((unsnoc s) @| create 1 (last s)) s)
      }
      forest_symbols ts s;
    }

#set-options "--z3refresh --ifuel 1 --fuel 2"
let rec lemma_forest_symbols_leaf_count_aux
  (ts: intermediate_ts) (hl: nat{1 <= hl /\ hl <= ts.heap_len}): Lemma
  (ensures
    length (forest_symbols' ts (slice (heap_seq ts) 0 hl)) ==
    forest_leaf_count' ts hl) =
  lemma_symbol_leaf_count ts.forest.[U32.v ts.heap.[hl]];
  match hl with
  | 1 -> ()
  | _ ->
    let hs = slice (heap_seq ts) 0 hl in
    let t = ts.forest.[U32.v (last hs)] in
    calc (==) {
      length (forest_symbols' ts hs);
      =={}
      length (
        forest_symbols' ts (unsnoc hs) @|
        symbols ts.forest.[U32.v (last hs)]);
      =={lemma_len_append (forest_symbols' ts (unsnoc hs)) (symbols t)}
      length (forest_symbols' ts (unsnoc hs)) + length (symbols t);
      =={lemma_symbol_leaf_count ts.forest.[U32.v (last hs)]}
      length (forest_symbols' ts (unsnoc hs)) + leaf_count t;
      =={lemma_forest_symbols_leaf_count_aux ts (hl - 1)}
      forest_leaf_count' ts (hl - 1) + leaf_count t;
      =={}
      forest_leaf_count' ts hl;
    }

#set-options "--z3refresh --fuel 0 --ifuel 0"
let lemma_forest_symbols_leaf_count (ts: intermediate_ts): Lemma
  (ensures
    length (forest_symbols ts (heap_seq ts)) ==
    forest_leaf_count ts) =
  calc (==) {
    length (forest_symbols ts (heap_seq ts));
    =={lemma_forest_symbols_rev ts (heap_seq ts)}
    length (forest_symbols' ts (heap_seq ts));
    =={}
    length (forest_symbols' ts (slice (heap_seq ts) 0 ts.heap_len));
    =={lemma_forest_symbols_leaf_count_aux ts ts.heap_len}
    forest_leaf_count ts;
  }

let build_tree_rec_cond
  (ts0: forest_wf_ts) (ts1: partial_wf_ts 2ul) (ts2: heap_wf_ts) (node: nat) =
  2 < ts0.heap_len /\
  build_tree_pre ts0 node /\
  build_tree_term_post ts0 node ts1 /\
  ts2 == pqdownheap ts1 1ul

#push-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let lemma_build_tree_flc
  (ts0: forest_wf_ts) (ts1: partial_wf_ts 2ul) (ts2: heap_wf_ts) (node: nat): Lemma
  (requires build_tree_rec_cond ts0 ts1 ts2 node)
  (ensures forest_leaf_count ts0 == forest_leaf_count ts2) =
  let hs0 = heap_seq ts0 in
  let fs0 = forest_symbols ts0 hs0 in
  let hs1 = heap_seq ts1 in
  let fs1 = forest_symbols ts1 hs1 in
  let hs2 = heap_seq ts2 in
  let fs2 = forest_symbols ts2 hs2 in
  calc (==) {
    forest_leaf_count ts0;
    =={lemma_forest_symbols_leaf_count ts0}
    length fs0;
    =={perm_len fs0 fs1}
    length fs1;
    =={
      lemma_forest_symbols_perm ts1 hs1 ts2 hs2;
      perm_len fs1 fs2
    }
    length fs2;
    =={lemma_forest_symbols_leaf_count ts2}
    forest_leaf_count ts2;
  }

let lemma_build_tree_fnc
  (ts0: forest_wf_ts) (ts1: partial_wf_ts 2ul) (ts2: heap_wf_ts) (node: nat): Lemma
  (requires build_tree_rec_cond ts0 ts1 ts2 node)
  (ensures forest_node_count ts0 + 1 == forest_node_count ts2) =
  let hs0 = heap_seq ts0 in let hs1 = heap_seq ts1 in let hs2 = heap_seq ts2 in
  calc (==) {
    forest_node_count ts0 + 1;
    =={}
    forest_leaf_count ts0 - ts0.heap_len + 1;
    =={Math.subtraction_is_distributive (forest_leaf_count ts0) ts0.heap_len 1}
    forest_leaf_count ts0 - (ts0.heap_len - 1);
    =={}
    forest_leaf_count ts0 - ts2.heap_len;
    =={lemma_build_tree_flc ts0 ts1 ts2 node}
    forest_leaf_count ts2 - ts2.heap_len;
    =={}
    forest_node_count ts2;
  }

let lemma_build_tree_flc_fnc
  (ts0: forest_wf_ts) (ts1: partial_wf_ts 2ul) (ts2: heap_wf_ts) (node: nat): Lemma
  (requires build_tree_rec_cond ts0 ts1 ts2 node)
  (ensures (
    let flc2 = forest_leaf_count ts2 in
    let fnc2 = forest_node_count ts2 in
    U32.v heap_size - ts2.heap_max + ts2.heap_len == flc2 + fnc2)) =
  let flc0 = forest_leaf_count ts0 in
  let fnc0 = forest_node_count ts0 in
  let flc2 = forest_leaf_count ts2 in
  let fnc2 = forest_node_count ts2 in
  calc (==) {
    flc2 + fnc2;
    =={
      lemma_build_tree_fnc ts0 ts1 ts2 node;
      lemma_build_tree_flc ts0 ts1 ts2 node
    }
    flc0 + (fnc0 + 1);
    =={Math.paren_add_right flc0 fnc0 1}
    flc0 + fnc0 + 1;
    =={}
    (U32.v heap_size - ts2.heap_max - 2) + (ts2.heap_len + 1) + 1;
    =={
      Math.paren_add_right
        (U32.v heap_size - ts2.heap_max - 2)
        (ts2.heap_len + 1)
        1
    }
    (U32.v heap_size - ts2.heap_max - 2) + ((ts2.heap_len + 1) + 1);
    =={Math.addition_is_associative ts2.heap_len 1 1}
    (U32.v heap_size - ts2.heap_max - 2) + (ts2.heap_len + 2);
    =={
      Math.addition_is_associative
        (U32.v heap_size - ts2.heap_max - 2)
        ts2.heap_len
        2
    }
    U32.v heap_size - ts2.heap_max - 2 + ts2.heap_len + 2;
    =={
      assert_norm(
        U32.v heap_size - ts2.heap_max - 2 + ts2.heap_len + 2 ==
        U32.v heap_size - ts2.heap_max + ts2.heap_len)
    }
    U32.v heap_size - ts2.heap_max + ts2.heap_len;
  }

let lemma_build_tree_rec ts0 ts1 ts2 node =
  let hs0 = heap_seq ts0 in
  let hs1 = heap_seq ts1 in
  let hs2 = heap_seq ts2 in
  lemma_forest_freq_perm ts1 hs1 ts2 hs2;
  lemma_forest_symbols_perm ts1 hs1 ts2 hs2;
  forall_intro (move_requires (lemma_pqdownheap_freq_corr ts1 ts2));
  forall_intro (move_requires (lemma_pqdownheap_parent_corr ts1 ts2));
  forall_intro (move_requires (lemma_pqdownheap_child_corr ts1 ts2));
  forall_intro (move_requires (lemma_pqdownheap_dad_zero ts1 ts2));
  forall_intro (move_requires (lemma_pqdownheap_max_id ts1 ts2 (node + 1)));
  lemma_forest_symbols_leaf_count ts1;
  lemma_build_tree_fnc ts0 ts1 ts2 node;
  lemma_build_tree_flc_fnc ts0 ts1 ts2 node
