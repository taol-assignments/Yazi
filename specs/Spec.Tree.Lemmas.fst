module Spec.Tree.Lemmas

open FStar.Mul

let lemma_subtraction_cancel (a b c: int): Lemma
  (requires b = a - c)
  (ensures b + c == a) = ()

#set-options "--z3refresh --z3rlimit 256 --fuel 0 --ifuel 0"
let lemma_heap_seq (ts: heap_wf_ts) (i: heap_index ts): Lemma
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

let lemma_sorted_seq (ts: heap_wf_ts) (i: heap_index ts): Lemma
  (requires i >= ts.heap_max)
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

#set-options "--z3refresh --z3rlimit 1024 --fuel 0 --ifuel 0"
let lemma_pqremove_forest_aux
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (requires (
    let ts' = pqremove ts in
    ts'.heap_max < i))
  (ensures (
    let ts' = pqremove ts in
    let (es, es') = (element_seq ts, element_seq ts') in
    let dad = Cast.uint16_to_uint32 (ts'.tree.[U32.v ts'.heap.[i]]).dad_or_len in
    mem ts'.heap.[i] es /\
    i - (ts'.heap_max - ts'.heap_len) == index_of es ts'.heap.[i] /\
    mem dad es)) =
  lemma_pqremove_index ts i;
  let ts' = pqremove ts in
  let (es, es') = (element_seq ts, element_seq ts') in
  let j = index_of es ts'.heap.[i] in
  let i' = i - (ts'.heap_max - ts'.heap_len) in
  let j' = j + (ts.heap_max - ts.heap_len) in
  lemma_sorted_seq ts' i;
  no_dup_index_of es i' ts'.heap.[i];
  no_dup_index_of es' j ts'.heap.[i];
  lemma_sorted_seq ts j';

  lemma_sorted_seq ts i;
  lemma_sorted_seq ts' i;
  assert(tree_corr ts i /\ parent_corr ts i);
  assert(ts.heap_max <= i /\ ts'.heap.[i] == ts.heap.[i])

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
  let open FStar.Classical in
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
let lemma_pqremove_child_corr
  (ts: forest_wf_ts{ts.heap_len > 1})
  (i: heap_index (pqremove ts)): Lemma
  (ensures 
    // let ts' = pqremove ts in
    // id ts'.forest.[U32.v ts'.heap.[i]] == U32.v ts'.heap.[i] /\
    child_corr (pqremove ts) i) =
  let ts' = pqremove ts in
  let i' = U32.v ts'.heap.[i] in
  let t = ts'.forest.[i'] in
  lemma_pqremove_index ts i;
  if Node? t then begin
    assert(ts.forest.[i'] == t);
    let l = id (left t) in let r = id (right t) in
    assert(l < id t /\ r < id t);
    assert(exists (j: heap_index ts). ts.heap.[j] == ts'.heap.[i] /\ child_corr ts j)
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

#push-options "--z3seed 0 --fuel 0 --ifuel 0 --query_stats"
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
  if ts'.heap_max < i then begin
    lemma_pqremove_forest_aux ts i;
    lemma_sorted_seq ts (j + (ts.heap_max - ts.heap_len));
    let k = index_of es dad in
    if ts.heap_len <= k then () else if k = 0 then
      no_dup_index_of es' ts'.heap_len dad
    else
      lemma_pqremove_heap_seq_index ts k
  end
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

#push-options "--z3seed 6 --fuel 0 --ifuel 0 --query_stats"
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

let rec lemma_forest_freq_perm
  (ts0: heap_elems_wf_ts) (s0: tree_id_seq ts0)
  (ts1: heap_elems_wf_ts) (s1: tree_id_seq ts1): Lemma
  (requires ts0.forest == ts1.forest /\ permutation U32.t s0 s1)
  (ensures forest_freq ts0 s0 == forest_freq ts1 s1)
  (decreases length s0) =
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

#push-options "--fuel 0 --ifuel 0"
let lemma_pqremove_forest ts node =
  let ts' = pqremove ts in
  let s = intermediate_fseq ts' in
  let open FStar.Classical in
  lemma_pqremove_id ts node;
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

#push-options "--query_stats"
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

#push-options "--fuel 2 --ifuel 2"
let lemma_pqmerge_child_corr
  (ts: heap_wf_ts) (node: nat) (ts': heap_elems_wf_ts) (t': wf_tree)
  (i: heap_index ts'): Lemma
  (requires pqmerge_main_pre ts node ts' t')
  (ensures child_corr ts' i) =
  let open FStar.Classical in
  let es = element_seq ts in
  let es' = element_seq ts' in
  if i = 1 || i = ts'.heap_max then
    admit()
  else begin
    let i' = U32.v ts.heap.[i] in
    let t = ts.forest.[i'] in
    assert(ts.heap.[i] == ts'.heap.[i]);
    assume(i' < node);
    assert(t == ts'.forest.[i']);
    if Node? t then begin
      assert(id t < node);
      assert(id (left t) < id t /\ id (right t) < id t);
      assert((ts.tree.[id (left t)]).dad_or_len == (ts'.tree.[id (left t)]).dad_or_len);
      assume((ts.tree.[id (right t)]).dad_or_len == (ts'.tree.[id (right t)]).dad_or_len);
      assert(ts.forest.[id (left t)] == ts'.forest.[id (left t)]);
      assert(ts.forest.[id (right t)] == ts'.forest.[id (right t)]);
      assume(id ts'.forest.[U32.v ts'.heap.[i]] == U32.v ts'.heap.[i])
    end;
    assume(id ts'.forest.[U32.v ts'.heap.[i]] == U32.v ts'.heap.[i]);
    assert(1 <= i /\ i <= ts.heap_len \/ ts.heap_max <= i /\ i < U32.v heap_size);
    assert(child_corr ts' i);
    admit()
  end

let lemma_pqmerge_main ts node ts' t' =
  let open FStar.Classical in
  lemma_pqmerge_heap_wf ts node ts' t';
  lemma_pqmerge_heap_sorted ts node ts' t' ts'.heap_max;
  forall_intro (move_requires (lemma_pqmerge_partial_wf ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_sorted_lt_heap ts node ts' t'));
  lemma_pqmerge_forest_symbols ts node ts' t';
  lemma_pqmerge_forest_freq ts node ts' t';
  forall_intro (move_requires (lemma_pqmerge_count ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_id_max ts node ts' t'));
  forall_intro (move_requires (lemma_pqmerge_child_corr ts node ts' t'))
