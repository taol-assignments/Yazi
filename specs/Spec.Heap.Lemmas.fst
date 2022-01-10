module Spec.Heap.Lemmas

(** Lemmas to verify that smaller() is a total order relation. **)
let lemma_smaller_asym (ts: heap_elems_wf_ts) (i j: U32.t): Lemma
  (requires
    is_tree_index ts i /\ is_tree_index ts j /\
    smaller ts i j /\ smaller ts j i)
  (ensures i == j) = ()

let lemma_smaller_trans (ts: heap_elems_wf_ts) (a b c: U32.t): Lemma
  (requires
    is_tree_index ts a /\ is_tree_index ts b /\ is_tree_index ts c /\
    smaller ts a b /\ smaller ts b c)
  (ensures smaller ts a c) = ()

let lemma_smaller_comp (ts: heap_elems_wf_ts) (i j: U32.t): Lemma
  (requires is_tree_index ts i /\ is_tree_index ts j)
  (ensures smaller ts i j \/ smaller ts j i) = ()

let lemma_heap_seq_upd_perm ts0 ts1 =
  assert(equal
    (Seq.slice ts0.heap (ts0.heap_len + 1) (U32.v heap_size))
    (Seq.slice ts1.heap (ts0.heap_len + 1) (U32.v heap_size)));
  permutation_split ts0.heap ts1.heap 1 (ts0.heap_len + 1)

let rec lemma_heap_sorted' (ts0 ts1: heap_elems_wf_ts) (i: nat{
  ts0.heap_max <= i /\ i <= U32.v heap_size
}): Lemma
  (requires
    ts1 == {ts0 with heap = ts1.heap} /\
    heap_sorted' ts0 i /\
    non_heap_unmodified ts0.heap ts1.heap ts0.heap_len)
  (ensures heap_sorted' ts1 i)
  (decreases U32.v heap_size - i) =
  match U32.v heap_size - i with
  | 0 -> ()
  | _ -> lemma_heap_sorted' ts0 ts1 (i + 1)

let lemma_non_heap_unmodified ts0 ts1 =
  assert(equal (sorted_seq ts0) (sorted_seq ts1));
  match U32.v heap_size - ts0.heap_max with
  | 0 -> ()
  | _ -> lemma_heap_sorted' ts0 ts1 ts0.heap_max

let rec log2 (a: pos): Tot (n: nat{
  pow2 n <= a /\ a < pow2 (n + 1)
}) = if a = 1 then 0 else 1 + log2 (a / 2)

let rec log2_pow2_lt (a: pos) (n: nat): Lemma
  (requires n < log2 a)
  (ensures pow2 n < a) =
  match n with
  | 0 -> ()
  | _ -> log2_pow2_lt (a / 2) (n - 1)

let rec log2_pow2_gt (a: pos) (n: pos): Lemma
  (requires a < pow2 n)
  (ensures log2 a < n) =
  match (a, n) with
  | (1, _) | (_, 1) -> ()
  | _ -> log2_pow2_gt (a / 2) (n - 1)

let rec ancestor (a: pos) (i: pos{i <= log2 a}): Tot (res: pos{res < a}) =
  if i > 1 then ancestor (a / 2) (i - 1) else a / 2

let rec lemma_ancestor_next (a: pos) (i: pos{1 < i /\ i <= log2 a}): Lemma
  (ensures ancestor a i == ancestor a (i - 1) / 2) =
  match i with
  | 2 -> ()
  | _ -> lemma_ancestor_next (a / 2) (i - 1)

#push-options "--z3refresh --z3rlimit 128 --fuel 1 --ifuel 0 --z3seed 11"
/// Generalized version of lemma_heap_wf. Given a heap element whose index is j,
/// heap.[j] should not smaller than one of its ancestor whose height is smaller than j.
let rec lemma_partial_wf (height: nat{height < 32}) (ts: heap_elems_wf_ts) (j: pos): Lemma
  (requires
    pow2 height < pow2 32 - 1 /\
    partial_wf ts (U32.uint_to_t (pow2 height)) /\
    height < log2 j /\ j <= ts.heap_len /\ pow2 height < j)
  (ensures (
    let aj = ancestor j (log2 j - height) in
    pow2 height <= aj /\ aj < pow2 (height + 1) /\
    smaller ts ts.heap.[aj] ts.heap.[j]))
  (decreases ts.heap_len - pow2 height) =
  let aj = ancestor j (log2 j - height) in
  (* If j's height is height + 1 *)
  if j < pow2 (height + 2) then begin
    (* pow2 height < j *)
    log2_pow2_lt j height;
    (* log2 j < height + 2 *)
    log2_pow2_gt j (height + 2);
    assert(aj * 2 == j \/ aj * 2 + 1 == j)
    (* Then we have log2 j == height + 1, and the sub-goal can be proven by the
       hypothesis partial_wf ts (U32.uint_to_t (pow2 height)). *)
  end else begin
    (* If j's height is height + n where n > 1. First, we introduce the induction
       hypothesis. *)
    lemma_partial_wf (height + 1) ts j;
    (* Then we have ancestor j (log2 j - height) *)
    lemma_ancestor_next j (log2 j - height);
    let aj' = ancestor j (log2 j - (height + 1)) in
    assert(aj * 2 == aj' \/ aj * 2 + 1 == aj')
  end

let lemma_heap_wf ts j = if j > 1 then lemma_partial_wf 0 ts j
#pop-options

#push-options "--z3refresh --z3rlimit 128 --fuel 1 --ifuel 1 --z3seed 111"
let rec lemma_heap_sorted_sub (ts: heap_elems_wf_ts) (j: nat{
  ts.heap_max <= j /\ j < U32.v heap_size
}): Lemma
  (requires heap_sorted ts)
  (ensures heap_sorted' ts j) =
  match j - ts.heap_max with
  | 0 -> ()
  | _ -> lemma_heap_sorted_sub ts (j - 1)

private let rec lemma_heap_wf_pqremove_aux
  (ts0: heap_wf_ts) (ts1: heap_elems_wf_ts)
  (j: nat{U32.v heap_size > j /\ j > ts1.heap_max}):
  Lemma
  (requires
    ts0.heap_max == ts1.heap_max + 1 /\
    ts0.tree == ts1.tree /\
    ts0.depth == ts1.depth /\
    (forall i. i > ts1.heap_max ==> ts0.heap.[i] == ts1.heap.[i]))
  (ensures heap_sorted' ts1 j)
  (decreases U32.v heap_size - j) =
  if j < U32.v heap_size - 1 then begin
    lemma_heap_wf_pqremove_aux ts0 ts1 (j + 1);
    lemma_heap_sorted_sub ts0 j
  end
#pop-options

#push-options "--z3refresh --fuel 0 --ifuel 0"
let lemma_four_seq_perm_1 (#t: eqtype) (top bot mid ss0: seq t) (s: t): Lemma
  (ensures count s ((bot @| mid) @| (top @| ss0)) == count s ((top @| mid @| bot) @| ss0)) =
  calc (==) {
    count s ((bot @| mid) @| (top @| ss0));
    =={lemma_append_count_aux s (bot @| mid) (top @| ss0)}
    count s (bot @| mid) + count s (top @| ss0);
    =={lemma_append_count_aux s bot mid}
    count s bot + count s mid + count s (top @| ss0);
    =={lemma_append_count_aux s top ss0}
    count s bot + count s mid + count s top + count s ss0;
    =={lemma_append_count_aux s top mid}
    count s (top @| mid) + count s bot + count s ss0;
    =={lemma_append_count_aux s (top @| mid) bot}
    count s ((top @| mid) @| bot) + count s ss0;
    =={append_assoc top mid bot}
    count s (top @| mid @| bot) + count s ss0;
    =={lemma_append_count_aux s (top @| mid @| bot) ss0}
    count s ((top @| mid @| bot) @| ss0);
  }

let lemma_four_seq_perm_2 (#t: eqtype) (top mid bot hs0 hs1: seq t) (s: t): Lemma
  (requires
    hs0 `equal` (top @| mid @| bot) /\
    hs1 `equal` (bot @| mid))
  (ensures count s hs0 == count s (top @| hs1)) =
  calc (==) {
    count s hs0;
    =={}
    count s (top @| mid @| bot);
    =={append_assoc top mid bot}
    count s ((top @| mid) @| bot);
    =={lemma_append_count_aux s (top @| mid) bot}
    count s (top @| mid) + count s bot;
    =={lemma_append_count_aux s top mid}
    count s top + count s mid + count s bot;
    =={}
    count s top + (count s bot + count s mid);
    =={lemma_append_count_aux s bot mid}
    count s top + count s (bot @| mid);
    =={lemma_append_count_aux s top (bot @| mid)}
    count s (top @| (bot @| mid));
    =={}
    count s (top @| hs1);
  }
#pop-options

#push-options "--z3refresh --z3rlimit 256 --fuel 1 --ifuel 0 --z3seed 17"
let lemma_heap_wf_pqremove ts =
  let ts' = {
    ts with
    heap = upd (upd ts.heap (ts.heap_max - 1) ts.heap.[1]) 1 ts.heap.[ts.heap_len];
    heap_max = ts.heap_max - 1;
    heap_len = ts.heap_len - 1;
  } in
  let open FStar.Classical in
  let hs0 = heap_seq ts in
  let hs1 = heap_seq ts' in
  let top = create 1 hs0.[0] in
  let mid = slice hs0 1 (length hs0 - 1) in
  let bot = create 1 (last hs0) in
  let ss0 = sorted_seq ts in
  let ss1 = sorted_seq ts' in
  let es0 = element_seq ts in
  let es1 = element_seq ts' in
  calc (==) {
    es0;
    =={}
    hs0 @| ss0;
    =={assert((top @| mid @| bot) `equal` hs0)}
    (top @| mid @| bot) @| ss0;
  };
  calc (==) {
    es1;
    =={}
    hs1 @| ss1;
    =={assert((bot @| mid) `equal` hs1)}
    (bot @| mid) @| ss1;
    =={assert((top @| ss0) `equal` ss1)}
    (bot @| mid) @| (top @| ss0);
  };
  forall_intro (lemma_four_seq_perm_1 top bot mid ss0);
  forall_intro (move_requires (lemma_four_seq_perm_2 top mid bot hs0 hs1));

  assert(forall i. {:pattern ts'.heap.[i]} 1 < i /\ i <= ts'.heap_len ==>
    ts.heap.[i] == ts'.heap.[i]);
  lemma_heap_wf_forall ts;

  if ts.heap_max < U32.v heap_size then
    lemma_heap_wf_pqremove_aux ts ts' ts.heap_max
#pop-options
