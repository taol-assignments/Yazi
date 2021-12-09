module Spec.Kraft

module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module MathLib = FStar.Math.Lib

open FStar.Mul
open FStar.Seq
open Lib.Seq
open Lib.Rational

type tree = 
  | Node: left: tree -> freq: pos -> right: tree -> tree
  | Leaf: symbol: nat -> freq: pos -> tree

type non_leaf = t: tree{Leaf? t == false}

unfold let left (t: non_leaf) =
  match t with
  | Node l _ _ -> l

unfold let right (t: non_leaf) =
  match t with
  | Node _ _ r -> r

unfold let freq (t: tree) =
  match t with
  | Node _ f _ -> f
  | Leaf _ f -> f

let rec symbols (t: tree) =
  match t with
  | Node l _ r -> symbols l @| symbols r
  | Leaf s _ -> create 1 s

let rec lemma_symbols_length_gt_zero(t: tree): Lemma
  (ensures length (symbols t) > 0)
  [SMTPat (length (symbols t))] =
  if Node? t then
    lemma_symbols_length_gt_zero (left t)

type tree_symbol (t: tree) = s: nat{
  Seq.mem s (symbols t)
}

let rec code_length (t: tree) (s: tree_symbol t) =
  match t with
  | Node l _ r ->
    let ls = symbols l in
    let rs = symbols r in
    lemma_mem_append ls rs;
    1 + (if Seq.mem s ls then code_length l s else code_length r s)
  | _ -> 0

let rec code_freq (t: tree) (s: tree_symbol t) =
  match t with
  | Node l _ r ->
    let ls = symbols l in
    let rs = symbols r in
    lemma_mem_append ls rs;
    if Seq.mem s ls then code_freq l s else code_freq r s
  | Leaf _ f -> f

let rec height (t: tree): Tot nat =
  match t with
  | Node l _ r ->
    let lh = height l in let rh = height r in
    1 + (if lh > rh then lh else rh)
  | _ -> 0

type tree_height (t: tree) = h: nat{
  h <= height t
}

private let rec freq_pred (t: tree): Tot Type0 =
  match t with
  | Node l f r -> f == freq l + freq r /\ freq_pred l /\ freq_pred r
  | _ -> True

/// Definition of well-formed trees. Their root frequencies should be the sum of
/// the children's frequency, and their symbol list should not have duplicated
/// symbols.
type wf_tree = t: tree{
  no_dup (symbols t) /\ freq_pred t
}

let rec avg_len (t: tree): Tot nat =
  match t with
  | Node l f r -> f + avg_len l + avg_len r
  | Leaf _ _ -> 0

let optimal_tree = t: wf_tree{
  forall (t': wf_tree{permutation nat (symbols t) (symbols t')}).
    avg_len t <= avg_len t'
}

unfold let merge (l r: tree) = Node l (freq l + freq r) r

unfold let subst_pre_cond (t: wf_tree) (s: tree_symbol t) (l' r': (nat & pos)): Tot Type0 =
  let (sl, fl) = l' in
  let (sr, fr) = r' in
  sl <> sr /\ sl <> s /\ sr <> s /\
  fl + fr == code_freq t s /\
  mem sl (symbols t) == false /\
  mem sr (symbols t) == false

let rec subst (t: wf_tree) (s: tree_symbol t) (l' r': (nat & pos)): Pure tree
  (requires subst_pre_cond t s l' r')
  (ensures fun _ -> True) =
 let (sl, fl) = l' in
 let (sr, fr) = r' in
  match t with
  | Node l f r ->
    lemma_append_count (symbols l) (symbols r);
    if mem s (symbols l) then
      Node (subst l s l' r') f r
    else
      Node l f (subst r s l' r')
  | Leaf _ f ->
    Node (Leaf sl fl) f (Leaf sr fr)

let lemma_merge_subst
  (l r: wf_tree) (s: tree_symbol (merge l r)) (l' r': (nat & pos)): Lemma
  (requires (
    let (sl, fl) = l' in
    let (sr, fr) = r' in
    disjoint (symbols l) (symbols r) /\
    subst_pre_cond (merge l r) s l' r'))
  (ensures (
    let (sl, fl) = l' in
    let (sr, fr) = r' in
    lemma_append_count (symbols l) (symbols r);
    (mem s (symbols l) ==> merge (subst l s l' r') r == subst (merge l r) s l' r') /\
    (mem s (symbols r) ==> merge l (subst r s l' r') == subst (merge l r) s l' r'))) =
  lemma_append_count (symbols l) (symbols r)

#push-options "--z3rlimit 512 --fuel 0 --ifuel 0"
[@"opaque_to_smt"]
let rec min_freq_2 (f: seq wf_tree{length f >= 2}): Tot (res: (nat & nat){
  let (i1, i2) = res in
  i1 < length f /\ i2 < length f /\ i1 <> i2 /\
  (forall i. freq f.[i1] <= freq f.[i]) /\
  (forall i. i <> i1 ==> freq f.[i2] <= freq f.[i])
}) (decreases length f) =
  match length f with
  | 2 ->
    let f1 = freq f.[0] in
    let f2 = freq f.[1] in
    if f1 <= f2 then (0, 1) else (1, 0)
  | _ ->
    assert(forall i. i > 0 ==> f.[i] == (tail f).[i - 1]);
    let (i1, i2) = min_freq_2 (tail f) in
    let f0 = freq f.[0] in
    if f0 < freq f.[i1 + 1] then
      (0, i1 + 1)
    else if f0 < freq f.[i2 + 1] then
      (i1 + 1, 0)
    else
      (i1 + 1, i2 + 1)
#pop-options

let rec forest_symbols (f: seq wf_tree): Tot (seq nat) (decreases length f) =
  match length f with
  | 0 -> empty #nat
  | _ -> symbols f.[0] @| forest_symbols (tail f)

/// Definition of well-formed forest. Their symbol list should not have duplications.
type wf_forest = f: seq wf_tree{
  length f > 0 /\ no_dup (forest_symbols f)
}

let rec forest_freq (f: seq wf_tree) (s: nat{mem s (forest_symbols f)}): Tot nat
  (decreases length f) =
  if mem s (symbols f.[0]) then
    code_freq f.[0] s
  else begin
    lemma_mem_append (symbols f.[0]) (forest_symbols (tail f));
    forest_freq (tail f) s
  end

let rec forest_symbols_begin (f: seq wf_tree{length f > 0}) (i: nat{i < length f}):
  Tot (res: nat{res < length (forest_symbols f)}) (decreases i) =
  match i with
  | 0 -> 0
  | _ -> length (symbols f.[0]) + forest_symbols_begin (tail f) (i - 1)

let forest_symbols_end (f: seq wf_tree{length f > 0}) (i: nat{i < length f}): Tot nat =
  (forest_symbols_begin f i) + length (symbols f.[i])

let rec lemma_forest_symbols_end (f: seq wf_tree{length f > 0}) (i: nat{i < length f}): Lemma
  (ensures forest_symbols_end f i <= length (forest_symbols f))
  (decreases length f)
  [SMTPat (forest_symbols_end f i)] =
  match length f with
  | 0 -> ()
  | _ -> if i > 0 then lemma_forest_symbols_end (tail f) (i - 1)

let rec lemma_forest_symbols_begin (f: seq wf_tree{length f > 0}): Lemma
  (ensures
    forest_symbols_begin f (length f - 1) + length (symbols (last f)) ==
    length (forest_symbols f))
  (decreases length f) =
  match length f with
  | 1 -> ()
  | _ -> lemma_forest_symbols_begin (tail f)

let rec lemma_forest_symbols_begin_lt_1 (f: seq wf_tree) (i: nat): Lemma
  (requires i < length f /\ 0 < length f)
  (ensures forest_symbols_begin f i < length (forest_symbols f))
  (decreases length f)
  [SMTPat (forest_symbols_begin f i)] =
  match i with
  | 1 -> ()
  | _ -> if i > 0 then lemma_forest_symbols_begin_lt_1 (tail f) (i - 1)

let rec lemma_forest_symbols_begin_lt_2 (f: seq wf_tree) (i j: nat): Lemma
  (requires length f > 0 /\ i < j /\ j < length f)
  (ensures forest_symbols_begin f i < forest_symbols_begin f j)
  (decreases length f)
  [SMTPat (forest_symbols_begin f i); SMTPat(forest_symbols_begin f j)] =
  match length f with
  | 0 -> ()
  | _ ->
    if i = 0 then
      if i + 1 < j then
        lemma_forest_symbols_begin_lt_2 (tail f) 0 (j - 1)
      else
        ()
    else
      lemma_forest_symbols_begin_lt_2 (tail f) (i - 1) (j - 1)

#push-options "--z3refresh --z3rlimit 128 --fuel 2 --ifuel 2"
let rec lemma_forest_symbols_begin_end (f: seq wf_tree) (i: nat): Lemma
  (requires length f > 1 /\ i < length f - 1)
  (ensures forest_symbols_end f i == forest_symbols_begin f (i + 1))
  (decreases length f)
  [SMTPat (forest_symbols_end f i)] =
  match length f with
  | 2 -> ()
  | _ -> if i > 0 then lemma_forest_symbols_begin_end (tail f) (i - 1)
#pop-options

#push-options "--z3refresh --fuel 1 --ifuel 1"
let rec lemma_forest_symbols_index (f: seq wf_tree{length f > 0}) (i: nat{i < length f}): Lemma
  (ensures (
    let j = forest_symbols_begin f i in
    let l = j + length (symbols f.[i]) in
    l <= length (forest_symbols f) /\
    slice (forest_symbols f) j l == symbols f.[i]))
  (decreases i) =
  match i with
  | 0 ->
    assert(equal (symbols f.[0]) (slice (forest_symbols f) 0 (length (symbols f.[0]))))
  | _ ->
    lemma_forest_symbols_index (tail f) (i - 1);
    let j = forest_symbols_begin f i in
    let l = j + length (symbols f.[i]) in
    let o = length (symbols f.[0]) in
    assert(equal
      (slice (forest_symbols (tail f)) (j - o) (l - o))
      (slice (slice (forest_symbols f) o (length (forest_symbols f))) (j - o) (l - o)))
#pop-options

let rec lemma_forest_symbols_unsnoc_1 (f: wf_forest {length f > 0}): Lemma
  (ensures forest_symbols (unsnoc f) @| symbols (last f) == forest_symbols f)
  (decreases length f) =
  match length f with
  | 1 -> assert(equal (forest_symbols (unsnoc f) @| symbols (last f)) (forest_symbols f))
  | _ ->
    lemma_forest_symbols_unsnoc_1 (tail f);
    append_assoc (symbols f.[0]) (forest_symbols (unsnoc (tail f))) (symbols (last f))

let rec lemma_forest_symbols_unsnoc_2 (f: wf_forest {length f > 0}): Lemma
  (ensures no_dup (forest_symbols (unsnoc f)))
  (decreases length f) =
  match length f with
  | 1 -> ()
  | _ ->
    lemma_forest_symbols_unsnoc_1 f;
    lemma_forest_symbols_unsnoc_2 (tail f)

#push-options "--z3refresh --z3rlimit 1024 --fuel 2 --ifuel 2"
let rec lemma_wf_forest_symbols_disjoint' (f: wf_forest{length f >= 2}) (i j: nat): Lemma
  (requires i < j /\ j < length f)
  (ensures 
    no_dup (symbols f.[i]) /\
    no_dup (symbols f.[j]) /\
    disjoint (symbols f.[i]) (symbols f.[j]))
  (decreases length f) =
  let fs = forest_symbols f in
  let fsbj = forest_symbols_begin f j in
  let l0 = length (symbols f.[0]) in
  let l1 = length (symbols f.[1]) in
  lemma_forest_symbols_index f i;
  lemma_forest_symbols_index f j;
  if i = 0 then
    if j = length f - 1 then begin
      no_dup_slice fs l0 fsbj;
      lemma_forest_symbols_begin f
    end else if j = 1 then begin
      no_dup_slice fs l0 (fsbj + l1);
      lemma_forest_symbols_begin f
    end else begin
      lemma_forest_symbols_unsnoc_2 f;
      lemma_wf_forest_symbols_disjoint' (unsnoc f) i j
    end
  else
    lemma_wf_forest_symbols_disjoint' (tail f) (i - 1) (j - 1)

let lemma_wf_forest_symbols_disjoint (f: wf_forest{length f >= 2}) (i j: nat): Lemma
  (requires i <> j /\ i < length f /\ j < length f)
  (ensures
    no_dup (symbols f.[i]) /\
    no_dup (symbols f.[j]) /\
    disjoint (symbols f.[i]) (symbols f.[j])) =
  if i < j then
    lemma_wf_forest_symbols_disjoint' f i j
  else
    lemma_wf_forest_symbols_disjoint' f j i

let rec lemma_forest_symbols_append (f1 f2: seq wf_tree): Lemma
  (ensures forest_symbols f1 @| forest_symbols f2 == forest_symbols (f1 @| f2))
  (decreases length f1) =
  match length f1 with
  | 0 ->
    lemma_empty f1;
    append_empty_l (forest_symbols f2);
    append_empty_l f2
  | _ ->
    calc (==) {
      (forest_symbols f1) @| (forest_symbols f2);
      =={}
      (symbols f1.[0] @| (forest_symbols (tail f1))) @| (forest_symbols f2);
      =={append_assoc (symbols f1.[0]) (forest_symbols (tail f1)) (forest_symbols f2)}
      (symbols f1.[0]) @| ((forest_symbols (tail f1)) @| (forest_symbols f2));
      =={lemma_forest_symbols_append (tail f1) f2}
      (symbols f1.[0]) @| (forest_symbols ((tail f1) @| f2));
      =={assert(equal ((tail f1) @| f2) (tail (f1 @| f2)))}
      (symbols (f1 @| f2).[0]) @| (forest_symbols (tail (f1 @| f2)));
      =={}
      forest_symbols (f1 @| f2);
    }

let lemma_forest_symbols_append_triple (f1 f2 f3: seq wf_tree): Lemma
  (ensures
    forest_symbols f1 @| forest_symbols f2 @| forest_symbols f3 ==
    forest_symbols (f1 @| f2 @| f3)) =
  calc (==) {
    forest_symbols (f1 @| f2 @| f3);
    =={append_assoc f1 f2 f3}
    forest_symbols ((f1 @| f2) @| f3);
    =={lemma_forest_symbols_append (f1 @| f2) f3}
    forest_symbols (f1 @| f2) @| forest_symbols f3;
    =={lemma_forest_symbols_append f1 f2}
    (forest_symbols f1 @| forest_symbols f2) @| forest_symbols f3;
    =={append_assoc (forest_symbols f1) (forest_symbols f2) (forest_symbols f3)}
    forest_symbols f1 @| forest_symbols f2 @| forest_symbols f3;
  }

let rec lemma_forest_symbols_slice (f: seq wf_tree) (i j: nat): Lemma
  (requires length f > 0 /\ i < j /\ j <= length f)
  (ensures
    (j < length f ==>
      forest_symbols (slice f i j) ==
      slice (forest_symbols f) (forest_symbols_begin f i) (forest_symbols_begin f j)) /\
    (j == length f ==>
      forest_symbols (slice f i j) ==
      slice (forest_symbols f) (forest_symbols_begin f i) (length (forest_symbols f))))
  (decreases length f)
  [SMTPat (forest_symbols (slice f i j))] =
  match length f with
  | 1 -> ()
  | _ ->
    let fs = forest_symbols f in
    let bi = forest_symbols_begin f i in
    if i = 0 then
      if j = length f then
        ()
      else
        let bj = forest_symbols_begin f j in
        if 1 < j then begin
          let fs' = forest_symbols (tail f) in
          let bj' = forest_symbols_begin (tail f) (j - 1) in
          lemma_forest_symbols_slice (tail f) 0 (j - 1);
          assert(equal (symbols f.[0] @| slice fs' 0 bj') (slice fs bi bj))
        end else
          assert(equal (symbols f.[0]) (slice fs bi bj))
    else begin
      let fs' = forest_symbols (tail f) in
      let bi' = forest_symbols_begin (tail f) (i - 1) in
      lemma_forest_symbols_slice (tail f) (i - 1) (j - 1);
      if j < length f then
        let bj = forest_symbols_begin f j in
        let bj' = forest_symbols_begin (tail f) (j - 1) in
        assert(equal (slice fs' bi' bj') (slice fs bi bj))
      else
        assert(equal (slice fs bi (length fs)) (slice fs' bi' (length fs')))
    end
#pop-options

#push-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 1"
let lemma_forest_symbols_remove (f: wf_forest) (i: nat{i < length f}) (s: nat): Lemma
  (ensures
    count s (forest_symbols (remove f i)) ==
    count s (forest_symbols f) - count s (symbols f.[i]) /\
    (count s (forest_symbols (remove f i)) == 1 \/
     count s (forest_symbols (remove f i)) == 0)) =
  if i = 0 then
    lemma_append_count_aux s (symbols f.[0]) (forest_symbols (tail f))
  else if i = length f - 1 then begin
    lemma_forest_symbols_append (unsnoc f) (create 1 (last f));
    calc (==) {
      forest_symbols (create 1 (last f));
      =={}
      symbols (last f) @| forest_symbols (empty #wf_tree);
      =={}
      symbols (last f) @| empty #nat;
      =={append_empty_r (symbols (last f))}
      symbols (last f);
    };
    assert(equal (unsnoc f @| create 1 (last f)) f);
    lemma_append_count_aux s (forest_symbols (unsnoc f)) (symbols (last f))
  end else begin
    let fl = slice f 0 i in
    let fi = create 1 f.[i] in
    let fr = slice f (i + 1) (length f) in
    calc (==) {
      forest_symbols (create 1 f.[i]);
      =={}
      symbols f.[i] @| forest_symbols (empty #wf_tree);
      =={}
      symbols f.[i] @| empty #nat;
      =={append_empty_r (symbols f.[i])}
      symbols f.[i];
    };
    assert(equal (fl @| fi @| fr) f);
    let fs = forest_symbols f in
    let fsl = forest_symbols fl in
    let fsi = forest_symbols fi in
    let fsr = forest_symbols fr in
    append_assoc fsl fsi fsr;
    
    calc (==) {
      count s (forest_symbols (remove f i)) <: int;
      =={lemma_forest_symbols_append fl fr}
      count s (fsl @| fsr);
      =={lemma_append_count_aux s fsl fsr}
      count s fsl + count s fsr;
      =={}
      count s fsl + count s fsi + count s fsr - count s fsi;
      =={}
      ((count s fsl + count s fsi) + count s fsr) - count s fsi;
      =={lemma_append_count_aux s fsl fsi}
      (count s (fsl @| fsi) + count s fsr) - count s fsi;
      =={lemma_append_count_aux s (fsl @| fsi) fsr}
      count s (fsl @| fsi @| fsr) - count s fsi;
      =={lemma_forest_symbols_append_triple fl fi fr}
      count s fs - count s fsi;
    }
  end

let lemma_forest_symbols_remove_gen (f: wf_forest) (i: nat{i < length f}): Lemma
  (requires 2 < length f)
  (ensures (
    let f' = remove f i in
    length f' == length f - 1 /\ no_dup (forest_symbols f')))
  [SMTPat (remove f i)] =
  FStar.Classical.forall_intro (lemma_forest_symbols_remove f i)

#push-options "--fuel 2 --ifuel 2"
let lemma_forest_remove_merge' (f: wf_forest) (i0 i1: nat) (s: nat): Lemma
  (requires i0 <> i1 /\ i0 < length f /\ i1 < length f /\ 2 <= length f)
  (ensures (
    lemma_wf_forest_symbols_disjoint f i0 i1;
    let fs = forest_symbols f in
    let fr = remove (remove f i0) (if i0 < i1 then i1 - 1 else i1) in
    let frm = create 1 (merge f.[i0] f.[i1]) @| fr in
    let fsr = forest_symbols fr in
    let fsr' = forest_symbols frm in
    count s fs == count s fsr')) =
  lemma_wf_forest_symbols_disjoint f i0 i1;
  if length f = 2 then begin
    let t = merge f.[i0] f.[i1] in
    calc (==) {
      forest_symbols (create 1 t);
      =={}
      symbols t @| empty #nat;
      =={append_empty_r (symbols t)}
      symbols t;
      =={}
      symbols f.[i0] @| symbols f.[i1];
    };
    if i0 < i1 then
      assert(forest_symbols f `equal` (symbols f.[i0] @| symbols f.[i1]))
    else
      assert(forest_symbols f `equal` (symbols f.[i1] @| symbols f.[i0]));
    lemma_append_count (symbols f.[i0]) (symbols f.[i1]);
    lemma_append_count (symbols f.[i1]) (symbols f.[i0])
  end else begin
    let fs = forest_symbols f in
    let fr = remove (remove f i0) (if i0 < i1 then i1 - 1 else i1) in
    let fsr = forest_symbols fr in
    let fsr' = forest_symbols (create 1 (merge f.[i0] f.[i1]) @| fr) in
    calc (==) {
      fsr';
      =={lemma_forest_symbols_append (create 1 (merge f.[i0] f.[i1])) fr}
      forest_symbols (create 1 (merge f.[i0] f.[i1])) @| fsr;
      =={}
      (symbols (merge f.[i0] f.[i1]) @| forest_symbols (empty #wf_tree)) @| fsr;
      =={}
      ((symbols f.[i0] @| symbols f.[i1]) @| empty #nat) @| fsr;
      =={append_empty_r (symbols f.[i0] @| symbols f.[i1])}
      (symbols f.[i0] @| symbols f.[i1]) @| fsr;
    };
    calc (==) {
      count s fsr';
      =={lemma_append_count_aux s (symbols f.[i0] @| symbols f.[i1]) fsr}
      count s (symbols f.[i0] @| symbols f.[i1]) + count s fsr;
      =={lemma_append_count_aux s (symbols f.[i0]) (symbols f.[i1])}
      count s (symbols f.[i0]) + count s (symbols f.[i1]) + count s fsr;
      =={
        lemma_forest_symbols_remove f i0 s;
        lemma_forest_symbols_remove (remove f i0) (if i0 < i1 then i1 - 1 else i1) s
      }
      count s (symbols f.[i0]) + count s (symbols f.[i1]) +
      (count s fs - count s (symbols f.[i0]) - count s (symbols f.[i1]));
      =={}
      count s fs;
    }
  end
#pop-options

let lemma_forest_remove_merge (f: wf_forest) (i0 i1: nat): Lemma
  (requires i0 <> i1 /\ i0 < length f /\ i1 < length f /\ 2 <= length f)
  (ensures (
    lemma_wf_forest_symbols_disjoint f i1 i0;
    let fs = forest_symbols f in
    let fr = remove (remove f i0) (if i0 < i1 then i1 - 1 else i1) in
    let fsr = forest_symbols fr in
    let fsr' = forest_symbols (create 1 (merge f.[i0] f.[i1]) @| fr) in
    permutation nat fs fsr')) =
  lemma_wf_forest_symbols_disjoint f i1 i0;
  let open FStar.Classical in
  forall_intro (move_requires (lemma_forest_remove_merge' f i0 i1))

#push-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 1"
let forest_reduce (f: wf_forest{length f >= 2}): Tot (f': wf_forest{
  length f' == length f - 1 /\
  permutation nat (forest_symbols f) (forest_symbols f')
}) =
  let (i0, i1) = min_freq_2 f in
  lemma_wf_forest_symbols_disjoint f i0 i1;
  lemma_forest_remove_merge f i0 i1;
  match length f with
  | 2 -> create 1 (merge f.[i0] f.[i1])
  | _ ->
    let t' = merge f.[i0] f.[i1] in
    let f' = remove f i0 in
    let f'' = remove f' (if i0 < i1 then i1 - 1 else i1) in
    create 1 t' @| f''
#pop-options

let rec leaf_count (t: tree): Tot pos = 
  match t with
  | Node l _ r -> leaf_count l + leaf_count r
  | _ -> 1

let max_leaf_count (t: tree): Tot pos = pow2 (height t)

let rec bit_length (t: tree) (h: nat): Tot nat =
  match t with
  | Node l _ r ->
    if h = 0 then 0 else bit_length l (h - 1) + bit_length r (h - 1)
  | _ ->
    if h = 0 then 1 else 0

val lemma_max_leaf_count: (t: tree) -> Lemma
  (ensures leaf_count t <= max_leaf_count t)

val lemma_non_full_bit_length: (t: tree) -> (h: nat) -> Lemma
  (requires leaf_count t < pow2 h)
  (ensures exists i. i < h /\ bit_length t i > 0)

let rec lemma_leaf_count_height (t: tree): Lemma
  (ensures height t < leaf_count t)
  [SMTPat (height t)] =
  match t with
  | Node l _ r ->
    lemma_leaf_count_height l;
    lemma_leaf_count_height r
  | _ -> ()

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
