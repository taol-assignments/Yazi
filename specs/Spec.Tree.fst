module Spec.Tree

module BV = FStar.BitVector
module Math = FStar.Math.Lemmas

open Lib.UInt

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let height_one t =
  if Leaf? t then
    assert_norm(height t == 0)
  else
    if Leaf? (left t) then
      if Leaf? (right t) then
        ()
      else
        assert_norm(height (right t) >= 1)
    else
      assert_norm(height (left t) >= 1)

let height_gt_one t =
  match t with
  | Root _ _ _ ->
    if height (left t) < 1 then
      assert_norm(height (right t) >= 1)
    else
      assert_norm(height (left t) >= 1)
  | Internal _ _ _ _ ->
    if height (left t) < 1 then
      assert_norm(height (right t) >= 1)
    else
      assert_norm(height (left t) >= 1)
  | Leaf _ _ _ -> ()

#set-options "--z3refresh --z3rlimit 512 --fuel 2 --ifuel 2 --z3seed 11"
let rec leaf_count_gt_height t h =
  match height t with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    assert_norm(
      leaf_count t h == leaf_count (left t) (h - 1) + leaf_count (right t) (h - 1));
    leaf_count_gt_height (left t) (h - 1);
    leaf_count_gt_height (right t) (h - 1)

let rec do_total_leaf_count_gt_height (t: well_formed_tree) (h: pos): Lemma
  (requires h >= height t)
  (ensures do_total_leaf_count t h == do_total_leaf_count t (height t)) =
  if h = height t + 1 || h = height t then
    ()
  else
    calc (==) {
      do_total_leaf_count t h;
      =={}
      do_total_leaf_count t (h - 1);
      =={do_total_leaf_count_gt_height t (h - 1)}
      do_total_leaf_count t (height t);
    }

let rec do_total_leaf_count_lr (t: well_formed_tree) (h: pos): Lemma
  (requires Leaf? t == false /\ 1 < h /\ h <= height t)
  (ensures do_total_leaf_count t h ==
    do_total_leaf_count (left t) (h - 1) + do_total_leaf_count (right t) (h - 1)) =
  if h > 2 then
    calc (==) {
      do_total_leaf_count t h;
      =={do_total_leaf_count_lr t (h - 1)}
      leaf_count (left t) (h - 1) + leaf_count (right t) (h - 1) +
      do_total_leaf_count (left t) (h - 2) + do_total_leaf_count (right t) (h - 2);
      =={}
      leaf_count (left t) (h - 1) + do_total_leaf_count (left t) (h - 2) +
      leaf_count (right t) (h - 1) + do_total_leaf_count (right t) (h - 2);
      =={
        Math.paren_add_right 
          (leaf_count (left t) (h - 1) + do_total_leaf_count (left t) (h - 2))
          (leaf_count (right t) (h - 1))
          (do_total_leaf_count (right t) (h - 2))
      }
      do_total_leaf_count (left t) (h - 1) + do_total_leaf_count (right t) (h - 1);
    }
  else
    calc (==) {
      do_total_leaf_count t 2;
      =={}
      leaf_count (left t) 1 + leaf_count (right t) 1 +
      do_total_leaf_count t 1;
      =={}
      leaf_count (left t) 1 + leaf_count (right t) 1 +
      leaf_count t 1 +
      do_total_leaf_count t 0;
      =={assert_norm(do_total_leaf_count t 0 == 0)}
      leaf_count (left t) 1 + leaf_count (right t) 1 + leaf_count t 1;
      =={}
      leaf_count (left t) 1 + leaf_count (left t) 0 + 
      leaf_count (right t) 1 + leaf_count (right t) 0;
      =={
        Math.paren_add_right
          (leaf_count (left t) 1 + leaf_count (left t) 0)
          (leaf_count (right t) 1)
          (leaf_count (right t) 0)
      }
      leaf_count (left t) 1 + leaf_count (left t) 0 + 
      (leaf_count (right t) 1 + leaf_count (right t) 0);
      =={}
      do_total_leaf_count (left t) 1 + do_total_leaf_count (right t) 1;
    }

let total_leaf_count_lr t =
  match height t with
  | 1 -> ()
  | _ ->
    calc (==) {
      total_leaf_count t;
      =={}
      do_total_leaf_count t (height t);
      =={do_total_leaf_count_lr t (height t)}
      do_total_leaf_count (left t) (height t - 1) +
      do_total_leaf_count (right t) (height t - 1);
      =={
        do_total_leaf_count_gt_height (left t) (height t - 1);
        do_total_leaf_count_gt_height (right t) (height t - 1)
      }
      do_total_leaf_count (left t) (height (left t)) +
      do_total_leaf_count (right t) (height (right t));
      =={}
      total_leaf_count (left t) + total_leaf_count (right t);
    }

let rec total_leaf_count_lower_bound t =
  match height t with
  | 0 -> ()
  | 1 -> assert_norm(total_leaf_count t == 2)
  | _ ->
    total_leaf_count_lr t;
    total_leaf_count_lower_bound (right t);
    total_leaf_count_lower_bound (left t)

let rec total_leaf_count_upper_bound t =
  match height t with
  | 0 -> ()
  | 1 -> assert_norm(total_leaf_count t == pow2 1)
  | _ ->
    total_leaf_count_lr t;
    total_leaf_count_upper_bound (right t);
    total_leaf_count_upper_bound (left t);
    if height (left t) < height (right t) then
      Math.pow2_le_compat (height t - 1) (height (left t))
    else
      Math.pow2_le_compat (height t - 1) (height (right t))

let rec min_leaf_depth_leaf_count t =
  match height t with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    min_leaf_depth_leaf_count (left t);
    min_leaf_depth_leaf_count (right t)

let rec min_leaf_depth_lt_pow2 t h =
  match height t with
  | 0 -> ()
  | 1 -> ()
  | _ ->
    if total_leaf_count (left t) < pow2 (h - 1) then
      min_leaf_depth_lt_pow2 (left t) (h - 1)
    else
      min_leaf_depth_lt_pow2 (right t) (h - 1)

let rec code_do_decode_cancel (rt: root) (t: non_leaf) (sym: tree_symbol t): Lemma
  (ensures (match do_decode rt t (code t sym) with
  | Some s -> equal s (create 1 sym)
  | None -> False)) =
  let c = code t sym in let l = left t in let r = right t in
  if Seq.mem sym (symbol_seq l) then
    if Leaf? l then
      ()
    else begin
      assert(equal c (create 1 false @| code l sym));
      assert(equal (tail c) (code l sym));
      code_do_decode_cancel rt l sym
    end
  else
    if Leaf? r then
      ()
    else begin
      assert(equal c (create 1 true @| code r sym));
      assert(equal (tail c) (code r sym));
      code_do_decode_cancel rt r sym
    end

let rec do_decode_append (rt: root) (t: well_formed_tree) (a b: seq bool) (sym: nat): Lemma
  (requires do_decode rt t a = Some (create 1 sym))
  (ensures Seq.length b > 0 ==>
    do_decode rt t (a @| b) == (match do_decode rt rt b with
    | Some res -> Some ((create 1 sym) @| res)
    | None -> None))
  (decreases (%[Seq.length a; if Seq.length a > 0 then 1 else 0])) =
  if Leaf? t then
    if Seq.length a = 0 then begin
      lemma_empty a;
      append_empty_l b
    end else
      ()
  else
    if Seq.length a = 0 then
      ()
    else begin
      let t' = if head a then right t else left t in
      assert(equal (tail (a @| b)) ((tail a) @| b));
      do_decode_append rt t' (tail a) b sym
    end

let decode_append (r: root) (a b: seq bool) (sym: nat): Lemma
  (requires decode r a == Some (create 1 sym) /\ Seq.length b > 0)
  (ensures decode r (a @| b) == (match decode r b with
  | Some res -> Some ((create 1 sym) @| res)
  | None -> None)) =
  do_decode_append r r a b sym

#push-options "--fuel 2 --ifuel 2"
let seq_create_tail_eq (#t: Type) (s: seq t): Lemma
  (requires Seq.length s > 0)
  (ensures create 1 (head s) @| tail s == s) =
  let s' = create 1 (head s) @| tail s in assert(equal s s')
#pop-options

let rec encode_decode_cancel r s =
  code_do_decode_cancel r r s.[0];
  if Seq.length s > 1 then begin
    encode_decode_cancel r (tail s);
    decode_append r (code r s.[0]) (encode r (tail s)) s.[0]
  end else
    ();
  match (decode r (encode r s)) with
  | Some res ->
    seq_create_tail_eq s;
    assert(equal s res)
  | None -> ()

let rec code_height t s =
  match height t with
  | 1 -> ()
  | _ ->
    let l = left t in let r = right t in
    if Seq.mem s (symbol_seq l) then
      if Leaf? l then () else code_height l s
    else
      if Leaf? r then () else code_height r s

#set-options "--z3refresh --z3rlimit 512 --fuel 2 --ifuel 2"
let rec symbol_seq_len_aux t =
  match height t with
  | 1 -> ()
  | _ ->
    if Leaf? (left t) then () else symbol_seq_len_aux (left t);
    if Leaf? (right t) then () else symbol_seq_len_aux (right t)

#set-options "--z3refresh --z3rlimit 512 --fuel 1 --ifuel 1"
let rec leftmost_code_vec t depth =
  match height t with
  | 1 -> ()
  | _ ->
    let l = left t in
    let h = (symbol_seq t).[0] in
    if depth = 1 then
      ()
    else begin
      leftmost_code_vec l (depth - 1);
      assert(equal
        (create 1 false @| code_partial l h (depth - 1))
        (BV.zero_vec #depth))
    end

#set-options "--z3refresh --z3rlimit 512 --fuel 2 --ifuel 2"
let rec rightmost_code_vec t depth =
  match height t with
  | 1 -> ()
  | _ ->
    let r = right t in
    let e = last (symbol_seq t) in
    if depth = 1 then
      ()
    else begin
      rightmost_code_vec r (depth - 1);
      assert(equal
        (create 1 true @| code_partial r e (depth - 1))
        (BV.ones_vec #depth))
    end

#set-options "--z3refresh --z3rlimit 2048 --fuel 1 --ifuel 1 --z3seed 14"
let rec code_partial_next t i =
  match height t with
  | 1 -> ()
  | _ ->
    let l = left t in let r = right t in
    let ts = symbol_seq t in
    let (s, s') = (ts.[i], ts.[i + 1]) in
    let ls = symbol_seq l in let rs = symbol_seq r in
    let zero = BV.zero_vec #1 in
    let one = BV.ones_vec #1 in
    let depth = code_len t ts.[i] in
    let depth' = depth - 1 in
    calc (==) {
      ((pow2 1) - 1) * pow2 depth';
      =={assert_norm((pow2 1) - 1 == 1)}
      pow2 depth';
    };
    Math.pow2_double_mult depth';

    if depth = 1 then
      ()
    else if i + 1 < total_leaf_count l then begin
      zero_prefix_vec 1 (code_partial l ls.[i] depth');
      zero_prefix_vec 1 (code_partial l ls.[i + 1] depth');
      code_partial_next l i
    end else if total_leaf_count l <= i then
      let i' = i - total_leaf_count l in
      calc (==) {
        UInt.from_vec (code t ts.[i]) + 1;
        =={}
        UInt.from_vec #depth (one @| code r rs.[i']) + 1;
        =={one_prefix_vec 1 (code r rs.[i'])}
        pow2 depth' + (UInt.from_vec (code r rs.[i']) + 1);
        =={code_partial_next r i'}
        pow2 depth' + UInt.from_vec (code_partial r rs.[i' + 1] depth');
        =={one_prefix_vec 1 (code_partial r rs.[i' + 1] depth')}
        UInt.from_vec #depth (one @| code_partial r rs.[i' + 1] depth');
        =={}
        UInt.from_vec (code_partial t ts.[i + 1] depth);
      }
    else
      calc (==) {
        UInt.from_vec (code t ts.[i]) + 1;
        =={}
        UInt.from_vec #depth (zero @| code l ls.[i]) + 1;
        =={symbol_seq_len_aux l}
        UInt.from_vec #depth (zero @| code l (last ls)) + 1;
        =={rightmost_code_val l depth'}
        pow2 (code_len l (last ls));
        =={}
        pow2 depth';
        =={UInt.pow2_from_vec_lemma #depth 0}
        UInt.from_vec (BV.elem_vec #depth 0);
        =={
          leftmost_code_vec r depth';
          assert(equal (BV.elem_vec #depth 0) (one @| code_partial r rs.[0] depth'))
        }
        UInt.from_vec #depth (one @| code_partial r rs.[0] depth');
        =={}
        UInt.from_vec (code_partial t ts.[i + 1] depth);
      }

#push-options "--fuel 0 --ifuel 0"
let total_leaf_count_aux (t: non_leaf) (i n: int): Lemma
  (requires i <= total_leaf_count t - n)
  (ensures i - total_leaf_count (left t) <= total_leaf_count (right t) - n) = ()
#pop-options

let height_lt (t: non_leaf): Lemma
  (ensures height (left t) < height t /\ height (right t) < height t)
  [SMTPatOr [
    [SMTPat (height (left t))];
    [SMTPat (height (right t))]
  ]] = ()

let code_len_subtree (t: non_leaf) (s: tree_symbol t): Lemma
  (ensures
    (mem s (symbol_seq (left t)) ==>
      (Leaf? (left t) ==> code_len t s == 1) /\
      (Leaf? (left t) == false ==> code_len t s == 1 + code_len (left t) s)) /\
    (mem s (symbol_seq (right t)) ==> 
     (Leaf? (right t) ==> code_len t s == 1) /\
     (Leaf? (right t) == false ==> code_len t s == 1 + code_len (right t) s)))
  [SMTPatOr [
    [SMTPat (code_len (left t) s)];
    [SMTPat (code_len (right t) s)];
    [SMTPat (code_len t s)]
  ]] = ()

#push-options "--z3seed 131 --fuel 1 --ifuel 1"
let rec non_rightmost_upper_bound t i =
  match height t with
  | 1 -> ()
  | _ ->
    let s = (symbol_seq t).[i] in
    let l = left t in let r = right t in
    let ls = symbol_seq l in let rs = symbol_seq r in
    let depth = code_len t s in
    if depth = 1 then
      assert_norm(UInt.from_vec (code t s) == 0)
    else if mem s ls then begin
      if Leaf? l then
        assert(code_len t s == 1)
      else begin
        zero_prefix_vec 1 (code l s);
        Math.pow2_lt_compat depth (depth - 1);
        assert(i < total_leaf_count l);
        if i = total_leaf_count l - 1 then 
          rightmost_code_val l (code_len l s)
        else
          non_rightmost_upper_bound l i
      end
    end else
      if Leaf? r then
        assert(code_len t s == 1)
      else begin
        let i' = i - total_leaf_count l in
        total_leaf_count_aux t i 2;
        code_len_subtree t s;
        non_rightmost_upper_bound r i';
        one_prefix_vec 1 (code r s);
        assert_norm(pow2 1 - 1 == 1);
        Math.mul_one_left_is_same (pow2 (depth - 1));
        Math.pow2_double_sum (depth - 1)
      end
#pop-options

let rec code_len_lt_aux t i =
  match height t with
  | 1 -> ()
  | _ ->
    let (s, s') = ((symbol_seq t).[i], (symbol_seq t).[i + 1]) in
    let (l, ls) = (left t, symbol_seq (left t)) in
    if Seq.mem s' ls then
      ()
    else
      let (r, rs) = (right t, symbol_seq (right t)) in
      if Seq.mem s rs then begin
        total_leaf_count_aux t i 1;
        code_len_lt_aux r (i - total_leaf_count l)
      end else
        ()

let rec code_len_upper_bound t i =
  let s = (symbol_seq t).[i] in
  match height t with
  | 1 -> ()
  | _ ->
    let l = left t in let ls = symbol_seq l in
    if mem s (symbol_seq (left t)) then
      if Leaf? l then () else code_len_upper_bound l i
    else
      let r = right t in let rs = symbol_seq r in
      if Leaf? r then () else code_len_upper_bound r (i - total_leaf_count l)

let code_upper_bound t i =
  let s = (symbol_seq t).[i] in
  code_len_upper_bound t i;
  Math.pow2_le_compat (height t) (code_len t s);
  if i <= total_leaf_count t - 2 then
    non_rightmost_upper_bound t i
  else
    rightmost_code_val t (code_len t s)

let total_leaf_count_left_aux (t: non_leaf) (i: nat): Lemma
  (requires i < total_leaf_count (left t))
  (ensures
    mem (symbol_seq t).[i] (symbol_seq (left t)) /\
    (Leaf? (left t) == false ==> 
      code t (symbol_seq t).[i] ==
      BV.zero_vec #1 @| code (left t) (symbol_seq t).[i])) = ()

let total_leaf_count_right_aux (t: non_leaf) (i: nat): Lemma
  (requires i < total_leaf_count t /\ total_leaf_count (left t) <= i)
  (ensures
    mem (symbol_seq t).[i] (symbol_seq (right t)) /\
    (Leaf? (right t) == false ==>
      code t (symbol_seq t).[i] ==
      BV.ones_vec #1 @| code (right t) (symbol_seq t).[i])) = ()

let symbol_seq_left_index (t: non_leaf) (i: nat): Lemma
  (requires
    i < total_leaf_count (left t) /\
    mem (symbol_seq t).[i] (symbol_seq (left t)))
  (ensures (symbol_seq (left t)).[i] == (symbol_seq t).[i]) = ()

let symbol_seq_right_index (t: non_leaf) (i: nat): Lemma
  (requires
    i < total_leaf_count t /\ total_leaf_count (left t) <= i /\
    mem (symbol_seq t).[i] (symbol_seq (right t)))
  (ensures (symbol_seq (right t)).[i - total_leaf_count (left t)] == (symbol_seq t).[i]) = ()

#set-options "--z3refresh --z3rlimit 4096 --fuel 0 --ifuel 0 --z3seed 13"
let uint_t_code_left (t: non_leaf) (n: pos{n >= height t})  (i: nat): Lemma
  (requires Leaf? (left t) == false /\ i < Seq.length (symbol_seq (left t)))
  (ensures uint_t_code t n i == uint_t_code (left t) n i) =
  let s = (symbol_seq t).[i] in
  let l = left t in
  let depth = code_len t s in
  total_leaf_count_left_aux t i;
  symbol_seq_left_index t i;
  if n > depth then begin
    append_assoc (BV.zero_vec #(n - depth)) (BV.zero_vec #1) (code l s);
    assert(equal
      (BV.zero_vec #(n - depth) @| BV.zero_vec #1)
      (BV.zero_vec #(n - depth + 1)))
  end else
    ()

let uint_t_code_right (t: non_leaf) (n: pos{n >= height t}) (i: nat): Lemma
  (requires
    Leaf? (right t) == false /\
    i < total_leaf_count t /\ i >= total_leaf_count (left t))
  (ensures 
    uint_t_code t n i ==
      pow2 (code_len (right t) (symbol_seq (right t)).[i - total_leaf_count (left t)]) +
      uint_t_code (right t) n (i - total_leaf_count (left t))) =
  let s = (symbol_seq t).[i] in
  let (l, r) = (left t, right t) in
  let depth = code_len t s in
  let i' = i - total_leaf_count l in
  total_leaf_count_right_aux t i;
  symbol_seq_right_index t i;
  if n > depth then begin
    calc (==) {
      UInt.from_vec #n (BV.zero_vec #(n - depth) @| (BV.ones_vec #1 @| code r s));
      =={zero_prefix_vec (n - depth) (BV.ones_vec #1 @| code r s)}
      UInt.from_vec #depth (BV.ones_vec #1 @| code r s);
      =={one_prefix_vec 1 (code r s)}
      pow2 (depth - 1) + UInt.from_vec (code r s);
    };
    zero_prefix_vec (n - depth + 1) (code r s)
  end else
    ()

let pow2_code_len_aux (t: non_leaf) (i: nat): Lemma
  (requires
    i < total_leaf_count t - 1 /\
    code_len t (symbol_seq t).[i] <= code_len t (symbol_seq t).[i + 1])
  (ensures
    pow2 ((code_len t (symbol_seq t).[i + 1]) - 1) ==
    pow2 ((code_len t (symbol_seq t).[i]) - 1) *
    pow2 ((code_len t (symbol_seq t).[i + 1]) - (code_len t (symbol_seq t).[i]))) =
  let s = (symbol_seq t).[i] in
  let s' = (symbol_seq t).[i + 1] in
  let depth = code_len t s in
  let depth' = code_len t s' in
  let diff = depth' - depth in
  calc (==) {
    pow2 (depth' - 1);
    =={
      calc (==) {
        depth - 1 + diff;
        =={Math.subtraction_is_distributive depth 1 diff}
        (depth - 1) + diff;
        =={Math.swap_add_plus_minus depth diff 1}
        depth + diff - 1;
        =={}
        depth + (depth' - depth) - 1;
        =={}
        depth - (depth - depth') - 1;
        =={}
        depth' - 1;
      }
    }
    pow2 ((depth - 1) + diff);
    =={Math.pow2_plus (depth - 1) diff}
    (pow2 (depth - 1)) * pow2 diff;
  }

let minus_plus (a n: int): Lemma (ensures a - n + n == a) = ()

#push-options "--z3refresh --z3rlimit 4096 --fuel 1 --ifuel 1 --z3seed 414"
let code_next_aux (t: non_leaf) (n: pos{n >= height t}) (i: nat): Lemma
  (requires
    canonical_common_cond t i /\
    i + 1 == total_leaf_count (left t))
  (ensures
    uint_t_code t n i < pow2 n - 1 /\
    uint_t_code t n (i + 1) ==
    UInt.shift_left
      ((uint_t_code t n i) + 1)
      (code_len t (symbol_seq t).[i + 1] - code_len t (symbol_seq t).[i])) =
  let s = (symbol_seq t).[i] in let s' = (symbol_seq t).[i + 1] in
  let depth = code_len t s in let depth' = code_len t s' in
  let diff = depth' - depth in
  let l = left t in let r = right t in
  total_leaf_count_left_aux t i;
  total_leaf_count_right_aux t (i + 1);
  if depth = 1 then begin
    assert(uint_t_code t n i == (pow2 (depth - 1)) - 1)
  end else begin
    leftmost_code_vec r (depth' - 1);
    rightmost_code_vec l (depth - 1);
    assert(UInt.from_vec (code r s') == 0);
    if n = depth then
      calc (==) {
        uint_t_code t n i;
        =={}
        UInt.from_vec (code l s);
        =={rightmost_code_vec l (depth - 1)}
        (pow2 (depth - 1)) - 1;
      }
    else begin
      zero_prefix_vec (n - depth) (code t s);
      zero_prefix_vec 1 (code l s);
      assert(uint_t_code t n i == (pow2 (depth - 1)) - 1)
    end
  end;
  assert(uint_t_code t n i == (pow2 (depth - 1)) - 1);
  if depth' = 1 then
    assert(uint_t_code t n (i + 1) == 1)
  else begin
    let c = BV.ones_vec #1 @| code r s' in
    assert((BV.elem_vec #depth' 0).[0] == 
      (BV.ones_vec #1 @| BV.zero_vec #(depth' - 1)).[0]);
    assert(forall i. i > 0 ==>
      (BV.elem_vec #depth' 0).[i] ==
      (BV.ones_vec #1 @| BV.zero_vec #(depth' - 1)).[i]);
    assert(equal
      (BV.ones_vec #1 @| BV.zero_vec #(depth' - 1))
      (BV.elem_vec #depth' 0));
    Math.pow2_lt_compat n (depth - 1);
    Math.pow2_lt_compat n (depth' - 1);
    calc (==) {
      uint_t_code t n (i + 1) <: int;
      =={}
      UInt.from_vec #depth' (BV.ones_vec #1 @| code r s') <: int;
      =={leftmost_code_vec r (depth' - 1)}
      UInt.from_vec #depth' (BV.ones_vec #1 @| BV.zero_vec #(depth' - 1)) <: int;
      =={
        lemma_eq_elim
          (BV.ones_vec #1 @| BV.zero_vec #(depth' - 1))
          (BV.elem_vec #depth' 0)
      }
      UInt.from_vec #depth' (BV.elem_vec #depth' 0) <: int;
      =={UInt.pow2_from_vec_lemma #depth' 0}
      pow2 (depth' - 1) <: int;
      =={Math.modulo_lemma (pow2 (depth' - 1)) (pow2 n)}
      pow2 (depth' - 1) % pow2 n <: int;
      =={pow2_code_len_aux t i}
      pow2 (depth - 1) * pow2 diff % pow2 n <: int;
    };
    UInt.shift_left_value_lemma #n (pow2 (depth - 1)) diff;
    minus_plus (pow2 (depth - 1)) 1
  end
#pop-options

#set-options "--z3refresh --z3rlimit 65536 --fuel 0 --ifuel 0 --z3seed 23" // 10
let rec code_next t n i =
  let ts = symbol_seq t in let s = ts.[i] in let s' = ts.[i + 1] in
  let depth = code_len t s in let depth' = code_len t s' in
  let diff = depth' - depth in
  non_rightmost_upper_bound t i;
  if n > depth then begin
    Math.pow2_lt_compat n depth;
    zero_prefix_vec (n - depth) (code t s)
  end else
    ();
  let l = left t in
  if depth = code_len t s' then
    code_partial_next t i
  else if i + 1 < total_leaf_count l then
    if Leaf? l then
      ()
    else begin
      total_leaf_count_left_aux t i;
      total_leaf_count_left_aux t (i + 1);
      symbol_seq_left_index t i;
      symbol_seq_left_index t (i + 1);
      code_next l n i;
      calc (==) {
        uint_t_code t n (i + 1);
        =={uint_t_code_left t n (i + 1)}
        uint_t_code l n (i + 1);
        =={}
        UInt.shift_left ((uint_t_code l n i) + 1) diff;
        =={uint_t_code_left t n i}
        UInt.shift_left ((uint_t_code t n i) + 1) diff;
      }
    end
  else if total_leaf_count l <= i then
    let r = right t in 
    if Leaf? r then
      ()
    else begin
      let i' = i - total_leaf_count l in
      total_leaf_count_right_aux t i;
      total_leaf_count_right_aux t (i + 1);
      symbol_seq_right_index t i;
      symbol_seq_right_index t (i + 1);
      code_next r n i';
      uint_t_code_right t n (i + 1);
      uint_t_code_right t n i;
      
      non_rightmost_upper_bound r i';
      Math.pow2_plus (depth - 1) diff;
      Math.lemma_mult_lt_right (pow2 diff) (1 + uint_t_code r n i') (pow2 (depth - 1));
      pow2_code_len_aux t i;
      Math.pow2_lt_compat n (depth' - 1);
      // (1 + uint_t_code r n i') * pow2 diff < pow2 (depth' - 1) < pow2 n

      Math.pow2_lt_compat n (depth - 1);
      Math.modulo_lemma ((1 + uint_t_code r n i') * pow2 diff) (pow2 n);
      UInt.shift_left_value_lemma #n (1 + uint_t_code r n i') diff;
      // uint_t_code r n (i' + 1) == (1 + uint_t_code r n i') * pow2 diff
      // assert(uint_t_code r n (i' + 1) == (1 + uint_t_code r n i') * pow2 diff);

      pow2_code_len_aux t i;
      Math.distributivity_add_left
        (pow2 (depth - 1))
        (1 + uint_t_code r n i')
        (pow2 diff);
      Math.modulo_lemma ((pow2 (depth - 1) + 1 + uint_t_code r n i') * pow2 diff) (pow2 n);
      UInt.shift_left_value_lemma #n (pow2 (depth - 1) + 1 + uint_t_code r n i') diff
    end
  else
    code_next_aux t n i
