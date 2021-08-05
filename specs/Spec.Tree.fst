module Spec.Tree

module Math = FStar.Math.Lemmas

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

#set-options "--z3rlimit 512 --fuel 2 --ifuel 2"
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
  lemma_mem_append (symbol_seq l) (symbol_seq r);
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

let rec encode_decode_cancel r s =
  code_do_decode_cancel r r s.[0];
  if Seq.length s > 1 then begin
    encode_decode_cancel r (tail s);
    decode_append r (code r s.[0]) (encode r (tail s)) s.[0]
  end else
    ();
  match (decode r (encode r s)) with
  | Some res -> assert(equal s res)
  | None -> ()

#set-options "--z3rlimit 200"
let rec kraft_sum_non_root t =
  match t with
  | Internal _ len l r ->
    calc (=$) {
      kraft_sum t;
      =={}
      kraft_sum l +$ kraft_sum r;
      =${
        kraft_sum_non_root l;
        kraft_sum_non_root r
      }
      kraft_term (len + 1) +$ kraft_term (len + 1);
    };
    calc (=$) {
      kraft_term (len + 1) +$ kraft_term (len + 1);
      =${
        assert_norm(len + 1 - 1 == len);
        kraft_term_plus (len + 1)
      }
      kraft_term len;
    }
  | Leaf _ len _ -> ()

let kraft_sum_root t =
  match t with
  | Root _ l r ->
    kraft_sum_non_root l;
    kraft_sum_non_root r
