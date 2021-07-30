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
