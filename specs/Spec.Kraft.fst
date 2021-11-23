module Spec.Kraft

module Math = FStar.Math.Lemmas

open FStar.Seq
open FStar.Mul
open Lib.Seq
open Lib.Rational

let rec lemma_max_leaf_count t =
  match t with
  | Node l _ r ->
    lemma_max_leaf_count l;
    lemma_max_leaf_count r;
    Math.pow2_le_compat (height t - 1) (height l);
    Math.pow2_le_compat (height t - 1) (height r)
  | _ -> ()

let rec bit_length_upper_bound (t: tree) (h: nat): Lemma
  (ensures bit_length t h <= pow2 h)
  [SMTPat (bit_length t h)] =
  match (height t, h) with
  | (0, _) | (_, 0) -> ()
  | _ ->
    bit_length_upper_bound (left t) (h - 1);
    bit_length_upper_bound (right t) (h - 1)

let rec lemma_non_full_bit_length t h =
  match (height t, h) with
  | (0, _) | (_, 0) -> ()
  | _ ->
    let l = left t in let r = right t in let h' = h - 1 in
    assert(leaf_count l < pow2 h' \/ leaf_count r < pow2 h');
    if leaf_count l < pow2 h' then begin
      lemma_non_full_bit_length l h';
      assert(exists i. i < h' /\ bit_length l i > 0 /\ (i + 1) < h /\ bit_length t (i + 1) > 0)
    end;
    if leaf_count r < pow2 h' then begin
      lemma_non_full_bit_length r h';
      assert(exists i. i < h' /\ bit_length r i > 0 /\ (i + 1) < h /\ bit_length t (i + 1) > 0)
    end

#set-options "--z3refresh --z3rlimit 32 --fuel 1 --ifuel 0"
let rec lemma_kraft_sorted sym len i j =
  match length len with
  | 2 -> ()
  | _ ->
    let len' = tail len in let sym' = tail sym in
    cons_head_tail sym;
    assert(forall k. {:pattern len.[k] \/ len'.[k - 1]} k > 0 ==> len.[k] == len'.[k - 1]);
    if 0 < i then
      lemma_kraft_sorted sym' len' (i - 1) (j - 1)
    else if i < j then
      lemma_kraft_sorted sym' len' 0 (j - 1)
    else
      ()
#reset-options

let kraft_code_rat (sym: sym_seq) (len: len_seq) (i: nat): Pure rat
  (requires kraft_cond sym len /\ i < length len)
  (ensures fun _ -> True) =
  if i = 0 then
    zero
  else
    sigma 0 (i - 1) (fun j -> (pow2 len.[i], pow2 len.[j]))

let lemma_kraft_code_rat_distr (sym: sym_seq) (len: len_seq) (i: pos): Lemma
  (requires kraft_cond sym len /\ i < length len)
  (ensures
    kraft_code_rat sym len i =$
    of_int (pow2 len.[i]) *$ sigma 0 (i - 1) (fun j -> 1, pow2 len.[j])) =
  sigma_mul_distributivity 
    0 (i - 1) (of_int (pow2 len.[i]))
    (fun j -> (pow2 len.[i], pow2 len.[j]))
    (fun j -> (1, pow2 len.[j]))

let lemma_kraft_term_gt_zero (l: pos): Lemma
  (ensures zero <$ (1, pow2 l))
  [SMTPat (1, pow2 l)] = ()

#set-options "--z3refresh --z3rlimit 128 --fuel 0 --ifuel 0"
let lemma_kraft_code_rat_upper_bound
  (sym: sym_seq) (len: len_seq) (i: nat): Lemma
  (requires kraft_cond sym len /\ i < length len)
  (ensures kraft_code_rat sym len i <$ (of_int (pow2 len.[i]))) =
  let f = fun j -> 1, pow2 len.[j] in
  let c = of_int (pow2 len.[i]) in
  if 0 < i then
    calc (<$) {
      kraft_code_rat sym len i;
      =={}
      sigma 0 (i - 1) (fun j -> (pow2 len.[i], pow2 len.[j]));
      =${lemma_kraft_code_rat_distr sym len i}
      c *$ sigma 0 (i - 1) (fun j -> 1, pow2 len.[j]);
      =${sigma_extensionality 0 (i - 1)  (fun j -> 1, pow2 len.[j]) f}
      c *$ sigma 0 (i - 1) f;
      <${
        calc (<$) {
          sigma 0 (i - 1) f;
          <${sigma_pos_lt 0 (i - 1) (length len - 1) f}
          sigma 0 (length len - 1) f;
          =${}
          kraft_sum len;
          <=${}
          one;
        }
      }
      c;
    }

#set-options "--z3refresh --z3rlimit 128 --fuel 1 --ifuel 0"
let rec lemma_kraft_code_rat_nat
  (sym: sym_seq) (len: len_seq) (i j: nat): Lemma
  (requires kraft_cond sym len /\ i < j /\ j < length len)
  (ensures
    sigma i (j - 1) (fun k -> (pow2 len.[j], pow2 len.[k])) =$
    of_int (do_kraft_code sym len i j))
  (decreases j - i) =
  calc (<=) {
    len.[i];
    <={lemma_kraft_sorted sym len i j}
    len.[j];
  };
  match j - i with
  | 1 ->
    calc (=$) {
      sigma i (j - 1) (fun k -> pow2 len.[j], pow2 len.[k]);
      =={}
      (pow2 len.[j], pow2 len.[i]);
      =${pow2_subtraction len.[j] len.[i]}
      (pow2 (len.[j] - len.[i]), 1);
      =={}
      of_int (do_kraft_code sym len i j);
    }
  | _ ->
    let f (k: nat{i <= k /\ k <= j - 1}): Tot rat =
      pow2 len.[j], pow2 len.[k]
    in
    lemma_kraft_code_rat_nat sym len (i + 1) j;
    sigma_extensionality (i + 1) (j - 1) f (fun k -> (pow2 len.[j], pow2 len.[k]));
    calc (=$) {
      sigma i (j - 1) f;
      =${}
      (pow2 len.[j], pow2 len.[i]) +$ of_int (do_kraft_code sym len (i + 1) j);
      =${pow2_subtraction len.[j] len.[i]}
      (pow2 (len.[j] - len.[i]), 1) +$ of_int (do_kraft_code sym len (i + 1) j);
      =={}
      (pow2 (len.[j] - len.[i]) + do_kraft_code sym len (i + 1) j, 1);
      =={}
      of_int (do_kraft_code sym len i j);
    }

let lemma_kraft_code_upper_bound sym len i =
  if i > 0 then begin
    lemma_kraft_code_rat_nat sym len 0 i;
    lemma_kraft_code_rat_upper_bound sym len i
  end

#push-options "--z3refresh --z3rlimit 512 --fuel 2"
let lemma_sigma_expand_1 (sym: sym_seq) (len: len_seq) (i j: nat): Lemma
  (requires kraft_cond sym len /\ i + 1 == j /\ j < length len)
  (ensures
    sigma i j (fun k -> pow2 len.[j], pow2 len.[k]) ==
    (pow2 len.[j], pow2 len.[i]) +$ (pow2 len.[j], pow2 len.[j])) = ()
#pop-options

#push-options "--fuel 1"
let rec lemma_kraft_series_rat_extend (sym: sym_seq) (len: len_seq) (i j: nat): Lemma
  (requires kraft_cond sym len /\ i < j /\ j < length len)
  (ensures
    sigma i j (fun k -> pow2 len.[j], pow2 len.[k]) =$
    sigma i (j - 1) (fun k -> pow2 len.[j], pow2 len.[k]) +$ one)
  (decreases j - i) =
  match j - i with
  | 1 ->
    calc (=$) {
      sigma i j (fun k -> pow2 len.[j], pow2 len.[k]);
      =={lemma_sigma_expand_1 sym len i j}
      (pow2 len.[j], pow2 len.[i]) +$ (pow2 len.[j], pow2 len.[j]);
      =${}
      (pow2 len.[j], pow2 len.[i]) +$ one;
      =={}
      sigma i (j - 1) (fun k -> pow2 len.[j], pow2 len.[k]) +$ one;
    }
  | _ ->
    let f (k: nat{i <= k /\ k <= j}): Tot rat = pow2 len.[j], pow2 len.[k] in
    calc (=$) {
      sigma i j f;
      =={}
      (pow2 len.[j], pow2 len.[i]) +$ sigma (i + 1) j f;
      =${sigma_extensionality (i + 1) j f (fun k -> pow2 len.[j], pow2 len.[k])}
      (pow2 len.[j], pow2 len.[i]) +$ sigma (i + 1) j (fun k -> pow2 len.[j], pow2 len.[k]);
      =${lemma_kraft_series_rat_extend sym len (i + 1) j}
      (pow2 len.[j], pow2 len.[i]) +$
      sigma (i + 1) (j - 1) (fun k -> pow2 len.[j], pow2 len.[k]) +$ one;
      =${}
      ((pow2 len.[j], pow2 len.[i]) +$
      sigma (i + 1) (j - 1) (fun k -> pow2 len.[j], pow2 len.[k])) +$ one;
      =${
        sigma_extensionality (i + 1) (j - 1) f (fun k -> pow2 len.[j], pow2 len.[k]);
        sigma_extensionality i (j - 1) f (fun k -> pow2 len.[j], pow2 len.[k])
      }
      sigma i (j - 1) (fun k -> pow2 len.[j], pow2 len.[k]) +$ one;
    }
#pop-options

let lemma_kraft_code_rat_next (sym: sym_seq) (len: len_seq) (i: pos): Lemma
  (requires kraft_cond sym len /\ i < length len)
  (ensures
    len.[i] >= len.[i - 1] /\
    kraft_code_rat sym len i =$
    (kraft_code_rat sym len (i - 1) +$ one) *$ of_int (pow2 (len.[i] - len.[i - 1]))) =
  lemma_kraft_sorted sym len (i - 1) i;
  if i > 1 then begin
    let f (j: nat{0 <= j /\ j <= i - 1}): Tot rat = pow2 len.[i - 1], pow2 len.[j] in
    calc (=$) {
      kraft_code_rat sym len i;
      =={}
      sigma 0 (i - 1) (fun j -> pow2 len.[i], pow2 len.[j]);
      =${
        Math.pow2_plus (len.[i] - len.[i - 1]) len.[i - 1];
        sigma_mul_distributivity
          0 (i - 1)
          (of_int (pow2 (len.[i] - len.[i - 1])))
          (fun j -> pow2 len.[i], pow2 len.[j])
          (fun j -> pow2 len.[i - 1], pow2 len.[j])
      }
      of_int (pow2 (len.[i] - len.[i - 1])) *$
      sigma 0 (i - 1) (fun j -> pow2 len.[i - 1], pow2 len.[j]);
      =${lemma_kraft_series_rat_extend sym len 0 (i - 1)}
      of_int (pow2 (len.[i] - len.[i - 1])) *$
      (sigma 0 (i - 1 - 1) (fun j -> pow2 len.[i - 1], pow2 len.[j]) +$ one);
      =${
        sigma_extensionality 0 (i - 1 - 1) f (fun j -> pow2 len.[i - 1], pow2 len.[j]);
        assert(kraft_code_rat sym len (i - 1) =$
          sigma 0 (i - 1 - 1) (fun j -> pow2 len.[i - 1], pow2 len.[j]))
      }
      of_int (pow2 (len.[i] - len.[i - 1])) *$ (kraft_code_rat sym len (i - 1) +$ one);
    }
  end else
    calc (=$) {
      kraft_code_rat sym len i;
      =={}
      (pow2 len.[1], pow2 len.[0]);
      =${pow2_subtraction len.[1] len.[0]}
      (pow2 (len.[1] - len.[0]), 1);
      =${}
      one *$ (pow2 (len.[1] - len.[0]), 1);
      =${}
      one *$ of_int (pow2 (len.[1] - len.[0]));
    }

let lemma_kraft_code_next sym len i =
  lemma_kraft_sorted sym len (i - 1) i;
  if i > 1 then
    let f (j: nat{0 <= j /\ j <= i - 1}): Tot rat = pow2 len.[i - 1], pow2 len.[j] in
    calc (=$) {
      of_int (do_kraft_code sym len 0 i);
      =${lemma_kraft_code_rat_nat sym len 0 i}
      sigma 0 (i - 1) (fun j -> (pow2 len.[i], pow2 len.[j]));
      =={}
      kraft_code_rat sym len i;
      =${lemma_kraft_code_rat_next sym len i}
      of_int (pow2 (len.[i] - len.[i - 1])) *$
      (kraft_code_rat sym len (i - 1) +$ one);
      =${
        sigma_extensionality 0 (i - 1 - 1) f (fun j -> pow2 len.[i - 1], pow2 len.[j]);
        assert(kraft_code_rat sym len (i - 1) =$
          sigma 0 (i - 1 - 1) (fun j -> pow2 len.[i - 1], pow2 len.[j]))
      }
      of_int (pow2 (len.[i] - len.[i - 1])) *$
      (sigma 0 (i - 1 - 1) (fun j -> pow2 len.[i - 1], pow2 len.[j]) +$ one);
      =${lemma_kraft_code_rat_nat sym len 0 (i - 1)}
      of_int (pow2 (len.[i] - len.[i - 1])) *$
      (of_int (do_kraft_code sym len 0 (i - 1) + 1));
      =={}
      of_int ((pow2 (len.[i] - len.[i - 1])) * (do_kraft_code sym len 0 (i - 1) + 1));
    }
