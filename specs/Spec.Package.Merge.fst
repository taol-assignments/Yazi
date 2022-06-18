module Spec.Package.Merge

open FStar.Classical

#push-options "--fuel 2 --ifuel 2 --z3rlimit 128"
let rec lemma_weight_sorted w i j =
  match i with
  | 0 -> if j > 1 then lemma_weight_sorted (tail w) 0 (j - 1)
  | _ -> if length w > 2 then lemma_weight_sorted (tail w) (i - 1) (j - 1)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 128"
let rec lemma_row_weight_sorted #w #e #c #p s i j =
  if j = c + p - 1 then begin
    if j - i > 1 then lemma_row_weight_sorted s i (j - 1)
  end else
    lemma_row_weight_sorted (unsnoc s) i j

let rec lemma_last_item_gte_last_leaf #w #e #c #p (s: row w e c p): Lemma
  (requires c >= 1)
  (ensures weight s.(c + p - 1) >= w.[c - 1]) =
  match s with
  | SHead _ | SCoin _ _ -> ()
  | SPackage xs x -> lemma_last_item_gte_last_leaf xs

#push-options "--fuel 1 --ifuel 0 --z3rlimit 1024 --z3refresh --query_stats"
let lemma_pkg_weight #w #n #e #p #c' #p' prev s =
  if 2 * p' + 3 < n + p then begin
    lemma_row_weight_sorted prev (p' * 2) (p' * 2 + 1);
    lemma_row_weight_sorted prev (p' * 2 + 1) (p' * 2 + 2);
    lemma_row_weight_sorted prev (p' * 2 + 2) (p' * 2 + 3)
  end;

  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  match (c' < n, p' < pmax) with
  | (false, true) -> lemma_last_item_gte_last_leaf s
  | (true, true) -> 
    let pkg: item (e - 1) _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin (e - 1) w.[c'] in
    if weight pkg < weight coin then lemma_last_item_gte_last_leaf s
  | _ -> ()
#pop-options

