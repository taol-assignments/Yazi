module Spec.Package.Merge

open FStar.Classical

#push-options "--fuel 2 --ifuel 2 --z3rlimit 128"
let rec lemma_weight_sorted w i j =
  match i with
  | 0 -> if j > 1 then lemma_weight_sorted (tail w) 0 (j - 1)
  | _ -> if length w > 2 then lemma_weight_sorted (tail w) (i - 1) (j - 1)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 128"
let rec lemma_row_weight_sorted
  #w #e #c #p (s:row_t w e c p{row_sorted s}) (i j: nat): Lemma
  (requires i < j /\ i < c + p /\ j < c + p)
  (ensures s.(i) `lt` s.(j))
  (decreases %[c + p; j - i]) =
  if j = c + p - 1 then begin
    if j - i > 1 then lemma_row_weight_sorted s i (j - 1)
  end else
    lemma_row_weight_sorted (unsnoc s) i j

let rec lemma_last_item_gte_last_coin #w #e #c #p (s: row_t w e c p): Lemma
  (requires c >= 1 /\ row_sorted s)
  (ensures weight s.(c + p - 1) >= w.[c - 1]) =
  match s with
  | SHead _ | SCoin _ _ -> ()
  | SPackage xs x -> lemma_last_item_gte_last_coin xs
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit 1024 --query_stats"
let lemma_pkg_weight_sorted #w (#e: pos)
  #p (prev: row w (e + 1) (length w) p)
  #c' #p' (s: row w e c' p'): Lemma
  (requires
    merge_element_lt prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures
    (pkg_smaller prev s ==>
      row_sorted (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> row_sorted (SCoin s (Coin e w.[c'])))) = ()

let lemma_pkg_weight_unpack #w (#e: pos)
  #p (prev: row w (e + 1) (length w) p)
  #c' #p' (s: row w e c' p'{unpack_correspond prev s}): Lemma
  (requires
    merge_element_lt prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures
    (pkg_smaller prev s ==>
      unpack_correspond prev (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> unpack_correspond prev (SCoin s (Coin e w.[c'])))) = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 1024 --query_stats"
let rec lemma_row_first #w #e #c #p (s: row_t w e c p): Lemma
  (ensures
    row_item_weight s 0 == w.[0] /\
    s.(0) == Coin e w.[0] /\
    weight s.(0) == weight (prefix s 1)) =
  match s with
  | SHead _ -> ()
  | SCoin xs _ -> lemma_row_first xs
  | SPackage xs _ -> lemma_row_first xs

#push-options "--fuel 2 --ifuel 1 --z3rlimit 1024 --query_stats"
let rec lemma_prefix_cnt_inv #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}): Lemma
  (ensures prefix_coin_cnt s i + prefix_pkg_cnt s i == i) =
  if i < c + p then
    match s with | SCoin xs _ | SPackage xs _ -> lemma_prefix_cnt_inv xs i

let rec lemma_eq_elim #w #e #c #p (a: row_t w e c p) #c' #p' (b: row_t w e c' p'): Lemma
  (requires c == c' /\ p == p' /\
    (forall i. row_item_weight a i == row_item_weight b i /\ a.(i) == b.(i)))
  (ensures a == b) =
  assert(a.(c + p - 1) == b.(c + p - 1));
  if c + p > 1 then match a with
  | SCoin a' _ -> (match b with | SCoin b' _ ->
    assert(forall i. i < c + p - 1 ==> row_item_weight a i == row_item_weight a' i);
    assert(forall i. i < c + p - 1 ==> row_item_weight b i == row_item_weight b' i);
    lemma_eq_elim a' b')
  | SPackage a' _ -> (match b with | SPackage b' _ ->
    assert(forall i. i < c + p - 1 ==> row_item_weight a i == row_item_weight a' i);
    assert(forall i. i < c + p - 1 ==> row_item_weight b i == row_item_weight b' i);
    lemma_eq_elim a' b')

let rec lemma_prefix_prefix_aux #w #e #c #p (s: row_t w e c p)
  (i: pos{i <= c + p}) (j: pos{j <= i}): Lemma
  (ensures (
    lemma_prefix_cnt_inv s i;
    prefix_coin_cnt (prefix s i) j == prefix_coin_cnt s j /\
    prefix_pkg_cnt (prefix s i) j == prefix_pkg_cnt s j)) =
  lemma_prefix_cnt_inv s i;
  if j < i && i < c + p then
    match s with
    | SCoin s' _ -> lemma_prefix_prefix_aux s' i j
    | SPackage s' _ -> lemma_prefix_prefix_aux s' i j

let rec lemma_prefix_prefix #w #e #c #p (s: row_t w e c p)
  (i: pos{i <= c + p}) (j: pos{j <= i}): Lemma
  (ensures (
    lemma_prefix_cnt_inv s i;
    lemma_prefix_prefix_aux s i j;
    prefix (prefix s i) j == prefix s j)) =
  lemma_prefix_cnt_inv s i;
  if j < i && i < c + p then
    match s with | SCoin s' _ | SPackage s' _ -> lemma_prefix_prefix s' i j

let rec lemma_prefix_eq_aux #w #e #c #p
  (s: row_t w e c p) (i: pos{i <= c + p}) (j: nat{j < i}): Lemma
  (ensures (
    lemma_prefix_cnt_inv s i;
    row_item_weight (prefix s i) j == row_item_weight s j)) =
  if j < i && i < c + p then
    match s with | SCoin s' _ | SPackage s' _ -> lemma_prefix_eq_aux s' i j

let rec lemma_prefix_eq #w #e #c #p
  (s: row_t w e c p) (i: pos{i <= c + p}) (j: nat{j < i}): Lemma
  (ensures (
    lemma_prefix_eq_aux s i j;
    lemma_prefix_cnt_inv s i;
    (prefix s i).(j) == s.(j))) =
  if j < i && i < c + p then
    match s with | SCoin s' _ | SPackage s' _ -> lemma_prefix_eq s' i j
  
let lemma_prefix_weight #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}): Lemma
  (requires i > 1)
  (ensures weight (prefix s i) = weight (prefix s (i - 1)) + weight s.(i - 1)) =
  let s' = prefix s i in
  lemma_prefix_cnt_inv s i;
  assert(weight s' ==
    (match s' with
    | SHead c -> w.[0]
    | SCoin xs x ->
      row_weight (prefix s' (i - 1)) + row_item_weight s' (i - 1)
    | SPackage #_ #_ #_ #_ #wp xs x ->
      row_weight (prefix s' (i - 1)) + row_item_weight s' (i - 1)));
  if c + p > 1 then
    calc (==) {
      row_weight (prefix s' (i - 1)) + row_item_weight s' (i - 1);
      =={lemma_prefix_prefix s i (i - 1)}
      row_weight (prefix s (i - 1)) + row_item_weight s' (i - 1);
      =={lemma_prefix_eq s i (i - 1)}
      weight (prefix s (i - 1)) + row_item_weight s (i - 1);
    }
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 1024 --query_stats"
let lemma_pkg_weight_equality #w (#e: pos)
  #p (prev: row w (e + 1) (length w) p)
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s}): Lemma
  (requires
    merge_element_lt prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures
    (pkg_smaller prev s ==>
      row_weight_equality prev (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> row_weight_equality prev (SCoin s (Coin e w.[c'])))) =
  let n = length w in
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if p' < pmax then
    let pkg: item e _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let s' = SPackage s pkg in
    if c' = n || weight (Coin e w.[c']) > weight pkg then begin
      calc (==) {
        weight (s' <: row_t w e c' (p' + 1));
        =={}
        weight (s <: row_t w e c' p') +
        weight (Package prev.(p' * 2) prev.(p' * 2 + 1));
      };
      if p' = 0 then
        calc (==) {
          weight (s <: row_t w e c' p') +
          weight (Package prev.(p' * 2) prev.(p' * 2 + 1));
          =={}
          weight_sum (slice w 0 c') +
          weight prev.(0) + weight prev.(1);
          =={lemma_row_first prev}
          weight_sum (slice w 0 c') +
          weight (prefix prev 1) + weight prev.(1);
          =={lemma_prefix_weight prev 2}
          weight_sum (slice w 0 c') + weight (prefix prev 2);
        }
      else
        calc (==) {
          weight (s <: row_t w e c' p') +
          weight (Package prev.(p' * 2) prev.(p' * 2 + 1));
          =={}
          weight_sum (slice w 0 c') +
          weight (prefix prev (p' * 2)) + weight prev.(p' * 2) +
          weight prev.(p' * 2 + 1);
          =={lemma_prefix_weight prev (p' * 2 + 1)}
          weight_sum (slice w 0 c') +
          weight (prefix prev ((p' * 2) + 1)) + weight prev.(p' * 2 + 1);
          =={lemma_prefix_weight prev (p' * 2 + 2)}
          weight_sum (slice w 0 c') + weight (prefix prev ((p' * 2) + 2));
        }
    end

#push-options "--fuel 2 --ifuel 1"
let rec lemma_unpack_correspond #w (#e: pos{e > 1}) #c #p 
  (prev: row_t w e c p) #c' #p' (s: row_t w (e - 1) c' p'): Lemma
  (requires
    row_sorted prev /\ row_sorted s /\
    unpack_correspond prev s /\
    p' > 0 /\ 2 * p' <= c + p)
  (ensures
    weight s.(c' + p' - 1) >=
    weight (prev.(2 * (p' - 1))) + weight (prev.(2 * (p' - 1) + 1)))
  (decreases c') =
  match s with
  | SCoin xs _ -> lemma_unpack_correspond prev #(c' - 1) #p' xs
  | SPackage xs x -> ()

let rec lemma_prefix_row_sorted #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}): Lemma
  (requires row_sorted s)
  (ensures row_sorted (prefix s i)) =
  if i < c + p then
    match s with | SCoin xs _ | SPackage xs _ -> lemma_prefix_row_sorted xs i

let lemma_row_monotonous #w (#e: pos{e > 1}) #p 
  (prev: row w e (length w) p) #c' #p' (s: row w (e - 1) c' p'): Lemma
  (requires
    p' > 0 /\ 2 * p' <= length w + p /\
    unpack_correspond prev s /\
    merge_element_lt prev s)
  (ensures prefix_coin_cnt prev (p' * 2) <= c') =
  if prefix_coin_cnt prev (p' * 2) > c' && c' < length w then begin
    lemma_prefix_cnt_inv prev (p' * 2);
    lemma_unpack_correspond prev s;
    lemma_prefix_row_sorted prev (p' * 2);
    lemma_prefix_eq prev (p' * 2) (p' * 2 - 1);
    lemma_last_item_gte_last_coin (prefix prev (p' * 2))
  end

let rec lemma_weight_monotonous (w: seq pos{length w >= 1}) (i j: pos): Lemma
  (requires i <= j /\ i <= length w /\ j <= length w)
  (ensures weight_sum (slice w 0 i) <= weight_sum (slice w 0 j)) =
  if i < j then lemma_weight_monotonous w i (j - 1)
#pop-options

#push-options "--fuel 1 --ifuel 0"
let lemma_pkg_weight_merge_inv #w (#e: pos) (max: pos{max > e})
  #p (prev: row w (e + 1) (length w) p{row_weight_upper_bound max prev})
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s /\ row_weight_upper_bound max s}): Lemma
  (requires
    merge_element_lt prev s /\
    unpack_correspond prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures (pkg_smaller prev s ==> 
      merge_element_lt prev (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> merge_element_lt prev (SCoin s (Coin e w.[c'])))) =
  let n = length w in
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if c' < n && (p' = pmax || weight prev.(p' * 2) + weight prev.(p' * 2 + 1) >= w.[c'])
  then begin
    let s' = SCoin s (Coin e w.[c']) in
    assert(weight s'.(c' + p') == w.[c']);
    if c' + 1 < n then
      assert(weight s'.(c' + p') <= w.[c' + 1]);
    if p' * 2 + 1 < length w + p then
      assert(weight s'.(c' + p') <= weight prev.(2 * p') + weight prev.(2 * p' + 1))
  end else if 2 * p' + 3 < n + p then begin
    lemma_row_weight_sorted prev (p' * 2) (p' * 2 + 1);
    lemma_row_weight_sorted prev (p' * 2 + 1) (p' * 2 + 2);
    lemma_row_weight_sorted prev (p' * 2 + 2) (p' * 2 + 3)
  end

let lemma_pkg_weight_upper_bound_coin_aux #w (#e: pos) (max: pos{max > e})
  #p (prev: row w (e + 1) (length w) p{row_weight_upper_bound max prev})
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s /\ row_weight_upper_bound max s})
  (i: pos{i <= c' + p' + 1}) : Lemma
  (requires merge_element_lt prev s /\ unpack_correspond prev s /\ coin_smaller prev s)
  (ensures (
    let s' = SCoin s (Coin e w.[c']) in
    let c'' = prefix_coin_cnt s' i in
    weight (prefix s' i) <= (max - e + 1) * weight_sum (slice w 0 c''))) =
  let n = length w in
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  let s' = SCoin s (Coin e w.[c']) in
  let c'' = prefix_coin_cnt s' i in
  if i = c' + p' + 1 then begin
    calc (==) {
      weight (prefix s' i);
      =={lemma_prefix_weight s' i}
      weight (prefix s (c' + p')) + weight s'.(c' + p');
      =={}
      weight (s <: row_t w e c' p') + w.[c'];
    };
    if p' = 0 then
      Math.Lemmas.lemma_mult_le_right (weight_sum (slice w 0 c'')) 1 (max - e + 1)
    else
      calc (<=) {
        weight (prefix s' i);
        <={}
        weight_sum (slice w 0 c'') + weight (prefix prev (p' * 2));
        <={}
        weight_sum (slice w 0 c'') +
        (max - e) * weight_sum (slice w 0 (prefix_coin_cnt prev (p' * 2)));
        <={
          lemma_row_monotonous prev s;
          lemma_weight_monotonous w (prefix_coin_cnt prev (p' * 2)) c'';
          Math.Lemmas.lemma_mult_le_left
            (max - e)
            (weight_sum (slice w 0 (prefix_coin_cnt prev (p' * 2))))
            (weight_sum (slice w 0 c''))
        }
        weight_sum (slice w 0 c'') + (max - e) * weight_sum (slice w 0 c'');
        =={Math.Lemmas.distributivity_add_left 1 (max - e) (weight_sum (slice w 0 c''))}
        (max - e + 1) * weight_sum (slice w 0 c'');
      }
  end

let lemma_pkg_weight_upper_bound_pkg_aux #w (#e: pos) (max: pos{max > e})
  #p (prev: row w (e + 1) (length w) p{row_weight_upper_bound max prev})
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s /\ row_weight_upper_bound max s})
  (i: pos{i <= c' + p' + 1}) : Lemma
  (requires merge_element_lt prev s /\ unpack_correspond prev s /\ pkg_smaller prev s)
  (ensures (
    let s' = SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)) in
    let c'' = prefix_coin_cnt s' i in
    weight (prefix s' i) <= (max - e + 1) * weight_sum (slice w 0 c''))) =
  let n = length w in
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  let s' = SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)) in
  let c'' = prefix_coin_cnt s' i in
  if i = c' + p' + 1 then begin
    calc (==) {
      weight (prefix s' i);
      =={lemma_prefix_weight s' i}
      weight (prefix s (c' + p')) + weight s'.(c' + p');
      =={}
      weight (s <: row_t w e c' p') + weight prev.(2 * p') + weight prev.(2 * p' + 1);
    };
    lemma_last_item_gte_last_coin s;
    lemma_pkg_weight_merge_inv max prev s;
    if p' = 0 then
      calc (<=) {
        weight (prefix s' i);
        <={}
        weight_sum (slice w 0 c'') + weight prev.(0) + weight prev.(1);
        <={lemma_row_first prev}
        weight_sum (slice w 0 c'') + weight (prefix prev 1) + weight prev.(1);
        <={lemma_prefix_weight prev 2}
        weight_sum (slice w 0 c'') + weight (prefix prev 2);
        <={}
        weight_sum (slice w 0 c'') +
        (max - e) * weight_sum (slice w 0 (prefix_coin_cnt prev 2));
        <={
          lemma_row_monotonous prev s';
          lemma_weight_monotonous w (prefix_coin_cnt prev 2) c'';
          Math.Lemmas.lemma_mult_le_left
            (max - e)
            (weight_sum (slice w 0 (prefix_coin_cnt prev 2)))
            (weight_sum (slice w 0 c''))
        }
        weight_sum (slice w 0 c'') + (max - e) * weight_sum (slice w 0 c'');
        <={Math.Lemmas.distributivity_add_left 1 (max - e) (weight_sum (slice w 0 c''))}
        (max - e + 1) * weight_sum (slice w 0 c'');
      }
    else
      let p'' = (p' + 1) * 2 in
      calc (<=) {
        weight (prefix s' i);
        <={}
        weight_sum (slice w 0 c'') + weight (prefix prev (p' * 2)) +
        weight prev.(p' * 2) + weight prev.(p' * 2 + 1);
        <={lemma_prefix_weight prev (p' * 2 + 1)}
        weight_sum (slice w 0 c'') +
        weight (prefix prev (p' * 2 + 1)) + weight prev.(p' * 2 + 1);
        <={lemma_prefix_weight prev (p' * 2 + 2)}
        weight_sum (slice w 0 c'') + weight (prefix prev p'');
        <={}
        weight_sum (slice w 0 c'') +
        (max - e ) * weight_sum (slice w 0 (prefix_coin_cnt prev p''));
        <={
          lemma_row_monotonous prev s';
          lemma_weight_monotonous w (prefix_coin_cnt prev p'') c'';
          Math.Lemmas.lemma_mult_le_left
            (max - e)
            (weight_sum (slice w 0 (prefix_coin_cnt prev p'')))
            (weight_sum (slice w 0 c''))
        }
        weight_sum (slice w 0 c'') + (max - e ) * weight_sum (slice w 0 c'');
        <={Math.Lemmas.distributivity_add_left 1 (max - e) (weight_sum (slice w 0 c''))}
        (max - e + 1) * weight_sum (slice w 0 c'');
      }
  end

let lemma_pkg_weight_upper_bound_aux #w (#e: pos) (max: pos{max > e})
  #p (prev: row w (e + 1) (length w) p{row_weight_upper_bound max prev})
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s /\ row_weight_upper_bound max s})
  (i: pos{i <= c' + p' + 1}) : Lemma
  (requires
    merge_element_lt prev s /\
    unpack_correspond prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures
    (pkg_smaller prev s ==> (
      let s' = SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)) in
      let c'' = prefix_coin_cnt s' i in
      weight (prefix s' i) <= (max - e + 1) * weight_sum (slice w 0 c''))) /\
    (coin_smaller prev s ==> (
      let s' = SCoin s (Coin e w.[c']) in
      let c'' = prefix_coin_cnt s' i in
      weight (prefix s' i) <= (max - e + 1) * weight_sum (slice w 0 c'')))) =
  let n = length w in
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if c' < n && (p' = pmax || weight prev.(p' * 2) + weight prev.(p' * 2 + 1) >= w.[c']) then
    lemma_pkg_weight_upper_bound_coin_aux max prev s i
  else
    lemma_pkg_weight_upper_bound_pkg_aux max prev s i

let lemma_pkg_weight_upper_bound #w (#e: pos) (max: pos{max > e})
  #p (prev: row w (e + 1) (length w) p{row_weight_upper_bound max prev})
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (s: row w e c' p'{row_weight_equality prev s /\ row_weight_upper_bound max s}): Lemma
  (requires
    merge_element_lt prev s /\
    unpack_correspond prev s /\
    (pkg_smaller prev s \/ coin_smaller prev s))
  (ensures
    (pkg_smaller prev s ==>
      row_weight_upper_bound max (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> row_weight_upper_bound max (SCoin s (Coin e w.[c'])))) =
  forall_intro (move_requires (lemma_pkg_weight_upper_bound_aux max prev s))

#push-options "--fuel 1 --ifuel 0"
let lemma_pkg_weight #w #n #e #max #p prev #c' #p' s =
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if 2 * p' + 3 < n + p then begin
    lemma_row_weight_sorted prev (p' * 2) (p' * 2 + 1);
    lemma_row_weight_sorted prev (p' * 2 + 1) (p' * 2 + 2);
    lemma_row_weight_sorted prev (p' * 2 + 2) (p' * 2 + 3)
  end;
  if c' < n || p' < pmax then begin
    lemma_pkg_weight_sorted prev s;
    lemma_pkg_weight_unpack prev s;
    lemma_pkg_weight_equality prev s;
    lemma_pkg_weight_upper_bound max prev s;
    lemma_pkg_weight_merge_inv max prev s
  end;

  match (c' < n, p' < pmax) with
  | (false, true) -> lemma_last_item_gte_last_coin s
  | (true, true) -> 
    let pkg: item e _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin e w.[c'] in
    if weight pkg < weight coin then lemma_last_item_gte_last_coin s
  | _ -> ()
#pop-options

