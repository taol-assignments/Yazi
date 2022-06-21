module Spec.Package.Merge

open FStar.Calc
open FStar.Mul
open FStar.Math.Lemmas
open FStar.Seq
open Lib.Rational
open Lib.Seq

class weight_value (a:Type) =
{
  weight : a -> nat;
  value : a -> rat
}

type item: (exp: pos) -> (weight: pos) -> Type =
  | Coin: exp: pos -> weight: pos -> item exp weight
  | Package: #exp: pos -> #w1: pos -> #w2: pos ->
    i1: item (exp + 1) w1 -> i2: item (exp + 1) w2 -> item exp (w1 + w2)

instance item_weight_value #e #w: weight_value (item e w) =
{
  weight = (fun _ -> w);
  value = fun _ -> qpow2 (-e)
}

let rec weight_sorted (w: seq pos): Tot bool (decreases length w) =
  match length w with
  | 0 | 1 -> true
  | _ -> w.[0] <= w.[1] && weight_sorted (tail w)

let rec weight_sum (w: seq pos{length w >= 1}): Tot pos (decreases length w) =
  match length w with
  | 1 -> last w
  | _ -> weight_sum (unsnoc w) + last w

type weights = w: seq pos{length w >= 2 /\ weight_sorted w}

type coin_cnt (w: weights) = c: pos{c <= length w}

type pkg_cnt #w (c: coin_cnt w) = p: nat{
  c + p <= 2 * length w - 2
}

type row_t: (w: weights) -> (exp: pos) -> (c: coin_cnt w) -> (p: pkg_cnt c) -> Type =
  | SHead: #w: weights -> #exp: pos -> c: item exp w.[0]{
      c == Coin exp w.[0]
    } -> row_t w exp 1 0
  | SCoin: #w: weights -> #exp: pos -> #c: index_t w{c > 0} -> #p: pkg_cnt c{
      c + p < 2 * length w - 2
    } -> xs: row_t w exp c p -> x: item exp w.[c]{x == Coin exp w.[c]} ->
    row_t w exp (c + 1) p
  | SPackage: #w: weights -> #exp: pos ->
    #c: coin_cnt w -> #p: pkg_cnt c{p + c + 1 <= 2 * length w - 2} ->
    #wp: pos -> xs: row_t w exp c p -> x: item exp wp {Package? x} ->
    row_t w exp c (p + 1)

private let rec row_weight #w #e #c #p (s: row_t w e c p): Tot pos =
  match s with
  | SHead c -> weight (c <: item e w.[0])
  | SCoin xs x -> row_weight xs + weight (x <: item e w.[c - 1])
  | SPackage #_ #_ #_ #_ #wp xs x -> row_weight xs + weight (x <: item e wp)

instance row_weight_value #w #e #c #p: weight_value (row_t w e c p) =
{
  weight = row_weight;
  value = fun _ -> of_int (c + p) *$ qpow2 (-e)
}

let lt #e #w1 #w2 (i1: item e w1) (i2: item e w2) =
  match (Coin? i1, Coin? i2) with
  | (true, _) | (false, false) -> w1 <= w2
  | (false, true) -> w1 < w2

private let rec row_item_weight #w #e #c #p
  (s: row_t w e c p) (i: nat{i < c + p}): Tot pos =
  match i = c + p - 1 with
  | true -> (match s with
    | SHead c -> weight (c <: item e w.[0])
    | SCoin xs x -> weight (x <: item e w.[c - 1])
    | SPackage #_ #_ #_ #_ #wp xs x -> weight (x <: item e wp))
  | false -> (match s with | SCoin xs x | SPackage xs x -> row_item_weight xs i)

private let rec row_index #w #e #c #p (s: row_t w e c p) (i: nat{i < c + p}):
  Tot (item e (row_item_weight s i)) =
  match i = c + p - 1 with
  | true -> (match s with | SHead x -> x | SCoin xs x | SPackage xs x -> x)
  | false -> match s with | SCoin xs x | SPackage xs x -> row_index xs i

let op_Array_Access #w #e #c #p (s: row_t w e c p) = row_index s

private let rec prefix_coin_cnt
  #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}): Tot (c': pos{c' <= c}) =
  if i = c + p then
    c
  else
    match s with | SCoin xs _ | SPackage xs _ -> prefix_coin_cnt xs i

private let rec prefix_pkg_cnt #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}):
  Tot (pkg_cnt #w (prefix_coin_cnt s i)) =
  if i = c + p then
    p
  else
    match s with | SCoin xs _ | SPackage xs _ -> prefix_pkg_cnt xs i

let rec prefix #w #e #c #p (s: row_t w e c p) (i: pos{i <= c + p}):
  Tot (row_t w e (prefix_coin_cnt s i) (prefix_pkg_cnt s i)) =
  if i = c + p then
    s
  else
    match s with | SCoin xs _ | SPackage xs _ -> prefix xs i

unfold let unsnoc #w #e #c #p (s: row_t w e c p{SHead? s == false}) = prefix s (c + p - 1)

let rec row_sorted #w #e #c #p (s: row_t w e c p): Tot bool =
  if c + p >= 2 then
    s.(c + p - 2) `lt` s.(c + p - 1) && row_sorted (unsnoc s)
  else
    true

private let row_pkg_gt #w #e #c #p (s: row_t w e c p): Tot Type0 =
  forall (i: nat{i % 2 == 0 /\ i + 1 < c + p /\ i / 2 + 1 < c}).
    weight s.(i) + weight s.(i + 1) > w.[i / 2 + 1]

type row w e c p = s: row_t w e c p{
  row_sorted s /\ row_pkg_gt s /\ c + p < 2 * c
}

private let rec unpack_correspond #w (#e: pos{e > 1}) #c #p #c' #p'
  (prev: row_t w e c p) (s: row_t w (e - 1) c' p'): Tot bool =
  match s with
  | SHead _ -> true
  | SCoin xs _ -> unpack_correspond prev xs
  | SPackage xs x ->
    let j = 2 * (p' - 1) in
    match x with | Package i1 i2 ->
      j + 1 < c + p &&
      weight i1 = row_item_weight prev j &&
      weight i2 = row_item_weight prev (j + 1) &&
      prev.(j) = i1 && prev.(j + 1) = i2 &&
      unpack_correspond prev xs

private let row_weight_upper_bound
  #w (#e: pos) #c #p (max: pos{max >= e}) (s: row_t w e c p) =
  forall i. weight (prefix s i) <= (max - e + 1) * weight_sum (slice w 0 (prefix_coin_cnt s i))

private let row_weight_equality
  (#w: weights) (#e: pos)
  (#p: pkg_cnt #w (length w)) #c' (#p': pkg_cnt c'{p' * 2 <= length w + p})
  (prev: row_t w (e + 1) (length w) p) (s: row_t w e c' p') =
  (p' > 0 ==> weight s == weight_sum (slice w 0 c') + weight (prefix prev (p' * 2))) /\
  (p' == 0 ==> weight s == weight_sum (slice w 0 c'))

let merge_element_lt #w (#e: pos)
  #p (prev: row_t w (e + 1) (length w) p{row_sorted prev})
  #c' #p' (s: row_t w e c' p'{row_sorted s}) =
  let n = length w in
  let lst = s.(p' + c' - 1) in
  (c' < n ==> lst `lt` Coin e w.[c']) /\
  (2 * p' + 1 < n + p ==> lst `lt` Package prev.(2 * p') prev.(2 * p' + 1))

#push-options "--fuel 0 --ifuel 0 --z3refresh"
type row_partial #w (#e: pos) #p (max: pos{max > e})
  (prev: row w (e + 1) (length w) p) c' p' =
  s: row w e c' p' {
    let n = length w in
    let lp = n + p in
    p' * 2 <= lp /\
    unpack_correspond prev s /\
    row_weight_upper_bound max s /\
    row_weight_equality prev s /\
    merge_element_lt prev s
  }
#pop-options

val lemma_weight_sorted: w: weights -> i: index_t w -> j: index_t w -> Lemma
  (requires i <= j)
  (ensures w.[i] <= w.[j])
  (decreases %[length w; j - i])
  [SMTPat w.[i]; SMTPat w.[j]]

type pkg_index #w (p: pkg_cnt #w (length w)) (c': coin_cnt w) = p': pkg_cnt c'{
  p' <= length w - 2 /\ p' <= (length w + p) / 2
}

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --query_stats"
let pkg_smaller
  #w (#e: pos) #p (prev: row_t w (e + 1) (length w) p) #c' #p' (s: row_t w e c' p') =
  let n = length w in
  p' < Math.Lib.min (n - 2) ((n + p) / 2) /\
  (c' < n ==> (
    let pkg: item e _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin e w.[c'] in
    weight pkg < weight coin
  ))

let coin_smaller
  #w (#e: pos) #p (prev: row_t w (e + 1) (length w) p) #c' #p' (s: row_t w e c' p') =
  let n = length w in
  c' < n /\
  (p' < Math.Lib.min (n - 2) ((n + p) / 2) ==> (
    let pkg: item e _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin e w.[c'] in
    weight coin <= weight pkg
  ))

private let table_row_pred (#w: weights) (#e: pos) (max: pos{max > e})
  (#p: pkg_cnt (length w)) (prev: row w (e + 1) (length w) p)
  #c' (#p': pkg_cnt c'{p' * 2 <= length w + p}) (s: row_t w e c' p') =
  row_sorted s /\
  row_pkg_gt s /\
  row_weight_equality prev s /\
  row_weight_upper_bound max s /\
  unpack_correspond prev s /\
  merge_element_lt prev s

val lemma_pkg_weight:
    #w: weights
  -> #n: nat{n == length w}
  -> #e: pos
  -> #max: pos{max > e}
  -> #p: pkg_cnt n{p <= n - 2}
  -> prev: row w (e + 1) n p{row_weight_upper_bound max prev}
  -> #c': pos{c' <= n}
  -> #p': pkg_index p c'{p' <= 2 * length w + p}
  -> s: row_partial #_ #e #_ max prev c' p'
  -> Lemma
  (requires c' < n \/ p' < Math.Lib.min (n - 2) ((n + p) / 2))
  (ensures 
    (2 * p' + 3 < n + p ==>
      prev.(p' * 2) `lt` prev.(p' * 2 + 1) /\
      prev.(p' * 2 + 1) `lt` prev.(p' * 2 + 2) /\
      prev.(p' * 2 + 2) `lt` prev.(p' * 2 + 3)) /\
    (pkg_smaller prev s ==> 
      table_row_pred max prev (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))) /\
    (coin_smaller prev s ==> table_row_pred max prev (SCoin s (Coin e w.[c']))))

unfold let next_pkg_cnt (w: weights) (p: nat): Tot nat =
  let n = length w in
  Math.Lib.min (n - 2) ((n + p) / 2) 

#push-options "--fuel 1 --ifuel 0 --z3rlimit 1024 --z3refresh"
let rec merge (#w: weights) (#n: nat{n == length w}) (#e: pos) (#max: pos{max >= e + 1})
  (#p: pkg_cnt n{p <= n - 2}) (prev: row w (e + 1) n p{
    row_weight_upper_bound max prev
  }) (#c': pos{c' <= n}) (#p': pkg_index p c')
  (s: row_partial max prev c' p'):
  Tot (s': row w e n (next_pkg_cnt w p){
    unpack_correspond prev s' /\
    row_weight_upper_bound max s
  }) (decreases %[n - c'; n + p - 2 * p']) =
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if c' < n || p' < pmax then lemma_pkg_weight prev s;

  match (c' < n, p' < pmax) with
  | (false, false) -> s
  | (false, true) ->
    merge #w #n #e #max #p prev (SPackage s (Package prev.(p' * 2) prev.(p' * 2 + 1)))
  | (true, false) ->
    merge #w #n #e #max #p prev (SCoin s (Coin e w.[c']))
  | _ ->
    let pkg: item e _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin e w.[c'] in
    if weight pkg < weight coin then 
      merge #w #n #e #max #p prev (SPackage s pkg)
    else
      merge #w #n #e #max #p prev (SCoin s coin)
#pop-options

type table:
    w: weights
  -> max: pos
  -> min: pos{max >= min}
  -> p: pkg_cnt #w (length w)
  -> last: row w min (length w) p
  -> Type =
  | Single:
      #w: weights -> #max: pos -> s: row w max (length w) 0 -> table w max max 0 s
  | SRow:
      #w: weights -> #max: pos -> #min: pos{max >= min /\ min > 1} ->
      #p: pkg_cnt #w (length w) -> #prev: row w min (length w) p ->
      t: table w max min p prev ->
      s: row w (min - 1) (length w) (next_pkg_cnt w p){
        unpack_correspond prev s
      } -> table w max (min - 1) (next_pkg_cnt w p) s
