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
  | Coin: id: nat -> exp: pos -> weight: pos -> item exp weight
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

type weights = w: seq pos{length w >= 2 /\ weight_sorted w}

type coin_cnt (w: weights) = c: pos{c <= length w}

type pkg_cnt #w (c: coin_cnt w) = p: nat{
  c + p <= 2 * length w - 2
}

type row_t: (w: weights) -> (exp: pos) -> (c: coin_cnt w) -> (p: pkg_cnt c) -> Type =
  | SHead: #w: weights -> #exp: pos -> c: item exp w.[0]{
      c == Coin 0 exp w.[0]
    } -> row_t w exp 1 0
  | SCoin: #w: weights -> #exp: pos -> #c: index_t w{c > 0} -> #p: pkg_cnt c{
      c + p < 2 * length w - 2
    } -> xs: row_t w exp c p -> x: item exp w.[c]{x == Coin c exp w.[c]} ->
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
  (s: row_t w e c p{c + p > 0}) (i: nat{i < c + p}): Tot pos =
  match i = c + p - 1 with
  | true -> (match s with
    | SHead c -> weight (c <: item e w.[0])
    | SCoin xs x -> weight (x <: item e w.[c - 1])
    | SPackage #_ #_ #_ #_ #wp xs x -> weight (x <: item e wp))
  | false -> (match s with | SCoin xs x | SPackage xs x -> row_item_weight xs i)

private let rec row_index #w #e #c #p (s: row_t w e c p{c + p > 0}) (i: nat{i < c + p}):
  Tot (item e (row_item_weight s i)) =
  match i = c + p - 1 with
  | true -> (match s with | SHead x -> x | SCoin xs x | SPackage xs x -> x)
  | false -> match s with | SCoin xs x | SPackage xs x -> row_index xs i

let op_Array_Access #w #e #c #p (s: row_t w e c p{c + p > 0}) = row_index s

type pkg_index #w (p: pkg_cnt #w (length w)) (c': coin_cnt w) = p': pkg_cnt c'{
  p' <= length w - 2 /\ p' <= (length w + p) / 2
}

private unfold let prev_coin_cnt #w #e #c #p (s: row_t w e c p) =
  match s with
  | SCoin xs x -> c - 1
  | _ -> c

private unfold let prev_pkg_cnt #w #e #c #p (s: row_t w e c p) =
  match s with
  | SPackage xs x -> p - 1
  | _ -> p

let unsnoc #w #e #c #p (s: row_t w e c p{SHead? s == false}):
  Tot (row_t w e (prev_coin_cnt s) (prev_pkg_cnt s)) =
  match s with
  | SCoin xs x | SPackage xs x -> xs

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

#push-options "--fuel 0 --ifuel 0 --z3refresh"
type row_partial #w (#e: pos) #p (prev: row w (e + 1) (length w) p) c' p' =
  xs: row w e c' p' {
    let n = length w in
    let lp = n + p in
    unpack_correspond prev xs /\
    (c' + p' > 0 ==>
      (let lst = xs.(p' + c' - 1) in
      (c' < n ==> lst `lt` Coin c' e w.[c']) /\
      (2 * p' + 1 < lp ==> lst `lt` Package prev.(2 * p') prev.(2 * p' + 1))))
  }
#pop-options

unfold let next_pkg_cnt (w: weights) (p: nat): Tot nat =
  let n = length w in
  Math.Lib.min (n - 2) ((n + p) / 2) 

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

val lemma_weight_sorted: w: weights -> i: index_t w -> j: index_t w -> Lemma
  (requires i <= j)
  (ensures w.[i] <= w.[j])
  (decreases %[length w; j - i])
  [SMTPat w.[i]; SMTPat w.[j]]

val lemma_row_weight_sorted:
    #w: weights
  -> #e: pos
  -> #c: coin_cnt w
  -> #p: pkg_cnt c
  -> s: row_t w e c p{row_sorted s}
  -> i: nat{i < c + p}
  -> j: nat{j < c + p}
  -> Lemma
  (requires i < j)
  (ensures s.(i) `lt` s.(j))
  (decreases %[c + p; j - i])

#push-options "--z3rlimit 256 --fuel 1 --ifuel 1 --query_stats"
let pkg_smaller
  (#w: weights) (#n: nat{n == length w}) (#e: pos{e > 1})
  (#p: pkg_cnt n{p <= n - 2}) (#c': pos{c' <= n}) (#p': pkg_index p c')
  (prev: row w e n p) (xs: row_partial #_ #(e - 1) #_ prev c' p') =
  p' < Math.Lib.min (n - 2) ((n + p) / 2) /\
  (c' < n ==> (
    let pkg: item (e - 1) _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin c' (e - 1) w.[c'] in
    weight pkg < weight coin
  ))

let coin_smaller
  (#w: weights) (#n: nat{n == length w}) (#e: pos{e > 1})
  (#p: pkg_cnt n{p <= n - 2}) (#c': pos{c' <= n}) (#p': pkg_index p c')
  (prev: row w e n p) (xs: row_partial #_ #(e - 1) #_ prev c' p') =
  c' < n /\
  (p' < Math.Lib.min (n - 2) ((n + p) / 2) ==> (
    let pkg: item (e - 1) _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin c' (e - 1) w.[c'] in
    weight coin <= weight pkg
  ))

val lemma_pkg_weight:
    #w: weights
  -> #n: nat{n == length w}
  -> #e: pos{e > 1}
  -> #p: pkg_cnt n{p <= n - 2}
  -> #c': pos{c' <= n}
  -> #p': pkg_index p c'
  -> prev: row w e n p
  -> xs: row_partial #_ #(e - 1) #_ prev c' p'
  -> Lemma
  (requires c' < n \/ p' < Math.Lib.min (n - 2) ((n + p) / 2))
  (ensures 
    (pkg_smaller prev xs ==> 
      row_pkg_gt (SPackage xs (Package prev.(p' * 2) prev.(p' * 2 + 1)))
    ) /\ (coin_smaller prev xs ==> 
      row_pkg_gt (SCoin xs (Coin c' (e - 1) w.[c']))
    ))

#push-options "--fuel 1 --ifuel 0 --z3rlimit 1024"
let rec merge (#w: weights) (#n: nat{n == length w}) (#e: pos{e > 1})
  (#p: pkg_cnt n{p <= n - 2}) (#c': pos{c' <= n}) (#p': pkg_index p c')
  (prev: row w e n p) (xs: row_partial prev c' p'):
  Tot (xs': row w (e - 1) n (next_pkg_cnt w p){
    unpack_correspond prev xs'
  }) (decreases %[n - c'; n + p - 2 * p']) =
  if 2 * p' + 3 < n + p then begin
    lemma_row_weight_sorted prev (p' * 2) (p' * 2 + 1);
    lemma_row_weight_sorted prev (p' * 2 + 1) (p' * 2 + 2);
    lemma_row_weight_sorted prev (p' * 2 + 2) (p' * 2 + 3)
  end;
  let pmax = Math.Lib.min (n - 2) ((n + p) / 2) in
  if (c' < n || p' < pmax) then lemma_pkg_weight prev xs;

  match (c' < n, p' < pmax) with
  | (false, false) -> xs
  | (false, true) ->
    merge prev (SPackage xs (Package prev.(p' * 2) prev.(p' * 2 + 1)))
  | (true, false) ->
    merge prev (SCoin xs (Coin c' (e - 1) w.[c']))
  | _ ->
    let pkg: item (e - 1) _ = Package prev.(p' * 2) prev.(p' * 2 + 1) in
    let coin = Coin c' (e - 1) w.[c'] in
    if weight pkg < weight coin then 
      merge prev (SPackage xs pkg)
    else
      merge prev (SCoin xs coin)

