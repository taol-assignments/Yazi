module Spec.Kraft

open FStar.Seq
open Lib.Rational
open Lib.Seq

let rec kraft_sum (l: seq nat): Tot rat (decreases length l) =
  match length l with
  | 0 -> zero
  | _ -> qpow2 (-l.[0]) +$ kraft_sum (tail l)

type kraft_series (max_len: pos) = l: seq nat{
  kraft_sum l =$ one /\ (forall i. l.[i] <= max_len)
}
