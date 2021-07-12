module Spec.Tree

open Lib.Rational
open FStar.Mul

type tree =
  | Root: freq: pos -> left: tree -> right: tree -> tree
  | Internal: freq: pos -> len: pos -> left: tree -> right: tree -> tree
  | Leaf: freq: pos -> len: pos -> symbol: nat -> tree

let get_freq (t: tree{Root? t == false}): pos =
  match t with
  | Internal freq _ _ _ -> freq
  | Leaf freq _ _ -> freq

let get_len (t: tree): nat =
  match t with
  | Root _ _ _ -> 0
  | Internal _ len _ _ -> len
  | Leaf _ len _ -> len

let rec well_formed (t: tree): Type0 =
  match t with
  | Root f l r ->
    Root? l == false /\ Root? r == false /\
    get_len l == 1 /\ get_len r == 1 /\
    well_formed l /\ well_formed r
  | Internal f len l r ->
    Root? l == false /\ Root? r == false /\
    get_len l == len + 1 /\ get_len r == len + 1 /\
    well_formed l /\ well_formed r
  | _ -> True

private let rec optimal' (t: tree{well_formed t}): Type0 =
  match t with
  | Root f l r -> get_freq l + get_freq r == f /\ optimal' l /\ optimal' r
  | Internal f len l r -> get_freq l + get_freq r == f /\ optimal' l /\ optimal' r
  | Leaf _ _ _ -> True

let optimal (t: tree): Type0 = well_formed t /\ optimal' t

type well_formed_tree = t: tree{well_formed t}

unfold let kraft_term (n: nat): rat = (1, pow2 n)

let kraft_term_plus (n: pos): Lemma
  (ensures kraft_term n +$ kraft_term n =$ kraft_term (n - 1))
  [SMTPat (kraft_term n +$ kraft_term n)] = ()

let rec term_times (l: pos) (n: nat): rat =
  match n with
  | 0 -> zero
  | _ -> kraft_term l +$ term_times l (n - 1)

let rec kraft_sum (t: well_formed_tree): rat =
  match t with
  | Root _ l r -> kraft_sum l +$ kraft_sum r
  | Internal _ _ l r -> kraft_sum l +$ kraft_sum r
  | Leaf _ len _ -> kraft_term len

#set-options "--z3rlimit 200"
let rec kraft_sum_non_root (t: well_formed_tree): Lemma
  (requires Root? t == false)
  (ensures kraft_sum t =$ kraft_term (get_len t)) =
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
