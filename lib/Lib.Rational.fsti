module Lib.Rational

module Math = FStar.Math.Lemmas

open FStar.Calc
open FStar.Mul
open FStar.Seq
open Lib.Seq

type rat = (int & pos)

unfold let num (a: rat) = fst a
unfold let den (a: rat) = snd a

let (=$) (a b: rat): bool =
  num a * den b = num b * den a

let eq_refl (a: rat) : Lemma (ensures a =$ a) = ()

let eq_sym (a b: rat): Lemma
  (requires a =$ b)
  (ensures b =$ a)
  (* [SMTPat (a =$ b)] *) = ()

let eq_trans (a b c: rat): Lemma
  (requires a =$ b /\ b =$ c)
  (ensures a =$ c)
  [SMTPat (a =$ b); SMTPat (b =$ c)] = ()

let eq_req (a b: rat): Lemma
  (requires a == b)
  (ensures a =$ b)
  (* [SMTPat (a == b)] *) = ()

let (<=$) (a b: rat): bool = num a * den b <= num b * den a
unfold let (>=$) (a b: rat): bool = b <=$ a

let le_eq (a b a' b': rat): Lemma
  (requires a =$ a' /\ b =$ b' /\ a <=$ b)
  (ensures a' <=$ b')
  (* [SMTPat (a =$ a'); SMTPat (b =$ b'); SMTPat (a <=$ b)] *) = ()

let le_refl (a: rat) : Lemma (ensures a <=$ a) = ()

let le_antisym (a b: rat): Lemma
  (requires a <=$ b /\ b <=$ a)
  (ensures a =$ b)
  (* [SMTPat (a <=$ b); SMTPat (b <=$ a)] *) = ()

let le_trans (a b c: rat): Lemma
  (requires a <=$ b /\ b <=$ c)
  (ensures a <=$ c)
  (* [SMTPat (a <=$ b); SMTPat (b <=$ c)] *) = ()

let (<$) (a b: rat) = num a * den b < num b * den a
unfold let (>$) (a b: rat) = b <$ a

let lt_eq_l (a b a': rat): Lemma
  (requires a =$ a' /\ a <$ b)
  (ensures a' <$ b)
  (* [SMTPat (a =$ a'); SMTPat (a <$ b)] *) = ()

let lt_eq_r (a b b': rat): Lemma
  (requires b =$ b' /\ a <$ b)
  (ensures a <$ b')
  (* [SMTPat (b =$ b'); SMTPat (a <$ b)] *) = ()

let lt_not_eq (a b: rat) : Lemma
  (requires a <$ b)
  (ensures a <> b)
  (* [SMTPat (a <$ b)] *) = ()

let lt_trans (a b c: rat): Lemma
  (requires a <$ b /\ b <$ c)
  (ensures a <$ c)
  (* [SMTPat (a <$ b); SMTPat (b <$ c)] *) = ()

let lt_le_trans (a b c: rat): Lemma
  (requires a <$ b /\ b <=$ c)
  (ensures a <$ c)
  (* [SMTPat (a <$ b); SMTPat (b <=$ c)] *) = ()

let (+$) (a b: rat): Tot rat =
  (num a * den b + num b * den a, den a * den b)

unfold let zero: rat = (0, 1)
unfold let one: rat = (1, 1)

let plus_eq_l (a b a': rat): Lemma
  (requires a =$ a')
  (ensures a +$ b =$ a' +$ b)
  [SMTPat (a =$ a'); SMTPat (a' +$ b)] = ()

let plus_eq_r (a b b': rat): Lemma
  (requires b =$ b')
  (ensures a +$ b =$ a +$ b')
  [SMTPat (b =$ b'); SMTPat (a +$ b')] = ()

let plus_comm (a b: rat): Lemma
  (ensures a +$ b =$ b +$ a)
  (* [SMTPat (a +$ b)] *) = ()

let plus_zero_l (a: rat): Lemma
  (ensures zero +$ a =$ a)
  (* [SMTPat (zero +$ a)] *) = ()

let plus_zero_r (a: rat): Lemma
  (ensures a +$ zero =$ a)
  (* [SMTPat (a +$ zero)] *) = ()

let plus_non_zero_l (a b: rat): Lemma
  (requires zero <$ a)
  (ensures b <$ a +$ b) = ()

#set-options "--z3refresh --z3rlimit 1024 --fuel 0 --ifuel 0 --z3seed 12"
val plus_assoc: a: rat -> b: rat -> c: rat -> Lemma
  (ensures (a +$ b) +$ c =$ a +$ (b +$ c))
  (* [SMTPatOr [[SMTPat ((a +$ b) +$ c)]; [SMTPat (a +$ (b +$ c))]]] *)

let (-$) (a b: rat): Tot rat = (num a * den b - num b * den a, den a * den b)

let sub_eq (a b: rat): Lemma
  (requires a =$ b)
  (ensures a -$ b =$ zero)
  (* [SMTPat (a -$ b =$ zero)] *) = ()

let op_Star_Dollar (a b: rat): Tot rat = (num a * num b, den a * den b)

let common_factor_cancel (a: pos) (r: rat): Lemma
  (ensures (a * num r, a * den r) =$ r) = ()

let mul_zero_l (a: rat): Lemma
  (ensures a *$ zero =$ zero)
  (* [SMTPat (a *$ zero)] *) = ()

let mul_zero_r (a: rat): Lemma
  (ensures zero *$ a =$ zero)
  (* [SMTPat (zero *$ a)] *) = ()

let mul_comm (a b: rat): Lemma
  (ensures a *$ b =$ b *$ a)
  (* [SMTPat (a *$ b)] *) = ()

let mul_assoc (a b c: rat): Lemma
  (ensures (a *$ b) *$ c =$ a *$ (b *$ c))
  (* [SMTPatOr [[SMTPat ((a *$ b) *$ c)]; [SMTPat (a *$ (b *$ c))]]] *) =
  assert((a *$ b) *$ c =$ a *$ (b *$ c))

val distributivity_add_left: a: rat -> b: rat -> c: rat -> Lemma
  (ensures (a *$ b) +$ (a *$ c) =$ a *$ (b +$ c))

val mul_eq_l: a: rat -> b: rat -> a': rat -> Lemma
  (requires a =$ a')
  (ensures a *$ b =$ a' *$ b)
  (* [SMTPat (a =$ a'); SMTPat (a' *$ b)] *)

val mul_eq_r: a: rat -> b: rat -> b': rat -> Lemma
  (requires b =$ b')
  (ensures a *$ b =$ a *$ b')
  (* [SMTPat (b =$ b'); SMTPat (a *$ b')] *)

let of_int (a: int): rat = (a, 1)

let rec sigma (i: nat) (j: nat{i <= j}) (f: (k: nat{i <= k /\ k <= j}) -> rat):
  Tot rat (decreases j - i) =
  if i = j then f i else f i +$ sigma (i + 1) j f

// #push-options "--fuel 1"
// let rec sigma_mul_distributivity (i j: nat) (c: rat) (f g: (k: nat{i <= k /\ k <= j}) -> rat): Lemma
//   (requires i <= j /\ (forall k. f k = c *$ g k))
//   (ensures sigma i j f =$ c *$ sigma i j g)
//   (decreases j - i) =
//   if i < j then begin
//     sigma_mul_distributivity (i + 1) j c f g;
//     distributivity_add_left c (g i) (sigma (i + 1) j g)
//   end

// let rec sigma_split (i j k: nat) (f: (l: nat{i <= l /\ l <= k}) -> rat): Lemma
//   (requires i <= j /\ j + 1 <= k)
//   (ensures sigma i k f =$ sigma i j f +$ sigma (j + 1) k f)
//   (decreases k - i) =
//   match k - i with
//   | 1 -> ()
//   | _ -> if i < j then sigma_split (i + 1) j k f

// let rec sigma_gt_zero (i j: nat) (f: (k: nat{i <= k /\ k <= j}) -> rat): Lemma
//   (requires i <= j /\ (forall k. f k >$ zero))
//   (ensures sigma i j f >$ zero)
//   (decreases j - i) =
//   match j - i with
//   | 0 -> ()
//   | _ -> sigma_gt_zero (i + 1) j f

// let plus_non_zero_r (a b: rat): Lemma
//   (requires zero <$ a)
//   (ensures b <$ b +$ a) = ()
  
// let sigma_pos_lt (i j k: nat) (f: (l: nat{i <= l /\ l <= k}) -> rat): Lemma
//   (requires i <= j /\ j < k /\ (forall l. f l >$ zero))
//   (ensures sigma i j f <$ sigma i k f) =
//   sigma_split i j k f;
//   sigma_gt_zero i j f;
//   sigma_gt_zero (j + 1) k f;
//   plus_non_zero_r (sigma (j + 1) k f) (sigma i j f)

// let rec sigma_extensionality (i j: nat) (f g: (l: nat{i <= l /\ l <= j}) -> rat): Lemma
//   (requires i <= j /\ (forall k. i <= k /\ k <= j ==> f k =$ g k))
//   (ensures sigma i j f =$ sigma i j g)
//   (decreases j - i)
//   [SMTPat (sigma i j f =$ sigma i j g)] =
//   match j - i with
//   | 0 -> ()
//   | _ -> sigma_extensionality (i + 1) j f g

// #push-options "--ifuel 1"
// let rec sigma_snoc (#t: eqtype) (s: seq t) (i: nat) (a: t) (f: t -> rat): Lemma
//   (requires length s > 0 /\ i <= length s - 1)
//   (ensures
//     sigma i (length (snoc s a) - 2) (fun k -> f (snoc s a).[k]) =$
//     sigma i (length s - 1) (fun k -> f s.[k]))
//   (decreases length s - i) =
//   let f' = fun k -> f (snoc s a).[k] in
//   if i = length s - 1 then
//     ()
//   else
//     calc (=$) {
//       sigma i (length (snoc s a) - 2) f';
//       =${}
//       f s.[i] +$ sigma (i + 1) (length (snoc s a) - 2) f';
//       =${
//         calc (=$) {
//           sigma (i + 1) (length (snoc s a) - 2) f';
//           =${sigma_snoc s (i + 1) a f}
//           sigma (i + 1) (length s - 1) (fun k -> f s.[k]);
//         }
//       }
//       f s.[i] +$ sigma (i + 1) (length s - 1) (fun k -> f s.[k]);
//     }
// #pop-options
// #pop-options

let pow2_subtraction (a b: nat): Lemma
  (requires a >= b)
  (ensures (pow2 (a - b), 1) =$ (pow2 a, pow2 b)) = Math.pow2_plus (a - b) b

let qpow2 (n: int): Tot rat =
  match n >= 0 with
  | true -> (pow2 n, 1)
  | false -> (1, pow2 (-n <: nat))

val qpow2_double_sum: n: int -> Lemma
  (ensures qpow2 n +$ qpow2 n =$ qpow2 (n + 1))
  [SMTPat (qpow2 n +$ qpow2 n)]

let qpow2_mult_even (n: int) (m: nat): Lemma
  (requires m % 2 == 0)
  (ensures qpow2 n *$ (of_int m) =$ qpow2 (n + 1) *$ (of_int (m / 2))) =
  if n < 0 then
    calc (=$) {
      qpow2 n *$ (of_int m);
      =={}
      (m, pow2 (-n));
      =${Math.Lemmas.pow2_double_mult (-n - 1)}
      (m / 2, (pow2 (-(n + 1))));
      =${}
      (1, (pow2 (-(n + 1)))) *$ (m / 2, 1);
      =={assert_norm(pow2 0 == 1)}
      qpow2 (n + 1) *$ of_int (m / 2);
    }
  else
    calc (=$) {
      qpow2 n *$ (of_int m);
      =={}
      (pow2 n * m, 1);
      =={}
      (pow2 n * 2 * (m / 2), 1);
      =={Math.Lemmas.pow2_double_mult n}
      (pow2 (n + 1) * (m / 2), 1);
      =={}
      qpow2 (n + 1) *$ of_int (m / 2);
    }
