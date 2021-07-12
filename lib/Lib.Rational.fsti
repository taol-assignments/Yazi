module Lib.Rational

module Math = FStar.Math.Lemmas

open FStar.Calc
open FStar.Mul

type rat = (int & pos)

unfold let num (a: rat) = fst a
unfold let den (a: rat) = snd a

let (=$) (a b: rat): Type0 =
  num a * den b == num b * den a

let eq_refl (a: rat) : Lemma (ensures a =$ a) = ()

let eq_sym (a b: rat): Lemma
  (requires a =$ b)
  (ensures b =$ a)
  [SMTPat (a =$ b)] = ()

let eq_trans (a b c: rat): Lemma
  (requires a =$ b /\ b =$ c)
  (ensures a =$ c)
  [SMTPat (a =$ b); SMTPat (b =$ c)] = ()

let (<=$) (a b: rat): Type0 = num a * den b <= num b * den a
unfold let (>=$) (a b: rat): Type0 = b <=$ a

let le_eq (a b a' b': rat): Lemma
  (requires a =$ a' /\ b =$ b' /\ a <=$ b)
  (ensures a' <=$ b')
  [SMTPat (a =$ a'); SMTPat (b =$ b'); SMTPat (a <=$ b)] = ()

let le_refl (a: rat) : Lemma (ensures a <=$ a) = ()

let le_antisym (a b: rat): Lemma
  (requires a <=$ b /\ b <=$ a)
  (ensures a =$ b)
  [SMTPat (a <=$ b); SMTPat (b <=$ a)] = ()

let le_trans (a b c: rat): Lemma
  (requires a <=$ b /\ b <=$ c)
  (ensures a <=$ c)
  [SMTPat (a <=$ b); SMTPat (b <=$ c)] = ()

let (<$) (a b: rat) = num a * den b < num b * den a
unfold let (>$) (a b: rat) = b <$ a

let lt_eq (a b a' b': rat): Lemma
  (requires a =$ a' /\ b =$ b' /\ a <$ b)
  (ensures a' <$ b')
  [SMTPat (a =$ a'); SMTPat (b =$ b'); SMTPat (a <$ b)] = ()

let lt_not_eq (a b: rat) : Lemma
  (requires a <$ b)
  (ensures a <> b)
  [SMTPat (a <$ b)]= ()

let lt_trans (a b c: rat): Lemma
  (requires a <$ b /\ b <$ c)
  (ensures a <$ c)
  [SMTPat (a <$ b); SMTPat (b <$ c)] = ()

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
  [SMTPat (a +$ b)] = ()

let plus_zero_l (a: rat): Lemma
  (ensures zero +$ a =$ a)
  [SMTPat (zero +$ a)] = ()

let plus_zero_r (a: rat): Lemma
  (ensures a +$ zero =$ a)
  [SMTPat (a +$ zero)] = ()

#set-options "--z3rlimit 200"
let plus_assoc (a b c: rat): Lemma
  (ensures (a +$ b) +$ c =$ a +$ (b +$ c))
  [SMTPatOr [[SMTPat ((a +$ b) +$ c)]; [SMTPat (a +$ (b +$ c))]]] = ()

let op_Star_Dollar (a b: rat): Tot rat = (num a * num b, den a * den b)

let mul_zero_l (a: rat): Lemma
  (ensures a *$ zero =$ zero)
  [SMTPat (a *$ zero)] = ()

let mul_zero_r (a: rat): Lemma
  (ensures zero *$ a =$ zero)
  [SMTPat (zero *$ a)] = ()

let mul_comm (a b: rat): Lemma
  (ensures a *$ b =$ b *$ a)
  [SMTPat (a *$ b)] = ()

let mul_assoc (a b c: rat): Lemma
  (ensures (a *$ b) *$ c =$ a *$ (b *$ c))
  [SMTPatOr [[SMTPat ((a *$ b) *$ c)]; [SMTPat (a *$ (b *$ c))]]] = ()

let of_int (a: int): rat = (a, 1)
