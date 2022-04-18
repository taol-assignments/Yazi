module Lib.Rational

module Math = FStar.Math.Lemmas
open FStar.Mul

#set-options "--z3refresh --fuel 0 --ifuel 0"
let plus_assoc a b c =
  assert(num (b +$ c) == num b * den c + den b * num c);
  assert(den (b +$ c) == den b * den c)

let distributivity_add_left a b c =
  calc (=$) {
    (a *$ b) +$ (a *$ c);
    =={}
    (num a * num b, den a * den b) +$ (num a * num c, den a * den c);
    =={}
    (num a * num b * (den a * den c) + num a * num c * (den a * den b),
     den a * den b * (den a * den c));
    =={
      Math.paren_mul_right (num a * num b) (den a) (den c);
      Math.paren_mul_right (num a) (num b) (den a);
      Math.swap_mul (num b) (den a);
      Math.paren_mul_right (num a) (den a) (num b);
      
      Math.paren_mul_right (num a * num c) (den a) (den b);
      Math.paren_mul_right (num a) (num c) (den a);
      Math.swap_mul (num c) (den a);
      Math.paren_mul_right (num a) (den a) (num c);
      
      Math.paren_mul_right (den a * den b) (den a) (den c)
    }
    (num a * den a * num b * den c + num a * den a * num c * den b,
     den a * den b * den a * den c);
    =={Math.swap_mul (num a) (den a)}
    (den a * num a * num b * den c + den a * num a * num c * den b,
     den a * den b * den a * den c);
    =={
      Math.paren_mul_right (den a * num a) (num b) (den c);
      Math.paren_mul_right (den a) (num a) (num b * den c);
      Math.paren_mul_right (num a) (num b) (den c);
      
      Math.paren_mul_right (den a * num a) (num c) (den b);
      Math.paren_mul_right (den a) (num a) (num c * den b);
      Math.paren_mul_right (num a) (num c) (den b);
      
      Math.paren_mul_right (den a * den b) (den a) (den c);
      Math.paren_mul_right (den a) (den b) (den a * den c);
      Math.paren_mul_right (den b) (den a) (den c)
    }
    (den a * (num a * num b * den c) + den a * (num a * num c * den b),
     den a * (den b * den a * den c));
    =={
      Math.distributivity_add_right (den a) (num a * num b * den c) (num a * num c * den b)
    }
    (den a * ((num a * num b * den c) + (num a * num c * den b)),
     den a * (den b * den a * den c));
    =${
      common_factor_cancel (den a) (
        num a * num b * den c + num a * num c * den b,
        den b * den a * den c)
    }
    (num a * num b * den c + num a * num c * den b, den b * den a * den c);
    =={
      Math.paren_mul_right (num a) (num b) (den c);
      Math.paren_mul_right (num a) (num c) (den b);
      
      Math.swap_mul (den b) (den a);
      Math.paren_mul_right (den a) (den b) (den c)
    }
    (num a * (num b * den c) + num a * (num c * den b), den a * (den b * den c));
    =={
      Math.distributivity_add_right (num a) (num b * den c) (num c * den b)
    }
    (num a * (num b * den c + num c * den b), den a * (den b * den c));
    =${}
    a *$ (b +$ c);
  }

let mul_eq_l a b a' = assert_norm(a *$ b =$ a' *$ b)

let mul_eq_r a b b' =
  mul_comm a b;
  mul_comm a b'

#set-options "--fuel 1"
let qpow2_double_sum n =
  if n >= 0 then
    Math.Lemmas.pow2_double_sum n
  else begin
    calc (==) {
      qpow2 n +$ qpow2 n =$ qpow2 (n + 1);
      =={}
      (1, pow2 (-n)) +$ (1, pow2 (-n)) =$ qpow2 (n + 1);
      =={}
      (pow2 (-n) + pow2 (-n), (pow2 (-n)) * (pow2 (-n))) =$ qpow2 (n + 1);
      =={Math.Lemmas.pow2_double_sum (-n)}
      (pow2 (-n + 1), (pow2 (-n)) * (pow2 (-n))) =$ qpow2 (n + 1);
      =={Math.Lemmas.pow2_plus (-n) (-n)}
      (pow2 (-n + 1), pow2 (-n * 2)) =$ qpow2 (n + 1);
    };
    if n < -1 then
      calc (==) {
        (pow2 (-n + 1), pow2 (-n * 2)) =$ qpow2 (n + 1);
        =={}
        (pow2 (-n + 1), pow2 (-n * 2)) =$ (1, pow2 (-n - 1));
        =={}
        pow2 (-n + 1) * pow2 (-n - 1) = pow2 (-n * 2);
        =={Math.Lemmas.pow2_plus (-n + 1) (-n - 1)}
        pow2 (-n * 2) = pow2 (-n * 2);
      }
  end

