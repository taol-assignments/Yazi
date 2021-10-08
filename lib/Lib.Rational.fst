module Lib.Rational

module Math = FStar.Math.Lemmas

#set-options "--fuel 0 --ifuel 0"
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
