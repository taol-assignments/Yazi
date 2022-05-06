module Lib.Rational

module Math = FStar.Math.Lemmas
open FStar.Mul

#set-options "--z3refresh --fuel 0 --ifuel 0"
let plus_assoc a b c =
  assert(num (b +$ c) == num b * den c + den b * num c);
  assert(den (b +$ c) == den b * den c)

let sub_eq_l_rev_aux (a b b': rat): Lemma
  (requires a -$ b' =$ a -$ b)
  (ensures (num b * den a) * (den a * den b') == (num b' * den a) * (den a * den b)) =
  let c = a -$ b in
  let c' = a -$ b' in
  calc (==) {
    (num a * den b) * (den a * den b') - (num b * den a) * (den a * den b');
    =={}
    (num a * den b - num b * den a) * (den a * den b');
    =={}
    num c * den c';
    =={}
    num c' * den c;
    =={}
    (num a * den b' - num b' * den a) * (den a * den b);
    =={}
    (num a * den b') * (den a * den b) - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.swap_mul (den a) (den b)}
    (num a * den b') * (den b * den a) - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.paren_mul_right (num a * den b') (den b) (den a)}
    (num a * den b') * den b * den a - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.paren_mul_left (num a) (den b') (den b)}
    num a * den b' * den b * den a - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.paren_mul_right (num a) (den b') (den b)}
    num a * (den b' * den b) * den a - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.swap_mul (den b') (den b)}
    num a * (den b * den b') * den a - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.paren_mul_right (num a) (den b * den b') (den a)}
    num a * ((den b * den b') * den a) - (num b' * den a) * (den a * den b);
    =={
      Math.Lemmas.paren_mul_left (den b) (den b') (den a);
      Math.Lemmas.paren_mul_right (den b) (den b') (den a);
      Math.Lemmas.swap_mul (den b') (den a)
    }
    num a * (den b * (den a * den b')) - (num b' * den a) * (den a * den b);
    =={Math.Lemmas.paren_mul_left (num a) (den b) (den a * den b')}
    (num a * den b) * (den a * den b') - (num b' * den a) * (den a * den b);
  }

let int_mul_eq (a b c: int): Lemma
  (requires a * b == a * c /\ a <> 0)
  (ensures b == c) = ()

let sub_eq_l_rev a b b' =
  calc (==) {
    (den a * den a) * (num b * den b');
    =={Math.Lemmas.paren_mul_left (den a) (den a) (num b * den b')}
    den a * den a * (num b * den b');
    =={
      Math.Lemmas.paren_mul_left (den a) (num b) (den b');
      Math.Lemmas.paren_mul_right (den a) (num b) (den b')
    }
    den a * ((den a * num b) * den b');
    =={Math.Lemmas.swap_mul (num b) (den a)}
    den a * ((num b * den a) * den b');
    =={Math.Lemmas.paren_mul_left (num b) (den a) (den b')}
    den a * (num b * den a * den b');
    =={Math.Lemmas.paren_mul_right (num b) (den a) (den b')}
    den a * (num b * (den a * den b'));
    =={Math.Lemmas.paren_mul_right (den a) (num b) (den a * den b')}
    den a * num b * (den a * den b');
    =={Math.Lemmas.paren_mul_left (den a) (num b) (den a * den b')}
    (den a * num b) * (den a * den b');
    =={Math.Lemmas.swap_mul (den a) (num b)}
    (num b * den a) * (den a * den b');
    =={sub_eq_l_rev_aux a b b'}
    (num b' * den a) * (den a * den b);
    =={Math.Lemmas.swap_mul (num b') (den a)}
    (den a * num b') * (den a * den b);
    =={
      Math.Lemmas.paren_mul_left (den a) (num b') (den a * den b);
      Math.Lemmas.paren_mul_right (den a) (num b') (den a * den b)
    }
    den a * (num b' * (den a * den b));
    =={
      Math.Lemmas.paren_mul_left (num b') (den a) (den b);
      Math.Lemmas.paren_mul_right (num b') (den a) (den b)
    }
    den a * ((num b' * den a) * den b);
    =={Math.Lemmas.swap_mul (num b') (den a)}
    den a * ((den a * num b') * den b);
    =={
      Math.Lemmas.paren_mul_left (den a) (num b') (den b);
      Math.Lemmas.paren_mul_right (den a) (num b') (den b);
      Math.Lemmas.paren_mul_right (den a) (den a) (num b' * den b);
      Math.Lemmas.paren_mul_left (den a * den a) (num b') (den b)
    }
    (den a * den a) * (num b' * den b);
  };
  int_mul_eq (den a * den a) (num b * den b') (num b' * den b)

let sub_eq_l a b b' =
  calc (==) {
    (num b * den a) * den a * den b';
    =={Math.Lemmas.paren_mul_right (num b * den a) (den a) (den b')}
    (num b * den a) * (den a * den b');
    =={
      Math.Lemmas.swap_mul (den a) (num b);
      Math.Lemmas.swap_mul (den b') (den a)
    }
    (den a * num b) * (den b' * den a);
    =={Math.Lemmas.paren_add_right (den a * num b) (den b') (den a)}
    (den a * num b) * den b' * den a;
    =={Math.Lemmas.paren_add_left (den a) (num b) (den b')}
    den a * (num b * den b') * den a;
    =={}
    den a * (num b' * den b) * den a;
    =={
      Math.Lemmas.paren_mul_left (num a * den b) (den a) (den b');
      Math.Lemmas.paren_mul_right (num b') (den b) (den a);
      Math.Lemmas.paren_mul_left (den a) (num b') (den b * den a)
    }
    (den a * num b') * (den b * den a);
    =={Math.swap_mul (den a * num b') (den b * den a)}
    (den b * den a) * (den a * num b');
  };
  calc (==) {
    (num a * den b) * den a * den b';
    =={
      Math.Lemmas.paren_mul_left (num a) (den b) (den a);
      Math.Lemmas.paren_mul_right (num a) (den b) (den a)
    }
    num a * (den b * den a) * den b';
    =={Math.Lemmas.swap_mul (num a) (den b * den a)}
    (den b * den a) * num a * den b';
    =={Math.Lemmas.paren_mul_right (den b * den a) (num a) (den b')}
    (den b * den a) * (num a * den b');
  };
  calc (==) {
    (num a * den b - num b * den a) * (den a * den b');
    =={}
    (num a * den b) * den a * den b' - (num b * den a) * den a * den b';
    =={}
    (den b * den a) * (num a * den b') - (den b * den a) * (den a * num b');
    =={}
    (den b * den a) * (num a * den b' - den a * num b');
  }

let sub_plus_l a b c =
  calc (=$) {
    (a -$ b) +$ c;
    =${}
    (a +$ (zero -$ b)) +$ c;
    =${plus_assoc a (zero -$ b) c}
    a +$ ((zero -$ b) +$ c);
    =${}
    a +$ (c +$ (zero -$ b));
    =${}
    a +$ (c -$ b);
    =${sub_neg a c b}
    a -$ (b -$ c);
  }

let sub_plus_r a b c =
  calc (=$) {
    a +$ (b -$ c);
    =${}
    a +$ ((b -$ c) +$ zero);
    =${sub_plus_l b c zero}
    a +$ (b -$ (c -$ zero));
    =${sub_neg b zero c}
    a +$ (b +$ (zero -$ c));
    =${plus_assoc a b (zero -$ c)}
    (a +$ b) +$ (zero -$ c);
    =${sub_neg (a +$ b) zero c}
    (a +$ b) -$ (c -$ zero);
    =${}
    (a +$ b) -$ c;
  }

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

