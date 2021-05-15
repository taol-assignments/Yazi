module Spec.CRC32.Bits
module BV = FStar.BitVector
module Seq = FStar.Seq
module U32 = FStar.UInt32
module UInt = FStar.UInt

unfold let zero_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < m ==> Seq.index res i == false) /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append (BV.zero_vec #m) a

unfold let zero_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < n ==> Seq.index res i == Seq.index a i) /\ 
    (i >= n /\ i < n + m ==> Seq.index res i == false)
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append a (BV.zero_vec #m)

unfold let ones_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < m ==> Seq.index res i == true) /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append (BV.ones_vec #m) a

unfold let ones_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i.
    (i < n ==> Seq.index res i == Seq.index a i) /\
    (i >= n /\ i < n + m ==> Seq.index res i == true)
}) =
  match m with
  | 0 -> a
  | _ -> Seq.append a (BV.ones_vec #m)

let zero_vec_l_app (#n: nat{n > 0}) (a: BV.bv_t n) (m l: nat): Lemma
  (ensures zero_vec_l l (zero_vec_l m a) == zero_vec_l (m + l) a) =
  assert(Seq.equal (zero_vec_l l (zero_vec_l m a)) (zero_vec_l (m + l) a))

unfold let gf2_plus (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (+@) #n = gf2_plus #n

unfold let gf2_sub (#n: nat{n > 0}) (a b: BV.bv_t n) : Tot (BV.bv_t n) =
  BV.logxor_vec a b

let (-@) #n = gf2_sub #n

unfold let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  forall i.
    Seq.length res == Seq.length s - 1 /\
    (Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)

let gf2_polynomial = Seq.init #bool 33 (fun i ->
  i = 0 || i = 1 || i = 2 || i = 4 || i = 5 || i = 7 || i = 8 || i = 10 || i = 11 ||
  i = 12 || i = 16 || i = 22 || i = 23 || i = 26 || i = 32)

let gf2_polynomial32 = unsnoc gf2_polynomial

type crc32_polynomial = res: U32.t{
  let res' = U32.v res in
  forall i. UInt.nth res' i == Seq.index gf2_polynomial32 i
}

unfold let poly (n: nat{n >= 33}): Tot (p: BV.bv_t n{
  Seq.index p (n - 1) == true
}) =
  assert(Seq.index gf2_polynomial 32 == true);
  zero_vec_l #33 (n - 33) gf2_polynomial

unfold let poly_xor (#n: nat{n >= 32}) (a: BV.bv_t n): Tot (res: BV.bv_t n{
  res == unsnoc ((ones_vec_r 1 a) -@ poly (n + 1))
}) =
  let a' = ones_vec_r 1 a in
  let p = poly (n + 1) in
  let r = a -@ (unsnoc p) in
  let r' = a' -@ p in
  assert(Seq.equal r (unsnoc r'));
  r

let rec poly_mod (#n: nat{n > 32}) (a: BV.bv_t n): Tot (BV.bv_t 32) =
  let p = poly n in
  let b = if Seq.index a (n - 1) then a -@ p else a in
  assert(Seq.index b (n - 1) == false);
  if n = 33 then unsnoc b else poly_mod #(n - 1) (unsnoc b)

val poly_mod_zero: #n: nat{n > 32} -> a: BV.bv_t n {a == BV.zero_vec #n} -> Lemma
  (ensures poly_mod a == BV.zero_vec #32)

val poly_mod_add: #n: nat{n > 32} -> a: BV.bv_t n ->  b: BV.bv_t n -> Lemma
  (ensures (poly_mod a) +@ (poly_mod b) == poly_mod (a +@ b))

val poly_mod_zero_prefix: #n: nat{n > 32} -> a: BV.bv_t n -> m: nat{m > 0} -> Lemma
  (ensures poly_mod (zero_vec_l m (poly_mod a)) == poly_mod (zero_vec_l m a))

val poly_mod_zero_suffix: a: BV.bv_t 32 -> m: nat{m > 0} -> Lemma
  (ensures poly_mod (zero_vec_r m a) == a)

unfold let poly_mod_correct (nzeros: nat{nzeros > 0}) (d res: U32.t) =
  let d' = zero_vec_l nzeros (UInt.to_vec (U32.v d)) in
  forall i. {:pattern UInt.nth (U32.v res) i}
    UInt.nth (U32.v res) i == Seq.index (poly_mod d') i

unfold let poly_mod_u32 (nzeros: nat{nzeros > 0}) (d: U32.t) =
  poly_mod (zero_vec_l nzeros (UInt.to_vec (U32.v d)))

let poly_mod_correct_eq (nzeros: nat{nzeros > 0}) (d res: U32.t): Lemma
  (requires poly_mod_correct nzeros d res)
  (ensures poly_mod_u32 nzeros d == UInt.to_vec (U32.v res)) =
  let open U32 in
  assert(forall i. UInt.nth (v res) i == Seq.index (UInt.to_vec (v res)) i);
  assert(Seq.equal (poly_mod (zero_vec_l nzeros (UInt.to_vec (U32.v d)))) (UInt.to_vec (v res)))
