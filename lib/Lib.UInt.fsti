module Lib.UInt

module BV = FStar.BitVector
module Math = FStar.Math.Lemmas
module U32 = FStar.UInt32
module UInt = FStar.UInt
module Seq = FStar.Seq

open FStar.Mul

#set-options "--z3rlimit 120 --z3seed 1 --fuel 16 --ifuel 16"
val cast_zero_prefix:
    #n: nat
  -> v: UInt.uint_t n
  -> m: nat{m >= n}
  -> Lemma
  (requires pow2 n <= pow2 m)
  (ensures UInt.to_vec #m v == Seq.append (Seq.create (m - n) false) (UInt.to_vec v))

val zero_prefix_eq:
    #n: nat{0 < n}
  -> #m: nat{0 < m /\ m <= n}
  -> vn: UInt.uint_t n
  -> vm: UInt.uint_t m
  -> Lemma
  (requires forall (i: nat{i < n}).
    (i < n - m ==> UInt.nth vn i == false) /\
    (n - m <= i ==> UInt.nth vn i == UInt.nth vm (i - n + m)))
  (ensures vn == vm)

val logand_256: (r: U32.t) -> Lemma
  (ensures forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth (U32.v (U32.logand r 0xFFul)) i == false) /\
    (i >= 32 - 8 ==> UInt.nth (U32.v (U32.logand r 0xFFul)) i == UInt.nth (U32.v r) i))

let rec uint_one_vec (#n: nat{n > 0}) (v: UInt.uint_t n): Lemma
  (requires v == 1)
  (ensures forall i. {:pattern UInt.nth v i}
    (i == n - 1 ==> UInt.nth #n v i == true) /\
    (i < n - 1 ==> UInt.nth #n v i == false)) =
  match n with
  | 1 -> ()
  | _ -> uint_one_vec #(n - 1) v

let mask_bit_status (#n: nat{n > 0}) (s: nat{s < n}) (v: UInt.uint_t n): Lemma
  (requires v == UInt.shift_left 1 s)
  (ensures forall j. {:pattern UInt.nth v j}
    (j == n - 1 - s ==> UInt.nth v j == true) /\
    (j <> n - 1 - s ==> UInt.nth v j == false)) =
  uint_one_vec #n 1

let mask_logor_status (#n: nat{n > 0}) (s: nat{s < n}) (mask v: UInt.uint_t n): Lemma
  (requires mask == UInt.shift_left 1 s /\ UInt.nth v (n - 1 - s) == false)
  (ensures
    forall j. {:pattern UInt.nth (UInt.logor v mask) j}
    (j <> n - 1 - s ==> UInt.nth (UInt.logor v mask) j == UInt.nth v j) /\
    (j == n - 1 - s ==> UInt.nth (UInt.logor v mask) j == true)) =
  mask_bit_status s mask

let mask_logand_status (#n: nat{n > 0}) (s: nat{s < n}) (mask v: UInt.uint_t n): Lemma
  (requires mask == UInt.shift_left 1 s)
  (ensures
    forall j. {:pattern UInt.nth (UInt.logand v mask) j}
    (j <> n - 1 - s ==> UInt.nth (UInt.logand v mask) j == false) /\
    (j == n - 1 - s ==> UInt.nth (UInt.logand v mask) j == (UInt.nth v (n - 1 - s) = true))) =
  mask_bit_status s mask

#set-options "--fuel 1 --ifuel 1"
let logand_one_ne (#n: nat{n > 0}) (a: UInt.uint_t n): Lemma
  (requires UInt.logand a (UInt.one n) <> 1)
  (ensures UInt.logand a (UInt.one n) == 0) =
  let one = UInt.one n in
  let s = UInt.logand a one in
  uint_one_vec one;
  assert(forall i. i < n - 1 ==> UInt.nth s i == false);
  if UInt.nth (UInt.logand a one) (n - 1) then
    UInt.nth_lemma s one
  else
    UInt.nth_lemma s (UInt.zero n)

#set-options "--z3rlimit 120 --fuel 128 --ifuel 128 --z3seed 13"
let one_shift_left (s: U32.t{U32.v s < 32}): Lemma
  (ensures forall (i: nat{i < 32}).
    (i == 31 - U32.v s ==> UInt.nth (U32.v (U32.shift_left 1ul s)) i == true) /\
    (i <> 31 - U32.v s ==> UInt.nth (U32.v (U32.shift_left 1ul s)) i == false)) = ()

let logxor_logand_distr (#n: nat{n > 0}) (a b c: UInt.uint_t n): Lemma
  (ensures
    UInt.logand (UInt.logxor a b) c ==
    UInt.logxor (UInt.logand a c) (UInt.logand b c)) =
  assert(Seq.equal
    (UInt.to_vec (UInt.logand (UInt.logxor a b) c))
    (UInt.to_vec (UInt.logxor (UInt.logand a c) (UInt.logand b c))))

#set-options "--fuel 0 --ifuel 0"
let shift_left_append (#n: nat{n > 0}) (a s1 s2: UInt.uint_t n): Lemma
  (ensures UInt.shift_left (UInt.shift_left a s1) s2 == UInt.shift_left a (s1 + s2))
  [SMTPat (UInt.shift_left (UInt.shift_left a s1) s2)] =
  calc (==) {
    UInt.shift_left (UInt.shift_left a s1) s2;
    =={}
    (((a * pow2 s1) % pow2 n) * pow2 s2) % pow2 n;
    =={Math.lemma_mod_mul_distr_l (a * pow2 s1) (pow2 s2) (pow2 n)}
    ((a * pow2 s1) * pow2 s2) % pow2 n;
    =={Math.paren_mul_right a (pow2 s1) (pow2 s2)}
    (a * ((pow2 s1) * (pow2 s2))) % pow2 n;
    =={Math.pow2_plus s1 s2}
    (a * pow2 (s1 + s2)) % pow2 n;
    =={UInt.shift_left_value_lemma a (s1 + s2)}
    UInt.shift_left a (s1 + s2);
  }

let zero_prefix_vec (n: pos) (v: Seq.seq bool): Lemma
  (requires Seq.length v > 0)
  (ensures UInt.from_vec #(n + Seq.length v) (Seq.append (BV.zero_vec #n) v) ==
    UInt.from_vec #(Seq.length v) v)
  [SMTPat (UInt.from_vec #(n + Seq.length v) (Seq.append (BV.zero_vec #n) v))] =
  let l = Seq.length v in
  let zero = BV.zero_vec #n in
  UInt.append_lemma #n #l zero v

let one_prefix_vec (n: pos) (v: Seq.seq bool): Lemma
  (requires Seq.length v > 0)
  (ensures UInt.from_vec #(n + Seq.length v) (Seq.append (BV.ones_vec #n) v) ==
    ((pow2 n) - 1) * pow2 (Seq.length v) + UInt.from_vec #(Seq.length v) v)
  [SMTPat (UInt.from_vec #(n + Seq.length v) (Seq.append (BV.ones_vec #n) v))] =
  let l = Seq.length v in
  let one = BV.ones_vec #n in
  UInt.append_lemma #n #l one v
