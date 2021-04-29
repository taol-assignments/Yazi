module Spec.CRC32

module BV = FStar.BitVector
module Seq = FStar.Seq
module U8 = FStar.UInt8
module UInt = FStar.UInt

open FStar.Seq
open FStar.Tactics

val is_rev_refl: (a: U8.t) -> (b: U8.t) -> Lemma
  (ensures is_rev a b <==> is_rev b a)
  [SMTPat (is_rev a b)]
let is_rev_refl a b = ()

private val do_u8_rev: BV.bv_t 8 -> (i: nat{i < 8}) -> (res: BV.bv_t 8) -> BV.bv_t 8
let rec do_u8_rev s i res =
  if i >= 1 then
    do_u8_rev s (i - 1) (Seq.upd res (7 - i) (Seq.index s i))
  else
    Seq.upd res (7 - i) (Seq.index s i)

let u8_rev v =
  let s = UInt.to_vec (U8.v v) in
  let emp = UInt.to_vec 0 in
  U8.uint_to_t (UInt.from_vec (do_u8_rev s 7 emp))

let rec seq_append_index_l (#t: Type) (a b: Seq.seq t): Lemma
  (ensures forall i. i < Seq.length a ==> Seq.index a i == Seq.index (a @| b) i)
  (decreases Seq.length a)
  [SMTPat (a @| b)] =
  match Seq.length a with
  | 0 -> ()
  | _ -> seq_append_index_l (Seq.tail a) b

// let rec seq_append_index_r (#t: Type) (a b: Seq.seq t): Lemma
//   (ensures forall i. i < Seq.length b ==> Seq.index (a @| b) (i + Seq.length a) == Seq.index b i)
//   (decreases Seq.length a)
//   [SMTPat (a @| b)] =
//   match Seq.length a with
//   | 0 -> ()
//   | _ -> seq_append_index_r (Seq.tail a) b

// #set-options "--z3rlimit 120 --z3seed 1"
// let logxor_concat (#n: nat{n > 0}) (#m: nat{m > 0}) (a c: BV.bv_t n) (b d: BV.bv_t m):
//   Lemma (ensures gf2_plus #(n + m) (a @| b) (c @| d) = (a +@ c) @| (b +@ d)) =
//   let ac = a +@ c in
//   let bd = b +@ d in
//   let abcd = gf2_plus #(n + m) (a @| b) (c @| d) in
//   assert_norm(Seq.length (ac @| bd) == (n + m));
//   assert_norm(forall (i: nat). i < n ==> Seq.index (ac @| bd) i = Seq.index abcd i);
//   assert_norm(forall (i: nat). i < m ==> Seq.index (ac @| bd) (n + i) = Seq.index abcd (n + i));
//   assert_norm(Seq.equal (ac @| bd) abcd)
// #reset-options

let logxor_zero_eq (#n: nat{n > 0}) (a: BV.bv_t n): Lemma
  (ensures (BV.logxor_vec a (BV.zero_vec #n)) == a)
  [SMTPat (BV.logxor_vec a (BV.zero_vec #n))] =
    let z = BV.zero_vec #n in
    let x = BV.logxor_vec a z in
    assert_norm(forall (i: nat) (v: BV.bv_t n). i < n ==> Seq.index v i = Seq.index v i <> false);
    assert_norm(Seq.equal x a)

let logxor_eq_zero (#n: nat{n > 0}) (a b: BV.bv_t n): Lemma
  (requires a == b)
  (ensures BV.logxor_vec a b == BV.zero_vec #n)
  [SMTPat (BV.logxor_vec #n a b)] =
  assert(Seq.equal (BV.logxor_vec a b) (BV.zero_vec #n))

let rec logxor_vec_comm (#n: nat{n > 0}) (a b: BV.bv_t n): Lemma
  (ensures BV.logxor_vec a b == BV.logxor_vec b a)
  [SMTPat (BV.logxor_vec a b)] =
  match n with
  | 1 -> ()
  | _ -> let c = BV.logxor_vec a b in
    let c' = BV.logxor_vec b a in
    assert_norm(Seq.index c 0 == Seq.index c' 0);
    logxor_vec_comm #(n - 1) (Seq.tail a) (Seq.tail b)

let logxor_vec_assoc (#n: nat{n > 0}) (a b c: BV.bv_t n): Lemma
  (ensures BV.logxor_vec (BV.logxor_vec a b) c == BV.logxor_vec a (BV.logxor_vec b c))
  [SMTPat (BV.logxor_vec (BV.logxor_vec a b) c); 
   SMTPat (BV.logxor_vec a (BV.logxor_vec b c))] =
  assert(Seq.equal (BV.logxor_vec (BV.logxor_vec a b) c) (BV.logxor_vec a (BV.logxor_vec b c)))

unfold let zero_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i. i < m ==> Seq.index res i == false /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> (BV.zero_vec #m) @| a

unfold let zero_vec_r (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i. i < n ==> Seq.index res i == Seq.index a i /\ 
    (i >= n /\ i < n + m ==> Seq.index res i == false)
}) =
  match m with
  | 0 -> a
  | _ -> a @| (BV.zero_vec #m)

unfold let ones_vec_l (#n: nat{n > 0}) (m: nat) (a: BV.bv_t n): Tot (res: BV.bv_t (n + m){
  forall i. i < m ==> Seq.index res i == true /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> (BV.ones_vec #m) @| a

unfold let poly (n: nat{n >= 33}): Tot (p: BV.bv_t n{
  Seq.head p == true
}) =
  let p = Seq.init #bool 33 (fun i ->
    i = 0 || i = 5 || i = 8 || i = 9 || i = 15 || i = 19 || i = 20 ||
    i = 21 || i = 23 || i = 24 || i = 26 || i = 27 || i = 29 || i = 30) in
  zero_vec_r #33 (n - 33) p

#set-options "--z3rlimit 120 --z3seed 1"
val poly_mod: #n: nat{n > 32} -> a: BV.bv_t n -> Tot (BV.bv_t 32)

let rec poly_mod #n a =
  let p = poly n in
  let b = if Seq.head a then a -@ p else a in
  assert(Seq.head b == false);
  if n = 33 then (Seq.tail b) else poly_mod #(n - 1) (Seq.tail b)
  
unfold let poly_xor (#n: nat{n >= 32}) (a: BV.bv_t n): Tot (res: BV.bv_t n{
  res == Seq.tail ((ones_vec_l 1 a) -@ poly (n + 1))
}) =
  let a' = ones_vec_l 1 a in
  let p = poly (n + 1) in
  let r = a -@ (Seq.tail p) in
  let r' = a' -@ p in
  assert(Seq.equal r (Seq.tail r'));
  r

let poly_xor_aux (#n: nat{n >= 32}) (a b: BV.bv_t n): Lemma
  (ensures (poly_xor a) +@ (poly_xor b) == a +@ b) =
  let p' = Seq.tail (poly (n + 1)) in
  calc (==) {
    (poly_xor a) +@ (poly_xor b);
    =={}
    (a +@ p') +@ (b +@ p');
    =={}
    a +@ (p' +@ b +@ p');
    =={}
    a +@ (p' +@ p' +@ b);
    =={}
    a +@ b;
  }

let rec poly_mod_zero (#n: nat{n > 32}) (a: BV.bv_t n): Lemma
  (ensures poly_mod #(n + 1) (zero_vec_l 1 a) == poly_mod a) =
  let a' = zero_vec_l 1 a in
  assert(Seq.equal (Seq.tail a') a);
  match n with
  | 33 -> assert_norm(poly_mod #34 a' == poly_mod #33 (Seq.tail a'))
  | _ -> poly_mod_zero #(n - 1) (Seq.tail a)

let poly_mod_one (#n: nat{n > 32}) (a: BV.bv_t n): Lemma
  (ensures poly_mod (ones_vec_l 1 a) == poly_mod (poly_xor a)) =
  let a' = ones_vec_l 1 a in
  assert_norm(poly_mod #(n + 1) a' == poly_mod (poly_xor a))

let rec poly_mod_add (#n: nat{n > 32}) (a b: BV.bv_t n): Lemma
  (ensures (poly_mod a) +@ (poly_mod b) == poly_mod (a +@ b)) =
  let a' = Seq.tail a in
  let b' = Seq.tail b in
  let c = a +@ b in
  let c' = gf2_plus #(n - 1) a' b' in

  if Seq.head a = Seq.head b then
    assert(Seq.equal (Seq.tail c) c')
  else
    assert(Seq.head a <> Seq.head b);

  if n = 33 then begin
    if Seq.head a then assert(Seq.equal (poly_mod a) (poly_xor #32 a')) else ();
    if Seq.head b then assert(Seq.equal (poly_mod b) (poly_xor #32 b')) else ();
    
    match Seq.head a = Seq.head b with
    | true -> if Seq.head a then poly_xor_aux #32 a' b' else ()
    | false -> assert(Seq.equal (poly_mod c) (poly_xor c'))
  end else begin
    assert(n > 33);
    if Seq.head a then begin
      assert(Seq.equal (Seq.tail (a -@ (poly n))) (poly_xor #(n - 1) a'));
      assert_norm(poly_mod a == poly_mod (poly_xor #(n - 1) a'))
    end else
      assert_norm(poly_mod a == poly_mod #(n - 1) a');

    if Seq.head b then begin
      assert(Seq.equal (Seq.tail (b -@ (poly n))) (poly_xor #(n - 1) b'));
      assert_norm(poly_mod b == poly_mod (poly_xor #(n - 1) b'))
    end else
      assert_norm(poly_mod b == poly_mod #(n - 1) b');

    match Seq.head a = Seq.head b with
    | true ->
      if Seq.head a then
        let a'' = poly_xor #(n - 1) a' in
        let b'' = poly_xor #(n - 1) b' in
        calc (==) {
          (poly_mod a) +@ (poly_mod b);
          =={}
          (poly_mod a'') +@ (poly_mod b'');
          =={poly_mod_add a'' b''}
          poly_mod (a'' +@ b'');
          =={poly_xor_aux #(n - 1) a' b'}
          poly_mod #(n - 1) (a' +@ b');
          =={}
          poly_mod c;
        }
      else
        calc (==) {
          (poly_mod a) +@ (poly_mod b);
          =={}
          (poly_mod #(n - 1) a') +@ (poly_mod #(n - 1) b');
          =={poly_mod_add #(n - 1) a' b'}
          poly_mod c';
          =={}
          poly_mod c;
        }
    | false ->
      assert(Seq.equal (poly_mod c) (poly_mod (poly_xor c')));
      let x = if Seq.head a then a else b in
      let x' = Seq.tail x in
      let y = if Seq.head a then b else a in
      let y' = Seq.tail y in
      let p' = Seq.tail (poly n) in
      calc (==) {
        (poly_mod x) +@ (poly_mod y);
        =={}
        (poly_mod (poly_xor #(n - 1) x')) +@ (poly_mod #(n - 1) y');
        =={poly_mod_add #(n - 1) (poly_xor #(n - 1) x') y'}
        poly_mod ((poly_xor #(n - 1) x') +@ y');
        =={}
        poly_mod c;
      }
  end
