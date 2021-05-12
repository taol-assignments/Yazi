module Spec.CRC32

module BV = FStar.BitVector
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Seq
open FStar.Mul

private val do_u8_rev: BV.bv_t 8 -> (i: nat{i < 8}) -> (res: BV.bv_t 8) -> BV.bv_t 8
let rec do_u8_rev s i res =
  if i >= 1 then
    do_u8_rev s (i - 1) (Seq.upd res (7 - i) (Seq.index s i))
  else
    Seq.upd res (7 - i) (Seq.index s i)

private val do_uint_rev:
    #n: nat{n > 0}
  -> s: BV.bv_t n
  -> i: nat{i < n}
  -> res: BV.bv_t n{forall j. j > i ==> Seq.index res (n - j - 1) == Seq.index s j}
  -> r: BV.bv_t n {forall j. Seq.index s j == Seq.index r (n - j - 1)}

let rec do_uint_rev #n s i res =
  if i >= 1 then
    do_uint_rev s (i - 1) (Seq.upd res (n - i - 1) (Seq.index s i))
  else
    Seq.upd res (n - i - 1) (Seq.index s i)
    
let u8_rev v =
  let s = UInt.to_vec (U8.v v) in
  let emp = UInt.to_vec 0 in
  U8.uint_to_t (UInt.from_vec (do_uint_rev s 7 emp))

let u32_rev v =
  let s = UInt.to_vec (U32.v v) in
  let emp = UInt.to_vec 0 in
  U32.uint_to_t (UInt.from_vec (do_uint_rev s 31 emp))

let rec seq_append_index_l (#t: Type) (a b: Seq.seq t): Lemma
  (ensures forall i. i < Seq.length a ==> Seq.index a i == Seq.index (a @| b) i)
  (decreases Seq.length a) =
  match Seq.length a with
  | 0 -> ()
  | _ -> seq_append_index_l (Seq.tail a) b

let rec seq_append_index_r (#t: Type) (a b: Seq.seq t): Lemma
  (ensures forall i. i < Seq.length b ==> Seq.index (a @| b) (i + Seq.length a) == Seq.index b i)
  (decreases Seq.length a) =
  match Seq.length a with
  | 0 -> ()
  | _ -> seq_append_index_r (Seq.tail a) b

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
  forall i. (i < m ==> Seq.index res i == true) /\
    (i >= m /\ i < n + m ==> Seq.index res i == Seq.index a (i - m))
}) =
  match m with
  | 0 -> a
  | _ -> (BV.ones_vec #m) @| a

unfold let poly (n: nat{n >= 33}): Tot (p: BV.bv_t n{
  Seq.head p == true
}) =
  zero_vec_r #33 (n - 33) gf2_polynomial

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

let poly_xor_zero_suffix (#n: nat{n >= 32}) (a: BV.bv_t n) (m: nat) (l: nat): Lemma
  (ensures forall i. Seq.index (poly_xor (zero_vec_r m a)) i ==
    Seq.index (poly_xor (zero_vec_r l a)) i) = ()

let rec poly_xor_zero_vec_r (#n: nat{n >= 32}) (a: BV.bv_t n) (m: nat): Lemma
  (ensures zero_vec_r m (poly_xor a) == poly_xor (zero_vec_r m a)) =
  match m with
  | 0 -> ()
  | _ ->
    let b = zero_vec_r m (poly_xor a) in
    let c = poly_xor (zero_vec_r m a) in
    let b' = zero_vec_r (m - 1) (poly_xor a) in
    let c' = poly_xor (zero_vec_r (m - 1) a) in
    poly_xor_zero_suffix a m (m - 1);
    poly_xor_zero_vec_r a (m - 1);
    assert(forall i. Seq.index b i == Seq.index b' i);
    assert(forall i. Seq.index c i == Seq.index c' i);
    assert(Seq.index b (m + n - 1) == Seq.index c (m + n - 1));
    assert(Seq.equal b c)

let poly_xor_sub_eq (#n: nat{n > 32}) (a: BV.bv_t n): Lemma
  (ensures poly_xor #(n - 1) (Seq.tail a) == Seq.tail (a -@ (poly n))) =
  assert(Seq.equal (poly_xor #(n - 1) (Seq.tail a)) (Seq.tail (a -@ (poly n))))

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

let rec poly_mod_zero (#n: nat{n > 32}) (a: BV.bv_t n {a == BV.zero_vec #n}): Lemma
  (ensures poly_mod a == BV.zero_vec #32) =
  match n with
  | 33 -> assert_norm(Seq.equal (poly_mod a) (BV.zero_vec #32))
  | _ -> 
    assert_norm(Seq.equal (Seq.tail a) (BV.zero_vec #(n - 1)));
    poly_mod_zero #(n - 1) (Seq.tail a)

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

unfold let magic_matrix_pattern (nzeros: nat{nzeros > 0}) (i: nat{i < 32}):
  res: BV.bv_t (32 + nzeros){
    forall j. (j == i ==> Seq.index res j == true) /\ (j <> i ==> Seq.index res j == false)
  } =
  let zero_right = BV.zero_vec #(nzeros + 32 - i - 1) in
  let one = ones_vec_l 1 zero_right in
  zero_vec_l i one

unfold let is_magic_matrix_elem (nzeros: nat{nzeros > 0}) (i: nat {i < 32}) (v: BV.bv_t 32) =
  poly_mod (magic_matrix_pattern nzeros i) == v

type matrix_seq = s:Seq.seq (BV.bv_t 32) {length s <= 32}

type sub_matrix_t (nzeros: nat{nzeros > 0}) = m: matrix_seq{
  forall i. i < Seq.length m ==> is_magic_matrix_elem nzeros i (index m i)
}

type matrix_t (nzeros: nat{nzeros > 0}) = m: sub_matrix_t nzeros{Seq.length m == 32}

val magic_matrix_init: s: sub_matrix_t 1 -> Tot (matrix_t 1) (decreases 32 - (Seq.length s))

let rec magic_matrix_init s =
  let l = Seq.length s in
  if l = 0 then begin
    let m = ones_vec_l 1 (BV.zero_vec #32) in
    let n = poly_xor (BV.zero_vec #32) in
    calc (==) {
      poly_mod #33 m;
      =={assert(Seq.head m == true)}
      Seq.tail (m -@ poly 33);
      =={}
      n;
    };
    let res = s @| (Seq.create 1 n) in
    calc (==) {
      Seq.index res l;
      =={seq_append_index_r s (Seq.create 1 n)}
      Seq.index (Seq.create 1 n) 0;
      =={}
      n;
    };
    magic_matrix_init res
  end else if l < 32 then begin
    let n = magic_matrix_pattern 1 l in
    let res = s @| (Seq.create 1 (poly_mod n)) in
    calc (==) {
      Seq.index res l;
      =={seq_append_index_r s (Seq.create 1 (poly_mod n))}
      Seq.index (Seq.create 1 (poly_mod n)) 0;
      =={}
      poly_mod n;
    };
    magic_matrix_init res
  end else 
    s

type matrix_dividend (nzeros: nat{nzeros > 0}) = d: BV.bv_t (32 + nzeros) {
  forall i. i > 31 /\ i < Seq.length d ==> Seq.index d i == false
}

val bit_extract:
    #nzeros: nat{nzeros > 0}
  -> n: matrix_dividend nzeros
  -> i: nat{i < 32}
  -> res: BV.bv_t (32 + nzeros) {
      forall j. (j == i ==> Seq.index res j == Seq.index n j) /\
        (j <> i ==> Seq.index res j == false)
    }

let bit_extract #nzeros n i =
  let zero_right = BV.zero_vec #(nzeros + 32 - i - 1) in
  let bit = (Seq.create 1 (Seq.index n i)) @| zero_right in
  zero_vec_l #(nzeros + 32 - i) i bit

val bit_sum:
    #nzeros: nat{nzeros > 0}
  -> n: matrix_dividend nzeros
  -> i: nat{i < 32}
  -> res: BV.bv_t (32 + nzeros) {
    forall j. (j <= i ==> Seq.index res j == Seq.index n j) /\ (j > i ==> Seq.index res j == false)
  }

let rec bit_sum #nzeros n i =
  match i with
  | 0 -> bit_extract n i
  | _ -> (bit_extract n i) +@ (bit_sum n (i - 1))

val do_magic_matrix_times:
    #nzeros: nat{nzeros > 0}
  -> m: matrix_t nzeros
  -> n: BV.bv_t 32
  -> i: nat{i < 32}
  -> res: BV.bv_t 32{
      res == poly_mod (bit_extract (zero_vec_r nzeros n) i)
    }

let do_magic_matrix_times
  (#nzeros: nat{nzeros > 0}) (m: matrix_t nzeros) (n: BV.bv_t 32) (i: nat{i < 32}) =
  if Seq.index n i then begin
    Seq.index m i
  end else begin
    assert(Seq.equal (bit_extract (zero_vec_r nzeros n) i) (BV.zero_vec #(32 + nzeros)));
    poly_mod_zero (bit_extract (zero_vec_r nzeros n) i);
    BV.zero_vec #32
  end

val magic_matrix_times':
    #nzeros: nat{nzeros > 0}
  -> m: matrix_t nzeros
  -> n: BV.bv_t 32
  -> i: nat{i < 32}
  -> res: BV.bv_t 32{
    res == poly_mod (bit_sum (zero_vec_r nzeros n) i)
  }

let rec magic_matrix_times'
  (#nzeros: nat{nzeros > 0}) (m: matrix_t nzeros) (n: BV.bv_t 32) (i: nat{i < 32}) =
  match i with
  | 0 -> do_magic_matrix_times m n i
  | _ -> 
    let n' = do_magic_matrix_times m n i in
    poly_mod_add (bit_extract (zero_vec_r nzeros n) i) (bit_sum (zero_vec_r nzeros n) (i - 1));
    n' +@ magic_matrix_times' m n (i - 1)

val magic_matrix_times:
  #nzeros: nat {nzeros > 0} ->
  matrix_t nzeros ->
  n: BV.bv_t 32 ->
  res: BV.bv_t 32 {res == poly_mod (zero_vec_r nzeros n)}

let magic_matrix_times #nzeros m n =
  assert_norm(Seq.equal (bit_sum (zero_vec_r nzeros n) 31) (zero_vec_r nzeros n));
  magic_matrix_times' m n 31

#set-options "--z3rlimit 200"
let rec poly_mod_zero_suffix (#n: nat{n > 32}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures poly_mod (zero_vec_r m (poly_mod a)) == poly_mod (zero_vec_r m a)) =
  assert(Seq.equal (zero_vec_r #(n - 1) m (Seq.tail a)) (Seq.tail (zero_vec_r m a)));
  if n = 33 then
    if Seq.index a 0 then
      calc (==) {
        poly_mod (zero_vec_r m (poly_mod a));
        =={assert(Seq.equal (poly_mod a) (poly_xor #(n - 1) (Seq.tail a)))}
        poly_mod (zero_vec_r m (poly_xor #(n - 1) (Seq.tail a)));
        =={
          let left = (zero_vec_r m (poly_xor #(n - 1) (Seq.tail a))) in
          let right = (poly_xor #(n + m - 1) (Seq.tail (zero_vec_r m a))) in
          assert(Seq.equal left right)
        }
        poly_mod (poly_xor #(n + m - 1) (Seq.tail (zero_vec_r m a)));
        =={poly_xor_sub_eq (zero_vec_r m a)}
        poly_mod (zero_vec_r m a);
      }
    else
      calc (==) {
        poly_mod (zero_vec_r m (poly_mod a));
        =={}
        poly_mod (zero_vec_r #(n - 1) m (Seq.tail a));
        =={}
        poly_mod #(n + m - 1) (Seq.tail (zero_vec_r m a));
        =={}
        poly_mod (zero_vec_r m a);
      }
  else
    if Seq.index a 0 then
      calc (==) {
        poly_mod (zero_vec_r m (poly_mod a));
        =={}
        poly_mod (zero_vec_r m (poly_mod #(n - 1) (Seq.tail (a -@ (poly n)))));
        =={poly_xor_sub_eq a}
        poly_mod (zero_vec_r m (poly_mod (poly_xor #(n - 1) (Seq.tail a))));
        =={poly_mod_zero_suffix (poly_xor #(n - 1) (Seq.tail a)) m}
        poly_mod (zero_vec_r m (poly_xor #(n - 1) (Seq.tail a)));
        =={poly_xor_zero_vec_r #(n - 1) (Seq.tail a) m}
        poly_mod (poly_xor (zero_vec_r #(n - 1) m (Seq.tail a)));
        =={}
        poly_mod (poly_xor #(n + m - 1) (Seq.tail (zero_vec_r m a)));
        =={poly_xor_sub_eq (zero_vec_r m a)}
        poly_mod (zero_vec_r m a);
      }
    else
      calc (==) {
        poly_mod (zero_vec_r m (poly_mod a));
        =={}
        poly_mod (zero_vec_r m (poly_mod #(n - 1) (Seq.tail a)));
        =={poly_mod_zero_suffix #(n - 1) (Seq.tail a) m}
        poly_mod (zero_vec_r #(n - 1) m (Seq.tail a));
        =={}
        poly_mod #(n + m - 1) (Seq.tail (zero_vec_r m a));
        =={}
        poly_mod (zero_vec_r m a);
      }

let magic_matrix_times_double
  (#nzeros: nat{nzeros > 0}) (m: matrix_t nzeros) (i: nat{i < 32}): Lemma
  (ensures is_magic_matrix_elem (nzeros * 2) i (magic_matrix_times m (Seq.index m i))) =
  let p = magic_matrix_pattern nzeros i in
  let p' = magic_matrix_pattern (nzeros * 2) i in
  let p'' = zero_vec_r nzeros p in
  let n = magic_matrix_times m (Seq.index m i) in
  poly_mod_zero_suffix p nzeros;
  assert(forall j.{:pattern Seq.index p' j} j < 32 + nzeros ==> Seq.index p j == Seq.index p' j);
  assert(forall j.{:pattern Seq.index p'' j} j < 32 + nzeros ==> Seq.index p j == Seq.index p'' j);
  assert(forall j.{:pattern Seq.index p' j} j >= 32 + nzeros ==> Seq.index p' j == false);
  assert(forall j.{:pattern Seq.index p'' j} j >= 32 + nzeros ==> Seq.index p'' j == false);
  assert(Seq.equal p'' p');
  calc (==) {
    n;
    =={}
    poly_mod (zero_vec_r nzeros (Seq.index m i));
    =={}
    poly_mod (zero_vec_r nzeros (poly_mod p));
    =={}
    poly_mod (zero_vec_r nzeros p);
    =={}
    poly_mod p';
    =={}
    poly_mod (magic_matrix_pattern (nzeros * 2) i);
  }

val magic_matrix_square':
    #nzeros: nat{nzeros > 0}
  -> m: matrix_t nzeros
  -> s: sub_matrix_t (nzeros * 2)
  -> Tot (matrix_t (nzeros * 2))
    (decreases 32 - (Seq.length s))

let rec magic_matrix_square' #nzeros m s =
  if Seq.length s < 32 then begin
    magic_matrix_times_double m (Seq.length s);
    let n: BV.bv_t 32 = magic_matrix_times m (Seq.index m (Seq.length s)) in
    let res = s @| (Seq.create 1 n) in
    seq_append_index_r s (Seq.create 1 n);
    calc (==) {
      poly_mod (magic_matrix_pattern (nzeros * 2) (Seq.length s));
      =={}
      n;
      =={}
      Seq.index (Seq.create 1 n) 0;
      =={}
      Seq.index res (Seq.length s);
    };
    assert(forall i.{:pattern Seq.index res i}
      i < Seq.length s ==> Seq.index res i == Seq.index s i);
    assert(forall i. i < Seq.length res ==> is_magic_matrix_elem (nzeros * 2) i (Seq.index res i));
    magic_matrix_square' #nzeros m res
  end
  else
    s

val magic_matrix_square:
    #nzeros: nat {nzeros > 0}
  -> matrix_t nzeros
  -> Tot (matrix_t (nzeros * 2))

let magic_matrix_square #_ m =
  magic_matrix_square' m (Seq.empty #(BV.bv_t 32))
