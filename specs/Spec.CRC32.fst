module Spec.CRC32

module BV = FStar.BitVector
module Math = FStar.Math.Lib
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Seq
open FStar.Mul

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

#set-options "--z3rlimit 120 --z3seed 1"
let poly_xor_zero_prefix (#n: nat{n >= 32}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures forall (i: nat{i > 0}).
    i < Seq.length (zero_vec_l m a) ==>
    Seq.index (poly_xor (zero_vec_l m a)) i ==
    Seq.index (poly_xor (zero_vec_l (m - 1) a)) (i - 1)) = ()

let zero_vec_l_aux (#n: nat{n > 0}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures forall (i: nat{i > 0}).
    i < Seq.length (zero_vec_l m a) ==>
   Seq.index (zero_vec_l m a) i == Seq.index (zero_vec_l (m - 1) a) (i - 1)) = ()

unfold let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  forall i.
    Seq.length res == Seq.length s - 1 /\
    (Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)

unfold let last (#a: Type) (s: Seq.seq a{Seq.length s > 0}) =
  Seq.index s (Seq.length s - 1)

let rec poly_xor_zero_vec_l (#n: nat{n >= 32}) (a: BV.bv_t n) (m: nat): Lemma
  (ensures zero_vec_l m (poly_xor a) == poly_xor (zero_vec_l m a)) =
  match m with
  | 0 -> ()
  | _ ->
    let b = zero_vec_l m (poly_xor a) in
    let c = poly_xor (zero_vec_l m a) in
    let b' = zero_vec_l (m - 1) (poly_xor a) in
    let c' = poly_xor (zero_vec_l (m - 1) a) in
    let p = poly (n + m + 1) in
    let p' = unsnoc p in
    poly_xor_zero_prefix a m;
    zero_vec_l_aux (poly_xor a) m;
    poly_xor_zero_vec_l a (m - 1);
    calc (==) {
      Seq.index c 0;
      =={}
      Seq.index ((zero_vec_l m a) -@ p') 0;
      =={
        assert(Seq.index (zero_vec_l m a) 0 == false);
        assert(Seq.index p 0 == false);
        assert(Seq.index p' 0 == false)
      }
      false;
    };
    assert(Seq.index b 0 == Seq.index c 0);
    assert(Seq.equal b c)

let poly_xor_sub_eq (#n: nat{n > 32}) (a: BV.bv_t n): Lemma
  (ensures poly_xor #(n - 1) (unsnoc a) == unsnoc (a -@ (poly n))) =
  assert(Seq.equal (poly_xor #(n - 1) (unsnoc a)) (unsnoc (a -@ (poly n))))

let poly_xor_aux (#n: nat{n >= 32}) (a b: BV.bv_t n): Lemma
  (ensures (poly_xor a) +@ (poly_xor b) == a +@ b) =
  let p' = unsnoc (poly (n + 1)) in
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
    assert_norm(Seq.equal (unsnoc a) (BV.zero_vec #(n - 1)));
    poly_mod_zero #(n - 1) (unsnoc a)

let rec poly_mod_add (#n: nat{n > 32}) (a b: BV.bv_t n): Lemma
  (ensures (poly_mod a) +@ (poly_mod b) == poly_mod (a +@ b)) =
  let a' = unsnoc a in
  let b' = unsnoc b in
  let c = a +@ b in
  let c' = gf2_plus #(n - 1) a' b' in

  if last a = last b then
    assert(Seq.equal (unsnoc c) c')
  else
    assert(last a <> last b);

  if n = 33 then begin
    if last a then assert(Seq.equal (poly_mod a) (poly_xor #32 a')) else ();
    if last b then assert(Seq.equal (poly_mod b) (poly_xor #32 b')) else ();
    
    match last a = last b with
    | true -> if last a then poly_xor_aux #32 a' b' else ()
    | false -> assert(Seq.equal (poly_mod c) (poly_xor c'))
  end else begin
    assert(n > 33);
    if last a then begin
      assert(Seq.equal (unsnoc (a -@ (poly n))) (poly_xor #(n - 1) a'));
      assert_norm(poly_mod a == poly_mod (poly_xor #(n - 1) a'))
    end else
      assert_norm(poly_mod a == poly_mod #(n - 1) a');

    if last b then begin
      assert(Seq.equal (unsnoc (b -@ (poly n))) (poly_xor #(n - 1) b'));
      assert_norm(poly_mod b == poly_mod (poly_xor #(n - 1) b'))
    end else
      assert_norm(poly_mod b == poly_mod #(n - 1) b');

    match last a = last b with
    | true ->
      if last a then
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
      calc (==) {
        poly_mod c;
        =={assert(last c == true)}
        poly_mod #(n - 1) (unsnoc (c -@ poly n));
        =={assert(Seq.equal (unsnoc (c -@ poly n)) (poly_xor #(n - 1) c'))}
        poly_mod (poly_xor #(n - 1) c');
      };
      let x = if last a then a else b in
      let x' = unsnoc x in
      let y = if last a then b else a in
      let y' = unsnoc y in
      let p' = unsnoc (poly n) in
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
  res: BV.bv_t (nzeros + 32){
    forall j.
      (j == nzeros + 31 - i ==> Seq.index res j == true) /\
      (j <> nzeros + 31 - i ==> Seq.index res j == false)
  } =
  let zero_left = BV.zero_vec #(nzeros + 32 - i - 1) in
  let one = ones_vec_r 1 zero_left in
  zero_vec_r i one

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
    let m = ones_vec_r 1 (BV.zero_vec #32) in
    let n = poly_xor (BV.zero_vec #32) in
    calc (==) {
      poly_mod #33 m;
      =={assert(last m == true)}
      unsnoc (m -@ poly 33);
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

type matrix_dividend (nzeros: nat{nzeros > 0}) = d: BV.bv_t (nzeros + 32) {
  forall i. i < nzeros ==> Seq.index d i == false
}

val bit_extract:
    #nzeros: nat{nzeros > 0}
  -> n: matrix_dividend nzeros
  -> i: nat{i < 32}
  -> res: BV.bv_t (nzeros + 32) {
      forall j.
        (j == nzeros + 31 - i ==> Seq.index res j == Seq.index n j) /\
        (j <> nzeros + 31 - i ==> Seq.index res j == false)
    }

let bit_extract #nzeros n i =
  let zero_left = BV.zero_vec #(nzeros + 32 - i - 1) in
  let bit = zero_left @| (Seq.create 1 (Seq.index n (nzeros + 31 - i))) in
  zero_vec_r #(nzeros + 32 - i) i bit

val bit_sum:
    #nzeros: nat{nzeros > 0}
  -> n: matrix_dividend nzeros
  -> i: nat{i < 32}
  -> res: BV.bv_t (nzeros + 32) {
    forall j.
      (j >= nzeros + 31 - i ==> Seq.index res j == Seq.index n j) /\
      (j < nzeros + 31 - i ==> Seq.index res j == false)
  }

let rec bit_sum #nzeros n i =
  match i with
  | 0 -> bit_extract #nzeros n i
  | _ -> (bit_extract n i) +@ (bit_sum n (i - 1))

val do_magic_matrix_times:
    #nzeros: nat{nzeros > 0}
  -> m: matrix_t nzeros
  -> n: BV.bv_t 32
  -> i: nat{i < 32}
  -> res: BV.bv_t 32{
      res == poly_mod (bit_extract #nzeros (zero_vec_l nzeros n) i)
    }

let do_magic_matrix_times #nzeros m n i =
  let pat = magic_matrix_pattern nzeros i in
  let ext = bit_extract #nzeros (zero_vec_l nzeros n) i in
  if Seq.index n (31 - i) then begin
    Seq.index m i
  end else begin
    assert(Seq.equal ext (BV.zero_vec #(nzeros + 32)));
    poly_mod_zero ext;
    BV.zero_vec #32
  end

val magic_matrix_times':
    #nzeros: nat{nzeros > 0}
  -> m: matrix_t nzeros
  -> n: BV.bv_t 32
  -> i: nat{i < 32}
  -> res: BV.bv_t 32{
    res == poly_mod (bit_sum #nzeros (zero_vec_l nzeros n) i)
  }

let rec magic_matrix_times'
  (#nzeros: nat{nzeros > 0}) (m: matrix_t nzeros) (n: BV.bv_t 32) (i: nat{i < 32}) =
  match i with
  | 0 -> do_magic_matrix_times m n i
  | _ -> 
    let n' = do_magic_matrix_times m n i in
    let e = bit_extract #nzeros (zero_vec_l nzeros n) i in
    let sum = bit_sum #nzeros (zero_vec_l nzeros n) (i - 1) in
    poly_mod_add e sum;
    n' +@ magic_matrix_times' m n (i - 1)

val magic_matrix_times:
  #nzeros: nat {nzeros > 0} ->
  matrix_t nzeros ->
  n: BV.bv_t 32 ->
  res: BV.bv_t 32 {res == poly_mod (zero_vec_l nzeros n)}

let magic_matrix_times #nzeros m n =
  assert(Seq.equal (bit_sum #nzeros (zero_vec_l nzeros n) 31) (zero_vec_l nzeros n));
  magic_matrix_times' m n 31

#set-options "--z3rlimit 200 --z3seed 1"
let rec poly_mod_zero_prefix (#n: nat{n > 32}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures poly_mod (zero_vec_l m (poly_mod a)) == poly_mod (zero_vec_l m a)) =
  assert(Seq.equal (zero_vec_l #(n - 1) m (unsnoc a)) (unsnoc (zero_vec_l m a)));
  if n = 33 then
    if Seq.index a (n - 1) then
      calc (==) {
        poly_mod (zero_vec_l m (poly_mod a));
        =={assert(Seq.equal (poly_mod a) (poly_xor #(n - 1) (unsnoc a)))}
        poly_mod (zero_vec_l m (poly_xor #(n - 1) (unsnoc a)));
        =={
          let left = (zero_vec_l m (poly_xor #(n - 1) (unsnoc a))) in
          let right = (poly_xor #(n + m - 1) (unsnoc (zero_vec_l m a))) in
          assert(Seq.equal left right)
        }
        poly_mod (poly_xor #(n + m - 1) (unsnoc (zero_vec_l m a)));
        =={poly_xor_sub_eq (zero_vec_l m a)}
        poly_mod (zero_vec_l m a);
      }
    else
      calc (==) {
        poly_mod (zero_vec_l m (poly_mod a));
        =={}
        poly_mod (zero_vec_l #(n - 1) m (unsnoc a));
        =={}
        poly_mod #(n + m - 1) (unsnoc (zero_vec_l m a));
        =={}
        poly_mod (zero_vec_l m a);
      }
  else
    if Seq.index a (n - 1) then
      calc (==) {
        poly_mod (zero_vec_l m (poly_mod a));
        =={}
        poly_mod (zero_vec_l m (poly_mod #(n - 1) (unsnoc (a -@ (poly n)))));
        =={poly_xor_sub_eq a}
        poly_mod (zero_vec_l m (poly_mod (poly_xor #(n - 1) (unsnoc a))));
        =={poly_mod_zero_prefix (poly_xor #(n - 1) (unsnoc a)) m}
        poly_mod (zero_vec_l m (poly_xor #(n - 1) (unsnoc a)));
        =={poly_xor_zero_vec_l #(n - 1) (unsnoc a) m}
        poly_mod (poly_xor (zero_vec_l #(n - 1) m (unsnoc a)));
        =={}
        poly_mod (poly_xor #(n + m - 1) (unsnoc (zero_vec_l m a)));
        =={poly_xor_sub_eq (zero_vec_l m a)}
        poly_mod #(n + m - 1) (unsnoc ((zero_vec_l m a) -@ poly (n + m)));
        =={assert(last (zero_vec_l m a) == true)}
        poly_mod (zero_vec_l m a);
      }
    else
      calc (==) {
        poly_mod (zero_vec_l m (poly_mod a));
        =={}
        poly_mod (zero_vec_l m (poly_mod #(n - 1) (unsnoc a)));
        =={poly_mod_zero_prefix #(n - 1) (unsnoc a) m}
        poly_mod (zero_vec_l #(n - 1) m (unsnoc a));
        =={}
        poly_mod #(n + m - 1) (unsnoc (zero_vec_l m a));
        =={}
        poly_mod (zero_vec_l m a);
      }

let magic_matrix_times_double
  (#nzeros: nat{nzeros > 0}) (m: matrix_t nzeros) (i: nat{i < 32}): Lemma
  (ensures is_magic_matrix_elem (nzeros * 2) i (magic_matrix_times m (Seq.index m i))) =
  let p = magic_matrix_pattern nzeros i in
  let p' = magic_matrix_pattern (nzeros * 2) i in
  let p'' = zero_vec_l nzeros p in
  let n = magic_matrix_times m (Seq.index m i) in
  poly_mod_zero_prefix p nzeros;
  assert(forall j.
    j >= nzeros /\ j < nzeros * 2 + 32 ==>
    Seq.index p (j - nzeros) == Seq.index p' j /\
    Seq.index p (j - nzeros) == Seq.index p'' j);
  assert(forall j. j < nzeros ==> Seq.index p' j == Seq.index p'' j);
  assert(Seq.equal p'' p');
  calc (==) {
    n;
    =={}
    poly_mod (zero_vec_l nzeros (Seq.index m i));
    =={}
    poly_mod (zero_vec_l nzeros (poly_mod p));
    =={}
    poly_mod (zero_vec_l nzeros p);
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
    let n = magic_matrix_times m (Seq.index m (Seq.length s)) in
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
