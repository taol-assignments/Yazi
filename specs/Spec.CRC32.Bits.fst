module Spec.CRC32.Bits

module BV = FStar.BitVector
module Math = FStar.Math.Lemmas
module Seq = FStar.Seq
module U32 = FStar.UInt32
module UInt = FStar.UInt

#set-options "--z3rlimit 200 --z3seed 1"
let poly_xor_zero_prefix (#n: nat{n >= 32}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures forall (i: nat{i > 0}).
    i < Seq.length (zero_vec_l m a) ==>
    Seq.index (poly_xor (zero_vec_l m a)) i ==
    Seq.index (poly_xor (zero_vec_l (m - 1) a)) (i - 1)) = ()

let zero_vec_l_aux (#n: nat{n > 0}) (a: BV.bv_t n) (m: nat{m > 0}): Lemma
  (ensures forall (i: nat{i > 0}).
    i < Seq.length (zero_vec_l m a) ==>
   Seq.index (zero_vec_l m a) i == Seq.index (zero_vec_l (m - 1) a) (i - 1)) = ()

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

let rec poly_mod_zero #n a =
  match n with
  | 33 -> assert_norm(Seq.equal (poly_mod #n a) (BV.zero_vec #32))
  | _ -> 
    assert_norm(Seq.equal (unsnoc a) (BV.zero_vec #(n - 1)));
    poly_mod_zero #(n - 1) (unsnoc a)

let rec poly_mod_add #n a b =
  let a' = unsnoc a in
  let b' = unsnoc b in
  let c = a +@ b in
  let c' = gf2_plus #(n - 1) a' b' in

  if Seq.last a = Seq.last b then
    assert(Seq.equal (unsnoc c) c')
  else
    assert(Seq.last a <> Seq.last b);

  if n = 33 then begin
    if Seq.last a then assert(Seq.equal (poly_mod a) (poly_xor #32 a')) else ();
    if Seq.last b then assert(Seq.equal (poly_mod b) (poly_xor #32 b')) else ();
    
    match Seq.last a = Seq.last b with
    | true -> if Seq.last a then poly_xor_aux #32 a' b' else ()
    | false -> assert(Seq.equal (poly_mod c) (poly_xor c'))
  end else begin
    assert(n > 33);
    if Seq.last a then begin
      assert(Seq.equal (unsnoc (a -@ (poly n))) (poly_xor #(n - 1) a'));
      assert_norm(poly_mod a == poly_mod (poly_xor #(n - 1) a'))
    end else
      assert_norm(poly_mod a == poly_mod #(n - 1) a');

    if Seq.last b then begin
      assert(Seq.equal (unsnoc (b -@ (poly n))) (poly_xor #(n - 1) b'));
      assert_norm(poly_mod b == poly_mod (poly_xor #(n - 1) b'))
    end else
      assert_norm(poly_mod b == poly_mod #(n - 1) b');

    match Seq.last a = Seq.last b with
    | true ->
      if Seq.last a then
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
        =={assert(Seq.last c == true)}
        poly_mod #(n - 1) (unsnoc (c -@ poly n));
        =={assert(Seq.equal (unsnoc (c -@ poly n)) (poly_xor #(n - 1) c'))}
        poly_mod (poly_xor #(n - 1) c');
      };
      let x = if Seq.last a then a else b in
      let x' = unsnoc x in
      let y = if Seq.last a then b else a in
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

let rec poly_mod_zero_prefix #n a m =
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
        =={assert(Seq.last (zero_vec_l m a) == true)}
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

let rec poly_mod_zero_suffix a m =
  match m with
  | 1 -> assert(Seq.equal (poly_mod (zero_vec_r m a)) a)
  | _ ->
    calc (==) {
      poly_mod (zero_vec_r m a);
      =={assert(Seq.equal (unsnoc (zero_vec_r m a)) (zero_vec_r (m - 1) a))}
      poly_mod (zero_vec_r (m - 1) a);
    };
    poly_mod_zero_suffix a (m - 1)

private let rec logand_mask_aux (a: nat{a > 0}) (n: nat{n >= a}): Lemma
  (requires (pow2 a) - 1 < pow2 n)
  (ensures forall i. 
    (i >= n - a ==> UInt.nth #n ((pow2 a) - 1) i == true) /\
    (i < n - a ==> UInt.nth #n ((pow2 a) - 1) i == false)) =
  if n = a then
    ()
  else begin
    Math.Lemmas.pow2_le_compat (n - 1) a;
    logand_mask_aux a (n - 1)
  end

let large_table_val_aux i nzeros p p' p'' =
   let open U32 in
   let vi = UInt.to_vec (v i) in
   let vp = UInt.to_vec (v p) in
   let vp' = UInt.to_vec (v p') in
   let vp'' = UInt.to_vec (v p'') in
   let vpand = UInt.to_vec (U32.v (U32.logand p 0xFFul)) in
   logand_mask_aux 8 32;
   assert(forall i.
     i < 32 - 8 ==> Seq.index vpand i == false /\
     i >= 32 - 8 ==> Seq.index vpand i == Seq.index vp i);
   assert(vp' == poly_mod (zero_vec_l 8 vpand));

   assert(forall i.
     i >= 8 ==> Seq.index vp'' i == Seq.index vp (i - 8) /\
     i < 8 ==> Seq.index vp'' i == false);
   poly_mod_zero_suffix vp'' 8;
   assert(vp'' == poly_mod (zero_vec_r 8 vp''));

   assert(forall i. {:pattern Seq.index (zero_vec_l 8 vpand) i}
     (i >= 40 - 8 ==> Seq.index (zero_vec_l 8 vpand) i == Seq.index vp (i - 8)) /\
     (i < 40 - 8 ==> Seq.index (zero_vec_l 8 vpand) i == false));

   assert(forall i. {:pattern Seq.index (zero_vec_r 8 vp'') i}
     (i < 8 \/ i >= 32 ==> Seq.index (zero_vec_r 8 vp'') i == false) /\
     (i >= 8 /\ i < 32 ==> Seq.index (zero_vec_r 8 vp'') i == Seq.index vp (i - 8)));

   let sum = (zero_vec_l 8 vpand) +@ (zero_vec_r 8 vp'') in
   assert(forall i. {:pattern Seq.index sum i}
     (i < 8 ==> Seq.index sum i == false) /\
     (i >= 8 ==> Seq.index sum i == Seq.index vp (i - 8)));
   assert(Seq.equal sum (zero_vec_l 8 vp));
   
   poly_mod_add (zero_vec_l 8 vpand) (zero_vec_r 8 vp'');
   assert(poly_mod sum == poly_mod (zero_vec_l 8 vp));

   assert(vp' +@ vp'' == poly_mod (zero_vec_l 8 (poly_mod (zero_vec_l nzeros vi))));
   poly_mod_zero_prefix (zero_vec_l nzeros vi) 8;
   assert(vp' +@ vp'' == poly_mod (zero_vec_l 8 (zero_vec_l nzeros vi)));
   zero_vec_l_app vi nzeros 8;
   assert(vp' +@ vp'' == poly_mod (zero_vec_l (nzeros + 8) vi))

open FStar.Seq
  
let rec crc32_u8_to_bits_append #m1 #m2 #n s1 s2 buf =
  match m1 with
  | 0 -> assert(Seq.equal (Seq.append s1 s2) s2)
  | _ ->
    let l = if m1 > 0 then
      if n = 0 then 32 + 8 * m1 else n + 8 * m1
    else
      n
    in
    if m2 = 0 then begin
      assert(Seq.equal (s1 @| s2) s1);
      assert(
        (normalize_term (crc32_u8_to_bits #m2 #l s2 (crc32_u8_to_bits #m1 #n s1 buf))) ==
        crc32_u8_to_bits #m1 #n s1 buf)
    end else if m1 = 1 then
      calc (==) {
        crc32_u8_to_bits #m2 #l s2 (crc32_u8_to_bits #m1 #n s1 buf);
        =={}
        crc32_u8_to_bits #m2 #l s2 (crc32_append_8bit buf (Seq.head s1));
        =={Seq.lemma_head_append s1 s2}
        crc32_u8_to_bits #m2 #l s2 (crc32_append_8bit buf (Seq.head (s1 @| s2)));
        =={
          Seq.lemma_tail_append s1 s2;
          assert(Seq.equal (Seq.tail (s1 @| s2)) s2)
        }
        crc32_u8_to_bits #m2 #l (Seq.tail (s1 @| s2)) (crc32_append_8bit buf (Seq.head (s1 @| s2)));
        =={assert(1 + m2 > 1)}
        crc32_u8_to_bits #(1 + m2) #n (s1 @| s2) buf;
      }
    else
      calc (==) {
        crc32_u8_to_bits #m2 #l s2 (crc32_u8_to_bits #m1 #n s1 buf);
        =={}
        crc32_u8_to_bits #m2 #l s2 (crc32_u8_to_bits
          #(m1 - 1) #_
          (Seq.tail s1)
          (crc32_append_8bit buf (Seq.head s1)));
        =={
          crc32_u8_to_bits_append
            #(m1 - 1)
            #m2
            #(if n = 0 then 40 else n + 8)
            (Seq.tail s1)
            s2
            (crc32_append_8bit buf (Seq.head s1))
        }
        crc32_u8_to_bits
          #(m1 + m2 - 1) #_
          ((Seq.tail s1) @| s2) 
          (crc32_append_8bit buf (Seq.head s1));
        =={
          Seq.lemma_tail_append s1 s2;
          Seq.lemma_head_append s1 s2
        }
        crc32_u8_to_bits
          #(m1 + m2 - 1) #_
          (Seq.tail (s1 @| s2))
          (crc32_append_8bit buf (Seq.head (s1 @| s2)));
        =={}
        crc32_u8_to_bits #(m1 + m2) #n (s1 @| s2) buf;
      }
