module Spec.CRC32.Matrix

module BV = FStar.BitVector
module Bits = Spec.CRC32.Bits
module Seq = FStar.Seq

open FStar.Seq
open FStar.Mul
open Spec.CRC32.Bits

#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rec seq_append_index_r (#t: Type) (a b: Seq.seq t): Lemma
  (ensures forall i. i < Seq.length b ==> Seq.index (a @| b) (i + Seq.length a) == Seq.index b i)
  (decreases Seq.length a) =
  match Seq.length a with
  | 0 -> ()
  | _ -> seq_append_index_r (Seq.tail a) b

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
    assert(Seq.length res == l + 1);
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
    assert(Seq.equal (magic_matrix_pattern nzeros i) (ext));
    Seq.index m i
  end else begin
    assert(Seq.equal ext (BV.zero_vec #(nzeros + 32)));
    Bits.poly_mod_zero ext;
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
    Bits.poly_mod_add e sum;
    n' +@ magic_matrix_times' m n (i - 1)

val magic_matrix_times:
  #nzeros: nat {nzeros > 0} ->
  matrix_t nzeros ->
  n: BV.bv_t 32 ->
  res: BV.bv_t 32 {res == poly_mod (zero_vec_l nzeros n)}

let magic_matrix_times #nzeros m n =
  assert(Seq.equal (bit_sum #nzeros (zero_vec_l nzeros n) 31) (zero_vec_l nzeros n));
  magic_matrix_times' m n 31

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
