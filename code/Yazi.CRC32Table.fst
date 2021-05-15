module Yazi.CRC32Table

module B = LowStar.Buffer
module BV = FStar.BitVector
module CB = LowStar.ConstBuffer
module Ghost = FStar.Ghost
module HS = FStar.HyperStack
module M = LowStar.Modifies
module Math = FStar.Math.Lemmas
module Seq = FStar.Seq
module U32 = FStar.UInt32

open FStar.Tactics
open LowStar.BufferOps
open Spec.CRC32

let rec logand_mask_aux (a: nat{a > 0}) (n: nat{n >= a}): Lemma
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

#set-options "--z3rlimit 120 --z3seed 1"
let large_table_val_aux
  (i: U32.t{U32.v i < 256}) (nzeros: nat{nzeros > 0}) (p p' p'': U32.t): Lemma
  (requires
    poly_mod_u32 nzeros i == UInt.to_vec (U32.v p) /\
    poly_mod_u32 8 (U32.logand p 0xFFul) == UInt.to_vec (U32.v p') /\
    p'' == U32.shift_right p 8ul)
  (ensures poly_mod_correct (nzeros + 8) i (U32.logxor p' p'')) =
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

#set-options "--z3rlimit 120 --z3seed 1"
inline_for_extraction
private let poly_mask (i: U32.t{(U32.v i) < 32}) (p: U32.t{
  let p' = U32.v p in
  let i' = U32.v i in
  forall j. {:pattern UInt.nth p' j}
    (j >= i' ==> UInt.nth p' j == false) /\
    (j < i' ==> UInt.nth p' j == Seq.index gf2_polynomial32 j)
}): Tot (res: U32.t{
  let res' = U32.v res in
  let i' = U32.v i in
  forall j. {:pattern UInt.nth res' j}
    (j > i' ==> UInt.nth res' j == false) /\
    (j <= i' ==> UInt.nth res' j == Seq.index gf2_polynomial32 j)
}) =
  if i = 0ul || i = 6ul || i = 9ul || i = 10ul || i = 16ul || i = 20ul || i = 21ul ||
  i = 22ul || i = 24ul || i = 25ul || i = 27ul || i = 28ul || i = 30ul || i = 31ul then
  begin
    let open U32 in
    let shift = 31ul -^ i in
    let mask = 1ul <<^ shift in
    let res = p |^ mask in
    
    mask_logor_status #32 (v shift) (v mask) (v p);
    assert(forall j. {:pattern UInt.nth (UInt.logor (v p) (v mask)) j}
      j <> (32 - 1 - v shift) ==>
      UInt.nth (UInt.logor (v p) (v mask)) j == UInt.nth (v p) j);
    assert_norm(Seq.index gf2_polynomial32 (v i) == true);
    res
  end else
    p

private let rec calc_polynomial (i: U32.t{U32.v i < 32}) (p: U32.t{
  let i' = U32.v i in
  let p' = U32.v p in
  forall j. {:pattern UInt.nth p' j}
    (j >= i' ==> UInt.nth p' j == false) /\
    (j < i' ==> UInt.nth p' j == Seq.index gf2_polynomial32 j)
}): Tot crc32_polynomial (decreases U32.v (U32.sub 32ul i)) =
  let open U32 in
  let p' = poly_mask i p in
  if i = 31ul then p' else calc_polynomial (i +^ 1ul) p'

#set-options "--ifuel 64 --fuel 64"
inline_for_extraction
let gen_polynomial _: Tot crc32_polynomial =
  assert(forall i. UInt.nth (U32.v 0ul) i == false) by (
    let _ = forall_intro () in
    norm [simplify]);

  calc_polynomial 0ul 0ul
#reset-options

let poly_mod_head_zero (d: U32.t): Lemma
  (requires UInt.nth (U32.v d) 31 == false)
  (ensures poly_mod_correct 1 d (U32.shift_right d 1ul)) =
  ()

let bv_one_aux (#n: nat{n > 0}) (v: BV.bv_t n): Lemma
  (requires forall i.
    (i < n - 1 ==> Seq.index v i == false) /\
    (i == n - 1 ==> Seq.index v i == true))
  (ensures UInt.from_vec v == 1) =
  match n with
  | 1 -> ()
  | _ -> assert(Seq.equal (Seq.slice v 0 (n - 1)) (BV.zero_vec #(n - 1)))

let logand_aux (#n: nat{n > 0}) (d: UInt.uint_t n): Lemma
  (requires UInt.logand d 1 <> 1)
  (ensures UInt.nth d (n - 1) == false) =
  let res = UInt.logand d 1 in
  uint_one_vec #n 1;
  assert(forall i. i < n - 1 ==> UInt.nth res i == false);
  if UInt.nth d (n - 1) then begin
    assert(UInt.nth res (n - 1) == true);
    bv_one_aux (UInt.to_vec res)
  end else
    ()

let poly_xor_aux (d: U32.t) (p: crc32_polynomial): Lemma
  (ensures forall i. {:pattern UInt.nth (U32.v (U32.logxor d p)) i}
    UInt.nth (U32.v (U32.logxor d p)) i ==
    Seq.index (poly_xor (UInt.to_vec (U32.v d))) i) = ()

#set-options "--z3rlimit 120 --z3seed 1"
let poly_xor_poly_mod (d: U32.t) (p: crc32_polynomial): Lemma
  (requires UInt.nth (U32.v d) 31 == true)
  (ensures
    poly_mod (zero_vec_l 1 (UInt.to_vec (U32.v d))) ==
    poly_xor (UInt.to_vec (U32.v (U32.shift_right d 1ul)))) =
  let open U32 in
  let d' = UInt.to_vec (U32.v d) in
  let d'' = zero_vec_l 1 d' in
  let d''' = UInt.to_vec (U32.v (d >>^ 1ul)) in
  assert(Seq.last d'' == true);
  assert(Seq.index d'' 0 == false);
  assert(forall i. i > 1 ==> Seq.index d'' i == UInt.nth (v d) (i - 1));
  assert(Seq.equal (poly_mod d'') (poly_xor #32 (unsnoc d'')));
  assert(forall i. i <= 31 ==> Seq.index d''' i == Seq.index d'' i);
  assert(Seq.equal d''' (unsnoc d''))

inline_for_extraction
private let cell_xor (d: U32.t): Tot (res:U32.t{poly_mod_correct 1 d res}) =
  let open U32 in
  let p = gen_polynomial () in
  let d' = d >>^ 1ul in
  if (d &^ 1ul) = 1ul then begin
    assert(UInt.logand (v d) 1 == 1);
    assert(UInt.nth (v d) 31 == true);
    let res = d' ^^ p in
    poly_xor_aux d' p;
    poly_xor_poly_mod d p;
    res
  end else begin
    assert(UInt.logand (v d) 1 <> 1);
    logand_aux (v d);
    poly_mod_head_zero d;
    d'
  end

let cell_xor_app (nzeros: nat{nzeros > 0}) (d res: U32.t): Lemma
  (requires poly_mod_correct nzeros d res)
  (ensures poly_mod_correct (nzeros + 1) d (cell_xor res)) =
  let open U32 in
  let d' = UInt.to_vec (v d) in
  let d'' = zero_vec_l nzeros d' in
  let res' = UInt.to_vec (U32.v res) in
  calc (==) {
    UInt.to_vec (U32.v (cell_xor res));
    =={poly_mod_correct_eq 1 res (cell_xor res)}
    poly_mod (zero_vec_l 1 res');
    =={poly_mod_correct_eq nzeros d res}
    poly_mod (zero_vec_l 1 (poly_mod d''));
    =={poly_mod_zero_prefix d'' 1}
    poly_mod (zero_vec_l 1 d'');
    =={zero_vec_l_app d' nzeros 1}
    poly_mod (zero_vec_l (nzeros + 1) d');
  }

private let rec calc_cell (m: Ghost.erased U32.t) (i: U32.t{U32.v i <= 7}) (d: U32.t{
  let open U32 in
  (v i < 7 ==> poly_mod_correct (v (7ul -^ i)) m d) /\
  (v i == 7 ==> (v d) == (v m))
}): Tot (res:U32.t{
  poly_mod_correct 8 m res
}) (decreases U32.v i) =
  let open U32 in
  if i <^ 7ul then cell_xor_app (v (7ul -^ i)) m d else ();
  if i = 0ul then
    cell_xor d
  else
    calc_cell m (i -^ 1ul) (cell_xor d)

private let rec gen_8bit_table
  (i: U32.t{U32.v i <= 255})
  (buf: table_buf):
  ST.Stack unit
  (decreases 255 - U32.v i)
  (requires fun h -> sub_table_correct (U32.v i) 8 h buf)
  (ensures fun h0 _ h1 -> M.modifies (B.loc_buffer buf) h0 h1 /\ table_correct 8 h1 buf) =
  let open U32 in
  buf.(i) <- calc_cell i 7ul i;
  if i <^ 255ul then gen_8bit_table (i +^ 1ul) buf else ()

private let rec gen_large_table
  (nzeros: Ghost.erased nat{nzeros > 0})
  (i: U32.t{U32.v i <= 255})
  (t8 tp buf: table_buf):
  ST.Stack unit
    (decreases 255 - U32.v i)
    (requires fun h ->
      B.disjoint buf t8 /\
      B.disjoint buf tp /\
      table_correct 8 h t8 /\
      table_correct nzeros h tp /\
      sub_table_correct (U32.v i) (nzeros + 8) h buf /\
      B.live h t8 /\ B.live h tp)
    (ensures fun h0 _ h1 -> 
      M.modifies (B.loc_buffer buf) h0 h1 /\ table_correct (nzeros + 8) h1 buf) =
    let open U32 in
    let p = B.index tp i in
    let j = p &^ 0xFFul in
    UInt.logand_le (v p) (v 0xFFul);
    let p' = B.index t8 j in
    let p'' = p >>^ 8ul in
    poly_mod_correct_eq nzeros i p;
    poly_mod_correct_eq 8 j p';
    large_table_val_aux i nzeros p p' p'';
    buf.(i) <- p' ^^ p'';
    if i <^ 255ul then gen_large_table nzeros (i +^ 1ul) t8 tp buf else ()
    
let gen_crc32_table t8 t16 t24 t32 =
  gen_8bit_table 0ul t8;
  gen_large_table 8 0ul t8 t8 t16;
  gen_large_table 16 0ul t8 t16 t24;
  gen_large_table 24 0ul t8 t24 t32
