module Yazi.CRC32Table

module B = LowStar.Buffer
module BV = FStar.BitVector
module Spec = Spec.CRC32
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open FStar.Tactics

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

#set-options "--z3rlimit 120"
inline_for_extraction
private let poly_mask (i: U32.t{(U32.v i) < 32}) (p: U32.t{
  let p' = U32.v p in
  let i' = U32.v i in
  forall j. {:pattern UInt.nth p' j}
    (j >= i' ==> UInt.nth p' j == false) /\
    (j < i' ==> UInt.nth p' j == Seq.index Spec.gf2_polynomial32 (31 - j))
}): Tot (res: U32.t{
  let res' = U32.v res in
  let i' = U32.v i in
  forall j. {:pattern UInt.nth res' j}
    (j > i' ==> UInt.nth res' j == false) /\
    (j <= i' ==> UInt.nth res' j == Seq.index Spec.gf2_polynomial32 (31 - j))
}) =
  if i = 0ul || i = 6ul || i = 9ul || i = 10ul || i = 16ul || i = 20ul || i = 21ul ||
  i = 22ul || i = 24ul || i = 25ul || i = 27ul || i = 28ul || i = 30ul || i = 31ul then
  begin
    let open U32 in
    let one = 1ul in
    let shift = 31ul -^ i in
    let mask = one <<^ shift in
    let res = p |^ mask in
    
    mask_logor_status #32 (v shift) (v mask) (v p);
    assert(forall j. {:pattern UInt.nth (UInt.logor (v p) (v mask)) j}
      j <> (32 - 1 - v shift) ==>
      UInt.nth (UInt.logor (v p) (v mask)) j == UInt.nth (v p) j);
    assert_norm(Seq.index Spec.gf2_polynomial32 (v shift) == true);
    res
  end else
    p

let rec calc_polynomial (i: U32.t{U32.v i < 32}) (p: U32.t{
  let i' = U32.v i in
  let p' = U32.v p in
  forall j. {:pattern UInt.nth p' j}
    (j >= i' ==> UInt.nth p' j == false) /\
    (j < i' ==> UInt.nth p' j == Seq.index Spec.gf2_polynomial32 (31 - j))
}): Tot Spec.crc32_polynomial (decreases U32.v (U32.sub 32ul i)) =
  let open U32 in
  let p' = poly_mask i p in
  if i = 31ul then p' else calc_polynomial (i +^ 1ul) p'

#set-options "--ifuel 64 --fuel 64"
inline_for_extraction
let gen_polynomial _: Tot Spec.crc32_polynomial =
  assert(forall i. UInt.nth (U32.v 0ul) i == false) by (
    let _ = forall_intro () in
    norm [simplify]);

  calc_polynomial 0ul 0ul
#reset-options

let poly_mod_head_zero (d: U32.t): Lemma
  (requires UInt.nth (U32.v d) 31 == false)
  (ensures Spec.poly_mod_correct d (U32.shift_right d 1ul)) =
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

let poly_xor_aux (d: U32.t) (p: Spec.crc32_polynomial): Lemma
  (ensures forall i. {:pattern UInt.nth (U32.v (U32.logxor d p)) i}
    UInt.nth (U32.v (U32.logxor d p)) i ==
    Seq.index (Spec.poly_xor (UInt.to_vec (U32.v (Spec.u32_rev d)))) (31 - i)) = ()

#set-options "--z3rlimit 120"
let poly_xor_poly_mod (d: U32.t) (p: Spec.crc32_polynomial): Lemma
  (requires UInt.nth (U32.v d) 31 == true)
  (ensures
    Spec.poly_mod (Spec.zero_vec_r 1 (UInt.to_vec (U32.v (Spec.u32_rev d)))) ==
    Spec.poly_xor (UInt.to_vec (U32.v (Spec.u32_rev (U32.shift_right d 1ul))))) =
  let open U32 in
  let d' = UInt.to_vec (U32.v (Spec.u32_rev d)) in
  let d'' = Spec.zero_vec_r 1 d' in
  let d''' = UInt.to_vec (U32.v (Spec.u32_rev (d >>^ 1ul))) in
  assert(Seq.head d'' == true);
  assert(Seq.index d'' 32 == false);
  assert(forall i. i < 32 ==> Seq.index d'' i == UInt.nth (v d) (31 - i));
  assert(Seq.equal (Spec.poly_mod d'') (Spec.poly_xor #32 (Seq.tail d'')));
  // assert(forall i. i < 31 ==> Seq.index d''' i == Seq.index d'' (i - 1));
  admit()
  
let cell_xor (d: U32.t): Tot (res:U32.t{Spec.poly_mod_correct d res}) =
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
