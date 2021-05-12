module Yazi.CRC32Table

module B = LowStar.Buffer
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
    (j < i' ==> UInt.nth p' j == Seq.index Spec.gf2_polynomial32 j)
}): Tot (res: U32.t{
  let res' = U32.v res in
  let i' = U32.v i in
  forall j. (j > i' ==> UInt.nth res' j == false) /\
  (j <= i' ==> UInt.nth res' j == Seq.index Spec.gf2_polynomial32 j)
}) =
  if i = 5ul || i = 8ul || i = 9ul || i = 15ul || i = 19ul || i = 20ul || i = 21ul ||
  i = 23ul || i = 24ul || i = 26ul || i = 27ul || i = 29ul || i = 30ul || i = 31ul then
  begin
    let open U32 in
    let one = 1ul in
    let shift = 31ul -^ i in
    let mask = one <<^ (31ul -^ i) in
    let res = p |^ mask in
    
    mask_logor_status #32 (v shift) (v mask) (v p);
    assert(forall j. {:pattern UInt.nth (UInt.logor (v p) (v mask)) j}
      j <> (32 - 1 - v shift) ==>
      UInt.nth (UInt.logor (v p) (v mask)) j == UInt.nth (v p) j);
    assert_norm(Seq.index Spec.gf2_polynomial32 (v i) == true);
    res
  end else
    p

let rec calc_polynomial (i: U32.t{U32.v i < 32}) (p: U32.t{
  let i' = U32.v i in
  let p' = U32.v p in
  forall j.
    (j >= i' ==> UInt.nth p' j == false) /\
    (j < i' ==> UInt.nth p' j == Seq.index Spec.gf2_polynomial32 j)
}): Tot Spec.crc32_polynomial (decreases U32.v (U32.sub 32ul i)) =
  let open U32 in
  let p' = poly_mask i p in
  if i = 31ul then p' else calc_polynomial (i +^ 1ul) p'

#set-options "--ifuel 64 --fuel 64"
let gen_polynomial _: Tot Spec.crc32_polynomial =
  assert(forall i. UInt.nth (U32.v 0ul) i == false) by (
    let _ = forall_intro () in
    norm [simplify]);

  calc_polynomial 0ul 0ul
