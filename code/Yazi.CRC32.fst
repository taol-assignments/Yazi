module Yazi.CRC32
module B = LowStar.Buffer
module BV = FStar.BitVector
module Cast = FStar.Int.Cast
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Seq
open LowStar.BufferOps
open Spec.CRC32
    
#set-options "--z3rlimit 120 --z3seed 1 --fuel 16 --ifuel 16"
let rec cast_zero_prefix (#n: nat) (v: UInt.uint_t n) (m: nat{m >= n}): Lemma
  (requires pow2 n <= pow2 m)
  (ensures UInt.to_vec #m v == (Seq.create (m - n) false) @| (UInt.to_vec v)) =
  match m - n with
  | 0 -> assert(Seq.equal (UInt.to_vec #m v) ((Seq.create (m - n) false) @| (UInt.to_vec v)))
  | _ ->
    if n >= 1 then
      calc (==) {
        UInt.to_vec #m v;
        =={}
        (UInt.to_vec #(m - 1) (v / 2)) @| (Seq.create 1 (v % 2 = 1));
        =={
          Math.Lemmas.pow2_le_compat (m - 1) (n - 1);
          assert(v / 2 <= pow2 (n - 1));
          cast_zero_prefix #(n - 1) (v / 2) (m - 1)
        }
        ((Seq.create (m - n) false) @| (UInt.to_vec #(n - 1) (v / 2))) @|
        (Seq.create 1 (v % 2 = 1));
        =={
          Seq.append_assoc
            (Seq.create (m - n) false)
            (UInt.to_vec #(n - 1) (v / 2))
            (Seq.create 1 (v % 2 = 1))
        }
        (Seq.create (m - n) false) @|
        ((UInt.to_vec #(n - 1) (v / 2)) @| (Seq.create 1 (v % 2 = 1)));
        =={}
        (Seq.create (m - n) false) @| (UInt.to_vec v);
      }
    else begin
      assert(Seq.equal (UInt.to_vec #m v) (Seq.create m false));
      assert(UInt.to_vec #n v == Seq.empty #bool);
      assert(Seq.equal (UInt.to_vec #m v) ((Seq.create m false) @| (Seq.empty #bool)))
    end

private unfold let u8_padding (b: U8.t) (n: nat{n > 32}): Tot (BV.bv_t n) =
  (BV.zero_vec #24) @| (UInt.to_vec (U8.v b)) @| (BV.zero_vec #(n - 32))

#set-options "--z3rlimit 120 --z3seed 1"
let do1_logxor (#m: crc32_buf_len) (prev: BV.bv_t m) (crc: U32.t) (b: U8.t): Lemma
  (requires crc32_matched #m prev crc false)
  (ensures
    (m == 0 ==>
      UInt.to_vec (U32.v (U32.logxor crc (Cast.uint8_to_uint32 b))) ==
      (BV.ones_vec #32 +@ (zero_vec_l 24 (UInt.to_vec (U8.v b))))) /\
    (m > 32 ==>
      UInt.to_vec (U32.v (U32.logxor crc (Cast.uint8_to_uint32 b))) ==
      poly_mod (prev +@ (u8_padding b m)))) =
  let open U32 in
  let b32 = Cast.uint8_to_uint32 b in
  let vb32: BV.bv_t 32 = UInt.to_vec (v b32) in
  let vcrc = UInt.to_vec (v crc) in
  cast_zero_prefix (U8.v b) 32;
  if m > 32 then
    calc (==) {
      vcrc +@ vb32;
      =={}
      (poly_mod prev) +@ vb32;
      =={poly_mod_zero_suffix vb32 (m - 32)}
      (poly_mod prev) +@ (poly_mod (zero_vec_r (m - 32) vb32));
      =={
        assert(Seq.equal (zero_vec_r (m - 32) vb32) (u8_padding b m))
      }
      (poly_mod prev) +@ (poly_mod (u8_padding b m));
      =={poly_mod_add prev (u8_padding b m)}
      poly_mod (prev +@ (u8_padding b m));
    }
  else
    ()

#set-options "--z3rlimit 200 --ifuel 128 --fuel 128 --z3seed 1"
let logand_256 (r: U32.t): Lemma
  (ensures forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth (U32.v (U32.logand r 0xFFul)) i == false) /\
    (i >= 32 - 8 ==> UInt.nth (U32.v (U32.logand r 0xFFul)) i == UInt.nth (U32.v r) i)) =
  let open U32 in
  let mask = v 0xFFul in
  assert(forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth mask i == false) /\
    (i >= 32 - 8 ==> UInt.nth mask i == true));
  assert(forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth (UInt.logand (v r) (v 0xFFul)) i == false) /\
    (i >= 32 - 8 ==> UInt.nth (UInt.logand (v r) (v 0xFFul)) i == UInt.nth (U32.v r) i))

#set-options "--z3rlimit 200 --z3seed 1"
let do1_shift_right_logxor (r: U32.t) (t: U32.t): Lemma
  (requires poly_mod_correct 8 (U32.logand r 0xFFul) t)
  (ensures
     UInt.to_vec (U32.v (U32.logxor (U32.shift_right r 8ul) t)) ==
     poly_mod (zero_vec_l 8 (UInt.to_vec (U32.v r)))) =
  let vr = UInt.to_vec (U32.v r) in
  let r' = U32.shift_right r 8ul in
  let vr' = UInt.to_vec (U32.v r') in
  let i = U32.logand r 0xfful in
  let vi = UInt.to_vec (U32.v i) in
  poly_mod_correct_eq 8 i t;
  assert(poly_mod (zero_vec_l 8 vi) == UInt.to_vec (U32.v t));
  poly_mod_zero_suffix vr' 8;
  assert(poly_mod (zero_vec_r 8 vr') == vr');
  poly_mod_add (zero_vec_r 8 vr') (zero_vec_l 8 vi);
  assert((poly_mod (zero_vec_r 8 vr')) +@ (poly_mod (zero_vec_l 8 vi)) ==
    poly_mod ((zero_vec_r 8 vr') +@ (zero_vec_l 8 vi)));
  assert(forall j. {:pattern (Seq.index (zero_vec_r 8 vr') j)}
    ((j >= 8 /\ j < 40 - 8) ==> Seq.index (zero_vec_r 8 vr') j == Seq.index vr (j - 8)) /\
    ((j < 8 \/ j >= 40 - 8) ==> Seq.index (zero_vec_r 8 vr') j == false));
  logand_256 r;
  assert(forall (j: nat{j < 40}). {:pattern (Seq.index (zero_vec_l 8 vi) j)}
    (j >= 40 - 8 ==> Seq.index (zero_vec_l 8 vi) j == Seq.index vr (j - 8)) /\
    (j < 40 - 8  ==> Seq.index (zero_vec_l 8 vi) j == false));
  assert(Seq.equal
    ((zero_vec_r 8 vr') +@ (zero_vec_l 8 vi))
    (zero_vec_l 8 (UInt.to_vec (U32.v r))))

inline_for_extraction
private let do1
  (#m: Ghost.erased crc32_buf_len)
  (t8: Spec.table_buf)
  (prev: Ghost.erased (BV.bv_t m))
  (crc: U32.t)
  (b: U8.t):
  ST.Stack U32.t
  (requires fun h -> table_correct 8 h t8 /\ crc32_matched #m prev crc false)
  (ensures fun h0 res h1 ->
    let curr = crc32_append_8bit #m prev b in
    M.modifies M.loc_none h0 h1 /\
    crc32_matched #(if Ghost.reveal m = 0 then 40 else m + 8) curr res false) =
  let b' = Cast.uint8_to_uint32 b in
  let open U32 in
  let r = crc ^^ b' in 
  UInt.logand_le (v r) (v 0xFFul);
  let tv = t8.(r &^ 0xFFul) in
  let r' = r >>^ 8ul in
  let p = r' ^^ tv in
  do1_shift_right_logxor r tv;
  do1_logxor prev crc b;
  assert(UInt.to_vec (v p) == poly_mod (zero_vec_l 8 (UInt.to_vec (v r))));
  if Ghost.reveal m = 0 then begin
    assert(poly_mod (zero_vec_l 8 (UInt.to_vec (v r))) ==
      poly_mod (zero_vec_l 8 (BV.ones_vec #32 +@ (zero_vec_l 24 (UInt.to_vec (U8.v b))))));
    assert(Seq.equal
      (zero_vec_l 8 (BV.ones_vec #32 +@ (zero_vec_l 24 (UInt.to_vec (U8.v b)))))
      (crc32_append_8bit prev b))
  end else begin
    assert(poly_mod (zero_vec_l 8 (UInt.to_vec (v r))) ==
      poly_mod (zero_vec_l 8 (poly_mod (prev +@ (u8_padding b m)))));
    poly_mod_zero_prefix (prev +@ (u8_padding b m)) 8;
    assert(Seq.equal
      (zero_vec_l 8 (prev +@ (u8_padding b m)))
      (crc32_append_8bit prev b))
  end;
  p

inline_for_extraction
private let rec do1_remain
  (t8: Spec.table_buf)
  (l: U32.t)
  (buf: B.buffer U8.t{B.length buf == U32.v l})
  (m: Ghost.erased nat)
  (data: Ghost.erased (Seq.seq U8.t){Seq.length data == Ghost.reveal m})
  (r: U32.t{U32.v r <= (U32.v l) % 4})
  (crc: U32.t):
  ST.Stack (U32.t * B.buffer U8.t)
  (decreases (U32.v r) - ((U32.v l) % 4))
  (requires fun h ->
    let curr = crc32_u8_to_bits #m #0 (data @| Seq.slice 0 (B.as_seq h buf) r) crc false in
    B.live h buf /\
    table_correct 8 h t8 /\
    crc32_matched
      (crc32_u8_to_bits #m #0 data (Seq.empty #bool))
      crc false)
  (ensures fun h0 res h1 ->
    let curr = crc32_u8_to_bits
      #(m + ((U32.v l) % 4))
      #0
      (data @| (Seq.slice (B.as_seq h1 buf) 0 ((U32.v l) % 4)))
      (Seq.empty #bool) in
    M.modifies M.loc_none h0 h1 /\
    crc32_matched #_ curr (fst res) false) =
  let open U32 in
  if r <^ (l %^ 4ul) then begin
    admit();
    do1_remain t8 l buf m data
      (r +^ 1ul)
      (do1
        t8
        (crc32_u8_to_bits #m #0 data (Seq.empty #bool))
        crc
        (B.index buf r))
  end else begin
    (crc, buf)
  end

let crc32_impl #n prev t8 t16 t24 t32 crc buf len =
  let open U32 in
  ST.push_frame ();
  admit();
  ST.pop_frame ();
  0ul
