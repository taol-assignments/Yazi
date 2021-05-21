module Yazi.CRC32
module B = LowStar.Buffer
module BV = FStar.BitVector
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Mul
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

private unfold let u8_padding
  (b: U8.t)
  (n: nat{n > 0}):
  Tot (BV.bv_t (32 + 8 * n)) =
  (BV.zero_vec #24) @|
  (UInt.to_vec (U8.v b)) @|
  (BV.zero_vec #(8 * n))

#set-options "--z3rlimit 120 --z3seed 13 --fuel 0 --ifuel 0"
let do1_logxor
  (m: nat)
  (data: Seq.seq U8.t{Seq.length data == m})
  (crc: U32.t)
  (b: U8.t): Lemma
  (requires crc32_matched m data crc false)
  (ensures
    (m == 0 ==>
      UInt.to_vec (U32.v (U32.logxor crc (Cast.uint8_to_uint32 b))) ==
      (BV.ones_vec #32 +@ (zero_vec_l 24 (UInt.to_vec (U8.v b))))) /\
    (m > 0 ==>
      UInt.to_vec (U32.v (U32.logxor crc (Cast.uint8_to_uint32 b))) ==
      poly_mod ((crc32_data_to_bits m data) +@ (u8_padding b m)))) =
  let open U32 in
  let buf = crc32_data_to_bits m data in
  let b32 = Cast.uint8_to_uint32 b in
  let vb32 = UInt.to_vec (v b32) in
  let vcrc = UInt.to_vec (v crc) in
  let m' = 8 * m in
  cast_zero_prefix (U8.v b) 32;
  if m > 0 then
    calc (==) {
      vcrc +@ vb32;
      =={}
      (poly_mod buf) +@ vb32;
      =={poly_mod_zero_suffix vb32 m'}
      (poly_mod buf) +@ (poly_mod (zero_vec_r m' vb32));
      =={assert(Seq.equal (zero_vec_r m' vb32) (u8_padding b m))}
      (poly_mod buf) +@ (poly_mod (u8_padding b m));
      =={poly_mod_add buf (u8_padding b m)}
      poly_mod (buf +@ (u8_padding b m));
    }
  else
    assert(Seq.equal (zero_vec_l 24 (UInt.to_vec (U8.v b))) vb32)
  
#set-options "--z3rlimit 200 --ifuel 128 --fuel 128 --z3seed 1"
private let logand_256 (r: U32.t): Lemma
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

#set-options "--z3seed 1 --fuel 0 --ifuel 0"
private let do1_shift_right_logxor (r: U32.t) (t: U32.t): Lemma
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

#set-options "--z3rlimit 200 --z3seed 1 --fuel 1 --ifuel 1"
inline_for_extraction
private let do1
  (m: Ghost.erased nat)
  (data: Ghost.erased (Seq.seq U8.t){Seq.length data == Ghost.reveal m})
  (t8: Spec.table_buf)
  (crc: U32.t)
  (b: U8.t):
  ST.Stack (U32.t & (Ghost.erased (Seq.seq U8.t)))
  (requires fun h -> table_correct 8 h t8 /\ crc32_matched m data crc false)
  (ensures fun h0 res h1 ->
    let crc' = fst res in
    let data' = Ghost.reveal (snd res) in
    B.modifies B.loc_none h0 h1 /\
    data' == data @| (Seq.create 1 b) /\
    crc32_matched (m + 1) data' crc' false) =
  let b' = Cast.uint8_to_uint32 b in
  let open U32 in
  let r = crc ^^ b' in
  UInt.logand_le (v r) (v 0xFFul);
  let tv = t8.(r &^ 0xFFul) in
  let r' = r >>^ 8ul in
  let p = r' ^^ tv in
  let buf: Ghost.erased (BV.bv_t (if Ghost.reveal m = 0 then 0 else 32 + 8 * m)) =
    Ghost.hide (crc32_data_to_bits m data)
  in
  do1_logxor m data crc b;
  do1_shift_right_logxor r tv;

  if Ghost.reveal m > 0 then begin
    poly_mod_zero_prefix (buf +@ (u8_padding b m)) 8;
    crc32_data_to_bits_append m 1 data (Seq.create 1 b)
  end else
    assert(Seq.equal (zero_vec_l 8 (UInt.to_vec (v r))) (crc32_append_8bit buf b));
    
  (p, Ghost.hide (data @| (Seq.create 1 b)))

#set-options "--z3rlimit 200 --ifuel 0 --fuel 0 --z3seed 7"
inline_for_extraction
private let rec do1_remain
  (m: Ghost.erased nat)
  (prev: Ghost.erased (Seq.seq U8.t){Seq.length prev == Ghost.reveal m})
  (m': Ghost.erased nat)
  (data: Ghost.erased (Seq.seq U8.t){Seq.length data == Ghost.reveal m'})
  (t8: Spec.table_buf)
  (l: U32.t{(U32.v l) % 4 > 0})
  (r: U32.t{U32.v r < (U32.v l) % 4})
  (buf: B.buffer U8.t{B.length buf == U32.v l})
  (crc: U32.t):
  ST.Stack ((U32.t & (B.buffer U8.t)) & (Ghost.erased (Seq.seq U8.t)))
  (decreases (U32.v r) - ((U32.v l) % 4))
  (requires fun h ->
    B.live h buf /\
    table_correct 8 h t8 /\
    B.disjoint t8 buf /\
    (Ghost.reveal m') == (Ghost.reveal m) + (U32.v r) /\
    Seq.equal data (prev @| (Seq.slice (B.as_seq h buf) 0 (U32.v r))) /\
    crc32_matched m' data crc false)
  (ensures fun h0 res h1 ->
    let crc' = fst (fst res) in
    let buf' = snd (fst res) in
    let data' = Ghost.reveal (snd res) in
    B.modifies B.loc_none h0 h1 /\
    (B.length buf') % 4 == 0 /\
    Seq.length data' == (m + ((U32.v l) % 4)) /\
    Seq.equal data' (prev @| (Seq.slice (B.as_seq h1 buf) 0 ((U32.v l) % 4))) /\
    crc32_matched (m + ((U32.v l) % 4)) data' crc' false) =
  let open U32 in
  let (crc', data') = do1 m' data t8 crc (B.index buf r) in
  if r +^ 1ul <^ l %^ 4ul then begin
    do1_remain m prev (m + ((v r) + 1)) data' t8 l (r +^ 1ul) buf crc'
  end else begin
    let buf' = B.sub buf (r +^ 1ul) (l -^ (r +^ 1ul)) in
    ((crc', buf'), data')
  end

inline_for_extraction
private let dword_seq_to_u32 (a b c d: U8.t): Tot(crc32_data_dword a b c d) =
  let a' = Cast.uint8_to_uint32 a in
  let b' = Cast.uint8_to_uint32 b in
  let c' = Cast.uint8_to_uint32 c in
  let d' = Cast.uint8_to_uint32 d in
  cast_zero_prefix (U8.v a) 32;
  cast_zero_prefix (U8.v b) 32;
  cast_zero_prefix (U8.v c) 32;
  cast_zero_prefix (U8.v d) 32;
  let open U32 in
  a' ^^ (b' <<^ 8ul) ^^ (c' <<^ 16ul) ^^ (d' <<^ 24ul)

let do4_logxor
  (#m: nat)
  (data: Seq.seq U8.t{Seq.length data == m})
  (crc: U32.t)
  (a b c d: U8.t): Lemma
  (requires crc32_matched m data crc false)
  (ensures
    (m == 0 ==>
      UInt.to_vec (U32.v (U32.logxor crc (dword_seq_to_u32 a b c d))) ==
      (BV.ones_vec #32 +@ (UInt.to_vec (U32.v (dword_seq_to_u32 a b c d))))) /\
    (m > 0 ==>
      UInt.to_vec (U32.v (U32.logxor crc (dword_seq_to_u32 a b c d))) ==
      poly_mod (
        (zero_vec_r (8 * m) (UInt.to_vec (U32.v (dword_seq_to_u32 a b c d)))) +@
        (crc32_data_to_bits m data)))) =
  let open U32 in
  let sum = dword_seq_to_u32 a b c d in
  let vsum = UInt.to_vec (v sum) in
  let prev_len = if m > 0 then 32 + 8 * m else 0 in
  if m = 0 then
    ()
  else
    calc (==) {
      UInt.to_vec (U32.v (U32.logxor crc (dword_seq_to_u32 a b c d)));
      =={}
      (UInt.to_vec (v crc)) +@ (UInt.to_vec (v sum));
      =={poly_mod_zero_suffix (UInt.to_vec (v sum)) (prev_len - 32)}
      poly_mod (crc32_data_to_bits m data) +@ poly_mod (zero_vec_r (prev_len - 32) vsum);
      =={poly_mod_add (crc32_data_to_bits m data) (zero_vec_r (prev_len - 32) vsum)}
      poly_mod ((crc32_data_to_bits m data) +@ (zero_vec_r (prev_len - 32) vsum));
    }

#set-options "--z3rlimit 120 --fuel 0 --ifuel 0"
private let do4_table_lookup
  (r: U32.t) (t0: U32.t{
    let open U32 in poly_mod_correct 32 (r &^ 0xFFul) t0
  }) (t1: U32.t{
    let open U32 in poly_mod_correct 24 ((r >>^ 8ul) &^ 0xFFul) t1
  }) (t2: U32.t{
    let open U32 in poly_mod_correct 16 ((r >>^ 16ul) &^ 0xFFul) t2
  }) (t3: U32.t{
    let open U32 in poly_mod_correct 8 (r >>^ 24ul) t3
  }) (sum: U32.t{
    let open U32 in sum == t0 ^^ t1 ^^ t2 ^^ t3
  }): Lemma
  (ensures poly_mod (zero_vec_l 32 (UInt.to_vec (U32.v r))) == UInt.to_vec (U32.v sum)) =
  let open U32 in
  let r0 = r &^ 0xFFul in
  let r1 = (r >>^ 8ul) &^ 0xFFul in
  let r2 = (r >>^ 16ul) &^ 0xFFul in
  let r3 = r >>^ 24ul in
  let vr = v r in let vr0 = v r0 in let vr1 = v r1 in let vr2 = v r2 in let vr3 = v r3 in
  let vr' = UInt.to_vec vr in let vr0' = UInt.to_vec vr0 in let vr1' = UInt.to_vec vr1 in
  let vr2' = UInt.to_vec vr2 in let vr3' = UInt.to_vec vr3 in

  logand_256 r; logand_256 (r >>^ 8ul); logand_256 (r >>^ 16ul);

  poly_mod_correct_eq 32 r0 t0; poly_mod_correct_eq 24 r1 t1;
  poly_mod_correct_eq 16 r2 t2; poly_mod_correct_eq 8 r3 t3;

  poly_mod_zero_suffix (zero_vec_l 24 vr1') 8;
  poly_mod_zero_suffix (zero_vec_l 16 vr2') 16;
  poly_mod_zero_suffix (zero_vec_l 8 vr3') 24;

  poly_mod_add (zero_vec_l 32 vr0') (zero_vec_r 8 (zero_vec_l 24 vr1'));
  poly_mod_add
    ((zero_vec_l 32 vr0') +@ zero_vec_r 8 (zero_vec_l 24 vr1'))
    (zero_vec_r 16 (zero_vec_l 16 vr2'));
  poly_mod_add
    ((zero_vec_l 32 vr0') +@
     zero_vec_r 8 (zero_vec_l 24 vr1') +@
     zero_vec_r 16 (zero_vec_l 16 vr2'))
    (zero_vec_r 24 (zero_vec_l 8 vr3'));
    
  assert(Seq.equal (zero_vec_l 32 vr') (
    (zero_vec_l 32 vr0') +@
    (zero_vec_r 8 (zero_vec_l 24 vr1')) +@
    (zero_vec_r 16 (zero_vec_l 16 vr2')) +@
    (zero_vec_r 24 (zero_vec_l 8 vr3'))
  ));

  assert(Seq.equal
    (UInt.to_vec (v sum))
    ((poly_mod_u32 32 r0) +@
    (poly_mod_u32 24 r1) +@
    (poly_mod_u32 16 r2) +@
    (poly_mod_u32 8 r3)))

#set-options "--z3rlimit 120 --fuel 0 --ifuel 0"
inline_for_extraction
private let do4
  (#m: Ghost.erased nat)
  (data: Ghost.erased (Seq.seq U8.t){Seq.length data == Ghost.reveal m})
  (t8 t16 t24 t32: Spec.table_buf)
  (crc: U32.t)
  (a b c d: U8.t):
  ST.Stack (U32.t & (Ghost.erased (Seq.seq U8.t)))
  (requires fun h ->
    table_group_correct h t8 t16 t24 t32 /\
    crc32_matched m data crc false)
  (ensures fun h0 res h1 ->
    let crc' = fst res in
    let data' = Ghost.reveal (snd res) in
    B.modifies B.loc_none h0 h1 /\
    data' == data @| (Seq.init 4 (fun i -> match i with | 0 -> a | 1 -> b | 2 -> c | 3 -> d)) /\
    crc32_matched (m + 4) data' crc' false) =
  let open U32 in
  let dw = dword_seq_to_u32 a b c d in
  let dw' = Ghost.hide (UInt.to_vec (v dw)) in
  let r = crc ^^ dw in
  let r' = Ghost.hide (UInt.to_vec (v r)) in
  let r0 = r &^ 0xFFul in
  let r1 = (r >>^ 8ul) &^ 0xFFul in
  let r2 = (r >>^ 16ul) &^ 0xFFul in
  let r3 = r >>^ 24ul in
  UInt.logand_le (v r) 255;
  UInt.logand_le (v (r >>^ 8ul)) 255;
  UInt.logand_le (v (r >>^ 16ul)) 255;
  Math.lemma_div_lt (v r) 32 24;
  do4_logxor #m data crc a b c d;

  let t0 = t32.(r0) in let t1 = t24.(r1) in let t2 = t16.(r2) in let t3 = t8.(r3) in
  let crc' = t0 ^^ t1 ^^ t2 ^^ t3 in
  do4_table_lookup r t0 t1 t2 t3 crc';

  let seq_32bit = Ghost.hide (crc32_dword_seq a b c d) in
  let buf:
    Ghost.erased (BV.bv_t (if m > 0 then 32 + 8 * m else 0)) =
    Ghost.hide (crc32_data_to_bits m data) in

  assert(poly_mod (zero_vec_l 32 (UInt.to_vec (U32.v r))) == (UInt.to_vec (U32.v crc')));
  crc32_data_to_bits_append m 4 data seq_32bit;
  crc32_data_to_bits_32bit m data buf dw;
  if Ghost.reveal m > 0 then
    poly_mod_zero_prefix ((zero_vec_r (8 * m) dw') +@ buf) 32
  else
    assert(Seq.equal seq_32bit (data @| seq_32bit));

  (crc', Ghost.hide (data @| seq_32bit))

let crc32_impl m data t8 t16 t24 t32 crc buf len =
  let open U32 in
  ST.push_frame ();
  let crc' = crc ^^ 0xfffffffful in
  crc32_matched_xor_inv_1 m data crc;
  let ((c0, buf'), data') = if len %^ 4ul >^ 0ul then
    do1_remain m data m data t8 len 0ul buf crc'
  else
    ((crc', buf), data)
  in
  admit();
  ST.pop_frame ();
  c0
