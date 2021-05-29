module Yazi.CRC32.Impl
module B = LowStar.Buffer
module BV = FStar.BitVector
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Mul
open FStar.Seq
open Lib.UInt
open LowStar.BufferOps
open Spec.CRC32

private unfold let do_pre_cond
  (h: HS.mem)
  (tg: table_group)
  (p: crc32_current_state)
  (d: crc32_init_state)
  (i: nat)
  (size: nat{size > 0}) =
  let slen' = U32.v p.slen in
  B.live h tg /\
  B.live h p.stream /\
  B.live h d.base /\  
  B.disjoint p.stream tg /\
  B.disjoint d.base tg /\

  i + size <= d.blen /\
  B.length p.stream == slen' /\
  slen' >= size /\
  slen' % size == 0 /\
  slen' == d.blen - i /\
  
  Seq.length p.consumed == Ghost.reveal p.clen /\
  B.length d.base == d.blen /\
  Seq.length d.data == d.dlen /\

  (let base' = B.as_seq h d.base in
  let pending = Seq.slice base' i d.blen in
  let consumed = Seq.slice base' 0 i in
  Seq.equal (B.as_seq h p.stream) pending /\
  Seq.equal (d.data @| consumed) p.consumed) /\
  
  crc32_matched p.clen p.consumed p.crc false /\
  table_group_correct_pre h tg

private unfold let do_post_cond
  (h0 h1: HS.mem)
  (tg: table_group)
  (p: crc32_current_state)
  (d: crc32_init_state)
  (res: (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t)))
  (i: nat)
  (size: nat{size > 0})
  (next_size: option nat) =
  let i' = match next_size with
    | None -> i + size
    | Some ns -> if ns > 0 then d.blen % ns else d.blen
  in
  let base' = B.as_seq h1 d.base in
  let (crc', buf', data') = res in
  B.(modifies loc_none h0 h1) /\
  
  B.length d.base == d.blen /\
  Seq.length d.data == d.dlen /\
  
  B.live h1 buf' /\ B.disjoint buf' tg /\ B.length buf' == d.blen - i' /\

  B.length buf' == d.blen - i' /\
  Seq.equal (B.as_seq h1 buf') (Seq.slice base' i' d.blen) /\
  Seq.equal data' (d.data @| (Seq.slice base' 0 i')) /\
  
  crc32_matched (d.dlen + i') data' crc' false

private unfold let u8_padding
  (b: U8.t)
  (n: nat{n > 0}):
  Tot (BV.bv_t (32 + 8 * n)) =
  (BV.zero_vec #24) @| (UInt.to_vec (U8.v b)) @| BV.zero_vec #(8 * n)

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
  
#set-options "--z3seed 1 --fuel 0 --ifuel 0"
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

#set-options "--z3rlimit 400 --z3seed 1 --fuel 1 --ifuel 1"
inline_for_extraction let do1
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h tg p d i 1)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 1 None) =
  let b = p.stream.(0ul) in
  let b' = Cast.uint8_to_uint32 b in
  let open U32 in
  let r = p.crc ^^ b' in
  let r' = r >>^ 8ul in
  UInt.logand_le (v r) (v 0xFFul);
  
  let (t8, _, _, _) = unfold_table_group tg in
  let tv = t8.(r &^ 0xFFul) in

  let crc' = r' ^^ tv in
  let buf: Ghost.erased (BV.bv_t (if Ghost.reveal p.clen = 0 then 0 else 32 + 8 * p.clen)) =
    Ghost.hide (crc32_data_to_bits p.clen p.consumed)
  in
  do1_logxor p.clen p.consumed p.crc b;
  do1_shift_right_logxor r tv;

  if Ghost.reveal p.clen > 0 then begin
    poly_mod_zero_prefix (buf +@ (u8_padding b p.clen)) 8;
    crc32_data_to_bits_append p.clen 1 p.consumed (Seq.create 1 b)
  end else
    assert(Seq.equal (zero_vec_l 8 (UInt.to_vec (v r))) (crc32_append_8bit buf b));

  (crc', B.sub p.stream 1ul (p.slen -^ 1ul), Ghost.hide (Seq.snoc p.consumed b))

#set-options "--z3rlimit 200 --ifuel 0 --fuel 0 --z3seed 7"
inline_for_extraction let rec iteration_1
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: U32.t{U32.v i < d.blen % 4}):
  ST.Stack (U32.t & (B.buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases U32.v i - U32.v p.slen % 4)
  (requires fun h -> do_pre_cond h tg p d (U32.v i) 1)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res (U32.v i) 1 (Some 4)) =
  let open U32 in
  let (crc', stream', data') = do1 tg p d (v i) in
  if i +^ 1ul <^ base_len %^ 4ul then begin
    iteration_1 tg ({
      clen = p.clen + 1;
      consumed = data';
      crc = crc';
      slen = p.slen -^ 1ul;
      stream = stream'
    }) d base_len (i +^ 1ul)
  end else
    (crc', stream', data')

inline_for_extraction
let dword_seq_to_u32 (a b c d: U8.t): Tot(crc32_data_dword a b c d) =
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

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let do4_table_lookup
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

inline_for_extraction let do4
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h tg p d i 4)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 4 None) = 
  let open U32 in
  let a = p.stream.(0ul) in
  let b = p.stream.(1ul) in
  let c = p.stream.(2ul) in
  let d = p.stream.(3ul) in
  
  let dw = dword_seq_to_u32 a b c d in
  let dw' = Ghost.hide (UInt.to_vec (v dw)) in
  let r = p.crc ^^ dw in
  let r' = Ghost.hide (UInt.to_vec (v r)) in
  let r0 = r &^ 0xFFul in
  let r1 = (r >>^ 8ul) &^ 0xFFul in
  let r2 = (r >>^ 16ul) &^ 0xFFul in
  let r3 = r >>^ 24ul in
  UInt.logand_le (v r) 255;
  UInt.logand_le (v (r >>^ 8ul)) 255;
  UInt.logand_le (v (r >>^ 16ul)) 255;
  Math.lemma_div_lt (v r) 32 24;
  do4_logxor #p.clen p.consumed p.crc a b c d;

  let (t8, t16, t24, t32) = unfold_table_group tg in
  let t0 = t32.(r0) in let t1 = t24.(r1) in let t2 = t16.(r2) in let t3 = t8.(r3) in
  let crc' = t0 ^^ t1 ^^ t2 ^^ t3 in
  do4_table_lookup r t0 t1 t2 t3 crc';

  let seq_32bit = Ghost.hide (crc32_dword_seq a b c d) in
  let buf:
    Ghost.erased (BV.bv_t (if p.clen > 0 then 32 + 8 * p.clen else 0)) =
    Ghost.hide (crc32_data_to_bits p.clen p.consumed) in

  crc32_data_to_bits_append p.clen 4 p.consumed seq_32bit;
  crc32_data_to_bits_32bit p.clen p.consumed buf dw;
  if Ghost.reveal p.clen > 0 then
    poly_mod_zero_prefix ((zero_vec_r (8 * p.clen) dw') +@ buf) 32
  else
    assert(Seq.equal seq_32bit (p.consumed @| seq_32bit));

  (crc', B.sub p.stream 4ul (p.slen -^ 4ul), Ghost.hide (p.consumed @| seq_32bit))

inline_for_extraction let rec iteration_4
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: U32.t{U32.v i < d.blen % 32}):
  ST.Stack (U32.t & (B.buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases U32.v i - U32.v p.slen % 32)
  (requires fun h -> do_pre_cond h tg p d (U32.v i) 4)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res (U32.v i) 4 (Some 32)) =
  let open U32 in
  let (crc', stream', data') = do4 tg p d (v i) in
  if i +^ 4ul <^ base_len %^ 32ul then
    iteration_4 tg ({
      clen = p.clen + 4;
      consumed = data';
      crc = crc';
      slen = p.slen -^ 4ul;
      stream = stream';
    }) d base_len (i +^ 4ul)
  else
    (crc', stream', data')

inline_for_extraction let do8
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h tg p d i 8)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 8 None) =
  let open U32 in
  let (c0, b0, d0) = do4 tg p d i in
  let (c1, b1, d1) = do4 tg ({
    clen = p.clen + 4;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 4ul;
    stream = b0;
  }) d (i + 4) in
  (c1, b1, d1)

inline_for_extraction let do16
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h tg p d i 16)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 16 None) =
  let open U32 in
  let (c0, b0, d0) = do8 tg p d i in
  let (c1, b1, d1) = do8 tg ({
    clen = p.clen + 8;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 8ul;
    stream = b0;
  }) d (i + 8) in
  (c1, b1, d1)

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
inline_for_extraction let do32
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (B.buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h tg p d i 32)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 32 None) =
  let open U32 in
  let (c0, b0, d0) = do16 tg p d i in
  let (c1, b1, d1) = do16 tg ({
    clen = p.clen + 16;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 16ul;
    stream = b0;
  }) d (i + 16) in
  (c1, b1, d1)

inline_for_extraction let rec iteration_32
  (tg: table_group)
  (p: crc32_current_state)
  (d: Ghost.erased crc32_init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: Ghost.erased nat{i + 32 <= d.blen}):
  ST.Stack (U32.t & (B.buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases d.blen - i)
  (requires fun h -> do_pre_cond h tg p d i 32)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 tg p d res i 32 (Some 0)) =
  let open U32 in
  let (crc', buf', data') = do32 tg p d i in
  if p.slen -^ 32ul >=^ 32ul then
    iteration_32 tg ({
      clen = p.clen + 32;
      consumed = data';
      crc = crc';
      slen = p.slen -^ 32ul;
      stream = buf';
    }) d base_len (i + 32)
  else
    (crc', buf', data')

type it_tuple = (U32.t & (B.buffer U8.t) & U32.t & Ghost.erased (Seq.seq U8.t))

let crc32_impl tg crc len buf d =
  let open U32 in
  ST.push_frame ();
  let crc' = crc ^^ 0xFFFFFFFFul in
  crc32_matched_xor_inv_1 d.dlen d.data crc;
  
  let (c0, b0, l0, d0): it_tuple = if len %^ 4ul >^ 0ul then begin
    let (c', b', d') = iteration_1 tg ({
      clen = d.dlen;
      consumed = d.data; 
      crc = crc';
      slen = len;
      stream = buf;
    }) d len 0ul
    in
    (c', b', len -^ (len %^ 4ul), d')
  end else
    (crc', buf, len, Ghost.hide d.data)
  in
  let (c1, b1, l1, d1): it_tuple = if l0 %^ 32ul >^ 0ul then
    let (c', b', d') = iteration_4 tg ({
      clen = d.dlen + v (len -^ l0);
      consumed = d0;
      crc = c0;
      slen = l0;
      stream = b0;
    }) d len (len -^ l0)
    in
    (c', b', l0 -^ (l0 %^ 32ul), d')
  else
    (c0, b0, l0, d0)
  in
  let (c2, d2): (U32.t & Ghost.erased (Seq.seq U8.t))  = if l1 >^ 0ul then
    let (c', _, d') = iteration_32 tg ({
      clen = d.dlen + v (len -^ l1);
      consumed = d1;
      crc = c1;
      slen = l1;
      stream = b1;
    }) d len (U32.v (len -^ l1))
    in
    (c', d')
  else
    (c1, d1)
  in
  ST.pop_frame ();
  crc32_matched_xor_inv_2 (d.dlen + v len) d2 c2;
  c2 ^^ 0xFFFFFFFFul

#set-options "--fuel 0 --ifuel 0"
inline_for_extraction
let rec do_gf2_matrix_times
  (nzeros: Ghost.erased nat{nzeros > 0})
  (vec': Ghost.erased U32.t)
  (buf: matrix_buf)
  (i: U32.t{0 < U32.v i /\ U32.v i < 32})
  (vec: U32.t{
    forall (j: nat{j >= U32.v i /\ j < 32}).
      UInt.nth (U32.v vec) j == UInt.nth (U32.v vec') (j - U32.v i)
  })
  (sum:sub_matrix_times_product nzeros (U32.v i - 1) vec'):
  ST.Stack (matrix_times_product nzeros vec')
  (decreases 31 - U32.v i)
  (requires fun h -> is_matrix_buf h nzeros buf)
  (ensures fun h0 res h1 -> B.(modifies loc_none h0 h1)) =
  let open U32 in
  let vec'' = Ghost.hide (zero_vec_l nzeros (UInt.to_vec (v vec'))) in
  let ext = Ghost.hide (bit_extract #(nzeros + 32) vec'' (v i)) in
  let prev = Ghost.hide (bit_sum #(nzeros + 32) vec'' (v i - 1)) in
  let current = Ghost.hide (bit_sum #(nzeros + 32) vec'' (v i)) in

  let t = if (vec &^ 1ul) = 1ul then begin
    UInt.one_nth_lemma #32 31;
    bit_extract_eq_pattern #(nzeros + 32) vec'' (v i);
    buf.(i)
  end else begin
    logand_one_ne (v vec);
    UInt.zero_nth_lemma #32 31;
    assert(Seq.equal ext (BV.zero_vec #(nzeros + 32)));
    poly_mod_zero (bit_extract #(nzeros + 32) vec'' (v i));
    0ul
  end in
  assert(Seq.equal (UInt.to_vec (v t)) (poly_mod #(nzeros + 32) ext));
  poly_mod_add prev ext;

  let sum' = sum ^^ t in
  assert(Seq.equal (poly_mod (ext +@ prev)) (UInt.to_vec (v sum')));
  assert(Seq.equal current (ext +@ prev));

  if i <^ 31ul then
    do_gf2_matrix_times nzeros vec' buf (i +^ 1ul) (vec >>^ 1ul) sum'
  else
    sum'

let gf2_matrix_times nzeros buf vec =
  let open U32 in
  let vec' = Ghost.hide (zero_vec_l nzeros (UInt.to_vec (v vec))) in
  let ext = Ghost.hide (bit_extract #(nzeros + 32) vec' 0) in
  let current = Ghost.hide (bit_sum #(nzeros + 32) vec' 0) in
  assert(Seq.equal ext current);

  let sum = if (vec &^ 1ul) = 1ul then begin
    UInt.one_nth_lemma #32 31;
    bit_extract_eq_pattern #(nzeros + 32) vec' 0;
    buf.(0ul)
  end else begin
    logand_one_ne (v vec);
    UInt.zero_nth_lemma #32 31;
    assert(Seq.equal ext (BV.zero_vec #(nzeros + 32)));
    poly_mod_zero #(nzeros + 32) (bit_extract #(nzeros + 32) vec' 0);
    assert(Seq.equal (UInt.to_vec (v 0ul)) (poly_mod #(nzeros + 32) current));
    0ul
  end in

  do_gf2_matrix_times nzeros vec buf 1ul (vec >>^ 1ul) sum

inline_for_extraction
let rec do_gf2_matrix_square
  (nzeros: Ghost.erased nat{nzeros > 0})
  (b0 b1: matrix_buf)
  (i: U32.t{U32.v i < 32}):
  ST.Stack unit
  (decreases 31 - U32.v i)
  (requires fun h ->
    B.live h b1 /\ B.disjoint b0 b1 /\
    is_matrix_buf h nzeros b0 /\
    is_sub_matrix_buf h (U32.v i) (nzeros * 2) b1)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer b1) h0 h1 /\
    is_matrix_buf h1 (nzeros * 2) b1) =
  let open U32 in
  let t = b0.(i) in

  let t' = Ghost.hide (zero_vec_l nzeros (UInt.to_vec (U32.v t))) in
  let r = gf2_matrix_times nzeros b0 t in
  let res' = Ghost.hide (UInt.to_vec (v r)) in
  let pat = Ghost.hide (magic_matrix_pattern nzeros (v i)) in

  calc (==) {
    Ghost.reveal res';
    =={}
    poly_mod (bit_sum t' 31);
    =={assert(Seq.equal (bit_sum t' 31) t')}
    poly_mod t';
    =={}
    poly_mod (zero_vec_l nzeros (poly_mod pat));
    =={poly_mod_zero_prefix pat nzeros}
    poly_mod (zero_vec_l nzeros pat);
    =={assert(Seq.equal (zero_vec_l nzeros pat) (magic_matrix_pattern (nzeros * 2) (v i)))}
    poly_mod (magic_matrix_pattern (nzeros * 2) (v i));
  };

  b1.(i) <- r;
  if i <^ 31ul then do_gf2_matrix_square nzeros b0 b1 (i +^ 1ul) else ()

let gf2_matrix_square nzeros b0 b1 = do_gf2_matrix_square nzeros b0 b1 0ul
