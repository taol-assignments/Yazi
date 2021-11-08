module Yazi.CRC32
module B = LowStar.Buffer
module BV = FStar.BitVector
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module List = FStar.List.Tot
module Math = FStar.Math.Lemmas
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt

open FStar.Mul
open FStar.Seq
open Lib.UInt
open LowStar.BufferOps
open Spec.CRC32

private noeq type current_state_t = {
  clen: Ghost.erased nat;
  consumed: Ghost.erased (Seq.seq U8.t);
  crc: U32.t;
  slen: U32.t;
  stream: CB.const_buffer U8.t;
}

private type current_state = p: current_state_t {
  Seq.length p.consumed == Ghost.reveal p.clen /\
  CB.length p.stream == U32.v p.slen
}

private noeq type init_state_t = {
  dlen: nat;
  blen: nat;
  base: CB.const_buffer U8.t;
  data: Seq.seq U8.t;
}

private type init_state = s: init_state_t {
  CB.length s.base == s.blen /\
  Seq.length s.data == s.dlen
}

let do_pre_cond
  (h: HS.mem) (p: current_state) (d: init_state) (i: nat) (size: pos) =
  let slen' = U32.v p.slen in
  CB.live h p.stream /\
  CB.live h d.base /\  

  i + size <= d.blen /\
  slen' >= size /\
  slen' % size == 0 /\
  slen' == d.blen - i /\
  
  (let base' = CB.as_seq h d.base in
  let pending = Seq.slice base' i d.blen in
  let consumed = Seq.slice base' 0 i in
  Seq.equal (B.as_seq h (CB.as_mbuf p.stream)) pending /\
  Seq.equal (d.data @| consumed) p.consumed) /\
  
  crc32_matched p.clen p.consumed p.crc false

let do_post_cond
  (h0 h1: HS.mem)
  (d: init_state)
  (res: (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t)))
  (i: nat)
  (size: pos)
  (next_size: option nat) =
  let i' = match next_size with
    | None -> i + size
    | Some ns -> if ns > 0 then d.blen % ns else d.blen
  in
  let base' = CB.as_seq h1 d.base in
  let (crc', buf', data') = res in
  B.(modifies loc_none h0 h1) /\
  
  CB.live h1 buf' /\ CB.length buf' == d.blen - i' /\

  CB.length buf' == d.blen - i' /\
  Seq.equal (CB.as_seq h1 buf') (Seq.slice base' i' d.blen) /\
  Seq.equal data' (d.data @| (Seq.slice base' 0 i')) /\
  
  crc32_matched (d.dlen + i') data' crc' false

private unfold let u8_padding (b: U8.t) (n: pos): Tot (BV.bv_t (32 + 8 * n)) =
  (BV.zero_vec #24) @| (UInt.to_vec (U8.v b)) @| BV.zero_vec #(8 * n)

#set-options "--z3rlimit 120 --z3seed 13 --fuel 0 --ifuel 0"
let do1_logxor (m: nat) (data: Seq.seq U8.t) (crc: U32.t) (b: U8.t): Lemma
  (requires Seq.length data == m /\ crc32_matched m data crc false)
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

[@ (CPrologue "#if 0")
   (CEpilogue "#endif")]
assume val get_crc32_table: i: U32.t{U32.v i < 4} -> ST.Stack (Spec.table_buf)
  (requires fun h -> True)
  (ensures fun h0 t h1 ->
    B.modifies B.loc_none h0 h1 /\
    CB.live h1 t /\ Spec.table_correct (8 * (U32.v i + 1)) h1 t)

#set-options "--z3rlimit 400 --z3seed 1 --fuel 1 --ifuel 1"
inline_for_extraction let do1
  (p: current_state)
  (d: Ghost.erased init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h p d i 1)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 1 None) =
  let b = CB.index p.stream 0ul in
  let b' = Cast.uint8_to_uint32 b in
  let open U32 in
  let r = p.crc ^^ b' in
  let r' = r >>^ 8ul in
  UInt.logand_le (v r) (v 0xFFul);
  
  let t8 = get_crc32_table 0ul in
  let tv = CB.index t8 (r &^ 0xFFul) in

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

  (crc', CB.sub p.stream 1ul (p.slen -^ 1ul), Ghost.hide (Seq.snoc p.consumed b))

#set-options "--z3rlimit 200 --ifuel 0 --fuel 0 --z3seed 7"
[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
let rec iteration_1
  (p: current_state)
  (d: Ghost.erased init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: U32.t{U32.v i < d.blen % 4}):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases U32.v i - U32.v p.slen % 4)
  (requires fun h -> do_pre_cond h p d (U32.v i) 1)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res (U32.v i) 1 (Some 4)) =
  let open U32 in
  let (crc', stream', data') = do1 p d (v i) in
  if i +^ 1ul <^ base_len %^ 4ul then begin
    iteration_1 ({
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

let do4_logxor (m: nat) (data: Seq.seq U8.t) (crc: U32.t) (a b c d: U8.t): Lemma
  (requires Seq.length data == m /\ crc32_matched m data crc false)
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
  (p: current_state)
  (d: Ghost.erased init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h p d i 4)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 4 None) = 
  let open U32 in
  let a = CB.index p.stream (0ul) in
  let b = CB.index p.stream (1ul) in
  let c = CB.index p.stream (2ul) in
  let d = CB.index p.stream (3ul) in
  
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
  do4_logxor p.clen p.consumed p.crc a b c d;

  let t8 = get_crc32_table 0ul in let t16 = get_crc32_table 1ul in
  let t24 = get_crc32_table 2ul in let t32 = get_crc32_table 3ul in
  let t0 = CB.index t32 r0 in
  let t1 = CB.index t24 r1 in
  let t2 = CB.index t16 r2 in
  let t3 = CB.index t8 r3 in
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

  (crc', CB.sub p.stream 4ul (p.slen -^ 4ul), Ghost.hide (p.consumed @| seq_32bit))

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
let rec iteration_4
  (p: current_state)
  (d: Ghost.erased init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: U32.t{U32.v i < d.blen % 32}):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases U32.v i - U32.v p.slen % 32)
  (requires fun h -> do_pre_cond h p d (U32.v i) 4)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res (U32.v i) 4 (Some 32)) =
  let open U32 in
  let (crc', stream', data') = do4 p d (v i) in
  if i +^ 4ul <^ base_len %^ 32ul then
    iteration_4 ({
      clen = p.clen + 4;
      consumed = data';
      crc = crc';
      slen = p.slen -^ 4ul;
      stream = stream';
    }) d base_len (i +^ 4ul)
  else
    (crc', stream', data')

#set-options "--z3refresh --z3rlimit 1024 --fuel 1 --ifuel 1 --z3seed 1"
inline_for_extraction let do8
  (p: current_state)
  (d: Ghost.erased init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h p d i 8)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 8 None) =
  let open U32 in
  let (c0, b0, d0) = do4 p d i in
  do4 ({
    clen = p.clen + 4;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 4ul;
    stream = b0;
  }) d (i + 4)

inline_for_extraction let do16
  (p: current_state)
  (d: Ghost.erased init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h p d i 16)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 16 None) =
  let open U32 in
  let (c0, b0, d0) = do8 p d i in
  let (c1, b1, d1) = do8 ({
    clen = p.clen + 8;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 8ul;
    stream = b0;
  }) d (i + 8) in
  (c1, b1, d1)

inline_for_extraction let do32
  (p: current_state)
  (d: Ghost.erased init_state)
  (i: Ghost.erased nat):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & Ghost.erased (Seq.seq U8.t))
  (requires fun h -> do_pre_cond h p d i 32)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 32 None) =
  let open U32 in
  let (c0, b0, d0) = do16 p d i in
  let (c1, b1, d1) = do16 ({
    clen = p.clen + 16;
    consumed = d0;
    crc = c0;
    slen = p.slen -^ 16ul;
    stream = b0;
  }) d (i + 16) in
  (c1, b1, d1)

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
let rec iteration_32
  (p: current_state)
  (d: Ghost.erased init_state)
  (base_len: U32.t{U32.v base_len == d.blen})
  (i: Ghost.erased nat{i + 32 <= d.blen}):
  ST.Stack (U32.t & (CB.const_buffer U8.t) & (Ghost.erased (Seq.seq U8.t)))
  (decreases d.blen - i)
  (requires fun h -> do_pre_cond h p d i 32)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d res i 32 (Some 0)) =
  let open U32 in
  let (crc', buf', data') = do32 p d i in
  if p.slen -^ 32ul >=^ 32ul then
    iteration_32 ({
      clen = p.clen + 32;
      consumed = data';
      crc = crc';
      slen = p.slen -^ 32ul;
      stream = buf';
    }) d base_len (i + 32)
  else
    (crc', buf', data')

type it_tuple = (U32.t & (CB.const_buffer U8.t) & U32.t & Ghost.erased (Seq.seq U8.t))

#set-options "--fuel 0 --ifuel 0"
let crc32 data' crc buf len =
  let open U32 in
  ST.push_frame ();
  let crc' = crc ^^ 0xFFFFFFFFul in
  let d: Ghost.erased init_state = {
    dlen = Seq.length data';
    blen = CB.length buf;
    base = buf;
    data = data';
  } in
  crc32_matched_xor_inv_1 d.dlen d.data crc;
  
  let (c0, b0, l0, d0): it_tuple = if len %^ 4ul >^ 0ul then
    let (c', b', d') = iteration_1 ({
      clen = d.dlen;
      consumed = d.data; 
      crc = crc';
      slen = len;
      stream = buf;
    }) d len 0ul
    in
    (c', b', len -^ (len %^ 4ul), d')
  else
    (crc', buf, len, Ghost.hide d.data)
  in
  let (c1, b1, l1, d1): it_tuple = if l0 %^ 32ul >^ 0ul then
    let (c', b', d') = iteration_4 ({
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
    let (c', _, d') = iteration_32 ({
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
  (nzeros: Ghost.erased pos)
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

let gf2_matrix_times (nzeros: Ghost.erased pos) (buf: matrix_buf) (vec: U32.t):
  ST.Stack (Spec.matrix_times_product nzeros vec)
  (requires fun h -> Spec.is_matrix_buf h nzeros buf)
  (ensures fun h0 res h1 -> B.(modifies loc_none h0 h1)) =
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
  end
  in
  do_gf2_matrix_times nzeros vec buf 1ul (vec >>^ 1ul) sum

inline_for_extraction
let rec do_gf2_matrix_square
  (nzeros: Ghost.erased pos) (b0 b1: matrix_buf) (i: U32.t{U32.v i < 32}):
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

let gf2_matrix_square (nzeros: Ghost.erased pos) (b0: matrix_buf) (b1: matrix_buf):
  ST.Stack unit
  (requires fun h -> B.live h b1 /\ B.disjoint b0 b1 /\ Spec.is_matrix_buf h nzeros b0)
  (ensures fun h0 _ h1 ->
     B.modifies (B.loc_buffer b1) h0 h1 /\ Spec.is_matrix_buf h1 (nzeros * 2) b1) =
  do_gf2_matrix_square nzeros b0 b1 0ul

let combine_len_aux
  (init_len post_len: UInt.uint_t 64) (cur_len next_len: U64.t) (i: U32.t): Lemma
  (requires
    U64.v cur_len * (pow2 (U32.v i)) + post_len == (init_len <: int) /\
    U64.v next_len == U64.v cur_len / 2)
  (ensures (
    let i = U32.v i in
    let cur_len = U64.v cur_len in
    let next_len = U64.v next_len in
    (cur_len % 2 == 1 ==>
      next_len * pow2 (i + 1) + pow2 i + post_len == (init_len <: int) /\
      pow2 i + post_len < pow2 64) /\
    (cur_len % 2 == 0 ==>
      next_len * pow2 (i + 1) + post_len == (init_len <: int)))) =
  Math.pow2_plus (U32.v i) 1

#push-options "--z3refresh --z3rlimit 2048 --z3seed 11 --fuel 0 --ifuel 0"
let rec do_crc32_combine
  (nzeros: Ghost.erased pos)
  (init_len: Ghost.erased (UInt.uint_t 64){init_len > 0})
  (post_len: Ghost.erased (UInt.uint_t 64))
  (cur_len: U64.t)
  (init_crc: Ghost.erased U32.t) (crc i: U32.t)
  (odd even: matrix_buf):
  ST.Stack (matrix_times_product (init_len * 8) init_crc)
  (requires fun h ->
    let cur_len = U64.v cur_len in
    let i = U32.v i in
    B.live h odd /\ B.live h even /\ B.disjoint odd even /\
    Ghost.reveal nzeros == pow2 (i + 3) /\
    i <= 64 /\
    is_matrix_buf h nzeros odd /\
    cur_len * (pow2 i) + post_len == (init_len <: int) /\
    (Ghost.reveal post_len > 0 ==>
      UInt.to_vec (U32.v crc) ==
      poly_mod (zero_vec_l (post_len * 8) (UInt.to_vec (U32.v init_crc)))) /\
    (Ghost.reveal post_len == 0 ==> crc == Ghost.reveal init_crc))
  (ensures fun h0 crc' h1 ->
    B.modifies (B.loc_buffer odd `B.loc_union` B.loc_buffer even) h0 h1)
  (decreases 64 - U32.v i) =
  let open U64 in
  let vi = Ghost.hide (U32.v i) in
  let vcrc = Ghost.hide (UInt.to_vec (U32.v crc)) in
  let vinit_crc = Ghost.hide (UInt.to_vec (U32.v init_crc)) in
  
  if cur_len =^ 0UL || U32.eq i 64ul then begin
    assert(Seq.equal
      (bit_sum (zero_vec_l (init_len * 8) vinit_crc) 31)
      (zero_vec_l (init_len * 8) vinit_crc));
    crc
  end else begin    
    gf2_matrix_square (Ghost.reveal nzeros) odd even;
    let next_len = cur_len /^ 2UL in
    
    Math.pow2_plus (vi + 3) 1;
    assert(nzeros * 2 == pow2 (vi + 4));
    combine_len_aux init_len post_len cur_len next_len i;
    let t1 = odd in let t2 = even in
    if (cur_len %^ 2UL) =^ 1UL then begin
      let crc' = gf2_matrix_times nzeros odd crc in
      let next_post_len: Ghost.erased (UInt.uint_t 64) =
        Ghost.hide (post_len + pow2 vi)
      in
      if post_len > 0 then
        calc (==) {
          UInt.to_vec (U32.v crc');
          =={
            assert(Seq.equal
              (bit_sum (zero_vec_l nzeros vcrc) 31)
              (zero_vec_l nzeros vcrc))
          }
          poly_mod (zero_vec_l nzeros vcrc);
          =={}
          poly_mod (zero_vec_l nzeros (
            poly_mod (zero_vec_l (post_len * 8) vinit_crc)
          ));
          =={
            poly_mod_zero_prefix (zero_vec_l (post_len * 8) vinit_crc) nzeros
          }
          poly_mod (zero_vec_l nzeros (zero_vec_l (post_len * 8) vinit_crc));
          =={zero_vec_l_app vinit_crc (post_len * 8) nzeros}
          poly_mod (zero_vec_l (nzeros + post_len * 8) vinit_crc);
          =={
            calc (==) {
              nzeros + post_len * 8;
              =={}
              pow2 (vi + 3) + post_len * 8;
              ={Math.pow2_plus vi 3}
              (pow2 vi) * pow2 3 + post_len * 8;
              =={assert_norm(pow2 3 == 8)}
              (post_len + pow2 vi) * 8;
              =={}
              next_post_len * 8;
            }
          }
          poly_mod (zero_vec_l (next_post_len * 8) (UInt.to_vec (U32.v init_crc)));
        }
      else
        calc (==) {
          UInt.to_vec (U32.v crc');
          =={
            assert(Seq.equal
              (bit_sum (zero_vec_l nzeros vcrc) 31)
              (zero_vec_l nzeros vcrc))
          }
          poly_mod (zero_vec_l nzeros vcrc);
          =={}
          poly_mod (zero_vec_l (pow2 (vi + 3)) vcrc);
          =={
            Math.pow2_plus vi 3;
            assert_norm(pow2 3 == 8)
          }
          poly_mod (zero_vec_l (next_post_len * 8) vinit_crc);
        };
      do_crc32_combine
        (nzeros * 2) init_len next_post_len next_len
        init_crc crc' (U32.add i 1ul) t2 t1
    end else
      do_crc32_combine
        (nzeros * 2) init_len post_len next_len
        init_crc crc (U32.add i 1ul) t2 t1
  end

[@ (CPrologue "#if 0")
   (CEpilogue "#endif")]
assume val init_magic_matrix: m: matrix_buf -> ST.Stack unit
  (requires fun h -> B.live h m)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer m) h0 h1 /\ is_matrix_buf h1 8 m)

let crc32_combine64 s1 s2 crc1 crc2 length =
  let open U64 in
  if length =^ 0UL then
    crc1
  else begin
    ST.push_frame ();
    let odd = B.alloca 0ul 32ul in
    let even = B.alloca 0ul 32ul in
    init_magic_matrix odd;

    assert_norm(pow2 3 == 8);
    let crc1' = do_crc32_combine 8 (v length) 0 length crc1 crc1 0ul odd even in
    crc32_matched_append (Seq.length s1) (v length) s1 s2 crc1 crc2 crc1';
    
    ST.pop_frame ();
    U32.logxor crc1' crc2
  end

(**** CRC-32 Table Generation Functions. ****)
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
  if i = 0ul || i = 1ul || i = 2ul || i = 4ul || i = 5ul || i = 7ul || i = 8ul ||
  i = 10ul || i = 11ul || i = 12ul || i = 16ul || i = 22ul || i = 23ul || i = 26ul then
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

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
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
  let open FStar.Tactics in
  assert(forall i. UInt.nth (U32.v 0ul) i == false) by (
    let _ = forall_intro () in
    norm [simplify]);

  calc_polynomial 0ul 0ul
#reset-options

let poly_mod_head_zero (d: U32.t): Lemma
  (requires UInt.nth (U32.v d) 31 == false)
  (ensures poly_mod_correct 1 d (U32.shift_right d 1ul)) = ()

let bv_one_aux (#n: pos) (v: BV.bv_t n): Lemma
  (requires forall i.
    (i < n - 1 ==> Seq.index v i == false) /\
    (i == n - 1 ==> Seq.index v i == true))
  (ensures UInt.from_vec v == 1) =
  match n with
  | 1 -> ()
  | _ -> assert(Seq.equal (Seq.slice v 0 (n - 1)) (BV.zero_vec #(n - 1)))

let logand_aux (#n: pos) (d: UInt.uint_t n): Lemma
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

#set-options "--z3rlimit 200 --z3seed 1 --fuel 1 --ifuel 1"
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

let cell_xor_app (nzeros: pos) (d res: U32.t): Lemma
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

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
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

#set-options "--fuel 1 --ifuel 1"
[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
private let rec gen_8bit_table
  (i: U32.t{U32.v i <= 255}) (buf: B.lbuffer U32.t 256): ST.Stack unit
  (decreases 255 - U32.v i)
  (requires fun h -> sub_table_correct (U32.v i) 8 h (CB.of_buffer buf))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer buf) h0 h1 /\ table_correct 8 h1 (CB.of_buffer buf)) =
  let open U32 in
  buf.(i) <- calc_cell i 7ul i;
  if i <^ 255ul then gen_8bit_table (i +^ 1ul) buf else ()

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
private let rec gen_large_table
  (nzeros: Ghost.erased pos)
  (i: U32.t{U32.v i <= 255})
  (t8 tp buf: B.lbuffer U32.t 256):
  ST.Stack unit
    (decreases 255 - U32.v i)
    (requires fun h ->
      B.disjoint buf t8 /\
      B.disjoint buf tp /\
      table_correct 8 h (CB.of_buffer t8) /\
      table_correct nzeros h (CB.of_buffer tp) /\
      sub_table_correct (U32.v i) (nzeros + 8) h (CB.of_buffer buf) /\
      B.live h t8 /\ B.live h tp)
    (ensures fun h0 _ h1 -> 
      B.modifies (B.loc_buffer buf) h0 h1 /\
      table_correct (nzeros + 8) h1 (CB.of_buffer buf)) =
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

#set-options "--fuel 1 --ifuel 1"
[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
let rec gf2_matrix_init
  (p: U32.t{UInt.to_vec (U32.v p) == gf2_polynomial32})
  (i: U32.t{U32.v i < 32})
  (buf: matrix_buf):
  ST.Stack unit
  (decreases 32 - U32.v i)
  (requires fun h -> is_sub_matrix_buf h (U32.v i) 1 buf)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer buf) h0 h1 /\ is_matrix_buf h1 1 buf) =
  let open U32 in
  if i = 0ul then
    let m = Ghost.hide (ones_vec_r 1 (BV.zero_vec #32)) in
    calc (==) {
      poly_mod #33 m;
      =={assert(Seq.last m == true)}
      unsnoc (m -@ poly 33);
      =={assert(Seq.equal (unsnoc (m -@ poly 33)) gf2_polynomial32)}
      UInt.to_vec (v p);
    };
    buf.(i) <- p
  else begin
    let pattern = Ghost.hide (magic_matrix_pattern 1 (U32.v i)) in
    let elem = 1ul <<^ (i -^ 1ul) in 
    one_shift_left (i -^ 1ul);
    assert(Seq.equal (poly_mod #33 pattern) (unsnoc pattern));
    assert(forall (j: nat{j < 32}). Seq.index (unsnoc pattern) j == UInt.nth (v elem) j);
    assert(Seq.equal (UInt.to_vec (v elem)) (poly_mod #33 pattern));
    buf.(i) <- 1ul <<^ (i -^ 1ul)
  end;
  if i <^ 31ul then gf2_matrix_init p (i +^ 1ul) buf else ()

#set-options "--fuel 0 --ifuel 0"
let gen_matrix_table buf =
  ST.push_frame();
  let t = B.alloca 0ul 32ul in
  let p = gen_polynomial () in
  assert(Seq.equal (UInt.to_vec (U32.v p)) gf2_polynomial32);
  gf2_matrix_init p 0ul t;

  gf2_matrix_square 1 t buf;
  gf2_matrix_square 2 buf t;
  gf2_matrix_square 4 t buf;
  ST.pop_frame()
