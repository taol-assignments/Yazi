module Yazi.CRC32.Impl

module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module Ghost = FStar.Ghost
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Spec = Spec.CRC32
module ST = FStar.HyperStack.ST

private type table_group = t: B.buffer U32.t{B.length t == 1024}

private unfold let unfold_table_group_ghost (t: table_group):
  GTot (Spec.table_buf & Spec.table_buf & Spec.table_buf & Spec.table_buf) =
  let t8 = B.gsub t 0ul 256ul in
  let t16 = B.gsub t 256ul 256ul in
  let t24 = B.gsub t 512ul 256ul in
  let t32 = B.gsub t 768ul 256ul in
  (t8, t16, t24, t32)

private unfold let table_group_correct_pre (h: HS.mem) (tg:table_group) =
  B.live h tg /\
  (let (t8, t16, t24, t32) = unfold_table_group_ghost tg in
  Spec.table_correct 8 h t8 /\
  Spec.table_correct 16 h t16 /\
  Spec.table_correct 24 h t24 /\
  Spec.table_correct 32 h t32 /\
  B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
  B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32)

private unfold let table_group_correct_post (h: HS.mem) (t8 t16 t24 t32: Spec.table_buf) =
  Spec.table_correct 8 h t8 /\
  Spec.table_correct 16 h t16 /\
  Spec.table_correct 24 h t24 /\
  Spec.table_correct 32 h t32 /\
  B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
  B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32 /\
  B.live h t8 /\ B.live h t16 /\ B.live h t24 /\ B.live h t32

private let unfold_table_group (tg: table_group):
  ST.Stack (Spec.table_buf & Spec.table_buf & Spec.table_buf & Spec.table_buf)
  (requires fun h -> table_group_correct_pre h tg)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    (let (t8, t16, t24, t32) = res in
    B.live h1 t8 /\ B.live h1 t16 /\ B.live h1 t24 /\ B.live h1 t32 /\
    table_group_correct_post h1 t8 t16 t24 t32)) =
  let t8 = B.sub tg 0ul 256ul in
  let t16 = B.sub tg 256ul 256ul in
  let t24 = B.sub tg 512ul 256ul in
  let t32 = B.sub tg 768ul 256ul in
  (t8, t16, t24, t32)

private noeq type crc32_current_state = {
  clen: Ghost.erased nat;
  consumed: Ghost.erased (Seq.seq U8.t);
  crc: U32.t;
  slen: U32.t;
  stream: B.buffer U8.t;
}

private noeq type crc32_init_state = {
  dlen: nat;
  blen: nat;
  base: B.buffer U8.t;
  data: Seq.seq U8.t;
}

private let crc32_pre_cond
  (h: HS.mem)
  (crc len: U32.t)
  (buf: B.buffer U8.t)
  (d: crc32_init_state) =
  let len' = U32.v len in
  d.base == buf /\ B.live h buf /\
  B.length buf == len' /\ B.length d.base == d.blen /\ Seq.length d.data == d.dlen /\
  Spec.crc32_matched d.dlen d.data crc true

private type matrix_buf = B.lbuffer U32.t 32

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
val crc32_impl:
    tg: table_group
  -> crc: U32.t
  -> len: U32.t
  -> buf: B.buffer U8.t
  -> d: Ghost.erased crc32_init_state
  -> ST.Stack U32.t
  (requires fun h ->
    crc32_pre_cond h crc len buf d /\
    B.disjoint buf tg /\
    table_group_correct_pre h tg)
  (ensures fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    Spec.crc32_matched (d.dlen + U32.v len) (Seq.append d.data (B.as_seq h1 buf)) res true)

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
val crc32_combine64:
    s1: Ghost.erased (Seq.seq U8.t)
  -> s2: Ghost.erased (Seq.seq U8.t)
  -> crc1: U32.t
  -> crc2: U32.t
  -> length: U64.t
  -> ST.Stack U32.t
    (requires fun h ->
      Spec.crc32_matched (Seq.length s1) s1 crc1 true /\
      Spec.crc32_matched (Seq.length s2) s2 crc2 true /\
      U64.v length == Seq.length s2)
    (ensures fun h0 res h1 ->
      B.(modifies loc_none h0 h1) /\
      Spec.crc32_matched (Seq.length s1 + Seq.length s2) (Seq.append s1 s2) res true)

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
let crc32_combine (s1 s2: Ghost.erased (Seq.seq U8.t)) (crc1 crc2 length: U32.t):
ST.Stack U32.t
(requires fun h ->
  Spec.crc32_matched (Seq.length s1) s1 crc1 true /\
  Spec.crc32_matched (Seq.length s2) s2 crc2 true /\
  U32.v length == Seq.length s2)
(ensures fun h0 res h1 ->
  B.(modifies loc_none h0 h1) /\
  Spec.crc32_matched (Seq.length s1 + Seq.length s2) (Seq.append s1 s2) res true) =
  crc32_combine64 s1 s2 crc1 crc2 (Cast.uint32_to_uint64 length)

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
val gen_crc32_table:
    t8: Spec.table_buf
  -> t16: Spec.table_buf
  -> t24: Spec.table_buf
  -> t32: Spec.table_buf
  -> ST.Stack unit
  (requires fun h ->
    B.live h t8 /\ B.live h t16 /\ B.live h t24 /\ B.live h t32 /\
    B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
    B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32)
  (ensures fun h0 _ h1 ->
    B.modifies 
      (B.loc_buffer t8 `B.loc_union`
      B.loc_buffer t16 `B.loc_union`
      B.loc_buffer t24 `B.loc_union`
      B.loc_buffer t32)
      h0 h1 /\
    Spec.table_correct 8 h1 t8 /\
    Spec.table_correct 16 h1 t16 /\
    Spec.table_correct 24 h1 t24 /\
    Spec.table_correct 32 h1 t32)

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
val gen_matrix_table:
    buf: Spec.matrix_buf
  -> ST.Stack unit
  (requires fun h -> B.live h buf)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer buf) h0 h1 /\ Spec.is_matrix_buf h1 8 buf)
