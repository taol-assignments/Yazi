module Yazi.CRC32

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

private type matrix_buf = B.lbuffer U32.t 32

[@ (CPrologue "#ifndef YAZI_CRC32_TABLE_GEN
uint32_t crc32_z(uint32_t crc, const unsigned char *buf, size_t len);")
  (CEpilogue "#endif")]
val crc32:
    data: Ghost.erased (Seq.seq U8.t)
  -> crc: U32.t
  -> buf: CB.const_buffer U8.t
  -> len: U32.t
  -> ST.Stack U32.t
  (requires fun h ->
    CB.live h buf /\ CB.length buf == U32.v len /\
    Spec.crc32_matched (Seq.length data) data crc true)
  (ensures fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    Spec.crc32_matched
      (Seq.length data + U32.v len)
      (Seq.append data (CB.as_seq h1 buf)) res true)

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
    t8: B.lbuffer U32.t 256
  -> t16: B.lbuffer U32.t 256
  -> t24: B.lbuffer U32.t 256
  -> t32: B.lbuffer U32.t 256
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
    Spec.table_correct 8 h1 (CB.of_buffer t8) /\
    Spec.table_correct 16 h1 (CB.of_buffer t16) /\
    Spec.table_correct 24 h1 (CB.of_buffer t24) /\
    Spec.table_correct 32 h1 (CB.of_buffer t32))

[@ (CPrologue "#ifdef YAZI_CRC32_TABLE_GEN")
   (CEpilogue "#endif")]
val gen_matrix_table: buf: Spec.matrix_buf -> ST.Stack unit
  (requires fun h -> B.live h buf)
  (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer buf) h0 h1 /\ Spec.is_matrix_buf h1 8 buf)

