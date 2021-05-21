module Yazi.CRC32

module B = LowStar.Buffer
module BV = FStar.BitVector
module Ghost = FStar.Ghost
module HS = FStar.HyperStack
module M = LowStar.Modifies
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Spec = Spec.CRC32
module ST = FStar.HyperStack.ST

private unfold let table_group_correct h t8 t16 t24 t32 =
  Spec.table_correct 8 h t8 /\
  Spec.table_correct 16 h t16 /\
  Spec.table_correct 24 h t24 /\
  Spec.table_correct 32 h t32 /\
  B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
  B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32

val crc32_impl:
    n: Ghost.erased nat
  -> data: Ghost.erased (Seq.seq U8.t){Seq.length data == Ghost.reveal n}
  -> t8: Spec.table_buf
  -> t16: Spec.table_buf
  -> t24: Spec.table_buf
  -> t32: Spec.table_buf
  -> crc: U32.t
  -> buf: B.buffer U8.t
  -> len: U32.t{B.length buf == U32.v len}
  -> ST.Stack U32.t
  (requires fun h ->
    B.live h buf /\
    B.disjoint buf t8 /\ B.disjoint buf t16 /\ B.disjoint buf t24 /\ B.disjoint buf t32 /\
    table_group_correct h t8 t16 t24 t32 /\
    Spec.crc32_matched n data crc true)
  (ensures fun h0 res h1 ->
    M.modifies B.loc_none h0 h1 /\
    Spec.crc32_matched (n + U32.v len) (Seq.append data (B.as_seq h1 buf)) crc true)
