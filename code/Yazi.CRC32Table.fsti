module Yazi.CRC32Table

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module Ghost = FStar.Ghost
module HS = FStar.HyperStack
module Spec = Spec.CRC32
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32

type table_buf = buf: B.buffer U32.t{B.length buf == 256}

private unfold let sub_table_correct
  (j: nat{j <= 256})
  (nzeros: nat{nzeros > 0})
  (h: HS.mem)
  (buf: table_buf) =
  (B.live h buf) /\
  (forall i. i < j ==>
  Spec.poly_mod_correct nzeros (U32.uint_to_t i) (Seq.index (B.as_seq h buf) i))

private unfold let table_correct
  (nzeros: nat{nzeros > 0})
  (h: HS.mem)
  (buf: B.buffer U32.t{B.length buf == 256}) = sub_table_correct (B.length buf) nzeros h buf

open LowStar.BufferOps

val gen_crc32_table:
    t8: table_buf
  -> t16: table_buf
  -> t24: table_buf
  -> t32: table_buf
  -> ST.Stack unit
  (requires fun h ->
    B.live h t8 /\ B.live h t16 /\ B.live h t24 /\ B.live h t32 /\
    B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
    B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32)
  (ensures fun h0 _ h1 ->
    M.modifies 
      (B.loc_buffer t8 `B.loc_union`
      B.loc_buffer t16 `B.loc_union`
      B.loc_buffer t24 `B.loc_union`
      B.loc_buffer t32)
      h0 h1 /\
    table_correct 8 h1 t8 /\
    table_correct 16 h1 t16 /\
    table_correct 24 h1 t24 /\
    table_correct 32 h1 t32)
