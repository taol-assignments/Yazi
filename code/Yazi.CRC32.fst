module Yazi.CRC32

module B = LowStar.Buffer
module Spec = Spec.CRC32
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

// TODO: Generate tables with the lowstar immutable buffer library.
assume val crc32:
    data: Ghost.erased (Seq.seq U8.t)
  -> crc: U32.t
  -> buf: B.buffer U8.t
  -> len: U32.t
  -> ST.Stack U32.t
  (requires fun h ->
    B.live h buf /\ B.length buf == U32.v len /\
    Spec.crc32_matched (Seq.length data) data crc true)
  (ensures fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    Spec.crc32_matched
      (Seq.length data + U32.v len)
      (Seq.append data (B.as_seq h1 buf)) res true)
