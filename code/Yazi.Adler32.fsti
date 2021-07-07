module Yazi.Adler32
module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module Cast = FStar.Int.Cast
module Spec = Spec.Adler32
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.Buffer

[@ (CPrologue "uint32_t adler32_z(uint32_t adler, const unsigned char *buf, size_t len);")]
val adler32:
    #m: Ghost.erased nat
  -> data: Ghost.erased (Spec.input m)
  -> adler: U32.t
  -> buf: CB.const_buffer U8.t
  -> len: U32.t
  -> ST.Stack U32.t
  (requires fun h ->
    CB.live h buf /\ CB.length buf == U32.v len /\ Spec.adler32_matched data adler)
  (ensures fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    Spec.adler32_matched #(m + U32.v len) (Seq.append data (CB.as_seq h1 buf)) res)

val adler32_combine64:
    #m1: Ghost.erased nat
  -> #m2: Ghost.erased nat
  -> s1: Ghost.erased (Spec.input m1)
  -> s2: Ghost.erased (Spec.input m2)
  -> adler1: U32.t{Spec.adler32_matched s1 adler1}
  -> adler2: U32.t{Spec.adler32_matched s2 adler2}
  -> len2: U64.t{U64.v len2 == Ghost.reveal m2}
  -> Tot (res: U32.t{Spec.adler32_matched #(m1 + m2) (Seq.append s1 s2) res})

inline_for_extraction
let adler32_combine
  (#m1 #m2: Ghost.erased nat)
  (s1: Ghost.erased (Spec.input m1))
  (s2: Ghost.erased (Spec.input m2))
  (adler1: U32.t{Spec.adler32_matched s1 adler1})
  (adler2: U32.t{Spec.adler32_matched s2 adler2})
  (len2: U32.t{U32.v len2 == Ghost.reveal m2}) =
  adler32_combine64 s1 s2 adler1 adler2 (Cast.uint32_to_uint64 len2)
