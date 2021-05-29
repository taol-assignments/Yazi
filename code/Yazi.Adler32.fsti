module Yazi.Adler32
module B = LowStar.Buffer
module Spec = Spec.Adler32
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module Seq = FStar.Seq
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

let empty_seq_aux (#a: Type) (h: HS.mem) (buf: B.buffer a) (s: Seq.seq a): Lemma
  (requires B.length buf == 0)
  (ensures Seq.append s (B.as_seq h buf) == s)
  [SMTPat (Seq.append s (B.as_seq h buf))] =
  assert(Seq.length (B.as_seq h buf) == 0);
  Seq.lemma_empty (B.as_seq h buf);
  Seq.append_empty_r s

[@ (CPrologue "uint32_t adler32_z(uint32_t adler, const unsigned char *buf, size_t len);")]
val adler32:
    #m: Ghost.erased nat
  -> data: Ghost.erased (Spec.input m)
  -> adler: U32.t
  -> buf: B.buffer U8.t
  -> len: U32.t
  -> ST.Stack U32.t
  (requires fun h -> B.live h buf /\ B.length buf == U32.v len /\ Spec.adler32_matched data adler)
  (ensures fun h0 res h1 ->
    B.(modifies loc_none h0 h1) /\
    Spec.adler32_matched #(m + U32.v len) (Seq.append data (B.as_seq h1 buf)) res)
