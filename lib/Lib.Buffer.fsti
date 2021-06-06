module Lib.Buffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module Seq = FStar.Seq

let append_empty_buf_r (#a: Type) (h: HS.mem) (buf: B.buffer a) (s: Seq.seq a): Lemma
  (requires B.length buf == 0)
  (ensures Seq.append s (B.as_seq h buf) == s)
  [SMTPat (Seq.append s (B.as_seq h buf))] =
  assert(Seq.length (B.as_seq h buf) == 0);
  Seq.lemma_empty (B.as_seq h buf);
  Seq.append_empty_r s

