module Lib.Buffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module Seq = FStar.Seq
module U32 = FStar.UInt32

open Lib.Seq

let append_empty_buf_r (#a: Type) (h: HS.mem) (buf: B.buffer a) (s: Seq.seq a): Lemma
  (requires B.length buf == 0)
  (ensures Seq.append s (B.as_seq h buf) == s)
  [SMTPat (Seq.append s (B.as_seq h buf))] =
  assert(Seq.length (B.as_seq h buf) == 0);
  Seq.lemma_empty (B.as_seq h buf);
  Seq.append_empty_r s

let unchange_except
  (#a: Type)
  (h0 h1: HS.mem)
  (buf: B.buffer a)
  (i: nat{i < B.length buf}) =
  let s0 = B.as_seq h0 buf in
  let s1 = B.as_seq h1 buf in
  forall (j: nat{j < B.length buf /\ j <> i}). Seq.index s0 j == Seq.index s1 j

let as_seq_gsub_eq
  (#a: Type)
  (h0 h1: HS.mem)
  (b0 b1: B.buffer a)
  (s0 s1 l l': U32.t): Lemma
  (requires
    U32.v s0 + U32.v l <= B.length b0 /\ U32.v s1 + U32.v l <= B.length b1 /\
    B.as_seq h0 (B.gsub b0 s0 l) == B.as_seq h1 (B.gsub b1 s1 l) /\
    U32.v l' <= U32.v l)
  (ensures
    B.as_seq h0 (B.gsub b0 s0 l') == B.as_seq h1 (B.gsub b1 s1 l') /\
    Seq.equal (B.as_seq h0 (B.gsub b0 s0 l')) (B.as_seq h1 (B.gsub b1 s1 l')) /\
    (forall (i: nat{i < U32.v l'}).
      (B.as_seq h0 (B.gsub b0 s0 l')).[i] == (B.as_seq h0 b0).[i + U32.v s0] /\
      (B.as_seq h1 (B.gsub b1 s1 l')).[i] == (B.as_seq h1 b1).[i + U32.v s1])) =
  let sq0 = B.as_seq h0 (B.gsub b0 s0 l) in
  let sq1 = B.as_seq h1 (B.gsub b1 s1 l) in
  let sq0' = Seq.slice (B.as_seq h0 b0) (U32.v s0) (U32.v l' + U32.v s0) in
  let sq1' = Seq.slice (B.as_seq h1 b1) (U32.v s1) (U32.v l' + U32.v s1) in
  assert(forall (i: nat{i < U32.v l'}).
    sq0.[i] == sq0'.[i] /\ sq1.[i] == sq1'.[i] /\ sq0.[i] == sq1.[i]);
  assert(Seq.equal sq0' sq1')
