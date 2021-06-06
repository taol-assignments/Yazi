module Spec.State

module Adler32 = Spec.Adler32
module B = LowStar.Buffer
module CFlags = Yazi.CFlags
module CRC32 = Spec.CRC32
module HS = FStar.HyperStack
module I32 = FStar.Int32
module Seq = FStar.Seq
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open Lib.Seq

type stream_state = s:Seq.seq U32.t{Seq.length s == 5}

unfold let avail_in (s: stream_state) = U32.v s.[0]
unfold let total_in (s: stream_state) = U32.v s.[1]
unfold let avail_out (s: stream_state) = U32.v s.[2]
unfold let total_out (s: stream_state) = U32.v s.[3]
unfold let adler (s: stream_state) = s.[4]

unfold let next_in_valid
  (h: HS.mem)
  (s: B.lbuffer U32.t 5)
  (next_in: B.pointer (B.buffer U8.t)) =
  let next_in' = B.get h next_in 0 in
  B.frameOf next_in == B.frameOf s /\
  B.frameOf next_in' == B.frameOf s /\
  B.live h next_in /\ B.live h next_in' /\
  B.disjoint next_in s /\ B.disjoint next_in' s /\ B.disjoint next_in next_in' /\
  B.length next_in' == avail_in (B.as_seq h s)

unfold let next_out_valid
  (h: HS.mem)
  (s: B.lbuffer U32.t 5)
  (next_out: B.pointer (B.buffer U8.t)) =
  let next_out' = B.get h next_out 0 in
  B.frameOf next_out == B.frameOf s /\
  B.frameOf next_out' == B.frameOf s /\
  B.live h next_out /\ B.live h next_out' /\
  B.disjoint next_out s /\ B.disjoint next_out' s /\ B.disjoint next_out next_out' /\
  B.length next_out' == avail_out (B.as_seq h s)

unfold let adler_valid
  (h: HS.mem)
  (s: B.lbuffer U32.t 5)
  (wrap: I32.t)
  (uncompressed: Seq.seq U8.t) =
  let s' = B.as_seq h s in
  let len = Seq.length uncompressed in
  (I32.v wrap == 1 ==>
    Adler32.adler32_matched #len uncompressed (adler s')) /\
  ((CFlags.gzip == true /\ I32.v wrap == 2) ==>
    CRC32.crc32_matched len uncompressed (adler s') true)

let stream_valid
  (h: HS.mem)
  (s: B.lbuffer U32.t 5)
  (next_in: B.pointer (B.buffer U8.t))
  (next_out: B.pointer (B.buffer U8.t))
  (wrap: I32.t)
  (uncompressed: Seq.seq U8.t) =
  let s' = B.as_seq h s in
  let len = Seq.length uncompressed in
  let next_out' = B.get h next_out 0 in
  let next_in' = B.get h next_in 0 in
  B.live h s /\
  B.disjoint next_in next_out /\
  B.disjoint next_in next_out' /\
  B.disjoint next_in' next_out /\
  B.disjoint next_in' next_out' /\

  next_in_valid h s next_in /\ next_out_valid h s next_out /\
  adler_valid h s wrap uncompressed
