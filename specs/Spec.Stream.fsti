module Spec.Stream

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
open Yazi.Stream.Types

type stream_state = s:Seq.seq U32.t{Seq.length s == 5}

unfold let avail_in (s: stream_state) = U32.v s.[0]
unfold let total_in (s: stream_state) = U32.v s.[1]
unfold let avail_out (s: stream_state) = U32.v s.[2]
unfold let total_out (s: stream_state) = U32.v s.[3]
unfold let adler (s: stream_state) = s.[4]

unfold let avail_in_unchange (s0 s1: stream_state) = U32.v s0.[0] == U32.v s1.[0]
unfold let total_in_unchange (s0 s1: stream_state) = U32.v s0.[1] == U32.v s1.[1]
unfold let avail_out_unchange (s0 s1: stream_state) = U32.v s0.[2] == U32.v s1.[2]
unfold let total_out_unchange (s0 s1: stream_state) = U32.v s0.[3] == U32.v s1.[3]
unfold let adler_unchange (s0 s1: stream_state) = U32.v s0.[4] == U32.v s1.[4]

private let adler_valid
  (h: HS.mem)
  (s: stream_state_t)
  (wrap: wrap_t)
  (block_data: Seq.seq U8.t) =
  let s' = B.as_seq h s in
  let len = Seq.length block_data in
  (I32.v wrap == 1 ==>
    Adler32.adler32_matched #len block_data (adler s')) /\
  (I32.v wrap == 2 ==>
    CRC32.crc32_matched len block_data (adler s') true)

unfold let next_in_valid
  (h: HS.mem)
  (s: stream_state_t)
  (next_in: io_buffer) =
  let next_in' = B.get h next_in 0 in
  B.frameOf next_in == B.frameOf s /\
  B.frameOf next_in' == B.frameOf s /\
  B.live h next_in /\ B.live h next_in' /\
  B.disjoint next_in s /\ B.disjoint next_in' s /\ B.disjoint next_in next_in' /\
  B.length next_in' == avail_in (B.as_seq h s)

unfold let next_out_valid
  (h: HS.mem)
  (s: stream_state_t)
  (next_out: io_buffer) =
  let next_out' = B.get h next_out 0 in
  B.frameOf next_out == B.frameOf s /\
  B.frameOf next_out' == B.frameOf s /\
  B.live h next_out /\ B.live h next_out' /\
  B.disjoint next_out s /\ B.disjoint next_out' s /\ B.disjoint next_out next_out' /\
  B.length next_out' == avail_out (B.as_seq h s)

let istream_valid
  (h: HS.mem)
  (s: stream_state_t)
  (next_in: io_buffer)
  (wrap: wrap_t)
  (block_data: Seq.seq U8.t) =
  B.live h s /\ next_in_valid h s next_in /\ adler_valid h s wrap block_data
  
let ostream_valid
  (h: HS.mem)
  (s: stream_state_t)
  (next_out: B.pointer (B.buffer U8.t))
  (wrap: wrap_t)
  (block_data: Seq.seq U8.t) =
  B.live h s /\ next_out_valid h s next_out /\ adler_valid h s wrap block_data
  
let stream_valid
  (h: HS.mem)
  (s: stream_state_t)
  (next_in: B.pointer (B.buffer U8.t))
  (next_out: B.pointer (B.buffer U8.t))
  (wrap: wrap_t)
  (block_data: Seq.seq U8.t) =
  let next_out' = B.get h next_out 0 in
  let next_in' = B.get h next_in 0 in
  B.live h s /\
  B.disjoint next_in next_out /\
  B.disjoint next_in next_out' /\
  B.disjoint next_in' next_out /\
  B.disjoint next_in' next_out' /\

  next_in_valid h s next_in /\ next_out_valid h s next_out /\
  adler_valid h s wrap block_data

private unfold let read_buf_size(h: HS.mem) (s: stream_state_t) (size: U32.t) =
  let s' = B.as_seq h s in
  if U32.v size > avail_in s' then avail_in s' else U32.v size

unfold let read_buf_pre
  (h: HS.mem)
  (s: stream_state_t)
  (block_data: Seq.seq U8.t)
  (next_in: B.pointer (B.buffer U8.t))
  (buf: B.buffer U8.t)
  (size: U32.t)
  (wrap: wrap_t) =
  let len = read_buf_size h s size in
  len > 0 /\
  B.live h s /\ ~(B.g_is_null s) /\
  B.live h buf /\ ~(B.g_is_null buf) /\
  HS.disjoint (B.frameOf s) (B.frameOf buf) /\
  B.length buf == U32.v size /\
  next_in_valid h s next_in /\
  adler_valid h s wrap block_data

let read_buf_post
  (h0: HS.mem)
  (res: (U32.t & Ghost.erased (B.buffer U8.t)))
  (h1: HS.mem)
  (s: stream_state_t)
  (block_data: Seq.seq U8.t)
  (next_in: B.pointer (B.buffer U8.t))
  (buf: B.buffer U8.t)
  (size: U32.t)
  (wrap: wrap_t) =
  let (len', read) = res in
  let next_in0 = B.get h0 next_in 0 in
  let next_in1 = B.get h1 next_in 0 in
  let b1 = B.as_seq h1 buf in
  let s0 = B.as_seq h0 s in
  let s1 = B.as_seq h1 s in
  let len = read_buf_size h0 s size in
  read_buf_pre h0 s block_data next_in buf size wrap /\
  len == U32.v len' /\
  B.modifies (
    B.loc_buffer s `B.loc_union`
    B.loc_buffer next_in `B.loc_union`
    B.loc_buffer buf) h0 h1 /\
  U32.v len' <= B.length next_in0 /\
  Ghost.reveal read == B.gsub next_in0 0ul len' /\
  Seq.equal (B.as_seq h1 read) (B.as_seq h0 (B.gsub next_in0 0ul len')) /\
  Seq.equal (B.as_seq h1 read) (B.as_seq h1 (B.gsub buf 0ul len')) /\
  next_in1 == B.gsub next_in0 len' (U32.uint_to_t ((avail_in s0) - len)) /\
  avail_in s0 - len == avail_in s1 /\
  next_in_valid h1 s next_in /\
  adler_valid h1 s wrap (Seq.append block_data (B.as_seq h1 read)) /\
  avail_out_unchange s0 s1 /\ total_out_unchange s0 s1
