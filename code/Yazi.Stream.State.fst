module Yazi.Stream.State

module B = LowStar.Buffer
module LB = Lib.Buffer
module S = Spec.Stream
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32

open LowStar.BufferOps
open Yazi.Stream.Types

inline_for_extraction
let get_avail_in (s: stream_state_t): ST.Stack U32.t
  (requires fun h -> B.live h s)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\ U32.v res == S.avail_in (B.as_seq h0 s)) =
  s.(0ul)

inline_for_extraction
let set_avail_in (s: stream_state_t) (a: U32.t): ST.Stack unit
  (requires fun h -> B.live h s)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer s) h0 h1 /\
    U32.v a == S.avail_in (B.as_seq h1 s) /\
    LB.unchange_except h0 h1 s 0) =
  s.(0ul) <- a

inline_for_extraction
let get_total_in (s: stream_state_t): ST.Stack U32.t
  (requires fun h -> B.live h s)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\ U32.v res == S.total_in (B.as_seq h0 s)) =
  s.(1ul)

inline_for_extraction
let set_total_in (s: stream_state_t) (a: U32.t): ST.Stack unit
  (requires fun h -> B.live h s)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer s) h0 h1 /\
    U32.v a == S.total_in (B.as_seq h1 s) /\
    LB.unchange_except h0 h1 s 1) =
  s.(1ul) <- a

inline_for_extraction
let get_adler (s: stream_state_t): ST.Stack U32.t
  (requires fun h -> B.live h s)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\ U32.v res == U32.v (S.adler (B.as_seq h0 s))) =
  s.(4ul)

inline_for_extraction
let set_adler (s: stream_state_t) (a: U32.t): ST.Stack unit
  (requires fun h -> B.live h s)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer s) h0 h1 /\
    U32.v a == U32.v (S.adler (B.as_seq h1 s)) /\
    LB.unchange_except h0 h1 s 4) =
  s.(4ul) <- a
