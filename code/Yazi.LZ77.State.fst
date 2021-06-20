module Yazi.LZ77.State

module B = LowStar.Buffer
module LB = Lib.Buffer
module S = Spec.LZ77
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32

open FStar.Mul
open LowStar.BufferOps

type lz77_state = B.lbuffer U32.t 8

inline_for_extraction
let set_match_start
  (bits: Ghost.erased S.window_bits)
  (w_size: Ghost.erased (S.window_size bits))
  (state: lz77_state)
  (match_start: U32.t{U32.v match_start < 2 * w_size}):
  ST.Stack unit
  (ensures fun h -> B.live h state)
  (requires fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.match_start (B.as_seq h1 state) == U32.v match_start /\
    LB.unchange_except h0 h1 state 2) =
  state.(2ul) <- match_start

inline_for_extraction
let get_match_start (state: lz77_state):
  ST.Stack U32.t
  (ensures fun h -> B.live h state)
  (requires fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.match_start (B.as_seq h0 state) == U32.v res) =
  state.(2ul)

inline_for_extraction
let set_strstart
  (bits: Ghost.erased S.window_bits)
  (w_size: Ghost.erased (S.window_size bits))
  (state: lz77_state)
  (strstart: U32.t{U32.v strstart < 2 * w_size}):
  ST.Stack unit
  (ensures fun h -> B.live h state)
  (requires fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.strstart (B.as_seq h1 state) == U32.v strstart /\
    LB.unchange_except h0 h1 state 5) =
  state.(5ul) <- strstart

inline_for_extraction
let get_strstart (state: lz77_state):
  ST.Stack U32.t
  (ensures fun h -> B.live h state)
  (requires fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.strstart (B.as_seq h0 state) == U32.v res) =
  state.(5ul)

inline_for_extraction
let get_lookahead (state: lz77_state):
  ST.Stack U32.t
  (ensures fun h -> B.live h state)
  (requires fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.lookahead (B.as_seq h0 state) == U32.v res) =
  state.(6ul)

inline_for_extraction
let get_insert (state: lz77_state):
  ST.Stack U32.t
  (ensures fun h -> B.live h state)
  (requires fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.insert (B.as_seq h0 state) == U32.v res) =
  state.(7ul)
