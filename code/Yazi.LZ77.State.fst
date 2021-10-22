module Yazi.LZ77.State

module B = LowStar.Buffer
module LB = Lib.Buffer
module S = Spec.LZ77
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8

open FStar.Mul
open LowStar.BufferOps
open Yazi.LZ77.Types

inline_for_extraction
let get_match_length (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.match_length (B.as_seq h0 state) == U32.v res) =
  state.(0ul)

inline_for_extraction
let set_match_start
  (bits: Ghost.erased S.window_bits)
  (w_size: Ghost.erased (S.window_size bits))
  (state: lz77_state_t)
  (match_start: U32.t{U32.v match_start < 2 * w_size}):
  ST.Stack unit
  (requires fun h -> B.live h state)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.match_start (B.as_seq h1 state) == U32.v match_start /\
    LB.unchange_except h0 h1 state 1) =
  state.(1ul) <- match_start

inline_for_extraction
let get_match_start (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.match_start (B.as_seq h0 state) == U32.v res) =
  state.(1ul)

inline_for_extraction
let get_prev_match (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.prev_match (B.as_seq h0 state) == U32.v res) =
  state.(2ul)

inline_for_extraction
let get_prev_length (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.prev_length (B.as_seq h0 state) == U32.v res) =
  state.(3ul)

inline_for_extraction
let set_strstart
  (bits: Ghost.erased S.window_bits)
  (w_size: Ghost.erased (S.window_size bits))
  (state: lz77_state_t)
  (strstart: U32.t{U32.v strstart < 2 * w_size}):
  ST.Stack unit
  (requires fun h -> B.live h state)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.strstart (B.as_seq h1 state) == U32.v strstart /\
    LB.unchange_except h0 h1 state 4) =
  state.(4ul) <- strstart

inline_for_extraction
let get_strstart (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.strstart (B.as_seq h0 state) == U32.v res) =
  state.(4ul)

inline_for_extraction
let set_lookahead
  (bits: Ghost.erased S.window_bits)
  (w_size: Ghost.erased (S.window_size bits))
  (state: lz77_state_t)
  (lookahead: U32.t{U32.v lookahead <= 2 * w_size}):
  ST.Stack unit
  (requires fun h -> B.live h state)
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.lookahead (B.as_seq h1 state) == U32.v lookahead /\
    LB.unchange_except h0 h1 state 5) =
  state.(5ul) <- lookahead

inline_for_extraction
let get_lookahead (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.lookahead (B.as_seq h0 state) == U32.v res) =
  state.(5ul)

inline_for_extraction
let get_insert (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.insert (B.as_seq h0 state) == U32.v res) =
  state.(6ul)

inline_for_extraction
let set_insert (state: lz77_state_t) (insert: U32.t):
  ST.Stack unit
  (requires fun h ->
    B.live h state /\
    U32.v insert <= S.strstart (B.as_seq h state))
  (ensures fun h0 _ h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.insert (B.as_seq h1 state) == U32.v insert /\
    LB.unchange_except h0 h1 state 6) =
  state.(6ul) <- insert

inline_for_extraction
let decr_insert (state: lz77_state_t):
  ST.Stack unit
  (requires fun h -> B.live h state /\ S.insert (B.as_seq h state) > 0)
  (ensures fun h0 res h1 ->
    B.modifies (B.loc_buffer state) h0 h1 /\
    S.insert (B.as_seq h0 state) == S.insert (B.as_seq h1 state) + 1 /\
    LB.unchange_except h0 h1 state 6) =
  let open U32 in
  state.(6ul) <- state.(6ul) -^ 1ul

inline_for_extraction
let get_level (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.level (B.as_seq h0 state) == U32.v res) =
  state.(7ul)

inline_for_extraction
let get_strategy (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.strategy (B.as_seq h0 state) == U32.v res) =
  state.(8ul)

inline_for_extraction
let get_max_fuel (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.max_fuel (B.as_seq h0 state) == U32.v res) =
  state.(9ul)

inline_for_extraction
let get_max_lazy_macth (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.max_lazy_match (B.as_seq h0 state) == U32.v res) =
  state.(10ul)

inline_for_extraction
let get_good_match (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.good_match (B.as_seq h0 state) == U32.v res) =
  state.(11ul)

inline_for_extraction
let get_nice_match (state: lz77_state_t):
  ST.Stack U32.t
  (requires fun h -> B.live h state)
  (ensures fun h0 res h1 ->
    B.modifies B.loc_none h0 h1 /\
    S.nice_match (B.as_seq h0 state) == U32.v res) =
  state.(12ul)
