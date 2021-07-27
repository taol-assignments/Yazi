module Yazi.LZ77

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module I32 = FStar.Int32
module S = Spec.LZ77
module SST = Yazi.Stream.Types
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

include Yazi.LZ77.Types

val init_input_hash: ctx: lz77_context_p -> state: lz77_state_t ->
  ST.Stack unit
  (requires fun h -> S.init_input_hash_pre h ctx state)
  (ensures fun h0 _ h1 -> S.init_input_hash_post h0 h1 ctx state)

val slide_hash: ctx: lz77_context_p -> state: lz77_state_t -> ST.Stack unit
  (requires fun h ->
    S.state_valid h ctx state /\
    S.hash_chain_valid h ctx state false)
  (ensures fun h0 _ h1 ->
    B.modifies (S.hash_loc_buffer h0 ctx) h0 h1 /\
    S.hash_chain_valid h1 ctx state true)

val fill_window:
    ss: SST.stream_state_t
  -> ctx: lz77_context_p
  -> ls: lz77_state_t
  -> next_in: SST.input_buffer
  -> wrap: SST.wrap_t
  -> block_start: B.pointer I32.t
  -> block_data: Ghost.erased (Seq.seq U8.t)
  -> ST.Stack (Ghost.erased (Seq.seq U8.t))
  (requires fun h -> S.fill_window_pre h ss ctx ls next_in wrap block_start block_data)
  (ensures fun h0 res h1 ->
     S.fill_window_post h0 res h1 ss ctx ls next_in wrap block_start (Ghost.reveal block_data))

val longest_match: ctx: lz77_context_p -> s: lz77_state_t -> cur_match: U32.t ->
  ST.Stack U32.t
  (requires fun h -> S.longest_match_pre h ctx s cur_match)
  (ensures fun h0 len h1 -> S.longest_match_post h0 len h1 ctx s cur_match)
