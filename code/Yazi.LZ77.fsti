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

private unfold let hash_range_pre_cond (ctx: lz77_context) (h_range: U32.t) =
  let open FStar.Mul in
  U32.v ctx.w_size < U32.v h_range /\ U32.v h_range <= U32.v ctx.window_size - S.min_match + 1

val init_dict_hash: ctx: lz77_context_p -> state: lz77_state_t ->
  ST.Stack unit
  (requires fun h -> S.init_dict_hash_pre h ctx state)
  (ensures fun h0 _ h1 -> S.init_dict_hash_post h0 h1 ctx state)

val slide_hash: ctx: lz77_context_p -> h_range: U32.t -> ST.Stack unit
  (requires fun h ->
    let open FStar.Mul in
    S.context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    (U32.v ctx'.w_size == U32.v h_range \/ hash_range_pre_cond ctx' h_range) /\
    S.hash_chain_valid h ctx h_range false))
  (ensures fun h0 _ h1 ->
    B.modifies (S.hash_loc_buffer h0 ctx) h0 h1 /\
    S.hash_chain_valid h1 ctx h_range true)

val fill_window:
    ss: SST.stream_state_t
  -> ctx: lz77_context_p
  -> ls: lz77_state_t
  -> next_in: SST.io_buffer
  -> wrap: SST.wrap_t
  -> block_start: B.pointer I32.t
  -> block_data: Ghost.erased (Seq.seq U8.t)
  -> ST.Stack (Ghost.erased (Seq.seq U8.t))
  (requires fun h -> S.fill_window_pre h ss ctx ls next_in wrap block_start block_data)
  (ensures fun h0 res h1 ->
    S.fill_window_post h0 res h1 ss ctx ls next_in wrap block_start block_data)
