module Yazi.LZ77

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module S = Spec.LZ77
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32

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
