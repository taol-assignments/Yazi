module Yazi.LZ77

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module HS = FStar.HyperStack
module I32 = FStar.Int32
module S = Spec.LZ77
module SS = Spec.Stream
module Seq = FStar.Seq
module ST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module U8 = FStar.UInt8

include Yazi.LZ77.Types

private unfold let hash_range_pre_cond (ctx: lz77_context) (h_range: U32.t) =
  let open FStar.Mul in
  U32.v ctx.w_size < U32.v h_range /\ U32.v h_range <= 2 * U32.v ctx.w_size
  
val slide_hash:
    ctx: lz77_context_p
  -> h_range: U32.t
  -> ST.Stack unit
  (requires fun h ->
    S.context_valid h ctx /\
    (let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    (ctx'.w_size == h_range \/ hash_range_pre_cond ctx' h_range) /\
    S.hash_chain_valid h ctx h_range false))
  (ensures fun h0 _ h1 ->
    let ctx' = B.get h0 (CB.as_mbuf ctx) 0 in
    B.modifies (
      (B.loc_buffer ctx'.head) `B.loc_union`
      (if CFlags.fastest then B.loc_none else B.loc_buffer ctx'.prev)) h0 h1 /\
    S.hash_chain_valid h1 ctx h_range true)
