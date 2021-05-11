module Yazi.Deflate

module B = LowStar.Buffer
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module U8 = FStar.UInt8
module U32 = FStar.UInt32

open Yazi.Types
open Yazi.Deflate.Constants
open Spec.Deflate.Params
open Spec.Deflate.State
open FStar.Int.Cast

val deflate_init:
  strm: B.pointer z_stream ->
  state: B.pointer deflate_state ->
  level: I32.t ->
  method: I32.t ->
  window_bits: I32.t ->
  mem_level: I32.t ->
  strategy: I32.t ->
  HST.ST I32.t
  (requires fun h -> B.live h strm /\ B.live h state)
  (ensures fun h0 res h1 -> B.live h0 state /\ B.live h1 state /\
    B.live h0 strm /\ B.live h1 strm // /\
  (*res == Util.z_ok ==> begin
    let state = B.get h1 state 0 in
    let open U32 in
    let open FStar.Mul in
    state.status == init_state /\
    window_bits_wrap_valid window_bits (uint32_to_int32 state.w_bits) state.wrap /\
    state.gzhead == B.null /\
    v state.w_size == pow2 (v state.w_bits) /\
    level_valid state.level /\
    state.strategy = strategy /\
    method_valid method (* /\
    v state.pending_buf_size == (v state.lit_bufsize * 4) /\
    B.length state.pending_buf == v state.pending_buf_size /\
    B.length state.window == 4 * (v state.w_size) *)
  end*))

// private let reset_pre_cond h strm msg data_type =
//   stream_and_state_live strm h /\ B.live h msg /\ B.live h data_type

// private let reset_keep_post_cond h0 result h1 strm msg data_type =
//  stream_and_state_live strm h0 /\ B.live h0 msg /\ B.live h0 data_type /\
//  stream_and_state_live strm h1 /\ B.live h1 msg /\ B.live h1 data_type /\
//  (~(stream_check_valid strm h0) ==> result == Util.z_stream_error) /\
//  (result == Util.z_ok ==> stream_check_valid strm h0)

// val deflate_reset_keep:
//   strm: B.pointer_or_null z_stream ->
//   msg: B.pointer (B.buffer U8.t) ->
//   data_type: B.pointer data_type_t ->
//   HST.ST (result: I32.t{
//     result == Util.z_stream_error \/
//     result == Util.z_ok
//   })
//   (requires fun h -> stream_and_state_live strm h /\ B.live h msg /\ B.live h data_type)
//   (ensures fun h0 result h1 ->
//     stream_and_state_live strm h0 /\ B.live h0 msg /\ B.live h0 data_type /\
//     stream_and_state_live strm h1 /\ B.live h1 msg /\ B.live h1 data_type /\
//     (~(stream_check_valid strm h0) ==> result == Util.z_stream_error) /\
//     (result == Util.z_ok ==> stream_check_valid strm h0))

val deflate_end:
  strm: B.pointer_or_null z_stream ->
  HST.ST (result: I32.t {
    result == Util.z_ok \/
    result == Util.z_data_error \/
    result == Util.z_stream_error
  })
  (requires fun h -> stream_and_state_live strm h /\ (stream_check_valid strm h ==>
    begin
      let sp = (B.get h strm 0).state in
      let s = B.get h sp 0 in
      B.freeable s.pending_buf /\ B.live h s.pending_buf /\
      B.freeable s.dyn_ltree /\ B.live h s.dyn_ltree /\
      B.freeable s.bl_count /\ B.live h s.bl_count /\
      B.freeable s.heap /\ B.live h s.heap /\
      B.freeable sp /\ B.live h sp /\
      B.disjoint s.pending_buf s.dyn_ltree /\ B.disjoint s.pending_buf s.bl_count /\
      B.disjoint s.pending_buf s.heap /\ B.disjoint s.pending_buf strm /\
      B.disjoint s.pending_buf sp /\ B.disjoint s.dyn_ltree s.bl_count /\
      B.disjoint s.dyn_ltree s.heap /\ B.disjoint s.dyn_ltree strm /\
      B.disjoint s.dyn_ltree sp /\ B.disjoint s.bl_count s.heap /\
      B.disjoint s.bl_count strm /\ B.disjoint s.bl_count sp /\
      B.disjoint s.heap strm /\ B.disjoint s.heap sp /\ B.disjoint strm sp
    end))
  (ensures fun h0 result h1 ->
    (~(stream_check_valid strm h0) ==> result == Util.z_stream_error) /\
    (result == Util.z_data_error ==> (get_deflate_state h0 strm).status == busy_state) /\
    (result == Util.z_ok ==>
      (stream_check_valid strm h0) /\ (get_deflate_state h0 strm).status <> busy_state))
