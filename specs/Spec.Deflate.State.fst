module Spec.Deflate.State

module B = LowStar.Buffer
module HS = FStar.HyperStack
module I32 = FStar.Int32

open Yazi.Types
open Yazi.Deflate.Constants
open Yazi.CFlags
open Spec.Deflate.Params
open LowStar.BufferOps

let status_valid (status: I32.t) =
  status == init_state \/
  (gzip /\ status == gzip_state) \/
  status == extra_state \/
  status == name_state \/
  status == comment_state \/
  status == hcrc_state \/
  status == busy_state \/
  status == finish_state

let stream_check_valid (strm: B.pointer_or_null z_stream) (h: HS.mem) =
  ~(B.g_is_null strm) /\ B.live h strm /\
  begin
    let sp = (B.get h strm 0).state in
    ~(B.g_is_null sp) /\ B.live h sp /\ status_valid (B.get h sp 0).status
  end

let stream_and_state_live (strm: B.pointer_or_null z_stream) (h: HS.mem) =
  B.live h strm /\ (~(B.g_is_null strm) ==> B.live h (B.get h strm 0).state)

let get_deflate_state (h: HS.mem) (strm: B.pointer z_stream{
  ~(B.g_is_null (B.get h strm 0).state)
}) =
  B.get h (B.get h strm 0).state 0
