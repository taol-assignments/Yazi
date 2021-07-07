module Yazi.Stream.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U8 = FStar.UInt8

type stream_state_t = B.lbuffer U32.t 5

type wrap_t = w: I32.t{
  let w' = I32.v w in
  w' == 0 \/ w' == 1 \/ (CFlags.gzip == true /\ w' == 2)
}

type input_buffer = B.pointer (CB.const_buffer U8.t)
type output_buffer = B.pointer (B.buffer U8.t)
