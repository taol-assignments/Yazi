module Yazi.Stream.Types

module B = LowStar.Buffer
module U32 = FStar.UInt32

type stream_state_t = B.lbuffer U32.t 5
