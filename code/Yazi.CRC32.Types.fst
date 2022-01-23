module Yazi.CRC32.Types

module B = LowStar.Buffer
module CB = LowStar.ConstBuffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module UInt = FStar.UInt

open Lib.Seq

type matrix_buf = B.lbuffer U32.t 32

type table_buf = buf: CB.const_buffer U32.t{CB.length buf == 256}

type crc32_data_dword (a b c d: U8.t) = res: U32.t{
  let a' = UInt.to_vec (U8.v a) in
  let b' = UInt.to_vec (U8.v b) in
  let c' = UInt.to_vec (U8.v c) in
  let d' = UInt.to_vec (U8.v d) in
  let r' = UInt.to_vec (U32.v res) in
  forall (i: nat{i < 32}). {:pattern r'.[i]}
    (i >= 24 ==> r'.[i] == a'.[i - 24]) /\
    (16 <= i /\ i < 24 ==> r'.[i] == b'.[i - 16]) /\
    (8 <= i /\ i < 16 ==> r'.[i] == c'.[i - 8]) /\
    (i < 8 ==> r'.[i] == d'.[i])
}
