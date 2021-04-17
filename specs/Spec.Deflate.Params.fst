module Spec.Deflate.Params

module B = LowStar.Buffer
module I32 = FStar.Int32
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Util = Yazi.Util
module CFlags = Yazi.CFlags

let level_valid level =
  let open I32 in
  v level >= 0 /\ v level <= v Util.z_best_compression

let raw_format_wb wb = let open I32 in v wb < -8 /\ v wb >= -15

let zlib_wrap_wb wb = let open I32 in v wb >= 8 /\ v wb <= 15

let gzip_wrap_wb wb =
  let open I32 in
  CFlags.gzip /\ v wb > 8 + 16 /\ v wb <= 15 + 16

let window_bits_range wb =
  let open I32 in 8 <= v wb /\ v wb <= 15

let window_bits_result_valid iwb wb =
  let open I32 in
  raw_format_wb iwb /\ v wb == -(v iwb) \/
  zlib_wrap_wb iwb /\ v wb == v iwb \/
  gzip_wrap_wb iwb /\ v wb == v iwb - 16

let window_bits_wrap_valid iwb wb wrap =
  let open I32 in
  (raw_format_wb iwb /\ v wrap = 0 \/
  zlib_wrap_wb iwb /\ v wrap = 1 \/
  gzip_wrap_wb iwb /\ v wrap = 2) /\
  window_bits_result_valid iwb wb

let mem_level_valid level =
  let open I32 in
  1 <= v level /\ v level <= 9

let strategy_valid strategy =
  let open I32 in
  0 <= v strategy /\ v strategy <= v Util.z_fixed

let method_valid method = 
  let open I32 in
  v method == v Util.z_deflated
