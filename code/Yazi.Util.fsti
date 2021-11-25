module Yazi.Util

module U8 = FStar.UInt8

[@CMacro]
let z_no_flush = 0l
[@CMacro]
let z_partial_flush = 1l
[@CMacro]
let z_sync_flush    = 2l
[@CMacro]
let z_full_flush    = 3l
[@CMacro]
let z_finish        = 4l
[@CMacro]
let z_block         = 5l
[@CMacro]
let z_trees         = 6l
(* Allowed flush values; see deflate() and inflate() below for details *)

[@CMacro]
let z_ok            = 0l
[@CMacro]
let z_stream_end    = 1l
[@CMacro]
let z_need_dict     = 2l
[@CMacro]
let z_errno        = -1l
[@CMacro]
let z_stream_error = -2l
[@CMacro]
let z_data_error   = -3l
[@CMacro]
let z_mem_error    = -4l
[@CMacro]
let z_buf_error    = -5l
[@CMacro]
let z_version_error = -6l
(* Return codes for the compression/decompression functions. Negative values
 * are errors, positive values are used for special but normal events. *)

[@CMacro]
let z_no_compression         = 0l
[@CMacro]
let z_best_speed             = 1l
[@CMacro]
let z_best_compression       = 9l
[@CMacro]
let z_default_compression    = -1l
(* compression levels *)

[@CMacro]
let z_filtered            = 1l
[@CMacro]
let z_huffman_only        = 2l
[@CMacro]
let z_rle                 = 3l
[@CMacro]
let z_fixed               = 4l
[@CMacro]
let z_default_strategy    = 0l
(* compression strategy; see deflateInit2() below for details *)

[@CMacro]
let z_binary   = 0l
[@CMacro]
let z_text     = 1l
[@CMacro]
let z_ascii    = 1l   (* for compatibility with 1.2.2 and earlier *)
[@CMacro]
let z_unknown  = 2l
(* Possible values of the data_type field for deflate() *)

[@CMacro]
let z_deflated   = 8l
(* The deflate compression method (the only one supported in this version) *)

[@CMacro]
let z_null  = 0l  (* for initializing zalloc, zfree, opaque *)

[@ (CPrologue "#if 0") (CEpilogue "#endif")]
val is_little_endian: unit -> Tot U8.t
