module Yazi.Deflate.Constants

open FStar.UInt32

[@CMacro]
let min_match = 3ul

[@CMacro]
let max_match = 258ul

[@CMacro]
let length_codes = 29ul
(* number of length codes, not counting the special END_BLOCK code *)

[@CMacro]
let literals  = 256ul
(* number of literal bytes 0..255 *)

[@CMacro]
let l_codes = 286ul (* literals +^ 1ul +^ length_codes *)
(* number of Literal or Length codes, including the END_BLOCK code *)

[@CMacro]
let d_codes   = 30ul
(* number of distance codes *)

[@CMacro]
let bl_codes  = 19ul
(* number of codes used to transfer the bit lengths *)

[@CMacro]
let heap_size = 573ul (* 2ul *^ l_codes +^ 1ul *)
(* maximum heap size *)

[@CMacro]
let max_bits = 15ul
(* All codes must not exceed MAX_BITS bits *)

[@CMacro]
let buf_size = 16ul
(* size of bit buffer in bi_buf *)

[@CMacro]
let init_state = 42l

[@CMacro]
let gzip_state = 57l     (* gzip header -> BUSY_STATE | EXTRA_STATE *)
[@CMacro]
let extra_state = 69l    (* gzip extra block -> NAME_STATE *)
[@CMacro]
let name_state = 73l     (* gzip file name -> COMMENT_STATE *)
[@CMacro]
let comment_state = 91l  (* gzip comment -> HCRC_STATE *)
[@CMacro]
let hcrc_state = 103l    (* gzip header CRC -> BUSY_STATE *)
[@CMacro]
let busy_state = 113l    (* deflate -> FINISH_STATE *)
[@CMacro]
let finish_state = 666l  (* stream complete *)
