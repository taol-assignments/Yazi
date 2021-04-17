module Yazi.Deflate

module B = LowStar.Buffer
module Flags = Yazi.CFlags
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Util = Yazi.Util

open FStar.Int.Cast
open LowStar.BufferOps
open Spec.Deflate.Params
open Spec.Deflate.State
open Yazi.Deflate.Constants
open Yazi.Huffman
open Yazi.Types

inline_for_extraction
val set_level: (level: I32.t) -> Tot (l:I32.t{
  let open I32 in
  (CFlags.fastest == true ==> v l = 1 \/ v l = 0) /\
  (CFlags.fastest == false /\ v level = v Util.z_default_compression ==> v l = 6)
})

let set_level level =
  if CFlags.fastest then
    if level <> 0l then 1l else level
  else if level = Util.z_default_compression then
    6l
  else
    level

inline_for_extraction
val verify_level: (level: I32.t) -> Tot (valid:bool{
  valid <==> level_valid level
})

let verify_level level =
  let open I32 in
  level >=^ 0l && level <=^ Util.z_best_compression

let verify_window_bits_input wb =
  let open I32 in
  if wb >=^ 8l +^ 16l && wb <=^ 15l +^ 16l then
    CFlags.gzip
  else
    wb >=^ 8l && wb <=^ 15l ||
    wb <=^ -8l && wb >=^ -15l

inline_for_extraction
val set_window_bits: (iwb: I32.t)
  -> Tot (p: (bool * I32.t * I32.t){
    let (valid, wb, wrap) = p in
    valid <==> window_bits_wrap_valid iwb wb wrap
  })

let set_window_bits wb =
  let open I32 in
  (* suppress zlib wrapper *)
  if -15l <=^ wb && wb <^ -8l then
    (true, 0l -^ wb, 0l)
  (* wrap with zlib header and tailor *)
  else if 8l <=^ wb && wb <=^ 15l then
    (true, wb, 1l)
  else if CFlags.gzip then
    (* write gzip wrapper instead *)
    if 8l +^ 16l <^ wb && wb <=^ 15l +^ 16l then
      (true, wb -^ 16l, 2l)
    else
      (false, 0l, 0l)
  else
    (false, 0l, 0l)

inline_for_extraction
val verify_mem_level: (level: I32.t) -> Tot (valid:bool{
  valid <==> mem_level_valid level
})

let verify_mem_level level =
  let open I32 in
  1l <=^ level && level <=^ 9l

inline_for_extraction
val verify_strategy: (strategy: I32.t) -> Tot (valid:bool{
  valid <==> strategy_valid strategy
})

let verify_strategy strategy =
  let open I32 in
  0l <=^ strategy && strategy <=^ Util.z_fixed
  
inline_for_extraction
val verify_params:
  (level: I32.t) ->
  (method: I32.t) ->
  (window_bits: I32.t) ->
  (mem_level: I32.t) ->
  (strategy: I32.t) ->
  Tot (option (result:(I32.t * window_bits_t * I32.t){
    let (level, wb, wrap) = result in
      level_valid level
      /\ method_valid method
      /\ window_bits_wrap_valid window_bits wb wrap
      /\ mem_level_valid mem_level
      /\ strategy_valid strategy
  }))

let verify_params level method window_bits mem_level strategy =
  let level = set_level level in
  let (wb_ok, wb, wrap) = set_window_bits window_bits in
  if not (verify_level level)
    || not (wb_ok)
    || not (verify_mem_level mem_level)
    || method <> Util.z_deflated
    || not (verify_strategy strategy) then
    None
  else
    Some (level, wb, wrap)

noextract
val shift_left_pow2:
  n: int ->
  Lemma (requires 0 < n /\ n < 32)
  (ensures (
    U32.v (U32.shift_left 1ul (U32.uint_to_t n)) == pow2 n
  ))

let shift_left_pow2 n =
  FStar.UInt.shift_left_value_aux_3 (U32.v 1ul) n;
  FStar.Math.Lemmas.pow2_lt_compat 32 n

inline_for_extraction
val window_size: wb: window_bits_t -> U32.t

let window_size wb =
  let open U32 in
  let n = int32_to_uint32 wb in
  1ul <<^ n

noextract
val window_size_lemma:
  window_bits: window_bits_t ->
  Lemma (requires True)
  (ensures (
    let open U32 in
    U32.v (window_size window_bits) == pow2 (I32.v window_bits)
  ))
  [SMTPat (window_size window_bits)]

let window_size_lemma wb = shift_left_pow2 (I32.v wb)

inline_for_extraction
let window_mask (window_bits: window_bits_t) =
  let open U32 in
  (window_size window_bits) -^ 1ul

inline_for_extraction
let hash_bits (mem_level: mem_level_t) =
  let open U32 in
  (int32_to_uint32 mem_level) +^ 7ul

noextract
val hash_bits_i32_lemma:
  mem_level: mem_level_t ->
  Lemma (requires True)
  (ensures (U32.v (hash_bits mem_level) == I32.v (I32.add mem_level 7l)))
  [SMTPat (hash_bits mem_level)]

let hash_bits_i32_lemma mem_level = ()

inline_for_extraction
let hash_size (mem_level: mem_level_t) =
  let open U32 in
  1ul <<^ hash_bits mem_level

noextract
val hash_size_lemma:
  mem_level: mem_level_t ->
  Lemma (requires True)
  (ensures (U32.v (hash_size mem_level) == pow2 (U32.v (hash_bits mem_level))))
  [SMTPat (hash_size mem_level)]

let hash_size_lemma mem_level =
  shift_left_pow2 (U32.v (hash_bits mem_level))

inline_for_extraction
let hash_mask (mem_level: mem_level_t) =
  let open U32 in (hash_size mem_level) -^ 1ul

inline_for_extraction
let hash_shift (mem_level: mem_level_t) =
  let bits = hash_bits mem_level in
  let open U32 in
  ((hash_bits mem_level) +^ min_match -^ 1ul) /^ min_match

inline_for_extraction
let lit_bufsize (mem_level: mem_level_t) =
  let open U32 in
  1ul <<^ ((int32_to_uint32 mem_level) +^ 6ul)

noextract
val lit_bufsize_lemma:
  mem_level: mem_level_t ->
  Lemma (requires True)
  (ensures (
    U32.v (lit_bufsize mem_level) == pow2 (I32.v (I32.add mem_level 6l))
  )) [SMTPat (lit_bufsize mem_level)]

#set-options "--z3rlimit 30"
let lit_bufsize_lemma mem_level =
  shift_left_pow2 (I32.v (I32.add mem_level 6l))
#reset-options

#set-options "--z3rlimit 60"
inline_for_extraction
val pending_buf_size: mem_level: mem_level_t -> s: U32.t{U32.v s <= pow2 17}
let pending_buf_size (mem_level: mem_level_t) =
  let open U32 in
  assert_norm(U32.v (lit_bufsize mem_level) == pow2 (I32.v (I32.add mem_level 6l)));
  FStar.Math.Lemmas.pow2_plus (I32.v (I32.add mem_level 6l)) 2;
  (lit_bufsize mem_level) *^ 4ul
#reset-options

inline_for_extraction  
let zmalloc (#a: Type) (init: a) (len: U32.t{U32.v len > 0}) =
  B.mmalloc_partial #a #(B.trivial_preorder a) HS.root init len

inline_for_extraction
val malloc_state_fields:
  state: Ghost.erased (B.pointer deflate_state) ->
  window_bits: window_bits_t ->
  mem_level: mem_level_t ->
  HST.ST (option (
    pending_buf: B.buffer U8.t{B.len pending_buf == pending_buf_size mem_level} *
    window: B.buffer U8.t{B.len window == U32.mul (window_size window_bits) 2ul} *
    prev: B.buffer U16.t{B.len prev == window_size window_bits} *
    head: B.buffer U16.t {B.len head == hash_size mem_level} *
    dyn_ltree_t *
    dyn_dtree_t *
    bl_tree_t *
    bl_count_t *
    tree_heap_t *
    tree_depth_t *
    l_buf: B.buffer U8.t{B.len l_buf == lit_bufsize mem_level} *
    d_buf: B.buffer U16.t{B.len d_buf == lit_bufsize mem_level}))
  (requires fun h -> B.live h state)
  (ensures fun h0 fields h1 -> match fields with
   | None -> B.live h0 state /\ B.live h1 state
   | Some (pending_buf, window, prev, head,
       dyn_ltree, dyn_dtree, bl_tree, bl_count,
       tree_heap, tree_depth, l_buf, d_buf) ->
     let open FStar.Mul in
     let open U32 in
     B.live h0 state /\ B.live h1 state /\
     B.length pending_buf == v (pending_buf_size mem_level) /\
     B.length window == (v (window_size window_bits)) * 2 /\
     (* TODO: more *)
     B.disjoint pending_buf window /\ B.disjoint pending_buf prev /\
     B.disjoint pending_buf head /\ B.disjoint pending_buf dyn_ltree /\
     B.disjoint pending_buf dyn_dtree /\ B.disjoint pending_buf bl_tree /\
     B.disjoint pending_buf bl_count /\ B.disjoint pending_buf tree_heap /\
     B.disjoint pending_buf tree_depth /\ B.disjoint pending_buf l_buf /\
     B.disjoint pending_buf d_buf /\ B.disjoint window prev /\ B.disjoint window head /\
     B.disjoint window dyn_ltree /\ B.disjoint window dyn_dtree /\
     B.disjoint window bl_tree /\ B.disjoint window bl_count /\
     B.disjoint window tree_heap /\ B.disjoint window tree_depth /\
     B.disjoint window l_buf /\ B.disjoint window d_buf /\ B.disjoint prev head /\
     B.disjoint prev dyn_ltree /\ B.disjoint prev dyn_dtree /\ B.disjoint prev bl_tree /\
     B.disjoint prev bl_count /\ B.disjoint prev tree_heap /\ B.disjoint prev tree_depth /\
     B.disjoint prev l_buf /\ B.disjoint prev d_buf /\ B.disjoint head dyn_ltree /\
     B.disjoint head dyn_dtree /\ B.disjoint head bl_tree /\ B.disjoint head bl_count /\
     B.disjoint head tree_heap /\ B.disjoint head tree_depth /\ B.disjoint head l_buf /\
     B.disjoint head d_buf /\ B.disjoint dyn_ltree dyn_dtree /\
     B.disjoint dyn_ltree bl_tree /\ B.disjoint dyn_ltree bl_count /\
     B.disjoint dyn_ltree tree_heap /\ B.disjoint dyn_ltree tree_depth /\
     B.disjoint dyn_ltree l_buf /\ B.disjoint dyn_ltree d_buf /\
     B.disjoint dyn_dtree bl_tree /\ B.disjoint dyn_dtree bl_count /\
     B.disjoint dyn_dtree tree_heap /\ B.disjoint dyn_dtree tree_depth /\
     B.disjoint dyn_dtree l_buf /\ B.disjoint dyn_dtree d_buf /\
     B.disjoint bl_tree bl_count /\ B.disjoint bl_tree tree_heap /\
     B.disjoint bl_tree tree_depth /\ B.disjoint bl_tree l_buf /\ B.disjoint bl_tree d_buf /\
     B.disjoint bl_count tree_heap /\ B.disjoint bl_count tree_depth /\
     B.disjoint bl_count l_buf /\ B.disjoint bl_count d_buf /\
     B.disjoint tree_heap tree_depth /\ B.disjoint tree_heap l_buf /\
     B.disjoint tree_heap d_buf /\ B.disjoint tree_depth l_buf /\
     B.disjoint tree_depth d_buf /\ B.disjoint l_buf d_buf)

#set-options "--z3rlimit 100"
[@inline_let]
let malloc_state_fields _ window_bits mem_level =
  let open U32 in

  (* Uint 8 buffer *)
  let pd_size = pending_buf_size mem_level in
  let win_size = (window_size window_bits) *^ 2ul in
  let ld_buf_size = lit_bufsize mem_level in
  let tree_heap_size = 2ul *^ l_codes +^ 1ul in

  assert_norm(v win_size <= pow2 16);
  assert_norm(v ld_buf_size == pow2 (I32.v (I32.add mem_level 6l)));
  assert_norm(v ld_buf_size <= pow2 15);

  let u8_buf = zmalloc 0uy (pd_size +^ win_size +^ ld_buf_size +^ tree_heap_size) in
  if B.is_null u8_buf then None else

  let pending_buf = B.sub u8_buf 0ul pd_size in
  let window = B.sub u8_buf pd_size win_size in
  let l_buf = B.sub u8_buf (pd_size +^ win_size) ld_buf_size in
  let tree_depth = B.sub u8_buf (pd_size +^ win_size +^ ld_buf_size) tree_heap_size in

  (* Huffman trees *)
  let ltree_size = heap_size in
  let dtree_size = 2ul *^ d_codes +^ 1ul in
  let bl_tree_size = 2ul *^ bl_codes +^ 1ul in
  
  let trees = zmalloc ({
    freq_or_dad = 0us;
    code_or_len = 0us;
  }) (ltree_size +^ dtree_size +^ bl_tree_size) in
  if B.is_null trees then begin
    B.free u8_buf;
    None
  end else

  let dyn_ltree = B.sub trees 0ul ltree_size in
  let dyn_dtree = B.sub trees ltree_size dtree_size in
  let bl_tree = B.sub trees (ltree_size +^ dtree_size) bl_tree_size in
  (* Initialize the dynamic tree *)
  dyn_ltree.(end_block) <- {
    freq_or_dad = 1us;
    code_or_len = 0us;
  };

  (* Uint 16 buffer *)
  let bl_count_size = max_bits +^ 1ul in
  let prev_size = window_size window_bits in
  let head_size = hash_size mem_level in

  assert_norm(v prev_size <= pow2 15);
  assert_norm(v head_size == pow2 (I32.v (I32.add mem_level 7l)));
  assert_norm(v head_size <= pow2 16);
  
  let u16_buf = zmalloc 0us (bl_count_size +^ ld_buf_size +^ prev_size +^ head_size) in
  if B.is_null u16_buf then begin
    B.free u8_buf;
    B.free trees;
    None
  end else

  let bl_count = B.sub u16_buf 0ul bl_count_size in
  let d_buf = B.sub u16_buf bl_count_size ld_buf_size in
  let prev = B.sub u16_buf (bl_count_size +^ ld_buf_size) prev_size in
  let head = B.sub u16_buf (bl_count_size +^ ld_buf_size +^ prev_size) head_size in

  (* Tree heap *)
  let tree_heap = zmalloc 0ul tree_heap_size in
  if B.is_null tree_heap then begin
    B.free u8_buf;
    B.free trees;
    B.free u16_buf;
    None
  end else
  
  Some (pending_buf, window, prev, head,
    dyn_ltree, dyn_dtree, bl_tree, bl_count,
    tree_heap, tree_depth, l_buf, d_buf)

let deflate_init state level method window_bits mem_level strategy =
  match verify_params level method window_bits mem_level strategy with
  | None -> Util.z_stream_error
  | Some (level, window_bits, wrap) ->
    match malloc_state_fields state window_bits mem_level with
    | None -> Util.z_mem_error
    | Some (
        pending_buf, window, prev, head,
        dyn_ltree, dyn_dtree, bl_tree, bl_count,
        tree_heap, tree_depth, l_buf, d_buf) ->
      state *= {
	status = if CFlags.gzip then
            if wrap = 2l then
              gzip_state
            else if wrap = 1l then
              init_state
            else
              busy_state
          else if wrap = 1l then
            init_state
          else
            busy_state;
	pending_buf = pending_buf;
	pending_buf_size = pending_buf_size mem_level;
	pending_out = pending_buf;
	pending = 0ul;
	wrap = wrap;

	gzhead = B.null;
	gzindex = 0ul;
	last_flush = Util.z_no_flush;

	w_size = window_size window_bits;
	w_bits = int32_to_uint32 window_bits;
	w_mask = window_mask window_bits;

	window = window;
	window_size = 0ul;

	prev = prev;
	head = head;

	ins_h = 0ul;

	hash_size = hash_size mem_level;
	hash_bits = hash_bits mem_level;
	hash_mask = hash_mask mem_level;
	hash_shift = hash_shift mem_level;

	block_start = 0L;

	match_length = 0ul;
	prev_match = 0ul;
	match_available = 0l;
	strstart = 0ul;
	match_start = 0ul;
	lookahead = 0ul;

	prev_length = 0ul;

	max_chain_length = 0ul;
	max_lazy_length = 0ul;

	level = level;
	strategy = strategy;

	good_match = 0ul;
	nice_match = 0l;

	dyn_ltree = dyn_ltree;
	dyn_dtree = dyn_dtree;
	bl_tree = bl_tree;

	l_desc = {
          dyn_tree = dyn_ltree;
          stat_desc = static_l_desc;
          max_code = 0l;
        };
	d_desc = {
          dyn_tree = dyn_dtree;
          stat_desc = static_d_desc;
          max_code = 0l;
        };
	bl_desc = {
          dyn_tree = bl_tree;
          stat_desc = static_bl_desc;
          max_code = 0l;
        };

	bl_count = bl_count;

	heap = tree_heap;
	heap_len = 0ul;
	heap_max = 0ul;

	depth = tree_depth;
	l_buf = l_buf;

	lit_bufsize = lit_bufsize mem_level;
	last_list = 0ul;

	d_buf = d_buf;

	opt_len = 0ul;
	static_len = 0ul;
	matches = 0ul;
	insert = 0ul;

	bi_buf = 0us;
	bi_valid = 0ul;

	high_water = 0ul;
      };
      Util.z_ok
#reset-options

assume val allocator_check:
  strm: B.pointer z_stream ->
  HST.Stack bool
  (requires fun h -> B.live h strm)
  (ensures fun h0 _ h1 -> HST.modifies_none h0 h1)

inline_for_extraction
val verify_status:
  status: I32.t ->
  Tot (ok: bool{ok <==> status_valid status})

let verify_status status =
  if status <> init_state &&
    status <> extra_state &&
    status <> name_state &&
    status <> comment_state &&
    status <> hcrc_state &&
    status <> busy_state &&
    status <> finish_state
  then
    if CFlags.gzip then
      if status <> gzip_state then false else true
    else
      false
  else
    true

val deflate_state_check:
  strm: B.pointer_or_null z_stream ->
  HST.Stack (v: I32.t{v == 0l \/ v == 1l})
  (requires fun h -> stream_and_state_live strm h)
  (ensures fun h0 result h1 ->
    let open FStar.Seq in
    HST.modifies_none h0 h1 /\
    (result == 0l ==> stream_check_valid strm h1 /\
      ~(B.g_is_null strm) /\
      ~(B.g_is_null (B.get h1 strm 0).state)) /\
    (~(stream_check_valid strm h1) ==> result == 1l))

let deflate_state_check strm =
  HST.push_frame ();
  let result = if B.is_null strm then
    1l
  else if allocator_check strm then
    1l
  else if B.is_null (!*strm).state then
    1l
  else let s = (!*(!*strm).state) in
    if verify_status s.status then 0l else 1l
  in
  HST.pop_frame ();
  result

let deflate_end strm =
  if 1l = deflate_state_check strm then
    Util.z_stream_error
  else begin
    let s = (!*(!*strm).state) in
    let status = s.status in
    B.free s.pending_buf;
    B.free s.dyn_ltree;
    B.free s.bl_count;
    B.free s.heap;
    B.free (!*strm).state;

    if status = busy_state then Util.z_data_error else Util.z_ok
  end
