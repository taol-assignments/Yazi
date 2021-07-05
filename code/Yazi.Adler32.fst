module Yazi.Adler32
module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
module Math = FStar.Math.Lemmas
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module UInt = FStar.UInt

open FStar.Mul
open FStar.Seq
open Lib.UInt
open LowStar.BufferOps
open Spec.Adler32

[@ CMacro ]
let base64 = 65521UL
let base_64_correct (_: unit): Lemma (ensures U64.v base64 == base) = ()

[@ CMacro ]
let nmax32 = 268961027ul
let nmax32_correct (_: unit): Lemma (ensures U32.v nmax32 == nmax) = ()

#set-options "--fuel 0 --ifuel 0"
private noeq type do_init_state = {
  dlen: nat;
  data: input dlen;
  blen: nat;
  base: B.buffer U8.t;
}

private noeq type do_state = {
  clen: Ghost.erased nat;
  consumed: Ghost.erased (input clen);
  slen: U32.t;
  stream: B.buffer U8.t;
  a: U64.t;
  b: U64.t;
}

let sum_a_state (#n #m: nat) (data: input n) (consumed: input m) (a: U64.t) =
 U64.v a == (sum_a data % base) + sum_seq consumed

let sum_b_state (#n #m: nat) (data: input n) (consumed: input m) (b: U64.t) =
 U64.v b == (sum_b data % base) + m * (sum_a data % base) + sum_b' consumed

unfold let do_pre_cond (h: HS.mem) (d: do_init_state) (s: do_state) (steps: nat) =
  B.live h d.base /\ B.length d.base == d.blen /\

  s.clen + U32.v s.slen == d.blen /\ s.clen + steps <= nmax /\
  Seq.equal (B.as_seq h d.base) (s.consumed @| (B.as_seq h s.stream)) /\
  U32.v s.slen >= steps /\ B.live h s.stream /\ B.length s.stream == U32.v s.slen /\
  sum_a_state d.data s.consumed s.a /\
  sum_b_state d.data s.consumed s.b

unfold let do_post_cond
  (h0 h1: HS.mem)
  (d: do_init_state)
  (s: do_state)
  (res: do_state)
  (steps: nat) =
  let sa = sum_a d.data % base in
  do_pre_cond h0 d s steps /\
  B.(modifies loc_none h0 h1) /\
  Ghost.reveal res.clen == Seq.length res.consumed /\
  res.clen + U32.v res.slen == d.blen /\
  Seq.equal res.consumed (s.consumed @| (slice (B.as_seq h1 s.stream) 0 steps)) /\
  Seq.equal (B.as_seq h1 d.base) (res.consumed @| (B.as_seq h1 res.stream)) /\
  (U32.v res.slen == 0 ==> Seq.equal res.consumed (B.as_seq h1 d.base)) /\
  
  B.live h1 res.stream /\ B.length res.stream == U32.v res.slen /\
  Seq.equal (slice (B.as_seq h1 s.stream) steps (U32.v s.slen)) (B.as_seq h1 res.stream) /\
  sum_a_state d.data res.consumed res.a /\
  sum_b_state d.data res.consumed res.b

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let sum_a_state_mod
  (#m1 #m2: nat)
  (data: input m1)
  (consumed: input m2)
  (a: U64.t{sum_a_state data consumed a}): Lemma
  (ensures U64.v a % base == (sum_a #(m1 + m2) (data @| consumed)) % base) =
  calc (==) {
    U64.v a % base;
    =={}
    ((sum_a data % base) + sum_seq consumed) % base;
    =={Math.lemma_mod_plus_distr_l (sum_a data) (sum_seq consumed) base}
    (sum_a data + sum_seq consumed) % base;
    =={sum_a_append data consumed}
    (sum_a #(m1 + m2) (data @| consumed)) % base;
  }

let sum_b_state_mod
  (#m1 #m2: nat)
  (data: input m1)
  (consumed: input m2)
  (b: U64.t{sum_b_state data consumed b}): Lemma
  (ensures U64.v b % base == (sum_b #(m1 + m2) (data @| consumed)) % base) =
  let sa = sum_a data % base in
  calc (==) {
    U64.v b % base;
    =={}
    ((sum_b data % base) + sum_b' consumed + m2 * sa) % base;
    =={Math.paren_add_right (sum_b data % base) (sum_b' consumed) (m2 * sa)}
    ((sum_b data % base) + (sum_b' consumed + m2 * sa)) % base;
    =={Math.lemma_mod_add_distr (sum_b' consumed + m2 * sa) (sum_b data) base}
    (sum_b data + sum_b' consumed + m2 * sa) % base;
    =={Math.lemma_mod_add_distr (sum_b data + sum_b' consumed) (m2 * sa) base}
    (sum_b data + sum_b' consumed + ((m2 * sa) % base)) % base;
    =={Math.lemma_mod_mul_distr_r m2 (sum_a data) base}
    (sum_b data + sum_b' consumed + ((m2 * sum_a data) % base)) % base;
    =={Math.lemma_mod_add_distr (sum_b data + sum_b' consumed) (m2 * sum_a data) base}
    (sum_b data + sum_b' consumed + m2 * sum_a data) % base;
    =={sum_b_append data consumed}
    (sum_b #(m1 + m2) (data @| consumed)) % base;
  }

inline_for_extraction
let do1
  (d: Ghost.erased do_init_state)
  (s: do_state):
  ST.Stack do_state
  (requires fun h -> do_pre_cond h d s 1)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res 1) =
  let open U64 in
  let sa = Ghost.hide (sum_a d.data % base) in
  let byte = s.stream.(0ul) in
  let byte' = Cast.uint8_to_uint64 byte in
  let consumed' = Ghost.hide (snoc s.consumed byte) in

  sum_a_seq_u64_upper_bound #_ #(s.clen + 1) d.data consumed';
  let a' = s.a +^ byte' in
  calc (==) {
    v a';
    =={}
    v s.a + v byte';
    =={
      cast_zero_prefix (U8.v byte) 64;
      zero_prefix_eq (v byte') (U8.v byte)
    }
    v s.a + U8.v byte;
    =={}
    sa + sum_seq s.consumed + U8.v byte;
    =={sum_seq_append_byte s.consumed byte}
    sa + sum_seq #(s.clen + 1) consumed';
  };

  calc (==) {
    v s.b + v a';
    =={}
    (sum_b d.data % base) + s.clen * sa + sum_b' s.consumed +
    sa + sum_seq #(s.clen + 1) (snoc s.consumed byte);
    =={}
    (sum_b d.data % base) + (s.clen + 1) * sa +
    sum_b' s.consumed + sum_seq #(s.clen + 1) (snoc s.consumed byte);
    =={sum_b'_sum_seq s.consumed byte}
    (sum_b d.data % base) + (s.clen + 1) * sa + sum_b' #(s.clen + 1) (snoc s.consumed byte);
    =={}
    (sum_b d.data % base) + (s.clen + 1) * sa + sum_b' #(s.clen + 1) consumed';
  };
  sum_b'_u64_uppser_bound #_ #(s.clen + 1) d.data consumed';
  let b' = s.b +^ a' in
  {
    clen = s.clen + 1;
    consumed = consumed';
    slen = U32.sub s.slen 1ul;
    stream = B.sub s.stream 1ul (U32.sub s.slen 1ul);
    a = a';
    b = b';
  }

[@ CInline ]
inline_for_extraction
let rec iteration_1 (d: Ghost.erased do_init_state) (s: do_state): ST.Stack do_state
  (requires fun h -> do_pre_cond h d s (U32.v s.slen) /\ d.blen <= nmax)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res (d.blen - s.clen)) =
  let open U32 in
  if s.slen >^ 1ul then
    let s' = do1 d s in
    iteration_1 d s'
  else if s.slen = 1ul then
    do1 d s
  else
    s

[@ CInline ]
inline_for_extraction
let rec iteration_1_remaining (d: Ghost.erased do_init_state) (s: do_state): ST.Stack do_state
  (requires fun h -> do_pre_cond h d s (U32.v s.slen % 16) /\ d.blen <= nmax)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res (U32.v s.slen % 16)) =
  let open U32 in
  if s.slen %^ 16ul >^ 0ul then
    let s' = do1 d s in
    iteration_1_remaining d s'
  else
    s

inline_for_extraction
let do2
  (d: Ghost.erased do_init_state)
  (s: do_state):
  ST.Stack do_state
  (requires fun h -> do_pre_cond h d s 2)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res 2) =
  let s' = do1 d s in
  do1 d s'

inline_for_extraction
let do4
  (d: Ghost.erased do_init_state)
  (s: do_state):
  ST.Stack do_state
  (requires fun h -> do_pre_cond h d s 4)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res 4) =
  let s' = do2 d s in
  do2 d s'

inline_for_extraction
let do8
  (d: Ghost.erased do_init_state)
  (s: do_state):
  ST.Stack do_state
  (requires fun h -> do_pre_cond h d s 8)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res 8) =
  let s' = do4 d s in
  do4 d s'

inline_for_extraction
let do16
  (d: Ghost.erased do_init_state)
  (s: do_state):
  ST.Stack do_state
  (requires fun h -> do_pre_cond h d s 16)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res 16) =
  let s' = do8 d s in
  do8 d s'

[@ CInline ]
inline_for_extraction
let rec iteration_16 (d: Ghost.erased do_init_state) (s: do_state): ST.Stack do_state
  (requires fun h ->
    do_pre_cond h d s (U32.v s.slen) /\ U32.v s.slen % 16 == 0 /\ d.blen <= nmax)
  (ensures fun h0 res h1 -> do_post_cond h0 h1 d s res (d.blen - s.clen)) =
  let open U32 in
  if s.slen >^ 16ul then
    let s' = do16 d s in
    iteration_16 d s'
  else if s.slen = 16ul then
    do16 d s
  else
    s

inline_for_extraction
let extract_sums
  (#m: Ghost.erased nat)
  (s: Ghost.erased (input m))
  (adler: U32.t{adler32_matched s adler}):
  Tot (adler32_pair s) =
  let open U32 in
  let a = adler &^ 0xfffful in
  let sa: Ghost.erased (UInt.uint_t 16) = Ghost.hide ((sum_a s) % base) in
  zero_prefix_eq (v a) sa;
  
  let b = adler >>^ 16ul in
  let sb: Ghost.erased (UInt.uint_t 16) = Ghost.hide ((sum_b s) % base) in
  zero_prefix_eq (v b) sb;
  (Cast.uint32_to_uint64 a, Cast.uint32_to_uint64 b)

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0 --z3seed 13"
inline_for_extraction
let combine_sums
  (#m1 #m2: Ghost.erased nat)
  (data: Ghost.erased (input m1))
  (consumed: Ghost.erased (input m2))
  (a: U64.t{sum_a_state data consumed a})
  (b: U64.t{sum_b_state data consumed b}):
  Tot (res: U32.t{adler32_matched #(m1 + m2) (data @| consumed) res}) =
  let open U64 in
  let a' = Cast.uint64_to_uint16 (a %^ base64) in
  let a'' = Cast.uint16_to_uint32 a' in
  sum_a_state_mod data consumed a;
  cast_zero_prefix (U16.v a') 32;

  let b' = Cast.uint64_to_uint16 (b %^ base64) in
  let b'' = Cast.uint16_to_uint32 b' in
  sum_b_state_mod data consumed b;
  cast_zero_prefix (U16.v b') 32;
  U32.logxor (U32.shift_left b'' 16ul) a''

inline_for_extraction unfold let init_state'
  (#m: Ghost.erased nat)
  (data: Ghost.erased (input m))
  (a': U64.t{sum_a_state #_ #0 data (Seq.empty #U8.t) a'})
  (b': U64.t{sum_b_state #_ #0 data (Seq.empty #U8.t) b'})
  (len: U32.t)
  (buf: B.buffer U8.t{B.length buf == U32.v len}):
  Tot ((Ghost.erased do_init_state) & do_state) =
  (Ghost.hide ({
    dlen = m;
    data = data;
    blen = U32.v len;
    base = buf;
  }), {
    clen = 0;
    consumed = Seq.empty #U8.t;
    slen = len;
    stream = buf;
    a = a';
    b = b';
  })
  
inline_for_extraction unfold let init_state
  (#m: Ghost.erased nat)
  (data: Ghost.erased (input m))
  (adler: U32.t{adler32_matched data adler})
  (len: U32.t)
  (buf: B.buffer U8.t{B.length buf == U32.v len}):
  Tot ((Ghost.erased do_init_state) & do_state) =
  let (a', b') = extract_sums data adler in
  init_state' data a' b' len buf

[@ CInline ]
inline_for_extraction
let rec do_iteration_nmax
  (#m1 #m2: Ghost.erased nat)
  (data: Ghost.erased (input m1))
  (consumed: Ghost.erased (input m2))
  (base_len: Ghost.erased nat{base_len >= nmax})
  (base_buf: Ghost.erased (B.buffer U8.t){B.length base_buf == Ghost.reveal base_len})
  (buf: B.buffer U8.t)
  (r: U32.t)
  (a b: U64.t):
  ST.Stack (U64.t & U64.t & (B.buffer U8.t) & U32.t & (Ghost.erased (Seq.seq U8.t)))
  (requires fun h ->
    let r' = U32.v r in
    let base_buf' = B.as_seq h base_buf in
    let remaining = B.as_seq h buf in
    B.live h base_buf /\ B.live h buf /\
    B.length buf == r' /\ r' <= base_len /\ r' >= nmax /\
    Seq.equal consumed (slice base_buf' 0 (base_len - r')) /\
    Seq.equal (consumed @| remaining) base_buf' /\
    (sum_a #(m1 + base_len - r') (data @| consumed)) % base == U64.v a /\
    (sum_b #(m1 + base_len - r') (data @| consumed)) % base == U64.v b)
  (ensures fun h0 res h1 ->
    let (a', b', buf', r', consumed') = res in
    let r'' = U32.v r' in
    let base_buf' = B.as_seq h1 base_buf in
    let remaining = B.as_seq h1 buf' in
    B.(modifies loc_none h0 h1) /\
    r'' < nmax /\ r'' == B.length buf' /\ B.live h1 buf' /\
    Seq.equal consumed' (slice base_buf' 0 (base_len - r'')) /\
    Seq.equal (consumed' @| remaining) base_buf' /\
    (sum_a #(m1 + base_len - r'') (data @| consumed')) % base == U64.v a' /\
    (sum_b #(m1 + base_len - r'') (data @| consumed')) % base == U64.v b') =
  let open U32 in
  let left = B.sub buf 0ul nmax32 in
  let r' = r -^ nmax32 in
  let right = B.sub buf nmax32 r' in
  let (d, s) = init_state' #(m1 + m2) (data @| consumed) a b nmax32 left in
  let s0 = iteration_1_remaining d s in
  let s1 = iteration_16 d s0 in
  let a' = U64.rem s1.a base64 in
  calc (==) {
    U64.v a';
    =={}
    U64.v s1.a % base;
    =={sum_a_state_mod #(m1 + m2) #nmax (data @| consumed) s1.consumed s1.a}
    (sum_a #(m1 + m2 + nmax) ((data @| consumed) @| s1.consumed)) % base;
    =={append_assoc data consumed s1.consumed}
    (sum_a #(m1 + m2 + nmax) (data @| (consumed @| s1.consumed))) % base;
    =={}
    (sum_a #(m1 + base_len - U32.v r') (data @| (consumed @| s1.consumed))) % base;
  };
  let b' = U64.rem s1.b base64 in
  calc (==) {
    U64.v b';
    =={}
    U64.v s1.b % base;
    =={sum_b_state_mod #(m1 + m2) #nmax (data @| consumed) s1.consumed s1.b}
    (sum_b #(m1 + m2 + nmax) ((data @| consumed) @| s1.consumed)) % base;
    =={append_assoc data consumed s1.consumed}
    (sum_b #(m1 + m2 + nmax) (data @| (consumed @| s1.consumed))) % base;
    =={}
    (sum_b #(m1 + base_len - U32.v r') (data @| (consumed @| s1.consumed))) % base;
  };
  if r' <^ nmax32 then
    (a', b', right, r', (Ghost.hide (consumed @| s1.consumed)))
  else
    do_iteration_nmax #_ #(m2 + nmax)
      data (consumed @| s1.consumed)
      (base_len) (base_buf)
      right r'
      a' b'

[@ CInline ]
inline_for_extraction
let iteration_nmax
  (#m: Ghost.erased nat)
  (data: Ghost.erased (input m))
  (base: Ghost.erased (B.buffer U8.t))
  (adler: U32.t{adler32_matched data adler})
  (buf: B.buffer U8.t)
  (len: U32.t):
  ST.Stack (U32.t & (Ghost.erased (Seq.seq U8.t)))
  (requires fun h ->
    B.live h buf /\ B.length buf == U32.v len /\ U32.v len >= nmax)
  (ensures fun h0 res h1 ->
    let (adler', consumed) = res in
    B.(modifies loc_none h0 h1) /\
    Seq.equal consumed (data @| (B.as_seq h1 buf)) /\
    adler32_matched #(m + U32.v len) (data @| (B.as_seq h1 buf)) adler') =
  let open U32 in
  append_empty_r data;
  let (a, b) = extract_sums data adler in
  let (a', b', buf', r', consumed) = do_iteration_nmax #_ #0
    data (Seq.empty #U8.t)
    (U32.v len) buf buf len
    a b
  in
  let (d, s) = init_state'
    #(m + v len - v r') (data @| consumed)
    a' b'
    r' buf'
  in
  let s' = iteration_1_remaining d s in
  let s'' = iteration_16 d s' in
  (combine_sums d.data s''.consumed s''.a s''.b, Ghost.hide (d.data @| s''.consumed))

let adler32 #m data adler buf len =
  let open U32 in
  if len = 1ul then
    let (d, s) = init_state data adler len buf in
    let s' = do1 d s in
    combine_sums data s'.consumed s'.a s'.b
  else if len = 0ul then
    adler
  else if len <^ 16ul then
    let (d, s) = init_state data adler len buf in
    let s' = iteration_1 d s in
    combine_sums data s'.consumed s'.a s'.b
  else if len <=^ nmax32 then
    let (d, s) = init_state data adler len buf in
    let s' = iteration_1_remaining d s in
    let s'' = iteration_16 d s' in
    combine_sums data s''.consumed s''.a s''.b
  else
    let (adler', _) = iteration_nmax data buf adler buf len in
    adler'

let adler32_combine64 #m1 #m2 s1 s2 adler1 adler2 len2 =
  let open U64 in
  let (a1, b1) = extract_sums s1 adler1 in
  let (a2, b2) = extract_sums s2 adler2 in
  let a3 = (a1 +^ a2 +^ base64 -^ 1UL) %^ base64 in
  calc (==) {
    v a3;
    =={}
    (v a1 + v a2 + base - 1) % base;
    =={}
    ((base - 1) + (sum_a s1 % base) + (sum_a s2 % base)) % base;
    =={Math.lemma_mod_add_distr ((base - 1) + (sum_a s1 % base)) (sum_a s2) base}
    ((base - 1) + (sum_a s1 % base) + sum_a s2) % base;
    =={Math.lemma_mod_add_distr ((base - 1) + sum_a s2) (sum_a s1) base}
    (base - 1 + sum_a s1 + sum_a s2) % base;
    =={Math.add_div_mod_1 (sum_a s1 + sum_a s2 - 1) base}
    (sum_a s1 + sum_a s2 - 1) % base;
    =={}
    (sum_a s1 + sum_seq s2) % base;
    =={sum_a_append s1 s2}
    sum_a #(m1 + m2) (s1 @| s2) % base;
  };
  let len2' = len2 %^ base64 in
  calc (<) {
    v b1 + v len2' * v a1 + v b2 + base;
    =={}
    (sum_b s1 % base) + (m2 % base) * (sum_a s1 % base) + (sum_b s2 % base) + base;
    <{Math.modulo_range_lemma (sum_b s1) base}
    2 * base + (m2 % base) * (sum_a s1 % base) + (sum_b s2 % base);
    <{Math.modulo_range_lemma (sum_b s2) base}
    3 * base + (m2 % base) * (sum_a s1 % base);
    <{
      Math.modulo_range_lemma m2 base;
      Math.modulo_range_lemma (sum_a s1) base;
      Math.lemma_mult_lt_sqr (m2 % base) (sum_a s1 % base) base
    }
    3 * base + base * base;
    <{}
    UInt.max_int 64;
  };
  let b3 = (b1 +^ len2' *^ a1 +^ b2 +^ base64 -^ len2') %^ base64 in
  calc (==) {
    v b3;
    =={}
    (v b1 + (v len2 % base) * v a1 + v b2 + base - (v len2 % base)) % base;
    =={}
    ((sum_b s1 % base) + (m2 % base) * (sum_a s1 % base) +
    (sum_b s2 % base) + base - (m2 % base)) % base;
    =={
      Math.lemma_mod_add_distr
        ((m2 % base) * (sum_a s1 % base) + (sum_b s2 % base) + base - (m2 % base))
        (sum_b s1)
        base
    }
    (sum_b s1 + (m2 % base) * (sum_a s1 % base) +
    (sum_b s2 % base) + base - (m2 % base)) % base;
    =={
      Math.lemma_mod_add_distr
        ((m2 % base) * (sum_a s1 % base) + sum_b s1 + base - (m2 % base))
        (sum_b s2)
        base
    }
    (sum_b s1 + (m2 % base) * (sum_a s1 % base) + sum_b s2 + base - (m2 % base)) % base;
    =={
      Math.lemma_mod_sub_distr 
        (sum_b s1 + (m2 % base) * (sum_a s1 % base) + sum_b s2 + base)
        m2
        base
    }
    (sum_b s1 + sum_b s2 + base - m2 + (m2 % base) * (sum_a s1 % base)) % base;
    =={
      Math.lemma_mod_add_distr
        (sum_b s1 + sum_b s2 + base - m2)
        ((m2 % base) * (sum_a s1 % base))
        base
    }
    (sum_b s1 + sum_b s2 + base - m2 + (((m2 % base) * (sum_a s1 % base)) % base)) % base;
    =={
      Math.lemma_mod_mul_distr_l m2 (sum_a s1 % base) base;
      Math.lemma_mod_mul_distr_r m2 (sum_a s1) base
    }
    (sum_b s1 + sum_b s2 + base - m2 + ((m2 * sum_a s1) % base)) % base;
    =={
      Math.lemma_mod_add_distr
        (sum_b s1 + sum_b s2 + base - m2)
        (m2 * sum_a s1)
        base
    }
    (sum_b s1 + sum_b s2 + base - m2 + m2 * sum_a s1) % base;
    =={}
    ((sum_b s1 + sum_b s2 - m2 + m2 * sum_a s1) + base) % base;
    =={Math.add_div_mod_1 (sum_b s1 + sum_b s2 - m2 + m2 * sum_a s1) base}
    (sum_b s1 + sum_b s2 - m2 + m2 * sum_a s1) % base;
    =={sum_b_append s1 s2}
    sum_b #(m1 + m2) (s1 @| s2) % base;
  };
  let a' = Cast.uint64_to_uint16 a3 in
  let a'' = Cast.uint16_to_uint32 a' in
  cast_zero_prefix (U16.v a') 32;

  let b' = Cast.uint64_to_uint16 b3 in
  let b'' = Cast.uint16_to_uint32 b' in
  cast_zero_prefix (U16.v b') 32;
  U32.logxor (U32.shift_left b'' 16ul) a''
