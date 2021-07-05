module Yazi.LZ77.Match

module B = LowStar.Buffer
module Cast = FStar.Int.Cast
module CB = LowStar.ConstBuffer
module CFlags = Yazi.CFlags
module I32 = FStar.Int32
module S = Spec.LZ77
module ST = FStar.HyperStack.ST
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module UInt = FStar.UInt

open LowStar.BufferOps
open Lib.Seq
open Yazi.LZ77.Types
open Yazi.LZ77.State

assume val do:
     len: nat
  -> s: B.buffer U8.t
  -> m: B.buffer U8.t
  -> i: U32.t
  -> ST.Stack U32.t
  (requires fun h -> S.ctz_compare_pre h len s m i)
  (ensures fun h0 res h1 -> S.ctz_compare_post h0 res h1 len s m i)

let rec do1 (s m: B.buffer U8.t) (i tail: U32.t):
  ST.Stack U32.t
  (requires fun h -> S.string_compare_ite_pre h s m i tail /\ U32.v tail < 4)
  (ensures fun h0 len h1 -> S.string_compare_ite_post h0 len h1 s m i tail) =
  let open U32 in
  if i <^ tail then
    if s.(i) = m.(i) then
      do1 s m (i +^ 1ul) tail
    else
      i
  else
    i

let rec do8 (s m: B.buffer U8.t) (i tail: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    S.string_compare_ite_pre h s m i tail /\
    (U32.v tail - U32.v i) % 8 == 0)
  (ensures fun h0 len h1 -> S.string_compare_ite_post h0 len h1 s m i tail)
  (decreases (U32.v tail - U32.v i)) =
  let open U32 in
  if U32.lt i tail then begin
    let len = do 8 s m i in
    if len = 8ul then
      do8 s m (i +^ len) tail
    else
      i +^ len
  end else
    i

#set-options "--z3rlimit 1024 --fuel 0 --ifuel 0"
let match_iteration (s m: B.buffer U8.t) (tail: U32.t):
  ST.Stack U32.t
  (requires fun h ->
    B.live h s /\ B.live h m /\
    B.length s <= B.length m /\
    U32.v tail <= B.length s /\
    U32.v tail <= S.max_match)
  (ensures fun h0 len h1 ->
    let s' = B.as_seq h0 s in
    let m' = B.as_seq h0 m in
    let len' = U32.v len in
    let tail' = U32.v tail in
    B.modifies B.loc_none h0 h1 /\
    len' <= tail' /\
    (forall (j: nat{j < len'}). s'.[j] == m'.[j])) =
  let open U32 in
  let r1 = tail %^ 4ul in
  let l1 = if r1 = 0ul then 0ul else do1 s m 0ul r1 in
  let t4 = tail -^ r1 in
  if l1 = r1 && t4 >^ 0ul then begin
    let r4 = t4 %^ 8ul in
    let l4 = l1 +^ (if r4 = 0ul then 0ul else do 4 s m l1) in
    let t8 = t4 -^ r4 in

    if l4 = l1 +^ 4ul && t8 >^ 0ul then begin
      do8 s m l4 tail
    end else begin
      l4
    end
  end else
    l1

assume val fast_compare: 
    s1: B.buffer U8.t
  -> s2: B.buffer U8.t
  -> len: U32.t
  -> ST.Stack I32.t
  (requires fun h ->
    B.live h s1 /\ B.live h s2 /\
    B.length s1 >= U32.v len /\ B.length s2 >= U32.v len)
  (ensures fun h0 res h1 ->
    let s1' = B.as_seq h0 s1 in
    let s2' = B.as_seq h0 s2 in
    B.modifies B.loc_none h0 h1 /\
    (I32.v res == 0 <==> (forall (i: nat{i < U32.v len}). s1'.[i] == s2'.[i])))

[@ CMacro ]
let min_match = 4ul

[@ CInline ]
#set-options "--z3rlimit 4096 --fuel 0 --ifuel 0"
let rec search_hash_chain
  (ctx: lz77_context_p)
  (s: lz77_state_t)
  (scan_end: U32.t)
  (limit chain_length i: U32.t):
  ST.Stack (option U32.t)
  (requires fun h ->
    let open U32 in
    let ctx' = B.get h (CB.as_mbuf ctx) 0 in
    let s' = B.as_seq h s in
    let scan_end' = v scan_end + S.min_match in
    CFlags.fastest == false /\
    S.match_ready h ctx s /\
    scan_end' <= B.length ctx'.window /\
    S.strstart s' <= v scan_end /\
    (S.strstart s' >= v ctx'.w_size ==> v limit == S.strstart s' - v ctx'.w_size) /\
    (S.strstart s' < v ctx'.w_size ==> v limit == 0) /\
    v chain_length >= 1 /\
    0 < v i /\ v i < S.strstart s')
  (ensures fun h0 res h1 ->
    let open U32 in
    let s' = B.as_seq h1 s in
    let w = B.as_seq h1 (B.get h1 (CB.as_mbuf ctx) 0).window in
    let strstart = S.strstart s' in
    B.modifies B.loc_none h0 h1 /\
    (match res with
     | Some j ->
         v j < strstart /\
         (forall (k: nat{k < S.min_match}). w.[v j + k] == w.[strstart + k])
     | None -> True)) =
  let open U32 in
  let h0 = Ghost.hide (ST.get ()) in
  let ctx' = Ghost.hide (B.get h0 (CB.as_mbuf ctx) 0) in
  let window = (CB.index ctx 0ul).window in
  let strstart = get_strstart s in
  let s1 = B.sub window strstart min_match in
  let s2 = B.sub window i min_match in
  let e1 = B.sub window scan_end min_match in
  let e2 = B.sub window (scan_end -^ strstart +^ i) min_match in
  let c1 = fast_compare s1 s2 min_match in
  let c2 = fast_compare e1 e2 min_match in
  if c1 = 0l && c2 = 0l then begin
    let w = Ghost.hide (B.as_seq h0 window) in
    let d = Ghost.hide (v strstart - v i) in
    let s1' = Ghost.hide (B.as_seq h0 (B.gsub window strstart min_match)) in
    let s2' = Ghost.hide (B.as_seq h0 (B.gsub window i min_match)) in
    let strstart' = Ghost.hide (U32.v strstart) in
    assert(forall (j: nat{j < S.min_match}).
      s1'.[j] == s2'.[j] /\
      s1'.[j] == w.[strstart' + j] /\
      s2'.[j] == w.[v i + j] /\
      w.[strstart' + j] == w.[v i + j]);
    Some i
  end else if chain_length >^ 1ul then begin
    let prev = (CB.index ctx 0ul).prev in
    let w_mask = (CB.index ctx 0ul).w_mask in
    [@inline_let] let w_mask' = Cast.uint16_to_uint32 w_mask in
    UInt.logand_mask #32 (v i) (U16.v ctx'.w_bits);
    let i' = prev.(i &^ w_mask') in
    let i'' = Cast.uint16_to_uint32 i' in
    if i'' >^ limit then
      search_hash_chain ctx s scan_end limit (chain_length -^ 1ul) i''
    else
      None
  end else
    None
