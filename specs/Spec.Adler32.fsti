module Spec.Adler32

module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open FStar.Mul

let base = 65521

let nmax = 268961027

type input (m: nat) = s: Seq.seq U8.t{Seq.length s == m}

let rec sum_seq (#m: nat) (s: input m): Tot nat =
  if m > 0 then U8.v (Seq.head s) + sum_seq #(m - 1) (Seq.tail s) else 0

let sum_a (#m: nat) (s: input m): Tot (res: nat{res >= 1}) = 1 + sum_seq s

let sum_a_upper_bound (n: nat): Tot nat = 255 * n + 1

val sum_a_upper_bound_aux: #n: nat -> s: input n -> Lemma
  (ensures sum_a s <= sum_a_upper_bound n)
  [SMTPat (sum_a s)]

val sum_seq_append_byte: #m: nat -> s: input m -> b: U8.t ->
  Lemma (ensures sum_seq s + U8.v b == sum_seq #(m + 1) (Seq.snoc s b))

let sum_seq_upper_bound (m: nat): Tot nat = m * 255

let rec sum_seq_upper_bound_aux (#m: nat) (s: input m): Lemma
  (ensures sum_seq s <= sum_seq_upper_bound m)
  [SMTPat (sum_seq s)] =
  match m with
  | 0 -> ()
  | _ -> sum_seq_upper_bound_aux #(m - 1) (Seq.tail s)

let sum_a_seq_u64_upper_bound
  (#m: nat)
  (#n: nat{n <= UInt.max_int 32})
  (s: input m)
  (c: input n): Lemma
  (ensures (sum_a s % base) + sum_seq c <= UInt.max_int 64) = ()

val sum_a_append: #m1: nat -> #m2: nat -> s1: input m1 -> s2: input m2 ->
  Lemma (ensures sum_a #(m1 + m2) (Seq.append s1 s2) == sum_a s1 + sum_seq s2)

let rec sum_b' (#m: nat) (s: input m): Tot nat =
  let open FStar.Mul in
  if m = 0 then 0 else m * (U8.v (Seq.head s)) + sum_b' #(m - 1) (Seq.tail s)

let sum_b (#m: nat) (s: input m) = sum_b' s + m

val sum_b_append: #m1: nat -> #m2: nat -> s1: input m1 -> s2: input m2 -> Lemma
  (ensures sum_b #(m1 + m2) (Seq.append s1 s2) == sum_b s1 + m2 * sum_a s1 + sum_b' s2)

let sum_b_upper_bound (n: nat): Tot nat =
  n * (n + 1) * 255 / 2 + n

val sum_b_upper_bound_aux: #n: nat -> s: input n -> Lemma
  (ensures sum_b #n s <= sum_b_upper_bound n)
  [SMTPat (sum_b s)]

let sum_b'_upper_bound_aux (#n: nat) (s: input n): Lemma
  (ensures sum_b' s <= (sum_b_upper_bound n) - n)
  [SMTPat (sum_b' s)] =
  assert(sum_b' s == (sum_b s) - n)

val sum_b'_sum_seq:
    #m: nat
  -> s: input m
  -> byte: U8.t
  -> Lemma
  (ensures sum_b' s + sum_seq #(m + 1) (Seq.snoc s byte) == sum_b' #(m + 1) (Seq.snoc s byte))

#set-options "--z3rlimit 512 --fuel 0"
val sum_b'_u64_uppser_bound:
    #n: nat
  -> #m: nat{m <= nmax}
  -> s: input n
  -> c: input m
  -> Lemma (ensures (sum_b s % base) + m * (sum_a s % base) + sum_b' c <= UInt.max_int 64)

let adler32_matched (#m: nat) (s: input m) (a: U32.t) =
  let open U32 in
  let sa: UInt.uint_t 16 = sum_a s % base in
  let sb: UInt.uint_t 16 = sum_b s % base in
  forall (i: nat{i < 32}). {:pattern UInt.nth (v a) i}
    (16 <= i /\ i < 32 ==> UInt.nth (v a) i == UInt.nth sa (i - 16)) /\
    (i < 16 ==> UInt.nth (v a) i == UInt.nth sb i)
