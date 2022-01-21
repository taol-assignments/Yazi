module Lib.Seq

open FStar.Seq

unfold let op_String_Access #a = index #a

unfold let op_Array_Assignment (#a:Type) = upd #a

let unsnoc (#a: Type) (s: seq a{
  length s > 0
}): Tot (res: seq a{
  (length res == length s - 1) /\
  (forall (i: nat{i < length s - 1}).
    index s i == index res i)
}) =
  slice s 0 (length s - 1)

type index_t (#a: eqtype) (s: seq a) = i:nat{i < length s}

let upd_count (#a: eqtype) (s1: seq a) (n: nat{n < length s1}) (x: a): Lemma
  (ensures 
    (x <> index s1 n ==>
      count x s1 + 1 == count x (s1.(n) <- x) /\
      count s1.[n] s1 == count (s1.[n]) (s1.(n) <- x) + 1) /\
    (x == s1.[n] ==> count x s1 == count x (s1.(n) <- x)) /\
    (forall (y: a). {:pattern (count y s1) \/ (count y (s1.(n) <- x))}
      (y <> x /\ y <> s1.[n]) ==> count y s1 == count y (s1.(n) <- x)))
  [SMTPat (s1.(n) <- x)] =
  lemma_count_slice s1 n;
  lemma_count_slice (upd s1 n x) n

let rec count_create (#t: eqtype) (n: nat) (a b: t): Lemma
  (ensures
    (a == b ==> count b (create n a) == n) /\
    (a <> b ==> count b (create n a) == 0)) =
  match n with
  | 0 -> ()
  | _ ->
    count_create (n - 1) a b;
    assert(create (n - 1) a `equal` (tail (create n a)))

let swap_equal (#a: eqtype) (s0 s1: seq a) (i j: nat): Lemma
  (requires
    i < length s0 /\ j < length s0 /\
    length s0 == length s1 /\
    s0.[i] == s1.[j] /\ s1.[i] == s0.[j] /\
    (forall k. k <> i /\ k <> j ==> s0.[k] == s1.[k]))
  (ensures (swap s0 i j) `equal` s1) =
  let s0' = s0.(j) <- s0.[i] in
  assert(forall k. k <> j ==> s0'.[k] == s0.[k]);
  let s0'' = s0'.(i) <- s0.[j] in
  assert(s0'' == swap s0 i j);
  assert(forall k. {:pattern s1.[k]} k <> i /\ k <> j ==>
    s0''.[k] == s0.[k] /\ s0''.[k] == s1.[k])

let rec count_neq (#a: eqtype) (s: seq a) (x: a): Lemma
  (requires forall i. s.[i] <> x)
  (ensures count x s == 0)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> count_neq (tail s) x

let rec count_create_cancel (#a: eqtype) (n: nat) (x: a): Lemma
  (ensures count x (create n x) == n)
  [SMTPat (count x (create n x))] =
  match n with
  | 0 -> ()
  | _ ->
    calc (==) {
      count x (create n x);
      =={}
      1 + count x (tail (create n x));
      =={assert(equal (tail (create n x)) (create (n - 1) x))}
      1 + count x (create (n - 1) x);
      =={count_create_cancel (n - 1) x}
      n;
    }

let no_dup (#a: eqtype) (s: seq a) =
  forall (x: a). {:pattern (count x s) \/ (mem x s)} mem x s ==> count x s == 1

let disjoint (#a: eqtype) (s1 s2: seq a) =
  forall (x: a). {:pattern (mem x s1) \/ (mem x s2)}
    (mem x s1 ==> mem x s2 = false) /\
    (mem x s2 ==> mem x s1 = false)

let rec not_mem_forall (#a: eqtype) (v: a) (s: seq a): Lemma
  (requires forall i. v <> s.[i])
  (ensures mem v s == false)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ -> not_mem_forall v (tail s)

let not_mem_disjoint (#a: eqtype) (v: a) (s: seq a): Lemma
  (requires forall i. v <> s.[i])
  (ensures disjoint (create 1 v) s) =
  not_mem_forall v s

let disjoint_comm (#a: eqtype) (s1 s2: seq a): Lemma
  (requires disjoint s1 s2)
  (ensures disjoint s2 s1)
  [SMTPat (disjoint s1 s2)] = ()

let no_dup_append_1 (#a: eqtype) (s1 s2: seq a): Lemma
  (requires no_dup s1 /\ no_dup s2 /\ disjoint s1 s2)
  (ensures no_dup (s1 @| s2))
  [SMTPat (no_dup s1); SMTPat (no_dup s2); SMTPat (disjoint s1 s2)] =
  match length s1 with
  | 0 ->
    lemma_empty s1;
    append_empty_l s2
  | _ -> lemma_append_count s1 s2

let no_dup_append_2 (#a: eqtype) (s1 s2: seq a): Lemma
  (requires no_dup (s1 @| s2))
  (ensures no_dup s1 /\ no_dup s2 /\ disjoint s1 s2)
  [SMTPat (no_dup (s1 @| s2))] =
  match length s1 with
  | 0 ->
    lemma_empty s1;
    append_empty_l s2
  | _ ->
    lemma_append_count s1 s2

#push-options "--z3rlimit 128 --fuel 1 --ifuel 1"
let rec no_dup_slice (#a: eqtype) (s: seq a) (i j: nat): Lemma
  (requires no_dup s /\ i <= j /\ j <= length s)
  (ensures (
    let l = length s in
    no_dup (slice s 0 i) /\
    no_dup (slice s i j) /\
    no_dup (slice s j l) /\
    disjoint (slice s 0 i) (slice s i j) /\
    disjoint (slice s i j) (slice s j l) /\
    disjoint (slice s 0 i) (slice s j l)))
  (decreases j - i) =
  let l = length s in
  if j = i then
    assert(equal s (slice s 0 i @| slice s i l))
  else begin
    assert(equal s (slice s 0 j @| slice s j l));
    assert(equal s (slice s 0 i @| slice s i l));
    assert(equal
      (slice (slice s i l) 0 (j - i) @| slice (slice s i l) (j - i) (l - i))
      (slice s i l));
    assert(equal (slice s 0 j) (slice s 0 i @| slice s i j));
    no_dup_slice s i (j - 1)
  end
#pop-options

let slice_empty (#a: Type) (s: seq a) (len: nat): Lemma
  (requires len == 0)
  (ensures slice s 0 len == empty #a /\ length (slice s 0 len) == 0)
  [SMTPat (slice s 0 len)] =
  lemma_empty (slice s 0 len)

let append_empty_seq_r (#a: Type) (s1 s2: seq a): Lemma
  (requires length s2 == 0)
  (ensures s1 @| s2 == s1)
  [SMTPat (s1 @| s2)] =
  lemma_empty s2;
  append_empty_r s1

[@@ "opaque_to_smt"]
let rec index_of (#a: eqtype) (s: seq a) (v: a{mem v s}):
  Tot (i: index_t s{
    index s i == v /\
    (forall j. j < i ==> index s j <> index s i)
  })
  (decreases length s) =
  if head s = v then
    0
  else begin
    assert(forall j. j > 0 ==> index s j == index (tail s) (j - 1));
    1 + index_of (tail s) v
  end

let rec no_dup_index_of (#a: eqtype) (s: seq a) (i: index_t s) (v: a): Lemma
  (requires no_dup s /\ s.[i] == v)
  (ensures index_of s v == i)
  (decreases length s) =
  match length s with
  | 0 | 1 -> ()
  | _ ->
    if i > 0 then begin
      assert((cons s.[0] (tail s)) `equal` s);
      no_dup_append_2 (create 1 s.[0]) (tail s);
      no_dup_index_of (tail s) (i - 1) v
    end

let no_dup_alt (#a: eqtype) (s: seq a) (i j: index_t s): Lemma
  (requires no_dup s /\ i <> j)
  (ensures s.[i] <> s.[j]) =
  no_dup_index_of s i s.[i];
  no_dup_index_of s j s.[j]

#push-options "--z3refresh --fuel 0 --ifuel 0"
let permutation_split (#t: eqtype) (a b: seq t) (i: nat) (j: nat{
  j <= length a /\ j <= length b
}): Lemma
  (requires
    i <= j /\
    permutation t a b /\
    permutation t (slice a 0 i) (slice b 0 i) /\
    permutation t (slice a j (length a)) (slice b j (length b)))
  (ensures permutation t (slice a i j) (slice b i j)) =
  lemma_count_slice a j;
  lemma_count_slice b j;
  lemma_count_slice (slice a 0 j) i;
  lemma_count_slice (slice b 0 j) i
#pop-options

let rec count_index (#t: eqtype) (s: seq t): Lemma
  (ensures forall i. {:pattern (count s.[i] s)} count s.[i] s > 0)
  (decreases length s) =
  match length s with
  | 0 -> ()
  | _ ->
    count_index (tail s);
    assert(forall (i: pos{i < length s}). (tail s).[i - 1] == s.[i]);
    assert(forall i. s.[0] <> s.[i] ==>
      count s.[i] s == count s.[i] (tail s) /\
      count s.[i] (tail s) == count (tail s).[i - 1] (tail s))

#push-options "--z3refresh --z3rlimit 256 --fuel 2 --ifuel 2"
let permutation_middle_aux (#t: eqtype) (a b: seq t) (c: t): Lemma
  (requires permutation t a b /\ length a > 0)
  (ensures (
    let i = index_of b a.[0] in
    count c (tail a) == count c (slice b 0 i @| slice b (i + 1) (length b))))
  (decreases length a) =
  let i = index_of b a.[0] in
  match length a with
  | 1 -> ()
  | _ ->
    calc (==) {
      count c (tail a) <: int;
      =={
        lemma_tl a.[0] (tail a);
        lemma_append_count_aux c (create 1 a.[0]) (tail a)
      }
      count c a - count c (create 1 a.[0]);
      =={}
      count c b - count c (create 1 a.[0]);
      =={
        calc (==) {
          b;
          =={assert(b `equal` (slice b 0 i @| slice b i (length b)))}
          slice b 0 i @| slice b i (length b);
          =={
          assert(slice b i (length b) `equal`
            (create 1 b.[i] @| slice b (i + 1) (length b)))
          }
          slice b 0 i @| (create 1 b.[i] @| slice b (i + 1) (length b));
          =={append_assoc (slice b 0 i) (create 1 b.[i]) (slice b (i + 1) (length b))}
          (slice b 0 i @| create 1 b.[i]) @| slice b (i + 1) (length b);
        }
      }
      count c ((slice b 0 i @| create 1 b.[i]) @| slice b (i + 1) (length b)) -
      count c (create 1 a.[0]);
      =={
        lemma_append_count_aux c
          (slice b 0 i @| create 1 b.[i])
          (slice b (i + 1) (length b))
      }
      count c (slice b 0 i @| create 1 b.[i]) + count c (slice b (i + 1) (length b)) -
      count c (create 1 a.[0]);
      =={lemma_append_count_aux c (slice b 0 i) (create 1 b.[i])}
      count c (slice b 0 i) +
      count c (create 1 b.[i]) +
      count c (slice b (i + 1) (length b)) -
      count c (create 1 a.[0]);
      =={}
      count c (slice b 0 i) + count c (slice b (i + 1) (length b));
      =={lemma_append_count_aux c (slice b 0 i) (slice b (i + 1) (length b))}
      count c (slice b 0 i @| slice b (i + 1) (length b));
    }
#pop-options

let permutation_middle (#t: eqtype) (a b: seq t): Lemma
  (requires permutation t a b /\ length a > 0)
  (ensures (
    let i = index_of b a.[0] in
    permutation t (tail a) (slice b 0 i @| slice b (i + 1) (length b))
  )) =
  let open FStar.Classical in
  perm_len a b;
  match length a with
  | 1 -> ()
  | _ -> forall_intro (move_requires (permutation_middle_aux a b))

let slice_middle (#t: eqtype) (s: seq t) (i: index_t s): Lemma
  (ensures slice s 0 i @| create 1 s.[i] @| slice s (i + 1) (length s) == s) =
  assert(equal (slice s 0 i @| create 1 s.[i] @| slice s (i + 1) (length s)) s)
  
