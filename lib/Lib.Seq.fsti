module Lib.Seq

module Seq = FStar.Seq

open FStar.Calc

unfold let op_String_Access #a = Seq.index #a

let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  (Seq.length res == Seq.length s - 1) /\
  (forall (i: nat{i < Seq.length s - 1}).
    Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)

let upd_count (#a: eqtype) (s1: Seq.seq a) (n: nat{n < Seq.length s1}) (x: a): Lemma
  (ensures 
    (x <> Seq.index s1 n ==>
      Seq.count x s1 + 1 == Seq.count x (Seq.upd s1 n x) /\
      Seq.count (Seq.index s1 n) s1 == Seq.count (Seq.index s1 n) (Seq.upd s1 n x) + 1) /\
    (x == Seq.index s1 n ==> Seq.count x s1 == Seq.count x (Seq.upd s1 n x)) /\
    (forall (y: a). {:pattern (Seq.count y s1) \/ (Seq.count y (Seq.upd s1 n x))}
      (y <> x /\ y <> Seq.index s1 n) ==> Seq.count y s1 == Seq.count y (Seq.upd s1 n x)))
  [SMTPat (Seq.upd s1 n x)] =
  Seq.lemma_count_slice s1 n;
  Seq.lemma_count_slice (Seq.upd s1 n x) n

let rec count_neq (#a: eqtype) (s: Seq.seq a) (x: a): Lemma
  (requires forall i. Seq.index s i <> x)
  (ensures Seq.count x s == 0)
  (decreases Seq.length s) =
  match Seq.length s with
  | 0 -> ()
  | _ -> count_neq (Seq.tail s) x

let rec count_create_cancel (#a: eqtype) (n: nat) (x: a): Lemma
  (ensures Seq.count x (Seq.create n x) == n)
  [SMTPat (Seq.count x (Seq.create n x))] =
  match n with
  | 0 -> ()
  | _ ->
    calc (==) {
      Seq.count x (Seq.create n x);
      =={}
      1 + Seq.count x (Seq.tail (Seq.create n x));
      =={assert(Seq.equal (Seq.tail (Seq.create n x)) (Seq.create (n - 1) x))}
      1 + Seq.count x (Seq.create (n - 1) x);
      =={count_create_cancel (n - 1) x}
      n;
    }

let no_dup (#a: eqtype) (s: Seq.seq a) =
  forall (x: a). {:pattern Seq.count x s} Seq.mem x s ==> Seq.count x s == 1

let disjoint (#a: eqtype) (s1 s2: Seq.seq a) =
  forall (x: a). {:pattern (Seq.mem x s1) \/ (Seq.mem x s2)}
    (Seq.mem x s1 ==> Seq.mem x s2 = false) /\
    (Seq.mem x s2 ==> Seq.mem x s1 = false)

let disjoint_comm (#a: eqtype) (s1 s2: Seq.seq a): Lemma
  (requires disjoint s1 s2)
  (ensures disjoint s2 s1)
  [SMTPat (disjoint s1 s2)] = ()

let no_dup_append (#a: eqtype) (s1 s2: Seq.seq a): Lemma
  (requires no_dup s1 /\ no_dup s2 /\ disjoint s1 s2)
  (ensures no_dup (Seq.append s1 s2))
  [SMTPat (no_dup s1); SMTPat (no_dup s2); SMTPat (disjoint s1 s2)] =
  match Seq.length s1 with
  | 0 ->
    Seq.lemma_empty s1;
    Seq.append_empty_l s2
  | _ -> Seq.lemma_append_count s1 s2

let no_dup_append' (#a: eqtype) (s1 s2: Seq.seq a): Lemma
  (requires no_dup (Seq.append s1 s2))
  (ensures no_dup s1 /\ no_dup s2 /\ disjoint s1 s2)
  [SMTPat (no_dup (Seq.append s1 s2))] =
  match Seq.length s1 with
  | 0 ->
    Seq.lemma_empty s1;
    Seq.append_empty_l s2
  | _ ->
    Seq.lemma_append_count s1 s2

let slice_empty (#a: Type) (s: Seq.seq a) (len: nat): Lemma
  (requires len == 0)
  (ensures Seq.slice s 0 len == Seq.empty #a /\ Seq.length (Seq.slice s 0 len) == 0)
  [SMTPat (Seq.slice s 0 len)] =
  Seq.lemma_empty (Seq.slice s 0 len)

let append_empty_seq_r (#a: Type) (s1 s2: Seq.seq a): Lemma
  (requires Seq.length s2 == 0)
  (ensures Seq.append s1 s2 == s1)
  [SMTPat (Seq.append s1 s2)] =
  Seq.lemma_empty s2;
  Seq.append_empty_r s1
