module Lib.Seq

module Seq = FStar.Seq

let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  (Seq.length res == Seq.length s - 1) /\
  (forall (i: nat{i < Seq.length s - 1}).
    Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)
