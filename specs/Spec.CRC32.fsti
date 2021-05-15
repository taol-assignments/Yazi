module Spec.CRC32

module Seq = FStar.Seq

unfold let unsnoc (#a: Type) (s: Seq.seq a{
  Seq.length s > 0
}): Tot (res: Seq.seq a{
  forall i.
    Seq.length res == Seq.length s - 1 /\
    (Seq.index s i == Seq.index res i)
}) =
  Seq.slice s 0 (Seq.length s - 1)

include Spec.CRC32.Bits
include Spec.CRC32.Matrix
