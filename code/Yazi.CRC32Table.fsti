module Yazi.CRC32Table

module B = LowStar.Buffer
module Spec = Spec.CRC32
module M = LowStar.Modifies
module ST = FStar.HyperStack.ST

val gen_crc32_table:
    t8: Spec.table_buf
  -> t16: Spec.table_buf
  -> t24: Spec.table_buf
  -> t32: Spec.table_buf
  -> ST.Stack unit
  (requires fun h ->
    B.live h t8 /\ B.live h t16 /\ B.live h t24 /\ B.live h t32 /\
    B.disjoint t8 t16 /\ B.disjoint t8 t24 /\ B.disjoint t8 t32 /\
    B.disjoint t16 t24 /\ B.disjoint t16 t32 /\ B.disjoint t24 t32)
  (ensures fun h0 _ h1 ->
    M.modifies 
      (B.loc_buffer t8 `B.loc_union`
      B.loc_buffer t16 `B.loc_union`
      B.loc_buffer t24 `B.loc_union`
      B.loc_buffer t32)
      h0 h1 /\
    Spec.table_correct 8 h1 t8 /\
    Spec.table_correct 16 h1 t16 /\
    Spec.table_correct 24 h1 t24 /\
    Spec.table_correct 32 h1 t32)
