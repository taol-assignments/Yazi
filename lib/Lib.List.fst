module Lib.List

open FStar.List.Tot

let rec lemma_index_append_l (#a: Type) (l1 l2:list a) (i:nat{i < length l1}): Lemma
  (ensures index l1 i == index (l1 @ l2) i)
  [SMTPat (index (append l1 l2) i)] = admit()
  // match l1 with
  // | [] -> ()
  // | x :: xs ->
  //   if i > 0 then begin
  //     lemma_len_append l1 l2;
  //     lemma_index_app1' #a (MkSeq tl) s2 (i - 1)
  //   end

let rec lemma_index_append_r (#a: Type) (l1 l2:list a) (i:nat{
  length l1 <= i /\ i < length (l1 @ l2)
}): Lemma
  (ensures index l2 (i - length l1) == index (l1 @ l2) i)
  [SMTPat (index (append l1 l2) i)] = admit()
