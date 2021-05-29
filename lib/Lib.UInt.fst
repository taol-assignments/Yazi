module Lib.UInt

module U32 = FStar.UInt32
module UInt = FStar.UInt

open FStar.Seq
open FStar.Mul

#set-options "--z3rlimit 120 --z3seed 1 --fuel 16 --ifuel 16"
let rec cast_zero_prefix #n v m =
  match m - n with
  | 0 -> assert(Seq.equal (UInt.to_vec #m v) ((Seq.create (m - n) false) @| (UInt.to_vec v)))
  | _ ->
    if n >= 1 then
      calc (==) {
        UInt.to_vec #m v;
        =={}
        (UInt.to_vec #(m - 1) (v / 2)) @| (Seq.create 1 (v % 2 = 1));
        =={
          Math.Lemmas.pow2_le_compat (m - 1) (n - 1);
          assert(v / 2 <= pow2 (n - 1));
          cast_zero_prefix #(n - 1) (v / 2) (m - 1)
        }
        ((Seq.create (m - n) false) @| (UInt.to_vec #(n - 1) (v / 2))) @|
        (Seq.create 1 (v % 2 = 1));
        =={
          Seq.append_assoc
            (Seq.create (m - n) false)
            (UInt.to_vec #(n - 1) (v / 2))
            (Seq.create 1 (v % 2 = 1))
        }
        (Seq.create (m - n) false) @|
        ((UInt.to_vec #(n - 1) (v / 2)) @| (Seq.create 1 (v % 2 = 1)));
        =={}
        (Seq.create (m - n) false) @| (UInt.to_vec v);
      }
    else begin
      assert(Seq.equal (UInt.to_vec #m v) (Seq.create m false));
      assert(UInt.to_vec #n v == Seq.empty #bool);
      assert(Seq.equal (UInt.to_vec #m v) ((Seq.create m false) @| (Seq.empty #bool)))
    end

#set-options "--z3rlimit 200 --z3seed 1 --fuel 1 --ifuel 0"
let div2_snoc (#n: nat{0 < n}) (a: UInt.uint_t n): Lemma
  (ensures UInt.to_vec #(n - 1) (a / 2) == slice (UInt.to_vec a) 0 (n - 1)) =
  calc (==) {
    UInt.to_vec #(n - 1) (a / 2);
    =={UInt.shift_right_value_lemma a 1}
    UInt.to_vec #(n - 1) (UInt.shift_right a 1);
    =={
      assert(Seq.equal
        (UInt.to_vec #(n - 1) (UInt.shift_right a 1))
        (slice (UInt.to_vec a) 0 (n - 1)))
    }
    slice (UInt.to_vec a) 0 (n - 1);
  }

let rec zero_prefix_eq #n #m vn vm =
  match m - n with
  | 0 ->
    assert(Seq.equal (UInt.to_vec vn) (UInt.to_vec vm));
    UInt.to_vec_lemma_2 vm vn
  | _ ->
    let vm' = UInt.to_vec vm in
    let vn' = UInt.to_vec vn in
    match m with
    | 1 ->
      if last vm' then
        UInt.to_vec_lemma_2 vn (UInt.one n)
      else
        UInt.to_vec_lemma_2 vn (UInt.zero n);
      assert(vn == 1 \/ vn == 0);
      calc (==) {
        vm;
        =={}
        UInt.from_vec vm';
        =={}
        0 + (if last vm' then 1 else 0);
        =={UInt.zero_from_vec_lemma #(n - 1)}
        UInt.from_vec #(n - 1) (slice vn' 0 (n - 1)) + (if last vn' then 1 else 0);
        =={}
        UInt.from_vec vn';
        =={UInt.inverse_num_lemma vn}
        vn;
      }
    | _ ->
      let vm'' = slice vm' 0 (m - 1) in
      let vn'' = slice vn' 0 (n - 1) in
      div2_snoc vm;
      div2_snoc vn;
      zero_prefix_eq #(n - 1) #(m - 1) (vn / 2) (vm / 2);
      calc (==) {
        vm;
        =={}
        UInt.from_vec vm';
        =={}
        2 * (UInt.from_vec #(m - 1) vm'') + (if last vm' then 1 else 0);
        =={div2_snoc vm}
        2 * (UInt.from_vec (UInt.to_vec #(m - 1) (vm / 2))) + (if last vn' then 1 else 0);
        =={}
        2 * (vn / 2) + (if last vn' then 1 else 0);
        =={}
        vn;
      }

#set-options "--z3rlimit 200 --ifuel 128 --fuel 128 --z3seed 1"
let logand_256 r =
  let open U32 in
  let mask = v 0xFFul in
  assert(forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth mask i == false) /\
    (i >= 32 - 8 ==> UInt.nth mask i == true));
  assert(forall (i: nat{i < 32}).
    (i < 32 - 8 ==> UInt.nth (UInt.logand (v r) (v 0xFFul)) i == false) /\
    (i >= 32 - 8 ==> UInt.nth (UInt.logand (v r) (v 0xFFul)) i == UInt.nth (U32.v r) i))
