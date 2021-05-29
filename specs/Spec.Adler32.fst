module Spec.Adler32

module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas

open FStar.Mul
open FStar.Seq
open Lib.Seq

let rec sum_a_upper_bound_aux #n s =
  match n with
  | 0 -> ()
  | _ -> sum_a_upper_bound_aux #(n - 1) (tail s)

let rec sum_seq_append_byte #m s b =
  match m with
  | 0 -> ()
  | _ ->
    calc (==) {
      sum_seq s + U8.v b;
      =={}
      U8.v (head s) + sum_seq #(m - 1) (tail s) + U8.v b;
      =={sum_seq_append_byte #(m - 1) (tail s) b}
      U8.v (head s) + sum_seq #m (snoc (tail s) b);
      =={}
      U8.v (head (create 1 (head s))) + sum_seq #m (snoc (tail s) b);
      =={
        lemma_head_append (create 1 (head s)) (snoc (tail s) b);
        lemma_tail_append (create 1 (head s)) (snoc (tail s) b);
        assert(equal
          ((tail (create 1 (head s))) @| (snoc (tail s) b))
          (snoc (tail s) b))
      }
      sum_seq #(m + 1) ((create 1 (head s)) @| (snoc (tail s) b));
      =={
         assert(equal
           ((create 1 (head s)) @| (snoc (tail s) b))
           (snoc s b))
      }
      sum_seq #(m + 1) (snoc s b);
    }
    
#set-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rec sum_a_append #m1 #m2 s1 s2 =
  let open U8 in
  match m1 with
  | 0 ->
    calc (==) {
      sum_a #(m1 + m2) (s1 @| s2);
      =={
        Seq.lemma_empty s1;
        Seq.append_empty_l s2
      }
      sum_a s2;
      =={}
      1 + sum_seq s2;
      =={}
      sum_a s1 + sum_seq s2;
    }
  | _ ->
    calc (==) {
      sum_a #(m1 + m2) (s1 @| s2);
      =={}
      1 + sum_seq #(m1 + m2) (s1 @| s2);
      =={
        lemma_head_append s1 s2;
        Seq.lemma_tail_append s1 s2
      }
      1 + U8.v (head s1) + sum_seq #(m1 + m2 - 1) ((tail s1) @| s2);
      =={}
      U8.v (head s1) + sum_a #(m1 + m2 - 1) ((tail s1) @| s2);
      =={sum_a_append #(m1 - 1) #m2 (tail s1) s2}
      U8.v (head s1) + sum_a #(m1 - 1) (tail s1) + sum_seq s2;
      =={}
      sum_a s1 + sum_seq s2;
    }

#set-options "--z3rlimit 65536 --fuel 1 --ifuel 0 --z3seed 49999"
let rec sum_b'_append (#m1 #m2: nat) (s1: input m1) (s2: input m2): Lemma (ensures
  sum_b' #(m1 + m2) (Seq.append s1 s2) == sum_b' s1 + m2 * (sum_seq s1) + sum_b' s2) =
  let open U8 in
  match m1 with
  | 0 -> 
    calc (==) {
      sum_b' s1 + m2 * (sum_seq s1) + sum_b' s2;
      =={}
      m2 * (sum_seq s1) + sum_b' s2;
      =={}
      sum_b' s2;
      =={
         Seq.lemma_empty s1;
         Seq.append_empty_l s2
      }
      sum_b' #(m1 + m2) (s1 @| s2);
    }
  | _ ->
    calc (==) {
      sum_b' #(m1 + m2) (s1 @| s2);
      =={}
      (m1 + m2) * (v (head (s1 @| s2))) + sum_b' #(m1 + m2 - 1) (tail (s1 @| s2));
      =={Seq.lemma_tail_append s1 s2}
      (m1 + m2) * (v (head (s1 @| s2))) + sum_b' #(m1 + m2 - 1) ((tail s1) @| s2);
      =={Seq.lemma_head_append s1 s2}
      (m1 + m2) * (v (head s1)) + sum_b' #(m1 + m2 - 1) ((tail s1) @| s2);
      =={sum_b'_append #(m1 - 1) #m2 (tail s1) s2}
      (m1 + m2) * (v (head s1)) +
      sum_b' #(m1 - 1) (tail s1) +
      m2 * sum_seq #(m1 - 1) (tail s1) +
      sum_b' s2;
      =={}
      m1 * (v (head s1)) +
      sum_b' #(m1 - 1) (tail s1) +
      m2 * (v (head s1)) +
      m2 * sum_seq #(m1 - 1) (tail s1) +
      sum_b' s2;
      =={}
      sum_b' s1 + m2 * sum_seq s1 + sum_b' s2;
    }

let rec sum_a_sum_seq (#m: nat) (s: input m): Lemma
  (ensures sum_a s - 1 == sum_seq s) =
  let open U8 in
  match m with
  | 0 -> ()
  | _ ->
    calc (==) {
      sum_a s - 1;
      =={}
      v (head s) + sum_a #(m - 1) (tail s) - 1;
      =={sum_a_sum_seq #(m - 1) (tail s)}
      v (head s) + sum_seq #(m - 1) (tail s);
      =={}
      sum_seq s;
    }

let sum_b_append #m1 #m2 s1 s2 =
  calc (==) {
    sum_b #(m1 + m2) (s1 @| s2);
    =={}
    sum_b' #(m1 + m2) (s1 @| s2) + m1 + m2;
    =={sum_b'_append s1 s2}
    sum_b' s1 + m2 * (sum_seq s1) + sum_b' s2 + m1 + m2;
    =={sum_a_sum_seq s1}
    sum_b' s1 + m2 * (sum_a s1 - 1) + sum_b' s2 + m1 + m2;
    =={}
    sum_b' s1 + m2 * sum_a s1 + sum_b' s2 + m1;
    =={}
    sum_b s1 + m2 * sum_a s1 + sum_b' s2;
  }

let n_mod2_aux (n: nat{n > 0}): Lemma
  (ensures (n * (n - 1)) % 2 == 0) =
  if n % 2 = 0 then
    calc (==) {
      (n * (n - 1)) % 2;
      =={Math.div_exact_r n 2}
      (2 * (n / 2) * (n - 1)) % 2;
      =={Math.paren_mul_right 2 (n / 2) (n - 1)}
      (2 * ((n / 2) * (n - 1))) % 2;
      =={Math.cancel_mul_mod ((n / 2) * (n - 1)) 2}
      0;
    }
  else
    calc (==) {
      (n * (n - 1)) % 2;
      =={Math.div_exact_r (n - 1) 2}
      (n * (((n - 1) / 2) * 2)) % 2;
      =={Math.paren_mul_right n ((n - 1) / 2) 2}
      (n * ((n - 1) / 2) * 2) % 2;
      =={Math.cancel_mul_mod (n * ((n - 1) / 2)) 2}
      0;
    }

let rec sum_b_upper_bound_aux #n s =
  match n with
  | 0 -> ()
  | _ ->
    calc (<=) {
      sum_b s;
      =={assert(Seq.equal s ((create 1 (head s)) @| tail s))}
      sum_b #n ((create 1 (head s)) @| tail s);
      =={sum_b_append #1 #(n - 1) (create 1 (head s)) (tail s)}
      sum_b #1 (create 1 (head s)) +
      (n - 1) * sum_a #1 (create 1 (head s)) +
      sum_b #(n - 1) (tail s) - n + 1;
      =={assert_norm(sum_b #1 (create 1 (head s)) == (U8.v (head s)) + 1)}
      (U8.v (head s)) + 1 +
      (n - 1) * (U8.v (head s) + 1) +
      sum_b #(n - 1) (tail s) - n + 1;
      =={}
      1 + n * (U8.v (head s)) + sum_b #(n - 1) (tail s);
      <= {sum_b_upper_bound_aux #(n - 1) (tail s)}
      1 + n * (U8.v (head s)) + (1 + (n - 1)) * (n - 1) * 255/ 2 + (n - 1);
      <={}
      n * 255 + n * (n - 1) * 255 / 2 + n;
      =={Math.swap_mul (n - 1) 255}
      n * 255 + n * 255 * (n - 1) / 2 + n;
      =={}
      (n * 255 + n * 255 * (n - 1) / 2 + n) * 2 / 2;
      =={
        calc (==) {
          (n * 255 * (n - 1)) % 2;
          =={Math.swap_mul 255 (n - 1)}
          (n * (n - 1) * 255) % 2;
          =={Math.lemma_mod_mul_distr_l (n * (n - 1)) 255 2}
          (((n * (n - 1)) % 2) * 255) % 2;
          =={n_mod2_aux n}
          0;
        };
        Math.div_exact_r (n * 255 * (n - 1)) 2
      }
      (n * 255 * 2 + n * 255 * (n - 1) + n * 2) / 2;
      =={}
      (n * 255 * (n + 1) + n * 2) / 2;
      =={}
      n * 255 * (n + 1) / 2 + n;
      =={Math.swap_mul 255 (n + 1)}
      n * (n + 1) * 255 / 2 + n;
      =={}
      sum_b_upper_bound n;
    }

#set-options "--fuel 0 --ifuel 0"
let rec sum_b'_sum_seq #m s byte =
  match m with
  | 0 -> ()
  | _ ->
    calc (==) {
      sum_b' s + sum_seq #(m + 1) (snoc s byte);
      =={}
      m * (U8.v (head s)) + sum_b' #(m - 1) (tail s) +
      sum_seq #(m + 1) (snoc s byte);
      =={
        lemma_head_append s (create 1 byte);
        lemma_tail_append s (create 1 byte)
      }
      m * (U8.v (head s)) + sum_b' #(m - 1) (tail s) +
      U8.v (head s) + sum_seq #m (snoc (tail s) byte);
      =={}
      (m + 1) * (U8.v (head s)) + sum_b' #(m - 1) (tail s) +
      sum_seq #m (snoc (tail s) byte);
      =={sum_b'_sum_seq #(m - 1) (tail s) byte}
      (m + 1) * (U8.v (head s)) + sum_b' #m (snoc (tail s) byte);
      =={
        lemma_head_append (create 1 (head s)) (snoc (tail s) byte);
        lemma_tail_append (create 1 (head s)) (snoc (tail s) byte);
        append_empty_r (snoc (tail s) byte);
        assert(equal
          (tail ((create 1 (head s)) @| snoc (tail s) byte))
          (snoc (tail s) byte))
      }
      sum_b' #(m + 1) ((create 1 (head s)) @| snoc (tail s) byte);
      =={
        assert(equal
          ((create 1 (head s)) @| (snoc (tail s) byte))
          (snoc s byte))
      }
      sum_b' #(m + 1) (snoc s byte);
    }

let sum_b'_u64_uppser_bound #n #m s c =
  calc (<=) {
     (sum_b s % base) + m * (sum_a s % base) + sum_b' c;
     <={
       Math.modulo_range_lemma (sum_b s) base;
       Math.modulo_range_lemma (sum_a s) base
     }
     (base - 1) + m * (base - 1) + sum_b' c;
     <={sum_b'_upper_bound_aux c}
     1 * (base - 1) + m * (base - 1) + ((sum_b_upper_bound m) - m);
     =={Math.distributivity_add_left 1 m (base - 1)}
     (m + 1) * (base - 1) + m * (m + 1) * 255 / 2;
  }
