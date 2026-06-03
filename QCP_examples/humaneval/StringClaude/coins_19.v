Load "../spec/19".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Import string_bridge.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Import naive_C_Rules.
Local Open Scope sac.

Definition ptr_mixed_store (p lo : Z) (a : option Z) : Assertion :=
  match a with
  | Some v => ((p + lo * sizeof(PTR)) # Ptr |-> v)
  | None => ((p + lo * sizeof(PTR)) # Ptr |->_)
  end.

Fixpoint ptr_mixed_seg (p lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => [| hi = lo |] && emp
  | cons a l' => ptr_mixed_store p lo a ** ptr_mixed_seg p (lo + 1) hi l'
  end.

Fixpoint ptr_mixed_missing_i (p i lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => [| False |] && emp
  | cons a l' =>
      if Z.eq_dec i lo then ptr_mixed_seg p (lo + 1) hi l'
      else ptr_mixed_store p lo a ** ptr_mixed_missing_i p i (lo + 1) hi l'
  end.

Module PtrArray.
  Include naive_C_Rules.PtrArray.

  Definition mixed_full (p n : Z) (l : list (option Z)) : Assertion :=
    ptr_mixed_seg p 0 n l.

  Definition mixed_missing_i
    (p i lo hi : Z) (l : list (option Z)) : Assertion :=
    ptr_mixed_missing_i p i lo hi l.
End PtrArray.

Definition problem_19_pre_z (input : list Z) : Prop :=
  problem_19_pre (string_of_list_z input).

Definition problem_19_spec_z (input output : list Z) : Prop :=
  problem_19_spec (string_of_list_z input) (string_of_list_z output).

Definition ascii_range_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  l = replace_Znth n (Some a) (repeat None 10).

Definition number_word_z (digit : Z) : list Z :=
  match digit with
  | 0 => [122; 101; 114; 111]
  | 1 => [111; 110; 101]
  | 2 => [116; 119; 111]
  | 3 => [116; 104; 114; 101; 101]
  | 4 => [102; 111; 117; 114]
  | 5 => [102; 105; 118; 101]
  | 6 => [115; 105; 120]
  | 7 => [115; 101; 118; 101; 110]
  | 8 => [101; 105; 103; 104; 116]
  | 9 => [110; 105; 110; 101]
  | 10 => [32]
  | _ => []
  end.

Definition number_word_len_z (digit : Z) : Z :=
  Zlength (number_word_z digit).

Definition number_word_ptrs_z
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : list Z :=
  [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9].

Definition number_word_char_full_z (w digit : Z) : Assertion :=
  CharArray.full w (number_word_len_z digit + 1)
    (number_word_z digit ++ [0]).

Definition number_words_chars_full_z
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  number_word_char_full_z w9 9 **
  number_word_char_full_z w8 8 **
  number_word_char_full_z w7 7 **
  number_word_char_full_z w6 6 **
  number_word_char_full_z w5 5 **
  number_word_char_full_z w4 4 **
  number_word_char_full_z w3 3 **
  number_word_char_full_z w2 2 **
  number_word_char_full_z w1 1 **
  number_word_char_full_z w0 0.

Definition number_words_chars_missing_z
  (d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  match d with
  | 0 =>
      [| word = w0 |] &&
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 1 =>
      [| word = w1 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 2 =>
      [| word = w2 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 3 =>
      [| word = w3 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 4 =>
      [| word = w4 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 5 =>
      [| word = w5 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 6 =>
      [| word = w6 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 7 =>
      [| word = w7 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w9 9
  | 8 =>
      [| word = w8 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w9 9
  | 9 =>
      [| word = w9 |] &&
      number_word_char_full_z w0 0 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w8 8
  | _ => [| False |] && emp
  end.

Definition number_words_full
  (words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  number_words_chars_full_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
  PtrArray.full words 10 (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9).

Definition number_words_missing
  (words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  PtrArray.missing_i words d 0 10
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) **
  number_words_chars_missing_z d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.

Definition scan_char_z (i : Z) (input : list Z) : Z :=
  if Z.ltb i (Zlength input) then Znth i input 0 else 32.

Fixpoint scan_word_start_nat (fuel : nat) (input : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      let prev := scan_word_start_nat fuel' input in
      let pos := Z.of_nat fuel' in
      if Z.eqb (scan_char_z pos input) 32 then pos + 1 else prev
  end.

Definition scan_word_start_z (i : Z) (input : list Z) : Z :=
  scan_word_start_nat (Z.to_nat i) input.

Definition token_prefix_z (i tlen : Z) (input : list Z) : list Z :=
  if Z.ltb tlen 31 then sublist (i - tlen) i input
  else
    let start := scan_word_start_z i input in
    sublist start (start + tlen) input.

Definition token_unsat_end_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 \/ scan_word_start_z i input + tlen = i.

Definition token_empty_start_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 -> scan_word_start_z i input = i.

Definition number_word_string (digit : Z) : string :=
  string_of_list_z (number_word_z digit).

Definition append_number_word_z (prefix : list Z) (digit : Z) : list Z :=
  prefix ++ (if Z.eqb (Zlength prefix) 0 then [] else [32]) ++ number_word_z digit.

Fixpoint append_repeated_number_word_nat
  (prefix : list Z) (digit : Z) (n : nat) : list Z :=
  match n with
  | O => prefix
  | S n' => append_number_word_z
              (append_repeated_number_word_nat prefix digit n') digit
  end.

Definition append_repeated_number_word_z
  (prefix : list Z) (digit count done : Z) : list Z :=
  append_repeated_number_word_nat prefix digit (Z.to_nat done).

Definition sorted_numbers_output_by_counts_z
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : list Z :=
  append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z [] 0 c0 c0)
      1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4)
      5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 c8) 9 c9 c9.

Definition output_prefix_z
  (digit done c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : list Z :=
  match digit with
  | 0 => append_repeated_number_word_z [] 0 c0 done
  | 1 => append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 done
  | 2 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 done
  | 3 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 done
  | 4 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 done
  | 5 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 done
  | 6 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 done
  | 7 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 done
  | 8 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 done
  | 9 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 c8) 9 c9 done
  | _ => sorted_numbers_output_by_counts_z c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  end.

Definition output_capacity_prefix_z
  (digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Z :=
  match digit with
  | 0 => 1
  | 1 => 1 + c0 * (number_word_len_z 0 + 1)
  | 2 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1)
  | 3 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1)
  | 4 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1)
  | 5 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1)
  | 6 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1)
  | 7 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1)
  | 8 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1)
  | 9 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1) + c8 * (number_word_len_z 8 + 1)
  | _ => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1) + c8 * (number_word_len_z 8 + 1) + c9 * (number_word_len_z 9 + 1)
  end.

Definition count_word_in_string (digit : Z) (input : list Z) : Z :=
  Z.of_nat
    (count_occ string_dec
       (SplitOnSpaces (string_of_list_z input))
       (number_word_string digit)).

Definition output_prefix_by_input_z
  (digit done : Z) (input : list Z) : list Z :=
  output_prefix_z digit done
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition output_capacity_prefix_by_input_z
  (digit : Z) (input : list Z) : Z :=
  output_capacity_prefix_z digit
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition sorted_numbers_output_z (input : list Z) : list Z :=
  sorted_numbers_output_by_counts_z
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition number_words_safe_z (input : list Z) : Prop :=
  problem_19_pre_z input /\ ascii_range_z input.

Fixpoint next_word_end_nat (fuel : nat) (pos : Z) (input : list Z) : Z :=
  match fuel with
  | O => pos
  | S fuel' =>
      if Z.geb pos (Zlength input) then pos
      else if Z.eqb (Znth pos input 0) 32 then pos
      else next_word_end_nat fuel' (pos + 1) input
  end.

Definition next_word_end_z (pos : Z) (input : list Z) : Z :=
  next_word_end_nat (Z.to_nat (Zlength input - pos + 1)) pos input.

Definition number_word_digit_at_z (pos : Z) (input : list Z) : Z :=
  let c0 := Znth pos input 0 in
  let c1 := Znth (pos + 1) input 0 in
  if Z.eqb c0 122 then 0
  else if Z.eqb c0 111 then 1
  else if Z.eqb c0 101 then 8
  else if Z.eqb c0 110 then 9
  else if Z.eqb c0 116 then if Z.eqb c1 119 then 2 else 3
  else if Z.eqb c0 102 then if Z.eqb c1 111 then 4 else 5
  else if Z.eqb c1 105 then 6 else 7.

Definition count_update_z (old matched digit : Z) : Z :=
  if Z.eqb matched digit then old + 1 else old.

Definition scan_counts_z
  (i : Z) (input : list Z)
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  0 <= i <= Zlength input + 1 /\
  0 <= c0 <= i /\ 0 <= c1 <= i /\
  0 <= c2 <= i /\ 0 <= c3 <= i /\
  0 <= c4 <= i /\ 0 <= c5 <= i /\
  0 <= c6 <= i /\ 0 <= c7 <= i /\
  0 <= c8 <= i /\ 0 <= c9 <= i.

Lemma append_number_word_z_length : forall prefix digit,
  0 <= digit <= 9 ->
  Zlength (append_number_word_z prefix digit) =
  Zlength prefix +
  (if Z.eqb (Zlength prefix) 0 then 0 else 1) +
  Zlength (number_word_z digit).
Proof.
  intros prefix digit Hdigit.
  unfold append_number_word_z.
  repeat rewrite Zlength_app.
  destruct (Z.eqb (Zlength prefix) 0);
    repeat rewrite Zlength_cons; repeat rewrite Zlength_nil; lia.
Qed.

Lemma append_repeated_number_word_z_0 : forall prefix digit count,
  append_repeated_number_word_z prefix digit count 0 = prefix.
Proof. reflexivity. Qed.

Lemma append_repeated_number_word_z_step : forall prefix digit count j,
  0 <= j ->
  append_repeated_number_word_z prefix digit count (j + 1) =
  append_number_word_z
    (append_repeated_number_word_z prefix digit count j) digit.
Proof.
  intros prefix digit count j Hj.
  unfold append_repeated_number_word_z.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  reflexivity.
Qed.

Lemma sublist_full_19 : forall (input : list Z),
  sublist 0 (Zlength input) input = input.
Proof.
  intros input.
  unfold sublist.
  rewrite skipn_O.
  rewrite Zlength_correct.
  replace (Z.to_nat (Z.of_nat (List.length input))) with
    (List.length input) by lia.
  apply firstn_all.
Qed.
