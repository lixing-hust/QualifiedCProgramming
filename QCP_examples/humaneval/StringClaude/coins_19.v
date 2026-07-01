Load "../spec/19".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.
Import ListNotations.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition ascii_of_z_19 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_19 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_19 c) (string_of_list_z_19 rest)
  end.

Definition ptr_mixed_store (p lo : Z) (a : option Z) : Assertion :=
  match a with
  | Some v => ((p + lo * sizeof(PTR)) # Ptr |-> v)
  | None => ((p + lo * sizeof(PTR)) # Ptr |->_)
  end.

Fixpoint ptr_mixed_seg (p lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => coq_prop (hi = lo) && emp
  | cons a l' => ptr_mixed_store p lo a ** ptr_mixed_seg p (lo + 1) hi l'
  end.

Fixpoint ptr_mixed_missing_i (p i lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => coq_prop False && emp
  | cons a l' =>
      if Z.eq_dec i lo then ptr_mixed_seg p (lo + 1) hi l'
      else ptr_mixed_store p lo a ** ptr_mixed_missing_i p i (lo + 1) hi l'
  end.

Definition problem_19_pre_z (input : list Z) : Prop :=
  problem_19_pre (string_of_list_z_19 input).

Definition problem_19_spec_z (input output : list Z) : Prop :=
  problem_19_spec (string_of_list_z_19 input) (string_of_list_z_19 output).

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

Ltac destruct_digit_cases_19 d :=
  let Hcases := fresh "Hcases" in
  assert (Hcases:
    d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
    d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia;
  destruct Hcases as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
  subst d.

Lemma number_word_z_neq_19 :
  forall d k,
    0 <= d < 10 ->
    0 <= k < 10 ->
    d <> k ->
    number_word_z d <> number_word_z k.
Proof.
  intros d k Hd Hk Hneq.
  destruct_digit_cases_19 d; destruct_digit_cases_19 k;
    cbn; congruence.
Qed.

Lemma number_word_z_nonempty_19 :
  forall d,
    0 <= d < 10 ->
    number_word_z d <> [].
Proof.
  intros d Hd.
  destruct_digit_cases_19 d; cbn; congruence.
Qed.

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
      coq_prop (word = w0) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1
  | 1 =>
      coq_prop (word = w1) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w0 0
  | 2 =>
      coq_prop (word = w2) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 3 =>
      coq_prop (word = w3) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 4 =>
      coq_prop (word = w4) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 5 =>
      coq_prop (word = w5) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 6 =>
      coq_prop (word = w6) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 7 =>
      coq_prop (word = w7) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 8 =>
      coq_prop (word = w8) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 9 =>
      coq_prop (word = w9) &&
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | _ => coq_prop False && emp
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

Definition token_sat_start_z (i tlen : Z) (input : list Z) : Prop :=
  31 <= tlen -> scan_word_start_z i input + 31 <= i.

Definition token_empty_start_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 -> scan_word_start_z i input = i \/ i >= Zlength input.

Definition token_miss_prefix_z (d : Z) (token : list Z) : Prop :=
  forall k, 0 <= k < d -> token <> number_word_z k.

Definition number_word_string (digit : Z) : string :=
  string_of_list_z_19 (number_word_z digit).

Fixpoint SplitOnSpaces_aux_19 (current_group : list ascii) (s : string) : list string :=
  match s with
  | EmptyString =>
      match current_group with
      | [] => []
      | _ => [string_of_list_ascii (List.rev current_group)]
      end
  | String h t =>
      if ascii_dec h " "%char then
        match current_group with
        | [] => SplitOnSpaces_aux_19 [] t
        | _ => string_of_list_ascii (List.rev current_group) :: SplitOnSpaces_aux_19 [] t
        end
      else SplitOnSpaces_aux_19 (h :: current_group) t
  end.

Definition SplitOnSpaces_19 (s : string) : list string :=
  SplitOnSpaces_aux_19 [] s.

Fixpoint SplitOnSpacesZ_aux_19 (current_group : list Z) (input : list Z)
  : list (list Z) :=
  match input with
  | [] =>
      match current_group with
      | [] => []
      | _ => [List.rev current_group]
      end
  | h :: t =>
      if Z.eqb h 32 then
        match current_group with
        | [] => SplitOnSpacesZ_aux_19 [] t
        | _ => List.rev current_group :: SplitOnSpacesZ_aux_19 [] t
        end
      else SplitOnSpacesZ_aux_19 (h :: current_group) t
  end.

Definition SplitOnSpacesZ_19 (input : list Z) : list (list Z) :=
  SplitOnSpacesZ_aux_19 [] input.

Definition list_Z_eq_dec_19 : forall x y : list Z, {x = y} + {x <> y} :=
  list_eq_dec Z.eq_dec.

Definition no_space_z_list_19 (l : list Z) : Prop :=
  forall x, In x l -> x <> 32.

Lemma SplitOnSpacesZ_aux_app_space_19 :
  forall current prefix rest,
    SplitOnSpacesZ_aux_19 current (prefix ++ 32 :: rest) =
    SplitOnSpacesZ_aux_19 current (prefix ++ [32]) ++
    SplitOnSpacesZ_aux_19 [] rest.
Proof.
  intros current prefix.
  revert current.
  induction prefix as [| h prefix IH]; intros current rest; simpl.
  - destruct current; reflexivity.
  - destruct (Z.eqb h 32); simpl.
    + destruct current; simpl; rewrite IH; reflexivity.
    + rewrite IH; reflexivity.
Qed.

Lemma SplitOnSpacesZ_aux_no_space_19 :
  forall token current,
    no_space_z_list_19 token ->
    SplitOnSpacesZ_aux_19 current token =
    match token with
    | [] =>
        match current with
        | [] => []
        | _ => [List.rev current]
        end
    | _ => [List.rev current ++ token]
    end.
Proof.
  induction token as [| h token IH]; intros current Hnospace; simpl.
  - destruct current; reflexivity.
  - assert (Hh : h <> 32).
    { apply Hnospace. left. reflexivity. }
    destruct (Z.eqb_spec h 32) as [Heq | Hneq]; [contradiction |].
    rewrite IH.
    + replace (List.rev (h :: current)) with (List.rev current ++ [h])
        by (simpl; reflexivity).
      destruct token as [| h' token']; simpl.
      * reflexivity.
      * f_equal.
        remember (List.rev current) as prefix.
        clear Heqprefix current Hnospace Hh Hneq IH.
        induction prefix; simpl; [reflexivity |].
        rewrite IHprefix. reflexivity.
    + intros x Hin. apply Hnospace. right. exact Hin.
Qed.

Lemma SplitOnSpacesZ_no_space_19 :
  forall token,
    no_space_z_list_19 token ->
    SplitOnSpacesZ_19 token =
    match token with
    | [] => []
    | _ => [token]
    end.
Proof.
  intros token Hnospace.
  unfold SplitOnSpacesZ_19.
  rewrite SplitOnSpacesZ_aux_no_space_19 by exact Hnospace.
  destruct token; reflexivity.
Qed.

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
    (count_occ list_Z_eq_dec_19
       (SplitOnSpacesZ_19 input)
       (number_word_z digit)).

Definition split_boundary_z (prefix : list Z) : Prop :=
  prefix = [] \/ exists pre, prefix = pre ++ [32].

Lemma SplitOnSpacesZ_aux_append_space_end_19 :
  forall current input,
    SplitOnSpacesZ_aux_19 current (input ++ [32]) =
    SplitOnSpacesZ_aux_19 current input.
Proof.
  intros current input.
  revert current.
  induction input as [| h input IH]; intros current; simpl.
  - destruct current; reflexivity.
  - destruct (Z.eqb h 32); destruct current; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma SplitOnSpacesZ_append_space_end_19 :
  forall input,
    SplitOnSpacesZ_19 (input ++ [32]) = SplitOnSpacesZ_19 input.
Proof.
  intros input.
  unfold SplitOnSpacesZ_19.
  apply SplitOnSpacesZ_aux_append_space_end_19.
Qed.

Lemma SplitOnSpacesZ_boundary_append_19 :
  forall prefix token,
    split_boundary_z prefix ->
    no_space_z_list_19 token ->
    SplitOnSpacesZ_19 (prefix ++ token) =
    SplitOnSpacesZ_19 prefix ++
      match token with
      | [] => []
      | _ => [token]
      end.
Proof.
  intros prefix token Hboundary Hnospace.
  destruct Hboundary as [-> | [pre ->]].
  - simpl. apply SplitOnSpacesZ_no_space_19. exact Hnospace.
  - destruct token as [| h token].
    + repeat rewrite app_nil_r. reflexivity.
    + unfold SplitOnSpacesZ_19.
      replace ((pre ++ [32]) ++ h :: token) with
        (pre ++ 32 :: h :: token) by (rewrite <- app_assoc; reflexivity).
      rewrite SplitOnSpacesZ_aux_app_space_19.
      simpl.
      assert (Hh : h <> 32).
      { apply Hnospace. left. reflexivity. }
      destruct (Z.eqb_spec h 32) as [Heq | Hneq]; [contradiction |].
      rewrite (SplitOnSpacesZ_aux_no_space_19 token [h]).
      2: { intros x Hin. apply Hnospace. right. exact Hin. }
      destruct token; reflexivity.
Qed.

Lemma count_occ_app_19 :
  forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l1 l2 : list A) (x : A),
    count_occ eq_dec (l1 ++ l2) x =
    (count_occ eq_dec l1 x + count_occ eq_dec l2 x)%nat.
Proof.
  intros A eq_dec l1.
  induction l1 as [| h l1 IH]; intros l2 x; simpl.
  - reflexivity.
  - destruct (eq_dec h x); simpl; rewrite IH; lia.
Qed.

Lemma count_word_boundary_append_nohit_19 :
  forall digit prefix token,
    split_boundary_z prefix ->
    no_space_z_list_19 token ->
    token <> number_word_z digit ->
    count_word_in_string digit (prefix ++ token) =
    count_word_in_string digit prefix.
Proof.
  intros digit prefix token Hboundary Hnospace Hneq.
  unfold count_word_in_string.
  rewrite SplitOnSpacesZ_boundary_append_19 by assumption.
  rewrite count_occ_app_19.
  assert (Hzero :
    count_occ list_Z_eq_dec_19
      match token with
      | [] => []
      | _ => [token]
      end (number_word_z digit) = 0%nat).
  {
    destruct token as [| h token]; simpl; auto.
    apply (proj1 (count_occ_not_In list_Z_eq_dec_19 [h :: token]
      (number_word_z digit))).
    intros Hin.
    destruct Hin as [Hin | []].
    exact (Hneq Hin).
  }
  rewrite Hzero, Nat.add_0_r.
  reflexivity.
Qed.

Lemma count_word_boundary_append_hit_19 :
  forall digit prefix token,
    0 <= digit < 10 ->
    split_boundary_z prefix ->
    no_space_z_list_19 token ->
    token = number_word_z digit ->
    count_word_in_string digit (prefix ++ token) =
    count_word_in_string digit prefix + 1.
Proof.
  intros digit prefix token Hdigit Hboundary Hnospace Htok.
  unfold count_word_in_string.
  rewrite SplitOnSpacesZ_boundary_append_19 by assumption.
  rewrite count_occ_app_19.
  rewrite Htok.
  assert (Hcases:
    digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/ digit = 4 \/
    digit = 5 \/ digit = 6 \/ digit = 7 \/ digit = 8 \/ digit = 9) by lia.
  destruct Hcases as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
    subst digit; cbn;
    rewrite Nat2Z.inj_add; cbn; lia.
Qed.

Lemma count_word_append_space_end_19 :
  forall digit input,
    count_word_in_string digit (input ++ [32]) =
    count_word_in_string digit input.
Proof.
  intros digit input.
  unfold count_word_in_string.
  rewrite SplitOnSpacesZ_append_space_end_19.
  reflexivity.
Qed.

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

Definition output_used_capacity_prefix_z
  (digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Z :=
  let over :=
    output_capacity_prefix_z digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 in
  if Z.leb over 1 then 1 else over - 1.

Definition output_used_capacity_prefix_by_input_z
  (digit : Z) (input : list Z) : Z :=
  output_used_capacity_prefix_z digit
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

Definition scan_counts_capacity_z
  (i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  1
  + c0 * (number_word_len_z 0 + 1)
  + c1 * (number_word_len_z 1 + 1)
  + c2 * (number_word_len_z 2 + 1)
  + c3 * (number_word_len_z 3 + 1)
  + c4 * (number_word_len_z 4 + 1)
  + c5 * (number_word_len_z 5 + 1)
  + c6 * (number_word_len_z 6 + 1)
  + c7 * (number_word_len_z 7 + 1)
  + c8 * (number_word_len_z 8 + 1)
  + c9 * (number_word_len_z 9 + 1) <= 1 + 6 * i.

Definition scan_completed_prefix_z (i tlen : Z) (input : list Z) : list Z :=
  if Z.ltb tlen 31 then
    sublist 0 (Z.min (i - tlen) (Zlength input)) input
  else
    sublist 0 (Z.min (scan_word_start_z i input) (Zlength input)) input.

Definition scan_counts_exact_z
  (i tlen : Z) (input : list Z)
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  c0 = count_word_in_string 0 (scan_completed_prefix_z i tlen input) /\
  c1 = count_word_in_string 1 (scan_completed_prefix_z i tlen input) /\
  c2 = count_word_in_string 2 (scan_completed_prefix_z i tlen input) /\
  c3 = count_word_in_string 3 (scan_completed_prefix_z i tlen input) /\
  c4 = count_word_in_string 4 (scan_completed_prefix_z i tlen input) /\
  c5 = count_word_in_string 5 (scan_completed_prefix_z i tlen input) /\
  c6 = count_word_in_string 6 (scan_completed_prefix_z i tlen input) /\
  c7 = count_word_in_string 7 (scan_completed_prefix_z i tlen input) /\
  c8 = count_word_in_string 8 (scan_completed_prefix_z i tlen input) /\
  c9 = count_word_in_string 9 (scan_completed_prefix_z i tlen input).

Definition scan_counts_z
  (i : Z) (input : list Z)
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  0 <= i <= Zlength input + 1 /\
  0 <= c0 <= i /\ 0 <= c1 <= i /\
  0 <= c2 <= i /\ 0 <= c3 <= i /\
  0 <= c4 <= i /\ 0 <= c5 <= i /\
  0 <= c6 <= i /\ 0 <= c7 <= i /\
  0 <= c8 <= i /\ 0 <= c9 <= i /\
  scan_counts_capacity_z i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.

Lemma scan_word_start_nat_nonneg_19 :
  forall fuel input, 0 <= scan_word_start_nat fuel input.
Proof.
  induction fuel as [| fuel IH]; intros input; simpl; try lia.
  pose proof (Nat2Z.is_nonneg fuel).
  destruct (Z.eqb (scan_char_z (Z.of_nat fuel) input) 32).
  - lia.
  - apply IH.
Qed.

Lemma scan_word_start_nat_upper_19 :
  forall fuel input, scan_word_start_nat fuel input <= Z.of_nat fuel.
Proof.
  induction fuel as [| fuel IH]; intros input; simpl; try lia.
  pose proof (Nat2Z.is_nonneg fuel).
  destruct (Z.eqb (scan_char_z (Z.of_nat fuel) input) 32).
  - lia.
  - eapply Z.le_trans; [apply IH | lia].
Qed.

Lemma scan_word_start_z_nonneg_19 :
  forall i input, 0 <= scan_word_start_z i input.
Proof.
  intros i input. unfold scan_word_start_z.
  apply scan_word_start_nat_nonneg_19.
Qed.

Lemma scan_word_start_z_upper_19 :
  forall i input, 0 <= i -> scan_word_start_z i input <= i.
Proof.
  intros i input Hi. unfold scan_word_start_z.
  pose proof (scan_word_start_nat_upper_19 (Z.to_nat i) input).
  replace (Z.of_nat (Z.to_nat i)) with i in H by lia.
  exact H.
Qed.

Lemma scan_word_start_nat_no_space_19 :
  forall fuel input k,
    scan_word_start_nat fuel input <= k < Z.of_nat fuel ->
    scan_char_z k input <> 32.
Proof.
  induction fuel as [| fuel IH]; intros input k Hrange; simpl in *; try lia.
  destruct (Z.eqb_spec (scan_char_z (Z.of_nat fuel) input) 32) as [Hspace | Hnonspace].
  - lia.
  - destruct (Z.eq_dec k (Z.of_nat fuel)) as [-> | Hneq].
    + exact Hnonspace.
    + apply IH. lia.
Qed.

Lemma scan_word_start_no_space_19 :
  forall i input k,
    0 <= i ->
    scan_word_start_z i input <= k < i ->
    scan_char_z k input <> 32.
Proof.
  intros i input k Hi Hrange.
  unfold scan_word_start_z in *.
  replace i with (Z.of_nat (Z.to_nat i)) in Hrange by lia.
  replace (Z.to_nat (Z.of_nat (Z.to_nat i))) with (Z.to_nat i) in Hrange by lia.
  apply (scan_word_start_nat_no_space_19 (Z.to_nat i) input k).
  exact Hrange.
Qed.

Lemma scan_word_start_nat_prev_space_19 :
  forall fuel input,
    0 < scan_word_start_nat fuel input ->
    scan_char_z (scan_word_start_nat fuel input - 1) input = 32.
Proof.
  induction fuel as [| fuel IH]; intros input Hpos; simpl in *; try lia.
  destruct (Z.eqb_spec (scan_char_z (Z.of_nat fuel) input) 32) as [Hspace | Hnonspace].
  - replace (Z.of_nat fuel + 1 - 1) with (Z.of_nat fuel) by lia.
    exact Hspace.
  - apply IH. exact Hpos.
Qed.

Lemma scan_word_start_prev_space_19 :
  forall i input,
    0 <= i ->
    0 < scan_word_start_z i input ->
    scan_char_z (scan_word_start_z i input - 1) input = 32.
Proof.
  intros i input Hi Hpos.
  unfold scan_word_start_z in *.
  apply scan_word_start_nat_prev_space_19.
  exact Hpos.
Qed.

Lemma scan_word_start_prefix_boundary_19 :
  forall i input,
    0 <= i ->
    i <= Zlength input ->
    split_boundary_z (sublist 0 (scan_word_start_z i input) input).
Proof.
  intros i input Hi Hilen.
  pose proof (scan_word_start_z_nonneg_19 i input) as Hs_nonneg.
  pose proof (scan_word_start_z_upper_19 i input Hi) as Hs_upper.
  destruct (Z.eq_dec (scan_word_start_z i input) 0) as [Hzero | Hnonzero].
  - left. rewrite Hzero. rewrite Zsublist_nil by lia. reflexivity.
  - right.
    exists (sublist 0 (scan_word_start_z i input - 1) input).
    assert (Hprev_scan :
      scan_char_z (scan_word_start_z i input - 1) input = 32).
    { apply scan_word_start_prev_space_19; lia. }
    assert (Hprev_z :
      Znth (scan_word_start_z i input - 1) input 0 = 32).
    {
      unfold scan_char_z in Hprev_scan.
      destruct (Z.ltb_spec (scan_word_start_z i input - 1) (Zlength input));
        [exact Hprev_scan | lia].
    }
    replace (sublist 0 (scan_word_start_z i input) input) with
      (sublist 0 (scan_word_start_z i input - 1) input ++
       sublist (scan_word_start_z i input - 1)
         (scan_word_start_z i input - 1 + 1) input).
    2: {
      replace (scan_word_start_z i input - 1 + 1) with
        (scan_word_start_z i input) by lia.
      symmetry.
      apply sublist_split; lia.
    }
    rewrite (@sublist_single Z 0 (scan_word_start_z i input - 1) input) by lia.
    rewrite Hprev_z.
    reflexivity.
Qed.

Lemma scan_word_start_sublist_no_space_19 :
  forall i input hi,
    0 <= i ->
    scan_word_start_z i input <= hi <= i ->
    hi <= Zlength input ->
    no_space_z_list_19 (sublist (scan_word_start_z i input) hi input).
Proof.
  unfold no_space_z_list_19.
  intros i input hi Hi Hbounds Hhi x Hin Hx.
  destruct (In_nth (sublist (scan_word_start_z i input) hi input) x 0 Hin)
    as [n [Hn Hnth]].
  assert (0 <= Z.of_nat n < Zlength (sublist (scan_word_start_z i input) hi input))
    as Hnz by (rewrite Zlength_correct; lia).
  assert (x = Znth (Z.of_nat n)
    (sublist (scan_word_start_z i input) hi input) 0) as Hxnth.
  {
    unfold Znth. rewrite Nat2Z.id. symmetry. exact Hnth.
  }
  rewrite Hxnth in Hx.
  pose proof (scan_word_start_z_nonneg_19 i input).
  pose proof (scan_word_start_z_upper_19 i input Hi).
  rewrite Znth_sublist in Hx by (rewrite Zlength_sublist in Hnz by lia; lia).
  exfalso.
  apply (scan_word_start_no_space_19 i input (scan_word_start_z i input + Z.of_nat n));
    try lia.
  rewrite Zlength_sublist in Hnz by lia.
  lia.
  unfold scan_char_z.
  destruct (Z.ltb_spec (scan_word_start_z i input + Z.of_nat n) (Zlength input)).
  - replace (scan_word_start_z i input + Z.of_nat n) with
      (Z.of_nat n + scan_word_start_z i input) by lia.
    exact Hx.
  - rewrite Zlength_sublist in Hnz by lia.
    lia.
Qed.

Lemma number_word_z_length_le_5_19 :
  forall digit, 0 <= digit < 10 -> Zlength (number_word_z digit) <= 5.
Proof.
  intros digit Hdigit.
  assert (digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/
          digit = 4 \/ digit = 5 \/ digit = 6 \/ digit = 7 \/
          digit = 8 \/ digit = 9) as Hcases by lia.
  destruct Hcases as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    rewrite Zlength_correct; simpl; lia.
Qed.

Lemma token_prefix_zero_z_19 :
  forall i input, token_prefix_z i 0 input = [].
Proof.
  intros i input.
  unfold token_prefix_z.
  destruct (Z.ltb_spec 0 31) as [_ | Hbad]; try lia.
  replace (i - 0) with i by lia.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.

Lemma scan_completed_prefix_finish_unsat_eq_19 :
  forall i tlen input,
    0 <= i <= Zlength input ->
    0 <= tlen ->
    tlen <= i ->
    tlen < 31 ->
    scan_char_z i input = 32 ->
    scan_completed_prefix_z (i + 1) 0 input =
      scan_completed_prefix_z i tlen input ++
      token_prefix_z i tlen input ++
      if Z.ltb i (Zlength input) then [32] else [].
Proof.
  intros i tlen input Hi Htlen Hti Hlt Hscan.
  unfold scan_completed_prefix_z, token_prefix_z.
  destruct (Z.ltb_spec 0 31) as [_ | Hbad0]; try lia.
  destruct (Z.ltb_spec tlen 31) as [_ | Hbad]; try lia.
  destruct (Z.ltb_spec i (Zlength input)) as [Hilen | Hige].
  - replace (Z.min (i + 1 - 0) (Zlength input)) with (i + 1) by lia.
    replace (Z.min (i - tlen) (Zlength input)) with (i - tlen) by lia.
    rewrite (@sublist_split Z 0 (i + 1) i input) by lia.
    rewrite (@sublist_split Z 0 i (i - tlen) input) by lia.
    rewrite (@sublist_single Z 0 i input) by lia.
    unfold scan_char_z in Hscan.
    destruct (Z.ltb_spec i (Zlength input)) as [_ | Hbad]; try lia.
    rewrite Hscan.
    rewrite app_assoc.
    reflexivity.
  - replace (Z.min (i + 1 - 0) (Zlength input)) with (Zlength input) by lia.
    replace i with (Zlength input) by lia.
    replace (Z.min (Zlength input - tlen) (Zlength input)) with
      (Zlength input - tlen) by lia.
    rewrite (@sublist_split Z 0 (Zlength input) (Zlength input - tlen) input)
      by lia.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma scan_completed_prefix_finish_sat_eq_19 :
  forall i tlen input,
    0 <= i <= Zlength input ->
    31 <= tlen ->
    scan_char_z i input = 32 ->
    scan_completed_prefix_z (i + 1) 0 input =
      scan_completed_prefix_z i tlen input ++
      sublist (scan_word_start_z i input) i input ++
      if Z.ltb i (Zlength input) then [32] else [].
Proof.
  intros i tlen input Hi Hsat Hscan.
  pose proof (scan_word_start_z_nonneg_19 i input) as Hstart_nonneg.
  pose proof (scan_word_start_z_upper_19 i input ltac:(lia)) as Hstart_upper.
  unfold scan_completed_prefix_z.
  destruct (Z.ltb_spec 0 31) as [_ | Hbad0]; try lia.
  destruct (Z.ltb_spec tlen 31) as [Hbad | _]; try lia.
  replace (Z.min (scan_word_start_z i input) (Zlength input))
    with (scan_word_start_z i input) by lia.
  destruct (Z.ltb_spec i (Zlength input)) as [Hilen | Hige].
  - replace (Z.min (i + 1 - 0) (Zlength input)) with (i + 1) by lia.
    rewrite (@sublist_split Z 0 (i + 1) i input) by lia.
    rewrite (@sublist_split Z 0 i (scan_word_start_z i input) input) by lia.
    rewrite (@sublist_single Z 0 i input) by lia.
    unfold scan_char_z in Hscan.
    destruct (Z.ltb_spec i (Zlength input)) as [_ | Hbad]; try lia.
    rewrite Hscan.
    rewrite app_assoc.
    reflexivity.
  - replace (Z.min (i + 1 - 0) (Zlength input)) with (Zlength input) by lia.
    replace i with (Zlength input) by lia.
    pose proof (scan_word_start_z_nonneg_19 (Zlength input) input).
    pose proof (scan_word_start_z_upper_19 (Zlength input) input ltac:(lia)).
    rewrite (@sublist_split Z 0 (Zlength input) (scan_word_start_z (Zlength input) input) input)
      by lia.
    rewrite app_nil_r.
    reflexivity.
Qed.

Lemma list_Z_eq_by_Znth_19 :
  forall l1 l2,
    Zlength l1 = Zlength l2 ->
    (forall k, 0 <= k < Zlength l1 -> Znth k l1 0 = Znth k l2 0) ->
    l1 = l2.
Proof.
  induction l1 as [| a l1 IH]; destruct l2 as [| b l2];
    intros Hlen Hnth; try reflexivity.
  - rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg l2). lia.
  - rewrite Zlength_nil, Zlength_cons in Hlen.
    pose proof (Zlength_nonneg l1). lia.
  - assert (Ha : a = b).
    {
      specialize (Hnth 0).
      rewrite !Znth0_cons in Hnth.
      apply Hnth.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg l1). lia.
    }
    subst b.
    f_equal.
    apply IH.
    + rewrite !Zlength_cons in Hlen. lia.
    + intros k Hk.
      specialize (Hnth (k + 1)).
      rewrite !Znth_cons in Hnth by lia.
      replace (k + 1 - 1) with k in Hnth by lia.
      apply Hnth.
      rewrite Zlength_cons.
      lia.
Qed.

Lemma strcmp_result_zero_eq_valid_19 :
  forall s1 s2,
    string_lib.valid_string s1 ->
    string_lib.valid_string s2 ->
    strcmp_result s1 s2 0 ->
    s1 = s2.
Proof.
  intros s1 s2 Hvalid1 Hvalid2 Hcmp.
  unfold strcmp_result in Hcmp.
  destruct Hcmp as [idx [Hidx1 [Hidx2 [Hprefix [Hret Hstop]]]]].
  destruct Hidx1 as [Hidx0 Hidx1_le].
  pose proof Hidx2 as Hidx2_le.
  assert (Hchar_eq :
    Znth idx (string_lib.c_string s1) 0 =
    Znth idx (string_lib.c_string s2) 0).
  {
    assert (Hdiff :
      Znth idx (string_lib.c_string s1) 0 -
      Znth idx (string_lib.c_string s2) 0 = 0)
      by (symmetry; exact Hret).
    lia.
  }
  destruct Hstop as [Hzero | Hneq].
  - assert (Hlen1 : idx = string_lib.string_length s1).
    {
      eapply c_string_zero_index_eq_length;
        [exact Hvalid1 | exact Hidx0 | exact Hidx1_le | exact Hzero].
    }
    assert (Hlen2 : idx = string_lib.string_length s2).
    {
      eapply c_string_zero_index_eq_length;
        [exact Hvalid2 | exact Hidx0 | exact Hidx2_le |].
      rewrite <- Hchar_eq. exact Hzero.
    }
    apply list_Z_eq_by_Znth_19.
    + unfold string_lib.string_length in *. lia.
    + intros k Hk.
      replace (Znth k s1 0) with (Znth k (string_lib.c_string s1) 0)
        by (apply string_lib.c_string_Znth_inside;
            unfold string_lib.string_length in *; lia).
      replace (Znth k s2 0) with (Znth k (string_lib.c_string s2) 0)
        by (apply string_lib.c_string_Znth_inside;
            unfold string_lib.string_length in *; lia).
      apply Hprefix. unfold string_lib.string_length in *. lia.
  - contradiction.
Qed.

Lemma Znth_replace_Znth_same_coins_19 :
  forall {A} (d0 : A) (l : list A) (i : Z) (v : A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i v l) d0 = v.
Proof.
  intros A d0 l i v Hi.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  rewrite Zlength_correct in Hi.
  assert (0 <= m < List.length l)%nat by lia.
  clearbody m. clear Hi i.
  generalize dependent m.
  induction l; simpl; intros; try lia.
  destruct m; simpl; auto.
  apply IHl; lia.
Qed.

Lemma Znth_replace_Znth_diff_coins_19 :
  forall {A} (d0 : A) (l : list A) (i j : Z) (v : A),
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    Znth j (replace_Znth i v l) d0 = Znth j l d0.
Proof.
  intros A d0 l i j v Hi Hj Hneq.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  set (n := Z.to_nat j).
  rewrite Zlength_correct in Hi, Hj.
  assert (0 <= m < List.length l)%nat by lia.
  assert (0 <= n < List.length l)%nat by lia.
  assert (m <> n) by lia.
  clearbody m n. clear Hi Hj Hneq i j.
  generalize dependent n.
  generalize dependent m.
  induction l; simpl; intros; try lia.
  destruct m, n; simpl; auto; try lia.
  apply IHl; lia.
Qed.

Lemma scan_count_word_finish_miss_19 :
  forall i tlen input digit,
    0 <= i <= Zlength input ->
    0 <= tlen < 32 ->
    tlen <= i ->
    scan_char_z i input = 32 ->
    Zlength (token_prefix_z i tlen input) = tlen ->
    token_empty_start_z i tlen input ->
    (tlen < 31 -> token_unsat_end_z i tlen input) ->
    token_sat_start_z i tlen input ->
    token_miss_prefix_z 10 (token_prefix_z i tlen input) ->
    0 <= digit < 10 ->
    count_word_in_string digit (scan_completed_prefix_z (i + 1) 0 input) =
    count_word_in_string digit (scan_completed_prefix_z i tlen input).
Proof.
  intros i tlen input digit Hi Htlen Hti Hscan Htok_len Hempty Hunsat
    Hsat Hmiss Hdigit.
  destruct (Z.eq_dec tlen 0) as [Htlen0 | Htlen_nonzero].
  - subst tlen.
    rewrite (scan_completed_prefix_finish_unsat_eq_19 i 0 input);
      try lia; try exact Hscan.
    rewrite token_prefix_zero_z_19.
    destruct (Z.ltb i (Zlength input)).
    + apply count_word_append_space_end_19.
    + rewrite app_nil_r. reflexivity.
  - destruct (Z.ltb_spec tlen 31) as [Htlt | Htge].
    + assert (Hend : token_unsat_end_z i tlen input) by (apply Hunsat; lia).
      assert (Hstart : scan_word_start_z i input + tlen = i).
      {
        unfold token_unsat_end_z in Hend.
        destruct Hend as [Hzero | Hend]; [lia | exact Hend].
      }
      rewrite (scan_completed_prefix_finish_unsat_eq_19 i tlen input);
        try lia; try exact Hscan.
      replace (i - tlen) with (scan_word_start_z i input) by lia.
      assert (Hboundary :
        split_boundary_z (scan_completed_prefix_z i tlen input)).
      {
        unfold scan_completed_prefix_z.
        destruct (Z.ltb_spec tlen 31) as [_ | Hbad]; try lia.
        replace (Z.min (i - tlen) (Zlength input)) with
          (scan_word_start_z i input) by lia.
        apply scan_word_start_prefix_boundary_19; lia.
      }
      assert (Hnospace :
        no_space_z_list_19 (token_prefix_z i tlen input)).
      {
        unfold token_prefix_z.
        destruct (Z.ltb_spec tlen 31) as [_ | Hbad]; try lia.
        replace (i - tlen) with (scan_word_start_z i input) by lia.
        apply scan_word_start_sublist_no_space_19; lia.
      }
      rewrite app_assoc.
      destruct (Z.ltb i (Zlength input)).
      * rewrite count_word_append_space_end_19.
        apply count_word_boundary_append_nohit_19; try assumption.
        apply Hmiss. lia.
      * rewrite app_nil_r.
        apply count_word_boundary_append_nohit_19; try assumption.
        apply Hmiss. lia.
    + assert (Htlen31 : tlen = 31) by lia; subst tlen.
      rewrite (scan_completed_prefix_finish_sat_eq_19 i 31 input);
        try lia; try exact Hscan.
      set (group := sublist (scan_word_start_z i input) i input).
      assert (Hboundary :
        split_boundary_z (scan_completed_prefix_z i 31 input)).
      {
        unfold scan_completed_prefix_z.
        destruct (Z.ltb_spec 31 31) as [Hbad | _]; try lia.
        replace (Z.min (scan_word_start_z i input) (Zlength input)) with
          (scan_word_start_z i input).
        - apply scan_word_start_prefix_boundary_19; lia.
        - pose proof (scan_word_start_z_upper_19 i input ltac:(lia)); lia.
      }
      assert (Hnospace : no_space_z_list_19 group).
      {
        unfold group.
        pose proof (scan_word_start_z_nonneg_19 i input).
        pose proof (scan_word_start_z_upper_19 i input ltac:(lia)).
        apply scan_word_start_sublist_no_space_19; lia.
      }
      assert (Hgroup_len : 31 <= Zlength group).
      {
        unfold group.
        rewrite Zlength_sublist by
          (pose proof (scan_word_start_z_nonneg_19 i input);
           pose proof (scan_word_start_z_upper_19 i input ltac:(lia)); lia).
        unfold token_sat_start_z in Hsat.
        specialize (Hsat ltac:(lia)).
        lia.
      }
      assert (Hgroup_neq : group <> number_word_z digit).
      {
        intro Heq.
        pose proof (f_equal (@Zlength Z) Heq) as Hlen_eq.
        rewrite Hlen_eq in Hgroup_len.
        pose proof (number_word_z_length_le_5_19 digit Hdigit).
        lia.
      }
      rewrite app_assoc.
      destruct (Z.ltb i (Zlength input)).
      * rewrite count_word_append_space_end_19.
        apply count_word_boundary_append_nohit_19; assumption.
      * rewrite app_nil_r.
        apply count_word_boundary_append_nohit_19; assumption.
Qed.

Lemma scan_count_word_finish_token_eq_19 :
  forall i tlen input matched digit,
    0 <= i <= Zlength input ->
    0 <= tlen < 32 ->
    tlen <= i ->
    scan_char_z i input = 32 ->
    Zlength (token_prefix_z i tlen input) = tlen ->
    string_lib.valid_string (token_prefix_z i tlen input) ->
    string_lib.valid_string (number_word_z matched) ->
    token_empty_start_z i tlen input ->
    (tlen < 31 -> token_unsat_end_z i tlen input) ->
    strcmp_result (token_prefix_z i tlen input) (number_word_z matched) 0 ->
    0 <= matched < 10 ->
    0 <= digit < 10 ->
    count_word_in_string digit (scan_completed_prefix_z (i + 1) 0 input) =
    count_word_in_string digit (scan_completed_prefix_z i tlen input) +
      (if Z.eq_dec digit matched then 1 else 0).
Proof.
  intros i tlen input matched digit Hi Htlen Hti Hscan Htok_len
    Htok_valid Hword_valid Hempty Hunsat Hcmp Hmatched Hdigit.
  assert (Htok_eq :
    token_prefix_z i tlen input = number_word_z matched).
  {
    eapply strcmp_result_zero_eq_valid_19; eauto.
  }
  assert (Htlt : tlen < 31).
  {
    rewrite Htok_eq in Htok_len.
    pose proof (number_word_z_length_le_5_19 matched Hmatched).
    lia.
  }
  assert (Htlen_nonzero : tlen <> 0).
  {
    intro Hz.
    rewrite Htok_eq in Htok_len.
    subst tlen.
    pose proof (number_word_z_nonempty_19 matched Hmatched).
    destruct_digit_cases_19 matched; cbn in *; lia.
  }
  assert (Hend : token_unsat_end_z i tlen input) by (apply Hunsat; lia).
  assert (Hstart : scan_word_start_z i input + tlen = i).
  {
    unfold token_unsat_end_z in Hend.
    destruct Hend as [Hzero | Hend]; [contradiction | exact Hend].
  }
  rewrite (scan_completed_prefix_finish_unsat_eq_19 i tlen input);
    try lia; try exact Hscan.
  replace (i - tlen) with (scan_word_start_z i input) by lia.
  assert (Hboundary :
    split_boundary_z (scan_completed_prefix_z i tlen input)).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec tlen 31) as [_ | Hbad]; try lia.
    replace (Z.min (i - tlen) (Zlength input)) with
      (scan_word_start_z i input) by lia.
    apply scan_word_start_prefix_boundary_19; lia.
  }
  assert (Hnospace :
    no_space_z_list_19 (token_prefix_z i tlen input)).
  {
    unfold token_prefix_z.
    destruct (Z.ltb_spec tlen 31) as [_ | Hbad]; try lia.
    replace (i - tlen) with (scan_word_start_z i input) by lia.
    apply scan_word_start_sublist_no_space_19; lia.
  }
  rewrite app_assoc.
  destruct (Z.ltb i (Zlength input)).
  - rewrite count_word_append_space_end_19.
    destruct (Z.eq_dec digit matched) as [Heq | Hneq].
    + subst digit.
      apply count_word_boundary_append_hit_19; try assumption.
    + replace (count_word_in_string digit (scan_completed_prefix_z i tlen input) +
        0) with (count_word_in_string digit (scan_completed_prefix_z i tlen input))
        by lia.
      apply count_word_boundary_append_nohit_19; try assumption.
      rewrite Htok_eq.
      apply number_word_z_neq_19; lia.
  - rewrite app_nil_r.
    destruct (Z.eq_dec digit matched) as [Heq | Hneq].
    + subst digit.
      apply count_word_boundary_append_hit_19; try assumption.
    + replace (count_word_in_string digit (scan_completed_prefix_z i tlen input) +
        0) with (count_word_in_string digit (scan_completed_prefix_z i tlen input))
        by lia.
      apply count_word_boundary_append_nohit_19; try assumption.
      rewrite Htok_eq.
      apply number_word_z_neq_19; lia.
Qed.

Lemma scan_counts_exact_finish_hit_19 :
  forall i tlen input cnts matched,
    Zlength cnts = 10 ->
    0 <= i <= Zlength input ->
    0 <= tlen < 32 ->
    tlen <= i ->
    scan_char_z i input = 32 ->
    Zlength (token_prefix_z i tlen input) = tlen ->
    string_lib.valid_string (token_prefix_z i tlen input) ->
    string_lib.valid_string (number_word_z matched) ->
    token_empty_start_z i tlen input ->
    (tlen < 31 -> token_unsat_end_z i tlen input) ->
    strcmp_result (token_prefix_z i tlen input) (number_word_z matched) 0 ->
    0 <= matched < 10 ->
    scan_counts_exact_z i tlen input
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_exact_z (i + 1) 0 input
      (Znth 0 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 1 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 2 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 3 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 4 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 5 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 6 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 7 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 8 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0)
      (Znth 9 (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0).
Proof.
  intros i tlen input cnts matched Hcnts_len Hi Htlen Hti Hscan Htok_len
    Htok_valid Hword_valid Hempty Hunsat Hcmp Hmatched Hexact.
  unfold scan_counts_exact_z in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  assert (Hold : forall digit,
    0 <= digit < 10 ->
    Znth digit cnts 0 =
      count_word_in_string digit (scan_completed_prefix_z i tlen input)).
  {
    intros digit Hd.
    destruct_digit_cases_19 digit; assumption.
  }
  assert (Hnew : forall digit,
    0 <= digit < 10 ->
    Znth digit (replace_Znth matched (Znth matched cnts 0 + 1) cnts) 0 =
      count_word_in_string digit (scan_completed_prefix_z (i + 1) 0 input)).
  {
    intros digit Hd.
    destruct (Z.eq_dec digit matched) as [Heq | Hneq].
    - subst digit.
      rewrite Znth_replace_Znth_same_coins_19 by lia.
      rewrite Hold by lia.
      rewrite (scan_count_word_finish_token_eq_19 i tlen input matched matched)
        by (try assumption; try lia).
      destruct (Z.eq_dec matched matched); lia.
    - rewrite Znth_replace_Znth_diff_coins_19 by lia.
      rewrite Hold by lia.
      rewrite (scan_count_word_finish_token_eq_19 i tlen input matched digit)
        by (try assumption; try lia).
      destruct (Z.eq_dec digit matched); lia.
  }
  repeat split; apply Hnew; lia.
Qed.

Lemma scan_counts_exact_finish_miss_19 :
  forall i tlen input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    0 <= i <= Zlength input ->
    0 <= tlen < 32 ->
    tlen <= i ->
    scan_char_z i input = 32 ->
    Zlength (token_prefix_z i tlen input) = tlen ->
    token_empty_start_z i tlen input ->
    (tlen < 31 -> token_unsat_end_z i tlen input) ->
    token_sat_start_z i tlen input ->
    token_miss_prefix_z 10 (token_prefix_z i tlen input) ->
    scan_counts_exact_z i tlen input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
    scan_counts_exact_z (i + 1) 0 input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.
Proof.
  intros i tlen input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    Hi Htlen Hti Hscan Htok_len Hempty Hunsat Hsat Hmiss Hexact.
  unfold scan_counts_exact_z in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat split;
    match goal with
    | H : ?c = count_word_in_string ?d (scan_completed_prefix_z i tlen input)
      |- ?c = count_word_in_string ?d (scan_completed_prefix_z (i + 1) 0 input) =>
        rewrite H; symmetry;
        apply scan_count_word_finish_miss_19; try assumption; lia
    end.
Qed.

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
