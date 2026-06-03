Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic CommonAssertion.
From SimpleC.EE Require Import C_19_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_19.
Require Import number_words_19_strategy_proof.
Local Open Scope sac.

Lemma number_word_len_z_plus_one_nonneg_for_digit :
  forall i, 0 <= i < 10 -> 0 <= number_word_len_z i + 1.
Proof.
  intros i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hdigit by lia.
  destruct Hdigit as [Hdigit | [Hdigit | [Hdigit | [Hdigit | [Hdigit |
    [Hdigit | [Hdigit | [Hdigit | [Hdigit | Hdigit]]]]]]]]];
    subst; cbn; lia.
Qed.

Lemma zeros_snoc :
  forall i, 0 <= i -> zeros (i + 1) = List.app (zeros i) (0 :: nil).
Proof.
  intros.
  unfold zeros.
  replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
  rewrite repeat_app.
  reflexivity.
Qed.

Ltac split_scan_counts :=
  unfold scan_counts_z in *;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Ltac destruct_digit i :=
  let Hdigit := fresh "Hdigit" in
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hdigit by lia;
  destruct Hdigit as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
  subst.

Ltac solve_char_full_init :=
  intros; unfold number_word_z, number_word_len_z, CharArray.full; cbn; entailer!.

Lemma w0_full_init : forall w,
  ((w + 4 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 111) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 114) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 122)
  |-- CharArray.full w 5 (number_word_z 0 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w1_full_init : forall w,
  ((w + 3 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 110) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 111)
  |-- CharArray.full w 4 (number_word_z 1 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w2_full_init : forall w,
  ((w + 3 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 111) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 119) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 116)
  |-- CharArray.full w 4 (number_word_z 2 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w3_full_init : forall w,
  ((w + 5 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 4 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 114) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 104) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 116)
  |-- CharArray.full w 6 (number_word_z 3 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w4_full_init : forall w,
  ((w + 4 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 114) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 117) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 111) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 102)
  |-- CharArray.full w 5 (number_word_z 4 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w5_full_init : forall w,
  ((w + 4 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 118) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 105) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 102)
  |-- CharArray.full w 5 (number_word_z 5 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w6_full_init : forall w,
  ((w + 3 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 120) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 105) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 115)
  |-- CharArray.full w 4 (number_word_z 6 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w7_full_init : forall w,
  ((w + 5 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 4 * sizeof(CHAR)) # Char |-> 110) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 118) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 115)
  |-- CharArray.full w 6 (number_word_z 7 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w8_full_init : forall w,
  ((w + 5 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 4 * sizeof(CHAR)) # Char |-> 116) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 104) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 103) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 105) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 101)
  |-- CharArray.full w 6 (number_word_z 8 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma w9_full_init : forall w,
  ((w + 4 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 3 * sizeof(CHAR)) # Char |-> 101) **
  ((w + 2 * sizeof(CHAR)) # Char |-> 110) **
  ((w + 1 * sizeof(CHAR)) # Char |-> 105) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 110)
  |-- CharArray.full w 5 (number_word_z 9 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma space_word_full_init : forall w,
  ((w + 1 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 32)
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma ptr_words_mixed_init_full :
  forall words l w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
  SingleSome l 0 (w0 + 0 * sizeof(CHAR)) ->
  PtrArray.mixed_full words 10
    (replace_Znth 9 (Some (w9 + 0 * sizeof(CHAR)))
    (replace_Znth 8 (Some (w8 + 0 * sizeof(CHAR)))
    (replace_Znth 7 (Some (w7 + 0 * sizeof(CHAR)))
    (replace_Znth 6 (Some (w6 + 0 * sizeof(CHAR)))
    (replace_Znth 5 (Some (w5 + 0 * sizeof(CHAR)))
    (replace_Znth 4 (Some (w4 + 0 * sizeof(CHAR)))
    (replace_Znth 3 (Some (w3 + 0 * sizeof(CHAR)))
    (replace_Znth 2 (Some (w2 + 0 * sizeof(CHAR)))
    (replace_Znth 1 (Some (w1 + 0 * sizeof(CHAR))) l)))))))))
  |-- PtrArray.full words 10
        (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9).
Proof.
  intros.
  unfold SingleSome in H; subst.
  repeat match goal with
  | |- context [?x + 0 * sizeof(CHAR)] =>
      replace (x + 0 * sizeof(CHAR)) with x by lia
  end.
  unfold PtrArray.mixed_full, ptr_mixed_seg, ptr_mixed_store,
         PtrArray.full, number_word_ptrs_z, store_array.
  cbn.
  repeat change (Pos.to_nat 9) with 9%nat.
  repeat change (Pos.to_nat 8) with 8%nat.
  repeat change (Pos.to_nat 7) with 7%nat.
  repeat change (Pos.to_nat 6) with 6%nat.
  repeat change (Pos.to_nat 5) with 5%nat.
  repeat change (Pos.to_nat 4) with 4%nat.
  repeat change (Pos.to_nat 3) with 3%nat.
  repeat change (Pos.to_nat 2) with 2%nat.
  repeat change (Pos.to_nat 1) with 1%nat.
  cbn.
  repeat match goal with
  | |- context [?x + 0] => replace (x + 0) with x by lia
  end.
  entailer!.
Qed.

Lemma number_words_full_init : forall words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
  number_words_chars_full_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
  PtrArray.full words 10 (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
  |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_full.
  entailer!.
Qed.

Lemma number_words_full_init_rev : forall words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
  CharArray.full w9 5 (number_word_z 9 ++ 0 :: nil) **
  CharArray.full w8 6 (number_word_z 8 ++ 0 :: nil) **
  CharArray.full w7 6 (number_word_z 7 ++ 0 :: nil) **
  CharArray.full w6 4 (number_word_z 6 ++ 0 :: nil) **
  CharArray.full w5 5 (number_word_z 5 ++ 0 :: nil) **
  CharArray.full w4 5 (number_word_z 4 ++ 0 :: nil) **
  CharArray.full w3 6 (number_word_z 3 ++ 0 :: nil) **
  CharArray.full w2 4 (number_word_z 2 ++ 0 :: nil) **
  CharArray.full w1 4 (number_word_z 1 ++ 0 :: nil) **
  CharArray.full w0 5 (number_word_z 0 ++ 0 :: nil) **
  PtrArray.full words 10 (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
  |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_full, number_words_chars_full_z.
  entailer!.
Qed.

Lemma number_words_full_init_ptr_rev : forall words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
  PtrArray.full words 10 (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) **
  CharArray.full w9 5 (number_word_z 9 ++ 0 :: nil) **
  CharArray.full w8 6 (number_word_z 8 ++ 0 :: nil) **
  CharArray.full w7 6 (number_word_z 7 ++ 0 :: nil) **
  CharArray.full w6 4 (number_word_z 6 ++ 0 :: nil) **
  CharArray.full w5 5 (number_word_z 5 ++ 0 :: nil) **
  CharArray.full w4 5 (number_word_z 4 ++ 0 :: nil) **
  CharArray.full w3 6 (number_word_z 3 ++ 0 :: nil) **
  CharArray.full w2 4 (number_word_z 2 ++ 0 :: nil) **
  CharArray.full w1 4 (number_word_z 1 ++ 0 :: nil) **
  CharArray.full w0 5 (number_word_z 0 ++ 0 :: nil)
  |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_full, number_words_chars_full_z.
  entailer!.
Qed.

Lemma Znth_10_len10_default :
  forall l : list Z, Zlength l = 10 -> Znth 10 l 0 = 0.
Proof.
  intros l Hl.
  rewrite Zlength_correct in Hl.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *; try lia.
  destruct l; cbn in *.
  - unfold Znth; cbn; reflexivity.
  - lia.
Qed.

Lemma number_words_missing_merge :
  forall words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    word = Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0 ->
    ((words + d * sizeof(PTR)) # Ptr |-> word) **
    number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
    CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil)
    |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  subst word.
  unfold number_words_missing, number_words_full.
  sep_apply (PtrArray.missing_i_merge_to_full words d 10
    (Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0)
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9));
    [ | lia ].
  rewrite replace_Znth_Znth.
  destruct_digit d; subst;
    unfold number_words_chars_full_z, number_words_chars_missing_z,
      number_word_ptrs_z in *; cbn [Znth] in *;
    asrt_simpl_pure;
    try change (CharArray.full w0 (number_word_len_z 0 + 1)
      (number_word_z 0 ++ 0 :: nil)) with (number_word_char_full_z w0 0);
    try change (CharArray.full w1 (number_word_len_z 1 + 1)
      (number_word_z 1 ++ 0 :: nil)) with (number_word_char_full_z w1 1);
    try change (CharArray.full w2 (number_word_len_z 2 + 1)
      (number_word_z 2 ++ 0 :: nil)) with (number_word_char_full_z w2 2);
    try change (CharArray.full w3 (number_word_len_z 3 + 1)
      (number_word_z 3 ++ 0 :: nil)) with (number_word_char_full_z w3 3);
    try change (CharArray.full w4 (number_word_len_z 4 + 1)
      (number_word_z 4 ++ 0 :: nil)) with (number_word_char_full_z w4 4);
    try change (CharArray.full w5 (number_word_len_z 5 + 1)
      (number_word_z 5 ++ 0 :: nil)) with (number_word_char_full_z w5 5);
    try change (CharArray.full w6 (number_word_len_z 6 + 1)
      (number_word_z 6 ++ 0 :: nil)) with (number_word_char_full_z w6 6);
    try change (CharArray.full w7 (number_word_len_z 7 + 1)
      (number_word_z 7 ++ 0 :: nil)) with (number_word_char_full_z w7 7);
    try change (CharArray.full w8 (number_word_len_z 8 + 1)
      (number_word_z 8 ++ 0 :: nil)) with (number_word_char_full_z w8 8);
    try change (CharArray.full w9 (number_word_len_z 9 + 1)
      (number_word_z 9 ++ 0 :: nil)) with (number_word_char_full_z w9 9);
    cancel; entailer!.
Qed.

Lemma number_words_missing_merge_vc :
  forall words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    word = Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0 ->
    CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil) **
    number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
    ((words + d * sizeof(PTR)) # Ptr |-> word)
    |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  subst word.
  unfold number_words_missing, number_words_full.
  sep_apply (PtrArray.missing_i_merge_to_full words d 10
    (Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0)
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9));
    [ | lia ].
  rewrite replace_Znth_Znth.
  destruct_digit d; subst;
    unfold number_words_chars_full_z, number_words_chars_missing_z,
      number_word_ptrs_z in *; cbn [Znth] in *;
    asrt_simpl_pure;
    try change (CharArray.full w0 (number_word_len_z 0 + 1)
      (number_word_z 0 ++ 0 :: nil)) with (number_word_char_full_z w0 0);
    try change (CharArray.full w1 (number_word_len_z 1 + 1)
      (number_word_z 1 ++ 0 :: nil)) with (number_word_char_full_z w1 1);
    try change (CharArray.full w2 (number_word_len_z 2 + 1)
      (number_word_z 2 ++ 0 :: nil)) with (number_word_char_full_z w2 2);
    try change (CharArray.full w3 (number_word_len_z 3 + 1)
      (number_word_z 3 ++ 0 :: nil)) with (number_word_char_full_z w3 3);
    try change (CharArray.full w4 (number_word_len_z 4 + 1)
      (number_word_z 4 ++ 0 :: nil)) with (number_word_char_full_z w4 4);
    try change (CharArray.full w5 (number_word_len_z 5 + 1)
      (number_word_z 5 ++ 0 :: nil)) with (number_word_char_full_z w5 5);
    try change (CharArray.full w6 (number_word_len_z 6 + 1)
      (number_word_z 6 ++ 0 :: nil)) with (number_word_char_full_z w6 6);
    try change (CharArray.full w7 (number_word_len_z 7 + 1)
      (number_word_z 7 ++ 0 :: nil)) with (number_word_char_full_z w7 7);
    try change (CharArray.full w8 (number_word_len_z 8 + 1)
      (number_word_z 8 ++ 0 :: nil)) with (number_word_char_full_z w8 8);
    try change (CharArray.full w9 (number_word_len_z 9 + 1)
      (number_word_z 9 ++ 0 :: nil)) with (number_word_char_full_z w9 9);
    cancel; entailer!.
Qed.

Lemma Znth_replace_Znth_same_19 :
  forall {A} (d0 : A) (l : list A) (i : Z) (v : A),
    0 <= i < Zlength l ->
    Znth i (replace_Znth i v l) d0 = v.
Proof.
  intros A d0 l i v Hi.
  unfold Znth, replace_Znth.
  set (m := Z.to_nat i).
  rewrite Zlength_correct in Hi.
  assert (0 <= m < length l)%nat by lia.
  clearbody m. clear Hi i.
  generalize dependent m.
  induction l; simpl; intros; try lia.
  destruct m; simpl; auto.
  apply IHl; lia.
Qed.

Lemma Znth_replace_Znth_diff_19 :
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
  assert (0 <= m < length l)%nat by lia.
  assert (0 <= n < length l)%nat by lia.
  assert (m <> n) by lia.
  clearbody m n. clear Hi Hj Hneq i j.
  generalize dependent n.
  generalize dependent m.
  induction l; simpl; intros; try lia.
  destruct m, n; simpl; auto; try lia.
  apply IHl; lia.
Qed.

Lemma Zlength_replace_Znth_19 :
  forall {A} (l : list A) (n : Z) (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  f_equal.
  generalize (Z.to_nat n) as m.
  induction l; intros m; destruct m; simpl; try rewrite IHl; reflexivity.
Qed.

Lemma scan_counts_replace_inc :
  forall i input cnts d,
    Zlength cnts = 10 ->
    0 <= d < 10 ->
    i <= Zlength input ->
    scan_counts_z i input
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_z (i + 1) input
      (Znth 0 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 1 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 2 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 3 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 4 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 5 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 6 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 7 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 8 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0)
      (Znth 9 (replace_Znth d (Znth d cnts 0 + 1) cnts) 0).
Proof.
  intros i input cnts d Hlen Hd Hi Hscan.
  unfold scan_counts_z in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat split; try lia;
    match goal with
    | |- context[Znth ?k (replace_Znth d _ cnts) 0] =>
        destruct (Z.eq_dec k d) as [Heq | Hneq];
        [subst; rewrite Znth_replace_Znth_same_19 by lia
        | rewrite Znth_replace_Znth_diff_19 by lia];
        lia
    end.
Qed.

Lemma scan_counts_step :
  forall i input cnts,
    i <= Zlength input ->
    scan_counts_z i input
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_z (i + 1) input
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0).
Proof.
  intros i input cnts Hi Hscan.
  unfold scan_counts_z in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat split; lia.
Qed.

Lemma scan_word_start_step_nonspace :
  forall i l,
    0 <= i ->
    scan_char_z i l <> 32 ->
    scan_word_start_z (i + 1) l = scan_word_start_z i l.
Proof.
  intros i l Hi Hch.
  unfold scan_word_start_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (Z.eqb_spec (scan_char_z i l) 32); congruence.
Qed.

Lemma scan_word_start_step_space :
  forall i l,
    0 <= i ->
    scan_char_z i l = 32 ->
    scan_word_start_z (i + 1) l = i + 1.
Proof.
  intros i l Hi Hch.
  unfold scan_word_start_z.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite Hch.
  reflexivity.
Qed.

Lemma token_empty_start_after_inc_z :
  forall i tlen l,
    0 <= tlen ->
    token_empty_start_z (i + 1) (tlen + 1) l.
Proof.
  intros i tlen l Htlen.
  unfold token_empty_start_z.
  intros Hempty.
  lia.
Qed.

Lemma token_unsat_end_extend_z :
  forall i tlen l,
    0 <= i ->
    0 <= tlen ->
    tlen < 31 ->
    token_empty_start_z i tlen l ->
    token_unsat_end_z i tlen l ->
    scan_char_z i l <> 32 ->
    tlen + 1 < 31 ->
    token_unsat_end_z (i + 1) (tlen + 1) l.
Proof.
  intros i tlen l Hi Htlen Hlt Hempty Hend Hch Hnext.
  unfold token_unsat_end_z in *.
  destruct (Z.eq_dec tlen 0) as [Hzero | Hpos].
  - subst tlen.
    unfold token_empty_start_z in Hempty.
    right.
    rewrite scan_word_start_step_nonspace by lia.
    specialize (Hempty ltac:(reflexivity)).
    lia.
  - destruct Hend as [Hzero | Hend]; try lia.
    right.
    rewrite scan_word_start_step_nonspace by lia.
    lia.
Qed.

Lemma token_prefix_extend_z :
  forall i tlen l,
    0 <= i < Zlength l ->
    0 <= tlen ->
    tlen < 31 ->
    tlen <= i ->
    token_unsat_end_z i tlen l ->
    scan_char_z i l <> 32 ->
    token_prefix_z (i + 1) (tlen + 1) l =
    List.app (token_prefix_z i tlen l) (Znth i (List.app l (0 :: nil)) 0 :: nil).
Proof.
  intros i tlen l Hi Htlen Htlt Hti Hend Hch.
  rewrite Zlength_correct in Hi.
  unfold token_prefix_z.
  destruct (Z.ltb_spec (tlen + 1) 31) as [Hnew | Hnew].
  - destruct (Z.ltb_spec tlen 31) as [Hold | Hold]; try lia.
    replace (i + 1 - (tlen + 1)) with (i - tlen) by lia.
    pose proof (@sublist_split Z (i - tlen) (i + 1) i l
      ltac:(lia) ltac:(lia)) as Hsplit.
    rewrite Hsplit; clear Hsplit.
    rewrite (sublist_single i l 0) by lia.
    rewrite app_Znth1 by (rewrite Zlength_correct; lia).
    reflexivity.
  - assert (tlen = 30) by lia; subst tlen.
    destruct (Z.ltb_spec 30 31) as [_ | Hbad]; try lia.
    unfold token_unsat_end_z in Hend.
    destruct Hend as [Hzero | Hend]; try lia.
    rewrite scan_word_start_step_nonspace by lia.
    set (s := scan_word_start_z i l) in *.
    replace (s + (30 + 1)) with (i + 1) by lia.
    replace s with (i - 30) by lia.
    pose proof (@sublist_split Z (i - 30) (i + 1) i l
      ltac:(lia) ltac:(lia)) as Hsplit.
    rewrite Hsplit; clear Hsplit.
    rewrite (sublist_single i l 0) by lia.
    rewrite app_Znth1 by (rewrite Zlength_correct; lia).
    reflexivity.
Qed.

Lemma token_prefix_zero_z :
  forall i l, token_prefix_z i 0 l = nil.
Proof.
  intros i l.
  unfold token_prefix_z.
  destruct (Z.ltb_spec 0 31) as [_ | Hbad]; try lia.
  replace (i - 0) with i by lia.
  rewrite sublist_nil by lia.
  reflexivity.
Qed.

Lemma token_prefix_empty_step_z :
  forall i tlen l,
    0 <= tlen ->
    tlen <= 0 ->
    token_prefix_z (i + 1) tlen l = token_prefix_z i tlen l /\
    Zlength (token_prefix_z (i + 1) tlen l) = tlen /\
    token_unsat_end_z (i + 1) tlen l.
Proof.
  intros i tlen l Hnonneg Hempty.
  assert (Htlen : tlen = 0) by lia.
  subst tlen.
  repeat split; rewrite ?token_prefix_zero_z; try reflexivity.
  unfold token_unsat_end_z; left; reflexivity.
Qed.

Lemma token_prefix_saturated_step_z :
  forall i tlen l,
    0 <= i ->
    31 <= tlen ->
    scan_char_z i l <> 32 ->
    token_prefix_z (i + 1) tlen l = token_prefix_z i tlen l.
Proof.
  intros i tlen l Hi Hsat Hch.
  unfold token_prefix_z.
  destruct (Z.ltb_spec tlen 31) as [Hlt | Hge]; try lia.
  rewrite scan_word_start_step_nonspace by lia.
  reflexivity.
Qed.

Lemma proof_of_sort_numbers_safety_wit_155 : sort_numbers_safety_wit_155.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_safety_wit_172 : sort_numbers_safety_wit_172.
Proof.
  pre_process; entailer!; try lia.
  pose proof (number_word_len_z_plus_one_nonneg_for_digit i ltac:(lia)).
  nia.
Qed. 

Lemma proof_of_sort_numbers_safety_wit_173 : sort_numbers_safety_wit_173.
Proof.
  pre_process; entailer!; try lia.
  pose proof (number_word_len_z_plus_one_nonneg_for_digit i ltac:(lia)).
  nia.
Qed. 

Lemma proof_of_sort_numbers_safety_wit_186 : sort_numbers_safety_wit_186.
Proof.
  pre_process; entailer!; try lia.
  split_scan_counts; destruct_digit i; lia.
Qed. 

Lemma proof_of_sort_numbers_safety_wit_187 : sort_numbers_safety_wit_187.
Proof.
  pre_process; entailer!; try lia.
  split_scan_counts; destruct_digit i; lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_1 : sort_numbers_entail_wit_1.
Proof.
  pre_process; subst.
  match goal with
  | Hsingle : SingleSome l_2 0 _ |- _ =>
      sep_apply (ptr_words_mixed_init_full (&( "words")) l_2
        (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
        (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))
        Hsingle)
  end.
  sep_apply (w9_full_init (&( "w9"))).
  sep_apply (w8_full_init (&( "w8"))).
  sep_apply (w7_full_init (&( "w7"))).
  sep_apply (w6_full_init (&( "w6"))).
  sep_apply (w5_full_init (&( "w5"))).
  sep_apply (w4_full_init (&( "w4"))).
  sep_apply (w3_full_init (&( "w3"))).
  sep_apply (w2_full_init (&( "w2"))).
  sep_apply (w1_full_init (&( "w1"))).
  sep_apply (w0_full_init (&( "w0"))).
  sep_apply (number_words_full_init_ptr_rev (&( "words")) (&( "w0")) (&( "w1"))
    (&( "w2")) (&( "w3")) (&( "w4")) (&( "w5")) (&( "w6")) (&( "w7"))
    (&( "w8")) (&( "w9"))).
  sep_apply (space_word_full_init retval).
  sep_apply (IntArray.undef_full_split_to_undef_seg (&( "count")) 0 10); [ | lia ].
  unfold number_word_len_z, number_word_z, zeros.
  cbn.
  unfold IntArray.seg, IntArray.undef_seg.
  cbn.
  entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_2 : sort_numbers_entail_wit_2.
Proof.
  pre_process.
  rewrite zeros_snoc by lia.
  sep_apply (IntArray.seg_single (&( "count")) i 0).
  sep_apply (IntArray.seg_merge_to_seg (&( "count")) 0 i (i + 1)
    (zeros i) (0 :: nil)).
  entailer!; try lia.
  lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_3 : sort_numbers_entail_wit_3.
Proof.
  pre_process; subst.
  assert (i = 10) by lia; subst i.
  Exists (zeros 10).
  sep_apply (CharArray.undef_full_split_to_undef_seg token 0 32); [ | lia ].
  sep_apply (IntArray.seg_to_full (&( "count")) 0 10 (zeros 10)).
  rewrite token_prefix_zero_z.
  unfold CharArray.full at 2.
  cbn.
  replace (&( "count") + 0) with (&( "count")) by lia.
  unfold scan_counts_z.
  entailer!; try lia;
    unfold zeros in *; cbn in *; try lia.
  all: try rewrite nth_repeat; try lia.
  intros _; unfold token_unsat_end_z; left; reflexivity.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_4_1 : sort_numbers_entail_wit_4_1.
Proof.
  pre_process.
  Exists cnts_2.
  split_scan_counts.
  entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_4_2 : sort_numbers_entail_wit_4_2.
Proof.
  pre_process.
  Exists cnts_2.
  split_scan_counts.
  entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_5 : sort_numbers_entail_wit_5.
Proof.
  pre_process.
  Exists cnts_2.
  cancel.
  sep_apply (number_words_missing_merge_vc
    (&( "words")) d
    (Znth d (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") :: &( "w4") ::
      &( "w5") :: &( "w6") :: &( "w7") :: &( "w8") :: &( "w9") :: nil) 0)
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))).
  split_scan_counts.
  destruct_digit d; cbn in *; try (entailer!; lia).
  rewrite (Znth_10_len10_default cnts_2) by lia.
  entailer!; lia.
  unfold number_word_ptrs_z; reflexivity.
  lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_1 : sort_numbers_entail_wit_6_1.
Proof.
  pre_process.
  Exists (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2).
  sep_apply (number_words_missing_merge_vc
    (&( "words")) d
    (Znth d (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") :: &( "w4") ::
      &( "w5") :: &( "w6") :: &( "w7") :: &( "w8") :: &( "w9") :: nil) 0)
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))).
  sep_apply (CharArray.full_to_undef_full token (tlen + 1)
    (token_prefix_z i tlen l ++ 0 :: nil)).
  sep_apply (CharArray.undef_full_to_undef_seg token (tlen + 1)).
  sep_apply (CharArray.undef_seg_merge_to_undef_seg token 0 (tlen + 1) 32);
    try lia.
  assert (Hscan_update: scan_counts_z (i + 1) l
      (Znth 0 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 1 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 2 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 3 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 4 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 5 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 6 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 7 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 8 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
      (Znth 9 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)).
  {
    apply scan_counts_replace_inc; try assumption; lia.
  }
  assert (Hcnts_update_len:
      Zlength (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) = 10).
  {
    rewrite Zlength_replace_Znth_19; lia.
  }
  rewrite token_prefix_zero_z.
  destruct_digit d; cbn in *;
    try (entailer!; try lia; intros _; unfold token_unsat_end_z; left; reflexivity).
  all: try (entailer!; try lia; intros _; unfold token_unsat_end_z; left; reflexivity).
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_2 : sort_numbers_entail_wit_6_2.
Proof.
  pre_process.
  Exists cnts_2.
  sep_apply (CharArray.full_to_undef_full token (tlen + 1)
    (token_prefix_z i tlen l ++ 0 :: nil)).
  sep_apply (CharArray.undef_full_to_undef_seg token (tlen + 1)).
  sep_apply (CharArray.undef_seg_merge_to_undef_seg token 0 (tlen + 1) 32);
    try lia.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  rewrite token_prefix_zero_z.
  entailer!; try lia; try (intros _; unfold token_unsat_end_z; left; reflexivity).
  unfold CharArray.full; cbn; entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_3 : sort_numbers_entail_wit_6_3.
Proof.
  pre_process.
  Exists cnts_2.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  pose proof (token_prefix_empty_step_z i tlen l ltac:(lia) ltac:(lia))
    as (Htoken_step & Htoken_len & Htoken_unsat).
  rewrite Htoken_step.
  entailer!; try lia; try (intros _; unfold token_unsat_end_z; left; reflexivity).
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_4 : sort_numbers_entail_wit_6_4.
Proof.
  pre_process.
  Exists cnts_2.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  pose proof (token_prefix_empty_step_z i tlen l ltac:(lia) ltac:(lia))
    as (Htoken_step & Htoken_len & Htoken_unsat).
  rewrite Htoken_step.
  entailer!; try lia; try (intros _; unfold token_unsat_end_z; left; reflexivity).
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_5 : sort_numbers_entail_wit_6_5.
Proof.
  pre_process.
  Exists cnts_2.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hscan_char_nonspace: scan_char_z i l <> 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)); try lia.
    match goal with
    | Hnz : Znth i (l ++ 0 :: nil) 0 <> 32 |- _ =>
        rewrite app_Znth1 in Hnz by lia; exact Hnz
    end.
  }
  rewrite (token_prefix_extend_z i tlen l) by (try lia; auto).
  assert (Htoken_empty_next:
      token_empty_start_z (i + 1) (tlen + 1) l).
  {
    apply token_empty_start_after_inc_z; lia.
  }
  assert (Htoken_unsat_next:
      tlen + 1 < 31 -> token_unsat_end_z (i + 1) (tlen + 1) l).
  {
    intros Hnext.
    apply token_unsat_end_extend_z; try lia; auto.
    - match goal with
      | H : token_empty_start_z i tlen l |- _ => exact H
      end.
    - match goal with
      | H : tlen < 31 -> token_unsat_end_z i tlen l |- _ =>
          apply H; lia
      end.
  }
  entailer!; try lia.
  all: try solve [
    rewrite Zlength_app; rewrite Zlength_cons; rewrite Zlength_nil; lia
  ].
  all: try solve [exact Htoken_empty_next].
  all: try solve [exact Htoken_unsat_next].
  all: try solve [
    rewrite app_Znth1 by lia;
    match goal with
    | Hr : ascii_range_z l |- _ =>
        unfold ascii_range_z in Hr; specialize (Hr i ltac:(lia)); lia
    end
  ].
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6_6 : sort_numbers_entail_wit_6_6.
Proof.
  pre_process.
  Exists cnts_2.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hscan_char_nonspace: scan_char_z i l <> 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)); try lia.
    match goal with
    | Hnz : Znth i (l ++ 0 :: nil) 0 <> 32 |- _ =>
        rewrite app_Znth1 in Hnz by lia; exact Hnz
    end.
  }
  rewrite (token_prefix_saturated_step_z i tlen l) by (try lia; auto).
  entailer!; try lia.
  all: try solve [
    rewrite app_Znth1 by lia;
    unfold ascii_range_z in H8;
    specialize (H8 i ltac:(lia)); lia
  ].
Qed. 

Lemma proof_of_sort_numbers_entail_wit_7 : sort_numbers_entail_wit_7.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_8 : sort_numbers_entail_wit_8.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_9 : sort_numbers_entail_wit_9.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_10 : sort_numbers_entail_wit_10.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_1 : sort_numbers_entail_wit_11_1.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_2 : sort_numbers_entail_wit_11_2.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_12 : sort_numbers_entail_wit_12.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_13 : sort_numbers_entail_wit_13.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_return_wit_1 : sort_numbers_return_wit_1.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_partial_solve_wit_71_pure : sort_numbers_partial_solve_wit_71_pure.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_partial_solve_wit_78_pure : sort_numbers_partial_solve_wit_78_pure.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_partial_solve_wit_83_pure : sort_numbers_partial_solve_wit_83_pure.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_partial_solve_wit_84_pure : sort_numbers_partial_solve_wit_84_pure.
Proof.
  pre_process; entailer!; try lia.
Qed. 

Lemma proof_of_sort_numbers_partial_solve_wit_85_pure : sort_numbers_partial_solve_wit_85_pure.
Proof.
  pre_process; entailer!; try lia.
Qed. 
