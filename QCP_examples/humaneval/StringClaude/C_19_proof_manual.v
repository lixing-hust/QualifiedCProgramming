Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_19_goal.
From SimpleC.EE Require Import C_19_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_19.
Local Open Scope sac.

Lemma sepcon_tail_comm_19 :
  forall P Q R : Assertion, P ** (Q ** R) |-- P ** (R ** Q).
Proof.
  intros.
  rewrite (logic_equiv_sepcon_comm Q R).
  apply derivable1_refl.
Qed.

Lemma sepcon_rotate_left_19 :
  forall P Q R : Assertion, P ** (Q ** R) |-- Q ** (R ** P).
Proof.
  intros.
  rewrite (logic_equiv_sepcon_swap P Q R).
  rewrite (logic_equiv_sepcon_comm P R).
  apply derivable1_refl.
Qed.

Ltac rotate_sepcon_left_top_19 :=
  match goal with
  | |- (?A ** ?B) ** ?C |-- _ =>
      rewrite <- (logic_equiv_sepcon_assoc A B C);
      rewrite (logic_equiv_sepcon_swap A B C);
      rewrite (logic_equiv_sepcon_comm A C)
  | |- ?A ** (?B ** ?C) |-- _ =>
      rewrite (logic_equiv_sepcon_swap A B C);
      rewrite (logic_equiv_sepcon_comm A C)
  end.

Ltac sepcon_tail_comm_top_19 :=
  match goal with
  | |- (?P ** ?Q) ** ?R |-- _ =>
      rewrite <- (logic_equiv_sepcon_assoc P Q R);
      rewrite (logic_equiv_sepcon_comm Q R)
  | |- ?P ** (?Q ** ?R) |-- _ =>
      rewrite (logic_equiv_sepcon_comm Q R)
  end.


Lemma zeros_snoc :
  forall i, 0 <= i -> zeros (i + 1) = List.app (zeros i) (0 :: nil).
Proof.
  intros.
  unfold zeros.
  replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
  rewrite repeat_app.
  reflexivity.
Qed.

Lemma Zlength_zeros_19 :
  forall n, 0 <= n -> Zlength (zeros n) = n.
Proof.
  intros.
  unfold zeros.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.

Lemma Znth_zeros_19 :
  forall n i, 0 <= i < n -> Znth i (zeros n) 0 = 0.
Proof.
  intros.
  unfold zeros.
  rewrite Znth_repeat by lia.
  reflexivity.
Qed.

Lemma token_prefix_zero_z :
  forall i l, token_prefix_z i 0 l = nil.
Proof.
  intros i l.
  unfold token_prefix_z.
  destruct (Z.ltb_spec 0 31) as [_ | Hbad]; try lia.
  replace (i - 0) with i by lia.
  rewrite Zsublist_nil by lia.
  reflexivity.
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

Lemma scan_word_start_after_end_z :
  forall l, scan_word_start_z (Zlength l + 1) l = Zlength l + 1.
Proof.
  intros l.
  apply scan_word_start_step_space.
  - apply Zlength_nonneg.
  - unfold scan_char_z.
    destruct (Z.ltb_spec (Zlength l) (Zlength l)); lia.
Qed.

Lemma token_prefix_after_end_zero_z :
  forall i tlen l,
    i = Zlength l + 1 ->
    0 <= tlen ->
    tlen < 32 ->
    Zlength (token_prefix_z i tlen l) = tlen ->
    tlen = 0.
Proof.
  intros i tlen l Hi Htlen Hlt Hlen.
  subst i.
  unfold token_prefix_z in Hlen.
  destruct (Z.ltb_spec tlen 31) as [Hunsat | Hsat].
  - rewrite Zlength_sublist' in Hlen.
    rewrite Zlength_correct in Hlen.
    assert (Hmin:
      Init.Nat.min (Z.to_nat (Z.of_nat (length l) + 1)) (length l) =
      length l) by lia.
    rewrite Hmin in Hlen.
    destruct (Z.eq_dec tlen 0) as [-> | Hnz]; auto.
    assert (1 <= tlen) by lia.
    lia.
  - assert (Ht31: tlen = 31) by lia; subst tlen.
    rewrite scan_word_start_after_end_z in Hlen.
    rewrite Zlength_sublist' in Hlen.
    rewrite Zlength_correct in Hlen.
    assert (Hmin:
      Init.Nat.min (Z.to_nat (Z.of_nat (length l) + 1 + 31)) (length l) =
      length l) by lia.
    rewrite Hmin in Hlen.
    lia.
Qed.

Lemma token_empty_start_after_inc_z :
  forall i tlen l,
    0 <= i ->
    0 <= tlen ->
    scan_word_start_z i l + tlen = i ->
    scan_char_z i l <> 32 ->
    token_empty_start_z (i + 1) (tlen + 1) l.
Proof.
  intros i tlen l Hi Htlen Hend Hch.
  unfold token_empty_start_z.
  intros Hempty.
  lia.
Qed.

Lemma token_unsat_end_extend_z :
  forall i tlen l,
    0 <= i < Zlength l ->
    0 <= tlen ->
    tlen < 31 ->
    scan_word_start_z i l + tlen = i ->
    scan_char_z i l <> 32 ->
    tlen + 1 < 31 ->
    token_unsat_end_z (i + 1) (tlen + 1) l.
Proof.
  intros i tlen l Hi Htlen Hlt Hend Hch Hnext.
  unfold token_unsat_end_z in *.
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
  unfold token_prefix_z.
  destruct (Z.ltb_spec (tlen + 1) 31) as [Hnew | Hnew].
  - destruct (Z.ltb_spec tlen 31) as [Hold | Hold]; try lia.
    replace (i + 1 - (tlen + 1)) with (i - tlen) by lia.
    pose proof (@sublist_split Z (i - tlen) (i + 1) i l
      ltac:(lia) ltac:(lia)) as Hsplit.
    rewrite Hsplit; clear Hsplit.
    rewrite (@sublist_single Z 0 i l) by lia.
    rewrite app_Znth1 by lia.
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
    rewrite (@sublist_single Z 0 i l) by lia.
    rewrite app_Znth1 by lia.
    reflexivity.
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

Lemma valid_string_token_prefix_snoc_19 :
  forall i l prefix,
    0 <= i < Zlength l ->
    valid_string l ->
    valid_string prefix ->
    valid_string (List.app prefix (Znth i (List.app l (0 :: nil)) 0 :: nil)).
Proof.
  intros i l prefix Hi Hvalid_l Hvalid_prefix.
  unfold valid_string, all_ascii, no_inner_nul in *.
  destruct Hvalid_l as [Hascii_l Hnul_l].
  destruct Hvalid_prefix as [Hascii_prefix Hnul_prefix].
  split; intros k Hk;
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk;
    destruct (Z_lt_ge_dec k (Zlength prefix)) as [Hleft | Hright].
  - rewrite app_Znth1 by lia.
    apply Hascii_prefix; lia.
  - assert (k = Zlength prefix) by lia; subst k.
    rewrite app_Znth2 by lia.
    replace (Zlength prefix - Zlength prefix) with 0 by lia.
    rewrite app_Znth1 by lia.
    apply Hascii_l; lia.
  - rewrite app_Znth1 by lia.
    apply Hnul_prefix; lia.
  - assert (k = Zlength prefix) by lia; subst k.
    rewrite app_Znth2 by lia.
    replace (Zlength prefix - Zlength prefix) with 0 by lia.
    rewrite app_Znth1 by lia.
    apply Hnul_l; lia.
Qed.

Lemma number_word_zero_valid_19 :
  (valid_string (number_word_z 0) /\
   string_length (number_word_z 0) = number_word_len_z 0) /\
  string_length (number_word_z 0) < INT_MAX.
Proof.
  split.
  - split.
    + unfold valid_string, all_ascii, no_inner_nul, number_word_z.
      split.
      * intros k Hk.
        change (Zlength (122 :: 101 :: 114 :: 111 :: nil)) with 4 in Hk.
        assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as Hcases by lia.
        destruct Hcases as [H0 | [H1 | [H2 | H3]]].
        -- subst k. change (0 <= 122 <= 127). lia.
        -- subst k. change (0 <= 101 <= 127). lia.
        -- subst k. change (0 <= 114 <= 127). lia.
        -- subst k. change (0 <= 111 <= 127). lia.
      * intros k Hk.
        change (Zlength (122 :: 101 :: 114 :: 111 :: nil)) with 4 in Hk.
        assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as Hcases by lia.
        destruct Hcases as [H0 | [H1 | [H2 | H3]]].
        -- subst k. change (122 <> 0). lia.
        -- subst k. change (101 <> 0). lia.
        -- subst k. change (114 <> 0). lia.
        -- subst k. change (111 <> 0). lia.
    + unfold string_length, number_word_len_z, number_word_z; cbn; reflexivity.
  - unfold string_length, number_word_z; cbn; lia.
Qed.

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

Lemma number_words_chars_full_init_rev : forall w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
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
  |-- number_words_chars_full_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_chars_full_z, number_word_char_full_z.
  entailer!.
Qed.

Ltac fold_number_words_chars_from_raw_19 :=
  sep_apply (w9_full_init (&( "w9" )));
  sep_apply (w8_full_init (&( "w8" )));
  sep_apply (w7_full_init (&( "w7" )));
  sep_apply (w6_full_init (&( "w6" )));
  sep_apply (w5_full_init (&( "w5" )));
  sep_apply (w4_full_init (&( "w4" )));
  sep_apply (w3_full_init (&( "w3" )));
  sep_apply (w2_full_init (&( "w2" )));
  sep_apply (w1_full_init (&( "w1" )));
  sep_apply (w0_full_init (&( "w0" )));
  sep_apply (number_words_chars_full_init_rev
    (&( "w0" )) (&( "w1" )) (&( "w2" )) (&( "w3" )) (&( "w4" ))
    (&( "w5" )) (&( "w6" )) (&( "w7" )) (&( "w8" )) (&( "w9" ))).

Lemma space_word_full_init : forall w,
  ((w + 1 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 32)
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil).
Proof. solve_char_full_init. Qed.

Lemma space_word_full_with_undef_19 : forall w,
  CharArray.undef_seg w (1 + 1) 3 **
  ((w + 1 * sizeof(CHAR)) # Char |-> 0) **
  ((w + 0 * sizeof(CHAR)) # Char |-> 32)
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil) **
      CharArray.undef_seg w (number_word_len_z 10 + 1) 3.
Proof.
  intros.
  rewrite <- (logic_equiv_sepcon_assoc
    (CharArray.undef_seg w (1 + 1) 3)
    ((w + 1 * sizeof(CHAR)) # Char |-> 0)
    ((w + 0 * sizeof(CHAR)) # Char |-> 32)).
  rewrite (logic_equiv_sepcon_swap
    (CharArray.undef_seg w (1 + 1) 3)
    ((w + 1 * sizeof(CHAR)) # Char |-> 0)
    ((w + 0 * sizeof(CHAR)) # Char |-> 32)).
  rewrite (logic_equiv_sepcon_comm
    (CharArray.undef_seg w (1 + 1) 3)
    ((w + 0 * sizeof(CHAR)) # Char |-> 32)).
  sep_apply (space_word_full_init w).
  unfold number_word_len_z, number_word_z.
  cbn.
  entailer!.
Qed.

Lemma space_word_full_with_undef_frame_19 : forall w R,
  CharArray.undef_seg w (1 + 1) 3 **
  (((w + 1 * sizeof(CHAR)) # Char |-> 0) **
   (((w + 0 * sizeof(CHAR)) # Char |-> 32) ** R))
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil) **
      (CharArray.undef_seg w (number_word_len_z 10 + 1) 3 ** R).
Proof.
  intros.
  rewrite (logic_equiv_sepcon_assoc
    (CharArray.undef_seg w (1 + 1) 3)
    ((w + 1 * sizeof(CHAR)) # Char |-> 0)
    (((w + 0 * sizeof(CHAR)) # Char |-> 32) ** R)).
  rewrite (logic_equiv_sepcon_assoc
    (CharArray.undef_seg w (1 + 1) 3 **
     ((w + 1 * sizeof(CHAR)) # Char |-> 0))
    ((w + 0 * sizeof(CHAR)) # Char |-> 32)
    R).
  sep_apply (space_word_full_init w).
  unfold number_word_len_z, number_word_z.
  cbn.
  entailer!.
Qed.

Lemma space_word_full_with_undef_pair_frame_19 : forall w R,
  CharArray.undef_seg w (1 + 1) 3 **
  ((((w + 1 * sizeof(CHAR)) # Char |-> 0) **
    ((w + 0 * sizeof(CHAR)) # Char |-> 32)) ** R)
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil) **
      (CharArray.undef_seg w (number_word_len_z 10 + 1) 3 ** R).
Proof.
  intros.
  rewrite (logic_equiv_sepcon_assoc
    (CharArray.undef_seg w (1 + 1) 3)
    (((w + 1 * sizeof(CHAR)) # Char |-> 0) **
     ((w + 0 * sizeof(CHAR)) # Char |-> 32))
    R).
  sep_apply (space_word_full_with_undef_19 w).
  entailer!.
Qed.

Lemma space_word_full_with_undef_mid_frame_19 : forall w R,
  (CharArray.undef_seg w (1 + 1) 3 **
   (((w + 1 * sizeof(CHAR)) # Char |-> 0) **
    ((w + 0 * sizeof(CHAR)) # Char |-> 32))) ** R
  |-- CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil) **
      (CharArray.undef_seg w (number_word_len_z 10 + 1) 3 ** R).
Proof.
  intros.
  sep_apply (space_word_full_with_undef_19 w).
  entailer!.
Qed.

Lemma space_word_full_with_undef_outer_frame_19 : forall NW w R,
  NW **
  ((CharArray.undef_seg w (1 + 1) 3 **
    (((w + 1 * sizeof(CHAR)) # Char |-> 0) **
     ((w + 0 * sizeof(CHAR)) # Char |-> 32))) ** R)
  |-- NW **
      (CharArray.full w (number_word_len_z 10 + 1) (number_word_z 10 ++ 0 :: nil) **
       (CharArray.undef_seg w (number_word_len_z 10 + 1) 3 ** R)).
Proof.
  intros.
  sepcon_lift (CharArray.undef_seg w (1 + 1) 3).
  sepcon_lift ((w + 0 * sizeof(CHAR)) # Char |-> 32).
  sepcon_lift ((w + 1 * sizeof(CHAR)) # Char |-> 0).
  unfold number_word_len_z, number_word_z, CharArray.full.
  cbn.
  cancel.
  entailer!.
Qed.

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

Lemma ptr_words_cells_full_init :
  forall words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
  ((words + 9 * sizeof(PTR)) # Ptr |-> (w9 + 0 * sizeof(CHAR))) **
  ((words + 8 * sizeof(PTR)) # Ptr |-> (w8 + 0 * sizeof(CHAR))) **
  ((words + 7 * sizeof(PTR)) # Ptr |-> (w7 + 0 * sizeof(CHAR))) **
  ((words + 6 * sizeof(PTR)) # Ptr |-> (w6 + 0 * sizeof(CHAR))) **
  ((words + 5 * sizeof(PTR)) # Ptr |-> (w5 + 0 * sizeof(CHAR))) **
  ((words + 4 * sizeof(PTR)) # Ptr |-> (w4 + 0 * sizeof(CHAR))) **
  ((words + 3 * sizeof(PTR)) # Ptr |-> (w3 + 0 * sizeof(CHAR))) **
  ((words + 2 * sizeof(PTR)) # Ptr |-> (w2 + 0 * sizeof(CHAR))) **
  ((words + 1 * sizeof(PTR)) # Ptr |-> (w1 + 0 * sizeof(CHAR))) **
  ((words + 0 * sizeof(PTR)) # Ptr |-> (w0 + 0 * sizeof(CHAR)))
  |-- PtrArray.full words 10
        (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9).
Proof.
  intros.
  rewrite sizeof_ptr.
  rewrite sizeof_char.
  unfold PtrArray.full, number_word_ptrs_z, store_array.
  repeat rewrite sizeof_ptr.
  repeat rewrite sizeof_char.
  cbn.
  repeat match goal with
  | |- context [?x + 0 * sizeof(CHAR)] =>
      replace (x + 0 * sizeof(CHAR)) with x by lia
  | |- context [?x + 0 * sizeof(PTR)] =>
      replace (x + 0 * sizeof(PTR)) with x by lia
  | |- context [?x + 0] =>
      replace (x + 0) with x by lia
  end.
  entailer!.
Qed.

Ltac split_scan_counts :=
  unfold scan_counts_z, scan_counts_capacity_z in *;
  unfold number_word_len_z, number_word_z in *; simpl in *;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.

Lemma scan_counts_digit_bound_19 :
  forall n input cnts idx,
    Zlength cnts = 10 ->
    0 <= idx < 10 ->
    scan_counts_z n input
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= Znth idx cnts 0 <= n.
Proof.
  intros n input cnts idx _ Hidx Hscan.
  unfold scan_counts_z, scan_counts_capacity_z in Hscan.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  assert (idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4 \/
          idx = 5 \/ idx = 6 \/ idx = 7 \/ idx = 8 \/ idx = 9)
    as Hcases by lia.
  destruct Hcases as
    [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
    subst; lia.
Qed.

Ltac change_number_word_lengths_19 :=
  change (Zlength (122 :: 101 :: 114 :: 111 :: nil)) with 4 in *;
  change (Zlength (111 :: 110 :: 101 :: nil)) with 3 in *;
  change (Zlength (116 :: 119 :: 111 :: nil)) with 3 in *;
  change (Zlength (116 :: 104 :: 114 :: 101 :: 101 :: nil)) with 5 in *;
  change (Zlength (102 :: 111 :: 117 :: 114 :: nil)) with 4 in *;
  change (Zlength (102 :: 105 :: 118 :: 101 :: nil)) with 4 in *;
  change (Zlength (115 :: 105 :: 120 :: nil)) with 3 in *;
  change (Zlength (115 :: 101 :: 118 :: 101 :: 110 :: nil)) with 5 in *;
  change (Zlength (101 :: 105 :: 103 :: 104 :: 116 :: nil)) with 5 in *;
  change (Zlength (110 :: 105 :: 110 :: 101 :: nil)) with 4 in *.

Lemma scan_counts_capacity_step_19 :
  forall i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    scan_counts_capacity_z i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
    scan_counts_capacity_z (i + 1) c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.
Proof.
  intros.
  unfold scan_counts_capacity_z, number_word_len_z, number_word_z in *.
  change_number_word_lengths_19.
  lia.
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
  unfold scan_counts_z, scan_counts_capacity_z in *.
  unfold number_word_len_z, number_word_z in *; simpl in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat match goal with
  | |- _ /\ _ => constructor
  end;
    try (eapply scan_counts_capacity_step_19; eassumption);
    lia.
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
  unfold scan_counts_z, scan_counts_capacity_z in *.
  unfold number_word_len_z, number_word_z in *.
  change_number_word_lengths_19.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  assert (Hd_cases:
    d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
    d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat match goal with
  | |- _ /\ _ => constructor
  end;
    try solve [
      destruct Hd_cases as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
      subst d;
      repeat rewrite Znth_replace_Znth_same_19 by lia;
      repeat rewrite Znth_replace_Znth_diff_19 by lia;
      change_number_word_lengths_19;
      lia
    ];
    lia.
Qed.

Ltac destruct_digit i :=
  let Hdigit := fresh "Hdigit" in
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
          i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hdigit by lia;
  destruct Hdigit as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
  subst.

Ltac solve_number_word_digit_valid :=
  unfold valid_string, all_ascii, no_inner_nul, string_length,
    number_word_len_z, number_word_z;
  cbn; repeat split; try reflexivity; try lia;
  repeat match goal with
  | |- forall idx : Z, _ =>
      intros idx Hidx
  | |- context [Z.to_nat ?idx] =>
      assert (idx = 0 \/ idx = 1 \/ idx = 2 \/ idx = 3 \/ idx = 4)
        as Hcases by lia;
      destruct Hcases as [? | [? | [? | [? | ?]]]]; subst; cbn in *; lia
  end; try lia.

Lemma number_word_valid_digit_19 :
  forall k,
    0 <= k < 10 ->
    (valid_string (number_word_z k) /\
     string_length (number_word_z k) = number_word_len_z k) /\
    string_length (number_word_z k) < INT_MAX.
Proof.
  intros k Hk.
  destruct_digit k;
    unfold valid_string, all_ascii, no_inner_nul, string_length,
      number_word_len_z, number_word_z;
    cbn; repeat split; try reflexivity; try lia.
  all: try (intros idx Hidx).
  all: try match goal with
    | Hidx : 0 <= ?idx < _ |- context [Z.to_nat ?idx] =>
        assert (Z.of_nat (Z.to_nat idx) = idx) as Hnat
      by (rewrite Z2Nat.id; lia);
        destruct (Z.to_nat idx) as [|[|[|[|[|n]]]]]; cbn in *; lia
  end.
Qed.

Lemma valid_string_app_19 :
  forall a b,
    valid_string a ->
    valid_string b ->
    valid_string (a ++ b).
Proof.
  intros a b Ha Hb.
  unfold valid_string, all_ascii, no_inner_nul in *.
  destruct Ha as [Ha_ascii Ha_nul].
  destruct Hb as [Hb_ascii Hb_nul].
  split; intros k Hk;
    rewrite Zlength_app in Hk;
    destruct (Z_lt_ge_dec k (Zlength a)) as [Hleft | Hright].
  - rewrite app_Znth1 by lia.
    apply Ha_ascii; lia.
  - rewrite app_Znth2 by lia.
    apply Hb_ascii; lia.
  - rewrite app_Znth1 by lia.
    apply Ha_nul; lia.
  - rewrite app_Znth2 by lia.
    apply Hb_nul; lia.
Qed.

Lemma valid_string_nil_19 : valid_string [].
Proof.
  unfold valid_string, all_ascii, no_inner_nul.
  cbn; split; intros; lia.
Qed.

Lemma valid_string_space_19 : valid_string [32].
Proof.
  unfold valid_string, all_ascii, no_inner_nul.
  cbn; split; intros idx Hidx; destruct idx; cbn in *; lia.
Qed.

Lemma valid_string_append_number_word_19 :
  forall prefix d,
    valid_string prefix ->
    0 <= d < 10 ->
    valid_string (append_number_word_z prefix d).
Proof.
  intros prefix d Hprefix Hd.
  unfold append_number_word_z.
  destruct (Z.eqb (Zlength prefix) 0).
  - change (valid_string (prefix ++ number_word_z d)).
    apply valid_string_app_19; [assumption |].
    destruct (number_word_valid_digit_19 d Hd) as [[Hvalid _] _].
    exact Hvalid.
  - change (valid_string (prefix ++ ([32] ++ number_word_z d))).
    apply valid_string_app_19.
    + assumption.
    + apply valid_string_app_19; [exact valid_string_space_19 |].
      destruct (number_word_valid_digit_19 d Hd) as [[Hvalid _] _].
      exact Hvalid.
Qed.

Lemma valid_string_append_repeated_number_word_nat_19 :
  forall n prefix d,
    valid_string prefix ->
    0 <= d < 10 ->
    valid_string (append_repeated_number_word_nat prefix d n).
Proof.
  induction n as [| n IH]; intros prefix d Hprefix Hd; cbn.
  - exact Hprefix.
  - apply valid_string_append_number_word_19; [apply IH; assumption | assumption].
Qed.

Lemma valid_string_append_repeated_number_word_z_19 :
  forall prefix d count done,
    valid_string prefix ->
    0 <= d < 10 ->
    valid_string (append_repeated_number_word_z prefix d count done).
Proof.
  intros.
  unfold append_repeated_number_word_z.
  apply valid_string_append_repeated_number_word_nat_19; assumption.
Qed.

Lemma valid_string_output_prefix_by_input_19 :
  forall d done input,
    0 <= d < 10 ->
    valid_string (output_prefix_by_input_z d done input).
Proof.
  intros d done input Hd.
  unfold output_prefix_by_input_z, output_prefix_z.
  destruct_digit d;
    repeat (apply valid_string_append_repeated_number_word_z_19; [ | lia ]);
    exact valid_string_nil_19.
Qed.

Definition billed_length_19 (s : list Z) : Z :=
  if Z.eqb (Zlength s) 0 then 0 else Zlength s + 1.

Lemma billed_length_nonempty_19 :
  forall s,
    0 < Zlength s ->
    billed_length_19 s = Zlength s + 1.
Proof.
  intros s Hs.
  unfold billed_length_19.
  destruct (Z.eqb_spec (Zlength s) 0); lia.
Qed.

Lemma append_number_word_z_billed_length_19 :
  forall prefix d,
    0 <= d < 10 ->
    billed_length_19 (append_number_word_z prefix d) =
      billed_length_19 prefix + number_word_len_z d + 1.
Proof.
  intros prefix d Hd.
  pose proof (Zlength_nonneg prefix) as Hprefix_len_nonneg.
  unfold billed_length_19.
  rewrite append_number_word_z_length by lia.
  destruct_digit d;
    unfold number_word_len_z, number_word_z;
    cbn;
    destruct (Z.eqb_spec (Zlength prefix) 0) as [Hempty | Hnonempty];
    rewrite ?Hempty;
    repeat match goal with
    | |- context [Z.eqb ?x 0] => destruct (Z.eqb_spec x 0)
    end;
    lia.
Qed.

Lemma append_repeated_number_word_nat_billed_length_19 :
  forall n prefix d,
    0 <= d < 10 ->
    billed_length_19 (append_repeated_number_word_nat prefix d n) =
      billed_length_19 prefix + Z.of_nat n * (number_word_len_z d + 1).
Proof.
  induction n as [| n IH]; intros prefix d Hd; cbn.
  - destruct_digit d; unfold number_word_len_z, number_word_z; cbn; lia.
  - destruct_digit d;
    rewrite append_number_word_z_billed_length_19 by lia;
    rewrite IH by lia;
    change (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1);
    unfold number_word_len_z, number_word_z in *; cbn in *; lia.
Qed.

Lemma append_repeated_number_word_z_billed_length_19 :
  forall prefix d count done,
    0 <= d < 10 ->
    0 <= done ->
    billed_length_19 (append_repeated_number_word_z prefix d count done) =
      billed_length_19 prefix + done * (number_word_len_z d + 1).
Proof.
  intros prefix d count done Hd Hdone.
  unfold append_repeated_number_word_z.
  rewrite append_repeated_number_word_nat_billed_length_19 by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma append_number_word_z_length_upper_19 :
  forall prefix d,
    0 <= d < 10 ->
    Zlength (append_number_word_z prefix d) <=
      Zlength prefix + number_word_len_z d + 1.
Proof.
  intros prefix d Hd.
  destruct_digit d;
    unfold append_number_word_z, number_word_len_z, number_word_z;
    destruct (Z.eqb (Zlength prefix) 0);
    repeat rewrite Zlength_app; cbn; lia.
Qed.

Lemma append_repeated_number_word_nat_length_upper_19 :
  forall n prefix d,
    0 <= d < 10 ->
    Zlength (append_repeated_number_word_nat prefix d n) <=
      Zlength prefix + Z.of_nat n * (number_word_len_z d + 1).
Proof.
  induction n as [| n IH]; intros prefix d Hd; simpl append_repeated_number_word_nat.
  - lia.
  - pose proof (IH prefix d Hd) as Hprev.
    pose proof (append_number_word_z_length_upper_19
      (append_repeated_number_word_nat prefix d n) d Hd) as Hstep.
    change (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1).
    lia.
Qed.

Lemma append_repeated_number_word_z_length_upper_19 :
  forall prefix d count done,
    0 <= d < 10 ->
    0 <= done ->
    Zlength (append_repeated_number_word_z prefix d count done) <=
      Zlength prefix + done * (number_word_len_z d + 1).
Proof.
  intros prefix d count done Hd Hdone.
  unfold append_repeated_number_word_z.
  pose proof (append_repeated_number_word_nat_length_upper_19
    (Z.to_nat done) prefix d Hd) as Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  exact Hlen.
Qed.

Ltac pose_repeated_length_bounds_19 :=
  repeat match goal with
  | |- context [Zlength (append_repeated_number_word_z ?p ?d ?c ?done)] =>
      match goal with
      | H : Zlength (append_repeated_number_word_z p d c done) <= _ |- _ =>
          fail 1
      | _ =>
          pose proof (append_repeated_number_word_z_length_upper_19
            p d c done ltac:(lia) ltac:(lia))
      end
  | Hctx : context [Zlength (append_repeated_number_word_z ?p ?d ?c ?done)] |- _ =>
      match goal with
      | H : Zlength (append_repeated_number_word_z p d c done) <= _ |- _ =>
          fail 1
      | _ =>
          pose proof (append_repeated_number_word_z_length_upper_19
            p d c done ltac:(lia) ltac:(lia))
      end
  end.

Fixpoint tokens_weight_19 (tokens : list (list Z)) : Z :=
  match tokens with
  | [] => 0
  | tok :: rest => Zlength tok + 1 + tokens_weight_19 rest
  end.

Lemma Zlength_aux_add_19 :
  forall {A} (l : list A) n,
    Zlength_aux n A l = n + Z.of_nat (length l).
Proof.
  intros A l.
  induction l as [| a l IH]; intros n; cbn.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma Zlength_aux_1_ge_19 :
  forall {A} (l : list A),
    Zlength l <= Zlength_aux 1 A l.
Proof.
  intros A l.
  unfold Zlength.
  repeat rewrite Zlength_aux_add_19.
  lia.
Qed.

Lemma SplitOnSpacesZ_aux_weight_bound_19 :
  forall input current,
    tokens_weight_19 (SplitOnSpacesZ_aux_19 current input) <=
    Zlength input + Zlength current + 1.
Proof.
  induction input as [| h input IH]; intros current; cbn.
  - destruct current as [| c current]; cbn.
    + lia.
    + replace (Zlength (rev current ++ [c])) with (Zlength (c :: current)).
      * change (Zlength (c :: current)) with (Zlength_aux 1 Z current).
        lia.
      * rewrite Zlength_app.
        unfold Zlength.
        repeat rewrite Zlength_aux_add_19.
        rewrite length_rev.
        cbn; lia.
  - destruct (Z.eqb h 32).
    + destruct current.
      * pose proof (IH []).
        cbn in *.
        change (Zlength (h :: input)) with (Zlength_aux 1 Z input).
        pose proof (Zlength_aux_1_ge_19 input).
        lia.
      * pose proof (IH []).
        cbn in *.
        replace (Zlength (rev current ++ [z])) with (Zlength (z :: current)).
        -- change (Zlength (z :: current)) with (Zlength_aux 1 Z current).
           assert (Hinput_aux : Zlength_aux 1 Z input = Zlength input + 1)
             by (unfold Zlength; repeat rewrite Zlength_aux_add_19; lia).
           lia.
        -- rewrite Zlength_app.
           unfold Zlength.
           repeat rewrite Zlength_aux_add_19.
           rewrite length_rev.
           cbn; lia.
    + pose proof (IH (h :: current)).
      cbn in *.
      change (Zlength (h :: current)) with (Zlength_aux 1 Z current) in H.
      change (Zlength (h :: input)) with (Zlength_aux 1 Z input).
      assert (Hinput_aux : Zlength_aux 1 Z input = Zlength input + 1)
        by (unfold Zlength; repeat rewrite Zlength_aux_add_19; lia).
      assert (Hcurrent_aux : Zlength_aux 1 Z current = Zlength current + 1)
        by (unfold Zlength; repeat rewrite Zlength_aux_add_19; lia).
      lia.
Qed.

Lemma SplitOnSpacesZ_weight_bound_19 :
  forall input,
    tokens_weight_19 (SplitOnSpacesZ_19 input) <= Zlength input + 1.
Proof.
  intros input.
  unfold SplitOnSpacesZ_19.
  pose proof (SplitOnSpacesZ_aux_weight_bound_19 input []).
  cbn in *; lia.
Qed.

Ltac solve_number_word_contradictions_19 :=
  unfold number_word_z in *; cbn in *; try discriminate.

Lemma count_occ_cons_eq_19 :
  forall tokens x,
    count_occ list_Z_eq_dec_19 (x :: tokens) x =
    S (count_occ list_Z_eq_dec_19 tokens x).
Proof.
  intros tokens x.
  cbn.
  destruct (list_Z_eq_dec_19 x x) as [_ | Hneq]; congruence.
Qed.

Lemma count_occ_cons_neq_19 :
  forall tokens x y,
    x <> y ->
    count_occ list_Z_eq_dec_19 (x :: tokens) y =
    count_occ list_Z_eq_dec_19 tokens y.
Proof.
  intros tokens x y Hneq.
  cbn.
  destruct (list_Z_eq_dec_19 x y) as [Heq | _]; congruence.
Qed.

Ltac prep_count_word_branch_19 :=
  repeat match goal with
  | |- context [match list_Z_eq_dec_19 ?x ?y with left _ => _ | right _ => _ end] =>
      destruct (list_Z_eq_dec_19 x y) as [Heq | Hneq];
      [try (exfalso; unfold number_word_z in Heq; cbn in Heq; discriminate)
      |try (exfalso; apply Hneq; unfold number_word_z; cbn; reflexivity)]
  end;
  unfold number_word_z in *;
  repeat match goal with
  | |- context [match list_Z_eq_dec_19 ?x ?y with left _ => _ | right _ => _ end] =>
      destruct (list_Z_eq_dec_19 x y) as [Heq | Hneq];
      [try (exfalso; cbn in Heq; discriminate)
      |try (exfalso; apply Hneq; cbn; reflexivity)]
  end;
  cbn [Zlength Zlength_aux] in *;
  rewrite ?Nat2Z.inj_succ in *.

Ltac prep_count_weight_branch_19 :=
  repeat match goal with
  | |- context [count_occ list_Z_eq_dec_19 (number_word_z ?d :: ?tokens) (number_word_z ?d)] =>
      rewrite count_occ_cons_eq_19
  | |- context [count_occ list_Z_eq_dec_19 (number_word_z ?d :: ?tokens) (number_word_z ?k)] =>
      rewrite count_occ_cons_neq_19
        by (apply number_word_z_neq_19; lia)
  end;
  unfold number_word_z in *;
  cbn [tokens_weight_19 Zlength Zlength_aux] in *;
  rewrite ?Nat2Z.inj_succ in *;
  repeat match goal with
  | |- context [Z.succ ?x] => change (Z.succ x) with (x + 1)
  | H : context [Z.succ ?x] |- _ => change (Z.succ x) with (x + 1) in H
  end.

Ltac solve_count_word_branch_19 :=
  prep_count_weight_branch_19;
  lia.

Lemma count_number_words_weight_tokens_bound_19 :
  forall tokens,
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 0)) * 5 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 1)) * 4 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 2)) * 4 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 3)) * 6 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 4)) * 5 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 5)) * 5 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 6)) * 4 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 7)) * 6 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 8)) * 6 +
    Z.of_nat (count_occ list_Z_eq_dec_19 tokens (number_word_z 9)) * 5 <=
    tokens_weight_19 tokens.
Proof.
  induction tokens as [| tok tokens IH].
  - cbn; lia.
  - destruct (list_Z_eq_dec_19 tok (number_word_z 0)) as [-> | Hneq0].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 1)) as [-> | Hneq1].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 2)) as [-> | Hneq2].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 3)) as [-> | Hneq3].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 4)) as [-> | Hneq4].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 5)) as [-> | Hneq5].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 6)) as [-> | Hneq6].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 7)) as [-> | Hneq7].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 8)) as [-> | Hneq8].
    { solve_count_word_branch_19. }
    destruct (list_Z_eq_dec_19 tok (number_word_z 9)) as [-> | Hneq9].
    { solve_count_word_branch_19. }
    cbn [tokens_weight_19].
    repeat match goal with
    | |- context [count_occ list_Z_eq_dec_19 (?tok :: ?tokens) ?word] =>
        rewrite count_occ_cons_neq_19 by congruence
    end.
    pose proof (Zlength_nonneg tok).
    lia.
Qed.

Lemma count_number_words_weight_input_bound_19 :
  forall input,
    count_word_in_string 0 input * 5 +
    count_word_in_string 1 input * 4 +
    count_word_in_string 2 input * 4 +
    count_word_in_string 3 input * 6 +
    count_word_in_string 4 input * 5 +
    count_word_in_string 5 input * 5 +
    count_word_in_string 6 input * 4 +
    count_word_in_string 7 input * 6 +
    count_word_in_string 8 input * 6 +
    count_word_in_string 9 input * 5 <=
    Zlength input + 1.
Proof.
  intros input.
  unfold count_word_in_string.
  pose proof (count_number_words_weight_tokens_bound_19
    (SplitOnSpacesZ_19 input)) as Hcount.
  pose proof (SplitOnSpacesZ_weight_bound_19 input) as Hsplit.
  lia.
Qed.

Lemma number_word_char_full_to_store_string_19 :
  forall w d,
    0 <= d < 10 ->
    number_word_char_full_z w d |-- store_string w (number_word_z d).
Proof.
  intros w d Hd.
  destruct (number_word_valid_digit_19 d Hd) as [[Hvalid Hlen] _].
  unfold number_word_char_full_z, store_string.
  rewrite Hlen.
  unfold c_string.
  entailer!.
Qed.

Lemma strcmp_result_nonzero_neq_19 :
  forall s1 s2 ret,
    strcmp_result s1 s2 ret ->
    ret <> 0 ->
    s1 <> s2.
Proof.
  intros s1 s2 ret Hcmp Hret Heq.
  subst s2.
  unfold strcmp_result in Hcmp.
  destruct Hcmp as [idx [_ [_ [_ [Hret_eq _]]]]].
  rewrite Z.sub_diag in Hret_eq.
  lia.
Qed.

Lemma token_miss_prefix_step_19 :
  forall d token ret,
    0 <= d < 10 ->
    token_miss_prefix_z d token ->
    strcmp_result token (number_word_z d) ret ->
    ret <> 0 ->
    token_miss_prefix_z (d + 1) token.
Proof.
  intros d token ret Hd Hmiss Hcmp Hret.
  unfold token_miss_prefix_z in *.
  intros k Hk.
  assert (k < d \/ k = d) as [Hlt | Heq] by lia.
  - apply Hmiss; lia.
  - subst k.
    eapply strcmp_result_nonzero_neq_19; eauto.
Qed.

Ltac solve_token_miss_step_19 :=
  match goal with
  | Hmiss : token_miss_prefix_z ?d ?tok,
    Hcmp : strcmp_result ?tok _ ?ret,
    Hret : ?ret <> 0
    |- token_miss_prefix_z ?next ?tok =>
      replace next with (d + 1) by lia;
      let Hcmp' := fresh "Hcmp'" in
      assert (Hcmp' : strcmp_result tok (number_word_z d) ret)
        by (change (strcmp_result tok (number_word_z d) ret) in Hcmp; exact Hcmp);
      eapply token_miss_prefix_step_19; [lia | exact Hmiss | exact Hcmp' | exact Hret]
  end.

Ltac c19_manual_auto :=
  pre_process; subst; cbn in *; split_scan_counts;
  try match goal with
  | Hlo : 0 <= ?i, Hhi : ?i < 10 |- _ => destruct_digit i
  end;
  entailer!;
    try match goal with
    | H : scan_counts_exact_z _ _ _ _ _ _ _ _ _ _ _ _ _ _
      |- scan_counts_exact_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact H
    end;
    try lia; try nia.

Lemma number_words_full_split_19 :
  forall words d w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 |--
      ((words + d * sizeof(PTR)) # Ptr |->
        Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0) **
      store_string
        (Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0)
        (number_word_z d) **
    number_words_missing words d
      (Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0)
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_full, number_words_missing.
  sep_apply (PtrArray.full_split_to_missing_i words d 10
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0); [ | lia ].
  destruct_digit d;
    unfold number_words_chars_full_z, number_words_chars_missing_z,
      number_word_ptrs_z in *;
    cbn [Znth] in *;
    rewrite sizeof_ptr.
  - sepcon_lift (number_word_char_full_z w0 0).
    sep_apply (number_word_char_full_to_store_string_19 w0 0 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w1 1).
    sep_apply (number_word_char_full_to_store_string_19 w1 1 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w2 2).
    sep_apply (number_word_char_full_to_store_string_19 w2 2 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w3 3).
    sep_apply (number_word_char_full_to_store_string_19 w3 3 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w4 4).
    sep_apply (number_word_char_full_to_store_string_19 w4 4 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w5 5).
    sep_apply (number_word_char_full_to_store_string_19 w5 5 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w6 6).
    sep_apply (number_word_char_full_to_store_string_19 w6 6 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w7 7).
    sep_apply (number_word_char_full_to_store_string_19 w7 7 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w8 8).
    sep_apply (number_word_char_full_to_store_string_19 w8 8 ltac:(lia)).
    entailer!.
  - sepcon_lift (number_word_char_full_z w9 9).
    sep_apply (number_word_char_full_to_store_string_19 w9 9 ltac:(lia)).
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

Lemma number_words_missing_merge_vc :
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
  rewrite sizeof_ptr.
  sep_apply (PtrArray.missing_i_merge_to_full words d 10
    (Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0)
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9));
    [ | lia ].
  rewrite replace_Znth_Znth.
  destruct_digit d; subst;
    unfold number_words_chars_full_z, number_words_chars_missing_z,
      number_word_ptrs_z in *;
    cbn [Znth] in *;
    asrt_simpl_pure.
  - fold (number_word_char_full_z w0 0). entailer!.
  - fold (number_word_char_full_z w1 1). entailer!.
  - fold (number_word_char_full_z w2 2). entailer!.
  - fold (number_word_char_full_z w3 3). entailer!.
  - fold (number_word_char_full_z w4 4). entailer!.
  - fold (number_word_char_full_z w5 5). entailer!.
  - fold (number_word_char_full_z w6 6). entailer!.
  - fold (number_word_char_full_z w7 7). entailer!.
  - fold (number_word_char_full_z w8 8). entailer!.
  - fold (number_word_char_full_z w9 9). entailer!.
Qed.

Lemma number_words_missing_merge_vc_char_first :
  forall words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    word = Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0 ->
    CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil) **
    ((words + d * sizeof(PTR)) # Ptr |-> word) **
    number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9
    |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  rotate_sepcon_left_top_19.
  rewrite (logic_equiv_sepcon_assoc
    ((words + d * sizeof(PTR)) # Ptr |-> word)
    (number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
    (CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil))).
  apply number_words_missing_merge_vc; auto.
Qed.

Lemma number_words_missing_merge_vc_missing_first :
  forall words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    word = Znth d (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) 0 ->
    number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
    ((words + d * sizeof(PTR)) # Ptr |-> word) **
    CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil)
    |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  rewrite <- (logic_equiv_sepcon_assoc
    (number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
    ((words + d * sizeof(PTR)) # Ptr |-> word)
    (CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil))).
  rewrite (logic_equiv_sepcon_swap
    (number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
    ((words + d * sizeof(PTR)) # Ptr |-> word)
    (CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil))).
  rewrite (logic_equiv_sepcon_assoc
    ((words + d * sizeof(PTR)) # Ptr |-> word)
    (number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9)
    (CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil))).
  apply number_words_missing_merge_vc; auto.
Qed.

Lemma number_words_missing_merge_vc_from_missing :
  forall words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9,
    0 <= d < 10 ->
    ((words + d * sizeof(PTR)) # Ptr |-> word) **
    number_words_missing words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
    CharArray.full word (number_word_len_z d + 1) (number_word_z d ++ 0 :: nil)
    |-- number_words_full words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.
Proof.
  intros.
  unfold number_words_missing, number_words_full.
  rewrite sizeof_ptr.
  sep_apply (PtrArray.missing_i_merge_to_full words d 10 word
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9));
    [ | lia ].
  destruct_digit d.
  all: unfold number_words_chars_missing_z, number_words_chars_full_z,
      number_word_ptrs_z in *;
    cbn [Znth] in *;
    asrt_simpl_pure;
    try match goal with
    | Hword : ?x = ?y |- _ => rewrite Hword in *
    end;
    try rewrite replace_Znth_Znth by lia;
    entailer!.
  all: subst; unfold replace_Znth; cbn;
    repeat match goal with
    | |- context [Pos.to_nat 1] => change (Pos.to_nat 1) with 1%nat
    | |- context [Pos.to_nat 2] => change (Pos.to_nat 2) with 2%nat
    | |- context [Pos.to_nat 3] => change (Pos.to_nat 3) with 3%nat
    | |- context [Pos.to_nat 4] => change (Pos.to_nat 4) with 4%nat
    | |- context [Pos.to_nat 5] => change (Pos.to_nat 5) with 5%nat
    | |- context [Pos.to_nat 6] => change (Pos.to_nat 6) with 6%nat
    | |- context [Pos.to_nat 7] => change (Pos.to_nat 7) with 7%nat
    | |- context [Pos.to_nat 8] => change (Pos.to_nat 8) with 8%nat
    | |- context [Pos.to_nat 9] => change (Pos.to_nat 9) with 9%nat
    end;
    cbn;
    unfold number_word_char_full_z; entailer!.
Qed.

Lemma proof_of_sort_numbers_safety_wit_162_split_goal_1 : sort_numbers_safety_wit_162_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_162_split_goal_2 : sort_numbers_safety_wit_162_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_162 : sort_numbers_safety_wit_162.
Proof. c19_manual_auto. Qed. 

Lemma proof_of_sort_numbers_safety_wit_179_split_goal_1 : sort_numbers_safety_wit_179_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_179_split_goal_2 : sort_numbers_safety_wit_179_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_179 : sort_numbers_safety_wit_179.
Proof. c19_manual_auto. Qed. 

Lemma proof_of_sort_numbers_safety_wit_180_split_goal_1 : sort_numbers_safety_wit_180_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_180_split_goal_2 : sort_numbers_safety_wit_180_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_180 : sort_numbers_safety_wit_180.
Proof. c19_manual_auto. Qed. 

Lemma proof_of_sort_numbers_safety_wit_200_split_goal_1 : sort_numbers_safety_wit_200_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_200_split_goal_2 : sort_numbers_safety_wit_200_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_200 : sort_numbers_safety_wit_200.
Proof.
  left.
  pre_process.
  unfold scan_counts_z in PreH19.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  destruct_digit i;
    unfold number_word_len_z, number_word_z in *;
    cbn in *;
    entailer!;
    lia.
Qed. 

Lemma proof_of_sort_numbers_safety_wit_201_split_goal_1 : sort_numbers_safety_wit_201_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_201_split_goal_2 : sort_numbers_safety_wit_201_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_safety_wit_201 : sort_numbers_safety_wit_201.
Proof.
  left.
  pre_process.
  unfold scan_counts_z in PreH19.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  destruct_digit i;
    unfold number_word_len_z, number_word_z in *;
    cbn in *;
    entailer!;
    lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_1_split_goal_1 : sort_numbers_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_1_split_goal_spatial : sort_numbers_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_1 : sort_numbers_entail_wit_1.
Proof.
  left.
  pre_process_default; subst.
  fold_number_words_chars_from_raw_19.
  rewrite (CharArray.undef_seg_empty (&( "w9" )) 5).
  unfold c_string.
  rewrite PreH8.
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_2_split_goal_spatial : sort_numbers_entail_wit_2_split_goal_spatial.
Proof.
  unfold sort_numbers_entail_wit_2_split_goal_spatial.
  intros.
  sep_apply_L
    [((( &( "words" ) ) + 9 * sizeof(PTR)) # Ptr |-> (( &( "w9" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 8 * sizeof(PTR)) # Ptr |-> (( &( "w8" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 7 * sizeof(PTR)) # Ptr |-> (( &( "w7" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 6 * sizeof(PTR)) # Ptr |-> (( &( "w6" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 5 * sizeof(PTR)) # Ptr |-> (( &( "w5" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 4 * sizeof(PTR)) # Ptr |-> (( &( "w4" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 3 * sizeof(PTR)) # Ptr |-> (( &( "w3" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 2 * sizeof(PTR)) # Ptr |-> (( &( "w2" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 1 * sizeof(PTR)) # Ptr |-> (( &( "w1" ) ) + 0 * sizeof(CHAR)));
     ((( &( "words" ) ) + 0 * sizeof(PTR)) # Ptr |-> (( &( "w0" ) ) + 0 * sizeof(CHAR)))]
    (ptr_words_cells_full_init (&( "words" )) (&( "w0" )) (&( "w1" ))
      (&( "w2" )) (&( "w3" )) (&( "w4" )) (&( "w5" )) (&( "w6" ))
      (&( "w7" )) (&( "w8" )) (&( "w9" ))).
  sepcon_lift (PtrArray.full (&( "words" )) 10
    (number_word_ptrs_z (&( "w0" )) (&( "w1" )) (&( "w2" ))
      (&( "w3" )) (&( "w4" )) (&( "w5" )) (&( "w6" ))
      (&( "w7" )) (&( "w8" )) (&( "w9" )))).
  sepcon_lift (number_words_chars_full_z (&( "w0" )) (&( "w1" )) (&( "w2" ))
    (&( "w3" )) (&( "w4" )) (&( "w5" )) (&( "w6" ))
    (&( "w7" )) (&( "w8" )) (&( "w9" ))).
  sep_apply (number_words_full_init (&( "words" )) (&( "w0" )) (&( "w1" ))
    (&( "w2" )) (&( "w3" )) (&( "w4" )) (&( "w5" )) (&( "w6" ))
    (&( "w7" )) (&( "w8" )) (&( "w9" ))).
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_2 : sort_numbers_entail_wit_2.
Proof.
  left.
  pre_process; subst.
  apply _derivable1_andp_intros; [entailer!; try lia |].
  rewrite (PtrArray.undef_seg_empty (&( "words" )) 10).
  sep_apply (proof_of_sort_numbers_entail_wit_2_split_goal_spatial
    (Zlength l) l 0 1 PreH1 eq_refl eq_refl PreH4 PreH5 PreH6 eq_refl PreH8 PreH9 PreH10 PreH11).
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_3_split_goal_spatial : sort_numbers_entail_wit_3_split_goal_spatial.
Proof.
  unfold sort_numbers_entail_wit_3_split_goal_spatial.
  intros.
  sep_apply (space_word_full_with_undef_19 retval).
  unfold number_word_len_z, number_word_z.
  cbn.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_3 : sort_numbers_entail_wit_3.
Proof.
  right.
  pre_process; subst.
  sep_apply (proof_of_sort_numbers_entail_wit_3_split_goal_spatial
    (Zlength l) l 0 1 retval PreH1 PreH2 eq_refl eq_refl PreH5 PreH6 PreH7 eq_refl PreH9 PreH10 PreH11 PreH12).
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_4_split_goal_1 : sort_numbers_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_4_split_goal_2 : sort_numbers_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_4_split_goal_3 : sort_numbers_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_4_split_goal_spatial : sort_numbers_entail_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_4 : sort_numbers_entail_wit_4.
Proof.
  left.
  pre_process; subst.
  sep_apply (IntArray.undef_full_to_undef_seg (&( "count" )) 10).
  change (zeros 0) with (@nil Z).
  rewrite (IntArray.seg_empty (&( "count" )) 0 0).
  unfold number_word_len_z, number_word_z, zeros.
  cbn.
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_5_split_goal_1 : sort_numbers_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_5_split_goal_spatial : sort_numbers_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_5 : sort_numbers_entail_wit_5.
Proof.
  left.
  pre_process; subst.
  rewrite <- (zeros_snoc i PreH12).
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_6 : sort_numbers_entail_wit_6.
Proof.
  right.
  pre_process; subst.
  assert (i = 10) by lia; subst i.
  Exists (zeros 10).
  rewrite token_prefix_zero_z.
  sep_apply (IntArray.seg_to_full (&( "count" )) 0 10).
  replace (&( "count" ) + 0) with (&( "count" )) by lia.
  unfold scan_counts_z, scan_counts_capacity_z, scan_counts_exact_z,
    scan_completed_prefix_z, number_word_len_z, number_word_z, zeros.
  cbn.
  repeat rewrite Znth_repeat by lia.
  entailer!; try lia.
  all: try (replace (Z.min 0 (Zlength l)) with 0 by lia;
            unfold count_word_in_string; cbn; reflexivity).
  all: try (unfold token_sat_start_z, token_unsat_end_z,
    token_empty_start_z; intros; lia).
  - replace (&( "count" ) + 0) with (&( "count" )) by lia.
    apply derivable1_refl.
  - unfold token_empty_start_z; intros _; left; reflexivity.
  - unfold valid_string, all_ascii, no_inner_nul.
    cbn; split; intros ? Hbad; lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_1 : sort_numbers_entail_wit_7_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_2 : sort_numbers_entail_wit_7_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_3 : sort_numbers_entail_wit_7_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_4 : sort_numbers_entail_wit_7_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_5 : sort_numbers_entail_wit_7_1_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1_split_goal_spatial : sort_numbers_entail_wit_7_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_1 : sort_numbers_entail_wit_7_1.
Proof.
  right.
  pre_process; subst.
  split_scan_counts.
  unfold scan_char_z.
  destruct (Z.ltb_spec i (Zlength l)).
  - rewrite <- (@app_Znth1 Z 0 l (0 :: nil) i) by lia.
    entailer!; try lia.
    + intros _. exact number_word_zero_valid_19.
    + unfold token_miss_prefix_z; intros k Hk; lia.
  - lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_1 : sort_numbers_entail_wit_7_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_2 : sort_numbers_entail_wit_7_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_3 : sort_numbers_entail_wit_7_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_4 : sort_numbers_entail_wit_7_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_5 : sort_numbers_entail_wit_7_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2_split_goal_spatial : sort_numbers_entail_wit_7_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_7_2 : sort_numbers_entail_wit_7_2.
Proof.
  right.
  pre_process; subst.
  split_scan_counts.
  unfold scan_char_z.
  destruct (Z.ltb_spec i (Zlength l)); try lia.
  entailer!; try lia.
  + intros _. exact number_word_zero_valid_19.
  + unfold token_miss_prefix_z; intros k Hk; lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_8_split_goal_1 : sort_numbers_entail_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_8_split_goal_spatial : sort_numbers_entail_wit_8_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_8 : sort_numbers_entail_wit_8.
Proof.
  left.
  pre_process; subst.
  Exists (Znth d (number_word_ptrs_z (&( "w0" )) (&( "w1" ))
    (&( "w2" )) (&( "w3" )) (&( "w4" )) (&( "w5" )) (&( "w6" ))
    (&( "w7" )) (&( "w8" )) (&( "w9" ))) 0) cnts_2.
  sep_apply (number_words_full_split_19
    (&( "words")) d
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))
    ltac:(lia)).
  pose proof (PreH38 (conj PreH19 PreH1)) as Hword_valid.
  unfold store_string, c_string, number_word_ptrs_z.
  entailer!; try lia; try reflexivity.
  rewrite PreH36.
  apply derivable1_refl.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_1 : sort_numbers_entail_wit_10_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_2 : sort_numbers_entail_wit_10_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_3 : sort_numbers_entail_wit_10_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_4 : sort_numbers_entail_wit_10_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_5 : sort_numbers_entail_wit_10_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10_split_goal_spatial : sort_numbers_entail_wit_10_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_10 : sort_numbers_entail_wit_10.
Proof.
  right.
  pre_process; subst.
  unfold c_string.
  rewrite PreH44.
  sep_apply (number_words_missing_merge_vc_char_first
    (&( "words")) d
    (Znth d (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") :: &( "w4") ::
      &( "w5") :: &( "w6") :: &( "w7") :: &( "w8") :: &( "w9") :: nil) 0)
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))
    ltac:(lia)
    ltac:(unfold number_word_ptrs_z; reflexivity)).
  assert (Hnext_bound : 0 <= Znth (d + 1) cnts_2 0 <= i).
  {
    destruct (Z_lt_ge_dec (d + 1) 10).
    - eapply scan_counts_digit_bound_19; eauto; lia.
    - assert (d = 9) by lia; subst d.
      replace (9 + 1) with 10 by lia.
      rewrite (Znth_10_len10_default cnts_2) by exact PreH38.
      lia.
  }
  entailer!; try lia; try reflexivity.
  - intros Hrange.
    apply number_word_valid_digit_19; lia.
  - eapply token_miss_prefix_step_19.
    + lia.
    + exact PreH49.
    + exact PreH2.
    + exact PreH1.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_1 : sort_numbers_entail_wit_11_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_2 : sort_numbers_entail_wit_11_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_3 : sort_numbers_entail_wit_11_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_4 : sort_numbers_entail_wit_11_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_5 : sort_numbers_entail_wit_11_1_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_6 : sort_numbers_entail_wit_11_1_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_7 : sort_numbers_entail_wit_11_1_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_8 : sort_numbers_entail_wit_11_1_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_9 : sort_numbers_entail_wit_11_1_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_10 : sort_numbers_entail_wit_11_1_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1_split_goal_spatial : sort_numbers_entail_wit_11_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_1 : sort_numbers_entail_wit_11_1.
Proof.
  left.
  pre_process; subst.
  assert (d = 10) by lia; subst d.
  Exists cnts_2.
  sep_apply_l_atomic (CharArray.full_to_undef_full token (tlen + 1)
    (token_prefix_z i tlen l ++ 0 :: nil)).
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg token (tlen + 1)).
  sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_seg token 0 (tlen + 1) 32);
    try lia.
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hexact_step: scan_counts_exact_z (i + 1) 0 l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    unfold scan_counts_exact_z in *.
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end.
    repeat split;
      match goal with
      | H : Znth ?d cnts_2 0 =
            count_word_in_string ?d (scan_completed_prefix_z i tlen l)
        |- Znth ?d cnts_2 0 =
            count_word_in_string ?d (scan_completed_prefix_z (i + 1) 0 l) =>
          rewrite H; symmetry;
          apply scan_count_word_finish_miss_19; try assumption; lia
      end.
  }
  try rewrite token_prefix_zero_z.
  replace (sublist (i + 1 - 0) (i + 1) l) with (@nil Z)
    by (replace (i + 1 - 0) with (i + 1) by lia;
        rewrite Zsublist_nil by lia; reflexivity).
  entailer!;
    try exact Hexact_step;
    try exact Hscan_step;
    try lia;
    try (intros _; unfold token_unsat_end_z; left; reflexivity).
  unfold CharArray.full; cbn; entailer!.
  all: try solve [
    unfold token_empty_start_z;
    intros _;
    left;
    rewrite scan_word_start_step_space by lia;
    reflexivity
  ].
  all: try solve [
    unfold valid_string, all_ascii, no_inner_nul;
    cbn; split; intros idx Hidx; lia
  ].
  all: try match goal with
  | |- context [sublist (?i + 1 - 0) (?i + 1) ?l] =>
      replace (sublist (i + 1 - 0) (i + 1) l) with (@nil Z)
        by (replace (i + 1 - 0) with (i + 1) by lia;
            rewrite Zsublist_nil by lia; reflexivity)
  end.
  all: try solve [exact Hscan_step].
  all: try solve [exact Hexact_step].
  all: try solve [
    eapply scan_counts_exact_finish_miss_19;
      try eassumption; try lia
  ].
  all: try solve [apply scan_counts_step; try assumption; lia].
  all: try solve [unfold token_sat_start_z; intros; lia].
  all: try solve [
    intros _;
    unfold token_unsat_end_z;
    left; reflexivity
  ].
  all: try solve [rewrite Zlength_nil; lia].
  all: try solve [
    unfold valid_string, all_ascii, no_inner_nul;
    cbn; split; intros idx Hidx; lia
  ].
  all: try solve [cbn [store_array_rec]; entailer!].
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_1 : sort_numbers_entail_wit_11_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_2 : sort_numbers_entail_wit_11_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_3 : sort_numbers_entail_wit_11_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_4 : sort_numbers_entail_wit_11_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_5 : sort_numbers_entail_wit_11_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_6 : sort_numbers_entail_wit_11_2_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_7 : sort_numbers_entail_wit_11_2_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_8 : sort_numbers_entail_wit_11_2_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_9 : sort_numbers_entail_wit_11_2_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_10 : sort_numbers_entail_wit_11_2_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_11 : sort_numbers_entail_wit_11_2_split_goal_11.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2_split_goal_spatial : sort_numbers_entail_wit_11_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_2 : sort_numbers_entail_wit_11_2.
Proof.
  right.
  pre_process; subst.
  unfold c_string.
  try rewrite PreH44.
  try rewrite PreH41.
  match goal with
  | |- context [CharArray.full ?wp (number_word_len_z d + 1) (number_word_z d +:: 0)] =>
      sepcon_lift (CharArray.full wp (number_word_len_z d + 1) (number_word_z d +:: 0));
      sepcon_lift (((&( "words") + d * sizeof(PTR)) # Ptr |-> wp));
      sepcon_lift (number_words_missing (&( "words")) d wp
        (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
        (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9")))
  end.
  sep_apply (number_words_missing_merge_vc_missing_first
    (&( "words")) d
    (Znth d (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") :: &( "w4") ::
      &( "w5") :: &( "w6") :: &( "w7") :: &( "w8") :: &( "w9") :: nil) 0)
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))).
  sep_apply_l_atomic (CharArray.full_to_undef_full token (tlen + 1)
    (token_prefix_z i tlen l ++ 0 :: nil)).
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg token (tlen + 1)).
  sepcon_lift (CharArray.undef_seg token (tlen + 1) 32).
  sepcon_lift (CharArray.undef_seg token 0 (tlen + 1)).
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
  assert (Hexact_update: scan_counts_exact_z (i + 1) 0 l
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
    eapply scan_counts_exact_finish_hit_19;
      try eassumption; try lia.
  }
  sep_apply_l_atomic (CharArray.undef_seg_merge_to_undef_full token 0 (tlen + 1) 32);
    try lia.
  try rewrite token_prefix_zero_z.
  replace (token + 0 * sizeof(CHAR)) with token by lia.
  replace (32 - 0) with 32 by lia.
  destruct_digit d; cbn in *;
    replace (token + 0 * sizeof(CHAR)) with token by lia;
    replace (32 - 0) with 32 by lia;
    try rewrite token_prefix_zero_z;
    entailer!;
    try exact Hexact_update;
    try exact Hscan_update;
    try (apply scan_counts_replace_inc; try assumption; lia);
    try (rewrite Zlength_replace_Znth_19; lia);
    try (unfold token_sat_start_z; intros; lia);
    try (unfold token_empty_start_z; intros _; left;
      rewrite scan_word_start_step_space by lia; reflexivity);
    try (intros _; unfold token_unsat_end_z; left; reflexivity);
    try (unfold valid_string, all_ascii, no_inner_nul;
      cbn; split; intros idx Hidx; lia);
    try lia.
  all: try solve [unfold number_word_ptrs_z; reflexivity | lia].
  all: try replace (token + 0 * sizeof(CHAR)) with token by lia.
  all: try replace (32 - 0) with 32 by lia.
  all: try rewrite token_prefix_zero_z.
  all: try solve [
    entailer!;
      try exact Hexact_update;
      try exact Hscan_update;
      try (rewrite Zlength_replace_Znth_19; lia);
      try (unfold token_sat_start_z; intros; lia);
      try (unfold token_empty_start_z; intros _; left;
        rewrite scan_word_start_step_space by lia; reflexivity);
      try (intros _; unfold token_unsat_end_z; left; reflexivity);
      try (unfold valid_string, all_ascii, no_inner_nul;
        cbn; split; intros idx Hidx; lia);
      try lia
  ].
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_1 : sort_numbers_entail_wit_11_3_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_2 : sort_numbers_entail_wit_11_3_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_3 : sort_numbers_entail_wit_11_3_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_4 : sort_numbers_entail_wit_11_3_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_5 : sort_numbers_entail_wit_11_3_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_6 : sort_numbers_entail_wit_11_3_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_7 : sort_numbers_entail_wit_11_3_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_8 : sort_numbers_entail_wit_11_3_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_9 : sort_numbers_entail_wit_11_3_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_10 : sort_numbers_entail_wit_11_3_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3_split_goal_spatial : sort_numbers_entail_wit_11_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_3 : sort_numbers_entail_wit_11_3.
Proof.
  right.
  pre_process; subst.
  assert (tlen = 0) by lia; subst tlen.
  assert (Hscan_char_space : scan_char_z i l = 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)).
    - rewrite <- (@app_Znth1 Z 0 l (0 :: nil) i) by lia.
      assumption.
    - lia.
  }
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hmiss_empty : token_miss_prefix_z 10 (token_prefix_z i 0 l)).
  {
    rewrite token_prefix_zero_z.
    unfold token_miss_prefix_z.
    intros k Hk Heq.
    pose proof (number_word_z_nonempty_19 k ltac:(lia)).
    congruence.
  }
  assert (Hexact_step: scan_counts_exact_z (i + 1) 0 l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    eapply scan_counts_exact_finish_miss_19;
      try eassumption; try lia.
  }
  repeat rewrite token_prefix_zero_z.
  entailer!;
    try exact Hexact_step;
    try exact Hscan_step;
    try (unfold token_sat_start_z; intros; lia);
    try (unfold token_empty_start_z; intros _; left;
      rewrite scan_word_start_step_space by lia; reflexivity);
    try (intros _; unfold token_unsat_end_z; left; reflexivity);
    try (unfold valid_string, all_ascii, no_inner_nul;
      cbn; split; intros idx Hidx; lia);
    try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_1 : sort_numbers_entail_wit_11_4_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_2 : sort_numbers_entail_wit_11_4_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_3 : sort_numbers_entail_wit_11_4_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_4 : sort_numbers_entail_wit_11_4_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_5 : sort_numbers_entail_wit_11_4_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_6 : sort_numbers_entail_wit_11_4_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_7 : sort_numbers_entail_wit_11_4_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_8 : sort_numbers_entail_wit_11_4_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_9 : sort_numbers_entail_wit_11_4_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_10 : sort_numbers_entail_wit_11_4_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4_split_goal_spatial : sort_numbers_entail_wit_11_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_4 : sort_numbers_entail_wit_11_4.
Proof.
  right.
  pre_process; subst.
  assert (tlen = 0) by lia; subst tlen.
  assert (Hscan_char_space : scan_char_z i l = 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)).
    - lia.
    - reflexivity.
  }
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hmiss_empty : token_miss_prefix_z 10 (token_prefix_z i 0 l)).
  {
    rewrite token_prefix_zero_z.
    unfold token_miss_prefix_z.
    intros k Hk Heq.
    pose proof (number_word_z_nonempty_19 k ltac:(lia)).
    congruence.
  }
  assert (Hexact_step: scan_counts_exact_z (i + 1) 0 l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    eapply scan_counts_exact_finish_miss_19;
      try eassumption; try lia.
  }
  repeat rewrite token_prefix_zero_z.
  entailer!;
    try exact Hexact_step;
    try exact Hscan_step;
    try (unfold token_sat_start_z; intros; lia);
    try (unfold token_empty_start_z; intros _; right; lia);
    try (intros _; unfold token_unsat_end_z; left; reflexivity);
    try (unfold valid_string, all_ascii, no_inner_nul;
      cbn; split; intros idx Hidx; lia);
    try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_1 : sort_numbers_entail_wit_11_5_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_2 : sort_numbers_entail_wit_11_5_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_3 : sort_numbers_entail_wit_11_5_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_4 : sort_numbers_entail_wit_11_5_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_5 : sort_numbers_entail_wit_11_5_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_6 : sort_numbers_entail_wit_11_5_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_7 : sort_numbers_entail_wit_11_5_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_8 : sort_numbers_entail_wit_11_5_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_9 : sort_numbers_entail_wit_11_5_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_10 : sort_numbers_entail_wit_11_5_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_11 : sort_numbers_entail_wit_11_5_split_goal_11.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_12 : sort_numbers_entail_wit_11_5_split_goal_12.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5_split_goal_spatial : sort_numbers_entail_wit_11_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_5 : sort_numbers_entail_wit_11_5.
Proof.
  right.
  pre_process; subst.
  assert (Hscan_char_nonspace : scan_char_z i l <> 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)).
    - rewrite <- (@app_Znth1 Z 0 l (0 :: nil) i) by lia.
      assumption.
    - lia.
  }
  assert (Hend : token_unsat_end_z i tlen l) by (apply PreH40; lia).
  assert (Hstart_end : scan_word_start_z i l + tlen = i).
  {
    unfold token_unsat_end_z in Hend.
    destruct Hend as [Htlen0 | Hend]; [subst tlen | exact Hend].
    unfold token_empty_start_z in PreH39.
    specialize (PreH39 eq_refl).
    destruct PreH39 as [Hstart | Hpast]; lia.
  }
  assert (Hprefix_step :
    token_prefix_z (i + 1) (tlen + 1) l =
    List.app (token_prefix_z i tlen l)
      (Znth i (List.app l (0 :: nil)) 0 :: nil)).
  {
    apply token_prefix_extend_z; try assumption; try lia.
  }
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hcompleted_step :
    scan_completed_prefix_z (i + 1) (tlen + 1) l =
    scan_completed_prefix_z i tlen l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec tlen 31) as [Htlt | Hbad]; try lia.
    destruct (Z.ltb_spec (tlen + 1) 31) as [Hnext_lt | Hnext_ge].
    - replace (i + 1 - (tlen + 1)) with (i - tlen) by lia.
      reflexivity.
    - assert (Htlen30 : tlen = 30) by lia; subst tlen.
      rewrite scan_word_start_step_nonspace by lia.
      assert (Hstart_eq : scan_word_start_z i l = i - 30) by lia.
      rewrite Hstart_eq.
      reflexivity.
  }
  assert (Hexact_step: scan_counts_exact_z (i + 1) (tlen + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    unfold scan_counts_exact_z in *.
    rewrite Hcompleted_step.
    assumption.
  }
  rewrite <- Hprefix_step.
  entailer!;
    try exact Hexact_step;
    try exact Hscan_step;
    try (unfold token_sat_start_z; intros Hsat;
      rewrite scan_word_start_step_nonspace by lia; lia);
    try (apply token_empty_start_after_inc_z; try assumption; lia);
    try (intros Htlen_next;
      apply token_unsat_end_extend_z; try assumption; try lia);
    try (rewrite Hprefix_step; apply valid_string_token_prefix_snoc_19;
      try assumption; lia);
    try (rewrite Hprefix_step; unfold string_length; rewrite Zlength_app;
      rewrite Zlength_cons, Zlength_nil; lia);
    try (rewrite app_Znth1 by lia; apply PreH14; lia);
    try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_1 : sort_numbers_entail_wit_11_6_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_2 : sort_numbers_entail_wit_11_6_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_3 : sort_numbers_entail_wit_11_6_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_4 : sort_numbers_entail_wit_11_6_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_5 : sort_numbers_entail_wit_11_6_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_6 : sort_numbers_entail_wit_11_6_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_7 : sort_numbers_entail_wit_11_6_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_8 : sort_numbers_entail_wit_11_6_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_9 : sort_numbers_entail_wit_11_6_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_10 : sort_numbers_entail_wit_11_6_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_11 : sort_numbers_entail_wit_11_6_split_goal_11.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6_split_goal_spatial : sort_numbers_entail_wit_11_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_11_6 : sort_numbers_entail_wit_11_6.
Proof.
  right.
  pre_process; subst.
  assert (Hscan_char_nonspace : scan_char_z i l <> 32).
  {
    unfold scan_char_z.
    destruct (Z.ltb_spec i (Zlength l)).
    - rewrite <- (@app_Znth1 Z 0 l (0 :: nil) i) by lia.
      assumption.
    - lia.
  }
  assert (Hprefix_same :
    token_prefix_z (i + 1) tlen l = token_prefix_z i tlen l).
  {
    apply token_prefix_saturated_step_z; try assumption; lia.
  }
  assert (Hscan_step: scan_counts_z (i + 1) l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    apply scan_counts_step; try assumption; lia.
  }
  assert (Hcompleted_step :
    scan_completed_prefix_z (i + 1) tlen l =
    scan_completed_prefix_z i tlen l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec tlen 31) as [Hbad | Hsat]; try lia.
    rewrite scan_word_start_step_nonspace by lia.
    reflexivity.
  }
  assert (Hexact_step: scan_counts_exact_z (i + 1) tlen l
      (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
      (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
      (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
      (Znth 9 cnts_2 0)).
  {
    unfold scan_counts_exact_z in *.
    rewrite Hcompleted_step.
    assumption.
  }
  rewrite Hprefix_same.
  entailer!;
    try exact Hexact_step;
    try exact Hscan_step;
    try (unfold token_sat_start_z; intros Hsat;
      rewrite scan_word_start_step_nonspace by lia;
      unfold token_sat_start_z in PreH40;
      specialize (PreH40 ltac:(lia)); lia);
    try (unfold token_empty_start_z; intros Hempty; lia);
    try (rewrite app_Znth1 by lia; apply PreH13; lia);
    try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_1 : sort_numbers_entail_wit_12_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_2 : sort_numbers_entail_wit_12_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_3 : sort_numbers_entail_wit_12_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_4 : sort_numbers_entail_wit_12_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_5 : sort_numbers_entail_wit_12_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_6 : sort_numbers_entail_wit_12_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_7 : sort_numbers_entail_wit_12_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_8 : sort_numbers_entail_wit_12_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_9 : sort_numbers_entail_wit_12_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12_split_goal_spatial : sort_numbers_entail_wit_12_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_12 : sort_numbers_entail_wit_12.
Proof.
  right.
  pre_process; subst.
  assert (Hi_end : i = Zlength l + 1) by lia.
  assert (Htlen_zero : tlen = 0).
  {
    apply (token_prefix_after_end_zero_z i tlen l); try assumption; try lia.
  }
  subst i tlen.
  unfold scan_counts_exact_z in PreH40.
  split_scan_counts.
  repeat apply _derivable1_andp_intros.
  all: try solve [
    apply derivable1s_coq_prop_r;
      try assumption;
      try (intros _; exact number_word_zero_valid_19);
      try (unfold output_capacity_prefix_by_input_z,
                  output_capacity_prefix_z;
           simpl; lia);
      try (unfold number_word_len_z, number_word_z; simpl; lia);
      try (unfold scan_counts_z, scan_counts_capacity_z in *;
           unfold number_word_len_z, number_word_z in *; simpl in *; lia);
      try lia
  ].
  entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_13_split_goal_spatial : sort_numbers_entail_wit_13_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_13 : sort_numbers_entail_wit_13.
Proof.
  left.
  pre_process; subst.
  pose proof (PreH19 (conj PreH17 PreH1)) as [[Hvalid_i Hlen_i] Hlt_i].
  rewrite Hlen_i.
  Exists cnts_2
    (Znth i (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") ::
      &( "w4") :: &( "w5") :: &( "w6") :: &( "w7") ::
      &( "w8") :: &( "w9") :: nil) 0).
  sep_apply (number_words_full_split_19
    (&( "words")) i (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3"))
    (&( "w4")) (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8"))
    (&( "w9"))); [ | lia ].
  unfold store_string, c_string.
  entailer!;
    try exact PreH16;
    try exact PreH15;
    try lia.
  all: try solve [unfold number_word_ptrs_z; reflexivity | lia].
  unfold number_word_ptrs_z.
  apply sepcon_tail_comm_19.
Qed. 

Lemma output_capacity_next_props_19 :
  forall len l cnts i out_len retval,
    Zlength l = len ->
    1 + 6 * (len + 1) <= INT_MAX ->
    Zlength cnts = 10 ->
    scan_counts_z (len + 1) l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_exact_z (len + 1) 0 l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= i < 10 ->
    retval = string_length (number_word_z i) ->
    out_len = output_capacity_prefix_by_input_z i l ->
    1 <= out_len ->
    0 <= Znth i cnts 0 ->
    out_len + Znth i cnts 0 * (number_word_len_z i + 1) <= INT_MAX ->
    let next_out := out_len + Znth i cnts 0 * (retval + 1) in
    0 <= i + 1 <= 10 /\
    (((0 <= i + 1) /\ (i + 1 < 10)) ->
      valid_string (number_word_z (i + 1)) /\
      string_length (number_word_z (i + 1)) = number_word_len_z (i + 1) /\
      string_length (number_word_z (i + 1)) < INT_MAX) /\
    1 <= next_out /\
    next_out = output_capacity_prefix_by_input_z (i + 1) l /\
    0 <= Znth (i + 1) cnts 0 /\
    number_word_len_z (i + 1) + 1 <= INT_MAX /\
    INT_MIN <= number_word_len_z (i + 1) + 1 /\
    next_out + Znth (i + 1) cnts 0 * (number_word_len_z (i + 1) + 1) <= INT_MAX.
Proof.
  intros len l cnts i out_len retval Hlen Hcap Hcnts Hscan Hexact Hi Hretval Hout Houtpos Hci Hcurcap.
  assert (Hcompleted_l :
    scan_completed_prefix_z (len + 1) 0 l = l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec 0 31) as [_ | Hbad]; [ | lia ].
    replace (Z.min (len + 1 - 0) (Zlength l)) with (Zlength l)
      by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  unfold scan_counts_z, scan_counts_capacity_z in Hscan.
  unfold scan_counts_exact_z in Hexact.
  rewrite Hcompleted_l in Hexact.
  rewrite Hout in *.
  rewrite Hretval in *.
  unfold output_capacity_prefix_by_input_z, output_capacity_prefix_z in *.
  unfold number_word_len_z, number_word_z in *.
  cbn in *.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  repeat match goal with
  | H : Znth ?d cnts 0 = ?v |- _ => rewrite H in *
  end.
  change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5) in *.
  pose proof (Z.le_trans _ _ _ H22 Hcap) as Hfullcap_int.
  assert (Hc0_nonneg : 0 <= count_word_in_string 0 l) by lia.
  assert (Hc1_nonneg : 0 <= count_word_in_string 1 l) by lia.
  assert (Hc2_nonneg : 0 <= count_word_in_string 2 l) by lia.
  assert (Hc3_nonneg : 0 <= count_word_in_string 3 l) by lia.
  assert (Hc4_nonneg : 0 <= count_word_in_string 4 l) by lia.
  assert (Hc5_nonneg : 0 <= count_word_in_string 5 l) by lia.
  assert (Hc6_nonneg : 0 <= count_word_in_string 6 l) by lia.
  assert (Hc7_nonneg : 0 <= count_word_in_string 7 l) by lia.
  assert (Hc8_nonneg : 0 <= count_word_in_string 8 l) by lia.
  assert (Hc9_nonneg : 0 <= count_word_in_string 9 l) by lia.
  assert (Hcases:
    i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/
    i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) by lia.
  destruct Hcases as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]].
  all: subst i; cbn in *.
  all: repeat match goal with
  | H : Znth ?d ?cs 0 = ?v |- _ => rewrite H in *
  end.
  all: change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5) in *.
  all: try change (9 + 1) with 10 in *.
  all: try rewrite (Znth_10_len10_default cnts Hcnts) in *.
  all: split; [solve [lia] |].
  all: split; [
    intros Hrange;
    destruct (number_word_valid_digit_19 _ Hrange) as [[Hv Hlen_word] Hlt_word];
    exact (conj Hv (conj Hlen_word Hlt_word))
  |].
  all: repeat split; lia.
Qed.

Lemma output_prefix_space_bounds_19 :
  forall len l cnts i j out_len,
    Zlength l = len ->
    len + 1 < INT_MAX ->
    1 + 6 * (len + 1) <= INT_MAX ->
    Zlength cnts = 10 ->
    scan_counts_z (len + 1) l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_exact_z (len + 1) 0 l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= i < 10 ->
    0 <= j ->
    j < Znth i cnts 0 ->
    0 < Zlength (output_prefix_by_input_z i j l) ->
    out_len = output_used_capacity_prefix_by_input_z 10 l ->
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10 + 1 <= out_len /\
    string_length (output_prefix_by_input_z i j l) +
      string_length (number_word_z 10) + 1 < INT_MAX.
Proof.
  intros len l cnts i j out_len Hlen Hlen_int Hcap Hcnts Hscan Hexact
    Hi Hj Hjlt Hprefix_nonempty Hout.
  assert (Hcompleted_l :
    scan_completed_prefix_z (len + 1) 0 l = l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec 0 31) as [_ | Hbad]; [ | lia ].
    replace (Z.min (len + 1 - 0) (Zlength l)) with (Zlength l)
      by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  destruct_digit i.
  all: unfold scan_counts_z, scan_counts_capacity_z in Hscan;
    unfold scan_counts_exact_z in Hexact;
    rewrite Hcompleted_l in Hexact;
    unfold output_prefix_by_input_z, output_capacity_prefix_by_input_z,
      output_used_capacity_prefix_by_input_z, output_used_capacity_prefix_z,
      output_prefix_z, output_capacity_prefix_z in *;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end;
    repeat match goal with
    | H : Znth ?d ?cs 0 = ?v |- _ => rewrite H in *
    end;
    pose proof (count_number_words_weight_input_bound_19 l) as Hinput_weight;
    pose proof (Zlength_nonneg l) as Hlen_nonneg;
    assert (Hcw0_nonneg : 0 <= count_word_in_string 0 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw1_nonneg : 0 <= count_word_in_string 1 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw2_nonneg : 0 <= count_word_in_string 2 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw3_nonneg : 0 <= count_word_in_string 3 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw4_nonneg : 0 <= count_word_in_string 4 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw5_nonneg : 0 <= count_word_in_string 5 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw6_nonneg : 0 <= count_word_in_string 6 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw7_nonneg : 0 <= count_word_in_string 7 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw8_nonneg : 0 <= count_word_in_string 8 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw9_nonneg : 0 <= count_word_in_string 9 l)
      by (unfold count_word_in_string; lia);
    pose_repeated_length_bounds_19;
    unfold string_length, number_word_len_z, number_word_z in *;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
      end)
      with (1 + count_word_in_string 0 l * 5) in *;
    repeat match goal with
    | H : context [if Z.leb ?x 1 then 1 else ?x - 1] |- _ =>
        destruct (Z.leb_spec x 1); simpl in H
    | |- context [if Z.leb ?x 1 then 1 else ?x - 1] =>
        destruct (Z.leb_spec x 1); simpl
    end.
  all: change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5) in *.
  all: split; [nia | lia].
  all: try solve [lia].
Qed.

Lemma output_prefix_word_bounds_19 :
  forall len l cnts i j out_len,
    Zlength l = len ->
    1 + 6 * (len + 1) <= INT_MAX ->
    Zlength cnts = 10 ->
    scan_counts_z (len + 1) l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_exact_z (len + 1) 0 l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= i < 10 ->
    0 <= j ->
    j < Znth i cnts 0 ->
    out_len = output_used_capacity_prefix_by_input_z 10 l ->
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z i + 1 <= out_len /\
    string_length (output_prefix_by_input_z i j l) +
      string_length (number_word_z i) + 1 < INT_MAX.
Proof.
  intros len l cnts i j out_len Hlen Hcap Hcnts Hscan Hexact
    Hi Hj Hjlt Hout.
  assert (Hcompleted_l :
    scan_completed_prefix_z (len + 1) 0 l = l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec 0 31) as [_ | Hbad]; [ | lia ].
    replace (Z.min (len + 1 - 0) (Zlength l)) with (Zlength l)
      by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  destruct_digit i.
  all: unfold scan_counts_z, scan_counts_capacity_z in Hscan;
    unfold scan_counts_exact_z in Hexact;
    rewrite Hcompleted_l in Hexact;
    unfold output_prefix_by_input_z, output_capacity_prefix_by_input_z,
      output_used_capacity_prefix_by_input_z, output_used_capacity_prefix_z,
      output_prefix_z, output_capacity_prefix_z in *;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end;
    repeat match goal with
    | H : Znth ?d ?cs 0 = ?v |- _ => rewrite H in *
    end;
    pose proof (count_number_words_weight_input_bound_19 l) as Hinput_weight;
    pose proof (Zlength_nonneg l) as Hlen_nonneg;
    assert (Hcw0_nonneg : 0 <= count_word_in_string 0 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw1_nonneg : 0 <= count_word_in_string 1 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw2_nonneg : 0 <= count_word_in_string 2 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw3_nonneg : 0 <= count_word_in_string 3 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw4_nonneg : 0 <= count_word_in_string 4 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw5_nonneg : 0 <= count_word_in_string 5 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw6_nonneg : 0 <= count_word_in_string 6 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw7_nonneg : 0 <= count_word_in_string 7 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw8_nonneg : 0 <= count_word_in_string 8 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw9_nonneg : 0 <= count_word_in_string 9 l)
      by (unfold count_word_in_string; lia);
    pose_repeated_length_bounds_19;
    unfold string_length, number_word_len_z, number_word_z in *;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
      end)
      with (1 + count_word_in_string 0 l * 5) in *;
    repeat match goal with
    | H : context [if Z.leb ?x 1 then 1 else ?x - 1] |- _ =>
        destruct (Z.leb_spec x 1); simpl in H
    | |- context [if Z.leb ?x 1 then 1 else ?x - 1] =>
        destruct (Z.leb_spec x 1); simpl
    end.
  all: change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5) in *.
  all: try split; nia.
Qed.

Lemma output_prefix_space_word_bounds_19 :
  forall len l cnts i j out_len,
    Zlength l = len ->
    len + 1 < INT_MAX ->
    1 + 6 * (len + 1) <= INT_MAX ->
    Zlength cnts = 10 ->
    scan_counts_z (len + 1) l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    scan_counts_exact_z (len + 1) 0 l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= i < 10 ->
    0 <= j ->
    j < Znth i cnts 0 ->
    0 < Zlength (output_prefix_by_input_z i j l) ->
    out_len = output_used_capacity_prefix_by_input_z 10 l ->
    Zlength (output_prefix_by_input_z i j l) +
      number_word_len_z 10 + number_word_len_z i + 1 <= out_len /\
    string_length (output_prefix_by_input_z i j l ++ number_word_z 10) +
      string_length (number_word_z i) + 1 < INT_MAX.
Proof.
  intros len l cnts i j out_len Hlen Hlen_int Hcap Hcnts Hscan Hexact
    Hi Hj Hjlt Hprefix_nonempty Hout.
  assert (Hcompleted_l :
    scan_completed_prefix_z (len + 1) 0 l = l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec 0 31) as [_ | Hbad]; [ | lia ].
    replace (Z.min (len + 1 - 0) (Zlength l)) with (Zlength l)
      by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  destruct_digit i.
  all: unfold scan_counts_z, scan_counts_capacity_z in Hscan;
    unfold scan_counts_exact_z in Hexact;
    rewrite Hcompleted_l in Hexact;
    unfold output_prefix_by_input_z, output_capacity_prefix_by_input_z,
      output_used_capacity_prefix_by_input_z, output_used_capacity_prefix_z,
      output_prefix_z, output_capacity_prefix_z in *;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end;
    repeat match goal with
    | H : Znth ?d ?cs 0 = ?v |- _ => rewrite H in *
    end;
    pose proof (count_number_words_weight_input_bound_19 l) as Hinput_weight;
    pose proof (Zlength_nonneg l) as Hlen_nonneg;
    assert (Hcw0_nonneg : 0 <= count_word_in_string 0 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw1_nonneg : 0 <= count_word_in_string 1 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw2_nonneg : 0 <= count_word_in_string 2 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw3_nonneg : 0 <= count_word_in_string 3 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw4_nonneg : 0 <= count_word_in_string 4 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw5_nonneg : 0 <= count_word_in_string 5 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw6_nonneg : 0 <= count_word_in_string 6 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw7_nonneg : 0 <= count_word_in_string 7 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw8_nonneg : 0 <= count_word_in_string 8 l)
      by (unfold count_word_in_string; lia);
    assert (Hcw9_nonneg : 0 <= count_word_in_string 9 l)
      by (unfold count_word_in_string; lia);
    assert (Htotal_strict :
      1 + count_word_in_string 0 l * 5 +
      count_word_in_string 1 l * 4 +
      count_word_in_string 2 l * 4 +
      count_word_in_string 3 l * 6 +
      count_word_in_string 4 l * 5 +
      count_word_in_string 5 l * 5 +
      count_word_in_string 6 l * 4 +
      count_word_in_string 7 l * 6 +
      count_word_in_string 8 l * 6 +
      count_word_in_string 9 l * 5 < INT_MAX).
    {
      lia.
    }
    pose_repeated_length_bounds_19;
    unfold string_length, number_word_len_z, number_word_z in *;
    rewrite ?Zlength_app;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
      end)
      with (1 + count_word_in_string 0 l * 5) in *;
    repeat match goal with
    | H : context [if Z.leb ?x 1 then 1 else ?x - 1] |- _ =>
        destruct (Z.leb_spec x 1); simpl in H; [lia |]
    | |- context [if Z.leb ?x 1 then 1 else ?x - 1] =>
        destruct (Z.leb_spec x 1); simpl; [lia |]
    end;
    match goal with
    | Hnon : 0 < Zlength ?pref |- _ =>
        pose proof (billed_length_nonempty_19 pref Hnon) as Hprefix_billed
    end;
    repeat match goal with
    | H : context [billed_length_19
        (append_repeated_number_word_z ?p ?d ?c ?done)] |- _ =>
        rewrite (append_repeated_number_word_z_billed_length_19 p d c done
          ltac:(lia) ltac:(lia)) in H
    end;
    unfold billed_length_19 in *;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
       end)
      with (1 + count_word_in_string 0 l * 5) in *;
    (split; [lia | lia]).
  all: try solve [lia].
  all: unfold string_length, number_word_len_z, number_word_z in *;
    pose_repeated_length_bounds_19;
    rewrite ?Zlength_app;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
       end)
      with (1 + count_word_in_string 0 l * 5) in *;
    repeat match goal with
    | H : context [if Z.leb ?x 1 then 1 else ?x - 1] |- _ =>
        destruct (Z.leb_spec x 1); simpl in H; [lia |]
    | |- context [if Z.leb ?x 1 then 1 else ?x - 1] =>
        destruct (Z.leb_spec x 1); simpl; [lia |]
    end;
    match goal with
    | Hnon : 0 < Zlength ?pref |- _ =>
        pose proof (billed_length_nonempty_19 pref Hnon) as Hprefix_billed
    end;
    repeat match goal with
    | H : context [billed_length_19
        (append_repeated_number_word_z ?p ?d ?c ?done)] |- _ =>
        rewrite (append_repeated_number_word_z_billed_length_19 p d c done
          ltac:(lia) ltac:(lia)) in H
    end;
    unfold billed_length_19 in *;
    cbn in *;
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
       end)
      with (1 + count_word_in_string 0 l * 5) in *;
    (split; [lia | lia]).
Qed.

Lemma output_prefix_by_input_step_19 :
  forall i j l,
    0 <= i < 10 ->
    0 <= j ->
    output_prefix_by_input_z i (j + 1) l =
    append_number_word_z (output_prefix_by_input_z i j l) i.
Proof.
  intros i j l Hi Hj.
  destruct_digit i;
    unfold output_prefix_by_input_z, output_prefix_z;
    cbn;
    rewrite append_repeated_number_word_z_step by lia;
    reflexivity.
Qed.

Lemma output_prefix_by_input_next_row_19 :
  forall len l cnts i j,
    Zlength l = len ->
    Zlength cnts = 10 ->
    scan_counts_exact_z (len + 1) 0 l
      (Znth 0 cnts 0) (Znth 1 cnts 0) (Znth 2 cnts 0)
      (Znth 3 cnts 0) (Znth 4 cnts 0) (Znth 5 cnts 0)
      (Znth 6 cnts 0) (Znth 7 cnts 0) (Znth 8 cnts 0)
      (Znth 9 cnts 0) ->
    0 <= i < 10 ->
    j = Znth i cnts 0 ->
    output_prefix_by_input_z i j l =
    output_prefix_by_input_z (i + 1) 0 l.
Proof.
  intros len l cnts i j Hlen _ Hexact Hi Hj.
  assert (Hcompleted_l :
    scan_completed_prefix_z (len + 1) 0 l = l).
  {
    unfold scan_completed_prefix_z.
    destruct (Z.ltb_spec 0 31) as [_ | Hbad]; [ | lia ].
    replace (Z.min (len + 1 - 0) (Zlength l)) with (Zlength l)
      by lia.
    rewrite sublist_self by reflexivity.
    reflexivity.
  }
  unfold scan_counts_exact_z in Hexact.
  rewrite Hcompleted_l in Hexact.
  destruct Hexact as
    [Hc0 [Hc1 [Hc2 [Hc3 [Hc4 [Hc5 [Hc6 [Hc7 [Hc8 Hc9]]]]]]]]].
  destruct_digit i.
  all: unfold output_prefix_by_input_z, output_prefix_z.
  all: rewrite ?Hj, ?Hc0, ?Hc1, ?Hc2, ?Hc3, ?Hc4, ?Hc5, ?Hc6, ?Hc7, ?Hc8, ?Hc9.
  all: reflexivity.
Qed.

Lemma output_final_length_used_capacity_19 :
  forall l,
    Zlength (output_prefix_by_input_z 10 0 l) + 1 =
    output_used_capacity_prefix_by_input_z 10 l.
Proof.
  intros l.
  assert (Hcw0_nonneg : 0 <= count_word_in_string 0 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw1_nonneg : 0 <= count_word_in_string 1 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw2_nonneg : 0 <= count_word_in_string 2 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw3_nonneg : 0 <= count_word_in_string 3 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw4_nonneg : 0 <= count_word_in_string 4 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw5_nonneg : 0 <= count_word_in_string 5 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw6_nonneg : 0 <= count_word_in_string 6 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw7_nonneg : 0 <= count_word_in_string 7 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw8_nonneg : 0 <= count_word_in_string 8 l)
    by (unfold count_word_in_string; lia).
  assert (Hcw9_nonneg : 0 <= count_word_in_string 9 l)
    by (unfold count_word_in_string; lia).
  unfold output_prefix_by_input_z, output_prefix_z.
  change
    (match 10 with
     | 0 => append_repeated_number_word_z [] 0
              (count_word_in_string 0 l) 0
     | 1 => append_repeated_number_word_z
              (append_repeated_number_word_z [] 0
                 (count_word_in_string 0 l) (count_word_in_string 0 l))
              1 (count_word_in_string 1 l) 0
     | 2 => append_repeated_number_word_z
              (append_repeated_number_word_z
              (append_repeated_number_word_z [] 0
                 (count_word_in_string 0 l) (count_word_in_string 0 l))
                1 (count_word_in_string 1 l) (count_word_in_string 1 l))
              2 (count_word_in_string 2 l) 0
     | _ => sorted_numbers_output_by_counts_z
              (count_word_in_string 0 l) (count_word_in_string 1 l)
              (count_word_in_string 2 l) (count_word_in_string 3 l)
              (count_word_in_string 4 l) (count_word_in_string 5 l)
              (count_word_in_string 6 l) (count_word_in_string 7 l)
              (count_word_in_string 8 l) (count_word_in_string 9 l)
     end)
    with (sorted_numbers_output_by_counts_z
      (count_word_in_string 0 l) (count_word_in_string 1 l)
      (count_word_in_string 2 l) (count_word_in_string 3 l)
      (count_word_in_string 4 l) (count_word_in_string 5 l)
      (count_word_in_string 6 l) (count_word_in_string 7 l)
      (count_word_in_string 8 l) (count_word_in_string 9 l)).
  set (final :=
    sorted_numbers_output_by_counts_z
      (count_word_in_string 0 l) (count_word_in_string 1 l)
      (count_word_in_string 2 l) (count_word_in_string 3 l)
      (count_word_in_string 4 l) (count_word_in_string 5 l)
      (count_word_in_string 6 l) (count_word_in_string 7 l)
      (count_word_in_string 8 l) (count_word_in_string 9 l)).
  assert (Hbilled :
    billed_length_19 final =
      count_word_in_string 0 l * 5 +
      count_word_in_string 1 l * 4 +
      count_word_in_string 2 l * 4 +
      count_word_in_string 3 l * 6 +
      count_word_in_string 4 l * 5 +
      count_word_in_string 5 l * 5 +
      count_word_in_string 6 l * 4 +
      count_word_in_string 7 l * 6 +
      count_word_in_string 8 l * 6 +
      count_word_in_string 9 l * 5).
  {
    unfold final, sorted_numbers_output_by_counts_z.
    repeat rewrite append_repeated_number_word_z_billed_length_19 by lia.
    unfold billed_length_19, number_word_len_z, number_word_z.
    cbn.
    lia.
  }
  unfold output_used_capacity_prefix_by_input_z, output_used_capacity_prefix_z,
    output_capacity_prefix_z, number_word_len_z, number_word_z.
  cbn.
  change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5).
  unfold billed_length_19 in Hbilled.
  destruct (Z.eqb (Zlength final) 0) eqn:Hfinal_empty.
  - apply Z.eqb_eq in Hfinal_empty.
    rewrite Hfinal_empty in *.
    destruct (Z.leb_spec
      (1 + count_word_in_string 0 l * 5 +
       count_word_in_string 1 l * 4 + count_word_in_string 2 l * 4 +
       count_word_in_string 3 l * 6 + count_word_in_string 4 l * 5 +
       count_word_in_string 5 l * 5 + count_word_in_string 6 l * 4 +
       count_word_in_string 7 l * 6 + count_word_in_string 8 l * 6 +
       count_word_in_string 9 l * 5) 1); lia.
  - apply Z.eqb_neq in Hfinal_empty.
    assert (Hfinal_pos : 0 < Zlength final).
    {
      pose proof (Zlength_nonneg final).
      lia.
    }
    assert (Hweight_gt :
      1 <
      count_word_in_string 0 l * 5 +
      count_word_in_string 1 l * 4 +
      count_word_in_string 2 l * 4 +
      count_word_in_string 3 l * 6 +
      count_word_in_string 4 l * 5 +
      count_word_in_string 5 l * 5 +
      count_word_in_string 6 l * 4 +
      count_word_in_string 7 l * 6 +
      count_word_in_string 8 l * 6 +
      count_word_in_string 9 l * 5).
    {
      lia.
    }
    destruct (Z.leb_spec
      (1 + count_word_in_string 0 l * 5 +
       count_word_in_string 1 l * 4 + count_word_in_string 2 l * 4 +
       count_word_in_string 3 l * 6 + count_word_in_string 4 l * 5 +
       count_word_in_string 5 l * 5 + count_word_in_string 6 l * 4 +
       count_word_in_string 7 l * 6 + count_word_in_string 8 l * 6 +
       count_word_in_string 9 l * 5) 1); lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_1 : sort_numbers_entail_wit_15_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_2 : sort_numbers_entail_wit_15_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_3 : sort_numbers_entail_wit_15_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_4 : sort_numbers_entail_wit_15_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_5 : sort_numbers_entail_wit_15_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_6 : sort_numbers_entail_wit_15_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_7 : sort_numbers_entail_wit_15_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15_split_goal_spatial : sort_numbers_entail_wit_15_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_15 : sort_numbers_entail_wit_15.
Proof.
  right.
  pre_process; subst.
  unfold store_string, c_string.
  rewrite PreH24.
  sep_apply (number_words_missing_merge_vc_char_first
    (&( "words")) i
    (Znth i (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") ::
      &( "w4") :: &( "w5") :: &( "w6") :: &( "w7") ::
      &( "w8") :: &( "w9") :: nil) 0)
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))
    ltac:(lia)
    ltac:(reflexivity)).
  pose proof (output_capacity_next_props_19 (Zlength l) l cnts_2 i
    (output_capacity_prefix_by_input_z i l) (string_length (number_word_z i))
    ltac:(reflexivity) PreH12 PreH18 PreH19 PreH20 (conj PreH21 PreH22)
    ltac:(reflexivity) ltac:(reflexivity) PreH26 PreH28 PreH31) as
    [Hi_next [Hvalid_next [Houtpos_next [Hout_next
      [Hcnt_next [Hlen_next [Hint_next Hcap_next]]]]]]].
  repeat apply _derivable1_andp_intros;
    try solve [apply derivable1s_coq_prop_r; eauto].
  - apply derivable1s_coq_prop_r.
    intros Hrange.
    destruct (Hvalid_next Hrange) as [Hv [Hlen_word Hlt_word]].
    split; [split |]; assumption.
  - entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_16_1_split_goal_1 : sort_numbers_entail_wit_16_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_1_split_goal_2 : sort_numbers_entail_wit_16_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_1_split_goal_3 : sort_numbers_entail_wit_16_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_1_split_goal_spatial : sort_numbers_entail_wit_16_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_1 : sort_numbers_entail_wit_16_1.
Proof.
  right.
  pre_process; subst.
  assert (Hi10 : i = 10) by lia.
  subst i.
  assert (Hempty : output_prefix_by_input_z 0 0 l = []) by reflexivity.
  assert (Hcap_gt : 1 < output_capacity_prefix_by_input_z 10 l) by lia.
  assert (Hused :
    output_capacity_prefix_by_input_z 10 l - 1 =
      output_used_capacity_prefix_by_input_z 10 l).
  {
    unfold output_used_capacity_prefix_by_input_z,
      output_used_capacity_prefix_z.
    fold (output_capacity_prefix_by_input_z 10 l).
    destruct (Z.leb_spec (output_capacity_prefix_by_input_z 10 l) 1);
      lia.
  }
  assert (Hcap_minus :
    1 <=
    1 + count_word_in_string 0 l * 5 +
    count_word_in_string 1 l * 4 + count_word_in_string 2 l * 4 +
    count_word_in_string 3 l * 6 + count_word_in_string 4 l * 5 +
    count_word_in_string 5 l * 5 + count_word_in_string 6 l * 4 +
    count_word_in_string 7 l * 6 + count_word_in_string 8 l * 6 +
    count_word_in_string 9 l * 5 - 1).
  {
    unfold output_capacity_prefix_by_input_z, output_capacity_prefix_z in Hcap_gt.
    unfold number_word_len_z, number_word_z in Hcap_gt.
    cbn in Hcap_gt.
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
       end)
      with (1 + count_word_in_string 0 l * 5) in Hcap_gt.
    lia.
  }
  rewrite Hempty.
  unfold c_string.
  unfold CharArray.full, store_array.
  cbn.
  entailer!;
    try exact PreH6;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH11;
    try exact PreH12;
    try exact PreH13;
    try exact PreH14;
    try exact PreH15;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact Hused;
    try exact Hcap_minus;
    try lia.
  all: change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5);
    lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_16_2_split_goal_1 : sort_numbers_entail_wit_16_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_2_split_goal_2 : sort_numbers_entail_wit_16_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_2_split_goal_3 : sort_numbers_entail_wit_16_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_2_split_goal_spatial : sort_numbers_entail_wit_16_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_16_2 : sort_numbers_entail_wit_16_2.
Proof.
  right.
  pre_process; subst.
  assert (Hi10 : i = 10) by lia.
  subst i.
  assert (Hout_one : output_capacity_prefix_by_input_z 10 l = 1) by lia.
  assert (Hcap_le : output_capacity_prefix_by_input_z 10 l <= 1) by lia.
  assert (Hempty : output_prefix_by_input_z 0 0 l = []) by reflexivity.
  assert (Hused :
    output_capacity_prefix_by_input_z 10 l =
      output_used_capacity_prefix_by_input_z 10 l).
  {
    rewrite Hout_one.
    unfold output_used_capacity_prefix_by_input_z,
      output_used_capacity_prefix_z.
    fold (output_capacity_prefix_by_input_z 10 l).
    destruct (Z.leb_spec (output_capacity_prefix_by_input_z 10 l) 1);
      lia.
  }
  assert (Hcap_expr_one :
    1 + count_word_in_string 0 l * 5 +
    count_word_in_string 1 l * 4 + count_word_in_string 2 l * 4 +
    count_word_in_string 3 l * 6 + count_word_in_string 4 l * 5 +
    count_word_in_string 5 l * 5 + count_word_in_string 6 l * 4 +
    count_word_in_string 7 l * 6 + count_word_in_string 8 l * 6 +
    count_word_in_string 9 l * 5 = 1).
  {
    unfold output_capacity_prefix_by_input_z, output_capacity_prefix_z in Hout_one.
    unfold number_word_len_z, number_word_z in Hout_one.
    cbn in Hout_one.
    change
      (match count_word_in_string 0 l * 5 with
       | 0 => 1
       | Z.pos y' =>
           Z.pos
             match y' with
             | xI q => xO (Pos.succ q)
             | xO q => xI q
             | xH => xO xH
             end
       | Z.neg y' => Z.pos_sub 1 y'
       end)
      with (1 + count_word_in_string 0 l * 5) in Hout_one.
    lia.
  }
  rewrite Hempty.
  unfold c_string.
  unfold CharArray.full, store_array.
  cbn.
  entailer!;
    try exact PreH6;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH11;
    try exact PreH12;
    try exact PreH13;
    try exact PreH14;
    try exact PreH15;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact Hused;
    try lia.
  all: change
    (match count_word_in_string 0 l * 5 with
     | 0 => 1
     | Z.pos y' =>
         Z.pos
           match y' with
           | xI q => xO (Pos.succ q)
           | xO q => xI q
           | xH => xO xH
           end
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (1 + count_word_in_string 0 l * 5).
  all: replace
    (1 + count_word_in_string 0 l * 5 +
     count_word_in_string 1 l * 4 + count_word_in_string 2 l * 4 +
     count_word_in_string 3 l * 6 + count_word_in_string 4 l * 5 +
     count_word_in_string 5 l * 5 + count_word_in_string 6 l * 4 +
     count_word_in_string 7 l * 6 + count_word_in_string 8 l * 6 +
     count_word_in_string 9 l * 5) with 1 by lia.
  all: rewrite (CharArray.undef_seg_empty retval 1); entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_17_split_goal_1 : sort_numbers_entail_wit_17_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_17_split_goal_2 : sort_numbers_entail_wit_17_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_17_split_goal_3 : sort_numbers_entail_wit_17_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_17_split_goal_spatial : sort_numbers_entail_wit_17_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_17 : sort_numbers_entail_wit_17.
Proof.
  pre_process; subst.
  pose proof (number_word_valid_digit_19 i (conj PreH19 PreH1)) as
    [[Hvalid_i Hlen_i] Hlt_i].
  Exists cnts_2
    (Znth i (&( "w0") :: &( "w1") :: &( "w2") :: &( "w3") ::
      &( "w4") :: &( "w5") :: &( "w6") :: &( "w7") ::
      &( "w8") :: &( "w9") :: nil) 0).
  sep_apply (number_words_full_split_19
    (&( "words")) i (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3"))
    (&( "w4")) (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8"))
    (&( "w9"))); [ | lia ].
  entailer!;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact Hvalid_i;
    try exact Hlen_i;
    try exact Hlt_i;
    try lia.
  all: try solve [unfold number_word_ptrs_z; reflexivity | lia].
  unfold number_word_ptrs_z.
  apply sepcon_tail_comm_19.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_1 : sort_numbers_entail_wit_18_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_2 : sort_numbers_entail_wit_18_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_3 : sort_numbers_entail_wit_18_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_4 : sort_numbers_entail_wit_18_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_5 : sort_numbers_entail_wit_18_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_6 : sort_numbers_entail_wit_18_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_7 : sort_numbers_entail_wit_18_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18_split_goal_spatial : sort_numbers_entail_wit_18_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_18 : sort_numbers_entail_wit_18.
Proof.
  pre_process; subst.
  Exists cnts_2.
  unfold store_string, c_string.
  entailer!;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact valid_string_space_19;
    try (apply valid_string_output_prefix_by_input_19; lia);
    try (eapply scan_counts_digit_bound_19; eauto; lia);
    try lia.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_1 : sort_numbers_entail_wit_19_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_2 : sort_numbers_entail_wit_19_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_3 : sort_numbers_entail_wit_19_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_4 : sort_numbers_entail_wit_19_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_5 : sort_numbers_entail_wit_19_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19_split_goal_spatial : sort_numbers_entail_wit_19_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_19 : sort_numbers_entail_wit_19.
Proof.
  left.
  pre_process.
  pose proof (output_prefix_space_bounds_19 len l cnts_2 i j out_len
    PreH15 PreH13 PreH14 PreH21 PreH22 PreH23 (conj PreH24 PreH25)
    PreH26 PreH2 (PreH30 PreH1) PreH32) as [Hspace_bound Hspace_int].
  assert (Hspace_split :
    Zlength (output_prefix_by_input_z i j l) + 1 <=
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10 + 1 <=
    out_len).
  { split; [rewrite PreH8; lia | exact Hspace_bound]. }
  Exists cnts_2.
  unfold store_string, c_string.
  sep_apply (CharArray.undef_seg_split_to_undef_seg out
    (Zlength (output_prefix_by_input_z i j l) + 1)
    ((Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10) + 1)
    out_len).
  entailer!;
    try exact PreH21;
    try exact PreH22;
    try exact PreH23;
    try exact Hspace_split;
    try exact Hspace_bound;
    try exact Hspace_int;
    try lia.
  exact Hspace_split.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_1 : sort_numbers_entail_wit_20_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_2 : sort_numbers_entail_wit_20_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_3 : sort_numbers_entail_wit_20_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_4 : sort_numbers_entail_wit_20_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_5 : sort_numbers_entail_wit_20_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_6 : sort_numbers_entail_wit_20_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_7 : sort_numbers_entail_wit_20_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20_split_goal_spatial : sort_numbers_entail_wit_20_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_20 : sort_numbers_entail_wit_20.
Proof.
  left.
  pre_process.
  pose proof (output_prefix_space_word_bounds_19 len l cnts_2 i j out_len
    PreH12 PreH10 PreH11 PreH18 PreH19 PreH20 (conj PreH21 PreH22)
    PreH23 PreH24 PreH26 PreH27) as [Hword_bound Hword_int].
  pose proof (number_word_valid_digit_19 i (conj PreH21 PreH22)) as
    [[Hvalid_i Hlen_i] Hlt_i].
  assert (Hspace_valid :
    valid_string (output_prefix_by_input_z i j l ++ number_word_z 10)).
  {
    apply valid_string_app_19; assumption.
  }
  assert (Hspace_len :
    string_length (output_prefix_by_input_z i j l ++ number_word_z 10) =
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10).
  {
    unfold string_length in *.
    rewrite Zlength_app.
    lia.
  }
  assert (Hword_len_nonneg : 0 <= number_word_len_z i).
  {
    rewrite <- Hlen_i.
    unfold string_length.
    apply Zlength_nonneg.
  }
  assert (Hword_split :
    (Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10) + 1 <=
    ((Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10) +
      number_word_len_z i) + 1 <= out_len).
  { split; [lia | exact Hword_bound]. }
  Exists cnts_2.
  unfold store_string, c_string.
  sep_apply (CharArray.undef_seg_split_to_undef_seg out
    ((Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10) + 1)
    (((Zlength (output_prefix_by_input_z i j l) + number_word_len_z 10) +
      number_word_len_z i) + 1)
    out_len).
  entailer!;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact Hvalid_i;
    try exact Hlen_i;
    try exact Hlt_i;
    try exact Hspace_valid;
    try exact Hspace_len;
    try exact Hword_int;
    try exact Hword_bound;
    try exact Hword_split;
    try lia.
  exact Hword_split.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_1 : sort_numbers_entail_wit_21_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_2 : sort_numbers_entail_wit_21_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_3 : sort_numbers_entail_wit_21_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_4 : sort_numbers_entail_wit_21_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_5 : sort_numbers_entail_wit_21_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21_split_goal_spatial : sort_numbers_entail_wit_21_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_21 : sort_numbers_entail_wit_21.
Proof.
  left.
  pre_process.
  pose proof (output_prefix_word_bounds_19 len l cnts_2 i j out_len
    PreH15 PreH14 PreH21 PreH22 PreH23 (conj PreH24 PreH25)
    PreH26 PreH2 PreH32) as [Hword_space_bound Hword_space_int].
  pose proof (number_word_valid_digit_19 i (conj PreH24 PreH25)) as
    [[Hvalid_i Hlen_i] Hlt_i].
  assert (Hspace_len :
    string_length (output_prefix_by_input_z i j l ++ number_word_z 10) =
    string_length (output_prefix_by_input_z i j l) + number_word_len_z 10).
  {
    unfold string_length in *.
    rewrite Zlength_app.
    lia.
  }
  assert (Hword_int :
    string_length (output_prefix_by_input_z i j l) +
      string_length (number_word_z i) + 1 < INT_MAX).
  {
    exact Hword_space_int.
  }
  assert (Hword_bound :
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z i + 1 <=
    out_len).
  { rewrite <- (Z.add_0_l (number_word_len_z i)) at 1; lia. }
  assert (Hword_len_nonneg : 0 <= number_word_len_z i).
  {
    rewrite <- Hlen_i.
    unfold string_length.
    apply Zlength_nonneg.
  }
  assert (Hword_split :
    Zlength (output_prefix_by_input_z i j l) + 1 <=
    Zlength (output_prefix_by_input_z i j l) + number_word_len_z i + 1 <=
    out_len).
  { split; lia. }
  Exists cnts_2.
  unfold store_string, c_string.
  sep_apply (CharArray.undef_seg_split_to_undef_seg out
    (Zlength (output_prefix_by_input_z i j l) + 1)
    (Zlength (output_prefix_by_input_z i j l) + number_word_len_z i + 1)
    out_len).
  entailer!;
    try exact PreH21;
    try exact PreH22;
    try exact PreH23;
    try exact Hvalid_i;
    try exact Hlen_i;
    try exact Hlt_i;
    try exact Hword_int;
    try exact Hword_bound;
    try exact Hword_split;
    try lia.
  exact Hword_split.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_1 : sort_numbers_entail_wit_22_1_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_2 : sort_numbers_entail_wit_22_1_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_3 : sort_numbers_entail_wit_22_1_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_4 : sort_numbers_entail_wit_22_1_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_5 : sort_numbers_entail_wit_22_1_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_6 : sort_numbers_entail_wit_22_1_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_7 : sort_numbers_entail_wit_22_1_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_8 : sort_numbers_entail_wit_22_1_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_9 : sort_numbers_entail_wit_22_1_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_10 : sort_numbers_entail_wit_22_1_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1_split_goal_spatial : sort_numbers_entail_wit_22_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_1 : sort_numbers_entail_wit_22_1.
Proof.
  left.
  intros numbers_pre len l cnts_2 out space_word word tlen out_len i j first
    retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  pose proof (output_prefix_by_input_step_19 i j l
    (conj PreH21 PreH22) PreH23) as Hstep.
  unfold append_number_word_z in Hstep.
  assert (Hprefix_pos : 0 < Zlength (output_prefix_by_input_z i j l))
    by exact PreH26.
  assert (Hprefix_ne : Zlength (output_prefix_by_input_z i j l) <> 0)
    by lia.
  destruct (Z.eqb_spec (Zlength (output_prefix_by_input_z i j l)) 0)
    as [Hprefix_empty | Hprefix_nonempty];
    [contradiction |].
  cbn in Hstep.
  assert (Hspace_valid : valid_string (number_word_z 10)).
  { change (valid_string [32]); exact valid_string_space_19. }
  assert (Hspace_len :
    string_length (number_word_z 10) = number_word_len_z 10).
  { unfold string_length, number_word_len_z, number_word_z; cbn; reflexivity. }
  assert (Hspace_int : string_length (number_word_z 10) < INT_MAX).
  { unfold string_length, number_word_z; cbn; lia. }
  assert (Hspace_word_len : number_word_len_z 10 = 1).
  { unfold number_word_len_z, number_word_z; cbn; reflexivity. }
  assert (Hspace_c_len : Zlength (number_word_z 10 ++ 0 :: nil) = 2).
  { unfold number_word_z; cbn; reflexivity. }
  Exists cnts_2.
  rewrite Hstep.
  unfold store_string, c_string.
  change (number_word_z 10) with [32] in *.
  change (number_word_len_z 10) with 1 in *.
  rewrite ?app_assoc in *.
  assert (Hnext_valid :
    valid_string ((output_prefix_by_input_z i j l ++ 32 :: number_word_z i)%list)).
  {
    change (valid_string ((output_prefix_by_input_z i j l ++ [32] ++ number_word_z i)%list)).
    rewrite List.app_assoc.
    apply valid_string_app_19; [exact PreH31 | exact PreH28].
  }
  assert (Hnext_nonempty :
    0 < Zlength ((output_prefix_by_input_z i j l ++ 32 :: number_word_z i)%list)).
  {
    rewrite Zlength_app, Zlength_cons.
    pose proof (Zlength_nonneg (number_word_z i)).
    lia.
  }
  change (output_prefix_by_input_z i j l +:: 32)
    with ((output_prefix_by_input_z i j l ++ [32])%list) in *.
  rewrite <- (List.app_assoc (output_prefix_by_input_z i j l)
    [32] (number_word_z i)) in *.
  unfold string_length in *.
  rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *.
  cbn in *.
  fold (Z.succ (Zlength (number_word_z i))) in *.
  replace (Zlength (number_word_z i) + 1)
    with (number_word_len_z i + 1) by lia.
  replace (Zlength (output_prefix_by_input_z i j l) + 1 +
      number_word_len_z i + 1)
    with (Zlength (output_prefix_by_input_z i j l) +
      Z.succ (Zlength (number_word_z i)) + 1) by lia.
  entailer!;
    try exact PreH6;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH11;
    try exact PreH12;
    try exact PreH13;
    try exact PreH14;
    try exact PreH15;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact PreH21;
    try exact PreH22;
    try exact PreH23;
    try exact PreH24;
    try exact PreH25;
    try exact PreH26;
    try exact PreH27;
    try exact PreH28;
    try exact PreH29;
    try exact PreH30;
    try exact Hspace_valid;
    try exact Hspace_len;
    try exact Hspace_int;
    try exact Hspace_word_len;
    try exact Hspace_c_len;
    try exact Hnext_valid;
    try exact Hnext_nonempty;
    try lia.
  all: fold (Z.succ (Zlength (number_word_z i))).
  all: replace (number_word_len_z i + 1)
    with (Z.succ (Zlength (number_word_z i))) by lia.
  all: replace (Zlength (output_prefix_by_input_z i j l) +
      match Zlength (number_word_z i) with
      | 0 => 1
      | Z.pos y' => Z.pos (Pos.succ y')
      | Z.neg y' => Z.pos_sub 1 y'
      end + 1)
    with (Zlength (output_prefix_by_input_z i j l) +
      Z.succ (Zlength (number_word_z i)) + 1)
    by (destruct (Zlength (number_word_z i)); cbn; lia).
  all: entailer!.
  all: change
    (match Zlength (number_word_z i) with
     | 0 => 1
     | Z.pos y' => Z.pos (Pos.succ y')
     | Z.neg y' => Z.pos_sub 1 y'
     end)
    with (Z.succ (Zlength (number_word_z i))).
  all: entailer!.
  all: unfold Z.succ.
  all: entailer!.
  all: cancel.
  all: pose proof (Zlength_nonneg (number_word_z i)).
  all: destruct (Zlength (number_word_z i)); cbn in *; try lia; entailer!.
  all: try change (Z.pos (Pos.succ p)) with (Z.succ (Z.pos p)).
  all: try change (Z.pos (p + 1)) with (Z.succ (Z.pos p)).
  all: entailer!.
  all: destruct p; cbn; entailer!.
Qed. 

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_1 : sort_numbers_entail_wit_22_2_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_2 : sort_numbers_entail_wit_22_2_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_3 : sort_numbers_entail_wit_22_2_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_4 : sort_numbers_entail_wit_22_2_split_goal_4.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_5 : sort_numbers_entail_wit_22_2_split_goal_5.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_6 : sort_numbers_entail_wit_22_2_split_goal_6.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_7 : sort_numbers_entail_wit_22_2_split_goal_7.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_8 : sort_numbers_entail_wit_22_2_split_goal_8.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_9 : sort_numbers_entail_wit_22_2_split_goal_9.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_10 : sort_numbers_entail_wit_22_2_split_goal_10.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2_split_goal_spatial : sort_numbers_entail_wit_22_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_22_2 : sort_numbers_entail_wit_22_2.
Proof.
  left.
  intros numbers_pre len l cnts_2 out space_word word tlen out_len i j first
    retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
    PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34.
  pose proof (output_prefix_by_input_step_19 i j l
    (conj PreH21 PreH22) PreH23) as Hstep.
  unfold append_number_word_z in Hstep.
  destruct (Z.eqb_spec (Zlength (output_prefix_by_input_z i j l)) 0)
    as [Hprefix_empty | Hprefix_nonempty]; [ | lia ].
  cbn in Hstep.
  assert (Hspace_valid : valid_string (number_word_z 10)).
  { change (valid_string [32]); exact valid_string_space_19. }
  assert (Hspace_len :
    string_length (number_word_z 10) = number_word_len_z 10).
  { unfold string_length, number_word_len_z, number_word_z; cbn; reflexivity. }
  assert (Hspace_int : string_length (number_word_z 10) < INT_MAX).
  { unfold string_length, number_word_z; cbn; lia. }
  assert (Hspace_word_len : number_word_len_z 10 = 1).
  { unfold number_word_len_z, number_word_z; cbn; reflexivity. }
  assert (Hspace_c_len : Zlength (number_word_z 10 ++ 0 :: nil) = 2).
  { unfold number_word_z; cbn; reflexivity. }
  assert (Hnext_valid :
    valid_string (output_prefix_by_input_z i (j + 1) l)).
  {
    rewrite Hstep.
    apply valid_string_app_19; [exact PreH28 | exact PreH30].
  }
  assert (Hnext_len :
    string_length (output_prefix_by_input_z i (j + 1) l) =
    Zlength (output_prefix_by_input_z i (j + 1) l)).
  {
    unfold string_length.
    reflexivity.
  }
  assert (Hword_nonempty : 0 < Zlength (number_word_z i)).
  {
    destruct_digit i; unfold number_word_z; cbn; lia.
  }
  assert (Hnext_nonempty :
    0 < Zlength (output_prefix_by_input_z i (j + 1) l)).
  {
    rewrite Hstep, Zlength_app.
    lia.
  }
  Exists cnts_2.
  rewrite Hstep.
  unfold store_string, c_string.
  unfold string_length in *.
  rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in *.
  cbn in *.
  entailer!;
    try exact PreH6;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH11;
    try exact PreH12;
    try exact PreH13;
    try exact PreH14;
    try exact PreH15;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact PreH21;
    try exact PreH22;
    try exact PreH23;
    try exact PreH24;
    try exact PreH27;
    try exact PreH28;
    try exact PreH29;
    try exact PreH30;
    try exact PreH31;
    try exact PreH32;
    try exact PreH33;
    try exact PreH34;
    try exact Hspace_valid;
    try exact Hspace_len;
    try exact Hspace_int;
    try exact Hspace_word_len;
    try exact Hspace_c_len;
    try exact Hnext_valid;
    try exact Hnext_len;
    try exact Hnext_nonempty;
    try lia.
  all: try (apply valid_string_app_19; [exact PreH28 | exact PreH30]).
  all: try (rewrite PreH31; cancel).
Qed. 

Lemma proof_of_sort_numbers_entail_wit_23_split_goal_1 : sort_numbers_entail_wit_23_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_23_split_goal_2 : sort_numbers_entail_wit_23_split_goal_2.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_23_split_goal_3 : sort_numbers_entail_wit_23_split_goal_3.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_23_split_goal_spatial : sort_numbers_entail_wit_23_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_23 : sort_numbers_entail_wit_23.
Proof.
  left.
  pre_process.
  assert (Hj_eq : j = Znth i cnts_2 0) by lia.
  pose proof (output_prefix_by_input_next_row_19 len l cnts_2 i j
    PreH14 PreH20 PreH22 (conj PreH23 PreH24) Hj_eq) as Hrow.
  assert (Hprefix_bound :
    Zlength (output_prefix_by_input_z i j l) + 1 <= out_len).
  {
    exact PreH34.
  }
  rewrite <- Hrow in *.
  sepcon_lift (((&( "words") + i * sizeof(PTR)) # Ptr |-> word)).
  sepcon_lift (number_words_missing (&( "words")) i word
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))).
  sepcon_lift (CharArray.full word (number_word_len_z i + 1)
    (number_word_z i +:: 0)).
  sep_apply (number_words_missing_merge_vc_from_missing
    (&( "words")) i word
    (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
    (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9"))
    ltac:(lia)).
  Exists cnts_2.
  entailer!;
    try exact PreH6;
    try exact PreH7;
    try exact PreH8;
    try exact PreH9;
    try exact PreH10;
    try exact PreH11;
    try exact PreH12;
    try exact PreH13;
    try exact PreH14;
    try exact PreH15;
    try exact PreH16;
    try exact PreH17;
    try exact PreH18;
    try exact PreH19;
    try exact PreH20;
    try exact PreH21;
    try exact PreH22;
    try exact PreH23;
    try exact PreH24;
    try exact PreH25;
    try exact PreH26;
    try exact PreH27;
    try exact PreH28;
    try exact PreH29;
    try exact PreH30;
    try exact PreH31;
    try exact Hprefix_bound;
    try lia.
Qed. 

Local Open Scope list_scope.

Lemma ascii_of_z_inj_range_19 :
  forall x y,
    0 <= x <= 127 ->
    0 <= y <= 127 ->
    ascii_of_z_19 x = ascii_of_z_19 y ->
    x = y.
Proof.
  intros x y Hx Hy H.
  unfold ascii_of_z_19 in H.
  apply f_equal with (f := nat_of_ascii) in H.
  repeat rewrite nat_ascii_embedding in H by lia.
  lia.
Qed.

Lemma string_of_list_z_inj_range_19 :
  forall a b,
    (forall x, In x a -> 0 <= x <= 127) ->
    (forall x, In x b -> 0 <= x <= 127) ->
    string_of_list_z_19 a = string_of_list_z_19 b ->
    a = b.
Proof.
  induction a as [| ah tl IHa]; intros b Ha Hb Heq; destruct b as [| bh bt]; cbn in Heq.
  - reflexivity.
  - discriminate.
  - discriminate.
  - inversion Heq as [[Hhead Htail]].
    f_equal.
    + apply ascii_of_z_inj_range_19; auto.
      * apply Ha. left. reflexivity.
      * apply Hb. left. reflexivity.
    + apply IHa; auto.
      * intros x Hin. apply Ha. right. exact Hin.
      * intros x Hin. apply Hb. right. exact Hin.
Qed.

Lemma ascii_range_z_In_19 :
  forall l x,
    ascii_range_z l ->
    In x l ->
    0 <= x <= 127.
Proof.
  induction l as [| a l IH]; intros x Hrange Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + specialize (Hrange 0 ltac:(rewrite Zlength_correct; cbn; lia)).
      cbn in Hrange. exact Hrange.
    + apply IH; auto.
      intros i Hi.
      specialize (Hrange (i + 1) ltac:(rewrite Zlength_correct in *; cbn; lia)).
      cbn in Hrange.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hrange by lia.
      exact Hrange.
Qed.

Lemma number_word_z_range_19 :
  forall d x,
    0 <= d < 10 ->
    In x (number_word_z d) ->
    0 <= x <= 127.
Proof.
  intros d x Hd Hin.
  destruct_digit_cases_19 d; cbn in Hin; lia.
Qed.

Lemma number_word_string_WordToNum_19 :
  forall d,
    0 <= d < 10 ->
    WordToNum (number_word_string d) (Z.to_nat d).
Proof.
  intros d Hd.
  destruct_digit_cases_19 d; cbn; constructor.
Qed.

Lemma WordToNum_functional_19 :
  forall s n m,
    WordToNum s n ->
    WordToNum s m ->
    n = m.
Proof.
  intros s n m Hn Hm.
  destruct Hn; inversion Hm; reflexivity.
Qed.

Lemma number_word_string_inj_19 :
  forall d e,
    0 <= d < 10 ->
    0 <= e < 10 ->
    number_word_string d = number_word_string e ->
    d = e.
Proof.
  intros d e Hd He H.
  pose proof (number_word_string_WordToNum_19 d Hd) as Hdwt.
  pose proof (number_word_string_WordToNum_19 e He) as Hewt.
  rewrite H in Hdwt.
  pose proof (WordToNum_functional_19 _ _ _ Hdwt Hewt).
  lia.
Qed.

Lemma valid_string_of_z_token_number_word_19 :
  forall tok,
    (forall x, In x tok -> 0 <= x <= 127) ->
    is_valid_word (string_of_list_z_19 tok) ->
    exists d, 0 <= d < 10 /\ tok = number_word_z d.
Proof.
  intros tok Hrange [n Hword].
  remember (string_of_list_z_19 tok) as s eqn:Hs.
  let solve_digit d :=
    exists d;
    split; [lia|];
    apply string_of_list_z_inj_range_19;
    [ exact Hrange
    | intros x Hin; apply (number_word_z_range_19 d); [lia|exact Hin]
    | cbn; symmetry; exact Hs ] in
  destruct Hword; subst;
    [ solve_digit 0 | solve_digit 1 | solve_digit 2 | solve_digit 3 | solve_digit 4
    | solve_digit 5 | solve_digit 6 | solve_digit 7 | solve_digit 8 | solve_digit 9 ].
Qed.

Lemma SplitOnSpacesZ_aux_tokens_range_19 :
  forall input current,
    (forall x, In x current \/ In x input -> 0 <= x <= 127) ->
    Forall (fun tok => forall x, In x tok -> 0 <= x <= 127)
      (SplitOnSpacesZ_aux_19 current input).
Proof.
  induction input as [| h t IH]; intros current Hrange; cbn.
  - destruct current as [| c current].
    + constructor.
    + constructor.
      * intros x Hin. apply in_rev in Hin. apply Hrange. left. exact Hin.
      * constructor.
  - destruct (Z.eqb h 32) eqn:Hspace.
    + destruct current as [| c current].
      * apply IH. intros x [Hin | Hin]; [contradiction|].
        apply Hrange. right. right. exact Hin.
      * constructor.
        -- intros x Hin. apply in_rev in Hin. apply Hrange. left. exact Hin.
        -- apply IH. intros x [Hin | Hin]; [contradiction|].
           apply Hrange. right. right. exact Hin.
    + apply IH. intros x [Hin | Hin].
      * destruct Hin as [-> | Hin].
        -- apply Hrange. right. left. reflexivity.
        -- apply Hrange. left. exact Hin.
      * apply Hrange. right. right. exact Hin.
Qed.

Lemma SplitOnSpacesZ_tokens_range_19 :
  forall l,
    ascii_range_z l ->
    Forall (fun tok => forall x, In x tok -> 0 <= x <= 127) (SplitOnSpacesZ_19 l).
Proof.
  intros l Hrange.
  unfold SplitOnSpacesZ_19.
  apply SplitOnSpacesZ_aux_tokens_range_19.
  intros x [Hin | Hin].
  - contradiction.
  - eapply ascii_range_z_In_19; eauto.
Qed.

Definition append_number_word_string_19 (prefix : list string) (digit : Z)
  : list string :=
  prefix ++ [number_word_string digit].

Fixpoint append_repeated_number_word_strings_nat_19
  (prefix : list string) (digit : Z) (n : nat) : list string :=
  match n with
  | O => prefix
  | S n' =>
      append_number_word_string_19
        (append_repeated_number_word_strings_nat_19 prefix digit n') digit
  end.

Definition append_repeated_number_word_strings_z_19
  (prefix : list string) (digit count done : Z) : list string :=
  append_repeated_number_word_strings_nat_19 prefix digit (Z.to_nat done).

Definition sorted_number_words_by_counts_19
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : list string :=
  append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19
    (append_repeated_number_word_strings_z_19 [] 0 c0 c0)
      1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4)
      5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 c8) 9 c9 c9.

Lemma repeat_snoc_19 :
  forall {A : Type} (x : A) n,
    repeat x (S n) = (repeat x n ++ [x])%list.
Proof.
  induction n; cbn; intros; [reflexivity|].
  f_equal. exact IHn.
Qed.

Lemma append_repeated_number_word_strings_nat_eq_19 :
  forall n words d,
    append_repeated_number_word_strings_nat_19 words d n =
      (words ++ repeat (number_word_string d) n)%list.
Proof.
  induction n as [| n IH]; intros words d; cbn.
  - rewrite app_nil_r. reflexivity.
  - unfold append_number_word_string_19.
    rewrite IH.
    rewrite <- app_assoc.
    rewrite <- repeat_snoc_19.
    reflexivity.
Qed.

Lemma sorted_number_words_by_counts_eq_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 =
      (repeat (number_word_string 0) (Z.to_nat c0) ++
      repeat (number_word_string 1) (Z.to_nat c1) ++
      repeat (number_word_string 2) (Z.to_nat c2) ++
      repeat (number_word_string 3) (Z.to_nat c3) ++
      repeat (number_word_string 4) (Z.to_nat c4) ++
      repeat (number_word_string 5) (Z.to_nat c5) ++
      repeat (number_word_string 6) (Z.to_nat c6) ++
      repeat (number_word_string 7) (Z.to_nat c7) ++
      repeat (number_word_string 8) (Z.to_nat c8) ++
      repeat (number_word_string 9) (Z.to_nat c9))%list.
Proof.
  intros.
  unfold sorted_number_words_by_counts_19, append_repeated_number_word_strings_z_19.
  repeat rewrite append_repeated_number_word_strings_nat_eq_19.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma number_word_string_valid_19 :
  forall d,
    0 <= d < 10 ->
    is_valid_word (number_word_string d).
Proof.
  intros d Hd. exists (Z.to_nat d). apply number_word_string_WordToNum_19. exact Hd.
Qed.

Lemma Forall_repeat_19 :
  forall {A} (P : A -> Prop) x n,
    P x ->
    Forall P (repeat x n).
Proof.
  induction n; intros Hx; cbn; constructor; auto.
Qed.

Lemma sorted_number_words_valid_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    Forall is_valid_word
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).
Proof.
  intros.
  rewrite sorted_number_words_by_counts_eq_19.
  repeat (apply Forall_app; split);
    apply Forall_repeat_19; apply number_word_string_valid_19; lia.
Qed.

Lemma IsSorted_app_19 :
  forall a b,
    IsSorted a ->
    IsSorted b ->
    (forall x y nx ny,
      In x a -> In y b -> WordToNum x nx -> WordToNum y ny -> (nx <= ny)%nat) ->
    IsSorted (a ++ b).
Proof.
  intros a b Hsa Hsb Hcross.
  unfold IsSorted in *.
  intros i j Hij Hjlen si sj ni nj Hni Hnj Hwi Hwj.
  rewrite app_length in Hjlen.
  destruct (lt_dec i (length a)) as [Hia | Hia].
  - rewrite app_nth1 in Hni by exact Hia.
    destruct (lt_dec j (length a)) as [Hja | Hja].
    + rewrite app_nth1 in Hnj by exact Hja.
      exact (Hsa i j Hij Hja si sj ni nj Hni Hnj Hwi Hwj).
    + rewrite app_nth2 in Hnj by lia.
      eapply Hcross; eauto.
      * rewrite <- Hni. apply nth_In. exact Hia.
      * rewrite <- Hnj. apply nth_In. lia.
  - rewrite app_nth2 in Hni by lia.
    rewrite app_nth2 in Hnj by lia.
    apply (Hsb (i - length a)%nat (j - length a)%nat
      ltac:(lia) ltac:(lia) si sj ni nj); auto.
Qed.

Lemma nth_repeat_default_19 :
  forall {A : Type} (x d : A) n i,
    (i < n)%nat ->
    nth i (repeat x n) d = x.
Proof.
  induction n as [| n IH]; intros i Hi; [lia|].
  destruct i as [| i]; cbn; auto.
  apply IH. lia.
Qed.

Lemma IsSorted_repeat_number_word_19 :
  forall d n,
    0 <= d < 10 ->
    IsSorted (repeat (number_word_string d) n).
Proof.
  unfold IsSorted.
  intros d n Hd i j Hij Hjlen si sj ni nj Hni Hnj Hwi Hwj.
  rewrite repeat_length in Hjlen.
  assert (Hilen : (i < n)%nat).
  { apply (Nat.lt_trans _ j _); assumption. }
  rewrite (nth_repeat_default_19 (number_word_string d) "" n i) in Hni by exact Hilen.
  rewrite (nth_repeat_default_19 (number_word_string d) "" n j) in Hnj by exact Hjlen.
  subst si sj.
  pose proof (number_word_string_WordToNum_19 d Hd) as Hwd.
  pose proof (WordToNum_functional_19 _ _ _ Hwi Hwd) as ->.
  pose proof (WordToNum_functional_19 _ _ _ Hwj Hwd) as ->.
  lia.
Qed.

Definition AllNumLe_19 (m : nat) (l : list string) : Prop :=
  forall x nx, In x l -> WordToNum x nx -> (nx <= m)%nat.

Definition AllNumGe_19 (m : nat) (l : list string) : Prop :=
  forall x nx, In x l -> WordToNum x nx -> (m <= nx)%nat.

Lemma AllNumLe_app_19 :
  forall m a b,
    AllNumLe_19 m a ->
    AllNumLe_19 m b ->
    AllNumLe_19 m (a ++ b).
Proof.
  unfold AllNumLe_19.
  intros m a b Ha Hb x nx Hin Hwx.
  apply in_app_or in Hin. destruct Hin; eauto.
Qed.

Lemma AllNumGe_app_19 :
  forall m a b,
    AllNumGe_19 m a ->
    AllNumGe_19 m b ->
    AllNumGe_19 m (a ++ b).
Proof.
  unfold AllNumGe_19.
  intros m a b Ha Hb x nx Hin Hwx.
  apply in_app_or in Hin. destruct Hin; eauto.
Qed.

Lemma AllNumLe_weaken_19 :
  forall m n l,
    (m <= n)%nat ->
    AllNumLe_19 m l ->
    AllNumLe_19 n l.
Proof.
  unfold AllNumLe_19. intros; specialize (H0 x nx H1 H2); lia.
Qed.

Lemma AllNumGe_weaken_19 :
  forall m n l,
    (m <= n)%nat ->
    AllNumGe_19 n l ->
    AllNumGe_19 m l.
Proof.
  unfold AllNumGe_19. intros; specialize (H0 x nx H1 H2); lia.
Qed.

Lemma AllNumLe_repeat_number_word_19 :
  forall d m n,
    0 <= d < 10 ->
    (Z.to_nat d <= m)%nat ->
    AllNumLe_19 m (repeat (number_word_string d) n).
Proof.
  unfold AllNumLe_19.
  intros d m n Hd Hle x nx Hin Hwx.
  apply repeat_spec in Hin. subst x.
  pose proof (number_word_string_WordToNum_19 d ltac:(lia)) as Hwd.
  pose proof (WordToNum_functional_19 _ _ _ Hwx Hwd) as ->.
  exact Hle.
Qed.

Lemma AllNumGe_repeat_number_word_19 :
  forall d m n,
    0 <= d < 10 ->
    (m <= Z.to_nat d)%nat ->
    AllNumGe_19 m (repeat (number_word_string d) n).
Proof.
  unfold AllNumGe_19.
  intros d m n Hd Hge x nx Hin Hwx.
  apply repeat_spec in Hin. subst x.
  pose proof (number_word_string_WordToNum_19 d ltac:(lia)) as Hwd.
  pose proof (WordToNum_functional_19 _ _ _ Hwx Hwd) as ->.
  exact Hge.
Qed.

Lemma IsSorted_app_le_ge_19 :
  forall m a b,
    IsSorted a ->
    IsSorted b ->
    AllNumLe_19 m a ->
    AllNumGe_19 m b ->
    IsSorted (a ++ b).
Proof.
  intros m a b Hsa Hsb Hle Hge.
  apply IsSorted_app_19; auto.
  unfold AllNumLe_19, AllNumGe_19 in *.
  intros x y nx ny Hx Hy Hwx Hwy.
  specialize (Hle x nx Hx Hwx).
  specialize (Hge y ny Hy Hwy).
  lia.
Qed.

Lemma IsSorted_sorted_number_words_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    IsSorted (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).
Proof.
  intros.
  rewrite sorted_number_words_by_counts_eq_19.
  set (b0 := repeat (number_word_string 0) (Z.to_nat c0)).
  set (b1 := repeat (number_word_string 1) (Z.to_nat c1)).
  set (b2 := repeat (number_word_string 2) (Z.to_nat c2)).
  set (b3 := repeat (number_word_string 3) (Z.to_nat c3)).
  set (b4 := repeat (number_word_string 4) (Z.to_nat c4)).
  set (b5 := repeat (number_word_string 5) (Z.to_nat c5)).
  set (b6 := repeat (number_word_string 6) (Z.to_nat c6)).
  set (b7 := repeat (number_word_string 7) (Z.to_nat c7)).
  set (b8 := repeat (number_word_string 8) (Z.to_nat c8)).
  set (b9 := repeat (number_word_string 9) (Z.to_nat c9)).
  change (IsSorted (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  assert (Hs9 : IsSorted b9) by (subst b9; apply IsSorted_repeat_number_word_19; lia).
  assert (Hg9 : AllNumGe_19 9%nat b9) by (subst b9; apply AllNumGe_repeat_number_word_19; lia).
  assert (Hs89 : IsSorted (b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 8%nat).
    - subst b8; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs9.
    - subst b8; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 8%nat 9%nat); [lia|exact Hg9]. }
  assert (Hg89 : AllNumGe_19 8%nat (b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b8; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 8%nat 9%nat); [lia|exact Hg9]. }
  assert (Hs789 : IsSorted (b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 7%nat).
    - subst b7; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs89.
    - subst b7; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 7%nat 8%nat); [lia|exact Hg89]. }
  assert (Hg789 : AllNumGe_19 7%nat (b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b7; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 7%nat 8%nat); [lia|exact Hg89]. }
  assert (Hs6789 : IsSorted (b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 6%nat).
    - subst b6; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs789.
    - subst b6; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 6%nat 7%nat); [lia|exact Hg789]. }
  assert (Hg6789 : AllNumGe_19 6%nat (b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b6; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 6%nat 7%nat); [lia|exact Hg789]. }
  assert (Hs56789 : IsSorted (b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 5%nat).
    - subst b5; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs6789.
    - subst b5; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 5%nat 6%nat); [lia|exact Hg6789]. }
  assert (Hg56789 : AllNumGe_19 5%nat (b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b5; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 5%nat 6%nat); [lia|exact Hg6789]. }
  assert (Hs456789 : IsSorted (b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 4%nat).
    - subst b4; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs56789.
    - subst b4; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 4%nat 5%nat); [lia|exact Hg56789]. }
  assert (Hg456789 : AllNumGe_19 4%nat (b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b4; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 4%nat 5%nat); [lia|exact Hg56789]. }
  assert (Hs3456789 : IsSorted (b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 3%nat).
    - subst b3; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs456789.
    - subst b3; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 3%nat 4%nat); [lia|exact Hg456789]. }
  assert (Hg3456789 : AllNumGe_19 3%nat (b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b3; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 3%nat 4%nat); [lia|exact Hg456789]. }
  assert (Hs23456789 : IsSorted (b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 2%nat).
    - subst b2; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs3456789.
    - subst b2; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 2%nat 3%nat); [lia|exact Hg3456789]. }
  assert (Hg23456789 : AllNumGe_19 2%nat (b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b2; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 2%nat 3%nat); [lia|exact Hg3456789]. }
  assert (Hs123456789 : IsSorted (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { eapply IsSorted_app_le_ge_19 with (m := 1%nat).
    - subst b1; apply IsSorted_repeat_number_word_19; lia.
    - exact Hs23456789.
    - subst b1; apply AllNumLe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 1%nat 2%nat); [lia|exact Hg23456789]. }
  assert (Hg123456789 : AllNumGe_19 1%nat (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9)).
  { apply AllNumGe_app_19.
    - subst b1; apply AllNumGe_repeat_number_word_19; lia.
    - apply (AllNumGe_weaken_19 1%nat 2%nat); [lia|exact Hg23456789]. }
  eapply IsSorted_app_le_ge_19 with (m := 0%nat).
  - subst b0; apply IsSorted_repeat_number_word_19; lia.
  - exact Hs123456789.
  - subst b0; apply AllNumLe_repeat_number_word_19; lia.
  - apply (AllNumGe_weaken_19 0%nat 1%nat); [lia|exact Hg123456789].
Qed.

Lemma count_occ_string_app_19 :
  forall (l1 l2 : list string) x,
    count_occ string_dec (l1 ++ l2) x =
    (count_occ string_dec l1 x + count_occ string_dec l2 x)%nat.
Proof.
  intros l1.
  induction l1 as [| h t IH]; intros l2 x; cbn.
  - reflexivity.
  - destruct (string_dec h x); cbn; rewrite IH; lia.
Qed.

Lemma count_occ_map_number_word_19 :
  forall toks d,
    0 <= d < 10 ->
    Forall (fun tok => forall x, In x tok -> 0 <= x <= 127) toks ->
    count_occ string_dec (map string_of_list_z_19 toks) (number_word_string d) =
    count_occ list_Z_eq_dec_19 toks (number_word_z d).
Proof.
  induction toks as [| tok toks IH]; intros d Hd Hrange; cbn.
  - reflexivity.
  - inversion Hrange as [| ? ? Htok Htail]; subst.
    destruct (string_dec (string_of_list_z_19 tok) (number_word_string d)) as [Hs | Hs].
    + assert (Htok_eq : tok = number_word_z d).
      { unfold number_word_string in Hs.
        apply string_of_list_z_inj_range_19; auto.
        intros x Hin. apply number_word_z_range_19 with (d := d); auto. }
      destruct (list_Z_eq_dec_19 tok (number_word_z d)) as [_ | Hneq];
        [| contradiction].
      cbn. f_equal. apply IH; auto.
    + destruct (list_Z_eq_dec_19 tok (number_word_z d)) as [Htok_eq | _].
      * subst tok. contradiction Hs. reflexivity.
      * apply IH; auto.
Qed.

Lemma count_sorted_words_zero_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 0) = Z.to_nat c0.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 0) ?n) (number_word_string 0)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 0)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_one_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 1) = Z.to_nat c1.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 1) ?n) (number_word_string 1)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 1)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_two_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 2) = Z.to_nat c2.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 2) ?n) (number_word_string 2)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 2)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_three_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 3) = Z.to_nat c3.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 3) ?n) (number_word_string 3)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 3)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_four_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 4) = Z.to_nat c4.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 4) ?n) (number_word_string 4)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 4)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_five_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 5) = Z.to_nat c5.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 5) ?n) (number_word_string 5)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 5)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_six_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 6) = Z.to_nat c6.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 6) ?n) (number_word_string 6)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 6)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_seven_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 7) = Z.to_nat c7.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 7) ?n) (number_word_string 7)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 7)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_eight_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 8) = Z.to_nat c8.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 8) ?n) (number_word_string 8)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 8)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma count_sorted_words_nine_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    count_occ string_dec
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9)
      (number_word_string 9) = Z.to_nat c9.
Proof.
  intros. rewrite sorted_number_words_by_counts_eq_19.
  repeat rewrite count_occ_string_app_19.
  repeat match goal with
  | |- context[count_occ string_dec (repeat (number_word_string 9) ?n) (number_word_string 9)] =>
      rewrite count_occ_repeat_eq by reflexivity
  | |- context[count_occ string_dec (repeat (number_word_string ?d) ?n) (number_word_string 9)] =>
      rewrite count_occ_repeat_neq by (intro H; apply number_word_string_inj_19 in H; lia)
  end; lia.
Qed.

Lemma valid_word_cases_19 :
  forall x,
    is_valid_word x ->
    x = number_word_string 0 \/ x = number_word_string 1 \/
    x = number_word_string 2 \/ x = number_word_string 3 \/
    x = number_word_string 4 \/ x = number_word_string 5 \/
    x = number_word_string 6 \/ x = number_word_string 7 \/
    x = number_word_string 8 \/ x = number_word_string 9.
Proof.
  intros x [n H].
  destruct H; cbn.
  - left. reflexivity.
  - right; left. reflexivity.
  - right; right; left. reflexivity.
  - right; right; right; left. reflexivity.
  - right; right; right; right; left. reflexivity.
  - right; right; right; right; right; left. reflexivity.
  - right; right; right; right; right; right; left. reflexivity.
  - right; right; right; right; right; right; right; left. reflexivity.
  - right; right; right; right; right; right; right; right; left. reflexivity.
  - right; right; right; right; right; right; right; right; right. reflexivity.
Qed.

Lemma count_occ_invalid_word_zero_19 :
  forall words x,
    Forall is_valid_word words ->
    x <> number_word_string 0 ->
    x <> number_word_string 1 ->
    x <> number_word_string 2 ->
    x <> number_word_string 3 ->
    x <> number_word_string 4 ->
    x <> number_word_string 5 ->
    x <> number_word_string 6 ->
    x <> number_word_string 7 ->
    x <> number_word_string 8 ->
    x <> number_word_string 9 ->
    count_occ string_dec words x = 0%nat.
Proof.
  intros words x Hvalid H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
  apply count_occ_not_In.
  intros Hin.
  apply Forall_forall with (x := x) in Hvalid; auto.
  destruct (valid_word_cases_19 x Hvalid) as
    [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | [Hx | Hx]]]]]]]]];
    subst; contradiction.
Qed.

Lemma sorted_number_words_permutation_19 :
  forall l input_words,
    ascii_range_z l ->
    map string_of_list_z_19 (SplitOnSpacesZ_19 l) = input_words ->
    Forall is_valid_word input_words ->
    Permutation input_words
      (sorted_number_words_by_counts_19
        (count_word_in_string 0 l)
        (count_word_in_string 1 l)
        (count_word_in_string 2 l)
        (count_word_in_string 3 l)
        (count_word_in_string 4 l)
        (count_word_in_string 5 l)
        (count_word_in_string 6 l)
        (count_word_in_string 7 l)
        (count_word_in_string 8 l)
        (count_word_in_string 9 l)).
Proof.
  intros l input_words Hrange Hmap Hvalid.
  apply (proj2 (Permutation_count_occ string_dec _ _)).
  intro x.
  pose proof (SplitOnSpacesZ_tokens_range_19 l Hrange) as Htokrange.
  assert (Hcount : forall d,
    0 <= d < 10 ->
    count_occ string_dec input_words (number_word_string d) =
      Z.to_nat (count_word_in_string d l)).
  {
    intros d Hd.
    rewrite <- Hmap.
    unfold count_word_in_string.
    rewrite count_occ_map_number_word_19 by assumption.
    rewrite Nat2Z.id. reflexivity.
  }
  destruct (string_dec x (number_word_string 0)) as [-> | Hx0].
  - rewrite Hcount by lia. rewrite count_sorted_words_zero_19. reflexivity.
  - destruct (string_dec x (number_word_string 1)) as [-> | Hx1].
    + rewrite Hcount by lia. rewrite count_sorted_words_one_19. reflexivity.
    + destruct (string_dec x (number_word_string 2)) as [-> | Hx2].
      * rewrite Hcount by lia. rewrite count_sorted_words_two_19. reflexivity.
      * destruct (string_dec x (number_word_string 3)) as [-> | Hx3].
        -- rewrite Hcount by lia. rewrite count_sorted_words_three_19. reflexivity.
        -- destruct (string_dec x (number_word_string 4)) as [-> | Hx4].
           ++ rewrite Hcount by lia. rewrite count_sorted_words_four_19. reflexivity.
           ++ destruct (string_dec x (number_word_string 5)) as [-> | Hx5].
              ** rewrite Hcount by lia. rewrite count_sorted_words_five_19. reflexivity.
              ** destruct (string_dec x (number_word_string 6)) as [-> | Hx6].
                 --- rewrite Hcount by lia. rewrite count_sorted_words_six_19. reflexivity.
                 --- destruct (string_dec x (number_word_string 7)) as [-> | Hx7].
                     +++ rewrite Hcount by lia. rewrite count_sorted_words_seven_19. reflexivity.
                     +++ destruct (string_dec x (number_word_string 8)) as [-> | Hx8].
                         *** rewrite Hcount by lia. rewrite count_sorted_words_eight_19. reflexivity.
                         *** destruct (string_dec x (number_word_string 9)) as [-> | Hx9].
                             ---- rewrite Hcount by lia. rewrite count_sorted_words_nine_19. reflexivity.
                             ---- rewrite (count_occ_invalid_word_zero_19 input_words x Hvalid
                                      Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9).
                                  rewrite (count_occ_invalid_word_zero_19
                                    (sorted_number_words_by_counts_19
                                      (count_word_in_string 0 l)
                                      (count_word_in_string 1 l)
                                      (count_word_in_string 2 l)
                                      (count_word_in_string 3 l)
                                      (count_word_in_string 4 l)
                                      (count_word_in_string 5 l)
                                      (count_word_in_string 6 l)
                                      (count_word_in_string 7 l)
                                      (count_word_in_string 8 l)
                                      (count_word_in_string 9 l)) x
                                    (sorted_number_words_valid_19 _ _ _ _ _ _ _ _ _ _)
                                    Hx0 Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9).
                                  reflexivity.
Qed.

Lemma string_of_list_ascii_map_z_19 :
  forall l,
    string_of_list_ascii (map ascii_of_z_19 l) = string_of_list_z_19 l.
Proof.
  induction l; simpl; [reflexivity | rewrite IHl; reflexivity].
Qed.

Lemma string_of_list_ascii_app_19 :
  forall a b,
    string_of_list_ascii (a ++ b) =
      (string_of_list_ascii a ++ string_of_list_ascii b)%string.
Proof.
  induction a; intros b; simpl; [reflexivity | rewrite IHa; reflexivity].
Qed.

Lemma string_of_list_z_app_19 :
  forall a b,
    string_of_list_z_19 (a ++ b) =
      (string_of_list_z_19 a ++ string_of_list_z_19 b)%string.
Proof.
  induction a; intros b; simpl; [reflexivity | rewrite IHa; reflexivity].
Qed.

Lemma string_of_list_ascii_rev_map_z_19 :
  forall l,
    string_of_list_ascii (rev (map ascii_of_z_19 l)) =
    string_of_list_z_19 (rev l).
Proof.
  intros l.
  rewrite <- map_rev.
  apply string_of_list_ascii_map_z_19.
Qed.

Lemma ascii_of_z_space_iff_19 :
  forall z,
    0 <= z <= 127 ->
    ascii_of_z_19 z = " "%char <-> z = 32.
Proof.
  intros z Hz.
  split; intro H.
  - unfold ascii_of_z_19 in H.
    apply f_equal with (f := nat_of_ascii) in H.
    rewrite nat_ascii_embedding in H by lia.
    cbn in H. lia.
  - subst. reflexivity.
Qed.

Lemma SplitOnSpaces_string_z_aux_19 :
  forall input current,
    (forall x, In x current \/ In x input -> 0 <= x <= 127) ->
    SplitOnSpaces_aux_19 (map ascii_of_z_19 current)
      (string_of_list_z_19 input) =
    map string_of_list_z_19 (SplitOnSpacesZ_aux_19 current input).
Proof.
  induction input as [| h t IH]; intros current Hrange; cbn.
  - destruct current as [| c current]; cbn; [reflexivity |].
    repeat rewrite string_of_list_ascii_app_19.
    repeat rewrite string_of_list_z_app_19.
    rewrite string_of_list_ascii_rev_map_z_19.
    reflexivity.
  - destruct (ascii_dec (ascii_of_z_19 h) " "%char) as [Hspace | Hnotspace].
    + assert (Hh : h = 32).
      { apply ascii_of_z_space_iff_19; auto.
        apply Hrange. right. left. reflexivity. }
      subst h. rewrite Z.eqb_refl.
      destruct current as [| c current]; cbn.
      * change (@nil ascii) with (map ascii_of_z_19 (@nil Z)).
        apply IH. intros x [Hin | Hin]; [contradiction|].
        apply Hrange. right. right. exact Hin.
      * repeat rewrite string_of_list_ascii_app_19.
        repeat rewrite string_of_list_z_app_19.
        rewrite string_of_list_ascii_rev_map_z_19.
        f_equal.
        change (@nil ascii) with (map ascii_of_z_19 (@nil Z)).
        apply IH. intros x [Hin | Hin]; [contradiction|].
        apply Hrange. right. right. exact Hin.
    + assert (Hh : h <> 32).
      { intros H; subst h. contradiction Hnotspace. reflexivity. }
      destruct (Z.eqb_spec h 32) as [Heq | Hneq]; [contradiction |].
      change (SplitOnSpaces_aux_19 (map ascii_of_z_19 (h :: current))
        (string_of_list_z_19 t) =
        map string_of_list_z_19 (SplitOnSpacesZ_aux_19 (h :: current) t)).
      rewrite IH.
      * reflexivity.
      * intros x [Hin | Hin].
        -- destruct Hin as [Hx | Hin].
           ++ subst x. apply Hrange. right. left. reflexivity.
           ++ apply Hrange. left. exact Hin.
        -- apply Hrange. right. right. exact Hin.
Qed.

Lemma SplitOnSpaces_string_z_19 :
  forall l,
    ascii_range_z l ->
    SplitOnSpaces_19 (string_of_list_z_19 l) =
    map string_of_list_z_19 (SplitOnSpacesZ_19 l).
Proof.
  intros l Hrange.
  unfold SplitOnSpaces_19, SplitOnSpacesZ_19.
  change (@nil ascii) with (map ascii_of_z_19 (@nil Z)).
  apply SplitOnSpaces_string_z_aux_19.
  intros x [Hin | Hin].
  - contradiction.
  - eapply ascii_range_z_In_19; eauto.
Qed.

Lemma valid_word_split_space_19 :
  forall w rest,
    is_valid_word w ->
    SplitOnSpaces_aux_19 [] ((w ++ " " ++ rest)%string) =
    w :: SplitOnSpaces_aux_19 [] rest.
Proof.
  intros w rest [n Hwn].
  inversion Hwn; subst; cbn; reflexivity.
Qed.

Lemma valid_word_split_single_19 :
  forall w,
    is_valid_word w ->
    SplitOnSpaces_19 w = [w].
Proof.
  intros w [n Hwn].
  inversion Hwn; subst; cbn; reflexivity.
Qed.

Lemma SplitOnSpaces_concat_valid_19 :
  forall words,
    Forall is_valid_word words ->
    SplitOnSpaces_19 (String.concat " " words) = words.
Proof.
  induction words as [| w words IH]; intros Hvalid; cbn.
  - reflexivity.
  - inversion Hvalid as [| ? ? Hw Htail]; subst.
    destruct words as [| w2 words].
    + apply valid_word_split_single_19. exact Hw.
    + cbn.
      change (String " " match words with
                         | [] => w2
                         | _ :: _ => w2 ++ String " " (String.concat " " words)
                         end)
        with (" " ++ String.concat " " (w2 :: words))%string.
      rewrite valid_word_split_space_19 by exact Hw.
      f_equal.
      change (SplitOnSpaces_19 (String.concat " " (w2 :: words)) =
        w2 :: words).
      apply IH. exact Htail.
Qed.

Lemma problem_19_pre_split_words_19 :
  forall l input_words,
    problem_19_pre_z l ->
    ascii_range_z l ->
    SpaceDelimited (string_of_list_z_19 l) input_words ->
    Forall is_valid_word input_words ->
    map string_of_list_z_19 (SplitOnSpacesZ_19 l) = input_words.
Proof.
  intros l input_words Hpre Hrange Hspace Hvalid.
  unfold SpaceDelimited in Hspace.
  pose proof (SplitOnSpaces_string_z_19 l Hrange) as Hsplit.
  rewrite <- Hspace in Hsplit.
  rewrite SplitOnSpaces_concat_valid_19 in Hsplit by exact Hvalid.
  symmetry. exact Hsplit.
Qed.

Lemma output_prefix_10_sorted_numbers_output_z_19 :
  forall l,
    output_prefix_by_input_z 10 0 l = sorted_numbers_output_z l.
Proof.
  intros l.
  unfold output_prefix_by_input_z, sorted_numbers_output_z, output_prefix_z.
  reflexivity.
Qed.

Lemma string_app_assoc_19 :
  forall a b c,
    ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a; intros b c; simpl; [reflexivity | rewrite IHa; reflexivity].
Qed.

Lemma string_concat_snoc_nonempty_19 :
  forall words w,
    words <> [] ->
    String.concat " " (words ++ [w]) =
      (String.concat " " words ++ " " ++ w)%string.
Proof.
  destruct words as [| a words]; intros w Hne;
    [contradiction Hne; reflexivity |].
  revert a w Hne.
  induction words as [| b words IH]; intros a w Hne.
  - reflexivity.
  - change (String.concat " " ((a :: b :: words) ++ [w]))
      with ((a ++ " " ++ String.concat " " ((b :: words) ++ [w]))%string).
    change (String.concat " " (a :: b :: words))
      with ((a ++ " " ++ String.concat " " (b :: words))%string).
    rewrite IH by discriminate.
    repeat rewrite string_app_assoc_19.
    reflexivity.
Qed.

Lemma append_number_word_concat_19 :
  forall words prefix d,
    0 <= d < 10 ->
    String.concat " " words = string_of_list_z_19 prefix ->
    (words = [] <-> prefix = []) ->
    String.concat " " (append_number_word_string_19 words d) =
    string_of_list_z_19 (append_number_word_z prefix d).
Proof.
  intros words prefix d Hd Hconcat Hemp.
  unfold append_number_word_string_19, append_number_word_z.
  destruct words as [| w words].
  - simpl in Hconcat.
    destruct Hemp as [Hemp _].
    specialize (Hemp eq_refl). subst prefix.
    cbn. reflexivity.
  - assert (Hprefix_nonempty : prefix <> []).
    { intros Hnil. destruct Hemp as [_ Hemp]. specialize (Hemp Hnil).
      discriminate. }
    assert (Hlen_ne : Zlength prefix <> 0).
    { intros Hz. apply Zlength_nil_inv in Hz. contradiction. }
    destruct (Z.eqb_spec (Zlength prefix) 0) as [Hz | Hz];
      [contradiction |].
    rewrite string_concat_snoc_nonempty_19 by discriminate.
    rewrite Hconcat.
    repeat rewrite string_of_list_z_app_19.
    cbn. reflexivity.
Qed.

Lemma append_repeated_number_word_strings_concat_19 :
  forall n words prefix d,
    0 <= d < 10 ->
    String.concat " " words = string_of_list_z_19 prefix ->
    (words = [] <-> prefix = []) ->
    String.concat " "
      (append_repeated_number_word_strings_nat_19 words d n) =
      string_of_list_z_19 (append_repeated_number_word_nat prefix d n) /\
    (append_repeated_number_word_strings_nat_19 words d n = [] <->
      append_repeated_number_word_nat prefix d n = []).
Proof.
  induction n as [| n IH]; intros words prefix d Hd Hconcat Hemp; simpl.
  - split; assumption.
  - destruct (IH words prefix d Hd Hconcat Hemp) as [Hconcat' Hemp'].
    split.
    + apply append_number_word_concat_19; auto.
    + unfold append_number_word_string_19, append_number_word_z.
      split; intro Hnil.
      * apply app_eq_nil in Hnil. destruct Hnil as [_ Hbad].
        discriminate.
      * destruct (Z.eqb
            (Zlength (append_repeated_number_word_nat prefix d n)) 0);
          apply app_eq_nil in Hnil; destruct Hnil as [_ Hbad];
          destruct_digit_cases_19 d; cbn in Hbad; discriminate.
Qed.

Lemma sorted_number_words_by_counts_concat_19 :
  forall c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    String.concat " "
      (sorted_number_words_by_counts_19 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9) =
    string_of_list_z_19
      (sorted_numbers_output_by_counts_z c0 c1 c2 c3 c4 c5 c6 c7 c8 c9).
Proof.
  intros.
  unfold sorted_number_words_by_counts_19, sorted_numbers_output_by_counts_z,
    append_repeated_number_word_strings_z_19, append_repeated_number_word_z.
  assert (Hempty : ((@nil string) = [] <-> (@nil Z) = [])).
  { split; intro; reflexivity. }
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c0) [] [] 0 ltac:(lia) eq_refl
    Hempty) as [H0 E0].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c1)
    (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0))
    (append_repeated_number_word_nat [] 0 (Z.to_nat c0))
    1 ltac:(lia) H0 E0) as [H1 E1].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c2)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1))
    2 ltac:(lia) H1 E1) as [H2 E2].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c3)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2))
    3 ltac:(lia) H2 E2) as [H3 E3].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c4)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3))
    4 ltac:(lia) H3 E3) as [H4 E4].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c5)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4))
    5 ltac:(lia) H4 E4) as [H5 E5].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c6)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5))
    6 ltac:(lia) H5 E5) as [H6 E6].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c7)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6))
    7 ltac:(lia) H6 E6) as [H7 E7].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c8)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6)) 7 (Z.to_nat c7))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6)) 7 (Z.to_nat c7))
    8 ltac:(lia) H7 E7) as [H8 E8].
  pose proof (append_repeated_number_word_strings_concat_19
    (Z.to_nat c9)
    (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19
      (append_repeated_number_word_strings_nat_19 [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6)) 7 (Z.to_nat c7)) 8 (Z.to_nat c8))
    (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat
      (append_repeated_number_word_nat [] 0 (Z.to_nat c0)) 1 (Z.to_nat c1)) 2 (Z.to_nat c2)) 3 (Z.to_nat c3)) 4 (Z.to_nat c4)) 5 (Z.to_nat c5)) 6 (Z.to_nat c6)) 7 (Z.to_nat c7)) 8 (Z.to_nat c8))
    9 ltac:(lia) H8 E8) as [H9 _].
  exact H9.
Qed.

Lemma problem_19_spec_sorted_output_bridge_19 :
  forall l,
    problem_19_pre_z l ->
    ascii_range_z l ->
    problem_19_spec_z l (output_prefix_by_input_z 10 0 l).
Proof.
  intros l Hpre Hrange.
  unfold problem_19_pre_z in Hpre.
  unfold problem_19_spec_z, problem_19_spec.
  destruct Hpre as [input_words [Hspace Hvalid]].
  exists input_words.
  exists (sorted_number_words_by_counts_19
    (count_word_in_string 0 l)
    (count_word_in_string 1 l)
    (count_word_in_string 2 l)
    (count_word_in_string 3 l)
    (count_word_in_string 4 l)
    (count_word_in_string 5 l)
    (count_word_in_string 6 l)
    (count_word_in_string 7 l)
    (count_word_in_string 8 l)
    (count_word_in_string 9 l)).
  repeat split.
  - exact Hspace.
  - unfold SpaceDelimited.
    rewrite output_prefix_10_sorted_numbers_output_z_19.
    unfold sorted_numbers_output_z.
    apply sorted_number_words_by_counts_concat_19.
  - exact Hvalid.
  - apply sorted_number_words_valid_19.
  - apply sorted_number_words_permutation_19; auto.
    apply problem_19_pre_split_words_19 with (input_words := input_words); auto.
    unfold problem_19_pre_z. exists input_words. split; auto.
  - apply IsSorted_sorted_number_words_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_24_split_goal_1 : sort_numbers_entail_wit_24_split_goal_1.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_24_split_goal_spatial : sort_numbers_entail_wit_24_split_goal_spatial.
Proof. Abort.

Lemma proof_of_sort_numbers_entail_wit_24 : sort_numbers_entail_wit_24.
Proof.
  right.
  pre_process; subst.
  assert (Hi10 : i = 10) by lia.
  subst i.
  pose proof (output_final_length_used_capacity_19 l) as Hfinal.
  assert (Hout_final :
    Zlength (output_prefix_by_input_z 10 0 l) + 1 =
      output_used_capacity_prefix_by_input_z 10 l).
  {
    exact Hfinal.
  }
  rewrite <- Hout_final.
  rewrite (CharArray.undef_seg_empty out
    (Zlength (output_prefix_by_input_z 10 0 l) + 1)).
  entailer!;
    try exact Hout_final;
    try lia.
Qed. 

Lemma proof_of_sort_numbers_return_wit_1 : sort_numbers_return_wit_1.
Proof.
  right.
  pre_process; subst.
  Exists (output_prefix_by_input_z 10 0 l).
  entailer!.
  apply problem_19_spec_sorted_output_bridge_19; auto.
Qed. 
