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
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_84_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_84.
Require Import coins_103.
Require Import coins_44.
Local Open Scope sac.

Lemma proof_of_solve_safety_wit_16 : solve_safety_wit_16.
Proof.
  unfold solve_safety_wit_16.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos x 10 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_solve_safety_wit_36 : solve_safety_wit_36.
Proof.
  unfold solve_safety_wit_36.
  intros.
  pre_process.
  assert (total <= num) by
    (subst total; apply binary_digits_z_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_solve_safety_wit_40 : solve_safety_wit_40.
Proof.
  unfold solve_safety_wit_40.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  unfold solve_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  apply decimal_sum_state_init; lia.
Qed. 

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  unfold solve_entail_wit_2.
  intros.
  pre_process.
  replace (x ÷ 10) with (x / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem x 10) with (x mod 10)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  entailer!.
  - apply decimal_sum_state_step; lia || assumption.
  - apply decimal_sum_state_sum_bound with (orig := N_pre) (x := x / 10); try lia.
    apply decimal_sum_state_step; lia || assumption.
  - pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia.
  - assert (x / 10 <= x).
    { apply Z.div_le_upper_bound; lia. }
    lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  unfold solve_entail_wit_3.
  intros.
  pre_process.
  assert (x = 0) by lia; subst x.
  entailer!.
  apply decimal_sum_state_done; assumption.
Qed. 

Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  unfold solve_entail_wit_4.
  intros.
  pre_process.
  subst bits.
  entailer!.
  apply binary_count_state_init; lia.
Qed. 

Lemma proof_of_solve_entail_wit_5 : solve_entail_wit_5.
Proof.
  unfold solve_entail_wit_5.
  intros.
  pre_process.
  replace (t ÷ 2) with (t / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; lia || assumption.
  - apply binary_count_state_step_safe with (orig := num) (t := t); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  unfold solve_entail_wit_6.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - unfold CharArray.undef_full, CharArray.undef_seg.
    unfold store_undef_array.
    replace (bits + 1 - 0) with (bits + 1) by lia.
    entailer!.
  - apply binary_count_state_done; lia || assumption.
Qed. 

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  unfold solve_entail_wit_7.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  unfold solve_entail_wit_8.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  entailer!.
  - rewrite naive_C_Rules.repeat_Z_tail
      by (pose proof (Zlength_nonneg (binary_digits_z num)); lia).
    unfold naive_C_Rules.repeat_Z, repeat_Z.
    entailer!.
  - subst bits. subst total. apply binary_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits_z num)); lia).
    lia.
Qed. 

Lemma proof_of_solve_entail_wit_9 : solve_entail_wit_9.
Proof.
  unfold solve_entail_wit_9.
  intros.
  pre_process.
  subst sum.
  subst orig.
  Exists out_l_2.
  entailer!.
  all: try assumption;
    pose proof (Zlength_nonneg (binary_digits_z num)); lia.
Qed. 

Lemma proof_of_solve_entail_wit_10 : solve_entail_wit_10.
Proof.
  unfold solve_entail_wit_10.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  - replace (bits - 1 + 1) with bits by lia.
    assumption.
  - pose proof (base_fill_full_state_positive_digits orig 2 num bits out_l_2
      ltac:(lia) ltac:(lia) H14).
    lia.
Qed. 

Lemma proof_of_solve_entail_wit_11 : solve_entail_wit_11.
Proof.
  unfold solve_entail_wit_11.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth bits (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply binary_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_solve_return_wit_1 : solve_return_wit_1.
Proof.
  unfold solve_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  unfold binary_fill_full_state_z in H14.
  destruct H14 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos_z in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst bits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (binary_digits_z orig) (Zlength (binary_digits_z orig)).
  replace (Zlength (binary_digits_z orig) + 1) with (total + 1) by lia.
  entailer!.
  - apply problem_84_spec_z_intro with (sum := orig); try lia.
    + match goal with
      | Hval: decimal_sum_value_z N_pre ?s,
        Hs: ?s = orig |- _ => rewrite <- Hs; exact Hval
      end.
    + reflexivity.
  - pose proof (binary_digits_z_length_pos_le orig ltac:(lia)).
    lia.
  - pose proof (binary_digits_z_nonempty orig) as Hnonempty.
    destruct (binary_digits_z orig) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed. 

Lemma proof_of_solve_return_wit_2 : solve_return_wit_2.
Proof.
  unfold solve_return_wit_2.
  intros.
  pre_process.
  subst sum.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
  - apply problem_84_spec_z_intro with (sum := 0); try lia.
    + assumption.
    + unfold binary_digits_z. rewrite base_digits_z_zero by lia. reflexivity.
Qed. 

Lemma proof_of_solve_return_wit_3 : solve_return_wit_3.
Proof.
  unfold solve_return_wit_3.
  intros.
  pre_process.
  subst N_pre.
  Exists ((48 :: nil) : list Z) 1.
  rewrite (CharArray.undef_seg_empty retval 2).
  entailer!.
  - change (List.app (48 :: nil) (0 :: nil)) with (48 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (1 + 1) (0 :: nil) 48).
    rewrite (CharArray.seg_unfold retval 1 (1 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 2 2).
    entailer!.
Qed. 
