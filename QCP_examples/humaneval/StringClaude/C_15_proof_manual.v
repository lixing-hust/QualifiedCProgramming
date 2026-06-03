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
From SimpleC.EE Require Import C_15_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_44.
Require Import coins_15.
Local Open Scope sac.

Ltac normalize_15 :=
  subst;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Zlength_repeat_Z in * by lia;
  try rewrite sequence_prefix_z_1 in *;
  try rewrite sequence_prefix_z_step in * by lia;
  try rewrite app_nil_r in *;
  simpl in *.

Ltac solve_15 :=
  pre_process;
  normalize_15;
  try match goal with
  | |- context[base_count_state_z ?i 10 ?i 0] =>
      apply base_count_state_init; lia
  | H : base_count_state_z ?i 10 ?t ?digits |- context[base_count_state_z ?i 10 (?t ÷ 10) (?digits + 1)] =>
      apply base_count_state_step; try lia; exact H
  | H : base_count_state_z ?i 10 0 ?digits |- ?digits = Zlength (base_digits_z ?i 10) =>
      apply base_count_state_done; try lia; exact H
  | |- context[base_fill_full_state_z ?i 10 ?i (Zlength (base_digits_z ?i 10)) (repeat_Z 0 (Zlength (base_digits_z ?i 10)))] =>
      apply base_fill_full_state_init; lia
  | H : base_fill_full_state_z ?i 10 ?t (?fill + 1) ?digit_l
      |- context[base_fill_full_state_z ?i 10 (?t ÷ 10) ?fill (replace_Znth ?fill (48 + ?t % 10) ?digit_l)] =>
      replace (48 + t % 10) with (signed_last_nbits (48 + t % 10) 8)
        by (rewrite signed_last_nbits_eq by (pose proof (Z.mod_pos_bound t 10 ltac:(lia)); lia); reflexivity);
      apply base_fill_full_state_step; try lia; exact H
  | H : base_fill_full_state_z ?i 10 0 0 ?digit_l |- ?digit_l = base_digits_z ?i 10 =>
      apply base_fill_full_state_done; exact H
  end;
  normalize_15;
  try entailer!;
  try eauto using base_count_state_init, base_count_state_step,
    base_count_state_done, base_fill_full_state_init,
    base_fill_full_state_step, base_fill_full_state_done;
  try lia.

Lemma proof_of_string_sequence_safety_wit_19 : string_sequence_safety_wit_19.
Proof.
  pre_process.
  match goal with
  | Hcount : base_count_state_z i 10 t digits |- _ =>
      pose proof (base_count_state_digits_le_orig_15 i t digits ltac:(lia) Hcount)
  end.
  entailer!.
Qed. 

Lemma proof_of_string_sequence_safety_wit_40 : string_sequence_safety_wit_40.
Proof.
  pre_process.
  pose proof (base_digits_z_len_le_orig_15 i ltac:(lia)).
  assert (0 <= k + digits) by
    (match goal with
     | Hk : k + digits = Zlength ?l |- _ => rewrite Hk; apply Zlength_nonneg
     end).
  entailer!; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_1 : string_sequence_entail_wit_1.
Proof.
  pre_process.
  Exists (cons 48 nil).
  normalize_15.
  entailer!.
  - unfold CharArray.full, store_array.
    simpl.
    entailer!.
  - change (2 <= 12 * (n_pre + 1) + 1).
    lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_2 : string_sequence_entail_wit_2.
Proof.
  pre_process.
  Exists out_l_2.
  entailer!.
  apply base_count_state_init; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_3 : string_sequence_entail_wit_3.
Proof.
  pre_process.
  replace (t ÷ 10) with (t / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  Exists out_l_2.
  entailer!.
  - apply base_count_state_step; try lia; assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_4 : string_sequence_entail_wit_4.
Proof.
  pre_process.
  assert (t = 0) by lia; subst t.
  Exists out_l_2.
  entailer!.
  - eapply sequence_prefix_step_length_bound_15; eauto; try lia.
    apply base_count_state_done; try lia; assumption.
  - apply base_count_state_done; try lia; assumption.
Qed. 

Lemma proof_of_string_sequence_entail_wit_5 : string_sequence_entail_wit_5.
Proof.
  pre_process.
  Exists out_l.
  normalize_15.
  entailer!.
  replace (Zlength (sequence_prefix_z i) + 1 + 0)
    with (Zlength (sequence_prefix_z i) + 1) by lia.
  entailer!.
Qed. 

Lemma proof_of_string_sequence_entail_wit_6 : string_sequence_entail_wit_6.
Proof.
  pre_process.
  Exists prefix_l_2.
  replace (k + (j + 1)) with (k + j + 1) by lia.
  normalize_15.
  rewrite repeat_Z_tail by lia.
  entailer!.
  repeat rewrite app_assoc.
  entailer!.
Qed. 

Lemma proof_of_string_sequence_entail_wit_7 : string_sequence_entail_wit_7.
Proof.
  pre_process.
  assert (j = digits) by lia; subst j.
  Exists (repeat_Z 0 digits) prefix_l_2.
  normalize_15.
  entailer!.
  apply base_fill_full_state_init; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_8 : string_sequence_entail_wit_8.
Proof.
  pre_process.
  Exists digit_l_2 prefix_l_2.
  entailer!.
  replace (k + digits) with (Zlength prefix_l_2 + 1 + digits) by lia.
  eapply sequence_prefix_step_length_bound_15 with
    (out_l := prefix_l_2) (k := Zlength prefix_l_2); eauto; lia.
  pose proof (Zlength_nonneg prefix_l_2).
  lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_9 : string_sequence_entail_wit_9.
Proof.
  pre_process.
  Exists digit_l_2 prefix_l_2.
  entailer!.
  - replace (fill - 1 + 1) with fill by lia.
    match goal with
    | Hfill : base_fill_full_state_z i 10 t fill digit_l_2 |- _ => exact Hfill
    end.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)); lia.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)); lia.
  - match goal with
    | Hfill : base_fill_full_state_z i 10 t fill digit_l_2 |- _ =>
        pose proof (base_fill_full_state_positive_digits i 10 t fill digit_l_2 ltac:(lia) ltac:(lia) Hfill)
    end; lia.
  - match goal with
    | Hfill : base_fill_full_state_z i 10 t fill digit_l_2 |- _ =>
        pose proof (base_fill_full_state_positive_digits i 10 t fill digit_l_2 ltac:(lia) ltac:(lia) Hfill)
    end; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_10 : string_sequence_entail_wit_10.
Proof.
  pre_process.
  replace (t ÷ 10) with (t / 10)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (replace_Znth (k + fill) (48 + t % 10)
    (((prefix_l_2 ++ 32 :: nil) ++ digit_l_2)%list))
    with (((prefix_l_2 ++ 32 :: nil) ++
      replace_Znth fill (48 + t % 10) digit_l_2)%list).
  2:{
    rewrite replace_Znth_app_r.
    - rewrite (replace_Znth_nothing (k + fill)
        ((prefix_l_2 ++ 32 :: nil)%list) (48 + t % 10)).
      + replace (k + fill - Zlength (prefix_l_2 ++ 32 :: nil)%list) with fill.
        * reflexivity.
        * rewrite H9. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
      + rewrite H9. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
    - rewrite H9. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  }
  Exists (replace_Znth fill (48 + t % 10) digit_l_2) prefix_l_2.
  entailer!.
  - replace (48 + t % 10) with (signed_last_nbits (48 + t % 10) 8).
    + apply base_fill_full_state_step_rem_15; try lia; assumption.
    + rewrite signed_last_nbits_eq by lia.
      reflexivity.
  - rewrite Zlength_replace_Znth_44; lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_11 : string_sequence_entail_wit_11.
Proof.
  pre_process.
  assert (t = 0) by lia; subst t.
  assert (fill = 0).
  { match goal with
    | Hfull : base_fill_full_state_z i 10 0 fill digit_l |- _ =>
        destruct Hfull as [suffix [[_ [_ [Hfill _]]] _]]
    end.
    unfold base_digits_pos_z in Hfill.
    replace (Z.leb 0 0) with true in Hfill by (symmetry; apply Z.leb_le; lia).
    change (Zlength (@nil Z)) with 0 in Hfill.
    lia. }
  subst fill.
  match goal with
  | Hfull : base_fill_full_state_z i 10 0 0 digit_l |- _ =>
      pose proof (base_fill_full_state_done i 10 digit_l Hfull) as Hdone
  end.
  subst digit_l.
  Exists (sequence_prefix_z (i + 1)).
  rewrite sequence_prefix_z_step by lia.
  normalize_15.
  entailer!.
  repeat rewrite <- app_assoc.
  entailer!.
  change (Zlength (sequence_prefix_z i) + 1 + Zlength (base_digits_z i 10) =
          Zlength (sequence_prefix_z i) + (1 + Zlength (base_digits_z i 10))).
  lia.
Qed. 

Lemma proof_of_string_sequence_entail_wit_12 : string_sequence_entail_wit_12.
Proof.
  pre_process.
  Exists out_l_2.
  entailer!.
  - subst j.
    match goal with
    | Hdigits : digits = Zlength (base_digits_z i 10) |- _ =>
        rewrite Hdigits; apply Zlength_nonneg
    end.
  - match goal with
    | Hdigits : digits = Zlength (base_digits_z i 10) |- _ =>
        rewrite Hdigits; apply Zlength_nonneg
    end.
Qed. 

Lemma proof_of_string_sequence_entail_wit_13 : string_sequence_entail_wit_13.
Proof.
  pre_process.
  assert (i = n_pre + 1) by lia; subst i.
  Exists out_l_2.
  unfold sequence_output_z.
  entailer!.
  replace out_l_2 with (sequence_output_z n_pre)
    by (unfold sequence_output_z; symmetry; exact H10).
  apply problem_15_spec_z_sequence_output; lia.
Qed. 

Lemma proof_of_string_sequence_return_wit_1 : string_sequence_return_wit_1.
Proof.
  pre_process.
  Exists out_l_2 len_2 cap_2.
  entailer!.
Qed. 
