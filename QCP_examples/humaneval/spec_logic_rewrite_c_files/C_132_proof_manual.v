Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_132_goal.
From SimpleC.EE Require Import C_132_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_132.
Local Open Scope sac.

Lemma proof_of_is_nested_entail_wit_1 : is_nested_entail_wit_1.
Proof.
  left; intros.
  pose proof (nested_scan_initial_132 input).
  unfold string_length in *.
  pose proof (Zlength_nonneg input).
  pre_process; entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_2_1 : is_nested_entail_wit_2_1.
Proof.
  unfold is_nested_entail_wit_2_1; intros.
  assert (Hi : 0 <= i < Zlength input) by
    (unfold string_length in *; lia).
  pose proof (bracket_codes_Znth_132 input i PreH16 Hi) as Hcode.
  rewrite c_string_Znth_inside in PreH3, PreH4 by exact Hi.
  destruct Hcode; congruence.
Qed.

Lemma proof_of_is_nested_entail_wit_2_2 : is_nested_entail_wit_2_2.
Proof.
  unfold is_nested_entail_wit_2_2; intros.
  assert (Hi : 0 <= i < Zlength input) by
    (unfold string_length in *; lia).
  assert (Hchar : Znth i input 0 = 91).
  { rewrite <- c_string_Znth_inside by exact Hi. exact PreH4. }
  pose proof (nested_scan_step_132 input i count maxcount 91
    (count + 1) maxcount PreH18 ltac:(lia) (eq_sym Hchar)
    (or_introl eq_refl) ltac:(vm_compute; lia)
    ltac:(rewrite Z.max_l; lia)) as Hstep.
  unfold string_length in *.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_2_3 : is_nested_entail_wit_2_3.
Proof.
  unfold is_nested_entail_wit_2_3; intros.
  assert (Hi : 0 <= i < Zlength input) by
    (unfold string_length in *; lia).
  assert (Hchar : Znth i input 0 = 93).
  { rewrite <- c_string_Znth_inside by exact Hi. exact PreH3. }
  pose proof (nested_scan_step_132 input i count maxcount 93
    (count - 1) maxcount PreH18 ltac:(lia) (eq_sym Hchar)
    (or_intror eq_refl)
    ltac:(change (count - 1 = Z.max 0 (count - 1));
          rewrite Z.max_r by lia; reflexivity)
    ltac:(rewrite Z.max_l; lia)) as Hstep.
  unfold string_length in *.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_2_4 : is_nested_entail_wit_2_4.
Proof.
  unfold is_nested_entail_wit_2_4; intros.
  assert (Hi : 0 <= i < Zlength input) by
    (unfold string_length in *; lia).
  assert (Hchar : Znth i input 0 = 93).
  { rewrite <- c_string_Znth_inside by exact Hi. exact PreH3. }
  pose proof (nested_scan_step_132 input i count maxcount 93
    0 maxcount PreH18 ltac:(lia) (eq_sym Hchar)
    (or_intror eq_refl)
    ltac:(change (0 = Z.max 0 (count - 1));
          rewrite Z.max_l by lia; reflexivity)
    ltac:(rewrite Z.max_l; lia)) as Hstep.
  unfold string_length in *.
  rewrite <- derivable1_orp_intros1.
  entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_2_5 : is_nested_entail_wit_2_5.
Proof.
  unfold is_nested_entail_wit_2_5; intros.
  assert (Hi : 0 <= i < Zlength input) by
    (unfold string_length in *; lia).
  assert (Hchar : Znth i input 0 = 91).
  { rewrite <- c_string_Znth_inside by exact Hi. exact PreH4. }
  pose proof (nested_scan_step_132 input i count maxcount 91
    (count + 1) (count + 1) PreH18 ltac:(lia) (eq_sym Hchar)
    (or_introl eq_refl) ltac:(vm_compute; lia)
    ltac:(rewrite Z.max_r; lia)) as Hstep.
  unfold string_length in *.
  rewrite <- derivable1_orp_intros2.
  entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_3_1 : is_nested_entail_wit_3_1.
Proof.
  left; intros.
  pose proof (nested_scan_after_found_132 input (i + 1)
    count maxcount PreH13 PreH1).
  pre_process; entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_3_2 : is_nested_entail_wit_3_2.
Proof.
  left; intros.
  pose proof (nested_scan_after_found_132 input (i + 1)
    count maxcount PreH13 PreH1).
  pre_process; entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_4_1 : is_nested_entail_wit_4_1.
Proof.
  left; intros.
  pose proof (nested_scan_after_continue_132 input (i + 1)
    count maxcount PreH13 ltac:(lia)).
  pre_process; entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_4_2 : is_nested_entail_wit_4_2.
Proof.
  left; intros.
  pose proof (nested_scan_after_continue_132 input (i + 1)
    count maxcount PreH13 ltac:(lia)).
  pre_process; entailer!.
Qed.

Lemma proof_of_is_nested_entail_wit_5 : is_nested_entail_wit_5.
Proof.
  left; intros.
  assert (i = Zlength input) by (unfold string_length in *; lia).
  subst i.
  pose proof (nested_scan_final_false_132 input count maxcount PreH14).
  pre_process; entailer!.
Qed.
