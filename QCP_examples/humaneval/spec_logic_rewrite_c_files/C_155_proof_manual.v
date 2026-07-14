Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_155_goal.
From SimpleC.EE Require Import C_155_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_155.
Local Open Scope sac.

Ltac unfold_abs_155 :=
  unfold Zabs_155 in *;
  repeat match goal with
  | H : ?x >= 0 |- context[Z.abs ?x] => rewrite Z.abs_eq by lia
  | H : ?x < 0 |- context[Z.abs ?x] => rewrite Z.abs_neq by lia
  | H : 0 <= ?x |- context[Z.abs ?x] => rewrite Z.abs_eq by lia
  end.

Ltac vc_basic_155 :=
  pre_process; entailer!; unfold_abs_155; try lia.

Ltac init_zero_155 :=
  subst; unfold_abs_155;
  apply digit_count_state_init_zero_155; lia.

Ltac step_even_safe_155 :=
  pose proof (digit_count_state_step_even_safe_155 _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(eassumption));
  lia.

Ltac step_odd_safe_155 :=
  pose proof (digit_count_state_step_odd_safe_155 _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(eassumption));
  lia.

Ltac quot_bound_155 :=
  pre_process; entailer!;
  unfold_abs_155;
  rewrite Z.quot_div_nonneg by lia;
  try (apply Z.div_pos; lia);
  try (apply Z.div_le_upper_bound; lia);
  lia.

Lemma proof_of_even_odd_count_safety_wit_19_split_goal_1 : even_odd_count_safety_wit_19_split_goal_1.
Proof. pre_process; entailer!; step_odd_safe_155. Qed.

Lemma proof_of_even_odd_count_safety_wit_19_split_goal_2 : even_odd_count_safety_wit_19_split_goal_2.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_safety_wit_19 : even_odd_count_safety_wit_19.
Proof. right; pre_process; entailer!; step_odd_safe_155. Qed.

Lemma proof_of_even_odd_count_safety_wit_21_split_goal_1 : even_odd_count_safety_wit_21_split_goal_1.
Proof. pre_process; entailer!; step_even_safe_155. Qed.

Lemma proof_of_even_odd_count_safety_wit_21_split_goal_2 : even_odd_count_safety_wit_21_split_goal_2.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_safety_wit_21 : even_odd_count_safety_wit_21.
Proof. right; pre_process; entailer!; step_even_safe_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1_split_goal_1 : even_odd_count_entail_wit_1_1_split_goal_1.
Proof. pre_process; entailer!; init_zero_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1_split_goal_2 : even_odd_count_entail_wit_1_1_split_goal_2.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1_split_goal_3 : even_odd_count_entail_wit_1_1_split_goal_3.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1_split_goal_4 : even_odd_count_entail_wit_1_1_split_goal_4.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_1 : even_odd_count_entail_wit_1_1.
Proof.
  right; pre_process; entailer!.
  all: try solve [init_zero_155 | unfold_abs_155; lia].
Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2_split_goal_1 : even_odd_count_entail_wit_1_2_split_goal_1.
Proof.
  pre_process; entailer!.
  subst.
  replace (- num0) with (Z.abs num0) by (rewrite Z.abs_neq by lia; lia).
  apply digit_count_state_init_nonzero_155; lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2_split_goal_2 : even_odd_count_entail_wit_1_2_split_goal_2.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2_split_goal_3 : even_odd_count_entail_wit_1_2_split_goal_3.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2_split_goal_4 : even_odd_count_entail_wit_1_2_split_goal_4.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_2 : even_odd_count_entail_wit_1_2.
Proof.
  right; pre_process; entailer!.
  all: try solve
    [ subst; replace (- num0) with (Z.abs num0) by (rewrite Z.abs_neq by lia; lia);
      apply digit_count_state_init_nonzero_155; lia
    | unfold_abs_155; lia ].
Qed.

Lemma proof_of_even_odd_count_entail_wit_1_3_split_goal_1 : even_odd_count_entail_wit_1_3_split_goal_1.
Proof.
  pre_process; entailer!.
  subst.
  replace num0 with (Z.abs num0) at 2 by (rewrite Z.abs_eq by lia; lia).
  apply digit_count_state_init_nonzero_155; lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_1_3_split_goal_2 : even_odd_count_entail_wit_1_3_split_goal_2.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_3_split_goal_3 : even_odd_count_entail_wit_1_3_split_goal_3.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_3_split_goal_4 : even_odd_count_entail_wit_1_3_split_goal_4.
Proof. vc_basic_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_1_3 : even_odd_count_entail_wit_1_3.
Proof.
  right; pre_process; entailer!.
  all: try solve
    [ subst; replace num0 with (Z.abs num0) at 2 by (rewrite Z.abs_eq by lia; lia);
      apply digit_count_state_init_nonzero_155; lia
    | unfold_abs_155; lia ].
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_1_split_goal_1 : even_odd_count_entail_wit_2_1_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply digit_count_state_step_even_155; [eassumption|lia|reflexivity|eassumption].
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_1_split_goal_2 : even_odd_count_entail_wit_2_1_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (digit_count_state_step_even_155
    num0 w n2 n1 (Z.rem w 10) PreH13 ltac:(lia) eq_refl PreH1) as Hnext.
  unfold digit_count_state_155 in Hnext.
  destruct Hnext as [_ [Hn2_next [Hn1_next [fuel [_ [_ Hbound]]]]]].
  rewrite Zlength_correct in Hbound.
  unfold_abs_155.
  lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_1_split_goal_3 : even_odd_count_entail_wit_2_1_split_goal_3.
Proof. quot_bound_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_2_1_split_goal_4 : even_odd_count_entail_wit_2_1_split_goal_4.
Proof. quot_bound_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_2_1 : even_odd_count_entail_wit_2_1.
Proof.
  right; pre_process; entailer!.
  all: try solve
    [ eapply digit_count_state_step_even_155; [eassumption|lia|reflexivity|eassumption]
    | match goal with
      | Hstate : digit_count_state_155 ?num ?w ?even ?odd,
        Hcase : Z.rem (Z.rem ?w 10) 2 <> 1 |- _ =>
          pose proof (digit_count_state_step_even_155
            num w even odd (Z.rem w 10) Hstate ltac:(lia) eq_refl Hcase) as Hnext;
          unfold digit_count_state_155 in Hnext;
          destruct Hnext as [_ [Hnext_even [Hnext_odd [fuel [_ [_ Hbound]]]]]];
          rewrite Zlength_correct in Hbound; unfold_abs_155; lia
      end
    | quot_bound_155
    | unfold_abs_155; lia ].
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_2_split_goal_1 : even_odd_count_entail_wit_2_2_split_goal_1.
Proof.
  pre_process; entailer!.
  eapply digit_count_state_step_odd_155; [eassumption|lia|reflexivity|eassumption].
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_2_split_goal_2 : even_odd_count_entail_wit_2_2_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (digit_count_state_step_odd_155
    num0 w n2 n1 (Z.rem w 10) PreH13 ltac:(lia) eq_refl PreH1) as Hnext.
  unfold digit_count_state_155 in Hnext.
  destruct Hnext as [_ [Hn2_next [Hn1_next [fuel [_ [_ Hbound]]]]]].
  rewrite Zlength_correct in Hbound.
  unfold_abs_155.
  lia.
Qed.

Lemma proof_of_even_odd_count_entail_wit_2_2_split_goal_3 : even_odd_count_entail_wit_2_2_split_goal_3.
Proof. quot_bound_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_2_2_split_goal_4 : even_odd_count_entail_wit_2_2_split_goal_4.
Proof. quot_bound_155. Qed.

Lemma proof_of_even_odd_count_entail_wit_2_2 : even_odd_count_entail_wit_2_2.
Proof.
  right; pre_process; entailer!.
  all: try solve
    [ eapply digit_count_state_step_odd_155; [eassumption|lia|reflexivity|eassumption]
    | match goal with
      | Hstate : digit_count_state_155 ?num ?w ?even ?odd,
        Hcase : Z.rem (Z.rem ?w 10) 2 = 1 |- _ =>
          pose proof (digit_count_state_step_odd_155
            num w even odd (Z.rem w 10) Hstate ltac:(lia) eq_refl Hcase) as Hnext;
          unfold digit_count_state_155 in Hnext;
          destruct Hnext as [_ [Hnext_even [Hnext_odd [fuel [_ [_ Hbound]]]]]];
          rewrite Zlength_correct in Hbound; unfold_abs_155; lia
      end
    | quot_bound_155
    | unfold_abs_155; lia ].
Qed.

Lemma proof_of_even_odd_count_entail_wit_4_split_goal_1 : even_odd_count_entail_wit_4_split_goal_1.
Proof.
  pre_process; entailer!.
  replace w with 0 in * by lia.
  apply digit_count_state_final_spec_155; assumption.
Qed.

Lemma proof_of_even_odd_count_entail_wit_4_split_goal_2 : even_odd_count_entail_wit_4_split_goal_2.
Proof.
  pre_process; entailer!.
  replace w with 0 in * by lia.
  exact PreH18.
Qed.

Lemma proof_of_even_odd_count_entail_wit_4_split_goal_spatial : even_odd_count_entail_wit_4_split_goal_spatial.
Proof.
  pre_process; unfold IntArray.full, store_array, store_array_rec; simpl; entailer!.
Qed.

Lemma proof_of_even_odd_count_entail_wit_4 : even_odd_count_entail_wit_4.
Proof.
  right; pre_process; entailer!.
  all: try solve
    [ replace w with 0 in * by lia; exact PreH18
    | replace w with 0 in * by lia; apply digit_count_state_final_spec_155; assumption
    | unfold IntArray.full, store_array, store_array_rec; simpl; entailer! ].
Qed.
