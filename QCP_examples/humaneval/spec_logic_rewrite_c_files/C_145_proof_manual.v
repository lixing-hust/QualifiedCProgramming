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
From SimpleC.EE Require Import C_145_goal.
From SimpleC.EE Require Import C_145_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_145.
Local Open Scope sac.

Ltac solve_abs_145 :=
  unfold Zabs in *;
  repeat match goal with
  | H : ?x >= 0 |- context[Z.abs ?x] => rewrite Z.abs_eq by lia
  | H : ?x < 0 |- context[Z.abs ?x] => rewrite Z.abs_neq by lia
  end;
  lia.

Ltac solve_digit_145 :=
  unfold signed_digit_score_result_145 in *;
  repeat match goal with
  | H : ?r = Z.abs ?x |- first_digit_state_145 (Z.abs ?x) ?r =>
      subst r; apply first_digit_state_145_start; lia
  | H : ?r = Z.abs ?x |- first_digit_state_145 (Zabs ?x) ?r =>
      subst r; unfold Zabs; apply first_digit_state_145_start; lia
  | Hs : first_digit_state_145 (Z.abs ?x) ?t,
    Ht : ?t >= 10 |- first_digit_state_145 (Z.abs ?x) (Z.quot ?t 10) =>
      apply first_digit_state_145_step; [lia|exact Hs]
  | Hs : first_digit_state_145 (Zabs ?x) ?t,
    Ht : ?t >= 10 |- first_digit_state_145 (Zabs ?x) (Z.quot ?t 10) =>
      unfold Zabs in *; apply first_digit_state_145_step; [lia|exact Hs]
  | Hs : first_digit_state_145 (Z.abs ?x) ?t,
    Hret : ?ret = Z.abs ?x,
    Hret10 : ?ret >= 10,
    Hx : ?x >= 0,
    Hsum : ?sum = 0
    |- highest_power10_state_145 ?x ?ret 1 (?sum + ?t) =>
      replace (sum + t) with t by lia;
      eapply first_digit_state_145_to_high_pos; [exact Hret|lia|exact Hs|lia|lia]
  | Hs : first_digit_state_145 (Zabs ?x) ?t,
    Hret : ?ret = Zabs ?x,
    Hret10 : ?ret >= 10,
    Hx : ?x >= 0,
    Hsum : ?sum = 0
    |- highest_power10_state_145 ?x ?ret 1 (?sum + ?t) =>
      change (Zabs x) with (Z.abs x) in Hret, Hs;
      replace (sum + t) with t by lia;
      eapply first_digit_state_145_to_high_pos; [exact Hret|lia|exact Hs|lia|lia]
  | Hs : first_digit_state_145 (Z.abs ?x) ?t,
    Hret : ?ret = Z.abs ?x,
    Hret10 : ?ret >= 10,
    Hx : ?x < 0,
    Hsum : ?sum = 0
    |- highest_power10_state_145 ?x ?ret 1 (?sum + (- ?t)) =>
      replace (sum + (- t)) with (- t) by lia;
      eapply first_digit_state_145_to_high_neg; [exact Hret|lia|exact Hs|lia|lia]
  | Hs : first_digit_state_145 (Zabs ?x) ?t,
    Hret : ?ret = Zabs ?x,
    Hret10 : ?ret >= 10,
    Hx : ?x < 0,
    Hsum : ?sum = 0
    |- highest_power10_state_145 ?x ?ret 1 (?sum + (- ?t)) =>
      change (Zabs x) with (Z.abs x) in Hret, Hs;
      replace (sum + (- t)) with (- t) by lia;
      eapply first_digit_state_145_to_high_neg; [exact Hret|lia|exact Hs|lia|lia]
  | Hs : highest_power10_state_145 ?x ?t ?p ?sum,
    Hp : ?p <= Z.quot ?t 10
    |- highest_power10_state_145 ?x ?t (?p * 10) ?sum =>
      eapply highest_power10_state_145_step; [exact Hp|exact Hs]
  | Hs : highest_power10_state_145 ?x ?t ?p ?sum,
    Hp : ?p > Z.quot ?t 10
    |- signed_digit_tail_state_145 ?x (Z.rem ?t ?p) ?sum =>
      eapply highest_power10_state_145_to_tail; [lia|lia|exact Hp|exact Hs]
  | Hs : signed_digit_tail_state_145 ?x ?t ?sum,
    Ht : ?t > 0
    |- signed_digit_tail_state_145 ?x (Z.quot ?t 10) (?sum + Z.rem ?t 10) =>
      eapply signed_digit_tail_state_145_step; [lia|exact Hs]
  | Hs : signed_digit_tail_state_145 ?x 0 ?sum
    |- signed_digit_sum ?x ?sum =>
      apply signed_digit_tail_state_145_done; exact Hs
  | Hs : signed_digit_tail_state_145 ?x ?t ?sum,
    Hle : ?t <= 0, Hge : 0 <= ?t
    |- signed_digit_sum ?x ?sum =>
      replace t with 0 in Hs by lia;
      apply signed_digit_tail_state_145_done; exact Hs
  | Hret : ?ret = Z.abs ?x, Hretlt : ?ret < 10, Hx : ?x >= 0
    |- signed_digit_tail_state_145 ?x 0 (0 + ?t) =>
      replace (0 + t) with t by lia;
      unfold signed_digit_tail_state_145;
      exists t, 0; repeat split; try lia;
      [ eapply signed_digit_sum_single_pos_145; [lia| |lia]; rewrite <- Hret; lia
      | cbn; lia ]
  | Hret : ?ret = Z.abs ?x, Hretlt : ?ret < 10, Hx : ?x < 0
    |- signed_digit_tail_state_145 ?x 0 (0 + (- ?t)) =>
      replace (0 + (- t)) with (- t) by lia;
      unfold signed_digit_tail_state_145;
      exists (- t), 0; repeat split; try lia;
      [ eapply signed_digit_sum_single_neg_145; [lia| |lia]; rewrite <- Hret; lia
      | cbn; lia ]
  end;
  match goal with
  | Hp : ?p <= Z.quot ?t 10 |- context[?p * 10] =>
      let Hmul := fresh "Hmul_bound" in
      assert (Hmul : p * 10 <= t) by
        (pose proof (Z.quot_rem t 10 ltac:(lia));
         pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia));
         nia)
  | _ => idtac
  end;
  try match goal with
  | |- context[Z.quot ?t 10] =>
      pose proof (Z.quot_pos t 10 ltac:(lia) ltac:(lia));
      pose proof (Z.quot_le_upper_bound t 10 t ltac:(lia) ltac:(lia))
  | |- context[Z.rem ?t 10] =>
      pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia))
  | |- context[Z.rem ?t ?p] =>
      pose proof (Z.rem_bound_pos t p ltac:(lia) ltac:(lia))
  end;
  try lia.

Ltac vc_145 :=
  pre_process; entailer!; solve_digit_145.

Lemma proof_of_abs_return_wit_1_split_goal_1 : abs_return_wit_1_split_goal_1.
Proof. pre_process; entailer!; solve_abs_145. Qed.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof. right; pre_process; entailer!; solve_abs_145. Qed.

Lemma proof_of_abs_return_wit_2_split_goal_1 : abs_return_wit_2_split_goal_1.
Proof. pre_process; entailer!; solve_abs_145. Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof. right; pre_process; entailer!; solve_abs_145. Qed.

Lemma proof_of_signed_digit_score_safety_wit_15_split_goal_1 : signed_digit_score_safety_wit_15_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_safety_wit_15_split_goal_2 : signed_digit_score_safety_wit_15_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_safety_wit_15 : signed_digit_score_safety_wit_15.
Proof. right; vc_145. Qed.

Lemma proof_of_signed_digit_score_safety_wit_21_split_goal_1 : signed_digit_score_safety_wit_21_split_goal_1.
Proof.
  pre_process; entailer!.
  pose proof (signed_digit_tail_state_145_add_upper x_pre t sum PreH1 PreH8) as Hupper.
  exact Hupper.
Qed.

Lemma proof_of_signed_digit_score_safety_wit_21_split_goal_2 : signed_digit_score_safety_wit_21_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_signed_digit_score_safety_wit_21 : signed_digit_score_safety_wit_21.
Proof.
  right.
  pre_process; entailer!.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (signed_digit_tail_state_145_add_upper x_pre t sum PreH1 PreH8) as Hupper.
    exact Hupper.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_1_split_goal_1 : signed_digit_score_entail_wit_1_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_1 : signed_digit_score_entail_wit_1.
Proof. right; vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_2_split_goal_1 : signed_digit_score_entail_wit_2_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_2_split_goal_2 : signed_digit_score_entail_wit_2_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_2_split_goal_3 : signed_digit_score_entail_wit_2_split_goal_3.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_2 : signed_digit_score_entail_wit_2.
Proof. right; vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_1_split_goal_1 : signed_digit_score_entail_wit_3_1_split_goal_1.
Proof.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  replace (sum + t) with t by lia.
  eapply first_digit_state_145_to_high_pos; [exact PreH2|lia|exact PreH12|lia|lia].
Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_1 : signed_digit_score_entail_wit_3_1.
Proof.
  right.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  replace (sum + t) with t by lia.
  eapply first_digit_state_145_to_high_pos; [exact PreH2|lia|exact PreH12|lia|lia].
Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_2_split_goal_1 : signed_digit_score_entail_wit_3_2_split_goal_1.
Proof.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  replace (sum + (- t)) with (- t) by lia.
  eapply first_digit_state_145_to_high_neg; [exact PreH2|lia|exact PreH12|lia|lia].
Qed.

Lemma proof_of_signed_digit_score_entail_wit_3_2 : signed_digit_score_entail_wit_3_2.
Proof.
  right.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  replace (sum + (- t)) with (- t) by lia.
  eapply first_digit_state_145_to_high_neg; [exact PreH2|lia|exact PreH12|lia|lia].
Qed.

Lemma proof_of_signed_digit_score_entail_wit_4_split_goal_1 : signed_digit_score_entail_wit_4_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_4_split_goal_2 : signed_digit_score_entail_wit_4_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_4 : signed_digit_score_entail_wit_4.
Proof. right; vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_1_split_goal_1 : signed_digit_score_entail_wit_5_1_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_1_split_goal_2 : signed_digit_score_entail_wit_5_1_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_1_split_goal_3 : signed_digit_score_entail_wit_5_1_split_goal_3.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_1 : signed_digit_score_entail_wit_5_1.
Proof. right; vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_2_split_goal_1 : signed_digit_score_entail_wit_5_2_split_goal_1.
Proof.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  assert (Ht_eq : t = retval).
  { eapply first_digit_state_145_small_eq; [exact PreH12|lia]. }
  subst t.
  replace (sum + retval) with retval by lia.
  unfold signed_digit_tail_state_145.
  exists retval, 0.
  repeat split; try lia.
  - eapply signed_digit_sum_single_pos_145; [lia|exact PreH2|lia].
  - cbn; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_2 : signed_digit_score_entail_wit_5_2.
Proof.
  right.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  assert (Ht_eq : t = retval).
  { eapply first_digit_state_145_small_eq; [exact PreH12|lia]. }
  subst t.
  replace (sum + retval) with retval by lia.
  unfold signed_digit_tail_state_145.
  exists retval, 0.
  repeat split; try lia.
  - eapply signed_digit_sum_single_pos_145; [lia|exact PreH2|lia].
  - cbn; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_3_split_goal_1 : signed_digit_score_entail_wit_5_3_split_goal_1.
Proof.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  assert (Ht_eq : t = retval).
  { eapply first_digit_state_145_small_eq; [exact PreH12|lia]. }
  subst t.
  replace (sum + (- retval)) with (- retval) by lia.
  unfold signed_digit_tail_state_145.
  exists (- retval), 0.
  repeat split; try lia.
  - eapply signed_digit_sum_single_neg_145; [lia|exact PreH2|lia].
  - cbn; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_5_3 : signed_digit_score_entail_wit_5_3.
Proof.
  right.
  pre_process; entailer!.
  change (Zabs x_pre) with (Z.abs x_pre) in PreH2, PreH12.
  rewrite <- PreH2 in PreH12.
  assert (Ht_eq : t = retval).
  { eapply first_digit_state_145_small_eq; [exact PreH12|lia]. }
  subst t.
  replace (sum + (- retval)) with (- retval) by lia.
  unfold signed_digit_tail_state_145.
  exists (- retval), 0.
  repeat split; try lia.
  - eapply signed_digit_sum_single_neg_145; [lia|exact PreH2|lia].
  - cbn; lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_6_split_goal_1 : signed_digit_score_entail_wit_6_split_goal_1.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_6_split_goal_2 : signed_digit_score_entail_wit_6_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (signed_digit_tail_state_145_add_upper x_pre t sum PreH1 PreH8) as Hupper.
  exact Hupper.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_6_split_goal_3 : signed_digit_score_entail_wit_6_split_goal_3.
Proof.
  pre_process; entailer!.
  pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_signed_digit_score_entail_wit_6_split_goal_4 : signed_digit_score_entail_wit_6_split_goal_4.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_6_split_goal_5 : signed_digit_score_entail_wit_6_split_goal_5.
Proof. vc_145. Qed.

Lemma proof_of_signed_digit_score_entail_wit_6 : signed_digit_score_entail_wit_6.
Proof.
  right.
  pre_process; entailer!.
  - pose proof (Z.quot_pos t 10 ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (Z.quot_pos t 10 ltac:(lia) ltac:(lia)).
    pose proof (Z.quot_le_upper_bound t 10 t ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (Z.rem_bound_pos t 10 ltac:(lia) ltac:(lia)).
    lia.
  - pose proof (signed_digit_tail_state_145_add_upper x_pre t sum PreH1 PreH8) as Hupper.
    exact Hupper.
  - eapply signed_digit_tail_state_145_step; [lia|exact PreH8].
Qed.

Lemma proof_of_signed_digit_score_return_wit_1_split_goal_1 : signed_digit_score_return_wit_1_split_goal_1.
Proof.
  pre_process; entailer!.
  pose proof (signed_digit_tail_state_145_final_bounds x_pre t sum ltac:(lia) PreH8) as [_ Hupper].
  exact Hupper.
Qed.

Lemma proof_of_signed_digit_score_return_wit_1_split_goal_2 : signed_digit_score_return_wit_1_split_goal_2.
Proof.
  pre_process; entailer!.
  pose proof (signed_digit_tail_state_145_final_bounds x_pre t sum ltac:(lia) PreH8) as [Hlower _].
  exact Hlower.
Qed.

Lemma proof_of_signed_digit_score_return_wit_1_split_goal_3 : signed_digit_score_return_wit_1_split_goal_3.
Proof.
  pre_process; entailer!.
  unfold signed_digit_score_result_145.
  replace t with 0 in PreH8 by lia.
  apply signed_digit_tail_state_145_done.
  exact PreH8.
Qed.

Lemma proof_of_signed_digit_score_return_wit_1 : signed_digit_score_return_wit_1.
Proof.
  right.
  pre_process; entailer!.
  - unfold signed_digit_score_result_145.
    replace t with 0 in PreH8 by lia.
    apply signed_digit_tail_state_145_done.
    exact PreH8.
  - pose proof (signed_digit_tail_state_145_final_bounds x_pre t sum ltac:(lia) PreH8) as [Hlower _].
    exact Hlower.
  - pose proof (signed_digit_tail_state_145_final_bounds x_pre t sum ltac:(lia) PreH8) as [_ Hupper].
    exact Hupper.
Qed.

Lemma proof_of_order_by_points_entail_wit_1_split_goal_1 : order_by_points_entail_wit_1_split_goal_1.
Proof. vc_145; apply order_copy_prefix_145_nil. Qed.

Lemma proof_of_order_by_points_entail_wit_1_split_goal_2 : order_by_points_entail_wit_1_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_order_by_points_entail_wit_1_split_goal_spatial : order_by_points_entail_wit_1_split_goal_spatial.
Proof. pre_process; entailer!. Qed.

Lemma proof_of_order_by_points_entail_wit_1 : order_by_points_entail_wit_1.
Proof.
  right.
  pre_process; entailer!.
  apply order_copy_prefix_145_nil.
Qed.

Lemma proof_of_order_by_points_entail_wit_2_split_goal_1 : order_by_points_entail_wit_2_split_goal_1.
Proof.
  vc_145.
  eapply order_copy_prefix_145_step; [exact PreH13|lia].
Qed.

Lemma proof_of_order_by_points_entail_wit_2_split_goal_2 : order_by_points_entail_wit_2_split_goal_2.
Proof.
  vc_145.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_2_split_goal_spatial : order_by_points_entail_wit_2_split_goal_spatial.
Proof. pre_process; entailer!. Qed.

Lemma proof_of_order_by_points_entail_wit_2 : order_by_points_entail_wit_2.
Proof.
  right.
  pre_process; entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - eapply order_copy_prefix_145_step; [exact PreH13|lia].
Qed.

Lemma proof_of_order_by_points_entail_wit_4_split_goal_1 : order_by_points_entail_wit_4_split_goal_1.
Proof. vc_145; apply order_score_prefix_145_nil. Qed.

Lemma proof_of_order_by_points_entail_wit_4_split_goal_2 : order_by_points_entail_wit_4_split_goal_2.
Proof. vc_145. Qed.

Lemma proof_of_order_by_points_entail_wit_4_split_goal_spatial : order_by_points_entail_wit_4_split_goal_spatial.
Proof.
  pre_process; entailer!.
  unfold order_copy_prefix_145 in PreH13.
  destruct PreH13 as [[_ _] [Hlen Hout]].
  assert (Hi : i = nums_size_pre) by lia.
  subst i.
  rewrite Hout.
  rewrite sublist_self by lia.
  replace (Zlength input_l) with nums_size_pre by lia.
  sep_apply (IntArray.seg_to_full data 0 nums_size_pre input_l).
  replace (data + 0 * sizeof(INT)) with data by lia.
  replace (nums_size_pre - 0) with nums_size_pre by lia.
  entailer!.
Qed.

Lemma proof_of_order_by_points_entail_wit_4 : order_by_points_entail_wit_4.
Proof.
  right.
  pre_process; entailer!.
  - unfold order_copy_prefix_145 in PreH13.
    destruct PreH13 as [[_ _] [Hlen Hout]].
    assert (Hi : i = nums_size_pre) by lia.
    subst i.
    rewrite Hout.
    rewrite sublist_self by lia.
    replace (Zlength input_l) with nums_size_pre by lia.
    sep_apply (IntArray.seg_to_full data 0 nums_size_pre input_l).
    replace (data + 0 * sizeof(INT)) with data by lia.
    replace (nums_size_pre - 0) with nums_size_pre by lia.
    entailer!.
  - apply order_score_prefix_145_nil.
Qed.

Lemma proof_of_order_by_points_entail_wit_5_split_goal_1 : order_by_points_entail_wit_5_split_goal_1.
Proof.
  vc_145.
  eapply order_score_prefix_145_step; [exact PreH16|lia|exact PreH1].
Qed.

Lemma proof_of_order_by_points_entail_wit_5_split_goal_2 : order_by_points_entail_wit_5_split_goal_2.
Proof.
  vc_145.
  rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_5 : order_by_points_entail_wit_5.
Proof.
  right.
  pre_process; entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  - eapply order_score_prefix_145_step; [exact PreH16|lia|exact PreH1].
Qed.

Lemma proof_of_order_by_points_entail_wit_7 : order_by_points_entail_wit_7.
Proof.
  right.
  pre_process.
  Exists score_l_2 score_l_2.
  entailer!.
  - assert (Hi : i = nums_size_pre) by lia.
    subst i.
    replace (Zlength input_l) with nums_size_pre by lia.
    replace (Zlength score_l_2) with nums_size_pre by lia.
    sep_apply (IntArray.seg_to_full score 0 nums_size_pre score_l_2).
    replace (score + 0 * sizeof(INT)) with score by lia.
    replace (nums_size_pre - 0) with nums_size_pre by lia.
    entailer!.
  - assert (Hi : i = nums_size_pre) by lia.
    subst i.
    replace (Zlength score_l_2) with (Zlength input_l) in PreH13 by lia.
    apply order_outer_state_145_init.
    exact PreH13.
Qed.

Lemma proof_of_order_by_points_entail_wit_8 : order_by_points_entail_wit_8.
Proof.
  right.
  pre_process.
  Exists initial_score_l_2.
  entailer!.
  eapply order_inner_state_145_init; [exact PreH14|lia].
Qed.

Lemma proof_of_order_by_points_entail_wit_9 : order_by_points_entail_wit_9.
Proof.
  right.
  pre_process.
  Exists initial_score_l_2.
  entailer!.
  assert (Hj : j = nums_size_pre) by lia.
  subst j.
  assert (Hinner :
    order_inner_state_145 i (Zlength input_l) input_l initial_score_l_2
      output_l_2 score_l_2).
  {
    rewrite <- PreH7.
    exact PreH16.
  }
  eapply order_outer_state_145_step.
  - exact Hinner.
  - lia.
  - intros Hdone.
    eapply order_inner_state_145_final_spec.
    + exact Hinner.
    + exact Hdone.
Qed.

Lemma proof_of_order_by_points_entail_wit_10_1 : order_by_points_entail_wit_10_1.
Proof.
  right.
  pre_process.
  Exists initial_score_l_2.
  entailer!.
  - eapply order_inner_state_145_step_swap; [exact PreH17|lia|exact PreH1].
  - repeat rewrite replace_Znth_length_145; lia.
  - repeat rewrite replace_Znth_length_145; lia.
Qed.

Lemma proof_of_order_by_points_entail_wit_10_2 : order_by_points_entail_wit_10_2.
Proof.
  right.
  pre_process.
  Exists initial_score_l_2.
  entailer!.
  eapply order_inner_state_145_step_keep; [exact PreH17|lia|exact PreH1].
Qed.

Lemma proof_of_order_by_points_entail_wit_12_split_goal_1 : order_by_points_entail_wit_12_split_goal_1.
Proof.
  pre_process; entailer!.
  assert (Hi : i = Zlength input_l) by lia.
  unfold order_outer_state_145 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ Hfinal]]]]].
  apply Hfinal.
  exact Hi.
Qed.

Lemma proof_of_order_by_points_entail_wit_12 : order_by_points_entail_wit_12.
Proof.
  right.
  pre_process; entailer!.
  assert (Hi : i = Zlength input_l) by lia.
  unfold order_outer_state_145 in PreH14.
  destruct PreH14 as [_ [_ [_ [_ [_ Hfinal]]]]].
  apply Hfinal.
  exact Hi.
Qed.

Lemma proof_of_order_by_points_partial_solve_wit_7_pure_split_goal_1 : order_by_points_partial_solve_wit_7_pure_split_goal_1.
Proof.
  vc_145.
  match goal with
  | Hsafe : order_by_points_safe_145 input_l |- _ =>
      pose proof (order_by_points_safe_145_at input_l i Hsafe ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_order_by_points_partial_solve_wit_7_pure_split_goal_2 : order_by_points_partial_solve_wit_7_pure_split_goal_2.
Proof.
  vc_145.
  match goal with
  | Hsafe : order_by_points_safe_145 input_l |- _ =>
      pose proof (order_by_points_safe_145_at input_l i Hsafe ltac:(lia))
  end.
  lia.
Qed.

Lemma proof_of_order_by_points_partial_solve_wit_7_pure : order_by_points_partial_solve_wit_7_pure.
Proof.
  vc_145.
  - match goal with
    | Hsafe : order_by_points_safe_145 input_l |- _ =>
        pose proof (order_by_points_safe_145_at input_l i Hsafe ltac:(lia))
    end.
    lia.
  - match goal with
    | Hsafe : order_by_points_safe_145 input_l |- _ =>
        pose proof (order_by_points_safe_145_at input_l i Hsafe ltac:(lia))
    end.
    lia.
Qed.
