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
From SimpleC.EE Require Import C_6_goal.
From SimpleC.EE Require Import C_6_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import coins_6.
Local Open Scope sac.

Ltac solve_len_6 :=
  unfold SimpleC.StdLib.string_lib.string_length, coins_6.string_length in *; lia.

Lemma proof_of_parse_nested_parens_entail_wit_1 : parse_nested_parens_entail_wit_1.
Proof.
  right; intros.
  pre_process.
  entailer!;
    try apply parse_state_6_initial;
    try (subst retval; unfold SimpleC.StdLib.string_lib.string_length, coins_6.string_length; apply Zlength_nonneg);
    try solve_len_6.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_1 : parse_nested_parens_entail_wit_2_1.
Proof.
  right; intros.
  pre_process.
  entailer!.
  rewrite c_string_Znth_inside in PreH3 by solve_len_6.
  pose proof (parse_state_6_step_open
                str_l i level max_level output_l_2
                PreH26 PreH3 ltac:(solve_len_6)) as Hstep.
  replace (Z.max max_level (level + 1)) with max_level in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_2_2 : parse_nested_parens_entail_wit_2_2.
Proof.
  right; intros.
  pre_process.
  entailer!.
  rewrite c_string_Znth_inside in PreH3 by solve_len_6.
  pose proof (parse_state_6_step_open
                str_l i level max_level output_l_2
                PreH26 PreH3 ltac:(solve_len_6)) as Hstep.
  replace (Z.max max_level (level + 1)) with (level + 1) in Hstep by lia.
  exact Hstep.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_3 : parse_nested_parens_entail_wit_3.
Proof.
  right; intros.
  pre_process.
  rewrite c_string_Znth_inside in PreH3 by solve_len_6.
  assert (Hlevel_one : level = 1) by lia.
  subst level.
  entailer!.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
  - replace (1 - 1) with 0 by lia.
    eapply parse_state_6_step_close_finish; eauto; solve_len_6.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_4 : parse_nested_parens_entail_wit_4.
Proof.
  right; intros.
  pre_process.
  rewrite c_string_Znth_inside in PreH3 by solve_len_6.
  assert (Hlevel_pos : 0 < level).
  {
    destruct PreH24 as [Hsafe _].
    assert (0 <= i < Zlength str_l) by solve_len_6.
    specialize (Hsafe i H PreH3).
    unfold parse_state_6 in PreH27.
    destruct PreH27 as [_ [_ [Hlev _]]].
    lia.
  }
  entailer!.
  eapply parse_state_6_step_close_continue; eauto; solve_len_6.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_5 : parse_nested_parens_entail_wit_5.
Proof.
  right; intros.
  pre_process.
  rewrite c_string_Znth_inside in PreH2 by solve_len_6.
  rewrite c_string_Znth_inside in PreH3 by solve_len_6.
  assert (Hspace : Znth i str_l 0 = 32).
  {
    destruct (PreH22 i ltac:(solve_len_6)) as [|[|]]; lia.
  }
  entailer!.
  - rewrite c_string_Znth_inside by solve_len_6.
    exact Hspace.
  - eapply parse_state_6_step_space; eauto; solve_len_6.
Qed.

Lemma proof_of_parse_nested_parens_entail_wit_7 : parse_nested_parens_entail_wit_7.
Proof.
  right; intros.
  pre_process.
  assert (Hend : i >= string_length str_l) by lia.
  destruct (parse_state_6_final_facts
              str_l i level max_level output_l_2 PreH24 PreH21 Hend)
    as [Hlevel [Hmax [Hout Hspec]]].
  subst.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_return_wit_1 : parse_nested_parens_return_wit_1.
Proof.
  right; intros.
  pre_process.
  subst.
  entailer!.
Qed.

Lemma proof_of_parse_nested_parens_partial_solve_wit_3_pure : parse_nested_parens_partial_solve_wit_3_pure.
Proof.
  right; intros.
  pre_process; entailer!.
  subst retval.
  unfold SimpleC.StdLib.string_lib.string_length, coins_6.string_length in *.
  pose proof (Zlength_nonneg str_l).
  lia.
Qed.
