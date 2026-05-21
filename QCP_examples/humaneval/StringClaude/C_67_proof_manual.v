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
From SimpleC.EE Require Import C_67_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_67.
Local Open Scope sac.

Ltac fruit_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  unfold int_min_z, int_max_z, int_cur_mul10_bound_z in *.

Ltac simplify_zbool :=
  repeat match goal with
  | H : ?x <= ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?y >= ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?x > ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?y < ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?x < ?y |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true by (symmetry; apply Z.ltb_lt; lia)
  | H : ?y > ?x |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true by (symmetry; apply Z.ltb_lt; lia)
  | H : ?x >= ?y |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false by (symmetry; apply Z.ltb_ge; lia)
  | H : ?y <= ?x |- context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false by (symmetry; apply Z.ltb_ge; lia)
  end;
  simpl in *.

Ltac simplify_zbool_in Hctx :=
  repeat match type of Hctx with
  | context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true in Hctx by (symmetry; apply Z.leb_le; lia)
  | context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false in Hctx by (symmetry; apply Z.leb_gt; lia)
  | context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with true in Hctx by (symmetry; apply Z.ltb_lt; lia)
  | context[Z.ltb ?x ?y] =>
      replace (Z.ltb x y) with false in Hctx by (symmetry; apply Z.ltb_ge; lia)
  end;
  simpl in Hctx.

Ltac use_digit_safe :=
  match goal with
  | Hsafe_all : fruit_state_safe_z ?l,
    Hi : ?i < Zlength ?l |- _ =>
      let Hsafe := fresh "Hdigit_safe" in
      pose proof (fruit_digit_update_safe_from_safe l i Hsafe_all ltac:(lia)) as Hsafe;
      unfold fruit_digit_update_safe_z, is_digit_z in Hsafe;
      specialize (Hsafe ltac:(lia));
      destruct Hsafe as [? | [? ?]];
      unfold int_cur_mul10_bound_z in *;
      lia
  end.

Ltac solve_digit_safety :=
  fruit_pre;
  entailer!;
  try use_digit_safe;
  lia.

Ltac solve_output_safety :=
  fruit_pre;
  match goal with
  | idx : Z, l : list Z |- _ =>
      assert (idx = Zlength l) by lia;
      subst idx
  end;
  entailer!;
  match goal with
  | Hsafe_out : fruit_output_safe_z ?l ?total |- _ =>
      let Hout := fresh "Hout" in
      pose proof (fruit_output_safe_from_safe l total Hsafe_out) as Hout;
      unfold fruit_output_safe_z, fruit_output_z in Hout;
      first
        [ match goal with
          | |- context[total - ?a - ?b] =>
              let Hf1 := fresh "Hf1" in
              let Hf2 := fresh "Hf2" in
              assert (Hf1 : fruit_final_num1_z l = a) by
                (unfold fruit_final_num1_z, fruit_flush_num1_z,
                        fruit_commit_num1_z;
                 simplify_zbool; reflexivity);
              assert (Hf2 : fruit_final_num2_z l = b) by
                (unfold fruit_final_num2_z, fruit_flush_num2_z,
                        fruit_commit_num2_z, fruit_commit_num1_z;
                 simplify_zbool; reflexivity);
              rewrite Hf1, Hf2 in Hout
          end
        | match goal with
          | |- context[total - ?a] =>
              let Hf1 := fresh "Hf1" in
              assert (Hf1 : fruit_final_num1_z l = a) by
                (unfold fruit_final_num1_z, fruit_flush_num1_z,
                        fruit_commit_num1_z;
                 simplify_zbool; reflexivity);
              rewrite Hf1 in Hout
          end ];
      unfold int_min_z, int_max_z in Hout;
      lia
  end.

Ltac unfold_fruit_step :=
  match goal with
  | i : Z, l : list Z |- _ =>
      let Hstep := fresh "Hstep" in
      pose proof (fruit_prefix_step i l ltac:(lia)) as Hstep;
      unfold fruit_step_z, fruit_commit_num1_z, fruit_commit_num2_z,
             digit_value_z in Hstep;
      simplify_zbool_in Hstep;
      inversion Hstep;
      subst;
      clear Hstep
  end.

Ltac solve_fruit_step :=
  fruit_pre;
  unfold_fruit_step;
  entailer!;
  try use_digit_safe;
  lia.

Ltac solve_fruit_return :=
  fruit_pre;
  match goal with
  | idx : Z, l : list Z |- _ =>
      assert (idx = Zlength l) by lia;
      subst idx
  end;
  entailer!;
  apply problem_67_spec_z_intro; try assumption; try lia;
  unfold fruit_output_z;
  match goal with
  | |- ?total - ?a - ?b = ?total - fruit_final_num1_z ?l - fruit_final_num2_z ?l =>
      let Hf1 := fresh "Hf1" in
      let Hf2 := fresh "Hf2" in
      assert (Hf1 : fruit_final_num1_z l = a) by
        (unfold fruit_final_num1_z, fruit_flush_num1_z,
                fruit_commit_num1_z;
         simplify_zbool; reflexivity);
      assert (Hf2 : fruit_final_num2_z l = b) by
        (unfold fruit_final_num2_z, fruit_flush_num2_z,
                fruit_commit_num2_z, fruit_commit_num1_z;
         simplify_zbool; reflexivity);
      rewrite Hf1, Hf2;
      reflexivity
  end.

Lemma proof_of_fruit_distribution_safety_wit_12 : fruit_distribution_safety_wit_12.
Proof. unfold fruit_distribution_safety_wit_12; intros; solve_digit_safety. Qed. 

Lemma proof_of_fruit_distribution_safety_wit_14 : fruit_distribution_safety_wit_14.
Proof. unfold fruit_distribution_safety_wit_14; intros; solve_digit_safety. Qed. 

Lemma proof_of_fruit_distribution_safety_wit_74 : fruit_distribution_safety_wit_74.
Proof. unfold fruit_distribution_safety_wit_74; intros; solve_output_safety. Qed. 

Lemma proof_of_fruit_distribution_safety_wit_75 : fruit_distribution_safety_wit_75.
Proof. unfold fruit_distribution_safety_wit_75; intros; solve_output_safety. Qed. 

Lemma proof_of_fruit_distribution_safety_wit_76 : fruit_distribution_safety_wit_76.
Proof. unfold fruit_distribution_safety_wit_76; intros; solve_output_safety. Qed. 

Lemma proof_of_fruit_distribution_safety_wit_77 : fruit_distribution_safety_wit_77.
Proof. unfold fruit_distribution_safety_wit_77; intros; solve_output_safety. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_1 : fruit_distribution_entail_wit_1.
Proof.
  unfold fruit_distribution_entail_wit_1.
  intros.
  fruit_pre.
  unfold fruit_num1_prefix_z, fruit_num2_prefix_z, fruit_cur_prefix_z.
  simpl.
  entailer!.
Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_1 : fruit_distribution_entail_wit_2_1.
Proof. unfold fruit_distribution_entail_wit_2_1; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_2 : fruit_distribution_entail_wit_2_2.
Proof. unfold fruit_distribution_entail_wit_2_2; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_3 : fruit_distribution_entail_wit_2_3.
Proof. unfold fruit_distribution_entail_wit_2_3; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_4 : fruit_distribution_entail_wit_2_4.
Proof. unfold fruit_distribution_entail_wit_2_4; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_5 : fruit_distribution_entail_wit_2_5.
Proof. unfold fruit_distribution_entail_wit_2_5; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_6 : fruit_distribution_entail_wit_2_6.
Proof. unfold fruit_distribution_entail_wit_2_6; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_7 : fruit_distribution_entail_wit_2_7.
Proof. unfold fruit_distribution_entail_wit_2_7; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_8 : fruit_distribution_entail_wit_2_8.
Proof. unfold fruit_distribution_entail_wit_2_8; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_9 : fruit_distribution_entail_wit_2_9.
Proof. unfold fruit_distribution_entail_wit_2_9; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_entail_wit_2_10 : fruit_distribution_entail_wit_2_10.
Proof. unfold fruit_distribution_entail_wit_2_10; intros; solve_fruit_step. Qed. 

Lemma proof_of_fruit_distribution_return_wit_1 : fruit_distribution_return_wit_1.
Proof. unfold fruit_distribution_return_wit_1; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_2 : fruit_distribution_return_wit_2.
Proof. unfold fruit_distribution_return_wit_2; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_3 : fruit_distribution_return_wit_3.
Proof. unfold fruit_distribution_return_wit_3; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_4 : fruit_distribution_return_wit_4.
Proof. unfold fruit_distribution_return_wit_4; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_5 : fruit_distribution_return_wit_5.
Proof. unfold fruit_distribution_return_wit_5; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_6 : fruit_distribution_return_wit_6.
Proof. unfold fruit_distribution_return_wit_6; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_7 : fruit_distribution_return_wit_7.
Proof. unfold fruit_distribution_return_wit_7; intros; solve_fruit_return. Qed. 

Lemma proof_of_fruit_distribution_return_wit_8 : fruit_distribution_return_wit_8.
Proof. unfold fruit_distribution_return_wit_8; intros; solve_fruit_return. Qed. 
