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
From SimpleC.EE Require Import C_124_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_124.
Local Open Scope sac.

Ltac date_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac solve_date_simple :=
  date_pre;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 0 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 0 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit_z in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 1 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 1 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit_z in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 3 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 3 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit_z in *
  end;
  try match goal with Hpre : date_prefix_valid ?i ?l |- context[Znth 4 ?l 0] =>
    pose proof (date_prefix_valid_digit_at i l 4 Hpre ltac:(lia) ltac:(lia) ltac:(lia)); unfold is_digit_z in *
  end;
  entailer!; try lia.

Ltac solve_date_false :=
  date_pre; entailer!;
  eapply problem_124_spec_z_false; eauto;
  intro;
  match goal with Hvalid : valid_date_z ?l |- _ =>
  first [
    pose proof (valid_date_z_len _ Hvalid); lia
  | match goal with
  | Hbad : Znth ?i ?l 0 <> 45, Hi : ?i = 2 |- _ =>
      pose proof (valid_date_z_sep_at l i Hvalid (or_introl eq_refl)); lia
  | Hbad : Znth ?i ?l 0 <> 45, Hi : ?i = 5 |- _ =>
      pose proof (valid_date_z_sep_at l i Hvalid (or_intror eq_refl)); lia
    end
  | match goal with
  | Hbad : Znth ?i ?l 0 < 48 |- _ =>
      pose proof (valid_date_z_digit_at l i Hvalid ltac:(lia) ltac:(lia) ltac:(lia));
      unfold is_digit_z in *; lia
  | Hbad : Znth ?i ?l 0 > 57 |- _ =>
      pose proof (valid_date_z_digit_at l i Hvalid ltac:(lia) ltac:(lia) ltac:(lia));
      unfold is_digit_z in *; lia
    end
  | pose proof (valid_date_z_month _ Hvalid) as Hmonth_valid;
    pose proof (valid_date_z_day _ Hvalid) as Hday_valid;
    pose proof (days_in_month_z_le_31 (month_z l)) as Hdays_le;
    unfold month_z, day_z in *;
    repeat rewrite app_Znth1 in * by lia;
    try match goal with
    | Hm : ?m = 4, Hday_valid : context[days_in_month_z ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 6, Hday_valid : context[days_in_month_z ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 9, Hday_valid : context[days_in_month_z ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 11, Hday_valid : context[days_in_month_z ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    try match goal with
    | Hm : ?m = 2, Hday_valid : context[days_in_month_z ?m] |- _ =>
        rewrite Hm in Hday_valid; simpl in Hday_valid
    end;
    lia
  ]
  end.

Ltac solve_date_true :=
  date_pre; entailer!;
  match goal with
  | Hge : ?i >= 10, Hle : ?i <= 10 |- _ =>
      assert (i = 10) by lia; subst i
  end;
  eapply problem_124_spec_z_true; eauto;
  apply valid_date_z_intro_from_checks;
  [ apply date_prefix_valid_10_format; [lia | assumption]
  | unfold month_z; lia
  | unfold day_z; lia
  | unfold month_z, day_z; intro;
    match goal with Hbad : _ /\ _ |- _ => destruct Hbad as [? ?]; lia end
  | unfold month_z, day_z; intro;
    match goal with Hbad : _ /\ _ |- _ => destruct Hbad as [? ?]; lia end
  ].

Ltac solve_date_bad_day_month :=
  date_pre; entailer!;
  eapply problem_124_spec_z_false; eauto;
  intro;
  match goal with Hvalid : valid_date_z _ |- _ =>
    let Hday := fresh "Hday_valid" in
    pose proof (valid_date_z_day _ Hvalid) as Hday;
    unfold month_z, day_z in Hday;
    try match goal with H : ?d = 30 |- _ => rewrite H in Hday end;
    try match goal with H : ?d = 31 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 2 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 4 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 6 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 9 |- _ => rewrite H in Hday end;
    try match goal with H : ?m = 11 |- _ => rewrite H in Hday end;
    unfold days_in_month_z in Hday;
    simpl in Hday;
    lia
  end.

Ltac solve_date_bad_sep :=
  date_pre; entailer!;
  eapply problem_124_spec_z_false; eauto;
  intro;
  match goal with Hvalid : valid_date_z ?l |- _ =>
    match goal with
    | Hbad : Znth ?i ?l' 0 <> 45, Hi : ?i = 2 |- _ =>
        unify l l';
        pose proof (valid_date_z_sep_at l i Hvalid (or_introl eq_refl)); lia
    | Hbad : Znth ?i ?l' 0 <> 45, Hi : ?i = 5 |- _ =>
        unify l l';
        pose proof (valid_date_z_sep_at l i Hvalid (or_intror eq_refl)); lia
    end
  end.

Lemma proof_of_valid_date_safety_wit_18 : valid_date_safety_wit_18.
Proof. unfold valid_date_safety_wit_18; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_19 : valid_date_safety_wit_19.
Proof. unfold valid_date_safety_wit_19; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_20 : valid_date_safety_wit_20.
Proof. unfold valid_date_safety_wit_20; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_21 : valid_date_safety_wit_21.
Proof. unfold valid_date_safety_wit_21; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_27 : valid_date_safety_wit_27.
Proof. unfold valid_date_safety_wit_27; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_28 : valid_date_safety_wit_28.
Proof. unfold valid_date_safety_wit_28; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_29 : valid_date_safety_wit_29.
Proof. unfold valid_date_safety_wit_29; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_safety_wit_30 : valid_date_safety_wit_30.
Proof. unfold valid_date_safety_wit_30; intros; solve_date_simple. Qed.

Lemma proof_of_valid_date_entail_wit_1 : valid_date_entail_wit_1.
Proof.
  unfold valid_date_entail_wit_1.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_0.
Qed.

Lemma proof_of_valid_date_entail_wit_2_1 : valid_date_entail_wit_2_1.
Proof.
  unfold valid_date_entail_wit_2_1.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_sep; auto; lia.
Qed.

Lemma proof_of_valid_date_entail_wit_2_2 : valid_date_entail_wit_2_2.
Proof.
  unfold valid_date_entail_wit_2_2.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_sep; auto; lia.
Qed.

Lemma proof_of_valid_date_entail_wit_2_3 : valid_date_entail_wit_2_3.
Proof.
  unfold valid_date_entail_wit_2_3.
  intros.
  date_pre.
  entailer!.
  apply date_prefix_valid_step_digit; auto; unfold is_digit_z; lia.
Qed.

Lemma proof_of_valid_date_return_wit_1 : valid_date_return_wit_1.
Proof. unfold valid_date_return_wit_1; intros; solve_date_true. Qed.

Lemma proof_of_valid_date_return_wit_2 : valid_date_return_wit_2.
Proof. unfold valid_date_return_wit_2; intros; solve_date_true. Qed.

Lemma proof_of_valid_date_return_wit_3 : valid_date_return_wit_3.
Proof. unfold valid_date_return_wit_3; intros; solve_date_true. Qed.

Lemma proof_of_valid_date_return_wit_4 : valid_date_return_wit_4.
Proof. unfold valid_date_return_wit_4; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_5 : valid_date_return_wit_5.
Proof. unfold valid_date_return_wit_5; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_6 : valid_date_return_wit_6.
Proof. unfold valid_date_return_wit_6; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_7 : valid_date_return_wit_7.
Proof. unfold valid_date_return_wit_7; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_8 : valid_date_return_wit_8.
Proof. unfold valid_date_return_wit_8; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_9 : valid_date_return_wit_9.
Proof. unfold valid_date_return_wit_9; intros; solve_date_bad_day_month. Qed.

Lemma proof_of_valid_date_return_wit_10 : valid_date_return_wit_10.
Proof. unfold valid_date_return_wit_10; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_11 : valid_date_return_wit_11.
Proof. unfold valid_date_return_wit_11; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_12 : valid_date_return_wit_12.
Proof. unfold valid_date_return_wit_12; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_13 : valid_date_return_wit_13.
Proof. unfold valid_date_return_wit_13; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_14 : valid_date_return_wit_14.
Proof. unfold valid_date_return_wit_14; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_15 : valid_date_return_wit_15.
Proof. unfold valid_date_return_wit_15; intros; solve_date_false. Qed.

Lemma proof_of_valid_date_return_wit_16 : valid_date_return_wit_16.
Proof.
  unfold valid_date_return_wit_16.
  intros.
  date_pre; entailer!.
  eapply problem_124_spec_z_false; eauto.
  intro Hvalid.
  pose proof (valid_date_z_sep_at l i Hvalid (or_intror H0)).
  lia.
Qed.

Lemma proof_of_valid_date_return_wit_17 : valid_date_return_wit_17.
Proof.
  unfold valid_date_return_wit_17.
  intros.
  date_pre; entailer!.
  eapply problem_124_spec_z_false; eauto.
  intro Hvalid.
  pose proof (valid_date_z_sep_at l i Hvalid (or_introl H0)).
  lia.
Qed.

Lemma proof_of_valid_date_return_wit_18 : valid_date_return_wit_18.
Proof. unfold valid_date_return_wit_18; intros; solve_date_false. Qed.
