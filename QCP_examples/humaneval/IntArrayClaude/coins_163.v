Load "../spec/163".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition digit_candidates : list Z := [2; 4; 6; 8].

Definition generate_prefix_list (lo i : Z) : list Z :=
  filter (fun d => andb (lo <=? d) (d <? i)) digit_candidates.

Definition generate_list (lo hi : Z) : list Z :=
  generate_prefix_list lo (hi + 1).

Definition generate_bounds (a0 b0 a b : Z) : Prop :=
  a = Z.min a0 b0 /\ b = Z.max a0 b0.

Definition z_min (a b : Z) : Z := Z.min a b.

Definition z_max (a b : Z) : Z := Z.max a b.

Definition generate_prefix (lo i hi : Z) (output : list Z) : Prop :=
  lo <= i <= hi + 1 /\
  output = generate_prefix_list lo i.

Lemma filter_length_le_nat : forall {A: Type} (f: A -> bool) (l: list A),
  (length (filter f l) <= length l)%nat.
Proof.
  intros A f l.
  induction l as [| x xs IH]; simpl; [lia|].
  destruct (f x); simpl; lia.
Qed.

Lemma generate_prefix_length_le_4 : forall lo i hi output,
  generate_prefix lo i hi output ->
  Zlength output <= 4.
Proof.
  intros lo i hi output [_ Hout].
  rewrite Hout.
  unfold generate_prefix_list, digit_candidates.
  simpl.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  end;
  simpl;
  repeat (rewrite Zlength_cons || rewrite Zlength_nil);
  lia.
Qed.

Definition problem_163_pre_z (a b : Z) : Prop :=
  problem_163_pre (Z.to_nat a) (Z.to_nat b).

Definition problem_163_spec_z (a b : Z) (output : list Z) : Prop :=
  problem_163_spec (Z.to_nat a) (Z.to_nat b) (map Z.to_nat output).

Lemma generate_prefix_list_in_163 : forall lo hi z,
  In z (generate_list lo hi) <->
  In z digit_candidates /\ lo <= z <= hi.
Proof.
  intros lo hi z.
  unfold generate_list, generate_prefix_list, digit_candidates.
  repeat rewrite filter_In.
  simpl.
  split.
  - intros [Hin Hfilter].
    apply andb_prop in Hfilter as [Hlo Hhi].
    apply Z.leb_le in Hlo.
    apply Z.ltb_lt in Hhi.
    split; [exact Hin|lia].
  - intros [Hin [Hlo Hhi]].
    split; [exact Hin|].
    apply andb_true_intro.
    split.
    + apply Z.leb_le. lia.
    + apply Z.ltb_lt. lia.
Qed.

Lemma even_digit_nat_cases_163 : forall d,
  (1 <= d)%nat ->
  (d < 10)%nat ->
  Nat.Even d ->
  d = 2%nat \/ d = 4%nat \/ d = 6%nat \/ d = 8%nat.
Proof.
  intros d Hd_pos Hd_lt Heven.
  destruct Heven as [k Hk].
  lia.
Qed.

Lemma digit_candidates_sorted_nat_163 :
  Sorted le (map Z.to_nat digit_candidates).
Proof.
  unfold digit_candidates.
  simpl.
  repeat constructor; simpl; lia.
Qed.

Lemma digit_candidates_nodup_nat_163 :
  NoDup (map Z.to_nat digit_candidates).
Proof.
  unfold digit_candidates.
  simpl.
  repeat constructor; simpl; lia.
Qed.

Lemma nat_bounds_to_z_digit_163 : forall a b z,
  0 < a ->
  0 < b ->
  0 <= z ->
  (Nat.min (Z.to_nat a) (Z.to_nat b) <= Z.to_nat z)%nat ->
  (Z.to_nat z <= Nat.max (Z.to_nat a) (Z.to_nat b))%nat ->
  Z.min a b <= z <= Z.max a b.
Proof.
  intros a b z Ha Hb Hz Hlo Hhi.
  rewrite <- Z2Nat.inj_min in Hlo.
  rewrite <- Z2Nat.inj_max in Hhi.
  split.
  - apply (proj2 (Z2Nat.inj_le (Z.min a b) z ltac:(lia) Hz)).
    exact Hlo.
  - apply (proj2 (Z2Nat.inj_le z (Z.max a b) Hz ltac:(lia))).
    exact Hhi.
Qed.

Lemma generate_list_original_spec_163 : forall a b,
  0 < a ->
  0 < b ->
  problem_163_spec_z a b (generate_list (Z.min a b) (Z.max a b)).
Proof.
  intros a b Ha Hb.
  unfold problem_163_spec_z, problem_163_spec.
  split.
  - intros d.
    split.
    + intros Hin.
      apply in_map_iff in Hin.
      destruct Hin as [z [Hd Hz_in]].
      apply generate_prefix_list_in_163 in Hz_in.
      destruct Hz_in as [Hz_candidate [Hz_lo Hz_hi]].
      assert (Hz_nonneg : 0 <= z).
      { destruct Hz_candidate as [Hz | [Hz | [Hz | [Hz | []]]]]; subst z; lia. }
      assert (Hlo_nat : (Nat.min (Z.to_nat a) (Z.to_nat b) <= Z.to_nat z)%nat).
      {
        rewrite <- Z2Nat.inj_min.
        apply (proj1 (Z2Nat.inj_le (Z.min a b) z ltac:(lia) Hz_nonneg)); lia.
      }
      assert (Hhi_nat : (Z.to_nat z <= Nat.max (Z.to_nat a) (Z.to_nat b))%nat).
      {
        rewrite <- Z2Nat.inj_max.
        apply (proj1 (Z2Nat.inj_le z (Z.max a b) Hz_nonneg ltac:(lia))); lia.
      }
      subst d.
      destruct Hz_candidate as [Hz | [Hz | [Hz | [Hz | []]]]]; subst z;
      repeat split; simpl; try exact Hlo_nat; try exact Hhi_nat; try lia.
      * unfold Nat.Even. exists 1%nat. lia.
      * unfold Nat.Even. exists 2%nat. lia.
      * unfold Nat.Even. exists 3%nat. lia.
      * unfold Nat.Even. exists 4%nat. lia.
    + intros [Hd_lo [Hd_hi [Hd_lt Heven]]].
      assert (Hd_pos : (1 <= d)%nat).
      {
        assert (Hmin_pos : (1 <= Z.to_nat (Z.min a b))%nat).
        {
          apply (proj1 (Z2Nat.inj_le 1 (Z.min a b) ltac:(lia) ltac:(lia))); lia.
        }
        rewrite Z2Nat.inj_min in Hmin_pos.
        lia.
      }
      pose proof (even_digit_nat_cases_163 d Hd_pos Hd_lt Heven) as Hcases.
      destruct Hcases as [Hd | [Hd | [Hd | Hd]]]; subst d; apply in_map_iff.
      * exists 2. split; [reflexivity|].
        apply generate_prefix_list_in_163.
        split; [simpl; tauto|].
        apply nat_bounds_to_z_digit_163; simpl; try lia; assumption.
      * exists 4. split; [reflexivity|].
        apply generate_prefix_list_in_163.
        split; [simpl; tauto|].
        apply nat_bounds_to_z_digit_163; simpl; try lia; assumption.
      * exists 6. split; [reflexivity|].
        apply generate_prefix_list_in_163.
        split; [simpl; tauto|].
        apply nat_bounds_to_z_digit_163; simpl; try lia; assumption.
      * exists 8. split; [reflexivity|].
        apply generate_prefix_list_in_163.
        split; [simpl; tauto|].
        apply nat_bounds_to_z_digit_163; simpl; try lia; assumption.
  - split.
    + unfold generate_list, generate_prefix_list, digit_candidates.
      simpl.
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; simpl
      | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
      end;
      repeat constructor; simpl; lia.
    + unfold generate_list, generate_prefix_list, digit_candidates.
      simpl.
      repeat match goal with
      | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; simpl
      | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; simpl
      end;
      repeat constructor; simpl; lia.
Qed.

Lemma generate_prefix_init : forall lo hi,
  0 < lo ->
  lo <= hi + 1 ->
  generate_prefix lo lo hi nil.
Proof.
  intros.
  unfold generate_prefix, generate_prefix_list, digit_candidates.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end; simpl; try reflexivity; lia.
Qed.

Lemma positive_even_digit_cases : forall i,
  0 < i ->
  i < 10 ->
  Z.even i = true ->
  i = 2 \/ i = 4 \/ i = 6 \/ i = 8.
Proof.
  intros i Hpos Hlt Heven.
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  assert (1 <= k <= 4) by lia.
  lia.
Qed.

Lemma generate_prefix_take : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  i < 10 ->
  Z.even i = true ->
  generate_prefix lo (i + 1) hi (output ++ [i]).
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hlt Heven.
  subst output.
  pose proof (positive_even_digit_cases i ltac:(lia) Hlt Heven) as Hcases.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  destruct Hcases as [-> | [-> | [-> | ->]]];
    simpl;
    repeat match goal with
    | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
    | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
    end;
    simpl; try lia; reflexivity.
Qed.

Lemma generate_prefix_skip : forall lo i hi output,
  0 < lo ->
  generate_prefix lo i hi output ->
  lo <= i <= hi ->
  ~ (i < 10 /\ Z.even i = true) ->
  generate_prefix lo (i + 1) hi output.
Proof.
  intros lo i hi output Hlo [Hbounds Hout] Hi Hskip.
  subst output.
  unfold generate_prefix, generate_prefix_list, digit_candidates in *.
  split; [lia|].
  simpl.
  repeat match goal with
  | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) eqn:?; try apply Z.leb_le in Heqb; try apply Z.leb_gt in Heqb
  | |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) eqn:?; try apply Z.ltb_lt in Heqb; try apply Z.ltb_ge in Heqb
  end;
  simpl; try reflexivity;
  exfalso; apply Hskip; split; try lia;
  assert (i = 2 \/ i = 4 \/ i = 6 \/ i = 8) by lia;
  destruct H as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma generate_prefix_full_spec : forall a0 b0 lo hi output,
  0 < a0 ->
  0 < b0 ->
  generate_bounds a0 b0 lo hi ->
  generate_prefix lo (hi + 1) hi output ->
  problem_163_spec_z a0 b0 output.
Proof.
  intros a0 b0 lo hi output Ha0 Hb0 [Hlo Hhi] [_ Hout].
  subst lo hi output.
  apply generate_list_original_spec_163; assumption.
Qed.

Lemma mod2_zero_even_true : forall i,
  i mod 2 = 0 ->
  Z.even i = true.
Proof.
  intros i Hmod.
  rewrite Zeven_mod.
  apply Zeq_is_eq_bool.
  exact Hmod.
Qed.

Lemma mod2_nonzero_even_false : forall i,
  i mod 2 <> 0 ->
  Z.even i <> true.
Proof.
  intros i Hmod Heven.
  apply Hmod.
  rewrite Zmod_even.
  rewrite Heven.
  reflexivity.
Qed.
