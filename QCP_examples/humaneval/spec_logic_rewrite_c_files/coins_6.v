Load "../spec/6".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_6 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_6 c) (string_of_list_z rest)
  end.

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition problem_6_pre_z (s : list Z) : Prop :=
  problem_6_pre (string_of_list_z s).

Definition problem_6_spec_z (s output : list Z) : Prop :=
  problem_6_spec (string_of_list_z s) (map Z.to_nat output).

Definition valid_paren_depth_char_6 (c : Z) : Prop :=
  c = 32 \/ c = 40 \/ c = 41.

Definition valid_paren_depth_input_6 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_paren_depth_char_6 (Znth i s 0).

Definition depth_step_6
    (st : list Z * Z * Z) (c : Z) : list Z * Z * Z :=
  let '(levels, level, max_level) := st in
  if Z.eqb c 40 then
    let level' := level + 1 in
    (levels, level', Z.max max_level level')
  else if Z.eqb c 41 then
    let level' := level - 1 in
    if Z.eqb level' 0 then
      (levels ++ [max_level], 0, 0)
    else (levels, level', max_level)
  else (levels, level, max_level).

Fixpoint depth_state_nat_6 (n : nat) (s : list Z) : list Z * Z * Z :=
  match n with
  | O => ([], 0, 0)
  | S n' =>
      depth_step_6
        (depth_state_nat_6 n' s)
        (Znth (Z.of_nat n') s 0)
  end.

Definition depth_completed_6 (s : list Z) (i : Z) : list Z :=
  let '(levels, _, _) := depth_state_nat_6 (Z.to_nat i) s in levels.

Definition depth_level_6 (s : list Z) (i : Z) : Z :=
  let '(_, level, _) := depth_state_nat_6 (Z.to_nat i) s in level.

Definition depth_max_6 (s : list Z) (i : Z) : Z :=
  let '(_, _, max_level) := depth_state_nat_6 (Z.to_nat i) s in max_level.

Definition parse_output_6 (s : list Z) : list Z :=
  depth_completed_6 s (Zlength s).

Definition parse_state_6
    (s : list Z) (i level max_level : Z) (output : list Z) : Prop :=
  0 <= i <= string_length s /\
  output = depth_completed_6 s i /\
  level = depth_level_6 s i /\
  max_level = depth_max_6 s i /\
  0 <= level /\
  0 <= max_level /\
  Zlength output <= i.

Definition parse_safe_input_6 (s : list Z) : Prop :=
  (forall i,
    0 <= i < Zlength s ->
    Znth i s 0 = 41 ->
    0 < depth_level_6 s i) /\
  depth_level_6 s (Zlength s) = 0 /\
  depth_max_6 s (Zlength s) = 0 /\
  problem_6_spec_z s (parse_output_6 s).

Lemma depth_state_nat_6_step : forall i s,
  0 <= i ->
  depth_state_nat_6 (Z.to_nat (i + 1)) s =
  depth_step_6 (depth_state_nat_6 (Z.to_nat i) s) (Znth i s 0).
Proof.
  intros i s Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma parse_state_6_initial : forall s,
  parse_state_6 s 0 0 0 [].
Proof.
  intros s.
  unfold parse_state_6, depth_completed_6, depth_level_6, depth_max_6, string_length.
  simpl.
  repeat split; try reflexivity; try rewrite Zlength_nil; try lia; apply Zlength_nonneg.
Qed.

Lemma parse_state_6_step_open : forall s i level max_level output,
  parse_state_6 s i level max_level output ->
  Znth i s 0 = 40 ->
  i < Zlength s ->
  parse_state_6 s (i + 1) (level + 1) (Z.max max_level (level + 1)) output.
Proof.
  intros s i level max_level output Hstate Hch Hi.
  unfold parse_state_6 in *.
  destruct Hstate as [Hbounds [Hout [Hlev [Hmax [Hlevnon [Hmaxnon Hlen]]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold depth_completed_6 in *.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst output level max_level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch, Z.eqb_refl.
    reflexivity.
  - unfold depth_level_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    subst level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch, Z.eqb_refl.
    reflexivity.
  - unfold depth_max_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst level max_level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch, Z.eqb_refl.
    reflexivity.
Qed.

Lemma parse_state_6_step_close_finish : forall s i max_level output,
  parse_state_6 s i 1 max_level output ->
  Znth i s 0 = 41 ->
  i < Zlength s ->
  parse_state_6 s (i + 1) 0 0 (output ++ [max_level]).
Proof.
  intros s i max_level output Hstate Hch Hi.
  unfold parse_state_6 in *.
  destruct Hstate as [Hbounds [Hout [Hlev [Hmax [Hlevnon [Hmaxnon Hlen]]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold depth_completed_6 in *.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    simpl in *.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst output max_level.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold depth_level_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold depth_max_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma parse_state_6_step_close_continue : forall s i level max_level output,
  parse_state_6 s i level max_level output ->
  parse_safe_input_6 s ->
  level - 1 <> 0 ->
  Znth i s 0 = 41 ->
  i < Zlength s ->
  parse_state_6 s (i + 1) (level - 1) max_level output.
Proof.
  intros s i level max_level output Hstate Hsafe Hnot0 Hch Hi.
  unfold parse_state_6 in *.
  destruct Hstate as [Hbounds [Hout [Hlev [Hmax [Hlevnon [Hmaxnon Hlen]]]]]].
  assert (Hpos : 0 < level).
  {
    destruct Hsafe as [Hsafe _].
    assert (0 <= i < Zlength s) as Hi_bounds by (unfold string_length in *; lia).
    specialize (Hsafe i Hi_bounds Hch).
    lia.
  }
  repeat split; try (unfold string_length in *; lia).
  - unfold depth_completed_6 in *.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    simpl in *.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst output level max_level.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    destruct (Z.eqb_spec (level0 - 1) 0); [lia | reflexivity].
  - unfold depth_level_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    subst level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    destruct (Z.eqb_spec (level0 - 1) 0); [lia | reflexivity].
  - unfold depth_max_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst level max_level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    replace (Z.eqb 41 40) with false by reflexivity.
    destruct (Z.eqb_spec (level0 - 1) 0); [lia |].
    reflexivity.
Qed.

Lemma parse_state_6_step_space : forall s i level max_level output,
  parse_state_6 s i level max_level output ->
  Znth i s 0 = 32 ->
  i < Zlength s ->
  parse_state_6 s (i + 1) level max_level output.
Proof.
  intros s i level max_level output Hstate Hch Hi.
  unfold parse_state_6 in *.
  destruct Hstate as [Hbounds [Hout [Hlev [Hmax [Hlevnon [Hmaxnon Hlen]]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold depth_completed_6 in *.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    simpl in *.
    subst output level max_level.
    unfold depth_step_6.
    rewrite Hch.
    reflexivity.
  - unfold depth_level_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_level_6 in Hlev; rewrite Hst in Hlev.
    subst level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    reflexivity.
  - unfold depth_max_6.
    rewrite depth_state_nat_6_step by lia.
    destruct (depth_state_nat_6 (Z.to_nat i) s) as [[levels0 level0] max0] eqn:Hst.
    unfold depth_max_6 in Hmax; rewrite Hst in Hmax.
    subst max_level.
    simpl in *.
    unfold depth_step_6.
    rewrite Hch.
    reflexivity.
Qed.

Lemma parse_state_6_final_spec : forall s output,
  parse_state_6 s (Zlength s) 0 0 output ->
  parse_safe_input_6 s ->
  problem_6_spec_z s output.
Proof.
  intros s output Hstate Hsafe.
  unfold parse_state_6 in Hstate.
  destruct Hstate as [_ [Hout _]].
  destruct Hsafe as [_ [_ [_ Hspec]]].
  subst output.
  exact Hspec.
Qed.

Lemma parse_state_6_final_facts : forall s i level max_level output,
  parse_state_6 s i level max_level output ->
  parse_safe_input_6 s ->
  i >= string_length s ->
  level = 0 /\
  max_level = 0 /\
  output = parse_output_6 s /\
  problem_6_spec_z s output.
Proof.
  intros s i level max_level output Hstate Hsafe Hend.
  unfold parse_state_6 in Hstate.
  destruct Hstate as [Hbounds [Hout [Hlev [Hmax _]]]].
  unfold string_length in *.
  assert (Hi : i = Zlength s) by lia.
  subst i.
  destruct Hsafe as [_ [Hlev_end [Hmax_end Hspec]]].
  unfold parse_output_6.
  subst output level max_level.
  repeat split; auto.
Qed.
