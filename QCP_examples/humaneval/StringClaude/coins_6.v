Load "../spec/6".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_6_pre_z (input : list Z) : Prop :=
  problem_6_pre (string_of_list_z input).

Definition problem_6_spec_z (input output : list Z) : Prop :=
  problem_6_spec (string_of_list_z input) (map Z.to_nat output).

Definition paren_zmax (a b : Z) : Z :=
  if Z.leb a b then b else a.

Definition paren_final_output_z (out : list Z) (in_group max_level : Z) : list Z :=
  if Z.eqb in_group 0 then out else out ++ [max_level].

Definition paren_step_output_z (out : list Z) (in_group max_level ch : Z) : list Z :=
  if Z.eqb ch 32 then paren_final_output_z out in_group max_level else out.

Definition paren_step_in_group_z (in_group ch : Z) : Z :=
  if Z.eqb ch 32 then 0 else 1.

Definition paren_step_level_z (in_group level ch : Z) : Z :=
  if Z.eqb ch 32 then
    if Z.eqb in_group 0 then level else 0
  else if Z.eqb ch 40 then level + 1
  else if Z.ltb 0 level then level - 1 else 0.

Definition paren_step_max_z (in_group level max_level ch : Z) : Z :=
  if Z.eqb ch 32 then
    if Z.eqb in_group 0 then max_level else 0
  else if Z.eqb ch 40 then paren_zmax max_level (level + 1)
  else max_level.

Fixpoint paren_scan_aux
  (chars out : list Z) (in_group level max_level : Z) : list Z * Z * Z * Z :=
  match chars with
  | [] => (out, in_group, level, max_level)
  | ch :: rest =>
      paren_scan_aux rest
        (paren_step_output_z out in_group max_level ch)
        (paren_step_in_group_z in_group ch)
        (paren_step_level_z in_group level ch)
        (paren_step_max_z in_group level max_level ch)
  end.

Definition paren_state_out (st : list Z * Z * Z * Z) : list Z :=
  match st with (out, _, _, _) => out end.

Definition paren_state_in_group (st : list Z * Z * Z * Z) : Z :=
  match st with (_, in_group, _, _) => in_group end.

Definition paren_state_level (st : list Z * Z * Z * Z) : Z :=
  match st with (_, _, level, _) => level end.

Definition paren_state_max (st : list Z * Z * Z * Z) : Z :=
  match st with (_, _, _, max_level) => max_level end.

Definition paren_prefix_state_z (i : Z) (input : list Z) : list Z * Z * Z * Z :=
  paren_scan_aux (sublist 0 i input) [] 0 0 0.

Definition paren_prefix_output_z (i : Z) (input : list Z) : list Z :=
  paren_state_out (paren_prefix_state_z i input).

Definition paren_prefix_in_group_z (i : Z) (input : list Z) : Z :=
  paren_state_in_group (paren_prefix_state_z i input).

Definition paren_prefix_level_z (i : Z) (input : list Z) : Z :=
  paren_state_level (paren_prefix_state_z i input).

Definition paren_prefix_max_z (i : Z) (input : list Z) : Z :=
  paren_state_max (paren_prefix_state_z i input).

Definition paren_output_z (input : list Z) : list Z :=
  let st := paren_scan_aux input [] 0 0 0 in
  paren_final_output_z (paren_state_out st) (paren_state_in_group st) (paren_state_max st).

Lemma paren_scan_aux_step : forall prefix ch out in_group level max_level,
  paren_scan_aux (prefix ++ [ch]) out in_group level max_level =
  let st := paren_scan_aux prefix out in_group level max_level in
  paren_scan_aux [ch]
    (paren_state_out st)
    (paren_state_in_group st)
    (paren_state_level st)
    (paren_state_max st).
Proof.
  induction prefix as [| h t IH]; intros ch out in_group level max_level; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma paren_scan_aux_one : forall ch out in_group level max_level,
  paren_scan_aux [ch] out in_group level max_level =
  (paren_step_output_z out in_group max_level ch,
   paren_step_in_group_z in_group ch,
   paren_step_level_z in_group level ch,
   paren_step_max_z in_group level max_level ch).
Proof.
  reflexivity.
Qed.

Lemma paren_prefix_step : forall input i,
  0 <= i < Zlength input ->
  paren_prefix_output_z (i + 1) input =
    paren_step_output_z
      (paren_prefix_output_z i input)
      (paren_prefix_in_group_z i input)
      (paren_prefix_max_z i input)
      (Znth i input 0) /\
  paren_prefix_in_group_z (i + 1) input =
    paren_step_in_group_z
      (paren_prefix_in_group_z i input)
      (Znth i input 0) /\
  paren_prefix_level_z (i + 1) input =
    paren_step_level_z
      (paren_prefix_in_group_z i input)
      (paren_prefix_level_z i input)
      (Znth i input 0) /\
  paren_prefix_max_z (i + 1) input =
    paren_step_max_z
      (paren_prefix_in_group_z i input)
      (paren_prefix_level_z i input)
      (paren_prefix_max_z i input)
      (Znth i input 0).
Proof.
  intros input i Hi.
  unfold paren_prefix_output_z, paren_prefix_in_group_z,
    paren_prefix_level_z, paren_prefix_max_z, paren_prefix_state_z.
  assert (sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i input);
      [| lia | rewrite <- Zlength_correct; lia].
    rewrite (sublist_single i input 0) by (rewrite <- Zlength_correct; lia).
    reflexivity.
  }
  rewrite Hsub.
  rewrite paren_scan_aux_step.
  rewrite paren_scan_aux_one.
  repeat split; reflexivity.
Qed.

Lemma paren_prefix_step_app : forall input i,
  0 <= i < Zlength input ->
  paren_prefix_output_z (i + 1) input =
    paren_step_output_z
      (paren_prefix_output_z i input)
      (paren_prefix_in_group_z i input)
      (paren_prefix_max_z i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_in_group_z (i + 1) input =
    paren_step_in_group_z
      (paren_prefix_in_group_z i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_level_z (i + 1) input =
    paren_step_level_z
      (paren_prefix_in_group_z i input)
      (paren_prefix_level_z i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  paren_prefix_max_z (i + 1) input =
    paren_step_max_z
      (paren_prefix_in_group_z i input)
      (paren_prefix_level_z i input)
      (paren_prefix_max_z i input)
      (Znth i (app input (cons 0 nil)) 0).
Proof.
  intros input i Hi.
  pose proof (paren_prefix_step input i Hi) as Hstep.
  replace (Znth i (app input (cons 0 nil)) 0) with (Znth i input 0).
  - exact Hstep.
  - rewrite app_Znth1; lia.
Qed.

Lemma paren_prefix_full_final : forall input len,
  len = Zlength input ->
  paren_final_output_z
    (paren_prefix_output_z len input)
    (paren_prefix_in_group_z len input)
    (paren_prefix_max_z len input) =
  paren_output_z input.
Proof.
  intros input len Hlen.
  unfold paren_prefix_output_z, paren_prefix_in_group_z,
    paren_prefix_max_z, paren_prefix_state_z, paren_output_z.
  rewrite (sublist_self input len Hlen).
  destruct (paren_scan_aux input [] 0 0 0) as [[[out in_group] level] max_level].
  reflexivity.
Qed.

Lemma paren_step_in_group_range : forall in_group ch,
  0 <= paren_step_in_group_z in_group ch <= 1.
Proof.
  intros. unfold paren_step_in_group_z.
  destruct (Z.eqb ch 32); lia.
Qed.

Lemma paren_zmax_bounds : forall a b i,
  0 <= a <= i ->
  0 <= b <= i ->
  0 <= paren_zmax a b <= i.
Proof.
  intros a b i Ha Hb.
  unfold paren_zmax.
  destruct (Z.leb a b); lia.
Qed.

Lemma paren_step_max_bounds : forall in_group level max_level ch i,
  0 <= in_group <= 1 ->
  -i <= level <= i ->
  0 <= max_level <= i ->
  ch = 32 \/ ch = 40 \/ ch = 41 ->
  0 <= paren_step_max_z in_group level max_level ch <= i + 1.
Proof.
  intros in_group level max_level ch i Hin Hlevel Hmax Hch.
  unfold paren_step_max_z.
  destruct Hch as [-> | [-> | ->]]; simpl.
  - destruct (Z.eqb in_group 0); lia.
  - replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    unfold paren_zmax.
    destruct (Z.leb_spec max_level (level + 1)); lia.
  - replace (Z.eqb 41 32) with false by reflexivity.
    replace (Z.eqb 41 40) with false by reflexivity.
    lia.
Qed.

Lemma paren_step_level_bounds : forall in_group level ch i,
  0 <= in_group <= 1 ->
  -i <= level <= i ->
  ch = 32 \/ ch = 40 \/ ch = 41 ->
  -(i + 1) <= paren_step_level_z in_group level ch <= i + 1.
Proof.
  intros in_group level ch i Hin Hlevel Hch.
  unfold paren_step_level_z.
  destruct Hch as [-> | [-> | ->]]; simpl.
  - destruct (Z.eqb in_group 0); lia.
  - replace (Z.eqb 40 32) with false by reflexivity.
    replace (Z.eqb 40 40) with true by reflexivity.
    lia.
  - replace (Z.eqb 41 32) with false by reflexivity.
    replace (Z.eqb 41 40) with false by reflexivity.
    lia.
Qed.

Lemma ascii_of_z_eq_32 : forall z,
  0 <= z < 256 ->
  (ascii_of_z z = " "%char <-> z = 32).
Proof.
  intros z Hz.
  split; intros H.
  - apply f_equal with (f := nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by exact Hz.
    change (nat_of_ascii " "%char) with 32%nat in H.
    lia.
  - subst. reflexivity.
Qed.

Lemma ascii_of_z_eq_40 : forall z,
  0 <= z < 256 ->
  (ascii_of_z z = "("%char <-> z = 40).
Proof.
  intros z Hz.
  split; intros H.
  - apply f_equal with (f := nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by exact Hz.
    change (nat_of_ascii "("%char) with 40%nat in H.
    lia.
  - subst. reflexivity.
Qed.

Lemma ascii_of_z_eq_41 : forall z,
  0 <= z < 256 ->
  (ascii_of_z z = ")"%char <-> z = 41).
Proof.
  intros z Hz.
  split; intros H.
  - apply f_equal with (f := nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of_z in H by exact Hz.
    change (nat_of_ascii ")"%char) with 41%nat in H.
    lia.
  - subst. reflexivity.
Qed.

Fixpoint chars_are_paren_space_z (l : list Z) : Prop :=
  match l with
  | [] => True
  | x :: xs => (x = 40 \/ x = 41 \/ x = 32) /\ chars_are_paren_space_z xs
  end.

Lemma ForallChars_paren_space_z : forall l,
  ascii_range_z l ->
  ForallChars is_paren_or_space (string_of_list_z l) ->
  chars_are_paren_space_z l.
Proof.
  induction l as [| x xs IH]; intros Hrange Hforall_all; simpl; auto.
  simpl in Hforall_all.
  destruct Hforall_all as [Hchar Hforall].
  assert (Hxrange : 0 <= x < 256).
  { specialize (Hrange 0). rewrite Zlength_cons in Hrange.
    change (Znth 0 (x :: xs) 0) with x in Hrange.
    apply Hrange. pose proof (Zlength_nonneg xs); lia. }
  split.
  - destruct Hchar as [Hopen | [Hclose | Hspace]].
    + left. apply ascii_of_z_eq_40; assumption.
    + right; left. apply ascii_of_z_eq_41; assumption.
    + right; right. apply ascii_of_z_eq_32; assumption.
  - apply IH.
    + intros i Hi.
      specialize (Hrange (i + 1)).
      rewrite Zlength_cons in Hrange.
      replace (Znth i xs 0) with (Znth (i + 1) (x :: xs) 0).
      * apply Hrange. lia.
      * unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    + exact Hforall.
Qed.

Lemma problem_6_pre_z_chars : forall l,
  ascii_range_z l ->
  problem_6_pre_z l ->
  chars_are_paren_space_z l.
Proof.
  intros l Hrange Hpre.
  unfold problem_6_pre_z, problem_6_pre in Hpre.
  destruct Hpre as [Hforall _].
  apply ForallChars_paren_space_z; assumption.
Qed.

Lemma paren_step_output_len : forall out in_group max_level ch,
  Zlength (paren_step_output_z out in_group max_level ch) =
  Zlength out +
  (if Z.eqb ch 32 then if Z.eqb in_group 0 then 0 else 1 else 0).
Proof.
  intros.
  unfold paren_step_output_z, paren_final_output_z.
  destruct (Z.eqb ch 32); [destruct (Z.eqb in_group 0) |]; rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia.
Qed.

Lemma paren_prefix_output_len_bound : forall input i,
  0 <= i ->
  i <= Zlength input ->
  Zlength (paren_prefix_output_z i input) <= i.
Proof.
  intros input i Hi Hle.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (i = Z.of_nat n) by lia.
  subst i.
  clear Hn Hi.
  induction n as [| n IH].
  - unfold paren_prefix_output_z, paren_prefix_state_z.
    replace (sublist 0 0 input) with (@nil Z) by (rewrite sublist_nil; reflexivity).
    cbn. lia.
  - assert (0 <= Z.of_nat n < Zlength input) as Hidx by lia.
    pose proof (paren_prefix_step input (Z.of_nat n) Hidx) as [Hout _].
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n)) with (Z.of_nat n + 1) by lia.
    rewrite Hout.
    rewrite paren_step_output_len.
    specialize (IH ltac:(lia)).
    destruct (Z.eqb (Znth (Z.of_nat n) input 0) 32);
      destruct (Z.eqb (paren_prefix_in_group_z (Z.of_nat n) input) 0); lia.
Qed.

Lemma Z_to_nat_paren_zmax : forall a b,
  0 <= a ->
  0 <= b ->
  Z.to_nat (paren_zmax a b) = Nat.max (Z.to_nat a) (Z.to_nat b).
Proof.
  intros a b Ha Hb.
  unfold paren_zmax.
  destruct (Z.leb_spec a b).
  - rewrite Nat.max_r; [reflexivity | apply Z2Nat.inj_le; lia].
  - rewrite Nat.max_l; [reflexivity | apply Z2Nat.inj_le; lia].
Qed.

Lemma Z_to_nat_clamped_pred : forall level,
  0 <= level ->
  Z.to_nat (if (0 <? level)%Z then level - 1 else 0) =
  Nat.pred (Z.to_nat level).
Proof.
  intros level Hlevel.
  destruct (Z.ltb_spec 0 level).
  - rewrite Z2Nat.inj_sub by lia.
    destruct (Z.to_nat level) eqn:Hn.
    + lia.
    + simpl. lia.
  - assert (level = 0) by lia.
    subst. reflexivity.
Qed.

Lemma bool_of_in_group_0 : forall in_group,
  in_group = 0 ->
  negb (Z.eqb in_group 0) = false.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma bool_of_in_group_nonzero : forall in_group,
  in_group <> 0 ->
  negb (Z.eqb in_group 0) = true.
Proof.
  intros in_group Hnz.
  rewrite Z.eqb_neq by exact Hnz.
  reflexivity.
Qed.

Lemma paren_scan_aux_string_correct : forall input out in_group level max_level,
  ascii_range_z input ->
  chars_are_paren_space_z input ->
  0 <= in_group <= 1 ->
  0 <= level ->
  0 <= max_level ->
  map Z.to_nat
    (let st := paren_scan_aux input out in_group level max_level in
     paren_final_output_z (paren_state_out st) (paren_state_in_group st) (paren_state_max st)) =
  parse_nested_parens_scan_aux
    (string_of_list_z input)
    (map Z.to_nat out)
    (negb (Z.eqb in_group 0))
    (Z.to_nat level)
    (Z.to_nat max_level).
Proof.
  induction input as [| ch rest IH]; intros out in_group level max_level Hrange Hchars Hin Hlevel Hmax.
  - simpl.
    unfold paren_final_output_z.
    destruct (Z.eqb_spec in_group 0).
    + subst. reflexivity.
    + rewrite map_app. reflexivity.
  - simpl in Hchars.
    destruct Hchars as [Hch Hchars].
    assert (Hch_range : 0 <= ch < 256).
    { specialize (Hrange 0).
      rewrite Zlength_cons in Hrange.
      change (Znth 0 (ch :: rest) 0) with ch in Hrange.
      apply Hrange. pose proof (Zlength_nonneg rest); lia. }
    assert (Hrange_rest : ascii_range_z rest).
    {
      intros i Hi.
      specialize (Hrange (i + 1)).
      rewrite Zlength_cons in Hrange.
      replace (Znth i rest 0) with (Znth (i + 1) (ch :: rest) 0).
      - apply Hrange. lia.
      - unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    destruct Hch as [Hopen | [Hclose | Hspace]].
    + subst ch.
      simpl.
      destruct (ascii_dec (ascii_of_z 40) space) as [Hs | Hs].
      { apply ascii_of_z_eq_32 in Hs; lia. all: lia. }
      destruct (ascii_dec (ascii_of_z 40) lparen) as [_ | Hnot]; [| exfalso; apply Hnot; reflexivity].
      apply IH; try assumption; try lia.
      * apply paren_step_in_group_range.
      * unfold paren_step_level_z.
        replace (Z.eqb 40 32) with false by reflexivity.
        replace (Z.eqb 40 40) with true by reflexivity.
        lia.
      * unfold paren_step_max_z.
        replace (Z.eqb 40 32) with false by reflexivity.
        replace (Z.eqb 40 40) with true by reflexivity.
        unfold paren_zmax.
        destruct (Z.leb_spec max_level (level + 1)); lia.
    + subst ch.
      simpl.
      destruct (ascii_dec (ascii_of_z 41) space) as [Hs | Hs].
      { apply ascii_of_z_eq_32 in Hs; lia. all: lia. }
      destruct (ascii_dec (ascii_of_z 41) lparen) as [Ho | Ho].
      { apply ascii_of_z_eq_40 in Ho; lia. all: lia. }
      destruct (ascii_dec (ascii_of_z 41) rparen) as [_ | Hnot]; [| exfalso; apply Hnot; reflexivity].
      rewrite <- Z_to_nat_clamped_pred by lia.
      apply IH; try assumption; try lia.
      * apply paren_step_in_group_range.
      * unfold paren_step_level_z.
        replace (Z.eqb 41 32) with false by reflexivity.
        replace (Z.eqb 41 40) with false by reflexivity.
        destruct (Z.ltb_spec 0 level); lia.
      * unfold paren_step_max_z.
        replace (Z.eqb 41 32) with false by reflexivity.
        replace (Z.eqb 41 40) with false by reflexivity.
        lia.
    + subst ch.
      simpl.
      destruct (ascii_dec (ascii_of_z 32) space) as [_ | Hnot]; [| exfalso; apply Hnot; reflexivity].
      destruct (Z.eqb_spec in_group 0).
      * subst in_group.
        apply IH; try assumption; try lia.
        -- apply paren_step_in_group_range.
        -- unfold paren_step_level_z.
           rewrite Z.eqb_refl. reflexivity.
        -- unfold paren_step_max_z.
           rewrite Z.eqb_refl. reflexivity.
      * rewrite map_app.
        apply IH; try assumption; try lia.
        -- apply paren_step_in_group_range.
        -- unfold paren_step_level_z.
           rewrite Z.eqb_refl.
           replace (Z.eqb in_group 0) with false by (symmetry; apply Z.eqb_neq; exact n).
           lia.
        -- unfold paren_step_max_z.
           rewrite Z.eqb_refl.
           replace (Z.eqb in_group 0) with false by (symmetry; apply Z.eqb_neq; exact n).
           lia.
Qed.

Lemma problem_6_spec_z_intro : forall input output,
  ascii_range_z input ->
  problem_6_pre_z input ->
  output = paren_output_z input ->
  problem_6_spec_z input output.
Proof.
  intros input output Hrange Hpre Hout.
  unfold problem_6_spec_z, problem_6_spec.
  rewrite Hout.
  unfold parse_nested_parens_impl, paren_output_z.
  pose proof (problem_6_pre_z_chars input Hrange Hpre) as Hchars.
  rewrite paren_scan_aux_string_correct; try assumption; try lia.
  reflexivity.
Qed.
