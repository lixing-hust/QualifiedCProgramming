Load "../spec/56".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_56 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_56 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_56 c) (string_of_list_z_56 rest)
  end.

Definition bool_of_z_56 (z : Z) : bool :=
  negb (Z.eqb z 0).

Definition problem_56_pre_z (input : list Z) : Prop :=
  problem_56_pre (string_of_list_z_56 input).

Definition problem_56_spec_z (input : list Z) (result : Z) : Prop :=
  problem_56_spec (string_of_list_z_56 input) (bool_of_z_56 result).

Inductive BracketScan56 : list Z -> Z -> Prop :=
| bracket_scan_nil_56 : BracketScan56 [] 0
| bracket_scan_open_56 : forall prefix depth,
    BracketScan56 prefix depth ->
    BracketScan56 (prefix ++ [60]) (depth + 1)
| bracket_scan_close_56 : forall prefix depth,
    BracketScan56 prefix depth ->
    0 < depth ->
    BracketScan56 (prefix ++ [62]) (depth - 1).

Definition bracket_state_56 (input : list Z) (i level : Z) : Prop :=
  0 <= i <= Zlength input /\
  BracketScan56 (firstn (Z.to_nat i) input) level.

Lemma list_ascii_of_string_of_list_z_56 : forall l,
  list_ascii_of_string (string_of_list_z_56 l) = map ascii_of_z_56 l.
Proof.
  induction l as [| c rest IH]; simpl; congruence.
Qed.

Lemma firstn_succ_snoc_56 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_56 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_56 with (d := 0)
    by (rewrite Zlength_correct in Hi; lia).
  reflexivity.
Qed.

Lemma bracket_scan_bounds_56 : forall prefix depth,
  BracketScan56 prefix depth ->
  0 <= depth <= Zlength prefix.
Proof.
  intros prefix depth Hscan.
  induction Hscan.
  - unfold Zlength. simpl. lia.
  - rewrite Zlength_app. unfold Zlength at 2. simpl. lia.
  - rewrite Zlength_app. unfold Zlength at 2. simpl. lia.
Qed.

Lemma bracket_scan_counts_56 : forall prefix depth,
  BracketScan56 prefix depth ->
  Z.of_nat (count_occ Z.eq_dec prefix 60) =
  Z.of_nat (count_occ Z.eq_dec prefix 62) + depth.
Proof.
  intros prefix depth Hscan.
  induction Hscan.
  - simpl. lia.
  - rewrite !count_occ_app. simpl. lia.
  - rewrite !count_occ_app. simpl. lia.
Qed.

Lemma prefix_of_snoc_56 : forall {A : Type} (l : list A) x p s,
  l ++ [x] = p ++ s ->
  (exists t, l = p ++ t) \/ (p = l ++ [x] /\ s = []).
Proof.
  intros A l x p s Heq.
  assert (Hlen : (List.length p <= List.length l + 1)%nat).
  { apply (f_equal (@List.length A)) in Heq.
    rewrite !app_length in Heq. simpl in Heq. lia. }
  destruct (le_gt_dec (List.length p) (List.length l)) as [Hple | Hgt].
  - left. exists (skipn (List.length p) l).
    rewrite <- firstn_skipn with (n := List.length p) (l := l) at 1.
    assert (Hp : firstn (List.length p) l = p).
    { apply (f_equal (firstn (List.length p))) in Heq.
      rewrite !firstn_app in Heq.
      rewrite firstn_all in Heq.
      replace (List.length p - List.length l)%nat with 0%nat in Heq by lia.
      replace (List.length p - List.length p)%nat with 0%nat in Heq by lia.
      simpl in Heq. rewrite !app_nil_r in Heq. exact Heq. }
    now rewrite Hp.
  - right.
    pose proof Heq as HlenEq.
    apply (f_equal (@List.length A)) in HlenEq.
    rewrite !app_length in HlenEq. simpl in HlenEq.
    assert (List.length p = (List.length l + 1)%nat) by lia.
    assert (List.length s = 0%nat) by lia.
    apply length_zero_iff_nil in H0. subst s.
    rewrite app_nil_r in Heq. split; congruence.
Qed.

Lemma bracket_scan_prefix_ok_56 : forall input depth,
  BracketScan56 input depth ->
  forall prefix suffix,
    input = prefix ++ suffix ->
    (count_occ Z.eq_dec prefix (62%Z) <=
     count_occ Z.eq_dec prefix (60%Z))%nat.
Proof.
  intros input depth Hscan.
  induction Hscan as
      [| input depth Hscan IH | input depth Hscan Hdepth IH];
    intros prefix suffix Heq.
  - destruct prefix; simpl in *; try discriminate; lia.
  - destruct (prefix_of_snoc_56 input 60 prefix suffix Heq)
      as [[tail Hinput] | [-> ->]].
    + eapply IH; eauto.
    + rewrite !count_occ_app. simpl.
      pose proof (bracket_scan_counts_56 input depth Hscan).
      pose proof (bracket_scan_bounds_56 input depth Hscan). lia.
  - destruct (prefix_of_snoc_56 input 62 prefix suffix Heq)
      as [[tail Hinput] | [-> ->]].
    + eapply Hdepth; eauto.
    + rewrite !count_occ_app. simpl.
      pose proof (bracket_scan_counts_56 input depth Hscan). lia.
Qed.

Definition angle_code_56 (z : Z) : Prop := z = 60 \/ z = 62.

Lemma bracket_scan_codes_56 : forall input depth,
  BracketScan56 input depth -> Forall angle_code_56 input.
Proof.
  intros input depth Hscan. induction Hscan.
  - constructor.
  - apply Forall_app. split; [exact IHHscan |].
    constructor; [left; reflexivity | constructor].
  - apply Forall_app. split; [exact IHHscan |].
    constructor; [right; reflexivity | constructor].
Qed.

Lemma angle_counts_map_56 : forall input,
  Forall angle_code_56 input ->
  count_occ ascii_dec (map ascii_of_z_56 input) "<"%char =
    count_occ Z.eq_dec input 60 /\
  count_occ ascii_dec (map ascii_of_z_56 input) ">"%char =
    count_occ Z.eq_dec input 62.
Proof.
  intros input Hcodes. induction Hcodes as [| z input Hz Hcodes IH].
  - simpl. auto.
  - destruct Hz as [-> | ->]; simpl in *; destruct IH; split; lia.
Qed.

Lemma bracket_scan_correctly_56 : forall input,
  BracketScan56 input 0 ->
  correctly_bracketed (map ascii_of_z_56 input).
Proof.
  intros input Hscan.
  unfold correctly_bracketed. split.
  - pose proof (bracket_scan_counts_56 input 0 Hscan) as Hcounts.
    pose proof (angle_counts_map_56 input
      (bracket_scan_codes_56 input 0 Hscan)) as [Hopen Hclose].
    lia.
  - intros prefix suffix Heq.
    set (raw_prefix := firstn (List.length prefix) input).
    set (raw_suffix := skipn (List.length prefix) input).
    assert (Hraw : input = raw_prefix ++ raw_suffix).
    { unfold raw_prefix, raw_suffix. symmetry. apply firstn_skipn. }
    assert (Hprefix : prefix = map ascii_of_z_56 raw_prefix).
    { apply (f_equal (firstn (List.length prefix))) in Heq.
      rewrite firstn_map in Heq.
      rewrite firstn_app in Heq.
      rewrite firstn_all in Heq.
      replace (List.length prefix - List.length prefix)%nat with 0%nat in Heq by lia.
      simpl in Heq. rewrite !app_nil_r in Heq.
      unfold raw_prefix. symmetry. exact Heq. }
    pose proof (bracket_scan_prefix_ok_56 input 0 Hscan
      raw_prefix raw_suffix Hraw) as Hraw_ok.
    pose proof (bracket_scan_codes_56 input 0 Hscan) as Hall.
    rewrite Hraw in Hall. apply Forall_app in Hall as [Hprefix_codes _].
    pose proof (angle_counts_map_56 raw_prefix Hprefix_codes)
      as [Hopen Hclose].
    rewrite Hprefix. lia.
Qed.

Lemma bracket_scan_nonzero_not_correct_56 : forall input depth,
  BracketScan56 input depth ->
  depth <> 0 ->
  ~ correctly_bracketed (map ascii_of_z_56 input).
Proof.
  intros input depth Hscan Hdepth [Heq _].
  pose proof (bracket_scan_counts_56 input depth Hscan) as Hcounts.
  pose proof (angle_counts_map_56 input
    (bracket_scan_codes_56 input depth Hscan)) as [Hopen Hclose].
  lia.
Qed.

Lemma ascii_of_z_angle_raw_56 : forall z,
  0 <= z <= 127 ->
  (ascii_of_z_56 z = "<"%char \/ ascii_of_z_56 z = ">"%char) ->
  z = 60 \/ z = 62.
Proof.
  intros z Hz [Hchar | Hchar].
  - left. apply (f_equal nat_of_ascii) in Hchar.
    unfold ascii_of_z_56 in Hchar.
    rewrite nat_ascii_embedding in Hchar by lia.
    cbn in Hchar. lia.
  - right. apply (f_equal nat_of_ascii) in Hchar.
    unfold ascii_of_z_56 in Hchar.
    rewrite nat_ascii_embedding in Hchar by lia.
    cbn in Hchar. lia.
Qed.

Lemma problem_56_pre_code_at : forall input i,
  problem_56_pre_z input ->
  string_lib.valid_string input ->
  0 <= i < string_lib.string_length input ->
  Znth i input 0 = 60 \/ Znth i input 0 = 62.
Proof.
  intros input i Hpre Hvalid Hi.
  unfold problem_56_pre_z, problem_56_pre in Hpre.
  rewrite list_ascii_of_string_of_list_z_56 in Hpre.
  assert (Hin : In (Znth i input 0) input).
  { unfold Znth.
    apply nth_In.
    unfold string_lib.string_length in Hi.
    rewrite Zlength_correct in Hi. lia. }
  assert (Hascii :
      ascii_of_z_56 (Znth i input 0) = "<"%char \/
      ascii_of_z_56 (Znth i input 0) = ">"%char).
  { rewrite Forall_forall in Hpre. apply Hpre.
    apply in_map. exact Hin. }
  apply ascii_of_z_angle_raw_56; [|exact Hascii].
  unfold string_lib.valid_string, string_lib.all_ascii in Hvalid.
  destruct Hvalid as [Hrange _]. apply Hrange. exact Hi.
Qed.

Lemma bracket_state_full_scan_56 : forall input i depth,
  bracket_state_56 input i depth ->
  i >= string_lib.string_length input ->
  BracketScan56 input depth.
Proof.
  intros input i depth [[Hi0 Hiend] Hscan] Hdone.
  unfold string_lib.string_length in Hdone.
  assert (i = Zlength input) by lia. subst i.
  replace (Z.to_nat (Zlength input)) with (List.length input) in Hscan.
  - now rewrite firstn_all in Hscan.
  - rewrite Zlength_correct. lia.
Qed.

Lemma bracket_state_zero_spec_56 : forall input i,
  bracket_state_56 input i 0 ->
  i >= string_lib.string_length input ->
  problem_56_spec_z input 1.
Proof.
  intros input i Hstate Hdone.
  pose proof (bracket_state_full_scan_56 input i 0 Hstate Hdone) as Hscan.
  unfold problem_56_spec_z, bool_of_z_56, problem_56_spec. simpl.
  rewrite list_ascii_of_string_of_list_z_56.
  split; [intro; apply bracket_scan_correctly_56; exact Hscan | auto].
Qed.

Lemma bracket_state_nonzero_spec_56 : forall input i depth,
  bracket_state_56 input i depth ->
  i >= string_lib.string_length input ->
  depth <> 0 ->
  problem_56_spec_z input 0.
Proof.
  intros input i depth Hstate Hdone Hdepth.
  pose proof (bracket_state_full_scan_56 input i depth Hstate Hdone) as Hscan.
  unfold problem_56_spec_z, bool_of_z_56, problem_56_spec. simpl.
  rewrite list_ascii_of_string_of_list_z_56.
  split; [discriminate |].
  intro Hcorrect. exfalso.
  eapply bracket_scan_nonzero_not_correct_56; eauto.
Qed.

Lemma bracket_scan_zero_close_bad_56 : forall prefix suffix,
  BracketScan56 prefix 0 ->
  ~ correctly_bracketed
      (map ascii_of_z_56 (prefix ++ [62] ++ suffix)).
Proof.
  intros prefix suffix Hscan [_ Hprefix].
  specialize (Hprefix
    (map ascii_of_z_56 (prefix ++ [62]))
    (map ascii_of_z_56 suffix)).
  assert (Hineq :
      (count_occ ascii_dec (map ascii_of_z_56 (prefix ++ [62%Z])) ">"%char <=
       count_occ ascii_dec (map ascii_of_z_56 (prefix ++ [62%Z])) "<"%char)%nat).
  { apply Hprefix. rewrite !map_app. apply app_assoc. }
  pose proof (bracket_scan_counts_56 prefix 0 Hscan) as Hcounts.
  pose proof (angle_counts_map_56 prefix
    (bracket_scan_codes_56 prefix 0 Hscan)) as [Hopen Hclose].
  rewrite !map_app in Hineq. simpl in Hineq.
  rewrite !count_occ_app in Hineq. simpl in Hineq. lia.
Qed.

Lemma bracket_state_negative_spec_56 : forall input i,
  bracket_state_56 input i 0 ->
  0 <= i < string_lib.string_length input ->
  Znth i input 0 = 62 ->
  problem_56_spec_z input 0.
Proof.
  intros input i [[Hi0 Hiend] Hscan] Hib Hchar.
  unfold problem_56_spec_z, bool_of_z_56, problem_56_spec. simpl.
  rewrite list_ascii_of_string_of_list_z_56.
  split; [discriminate |]. intro Hcorrect. exfalso.
  unfold string_lib.string_length in Hib.
  assert (Hnext :
      firstn (Z.to_nat (i + 1)) input =
      firstn (Z.to_nat i) input ++ [62]).
  { rewrite firstn_succ_Znth_56 by exact Hib. now rewrite Hchar. }
  assert (Hdecomp : input =
      (firstn (Z.to_nat i) input ++ [62]) ++
      skipn (Z.to_nat (i + 1)) input).
  { rewrite <- Hnext. symmetry. apply firstn_skipn. }
  rewrite Hdecomp in Hcorrect.
  pose proof (bracket_scan_zero_close_bad_56
    (firstn (Z.to_nat i) input)
    (skipn (Z.to_nat (i + 1)) input) Hscan) as Hbad.
  apply Hbad. rewrite app_assoc. exact Hcorrect.
Qed.

Lemma bracket_state_nil_56 : forall input,
  bracket_state_56 input 0 0.
Proof.
  intro input. split.
  - pose proof (Zlength_nonneg input). lia.
  - simpl. constructor.
Qed.

Lemma bracket_state_open_56 : forall input i depth,
  bracket_state_56 input i depth ->
  0 <= i < Zlength input ->
  Znth i input 0 = 60 ->
  bracket_state_56 input (i + 1) (depth + 1).
Proof.
  intros input i depth [Hi Hscan] Hib Hchar.
  split; [lia |].
  rewrite firstn_succ_Znth_56 by exact Hib.
  rewrite Hchar. now constructor.
Qed.

Lemma bracket_state_close_56 : forall input i depth,
  bracket_state_56 input i depth ->
  0 <= i < Zlength input ->
  Znth i input 0 = 62 ->
  0 < depth ->
  bracket_state_56 input (i + 1) (depth - 1).
Proof.
  intros input i depth [Hi Hscan] Hib Hchar Hdepth.
  split; [lia |].
  rewrite firstn_succ_Znth_56 by exact Hib.
  rewrite Hchar. now constructor.
Qed.

Lemma Znth_c_string_56 : forall input i,
  0 <= i < string_lib.string_length input ->
  Znth i (string_lib.c_string input) 0 = Znth i input 0.
Proof.
  intros input i Hi.
  unfold string_lib.c_string, string_lib.string_length in *.
  apply app_Znth1. exact Hi.
Qed.
