Load "../spec/132".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_132 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_132 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_132 c) (string_of_list_z_132 rest)
  end.

Definition string_length (l : list Z) : Z := Zlength l.

Definition problem_132_pre_z (l : list Z) : Prop :=
  problem_132_pre (string_of_list_z_132 l).

Definition problem_132_spec_z (l : list Z) (output : bool) : Prop :=
  problem_132_spec (string_of_list_z_132 l) output.

Definition problem_132_result_z (l : list Z) (output : Z) : Prop :=
  problem_132_spec_z l (Z.eqb output 1).

Definition bracket_codes_z_132 (l : list Z) : Prop :=
  Forall (fun c => c = 91 \/ c = 93) l.

Definition initial_bracket_scan_132 : bracket_scan_state :=
  {| scan_current := 0; scan_maximum := 0; scan_nested := false |}.

Definition scan_prefix_132 (input : list Z) (i : Z) : bracket_scan_state :=
  fold_left bracket_scan_step
    (map ascii_of_z_132 (sublist 0 i input))
    initial_bracket_scan_132.

Definition nested_scan_state_132
    (input : list Z) (i count maximum : Z) : Prop :=
  0 <= i <= Zlength input /\
  count = scan_current (scan_prefix_132 input i) /\
  maximum = scan_maximum (scan_prefix_132 input i) /\
  scan_nested (scan_prefix_132 input i) = false.

Definition nested_scan_after_132
    (input : list Z) (i count maximum : Z) : Prop :=
  0 <= i <= Zlength input /\
  count = scan_current (scan_prefix_132 input i) /\
  maximum = scan_maximum (scan_prefix_132 input i) /\
  scan_nested (scan_prefix_132 input i) = Z.leb (count + 2) maximum.

Lemma list_ascii_string_of_list_z_132 : forall l,
  list_ascii_of_string (string_of_list_z_132 l) = map ascii_of_z_132 l.
Proof.
  induction l as [|c rest IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma ascii_of_z_open_132 : ascii_of_z_132 91 = open_bracket.
Proof. vm_compute. reflexivity. Qed.

Lemma ascii_of_z_close_132 : ascii_of_z_132 93 = close_bracket.
Proof. vm_compute. reflexivity. Qed.

Lemma nat_of_ascii_ascii_of_z_132 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z_132 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_132.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma problem_132_pre_valid_bracket_codes : forall input,
  problem_132_pre_z input ->
  valid_string input ->
  bracket_codes_z_132 input.
Proof.
  intros input Hpre [Hrange _].
  unfold problem_132_pre_z, problem_132_pre in Hpre.
  rewrite list_ascii_string_of_list_z_132 in Hpre.
  unfold bracket_codes_z_132.
  apply Forall_forall.
  intros z Hin.
  apply Forall_forall with (x := ascii_of_z_132 z) in Hpre.
  - destruct (In_nth input z 0 Hin) as [n [Hn Hnth]].
    assert (Hzrange : 0 <= z <= 127).
    { specialize (Hrange (Z.of_nat n)).
      assert (0 <= Z.of_nat n < Zlength input).
      { rewrite Zlength_correct; lia. }
      specialize (Hrange H).
      unfold Znth in Hrange.
      rewrite Nat2Z.id in Hrange.
      now rewrite Hnth in Hrange. }
    destruct Hpre as [Hopen | Hclose].
    + left.
      apply f_equal with (f := nat_of_ascii) in Hopen.
      rewrite nat_of_ascii_ascii_of_z_132 in Hopen by lia.
      vm_compute in Hopen.
      apply Z2Nat.inj; try lia.
      exact Hopen.
    + right.
      apply f_equal with (f := nat_of_ascii) in Hclose.
      rewrite nat_of_ascii_ascii_of_z_132 in Hclose by lia.
      vm_compute in Hclose.
      apply Z2Nat.inj; try lia.
      exact Hclose.
  - apply in_map; exact Hin.
Qed.

Lemma sublist_succ_132 : forall input i,
  0 <= i < Zlength input ->
  sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0].
Proof.
  intros input i Hi.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  reflexivity.
Qed.

Lemma scan_prefix_succ_132 : forall input i,
  0 <= i < Zlength input ->
  scan_prefix_132 input (i + 1) =
  bracket_scan_step (scan_prefix_132 input i)
    (ascii_of_z_132 (Znth i input 0)).
Proof.
  intros input i Hi.
  unfold scan_prefix_132.
  rewrite (sublist_succ_132 input i Hi), map_app.
  simpl.
  rewrite fold_left_app.
  reflexivity.
Qed.

Lemma bracket_codes_Znth_132 : forall input i,
  bracket_codes_z_132 input ->
  0 <= i < Zlength input ->
  Znth i input 0 = 91 \/ Znth i input 0 = 93.
Proof.
  intros input i Hcodes Hi.
  unfold bracket_codes_z_132 in Hcodes.
  apply Forall_forall with (x := Znth i input 0) in Hcodes.
  - exact Hcodes.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma nested_scan_initial_132 : forall input,
  nested_scan_state_132 input 0 0 0.
Proof.
  intros input.
  unfold nested_scan_state_132, scan_prefix_132,
    initial_bracket_scan_132.
  simpl.
  split; [pose proof (Zlength_nonneg input); lia|].
  repeat split; reflexivity.
Qed.

Lemma nested_scan_step_132 : forall input i count maximum ch count' maximum',
  nested_scan_state_132 input i count maximum ->
  i < Zlength input ->
  ch = Znth i input 0 ->
  (ch = 91 \/ ch = 93) ->
  count' = (if Z.eqb ch 91 then count + 1 else Z.max 0 (count - 1)) ->
  maximum' = Z.max maximum count' ->
  nested_scan_after_132 input (i + 1) count' maximum'.
Proof.
  intros input i count maximum ch count' maximum'
    Hstate Hi Hch Hcodes Hcount Hmaximum.
  unfold nested_scan_state_132 in Hstate.
  destruct Hstate as [Hrange [Hcount0 [Hmaximum0 Hfound]]].
  unfold nested_scan_after_132.
  rewrite scan_prefix_succ_132 by lia.
  subst ch count maximum count' maximum'.
  destruct Hcodes as [Hopen | Hclose].
  - rewrite Hopen, ascii_of_z_open_132.
    unfold bracket_scan_step; cbn [scan_current scan_maximum scan_nested].
    rewrite Hfound; cbn [orb].
    repeat split; try lia; reflexivity.
  - rewrite Hclose, ascii_of_z_close_132.
    unfold bracket_scan_step; cbn [scan_current scan_maximum scan_nested].
    rewrite Hfound; cbn [orb].
    repeat split; try lia; reflexivity.
Qed.

Lemma nested_scan_after_continue_132 : forall input i count maximum,
  nested_scan_after_132 input i count maximum ->
  maximum - 2 < count ->
  nested_scan_state_132 input i count maximum.
Proof.
  intros input i count maximum Hafter Hcontinue.
  unfold nested_scan_after_132 in Hafter.
  unfold nested_scan_state_132.
  destruct Hafter as [Hrange [Hcount [Hmaximum Hfound]]].
  refine (conj Hrange (conj Hcount (conj Hmaximum _))).
  rewrite Hfound.
  apply Z.leb_gt; lia.
Qed.

Lemma scan_nested_step_true_132 : forall state c,
  scan_nested state = true ->
  scan_nested (bracket_scan_step state c) = true.
Proof.
  intros state c H.
  unfold bracket_scan_step.
  destruct (ascii_dec c open_bracket); simpl; now rewrite H.
Qed.

Lemma scan_nested_fold_true_132 : forall chars state,
  scan_nested state = true ->
  scan_nested (fold_left bracket_scan_step chars state) = true.
Proof.
  induction chars as [|c rest IH]; intros state H; simpl; [exact H|].
  apply IH. now apply scan_nested_step_true_132.
Qed.

Lemma scan_prefix_full_132 : forall input,
  scan_prefix_132 input (Zlength input) =
  canonical_bracket_scan (string_of_list_z_132 input).
Proof.
  intros input.
  unfold scan_prefix_132, canonical_bracket_scan,
    initial_bracket_scan_132.
  rewrite (sublist_self input (Zlength input) eq_refl),
    list_ascii_string_of_list_z_132.
  reflexivity.
Qed.

Lemma nested_scan_after_found_132 : forall input i count maximum,
  nested_scan_after_132 input i count maximum ->
  count <= maximum - 2 ->
  problem_132_result_z input 1.
Proof.
  intros input i count maximum Hafter Hfound.
  unfold nested_scan_after_132 in Hafter.
  destruct Hafter as [Hrange [Hcount [Hmaximum Hnested]]].
  assert (Hprefix : scan_nested (scan_prefix_132 input i) = true).
  { rewrite Hnested, Z.leb_le; lia. }
  unfold problem_132_result_z, problem_132_spec_z, problem_132_spec.
  simpl.
  split; [intros _|intros _; reflexivity].
  unfold nested_depth_drop.
  rewrite <- scan_prefix_full_132.
  unfold scan_prefix_132 in *.
  rewrite (sublist_split 0 (Zlength input) i input) by lia.
  rewrite map_app, fold_left_app.
  apply scan_nested_fold_true_132; exact Hprefix.
Qed.

Lemma nested_scan_final_false_132 : forall input count maximum,
  nested_scan_state_132 input (Zlength input) count maximum ->
  problem_132_result_z input 0.
Proof.
  intros input count maximum Hstate.
  unfold nested_scan_state_132 in Hstate.
  destruct Hstate as [_ [_ [_ Hfalse]]].
  unfold problem_132_result_z, problem_132_spec_z, problem_132_spec.
  simpl.
  split; [discriminate|].
  unfold nested_depth_drop.
  rewrite <- scan_prefix_full_132.
  now rewrite Hfalse.
Qed.
