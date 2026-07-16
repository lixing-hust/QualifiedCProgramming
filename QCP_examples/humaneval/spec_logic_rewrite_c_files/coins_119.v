Load "../spec/119".

Require Import Coq.ZArith.ZArith.
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

Definition ascii_of_z_119 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_119 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_119 c) (string_of_list_z_119 rest)
  end.

Definition yesno_of_z_119 (z : Z) : string :=
  if Z.eqb z 1 then "Yes"%string else "No"%string.

Definition problem_119_pre_z (l1 l2 : list Z) : Prop :=
  problem_119_pre [string_of_list_z_119 l1; string_of_list_z_119 l2].

Definition problem_119_spec_z (l1 l2 : list Z) (output : Z) : Prop :=
  problem_119_spec
    [string_of_list_z_119 l1; string_of_list_z_119 l2]
    (yesno_of_z_119 output).

Definition paren_codes_119 (l : list Z) : Prop :=
  Forall (fun c => c = 40 \/ c = 41) l.

Definition open_count_119 (l : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l 40).

Definition close_count_119 (l : list Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec l 41).

Definition paren_balance_119 (l : list Z) : Z :=
  open_count_119 l - close_count_119 l.

Definition paren_prefix_ok_119 (l : list Z) : Prop :=
  forall n,
    (n <= List.length l)%nat ->
    close_count_119 (firstn n l) <= open_count_119 (firstn n l).

Definition paren_scan_state_119
    (whole : list Z) (i count can : Z) : Prop :=
  0 <= i <= Zlength whole /\
  let done := sublist 0 i whole in
  count = paren_balance_119 done /\
  (can = 1 <-> paren_prefix_ok_119 done) /\
  (can = 0 \/ can = 1).

Lemma paren_prefix_ok_balance_nonnegative_119 : forall l,
  paren_prefix_ok_119 l -> 0 <= paren_balance_119 l.
Proof.
  intros l Hprefix.
  specialize (Hprefix (List.length l) (Nat.le_refl _)).
  rewrite firstn_all in Hprefix.
  unfold paren_balance_119; lia.
Qed.

Lemma paren_scan_can_one_nonnegative_119 : forall whole i count,
  paren_scan_state_119 whole i count 1 -> 0 <= count.
Proof.
  intros whole i count Hstate.
  unfold paren_scan_state_119 in Hstate.
  cbn beta in Hstate.
  destruct Hstate as [_ [Hcount [Hcan _]]].
  rewrite Hcount.
  apply paren_prefix_ok_balance_nonnegative_119.
  apply (proj1 Hcan); reflexivity.
Qed.

Lemma list_ascii_string_of_list_z_119 : forall l,
  list_ascii_of_string (string_of_list_z_119 l) = map ascii_of_z_119 l.
Proof.
  induction l as [|c rest IH]; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma string_of_list_z_119_app : forall l1 l2,
  string_of_list_z_119 (l1 ++ l2) =
  String.append (string_of_list_z_119 l1) (string_of_list_z_119 l2).
Proof.
  induction l1 as [|c rest IH]; intros l2; simpl; [reflexivity|].
  now rewrite IH.
Qed.

Lemma paren_codes_app_119 : forall l1 l2,
  paren_codes_119 l1 ->
  paren_codes_119 l2 ->
  paren_codes_119 (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2.
  unfold paren_codes_119 in *.
  now apply Forall_app.
Qed.

Lemma paren_codes_firstn_119 : forall l n,
  paren_codes_119 l ->
  paren_codes_119 (firstn n l).
Proof.
  intros l n H.
  unfold paren_codes_119 in *.
  revert l H.
  induction n as [|n IH]; intros l H; simpl; [constructor|].
  destruct l as [|c rest]; simpl; [constructor|].
  inversion H; subst.
  constructor; [assumption|].
  now apply IH.
Qed.

Lemma ascii_open_count_119 : forall l,
  paren_codes_119 l ->
  count_occ ascii_dec (map ascii_of_z_119 l) "("%char =
  count_occ Z.eq_dec l 40.
Proof.
  intros l Hcodes.
  induction Hcodes as [|c rest Hc Hrest IH]; simpl; [reflexivity|].
  destruct Hc as [-> | ->]; vm_compute in *; now rewrite IH.
Qed.

Lemma ascii_close_count_119 : forall l,
  paren_codes_119 l ->
  count_occ ascii_dec (map ascii_of_z_119 l) ")"%char =
  count_occ Z.eq_dec l 41.
Proof.
  intros l Hcodes.
  induction Hcodes as [|c rest Hc Hrest IH]; simpl; [reflexivity|].
  destruct Hc as [-> | ->]; vm_compute in *; now rewrite IH.
Qed.

Lemma balanced_parentheses_codes_119 : forall l,
  paren_codes_119 l ->
  (balanced_parentheses (map ascii_of_z_119 l) <->
   paren_balance_119 l = 0 /\ paren_prefix_ok_119 l).
Proof.
  intros l Hcodes.
  unfold balanced_parentheses, paren_balance_119,
    paren_prefix_ok_119, open_count_119, close_count_119.
  rewrite (ascii_open_count_119 l Hcodes).
  rewrite (ascii_close_count_119 l Hcodes).
  split.
  - intros [Htotal Hprefix].
    split; [lia|].
    intros n Hn.
    specialize (Hprefix n).
    rewrite map_length in Hprefix.
    specialize (Hprefix Hn).
    rewrite firstn_map in Hprefix.
    rewrite (ascii_open_count_119 (firstn n l)
      (paren_codes_firstn_119 l n Hcodes)) in Hprefix.
    rewrite (ascii_close_count_119 (firstn n l)
      (paren_codes_firstn_119 l n Hcodes)) in Hprefix.
    lia.
  - intros [Htotal Hprefix].
    split; [lia|].
    intros n Hn.
    rewrite map_length in Hn.
    rewrite firstn_map.
    specialize (Hprefix n Hn).
    rewrite (ascii_open_count_119 (firstn n l)
      (paren_codes_firstn_119 l n Hcodes)).
    rewrite (ascii_close_count_119 (firstn n l)
      (paren_codes_firstn_119 l n Hcodes)).
    lia.
Qed.

Lemma paren_scan_initial_119 : forall whole,
  paren_scan_state_119 whole 0 0 1.
Proof.
  intros whole.
  unfold paren_scan_state_119.
  change (0 <= 0 <= Zlength whole /\
    0 = paren_balance_119 [] /\
    (1 = 1 <-> paren_prefix_ok_119 []) /\ (1 = 0 \/ 1 = 1)).
  split; [unfold Zlength; rewrite Zlength_correct; lia|].
  split.
  - reflexivity.
  - split.
    + split; [|intros; reflexivity].
      intros _.
      unfold paren_prefix_ok_119.
      intros n Hn.
      replace n with 0%nat by (simpl in Hn; lia).
      reflexivity.
    + right; reflexivity.
Qed.

Lemma paren_prefix_ok_snoc_119 : forall l c,
  paren_prefix_ok_119 (l ++ [c]) <->
  paren_prefix_ok_119 l /\
  close_count_119 (l ++ [c]) <= open_count_119 (l ++ [c]).
Proof.
  intros l c.
  unfold paren_prefix_ok_119.
  rewrite app_length; simpl.
  split.
  - intros H.
    split.
    + intros n Hn.
      specialize (H n ltac:(lia)).
      rewrite firstn_app in H.
      replace (n - List.length l)%nat with 0%nat in H by lia.
      simpl in H.
      now rewrite app_nil_r in H.
    + specialize (H (S (List.length l)) ltac:(lia)).
      replace (S (List.length l)) with (List.length (l ++ [c])) in H
        by (rewrite app_length; simpl; lia).
      rewrite firstn_all in H.
      exact H.
  - intros [Hl Hfull] n Hn.
    destruct (Nat.le_gt_cases n (List.length l)) as [Hle | Hgt].
    + specialize (Hl n Hle).
      rewrite firstn_app.
      replace (n - List.length l)%nat with 0%nat by lia.
      simpl.
      now rewrite app_nil_r.
    + assert (n = S (List.length l)) by lia.
      subst n.
      replace (S (List.length l)) with (List.length (l ++ [c]))
        by (rewrite app_length; simpl; lia).
      rewrite firstn_all.
      exact Hfull.
Qed.

Lemma paren_balance_snoc_open_119 : forall l,
  paren_balance_119 (l ++ [40]) = paren_balance_119 l + 1.
Proof.
  intros l.
  unfold paren_balance_119, open_count_119, close_count_119.
  repeat rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec 40 40); [|congruence].
  destruct (Z.eq_dec 40 41); [congruence|].
  lia.
Qed.

Lemma paren_balance_snoc_close_119 : forall l,
  paren_balance_119 (l ++ [41]) = paren_balance_119 l - 1.
Proof.
  intros l.
  unfold paren_balance_119, open_count_119, close_count_119.
  repeat rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec 41 40); [congruence|].
  destruct (Z.eq_dec 41 41); [|congruence].
  lia.
Qed.

Lemma paren_prefix_ok_open_119 : forall l,
  paren_prefix_ok_119 (l ++ [40]) <-> paren_prefix_ok_119 l.
Proof.
  intros l.
  rewrite paren_prefix_ok_snoc_119.
  split.
  - tauto.
  - intros Hl.
    split; [exact Hl|].
    specialize (Hl (List.length l) (Nat.le_refl _)).
    rewrite firstn_all in Hl by lia.
    unfold open_count_119, close_count_119 in *.
    repeat rewrite count_occ_app.
    simpl.
    destruct (Z.eq_dec 40 40); [|congruence].
    destruct (Z.eq_dec 40 41); [congruence|].
    lia.
Qed.

Lemma paren_prefix_ok_close_119 : forall l,
  paren_prefix_ok_119 (l ++ [41]) <->
  paren_prefix_ok_119 l /\ 0 <= paren_balance_119 l - 1.
Proof.
  intros l.
  rewrite paren_prefix_ok_snoc_119.
  assert (Hnonneg:
    close_count_119 (l ++ [41]) <= open_count_119 (l ++ [41]) <->
    0 <= paren_balance_119 (l ++ [41])).
  { unfold paren_balance_119; lia. }
  rewrite Hnonneg.
  rewrite paren_balance_snoc_close_119.
  tauto.
Qed.

Lemma paren_scan_open_119 : forall whole i count can,
  paren_scan_state_119 whole i count can ->
  i < Zlength whole ->
  Znth i whole 0 = 40 ->
  paren_scan_state_119 whole (i + 1) (count + 1) can.
Proof.
  intros whole i count can Hstate Hi Hchar.
  unfold paren_scan_state_119 in Hstate |- *.
  cbn beta in Hstate |- *.
  destruct Hstate as [Hbounds [Hcount [Hcan Hrange]]].
  split; [lia|].
  rewrite (helper_sublist_snoc_Z whole i 0) by lia.
  rewrite Hchar.
  split.
  - rewrite paren_balance_snoc_open_119; lia.
  - split.
    + rewrite paren_prefix_ok_open_119.
      exact Hcan.
    + exact Hrange.
Qed.

Lemma paren_scan_close_negative_119 : forall whole i count can,
  paren_scan_state_119 whole i count can ->
  i < Zlength whole ->
  Znth i whole 0 = 41 ->
  count - 1 < 0 ->
  paren_scan_state_119 whole (i + 1) (count - 1) 0.
Proof.
  intros whole i count can Hstate Hi Hchar Hnegative.
  unfold paren_scan_state_119 in Hstate |- *.
  cbn beta in Hstate |- *.
  destruct Hstate as [Hbounds [Hcount [Hcan Hrange]]].
  split; [lia|].
  rewrite (helper_sublist_snoc_Z whole i 0) by lia.
  rewrite Hchar.
  split.
  - rewrite paren_balance_snoc_close_119; lia.
  - split.
    + rewrite paren_prefix_ok_close_119.
      split.
      * intro Hbad; discriminate.
      * intros [_ Hnonnegative].
        rewrite <- Hcount in Hnonnegative.
        lia.
    + now left.
Qed.

Lemma paren_scan_close_nonnegative_119 : forall whole i count can,
  paren_scan_state_119 whole i count can ->
  i < Zlength whole ->
  Znth i whole 0 = 41 ->
  0 <= count - 1 ->
  paren_scan_state_119 whole (i + 1) (count - 1) can.
Proof.
  intros whole i count can Hstate Hi Hchar Hnonnegative.
  unfold paren_scan_state_119 in Hstate |- *.
  cbn beta in Hstate |- *.
  destruct Hstate as [Hbounds [Hcount [Hcan Hrange]]].
  split; [lia|].
  rewrite (helper_sublist_snoc_Z whole i 0) by lia.
  rewrite Hchar.
  split.
  - rewrite paren_balance_snoc_close_119; lia.
  - split.
    + rewrite paren_prefix_ok_close_119.
      rewrite <- Hcan.
      split.
      * intros Hcan1; split; [exact Hcan1|].
        now rewrite <- Hcount.
      * tauto.
    + exact Hrange.
Qed.

Lemma paren_code_at_119 : forall l i,
  paren_codes_119 l ->
  0 <= i < Zlength l ->
  Znth i l 0 = 40 \/ Znth i l 0 = 41.
Proof.
  intros l i Hcodes Hi.
  unfold paren_codes_119 in Hcodes.
  apply Forall_forall with (x := Znth i l 0) in Hcodes.
  - exact Hcodes.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma paren_code_at_app_left_119 : forall l1 l2 i,
  paren_codes_119 l1 ->
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) 0 = 40 \/ Znth i (l1 ++ l2) 0 = 41.
Proof.
  intros l1 l2 i Hcodes Hi.
  rewrite app_Znth1 by lia.
  now apply paren_code_at_119.
Qed.

Lemma paren_code_at_app_right_119 : forall l1 l2 i,
  paren_codes_119 l2 ->
  0 <= i < Zlength l2 ->
  Znth (Zlength l1 + i) (l1 ++ l2) 0 = 40 \/
  Znth (Zlength l1 + i) (l1 ++ l2) 0 = 41.
Proof.
  intros l1 l2 i Hcodes Hi.
  rewrite app_Znth2 by lia.
  replace (Zlength l1 + i - Zlength l1) with i by lia.
  now apply paren_code_at_119.
Qed.

Lemma paren_balance_app_119 : forall l1 l2,
  paren_balance_119 (l1 ++ l2) =
  paren_balance_119 l1 + paren_balance_119 l2.
Proof.
  intros l1 l2.
  unfold paren_balance_119, open_count_119, close_count_119.
  repeat rewrite count_occ_app.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma paren_balance_swap_119 : forall l1 l2,
  paren_balance_119 (l1 ++ l2) = paren_balance_119 (l2 ++ l1).
Proof.
  intros l1 l2.
  repeat rewrite paren_balance_app_119.
  lia.
Qed.

Lemma paren_scan_full_119 : forall whole count can,
  paren_scan_state_119 whole (Zlength whole) count can ->
  count = paren_balance_119 whole /\
  (can = 1 <-> paren_prefix_ok_119 whole) /\
  (can = 0 \/ can = 1).
Proof.
  intros whole count can Hstate.
  unfold paren_scan_state_119 in Hstate.
  cbn beta in Hstate.
  destruct Hstate as [_ [Hcount [Hcan Hrange]]].
  rewrite sublist_self in Hcount by reflexivity.
  rewrite sublist_self in Hcan by reflexivity.
  auto.
Qed.

Lemma balanced_string_codes_119 : forall l,
  paren_codes_119 l ->
  (balanced_parentheses
     (list_ascii_of_string (string_of_list_z_119 l)) <->
   paren_balance_119 l = 0 /\ paren_prefix_ok_119 l).
Proof.
  intros l Hcodes.
  rewrite list_ascii_string_of_list_z_119.
  now apply balanced_parentheses_codes_119.
Qed.

Lemma balanced_concat_codes_119 : forall l1 l2,
  paren_codes_119 l1 -> paren_codes_119 l2 ->
  (balanced_parentheses
     (list_ascii_of_string (string_of_list_z_119 l1) ++
      list_ascii_of_string (string_of_list_z_119 l2)) <->
   paren_balance_119 (l1 ++ l2) = 0 /\
   paren_prefix_ok_119 (l1 ++ l2)).
Proof.
  intros l1 l2 Hcodes1 Hcodes2.
  repeat rewrite list_ascii_string_of_list_z_119.
  rewrite <- map_app.
  apply balanced_parentheses_codes_119.
  now apply paren_codes_app_119.
Qed.

Lemma paren_prefix_false_of_can_zero_119 : forall whole,
  paren_scan_state_119 whole (Zlength whole) 0 0 ->
  ~ paren_prefix_ok_119 whole.
Proof.
  intros whole Hstate Hprefix.
  pose proof (paren_scan_full_119 whole 0 0 Hstate) as [_ [Hcan _]].
  apply (proj2 Hcan) in Hprefix.
  discriminate.
Qed.

Lemma problem_119_spec_total_nonzero : forall l1 l2 count can,
  paren_codes_119 l1 -> paren_codes_119 l2 ->
  paren_scan_state_119 (l1 ++ l2) (Zlength l1 + Zlength l2) count can ->
  count <> 0 ->
  problem_119_spec_z l1 l2 0.
Proof.
  intros l1 l2 count can Hcodes1 Hcodes2 Hstate Hcountnz.
  assert (Hcodes12 : paren_codes_119 (l1 ++ l2))
    by now apply paren_codes_app_119.
  assert (Hcodes21 : paren_codes_119 (l2 ++ l1))
    by now apply paren_codes_app_119.
  rewrite <- Zlength_app in Hstate.
  pose proof (paren_scan_full_119 (l1 ++ l2) count can Hstate)
    as [Hcount _].
  assert (Hbal12 : paren_balance_119 (l1 ++ l2) <> 0) by lia.
  assert (Hbal21 : paren_balance_119 (l2 ++ l1) <> 0).
  { rewrite <- paren_balance_swap_119; exact Hbal12. }
  unfold problem_119_spec_z, yesno_of_z_119, problem_119_spec.
  simpl.
  exists (string_of_list_z_119 l1), (string_of_list_z_119 l2).
  split; [reflexivity|].
  right.
  split.
  - split.
    + intro Hbalanced.
    apply (balanced_concat_codes_119 l1 l2 Hcodes1 Hcodes2) in Hbalanced.
      tauto.
    + intro Hbalanced.
      apply (balanced_concat_codes_119 l2 l1 Hcodes2 Hcodes1) in Hbalanced.
      tauto.
  - reflexivity.
Qed.

Lemma problem_119_spec_left_yes : forall l1 l2,
  paren_codes_119 l1 -> paren_codes_119 l2 ->
  paren_scan_state_119 (l1 ++ l2) (Zlength l1 + Zlength l2) 0 1 ->
  problem_119_spec_z l1 l2 1.
Proof.
  intros l1 l2 Hcodes1 Hcodes2 Hstate.
  assert (Hcodes12 : paren_codes_119 (l1 ++ l2))
    by now apply paren_codes_app_119.
  rewrite <- Zlength_app in Hstate.
  pose proof (paren_scan_full_119 (l1 ++ l2) 0 1 Hstate)
    as [Hbalance [Hcan _]].
  assert (Hbalanced : balanced_parentheses
    (list_ascii_of_string (string_of_list_z_119 l1) ++
     list_ascii_of_string (string_of_list_z_119 l2))).
  { apply (balanced_concat_codes_119 l1 l2 Hcodes1 Hcodes2).
    split; [lia|].
    apply Hcan; reflexivity. }
  unfold problem_119_spec_z, yesno_of_z_119, problem_119_spec.
  simpl.
  exists (string_of_list_z_119 l1), (string_of_list_z_119 l2).
  split; [reflexivity|].
  left.
  split.
  - left; exact Hbalanced.
  - reflexivity.
Qed.

Lemma problem_119_spec_right_yes : forall l1 l2 count,
  paren_codes_119 l1 -> paren_codes_119 l2 ->
  paren_scan_state_119 (l1 ++ l2) (Zlength l1 + Zlength l2) 0 0 ->
  paren_scan_state_119 (l2 ++ l1) (Zlength l2 + Zlength l1) count 1 ->
  problem_119_spec_z l1 l2 1.
Proof.
  intros l1 l2 count Hcodes1 Hcodes2 Hleft Hright.
  assert (Hcodes21 : paren_codes_119 (l2 ++ l1))
    by now apply paren_codes_app_119.
  rewrite <- Zlength_app in Hleft.
  rewrite <- Zlength_app in Hright.
  pose proof (paren_scan_full_119 (l1 ++ l2) 0 0 Hleft)
    as [Hbal12 _].
  pose proof (paren_scan_full_119 (l2 ++ l1) count 1 Hright)
    as [Hcount [Hcan _]].
  assert (Hbal21 : paren_balance_119 (l2 ++ l1) = 0).
  { rewrite <- paren_balance_swap_119; symmetry; exact Hbal12. }
  assert (Hbalanced : balanced_parentheses
    (list_ascii_of_string (string_of_list_z_119 l2) ++
     list_ascii_of_string (string_of_list_z_119 l1))).
  { apply (balanced_concat_codes_119 l2 l1 Hcodes2 Hcodes1).
    split; [exact Hbal21|].
    apply Hcan; reflexivity. }
  unfold problem_119_spec_z, yesno_of_z_119, problem_119_spec.
  simpl.
  exists (string_of_list_z_119 l1), (string_of_list_z_119 l2).
  split; [reflexivity|].
  left.
  split.
  - right.
    exact Hbalanced.
  - reflexivity.
Qed.

Lemma problem_119_spec_both_no : forall l1 l2 count,
  paren_codes_119 l1 -> paren_codes_119 l2 ->
  paren_scan_state_119 (l1 ++ l2) (Zlength l1 + Zlength l2) 0 0 ->
  paren_scan_state_119 (l2 ++ l1) (Zlength l2 + Zlength l1) count 0 ->
  problem_119_spec_z l1 l2 0.
Proof.
  intros l1 l2 count Hcodes1 Hcodes2 Hleft Hright.
  assert (Hcodes12 : paren_codes_119 (l1 ++ l2))
    by now apply paren_codes_app_119.
  assert (Hcodes21 : paren_codes_119 (l2 ++ l1))
    by now apply paren_codes_app_119.
  rewrite <- Zlength_app in Hleft.
  rewrite <- Zlength_app in Hright.
  assert (Hnot12 : ~ paren_prefix_ok_119 (l1 ++ l2))
    by now apply paren_prefix_false_of_can_zero_119.
  pose proof (paren_scan_full_119 (l2 ++ l1) count 0 Hright)
    as [_ [Hcan21 _]].
  assert (Hnot21 : ~ paren_prefix_ok_119 (l2 ++ l1)).
  { intro Hprefix.
    apply (proj2 Hcan21) in Hprefix.
    discriminate. }
  unfold problem_119_spec_z, yesno_of_z_119, problem_119_spec.
  simpl.
  exists (string_of_list_z_119 l1), (string_of_list_z_119 l2).
  split; [reflexivity|].
  right.
  split.
  - split.
    + intro Hbalanced.
      apply (balanced_concat_codes_119 l1 l2 Hcodes1 Hcodes2) in Hbalanced.
      tauto.
    + intro Hbalanced.
      apply (balanced_concat_codes_119 l2 l1 Hcodes2 Hcodes1) in Hbalanced.
      tauto.
  - reflexivity.
Qed.
