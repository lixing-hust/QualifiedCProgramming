Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import ListLib.
From SimpleC.StdLib Require Import string_lib.
From SimpleC.SL Require Import IntLib PtrArray2Lib SeparationLogic.
Import ListNotations.
Import naive_C_Rules.

Load "../spec/158".
Load "../StringClaude/string_bridge".

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition rows_to_strings_z_158 (rows : list (list Z)) : list string :=
  map string_of_list_z rows.

Definition problem_158_pre_z (rows : list (list Z)) : Prop :=
  problem_158_pre (rows_to_strings_z_158 rows).

Definition problem_158_spec_z (rows : list (list Z)) (result : list Z) : Prop :=
  problem_158_spec (rows_to_strings_z_158 rows) (string_of_list_z result).

Definition row_well_formed_158 (row : list Z) : Prop :=
  SimpleC.StdLib.string_lib.valid_string row /\
  SimpleC.StdLib.string_lib.string_length row < INT_MAX.

Definition rows_well_formed_158 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\ Forall row_well_formed_158 rows.

Definition row_store_pair_158 (pr : Z * list Z) : Assertion :=
  SimpleC.StdLib.string_lib.store_string (fst pr) (snd pr).

Definition row_stores_158 (ptrs : list Z) (rows : list (list Z)) : Assertion :=
  iter_sepcon (map row_store_pair_158 (combine ptrs rows)).

Definition row_stores_missing_i_158
    (ptrs : list Z) (rows : list (list Z)) (i : Z) : Assertion :=
  iter_sepcon
    (map row_store_pair_158 (CharPtrArray2.remove_Znth i (combine ptrs rows))).

Definition row_stores_missing_two_158
    (ptrs : list Z) (rows : list (list Z)) (best i : Z) : Assertion :=
  iter_sepcon
    (map row_store_pair_158
      (CharPtrArray2.remove_Znth best
        (CharPtrArray2.remove_Znth i (combine ptrs rows)))).

Definition seen_step_158 (st : list Z * Z) (ch : Z) : list Z * Z :=
  if Z.eq_dec (Znth ch (fst st) 0) 0
  then (replace_Znth ch 1 (fst st), snd st + 1)
  else st.

Definition seen_scan_158 (row : list Z) (j : Z) : list Z * Z :=
  fold_left seen_step_158 (sublist 0 j row) (repeat_Z 0 256, 0).

Definition unique_count_z_158 (row : list Z) : Z :=
  snd (seen_scan_158 row (Zlength row)).

Definition seen_state_158
    (row : list Z) (j : Z) (seen : list Z) (unique : Z) : Prop :=
  seen_scan_158 row j = (seen, unique).

Definition best_state_158
    (rows : list (list Z)) (i best maxu : Z) : Prop :=
  (i = 0 /\ best = 0 /\ maxu = 0) \/
  (0 < i /\ 0 <= best < i /\
   maxu = unique_count_z_158 (Znth best rows nil) /\
   forall k, 0 <= k < i ->
     unique_count_z_158 (Znth best rows nil) >
       unique_count_z_158 (Znth k rows nil) \/
     (unique_count_z_158 (Znth best rows nil) =
        unique_count_z_158 (Znth k rows nil) /\
      string_le
        (string_of_list_z (Znth best rows nil))
        (string_of_list_z (Znth k rows nil)))).

Lemma rows_well_formed_Znth_158 : forall rows n i,
  rows_well_formed_158 rows n ->
  0 <= i < n ->
  row_well_formed_158 (Znth i rows nil).
Proof.
  intros rows n i Hrows Hi.
  unfold rows_well_formed_158 in Hrows.
  destruct Hrows as [Hlen Hforall].
  apply Forall_forall with (x := Znth i rows nil) in Hforall; auto.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma string_le_refl_158 : forall s, string_le s s.
Proof.
  intros s. unfold string_le. left. reflexivity.
Qed.

Lemma string_le_trans_158 : forall a b c,
  string_le a b -> string_le b c -> string_le a c.
Proof.
  intros a b c Hab Hbc.
  unfold string_le in *.
  destruct Hab as [Hab | Hab]; destruct Hbc as [Hbc | Hbc].
  - left. congruence.
  - subst. right. exact Hbc.
  - subst. right. exact Hab.
  - right. eapply String_as_OT.lt_trans; eauto.
Qed.

Lemma string_of_list_z_lt_at_nat_158 : forall a b n,
  (forall k, (k < n)%nat ->
    nth k (c_string a) 0 = nth k (c_string b) 0) ->
  nth n (c_string a) 0 < nth n (c_string b) 0 ->
  (forall k, (k < List.length a)%nat -> 0 < nth k a 0 < 256) ->
  (forall k, (k < List.length b)%nat -> 0 < nth k b 0 < 256) ->
  String_as_OT.lt (string_of_list_z a) (string_of_list_z b).
Proof.
  induction a as [| ah tl IH]; intros b n Hpref Hlt Ha Hb;
    destruct b as [| bh br]; destruct n as [| n]; simpl in *.
  - lia.
  - lia.
  - apply String_as_OT.lts_empty.
  - specialize (Hpref 0%nat ltac:(lia)). simpl in Hpref.
    pose proof (Hb 0%nat ltac:(lia)) as Hbh. lia.
  - pose proof (Ha 0%nat ltac:(lia)) as Hah. lia.
  - pose proof (Ha 0%nat ltac:(lia)) as Hah.
    specialize (Hpref 0%nat ltac:(lia)). simpl in Hpref. lia.
  - apply String_as_OT.lts_head.
    assert (Ha0 : 0 <= ah < 256).
    { pose proof (Ha 0%nat ltac:(lia)) as H. lia. }
    assert (Hb0 : 0 <= bh < 256).
    { pose proof (Hb 0%nat ltac:(lia)) as H. lia. }
    rewrite !nat_of_ascii_ascii_of_z by lia.
    lia.
  - assert (Heq_head : ah = bh).
    { specialize (Hpref 0%nat ltac:(lia)). simpl in Hpref. lia. }
    subst bh.
    apply String_as_OT.lts_tail.
    apply (IH br n).
    + intros k Hk.
      specialize (Hpref (S k) ltac:(lia)).
      simpl in Hpref. exact Hpref.
    + exact Hlt.
    + intros k Hk.
      pose proof (Ha (S k) ltac:(simpl; lia)) as H.
      simpl in H. exact H.
    + intros k Hk.
      pose proof (Hb (S k) ltac:(simpl; lia)) as H.
      simpl in H. exact H.
Qed.

Lemma nth_Znth_nonneg_158 : forall {A : Type} (l : list A) n d,
  nth n l d = Znth (Z.of_nat n) l d.
Proof.
  intros A l n d.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma row_well_formed_nth_strict_158 : forall row n,
  (n < List.length row)%nat ->
  row_well_formed_158 row ->
  0 < nth n row 0 < 256.
Proof.
  intros row n Hn Hwf.
  unfold row_well_formed_158 in Hwf.
  destruct Hwf as [Hvalid _].
  unfold SimpleC.StdLib.string_lib.valid_string,
    SimpleC.StdLib.string_lib.all_ascii,
    SimpleC.StdLib.string_lib.no_inner_nul in Hvalid.
  destruct Hvalid as [Hascii Hno_nul].
  pose proof (Hascii (Z.of_nat n)) as Hrange.
  assert (Hidx : 0 <= Z.of_nat n < Zlength row).
  { rewrite Zlength_correct. lia. }
  specialize (Hrange Hidx).
  pose proof (Hno_nul (Z.of_nat n) Hidx) as Hnz.
  rewrite <- nth_Znth_nonneg_158 in Hrange, Hnz.
  lia.
Qed.

Lemma list_eq_by_nth_158 : forall a b,
  List.length a = List.length b ->
  (forall k, (k < List.length a)%nat -> nth k a 0 = nth k b 0) ->
  a = b.
Proof.
  induction a as [| ah tl IH]; intros b Hlen Hnth; destruct b as [| bh br]; simpl in *; try lia.
  - reflexivity.
  - assert (ah = bh) by (specialize (Hnth 0%nat ltac:(lia)); simpl in Hnth; exact Hnth).
    subst bh. f_equal.
    apply IH.
    + lia.
    + intros k Hk.
      specialize (Hnth (S k) ltac:(simpl; lia)).
      simpl in Hnth. exact Hnth.
Qed.

Lemma c_string_zero_row_well_formed_length_158 : forall row i,
  row_well_formed_158 row ->
  0 <= i <= SimpleC.StdLib.string_lib.string_length row ->
  Znth i (c_string row) 0 = 0 ->
  i = SimpleC.StdLib.string_lib.string_length row.
Proof.
  intros row i Hwf Hi Hzero.
  unfold row_well_formed_158 in Hwf.
  destruct Hwf as [Hvalid _].
  pose proof (SimpleC.StdLib.string_lib.c_string_zero_index_eq_length
    row i Hvalid ltac:(lia) ltac:(lia) Hzero) as H.
  exact H.
Qed.

Lemma string_of_list_z_eq_of_c_prefix_158 : forall a b i,
  row_well_formed_158 a ->
  row_well_formed_158 b ->
  0 <= i <= SimpleC.StdLib.string_lib.string_length a ->
  i <= SimpleC.StdLib.string_lib.string_length b ->
  (forall k, 0 <= k < i -> Znth k (c_string a) 0 = Znth k (c_string b) 0) ->
  Znth i (c_string a) 0 = 0 ->
  Znth i (c_string b) 0 = 0 ->
  string_of_list_z a = string_of_list_z b.
Proof.
  intros a b i Hwa Hwb Hia Hib Hpref Ha0 Hb0.
  assert (Hia_len : i = string_length a).
  { apply c_string_zero_row_well_formed_length_158; auto. }
  assert (Hib_len : i = string_length b).
  { apply c_string_zero_row_well_formed_length_158; auto; lia. }
  assert (Hlen : List.length a = List.length b).
  { unfold string_length in *. rewrite !Zlength_correct in *. lia. }
  assert (Heql : a = b).
  {
    apply list_eq_by_nth_158; auto.
    intros k Hk.
    rewrite !nth_Znth_nonneg_158.
    pose proof (Hpref (Z.of_nat k)) as Hc.
    assert (Hki : 0 <= Z.of_nat k < i).
    { rewrite Hia_len. unfold string_length. rewrite Zlength_correct. lia. }
    specialize (Hc Hki).
    unfold c_string in Hc.
    rewrite !app_Znth1 in Hc by (rewrite Zlength_correct; lia).
    exact Hc.
  }
  subst. reflexivity.
Qed.

Lemma string_of_list_z_lt_at_158 : forall a b i,
  row_well_formed_158 a ->
  row_well_formed_158 b ->
  0 <= i <= SimpleC.StdLib.string_lib.string_length a ->
  i <= SimpleC.StdLib.string_lib.string_length b ->
  (forall k, 0 <= k < i -> Znth k (c_string a) 0 = Znth k (c_string b) 0) ->
  Znth i (c_string a) 0 < Znth i (c_string b) 0 ->
  String_as_OT.lt (string_of_list_z a) (string_of_list_z b).
Proof.
  intros a b i Hwa Hwb Hia Hib Hpref Hlt.
  pose (n := Z.to_nat i).
  apply (string_of_list_z_lt_at_nat_158 a b n).
  - subst n. intros k Hk.
    rewrite !nth_Znth_nonneg_158.
    apply Hpref. lia.
  - subst n.
    rewrite !nth_Znth_nonneg_158.
    replace (Z.of_nat (Z.to_nat i)) with i by lia.
    exact Hlt.
  - intros k Hk. apply row_well_formed_nth_strict_158; auto.
  - intros k Hk. apply row_well_formed_nth_strict_158; auto.
Qed.

Lemma strcmp_result_nonneg_string_le_158 : forall a b cmp,
  row_well_formed_158 a ->
  row_well_formed_158 b ->
  strcmp_result a b cmp ->
  cmp >= 0 ->
  string_le (string_of_list_z b) (string_of_list_z a).
Proof.
  intros a b cmp Hwa Hwb Hcmp Hge.
  unfold strcmp_result in Hcmp.
  destruct Hcmp as (i & Hia & Hib & Hpref & Hret & Hstop).
  set (ca := Znth i (c_string a) 0) in *.
  set (cb := Znth i (c_string b) 0) in *.
  assert (Hret' : cmp = ca - cb) by (subst ca cb; exact Hret).
  assert (Hcb_le_ca : cb <= ca) by lia.
  destruct (Z.eq_dec cb ca) as [Heq | Hneq].
  - assert (Ha0 : ca = 0).
    { destruct Hstop as [Ha0 | Hdiff]; [exact Ha0 | exfalso; apply Hdiff; lia]. }
    assert (Hb0 : cb = 0) by lia.
    unfold string_le. left.
    eapply string_of_list_z_eq_of_c_prefix_158 with (i := i).
    + exact Hwb.
    + exact Hwa.
    + split; [lia | exact Hib].
    + destruct Hia as [_ Hia_upper]. exact Hia_upper.
    + intros k Hk. symmetry. apply Hpref. exact Hk.
    + subst cb. exact Hb0.
    + subst ca. exact Ha0.
  - assert (Hlt : cb < ca) by lia.
    unfold string_le. right.
    eapply string_of_list_z_lt_at_158 with (i := i).
    + exact Hwb.
    + exact Hwa.
    + split; [lia | exact Hib].
    + destruct Hia as [_ Hia_upper]. exact Hia_upper.
    + intros k Hk. symmetry. apply Hpref. exact Hk.
    + subst cb ca. exact Hlt.
Qed.

Lemma strcmp_result_neg_string_le_158 : forall a b cmp,
  row_well_formed_158 a ->
  row_well_formed_158 b ->
  strcmp_result a b cmp ->
  cmp < 0 ->
  string_le (string_of_list_z a) (string_of_list_z b).
Proof.
  intros a b cmp Hwa Hwb Hcmp Hlt_cmp.
  unfold strcmp_result in Hcmp.
  destruct Hcmp as (i & Hia & Hib & Hpref & Hret & Hstop).
  set (ca := Znth i (c_string a) 0) in *.
  set (cb := Znth i (c_string b) 0) in *.
  assert (Hret' : cmp = ca - cb) by (subst ca cb; exact Hret).
  assert (Hlt : ca < cb) by lia.
  unfold string_le. right.
  eapply string_of_list_z_lt_at_158 with (i := i); eauto.
Qed.

Lemma seen_scan_unique_nonneg_158 : forall l seen u,
  0 <= u ->
  0 <= snd (fold_left seen_step_158 l (seen, u)).
Proof.
  induction l as [| ch tl IH]; intros seen u Hu; simpl.
  - exact Hu.
  - unfold seen_step_158. simpl.
    destruct (Z.eq_dec (Znth ch seen 0) 0).
    + apply IH. lia.
    + apply IH. lia.
Qed.

Lemma unique_count_nonneg_158 : forall row,
  0 <= unique_count_z_158 row.
Proof.
  intros row. unfold unique_count_z_158, seen_scan_158.
  apply seen_scan_unique_nonneg_158. lia.
Qed.

Definition seen_rep_158 (seen done : list Z) : Prop :=
  forall ch, 0 <= ch < 256 ->
    (Znth ch seen 0 <> 0 <-> In ch done).

Definition seen_inv_158 (seen done : list Z) : Prop :=
  Zlength seen = 256 /\ seen_rep_158 seen done.

Definition unique_count_list_z_158 (done : list Z) : Z :=
  Z.of_nat (List.length (nodup Z.eq_dec done)).

Lemma seen_inv_init_158 :
  seen_inv_158 (repeat_Z 0 256) [].
Proof.
  unfold seen_inv_158, seen_rep_158, repeat_Z. split.
  - rewrite Zlength_correct, repeat_length. reflexivity.
  - intros ch Hch. rewrite Znth_repeat_lt by lia. split; intros H; simpl in *; tauto.
Qed.

Lemma seen_inv_mark_new_158 : forall seen done ch,
  seen_inv_158 seen done ->
  0 <= ch < 256 ->
  Znth ch seen 0 = 0 ->
  seen_inv_158 (replace_Znth ch 1 seen) (ch :: done).
Proof.
  intros seen done ch [Hlen Hrep] Hch Hzero.
  split.
  - rewrite Zlength_replace_Znth. exact Hlen.
  - intros x Hx. split; intros H.
    + destruct (Z.eq_dec x ch) as [Heq | Hneq].
      * subst. simpl. auto.
      * simpl. right. apply Hrep; auto.
        rewrite Znth_replace_Znth_Diff in H by lia. exact H.
    + simpl in H. destruct H as [Hxch | Hdone].
      * subst x. rewrite Znth_replace_Znth_Same by lia. lia.
      * destruct (Z.eq_dec x ch) as [Heq | Hneq].
        -- subst x. rewrite Znth_replace_Znth_Same by lia. lia.
        -- rewrite Znth_replace_Znth_Diff by lia.
           apply Hrep; auto.
Qed.

Lemma seen_inv_mark_old_158 : forall seen done ch,
  seen_inv_158 seen done ->
  0 <= ch < 256 ->
  Znth ch seen 0 <> 0 ->
  seen_inv_158 seen (ch :: done).
Proof.
  intros seen done ch [Hlen Hrep] Hch Hseen.
  split; [exact Hlen|].
  intros x Hx. split; intros H.
  - simpl. destruct (Z.eq_dec x ch) as [Heq | Hneq].
    + subst. auto.
    + right. apply Hrep; auto.
  - simpl in H. destruct H as [Hxch | Hdone].
    + subst. exact Hseen.
    + apply Hrep; auto.
Qed.

Lemma unique_count_cons_new_158 : forall ch done,
  ~ In ch done ->
  unique_count_list_z_158 (ch :: done) =
    unique_count_list_z_158 done + 1.
Proof.
  intros ch done Hnotin.
  unfold unique_count_list_z_158. simpl.
  destruct (in_dec Z.eq_dec ch done) as [Hin | Hnin]; [contradiction|].
  simpl. lia.
Qed.

Lemma unique_count_cons_old_158 : forall ch done,
  In ch done ->
  unique_count_list_z_158 (ch :: done) =
    unique_count_list_z_158 done.
Proof.
  intros ch done Hin.
  unfold unique_count_list_z_158. simpl.
  destruct (in_dec Z.eq_dec ch done) as [_ | Hnin]; [reflexivity|contradiction].
Qed.

Lemma seen_step_count_158 : forall seen done ch u,
  seen_inv_158 seen done ->
  0 <= ch < 256 ->
  u = unique_count_list_z_158 done ->
  let st := seen_step_158 (seen, u) ch in
  seen_inv_158 (fst st) (ch :: done) /\
  snd st = unique_count_list_z_158 (ch :: done).
Proof.
  intros seen done ch u Hinv Hch Hu.
  unfold seen_step_158. simpl.
  destruct (Z.eq_dec (Znth ch seen 0) 0) as [Hzero | Hnonzero].
  - split.
    + apply seen_inv_mark_new_158; auto.
    + rewrite Hu. rewrite unique_count_cons_new_158.
      * reflexivity.
      * intro Hin.
        destruct Hinv as [_ Hrep].
        pose proof (proj2 (Hrep ch Hch) Hin) as Hseen.
        congruence.
  - split.
    + apply seen_inv_mark_old_158; auto.
    + rewrite Hu. symmetry. apply unique_count_cons_old_158.
      destruct Hinv as [_ Hrep].
      apply Hrep; auto.
Qed.

Lemma nodup_length_perm_158 : forall l1 l2,
  Permutation l1 l2 ->
  List.length (nodup Z.eq_dec l1) =
  List.length (nodup Z.eq_dec l2).
Proof.
  intros l1 l2 Hperm.
  apply Nat.le_antisymm;
    apply NoDup_incl_length.
  - apply NoDup_nodup.
  - intros x Hin. rewrite nodup_In in *.
    apply (Permutation_in x Hperm). exact Hin.
  - apply NoDup_nodup.
  - intros x Hin. rewrite nodup_In in *.
    apply (Permutation_in x (Permutation_sym Hperm)). exact Hin.
Qed.

Lemma unique_count_list_z_perm_158 : forall l1 l2,
  Permutation l1 l2 ->
  unique_count_list_z_158 l1 = unique_count_list_z_158 l2.
Proof.
  intros l1 l2 Hperm.
  unfold unique_count_list_z_158.
  rewrite (nodup_length_perm_158 l1 l2 Hperm).
  reflexivity.
Qed.

Lemma seen_fold_count_158 : forall l seen u done,
  (forall ch, In ch l -> 0 <= ch < 256) ->
  seen_inv_158 seen done ->
  u = unique_count_list_z_158 done ->
  snd (fold_left seen_step_158 l (seen, u)) =
    unique_count_list_z_158 (rev l ++ done).
Proof.
  induction l as [| ch tl IH]; intros seen u done Hrange Hinv Hu; simpl.
  - subst u. simpl. reflexivity.
  - pose proof (seen_step_count_158 seen done ch u Hinv
      ltac:(apply Hrange; simpl; auto) Hu) as Hstep.
    set (st := seen_step_158 (seen, u) ch) in *.
    destruct st as [seen1 u1].
    destruct Hstep as [Hinv' Hu'].
    rewrite (IH seen1 u1 (ch :: done)).
    + replace (rev tl ++ ch :: done) with (rev (ch :: tl) ++ done) by
        (simpl; rewrite <- app_assoc; reflexivity).
      reflexivity.
    + intros x Hx. apply Hrange. simpl. auto.
    + exact Hinv'.
    + exact Hu'.
Qed.

Lemma unique_count_z_nodup_z_158 : forall row,
  row_well_formed_158 row ->
  unique_count_z_158 row = unique_count_list_z_158 row.
Proof.
  intros row Hwf.
  unfold unique_count_z_158, seen_scan_158.
  rewrite sublist_self by reflexivity.
  rewrite seen_fold_count_158 with (done := (@nil Z)).
  - rewrite app_nil_r.
    apply unique_count_list_z_perm_158.
    apply Permutation_sym. apply Permutation_rev.
  - intros ch Hin.
    unfold row_well_formed_158 in Hwf.
    destruct Hwf as [Hvalid _].
    unfold SimpleC.StdLib.string_lib.valid_string,
      SimpleC.StdLib.string_lib.all_ascii in Hvalid.
    destruct Hvalid as [Hascii _].
    apply In_nth with (d := 0) in Hin.
    destruct Hin as [n [Hn Hnth]].
    pose proof (Hascii (Z.of_nat n)) as Hrange.
    assert (Hidx : 0 <= Z.of_nat n < Zlength row).
    { rewrite Zlength_correct. lia. }
    specialize (Hrange Hidx).
    rewrite <- nth_Znth_nonneg_158 in Hrange.
    rewrite Hnth in Hrange. lia.
  - apply seen_inv_init_158.
  - reflexivity.
Qed.

Lemma ascii_of_z_inj_158 : forall x y,
  0 <= x < 256 ->
  0 <= y < 256 ->
  ascii_of_z x = ascii_of_z y ->
  x = y.
Proof.
  intros x y Hx Hy H.
  apply f_equal with (f := nat_of_ascii) in H.
  rewrite !nat_of_ascii_ascii_of_z in H by assumption.
  lia.
Qed.

Lemma NoDup_map_ascii_of_z_158 : forall l,
  (forall x, In x l -> 0 <= x < 256) ->
  NoDup l ->
  NoDup (map ascii_of_z l).
Proof.
  intros l Hrange Hnd.
  induction Hnd as [| x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hy Hiny]].
      apply ascii_of_z_inj_158 in Hy; try (apply Hrange; simpl; auto).
      subst y. contradiction.
    + apply IH. intros y Hy. apply Hrange. simpl; auto.
Qed.

Lemma nodup_ascii_length_eq_z_158 : forall row,
  (forall x, In x row -> 0 <= x < 256) ->
  List.length (nodup Ascii.ascii_dec (map ascii_of_z row)) =
  List.length (nodup Z.eq_dec row).
Proof.
  intros row Hrange.
  set (zu := nodup Z.eq_dec row).
  set (au := nodup Ascii.ascii_dec (map ascii_of_z row)).
  assert (Hz_nd : NoDup zu) by (subst zu; apply NoDup_nodup).
  assert (Ha_nd : NoDup au) by (subst au; apply NoDup_nodup).
  assert (Hzu_range : forall x, In x zu -> 0 <= x < 256).
  { intros x Hin. apply Hrange. subst zu. rewrite nodup_In in Hin. exact Hin. }
  assert (Hmap_nd : NoDup (map ascii_of_z zu)).
  { apply NoDup_map_ascii_of_z_158; auto. }
  assert (Hle1 : Nat.le (List.length (map ascii_of_z zu)) (List.length au)).
  {
    apply NoDup_incl_length; auto.
    intros a Hin.
    apply in_map_iff in Hin.
    destruct Hin as [z [Hz Hinz]].
    subst a. subst au.
    rewrite nodup_In, in_map_iff.
    exists z. split; auto.
    subst zu. rewrite nodup_In in Hinz. exact Hinz.
  }
  assert (Hle2 : Nat.le (List.length au) (List.length (map ascii_of_z zu))).
  {
    apply NoDup_incl_length; auto.
    intros a Hin.
    subst au. rewrite nodup_In in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [z [Hz Hzin]].
    subst a. apply in_map.
    subst zu. rewrite nodup_In. exact Hzin.
  }
  rewrite map_length in Hle1, Hle2.
  lia.
Qed.

Lemma unique_count_z_spec_count_158 : forall row,
  row_well_formed_158 row ->
  unique_count_z_158 row =
    Z.of_nat (count_unique_chars (string_of_list_z row)).
Proof.
  intros row Hwf.
  rewrite unique_count_z_nodup_z_158 by exact Hwf.
  unfold unique_count_list_z_158, count_unique_chars.
  rewrite list_ascii_of_string_string_of_list_z.
  f_equal.
  symmetry.
  apply nodup_ascii_length_eq_z_158.
  intros x Hin.
  unfold row_well_formed_158 in Hwf.
  destruct Hwf as [Hvalid _].
  unfold SimpleC.StdLib.string_lib.valid_string,
    SimpleC.StdLib.string_lib.all_ascii in Hvalid.
  destruct Hvalid as [Hascii _].
  apply In_nth with (d := 0) in Hin.
  destruct Hin as [n [Hn Hnth]].
  pose proof (Hascii (Z.of_nat n)) as Hrange.
  assert (Hidx : 0 <= Z.of_nat n < Zlength row).
  { rewrite Zlength_correct. lia. }
  specialize (Hrange Hidx).
  rewrite <- nth_Znth_nonneg_158 in Hrange.
  rewrite Hnth in Hrange. lia.
Qed.

Lemma best_state_problem_spec_z_158 : forall rows n best maxu,
  rows_well_formed_158 rows n ->
  problem_158_pre_z rows ->
  0 < n ->
  0 <= best < n ->
  best_state_158 rows n best maxu ->
  problem_158_spec_z rows (Znth best rows nil).
Proof.
  intros rows n best maxu Hrows Hpre Hn Hbest_range Hstate.
  unfold problem_158_spec_z, problem_158_spec, rows_to_strings_z_158.
  split.
  - apply in_map.
    unfold Znth.
    apply nth_In.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    unfold rows_well_formed_158 in Hrows. lia.
  - intros w Hw.
    apply in_map_iff in Hw.
    destruct Hw as [row [Hw_eq Hrow_in]].
    subst w.
    apply In_nth with (d := nil) in Hrow_in.
    destruct Hrow_in as [k_nat [Hk_len Hk_nth]].
    set (k := Z.of_nat k_nat).
    assert (Hk_range : 0 <= k < n).
    {
      subst k.
      assert (Hlen_rows : Zlength rows = n).
      { unfold rows_well_formed_158 in Hrows. tauto. }
      rewrite Zlength_correct in Hlen_rows. lia.
    }
    assert (Hrow_eq : row = Znth k rows nil).
    {
      subst k. rewrite <- nth_Znth_nonneg_158. symmetry. exact Hk_nth.
    }
    subst row.
    unfold best_state_158 in Hstate.
    destruct Hstate as [(Hn0 & _ & _) | (_ & _ & Hmaxu & Hall)].
    { lia. }
    specialize (Hall k Hk_range).
    pose proof (rows_well_formed_Znth_158 rows n best Hrows Hbest_range) as Hbest_wf.
    pose proof (rows_well_formed_Znth_158 rows n k Hrows Hk_range) as Hk_wf.
    rewrite (unique_count_z_spec_count_158 (Znth best rows nil) Hbest_wf) in Hall.
    rewrite (unique_count_z_spec_count_158 (Znth k rows nil) Hk_wf) in Hall.
    rewrite Hrow_eq.
    destruct Hall as [Hgt | [Heq Hlex]].
    + left. apply Nat2Z.inj_gt. exact Hgt.
    + right. split; [apply Nat2Z.inj; exact Heq | exact Hlex].
Qed.

Lemma best_state_bounds_158 : forall rows i best maxu n,
  0 <= i < n ->
  0 < n ->
  best_state_158 rows i best maxu ->
  0 <= best /\ best < n.
Proof.
  intros rows i best maxu n Hi Hn Hbest.
  unfold best_state_158 in Hbest.
  destruct Hbest as [(Hi0 & Hbest0 & _) | (_ & Hbest_range & _)].
  - subst. lia.
  - lia.
Qed.

Lemma best_state_before_i_158 : forall rows i best maxu,
  best_state_158 rows i best maxu ->
  i <> best ->
  0 <= best /\ best < i.
Proof.
  intros rows i best maxu Hbest Hneq.
  unfold best_state_158 in Hbest.
  destruct Hbest as [(Hi & Hb & _) | (_ & Hrange & _)].
  - subst. contradiction.
  - lia.
Qed.

Lemma best_state_keep_self_158 : forall rows i best maxu unique,
  i = best ->
  unique = maxu ->
  unique = unique_count_z_158 (Znth i rows nil) ->
  0 <= i ->
  best_state_158 rows i best maxu ->
  best_state_158 rows (i + 1) best maxu.
Proof.
  intros rows i best maxu unique Hi_best Huniq_max Huniq Hi_nonneg Hstate.
  unfold best_state_158 in *.
  destruct Hstate as [(Hi0 & Hb0 & Hm0) | (Hi0 & Hbest_range & Hmaxu & Hall)].
  - subst i best maxu.
    right. repeat split; try lia.
    intros k Hk.
    assert (k = 0) by lia. subst k.
    right. split; [lia | apply string_le_refl_158].
  - lia.
Qed.

Lemma best_state_keep_lower_158 : forall rows i best maxu unique,
  unique <> maxu ->
  unique <= maxu ->
  unique = unique_count_z_158 (Znth i rows nil) ->
  0 <= i ->
  best_state_158 rows i best maxu ->
  best_state_158 rows (i + 1) best maxu.
Proof.
  intros rows i best maxu unique Hneq Hle Huniq Hi_nonneg Hstate.
  assert (Hlt : unique < maxu) by lia.
  unfold best_state_158 in *.
  destruct Hstate as [(Hi0 & Hb0 & Hm0) | (Hi0 & Hbest_range & Hmaxu & Hall)].
  - subst i best maxu.
    pose proof (unique_count_nonneg_158 (Znth 0 rows nil)).
    lia.
  - right. repeat split; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + apply Hall. lia.
    + assert (k = i) by lia. subst k.
      left. lia.
Qed.

Lemma best_state_keep_tie_158 : forall rows i best maxu unique,
  unique = maxu ->
  unique = unique_count_z_158 (Znth i rows nil) ->
  0 <= best ->
  best < i ->
  i >= 0 ->
  string_le (string_of_list_z (Znth best rows nil))
            (string_of_list_z (Znth i rows nil)) ->
  best_state_158 rows i best maxu ->
  best_state_158 rows (i + 1) best maxu.
Proof.
  intros rows i best maxu unique Huniq_max Huniq Hb0 Hbi Hi_nonneg Hlex Hstate.
  unfold best_state_158 in *.
  destruct Hstate as [(Hi0 & Hb_init & Hm0) | (Hi0 & Hbest_range & Hmaxu & Hall)].
  - lia.
  - right. repeat split; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + apply Hall. lia.
    + assert (k = i) by lia. subst k.
      right. split; [lia | exact Hlex].
Qed.

Lemma best_state_update_tie_158 : forall rows i best maxu unique,
  unique = maxu ->
  unique = unique_count_z_158 (Znth i rows nil) ->
  0 <= best ->
  best < i ->
  i >= 0 ->
  string_le (string_of_list_z (Znth i rows nil))
            (string_of_list_z (Znth best rows nil)) ->
  best_state_158 rows i best maxu ->
  best_state_158 rows (i + 1) i unique.
Proof.
  intros rows i best maxu unique Huniq_max Huniq Hb0 Hbi Hi_nonneg Hlex Hstate.
  unfold best_state_158 in *.
  destruct Hstate as [(Hi0 & Hb_init & Hm0) | (Hi0 & Hbest_range & Hmaxu & Hall)].
  - lia.
  - right. repeat split; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + specialize (Hall k ltac:(lia)).
      destruct Hall as [Hgt | [Heq Hbest_le_k]].
      * left. lia.
      * right. split; [lia |].
        eapply string_le_trans_158; eauto.
    + assert (k = i) by lia. subst k.
      right. split; [lia | apply string_le_refl_158].
Qed.

Lemma best_state_update_strict_158 : forall rows i best maxu unique,
  unique > maxu ->
  unique = unique_count_z_158 (Znth i rows nil) ->
  0 <= i ->
  best_state_158 rows i best maxu ->
  best_state_158 rows (i + 1) i unique.
Proof.
  intros rows i best maxu unique Hgt Huniq Hi_nonneg Hstate.
  unfold best_state_158 in *.
  destruct Hstate as [(Hi0 & Hb_init & Hm0) | (Hi0 & Hbest_range & Hmaxu & Hall)].
  - subst i best maxu.
    right. repeat split; try lia.
    intros k Hk.
    assert (k = 0) by lia. subst k.
    right. split; [lia | apply string_le_refl_158].
  - right. repeat split; try lia.
    intros k Hk.
    destruct (Z_lt_ge_dec k i) as [Hki | Hki].
    + specialize (Hall k ltac:(lia)).
      destruct Hall as [Hprev_gt | [Hprev_eq _]].
      * left. lia.
      * left. lia.
    + assert (k = i) by lia. subst k.
      right. split; [lia | apply string_le_refl_158].
Qed.

Lemma Znth_In_range_158 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma row_well_formed_char_range_158 : forall row j,
  row_well_formed_158 row ->
  0 <= j < string_length row ->
  0 <= Znth j row 0 < 256.
Proof.
  intros row j Hwf Hj.
  unfold row_well_formed_158 in Hwf.
  destruct Hwf as [Hvalid _].
  unfold SimpleC.StdLib.string_lib.valid_string,
    SimpleC.StdLib.string_lib.all_ascii in Hvalid.
  destruct Hvalid as [Hascii _].
  pose proof (Hascii j ltac:(unfold string_length in Hj; lia)) as Hrange.
  lia.
Qed.

Lemma sublist_snoc_158 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (@sublist_single Z 0 i l) by lia.
  reflexivity.
Qed.

Lemma seen_state_init_158 : forall row,
  seen_state_158 row 0 (repeat_Z 0 256) 0.
Proof.
  intros row. unfold seen_state_158, seen_scan_158.
  replace (sublist 0 0 row) with (@nil Z) by (symmetry; apply sublist_nil; lia).
  reflexivity.
Qed.

Lemma seen_state_step_zero_158 : forall row j seen unique ch,
  0 <= j < Zlength row ->
  ch = Znth j row 0 ->
  seen_state_158 row j seen unique ->
  Znth ch seen 0 = 0 ->
  seen_state_158 row (j + 1) (replace_Znth ch 1 seen) (unique + 1).
Proof.
  intros row j seen unique ch Hj Hch Hstate Hzero.
  unfold seen_state_158, seen_scan_158 in *.
  rewrite sublist_snoc_158 by exact Hj.
  rewrite fold_left_app. simpl.
  rewrite Hstate. unfold seen_step_158. simpl.
  rewrite <- Hch.
  destruct (Z.eq_dec (Znth ch seen 0) 0); congruence.
Qed.

Lemma seen_state_step_nonzero_158 : forall row j seen unique ch,
  0 <= j < Zlength row ->
  ch = Znth j row 0 ->
  seen_state_158 row j seen unique ->
  Znth ch seen 0 <> 0 ->
  seen_state_158 row (j + 1) seen unique.
Proof.
  intros row j seen unique ch Hj Hch Hstate Hnonzero.
  unfold seen_state_158, seen_scan_158 in *.
  rewrite sublist_snoc_158 by exact Hj.
  rewrite fold_left_app. simpl.
  rewrite Hstate. unfold seen_step_158. simpl.
  rewrite <- Hch.
  destruct (Z.eq_dec (Znth ch seen 0) 0); congruence.
Qed.

Lemma seen_state_done_158 : forall row j seen unique,
  j = Zlength row ->
  seen_state_158 row j seen unique ->
  unique = unique_count_z_158 row.
Proof.
  intros row j seen unique Hj Hstate.
  subst j. unfold seen_state_158, unique_count_z_158 in *.
  rewrite Hstate. reflexivity.
Qed.

Lemma Zlength_firstn_158 : forall {A : Type} (l : list A) i,
  0 <= i <= Zlength l ->
  Zlength (firstn (Z.to_nat i) l) = i.
Proof.
  intros A l i Hi. rewrite Zlength_correct, firstn_length.
  rewrite Nat.min_l.
  - rewrite Z2Nat.id by lia. reflexivity.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia.
Qed.

Lemma Zlength_remove_Znth_158 : forall {A : Type} i (l : list A),
  0 <= i < Zlength l ->
  Zlength (CharPtrArray2.remove_Znth i l) = Zlength l - 1.
Proof.
  intros A i l Hi. unfold CharPtrArray2.remove_Znth.
  rewrite Zlength_app, Zlength_firstn_158 by lia.
  rewrite Zlength_correct, skipn_length.
  rewrite Nat2Z.inj_sub by (apply Nat2Z.inj_le;
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia;
    rewrite <- Zlength_correct; lia).
  rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma Znth_firstn_158 : forall {A : Type} n (l : list A) i d,
  0 <= i < Z.of_nat n ->
  Znth i (firstn n l) d = Znth i l d.
Proof.
  intros A n l i d Hi. unfold Znth.
  rewrite List.nth_firstn.
  destruct (Z.to_nat i <? n)%nat eqn:Hcmp; auto.
  apply Nat.ltb_ge in Hcmp. lia.
Qed.

Lemma Znth_remove_Znth_before_158 : forall {A : Type} i k (l : list A) d,
  0 <= k < i -> i < Zlength l ->
  Znth k (CharPtrArray2.remove_Znth i l) d = Znth k l d.
Proof.
  intros A i k l d Hki Hil.
  unfold CharPtrArray2.remove_Znth.
  rewrite app_Znth1.
  - apply Znth_firstn_158. lia.
  - rewrite Zlength_firstn_158 by lia. lia.
Qed.

Lemma row_stores_split_i_158 : forall ptrs rows i,
  0 <= i < Zlength ptrs -> Zlength ptrs = Zlength rows ->
  row_stores_158 ptrs rows |--
    SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil) **
    row_stores_missing_i_158 ptrs rows i.
Proof.
  intros ptrs rows i Hi Hlen.
  unfold row_stores_158, row_stores_missing_i_158.
  assert (Hc : 0 <= i < Zlength (combine ptrs rows)).
  { rewrite CharPtrArray2.Zlength_combine_eq by exact Hlen. lia. }
  sep_apply (CharPtrArray2.iter_sepcon_split_remove_Znth
    row_store_pair_158 i (combine ptrs rows) (0, nil) Hc).
  rewrite CharPtrArray2.Znth_combine by lia. unfold row_store_pair_158. simpl. entailer!.
Qed.

Lemma row_stores_merge_i_158 : forall ptrs rows i,
  0 <= i < Zlength ptrs -> Zlength ptrs = Zlength rows ->
  SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil) **
  row_stores_missing_i_158 ptrs rows i |-- row_stores_158 ptrs rows.
Proof.
  intros ptrs rows i Hi Hlen.
  unfold row_stores_158, row_stores_missing_i_158.
  assert (Hc : 0 <= i < Zlength (combine ptrs rows)).
  { rewrite CharPtrArray2.Zlength_combine_eq by exact Hlen. lia. }
  assert (HZnth :
    Znth i (combine ptrs rows) (0, nil) =
    (Znth i ptrs 0, Znth i rows nil)).
  { apply CharPtrArray2.Znth_combine; lia. }
  change (SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil))
    with (row_store_pair_158 (Znth i ptrs 0, Znth i rows nil)).
  rewrite <- HZnth.
  change (row_store_pair_158 (Znth i (combine ptrs rows) (0, nil)) **
    iter_sepcon (map row_store_pair_158
      (CharPtrArray2.remove_Znth i (combine ptrs rows))) |--
    iter_sepcon (map row_store_pair_158 (combine ptrs rows))).
  sep_apply (CharPtrArray2.iter_sepcon_merge_remove_Znth
    row_store_pair_158 i (combine ptrs rows) (Znth i (combine ptrs rows) (0,nil)) Hc).
  rewrite replace_Znth_Znth by exact Hc.
  entailer!.
Qed.

Lemma row_stores_split_two_158 : forall ptrs rows best i,
  0 <= best /\ best < i /\ i < Zlength ptrs -> Zlength ptrs = Zlength rows ->
  row_stores_158 ptrs rows |--
    SimpleC.StdLib.string_lib.store_string (Znth best ptrs 0) (Znth best rows nil) **
    SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil) **
    row_stores_missing_two_158 ptrs rows best i.
Proof.
  intros ptrs rows best i Hbi Hlen.
  destruct Hbi as (Hb0 & Hbi & Hi).
  eapply derivable1_trans.
  { apply (row_stores_split_i_158 ptrs rows i); [lia | exact Hlen]. }
  unfold row_stores_missing_i_158, row_stores_missing_two_158.
  assert (Hc : 0 <= i < Zlength (combine ptrs rows)).
  { rewrite CharPtrArray2.Zlength_combine_eq by exact Hlen. lia. }
  assert (Hb : 0 <= best < Zlength
    (CharPtrArray2.remove_Znth i (combine ptrs rows))).
  { rewrite Zlength_remove_Znth_158 by exact Hc. lia. }
  sep_apply (CharPtrArray2.iter_sepcon_split_remove_Znth
    row_store_pair_158 best
    (CharPtrArray2.remove_Znth i (combine ptrs rows)) (0,nil) Hb).
  rewrite Znth_remove_Znth_before_158 by lia.
  rewrite CharPtrArray2.Znth_combine by lia. unfold row_store_pair_158. simpl. entailer!.
Qed.

Lemma row_stores_merge_two_158 : forall ptrs rows best i,
  0 <= best /\ best < i /\ i < Zlength ptrs -> Zlength ptrs = Zlength rows ->
  SimpleC.StdLib.string_lib.store_string (Znth best ptrs 0) (Znth best rows nil) **
  SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil) **
  row_stores_missing_two_158 ptrs rows best i |-- row_stores_158 ptrs rows.
Proof.
  intros ptrs rows best i Hbi Hlen.
  destruct Hbi as (Hb0 & Hbi & Hi).
  unfold row_stores_missing_two_158.
  assert (Hc : 0 <= i < Zlength (combine ptrs rows)).
  { rewrite CharPtrArray2.Zlength_combine_eq by exact Hlen. lia. }
  assert (Hb : 0 <= best < Zlength
    (CharPtrArray2.remove_Znth i (combine ptrs rows))).
  { rewrite Zlength_remove_Znth_158 by exact Hc. lia. }
  assert (HZnth :
    Znth best (CharPtrArray2.remove_Znth i (combine ptrs rows)) (0, nil) =
    (Znth best ptrs 0, Znth best rows nil)).
  {
    rewrite Znth_remove_Znth_before_158 by lia.
    apply CharPtrArray2.Znth_combine; lia.
  }
  change (SimpleC.StdLib.string_lib.store_string (Znth best ptrs 0) (Znth best rows nil))
    with (row_store_pair_158 (Znth best ptrs 0, Znth best rows nil)).
  rewrite <- HZnth.
  change (row_store_pair_158
    (Znth best (CharPtrArray2.remove_Znth i (combine ptrs rows)) (0, nil)) **
    SimpleC.StdLib.string_lib.store_string (Znth i ptrs 0) (Znth i rows nil) **
    iter_sepcon (map row_store_pair_158
      (CharPtrArray2.remove_Znth best
        (CharPtrArray2.remove_Znth i (combine ptrs rows)))) |--
    iter_sepcon (map row_store_pair_158 (combine ptrs rows))).
  sep_apply (CharPtrArray2.iter_sepcon_merge_remove_Znth
    row_store_pair_158 best
    (CharPtrArray2.remove_Znth i (combine ptrs rows))
    (Znth best (CharPtrArray2.remove_Znth i (combine ptrs rows)) (0,nil)) Hb).
  rewrite replace_Znth_Znth by exact Hb.
  fold (row_stores_missing_i_158 ptrs rows i).
  rewrite derivable1_sepcon_comm.
  apply (row_stores_merge_i_158 ptrs rows i); [lia | exact Hlen].
Qed.
