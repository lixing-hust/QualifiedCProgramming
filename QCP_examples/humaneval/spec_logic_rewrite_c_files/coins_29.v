Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.StdLib Require Import string_lib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Load "../spec/29".
Load "../StringClaude/string_bridge".

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition row_payload_z_29 (row : list Z) : list Z := removelast row.

Definition row_well_formed_29 (row : list Z) : Prop :=
  row = c_string (row_payload_z_29 row) /\
  valid_string (row_payload_z_29 row) /\
  string_length (row_payload_z_29 row) < INT_MAX.

Definition rows_well_formed_29 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\ Forall row_well_formed_29 rows.

Definition rows_to_strings_z_29 (rows : list (list Z)) : list string :=
  map (fun row => string_of_list_z (row_payload_z_29 row)) rows.

Definition problem_29_pre_z (rows : list (list Z)) : Prop :=
  problem_29_pre (rows_to_strings_z_29 rows).

Definition problem_29_spec_z
    (rows : list (list Z)) (prefix : list Z)
    (output : list (list Z)) : Prop :=
  problem_29_spec
    (rows_to_strings_z_29 rows)
    (string_of_list_z prefix)
    (map string_of_list_z output).

Definition prefix_hit_z_29 (row prefix : list Z) : Prop :=
  exists suffix, row = prefix ++ suffix.

Definition prefix_miss_z_29 (row prefix : list Z) : Prop :=
  ~ prefix_hit_z_29 row prefix.

Inductive filter_by_prefix_z_29
    : list (list Z) -> list Z -> list (list Z) -> Prop :=
| fbpz29_nil : forall prefix,
    filter_by_prefix_z_29 [] prefix []
| fbpz29_keep : forall h t prefix output,
    prefix_hit_z_29 h prefix ->
    filter_by_prefix_z_29 t prefix output ->
    filter_by_prefix_z_29 (h :: t) prefix (h :: output)
| fbpz29_drop : forall h t prefix output,
    prefix_miss_z_29 h prefix ->
    filter_by_prefix_z_29 t prefix output ->
    filter_by_prefix_z_29 (h :: t) prefix output.

Definition filter_prefix_state_29
    (rows : list (list Z)) (prefix : list Z) (i : Z)
    (output : list (list Z)) : Prop :=
  filter_by_prefix_z_29
    (map row_payload_z_29 (sublist 0 i rows)) prefix output.

Lemma removelast_app_single_29 : forall {A : Type} (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros A l x. induction l as [|a l IH]; simpl; auto.
  destruct l; simpl in *; congruence.
Qed.

Lemma row_payload_c_string_29 : forall payload,
  row_payload_z_29 (c_string payload) = payload.
Proof.
  intros payload. unfold row_payload_z_29, c_string.
  apply removelast_app_single_29.
Qed.

Lemma c_string_Zlength_29 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload. unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma rows_well_formed_length_29 : forall rows n,
  rows_well_formed_29 rows n -> Zlength rows = n.
Proof. intros rows n [Hlen _]. exact Hlen. Qed.

Lemma rows_well_formed_nth_29 : forall rows n i,
  rows_well_formed_29 rows n ->
  0 <= i < n ->
  row_well_formed_29 (Znth i rows []).
Proof.
  intros rows n i [Hlen Hall] Hi.
  rewrite Forall_forall in Hall. apply Hall.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma string_of_list_z_app_29 : forall a b,
  string_of_list_z (a ++ b) =
  (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a as [|x a IH]; intros b; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma prefix_hit_string_29 : forall row prefix,
  prefix_hit_z_29 row prefix ->
  String.prefix (string_of_list_z prefix) (string_of_list_z row) = true.
Proof.
  intros row prefix [suffix ->].
  induction prefix as [|x prefix IH].
  - destruct suffix; reflexivity.
  - cbn [List.app string_of_list_z String.prefix].
    destruct (ascii_dec (ascii_of_z x) (ascii_of_z x)); congruence.
Qed.

Lemma valid_string_tail_29 : forall x l,
  valid_string (x :: l) -> valid_string l.
Proof.
  intros x l [Hascii Hnul]. split.
  - intros i Hi. specialize (Hascii (i + 1)).
    rewrite Znth_cons in Hascii by lia.
    replace (i + 1 - 1) with i in Hascii by lia.
    apply Hascii. rewrite Zlength_cons. lia.
  - intros i Hi. specialize (Hnul (i + 1)).
    rewrite Znth_cons in Hnul by lia.
    replace (i + 1 - 1) with i in Hnul by lia.
    apply Hnul. rewrite Zlength_cons. lia.
Qed.

Lemma valid_string_head_range_29 : forall x l,
  valid_string (x :: l) -> 0 <= x <= 127.
Proof.
  intros x l [Hascii _]. specialize (Hascii 0).
  rewrite Znth0_cons in Hascii. apply Hascii.
  rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
Qed.

Lemma ascii_of_z_inj_29 : forall x y,
  0 <= x <= 127 -> 0 <= y <= 127 ->
  ascii_of_z x = ascii_of_z y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite !nat_of_ascii_ascii_of_z in Heq by lia.
  apply (f_equal Z.of_nat) in Heq.
  rewrite !Z2Nat.id in Heq by lia. exact Heq.
Qed.

Lemma prefix_string_hit_29 : forall row prefix,
  valid_string row -> valid_string prefix ->
  String.prefix (string_of_list_z prefix) (string_of_list_z row) = true ->
  prefix_hit_z_29 row prefix.
Proof.
  induction row as [|r row IH]; intros [|p prefix] Hrow Hprefix Hhit.
  - exists []; reflexivity.
  - simpl in Hhit. discriminate.
  - exists (r :: row). reflexivity.
  - simpl in Hhit.
    destruct (ascii_dec (ascii_of_z p) (ascii_of_z r)) as [Heq | Hneq].
    + assert (Hp := valid_string_head_range_29 p prefix Hprefix).
      assert (Hr := valid_string_head_range_29 r row Hrow).
      assert (p = r) by (apply ascii_of_z_inj_29; auto).
      subst r.
      destruct (IH prefix (valid_string_tail_29 p row Hrow)
                  (valid_string_tail_29 p prefix Hprefix) Hhit)
        as [suffix Hsuffix].
      exists suffix. simpl. f_equal. exact Hsuffix.
    + discriminate.
Qed.

Lemma prefix_hit_sublist_29 : forall row prefix,
  prefix_hit_z_29 row prefix ->
  sublist 0 (Zlength prefix) row = prefix.
Proof.
  intros row prefix [suffix ->].
  rewrite (sublist_split_app_l 0 (Zlength prefix) prefix suffix).
  2: { pose proof (Zlength_nonneg prefix); lia. }
  2: lia.
  apply sublist_self. reflexivity.
Qed.

Lemma equal_prefix_sublist_hit_29 : forall row prefix,
  Zlength prefix <= Zlength row ->
  (forall k, 0 <= k < Zlength prefix -> Znth k row 0 = Znth k prefix 0) ->
  prefix_hit_z_29 row prefix.
Proof.
  intros row prefix Hlen Heq.
  pose proof (Zlength_nonneg row) as Hrow_nonneg.
  pose proof (Zlength_nonneg prefix) as Hprefix_nonneg.
  assert (Hsub : sublist 0 (Zlength prefix) row = prefix).
  {
    apply (proj2 (list_eq_ext _ _ 0)). split.
    - rewrite Zlength_sublist by lia. lia.
    - intros k Hk.
      rewrite Zlength_sublist in Hk by lia.
      rewrite Znth_sublist by lia.
      replace (k + 0) with k by lia.
      apply Heq. lia.
  }
  exists (sublist (Zlength prefix) (Zlength row) row).
  transitivity
    (sublist 0 (Zlength prefix) row ++
     sublist (Zlength prefix) (Zlength row) row).
  - rewrite <- (sublist_split 0 (Zlength row) (Zlength prefix) row) by lia.
    symmetry. apply sublist_self. reflexivity.
  - rewrite Hsub. reflexivity.
Qed.

Lemma strncmp_zero_prefix_hit_29 : forall row prefix n,
  valid_string row -> valid_string prefix ->
  n = string_length prefix ->
  strncmp_result row prefix n 0 ->
  prefix_hit_z_29 row prefix.
Proof.
  intros row prefix n Hrow Hprefix Hn [i [Hi [Hirow [Hiprefix [Heq Hcase]]]]].
  subst n. unfold string_length in *.
  destruct Hcase as [[Hin _] | [Hilt [Hret Hstop]]].
  - subst i. apply equal_prefix_sublist_hit_29; [lia|].
    intros k Hk. specialize (Heq k Hk).
    rewrite !c_string_Znth_inside in Heq.
    2: { unfold string_length. lia. }
    2: { unfold string_length. lia. }
    exact Heq.
  - assert (Hz : Znth i (c_string row) 0 = Znth i (c_string prefix) 0)
      by lia.
    destruct Hstop as [Hrowzero | Hneq]; [|congruence].
    assert (Hprefixzero : Znth i (c_string prefix) 0 = 0) by lia.
    pose proof (c_string_zero_index_eq_length row i Hrow (proj1 Hi) Hirow Hrowzero)
      as Hirowlen.
    pose proof (c_string_zero_index_eq_length prefix i Hprefix (proj1 Hi) Hiprefix Hprefixzero)
      as Hiprelen.
    unfold string_length in Hirowlen, Hiprelen.
    lia.
Qed.

Lemma prefix_hit_strncmp_zero_29 : forall row prefix n ret,
  prefix_hit_z_29 row prefix ->
  n = string_length prefix ->
  strncmp_result row prefix n ret ->
  ret = 0.
Proof.
  intros row prefix n ret Hhit Hn [i [Hi [Hirow [Hiprefix [Heq Hcase]]]]].
  subst n. unfold string_length in *.
  destruct Hcase as [[Hin Hret] | [Hilt [Hret Hstop]]]; auto.
  assert (Hlen : Zlength prefix <= Zlength row).
  { destruct Hhit as [suffix Hsuffix].
    pose proof (Zlength_nonneg suffix). rewrite Hsuffix, Zlength_app. lia. }
  assert (Hsub := prefix_hit_sublist_29 row prefix Hhit).
  assert (Hchars : Znth i row 0 = Znth i prefix 0).
  {
    apply (f_equal (fun l => Znth i l 0)) in Hsub.
    rewrite Znth_sublist in Hsub by lia.
    replace (i + 0) with i in Hsub by lia. exact Hsub.
  }
  rewrite !c_string_Znth_inside in Hret.
  2: { unfold string_length. lia. }
  2: { unfold string_length. lia. }
  lia.
Qed.

Lemma strncmp_nonzero_prefix_miss_29 : forall row prefix n ret,
  n = string_length prefix ->
  strncmp_result row prefix n ret ->
  ret <> 0 ->
  prefix_miss_z_29 row prefix.
Proof.
  intros row prefix n ret Hn Hres Hnz Hhit.
  apply Hnz. eapply prefix_hit_strncmp_zero_29; eauto.
Qed.

Lemma filter_prefix_state_nil_29 : forall rows prefix,
  filter_prefix_state_29 rows prefix 0 [].
Proof.
  intros rows prefix. unfold filter_prefix_state_29.
  simpl [sublist]. constructor.
Qed.

Lemma filter_by_prefix_snoc_keep_29 : forall input prefix output h,
  filter_by_prefix_z_29 input prefix output ->
  prefix_hit_z_29 h prefix ->
  filter_by_prefix_z_29 (input ++ [h]) prefix (output ++ [h]).
Proof.
  intros input prefix output h Hfilter Hhit.
  induction Hfilter; simpl.
  - constructor; [exact Hhit | constructor].
  - constructor; auto.
  - apply fbpz29_drop; auto.
Qed.

Lemma filter_by_prefix_snoc_drop_29 : forall input prefix output h,
  filter_by_prefix_z_29 input prefix output ->
  prefix_miss_z_29 h prefix ->
  filter_by_prefix_z_29 (input ++ [h]) prefix output.
Proof.
  intros input prefix output h Hfilter Hmiss.
  induction Hfilter; simpl.
  - apply fbpz29_drop; [exact Hmiss | constructor].
  - constructor; auto.
  - apply fbpz29_drop; auto.
Qed.

Lemma filter_prefix_state_keep_29 : forall rows prefix i output,
  0 <= i < Zlength rows ->
  filter_prefix_state_29 rows prefix i output ->
  prefix_hit_z_29 (row_payload_z_29 (Znth i rows [])) prefix ->
  filter_prefix_state_29 rows prefix (i + 1)
    (output ++ [row_payload_z_29 (Znth i rows [])]).
Proof.
  intros rows prefix i output Hi Hstate Hhit.
  unfold filter_prefix_state_29 in *.
  rewrite (sublist_split 0 (i + 1) i rows) by lia.
  rewrite (@sublist_single (list Z) [] i rows) by lia.
  rewrite map_app. simpl.
  apply filter_by_prefix_snoc_keep_29; auto.
Qed.

Lemma filter_prefix_state_drop_29 : forall rows prefix i output,
  0 <= i < Zlength rows ->
  filter_prefix_state_29 rows prefix i output ->
  prefix_miss_z_29 (row_payload_z_29 (Znth i rows [])) prefix ->
  filter_prefix_state_29 rows prefix (i + 1) output.
Proof.
  intros rows prefix i output Hi Hstate Hmiss.
  unfold filter_prefix_state_29 in *.
  rewrite (sublist_split 0 (i + 1) i rows) by lia.
  rewrite (@sublist_single (list Z) [] i rows) by lia.
  rewrite map_app. simpl.
  apply filter_by_prefix_snoc_drop_29; auto.
Qed.

Lemma filter_by_prefix_to_filter_29 : forall input prefix output,
  Forall valid_string input -> valid_string prefix ->
  filter_by_prefix_z_29 input prefix output ->
  map string_of_list_z output =
  filter (String.prefix (string_of_list_z prefix))
         (map string_of_list_z input).
Proof.
  intros input prefix output Hvalid Hprefix Hfilter.
  induction Hfilter; inversion Hvalid; subst; simpl.
  - reflexivity.
  - rewrite (prefix_hit_string_29 _ _ H). simpl.
    f_equal. apply IHHfilter; auto.
  - assert (Hfalse :
        String.prefix (string_of_list_z prefix) (string_of_list_z h) = false).
    {
      destruct (String.prefix (string_of_list_z prefix) (string_of_list_z h))
        eqn:Htest; auto.
      exfalso. apply H.
      eapply prefix_string_hit_29; eauto.
    }
    rewrite Hfalse. apply IHHfilter; auto.
Qed.

Lemma rows_payloads_valid_29 : forall rows,
  Forall row_well_formed_29 rows ->
  Forall valid_string (map row_payload_z_29 rows).
Proof.
  intros rows Hall. induction Hall; simpl; constructor; auto.
  destruct H as [_ [Hvalid _]]. exact Hvalid.
Qed.

Lemma filter_prefix_state_final_29 : forall rows n prefix output,
  rows_well_formed_29 rows n -> valid_string prefix ->
  filter_prefix_state_29 rows prefix n output ->
  problem_29_spec_z rows prefix output.
Proof.
  intros rows n prefix output [Hlen Hall] Hprefix Hstate.
  unfold filter_prefix_state_29 in Hstate.
  rewrite <- Hlen in Hstate.
  rewrite sublist_self in Hstate by reflexivity.
  unfold problem_29_spec_z, problem_29_spec, rows_to_strings_z_29.
  replace (map (fun row : list Z => string_of_list_z (row_payload_z_29 row)) rows)
    with (map string_of_list_z (map row_payload_z_29 rows)).
  2: { rewrite map_map. reflexivity. }
  eapply filter_by_prefix_to_filter_29; eauto.
  apply rows_payloads_valid_29. exact Hall.
Qed.
