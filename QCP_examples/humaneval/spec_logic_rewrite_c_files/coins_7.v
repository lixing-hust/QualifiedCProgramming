Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.StdLib Require Import string_lib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Load "../spec/7".
Load "../StringClaude/string_bridge".

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition row_payload_z_7 (row : list Z) : list Z :=
  removelast row.

Definition row_well_formed_7 (row : list Z) : Prop :=
  row = c_string (row_payload_z_7 row) /\
  valid_string (row_payload_z_7 row) /\
  string_length (row_payload_z_7 row) < INT_MAX.

Definition rows_well_formed_7 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\ Forall row_well_formed_7 rows.

Definition rows_to_strings_z_7 (rows : list (list Z)) : list string :=
  map (fun row => string_of_list_z (row_payload_z_7 row)) rows.

Definition problem_7_pre_z (rows : list (list Z)) : Prop :=
  problem_7_pre.

Definition problem_7_spec_z
    (rows : list (list Z)) (substring : list Z)
    (output : list (list Z)) : Prop :=
  problem_7_spec
    (rows_to_strings_z_7 rows)
    (map string_of_list_z output)
    (string_of_list_z substring).

Definition substring_hit_z_7 (str sub : list Z) : Prop :=
  exists i, substring_at str sub i.

Definition substring_miss_z_7 (str sub : list Z) : Prop :=
  ~ substring_hit_z_7 str sub.

Inductive filter_by_substring_z_7
    : list (list Z) -> list Z -> list (list Z) -> Prop :=
| fbsz_nil : forall sub,
    filter_by_substring_z_7 [] sub []
| fbsz_keep : forall h t sub output,
    substring_hit_z_7 h sub ->
    filter_by_substring_z_7 t sub output ->
    filter_by_substring_z_7 (h :: t) sub (h :: output)
| fbsz_drop : forall h t sub output,
    ~ substring_hit_z_7 h sub ->
    filter_by_substring_z_7 t sub output ->
    filter_by_substring_z_7 (h :: t) sub output.

Definition filter_substring_state_7
    (rows : list (list Z)) (sub : list Z) (i : Z)
    (output : list (list Z)) : Prop :=
  filter_by_substring_z_7
    (map row_payload_z_7 (sublist 0 i rows)) sub output.

Lemma removelast_app_single_7 : forall {A : Type} (l : list A) x,
  removelast (l ++ [x]) = l.
Proof.
  intros A l x. induction l as [|a l IH]; simpl; auto.
  destruct l; simpl in *; congruence.
Qed.

Lemma row_payload_c_string_7 : forall payload,
  row_payload_z_7 (c_string payload) = payload.
Proof.
  intros payload. unfold row_payload_z_7, c_string.
  apply removelast_app_single_7.
Qed.

Lemma c_string_Zlength_7 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload. unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma rows_well_formed_length_7 : forall rows n,
  rows_well_formed_7 rows n -> Zlength rows = n.
Proof. intros rows n [H _]; exact H. Qed.

Lemma rows_well_formed_nth_7 : forall rows n i,
  rows_well_formed_7 rows n ->
  0 <= i < n ->
  row_well_formed_7 (Znth i rows []).
Proof.
  intros rows n i [Hlen Hall] Hi.
  rewrite Forall_forall in Hall. apply Hall.
  unfold Znth. apply nth_In.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma string_of_list_z_app_7 : forall a b,
  string_of_list_z (a ++ b) =
  (string_of_list_z a ++ string_of_list_z b)%string.
Proof.
  induction a as [|x a IH]; intros b; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma substring_at_decompose_7 : forall str sub i,
  substring_at str sub i ->
  exists pre suf, str = pre ++ sub ++ suf.
Proof.
  intros str sub i [Hi [Hend Hpoint]].
  unfold string_length in Hi, Hend, Hpoint.
  pose proof (Zlength_nonneg sub) as Hsub_len.
  exists (sublist 0 i str), (sublist (i + Zlength sub) (Zlength str) str).
  assert (Hmid : sublist i (i + Zlength sub) str = sub).
  {
    apply (proj2 (list_eq_ext (sublist i (i + Zlength sub) str) sub 0)).
    split.
    - rewrite Zlength_sublist.
      + lia.
      + split.
        * split; [exact (proj1 Hi) | lia].
        * exact Hend.
    - intros k Hk.
      assert (Hk' : 0 <= k < Zlength sub).
      { pose proof (Zlength_sublist i (i + Zlength sub) str) as Hlenmid.
        specialize (Hlenmid ltac:(split; [split; [exact (proj1 Hi) | lia] | exact Hend])).
        rewrite Hlenmid in Hk. lia. }
      rewrite Znth_sublist.
      2: exact (proj1 Hi).
      2: lia.
      replace (k + i) with (i + k) by lia.
      apply Hpoint. exact Hk'.
  }
  assert (Hself : sublist 0 (Zlength str) str = str).
  { apply sublist_self. reflexivity. }
  rewrite <- Hself at 1.
  rewrite (sublist_split 0 (Zlength str) i str).
  2: { split; lia. }
  2: { split; lia. }
  rewrite (sublist_split i (Zlength str) (i + Zlength sub) str).
  2: { split; lia. }
  2: { split; lia. }
  rewrite Hmid.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma decompose_substring_at_7 : forall str sub pre suf,
  str = pre ++ sub ++ suf ->
  substring_at str sub (Zlength pre).
Proof.
  intros str sub pre suf ->.
  unfold substring_at, string_length.
  pose proof (Zlength_nonneg pre).
  pose proof (Zlength_nonneg sub).
  pose proof (Zlength_nonneg suf).
  repeat split.
  - lia.
  - rewrite !Zlength_app. lia.
  - rewrite !Zlength_app. lia.
  - intros k Hk.
    rewrite app_Znth2 by lia.
    replace (Zlength pre + k - Zlength pre) with k by lia.
    rewrite app_Znth1 by exact Hk.
    reflexivity.
Qed.

Definition z_of_ascii_7 (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Lemma list_ascii_of_string_app_7 : forall a b,
  list_ascii_of_string (a ++ b) =
  (list_ascii_of_string a ++ list_ascii_of_string b)%list.
Proof.
  induction a; intros b; simpl; auto.
  rewrite IHa. reflexivity.
Qed.

Lemma map_z_ascii_inverse_7 : forall l,
  all_ascii l ->
  map z_of_ascii_7 (map ascii_of_z l) = l.
Proof.
  induction l as [|x l IH]; intros Hall; simpl; auto.
  f_equal.
  - unfold z_of_ascii_7.
    assert (Hx : 0 <= x < 256).
    { specialize (Hall 0). rewrite Znth0_cons in Hall.
      specialize (Hall ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia)).
      lia. }
    rewrite nat_of_ascii_ascii_of_z by exact Hx.
    rewrite Z2Nat.id by lia. reflexivity.
  - apply IH. intros i Hi.
    specialize (Hall (i + 1)).
    rewrite Znth_cons in Hall by lia.
    replace (i + 1 - 1) with i in Hall by lia.
    apply Hall. rewrite Zlength_cons. lia.
Qed.

Lemma substring_hit_string_7 : forall str sub,
  all_ascii str ->
  all_ascii sub ->
  substring_hit_z_7 str sub <->
  contains_substring (string_of_list_z str) (string_of_list_z sub).
Proof.
  intros str sub Hstr Hsub. split.
  - intros [i Hi].
    destruct (substring_at_decompose_7 str sub i Hi) as [pre [suf ->]].
    exists (string_of_list_z pre), (string_of_list_z suf).
    rewrite !string_of_list_z_app_7. reflexivity.
  - intros [pre [suf H]].
    apply (f_equal list_ascii_of_string) in H.
    rewrite list_ascii_of_string_string_of_list_z in H.
    rewrite !list_ascii_of_string_app_7 in H.
    rewrite list_ascii_of_string_string_of_list_z in H.
    apply (f_equal (map z_of_ascii_7)) in H.
    rewrite !map_app in H.
    rewrite (map_z_ascii_inverse_7 str Hstr) in H.
    rewrite (map_z_ascii_inverse_7 sub Hsub) in H.
    exists (Zlength (map z_of_ascii_7 (list_ascii_of_string pre))).
    apply decompose_substring_at_7 with
      (pre := map z_of_ascii_7 (list_ascii_of_string pre))
      (suf := map z_of_ascii_7 (list_ascii_of_string suf)).
    exact H.
Qed.

Lemma filter_substring_state_nil_7 : forall rows sub,
  filter_substring_state_7 rows sub 0 [].
Proof.
  intros rows sub. unfold filter_substring_state_7.
  simpl [sublist]. constructor.
Qed.

Lemma filter_by_substring_z_snoc_keep_7 : forall input sub output h,
  filter_by_substring_z_7 input sub output ->
  substring_hit_z_7 h sub ->
  filter_by_substring_z_7 (input ++ [h]) sub (output ++ [h]).
Proof.
  intros input sub output h Hfilter Hhit.
  induction Hfilter; simpl.
  - constructor; [exact Hhit | constructor].
  - constructor; auto.
  - apply fbsz_drop; auto.
Qed.

Lemma filter_by_substring_z_snoc_drop_7 : forall input sub output h,
  filter_by_substring_z_7 input sub output ->
  ~ substring_hit_z_7 h sub ->
  filter_by_substring_z_7 (input ++ [h]) sub output.
Proof.
  intros input sub output h Hfilter Hmiss.
  induction Hfilter; simpl.
  - apply fbsz_drop; [exact Hmiss | constructor].
  - constructor; auto.
  - apply fbsz_drop; auto.
Qed.

Lemma filter_substring_state_keep_7 : forall rows sub i output,
  0 <= i < Zlength rows ->
  filter_substring_state_7 rows sub i output ->
  substring_hit_z_7 (row_payload_z_7 (Znth i rows [])) sub ->
  filter_substring_state_7 rows sub (i + 1)
    (output ++ [row_payload_z_7 (Znth i rows [])]).
Proof.
  intros rows sub i output Hi Hstate Hhit.
  unfold filter_substring_state_7 in *.
  rewrite (sublist_split 0 (i + 1) i rows) by lia.
  rewrite (@sublist_single (list Z) [] i rows) by lia. simpl.
  rewrite map_app. simpl.
  apply filter_by_substring_z_snoc_keep_7; assumption.
Qed.

Lemma filter_substring_state_drop_7 : forall rows sub i output,
  0 <= i < Zlength rows ->
  filter_substring_state_7 rows sub i output ->
  ~ substring_hit_z_7 (row_payload_z_7 (Znth i rows [])) sub ->
  filter_substring_state_7 rows sub (i + 1) output.
Proof.
  intros rows sub i output Hi Hstate Hmiss.
  unfold filter_substring_state_7 in *.
  rewrite (sublist_split 0 (i + 1) i rows) by lia.
  rewrite (@sublist_single (list Z) [] i rows) by lia. simpl.
  rewrite map_app. simpl.
  apply filter_by_substring_z_snoc_drop_7; assumption.
Qed.

Lemma strstr_result_hit_7 : forall str sub ret base,
  strstr_result str sub ret base ->
  ret <> 0 -> substring_hit_z_7 str sub.
Proof.
  intros str sub ret base [Hhit | [Hnone ->]] Hret.
  - destruct Hhit as [i [Hi _]]. exists i. exact Hi.
  - contradiction.
Qed.

Lemma strstr_result_miss_7 : forall str sub ret base,
  strstr_result str sub ret base ->
  ret = 0 -> ~ substring_hit_z_7 str sub.
Proof.
  intros str sub ret base [Hhit | [Hnone _]] Hzero [i Hi].
  - destruct Hhit as [j [_ [_ [Hret Hnz]]]]. subst ret. contradiction.
  - apply (Hnone i (proj1 Hi)). exact Hi.
Qed.

Lemma filter_by_substring_z_sound_7 : forall input sub output,
  Forall all_ascii input ->
  all_ascii sub ->
  filter_by_substring_z_7 input sub output ->
  filter_by_substring
    (map string_of_list_z input)
    (string_of_list_z sub)
    (map string_of_list_z output).
Proof.
  intros input sub output Hinput Hsub Hfilter.
  induction Hfilter; simpl in *.
  - constructor.
  - inversion Hinput; subst.
    constructor.
    + apply (proj1 (substring_hit_string_7 h sub H2 Hsub)); exact H.
    + apply IHHfilter; assumption.
  - apply fbsr_drop.
    + inversion Hinput; subst.
      intro Hcontains. apply H.
      apply (proj2 (substring_hit_string_7 h sub H2 Hsub)); exact Hcontains.
    + inversion Hinput; subst. apply IHHfilter; assumption.
Qed.

Lemma rows_well_formed_payload_ascii_7 : forall rows n,
  rows_well_formed_7 rows n ->
  Forall all_ascii (map row_payload_z_7 rows).
Proof.
  intros rows n [_ Hall].
  induction Hall; simpl; constructor; auto.
  unfold row_well_formed_7 in H.
  destruct H as [_ [[Hascii _] _]]. exact Hascii.
Qed.

Lemma problem_7_spec_z_of_filter_state : forall rows sub output,
  rows_well_formed_7 rows (Zlength rows) ->
  valid_string sub ->
  filter_substring_state_7 rows sub (Zlength rows) output ->
  problem_7_spec_z rows sub output.
Proof.
  intros rows sub output Hrows [Hsub _] Hstate.
  unfold filter_substring_state_7 in Hstate.
  rewrite sublist_self in Hstate by reflexivity.
  unfold problem_7_spec_z, problem_7_spec, rows_to_strings_z_7.
  rewrite <- map_map.
  apply filter_by_substring_z_sound_7.
  - apply rows_well_formed_payload_ascii_7 with (n := Zlength rows).
    exact Hrows.
  - exact Hsub.
  - exact Hstate.
Qed.
