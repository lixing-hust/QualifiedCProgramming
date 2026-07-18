Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.StdLib Require Import string_lib.

Load "../spec/154".

Import ListNotations.
Local Open Scope Z_scope.

Definition ascii_of_z_154 (z : Z) : ascii :=
  ascii_of_N (Z.to_N z).

Fixpoint string_of_list_z_154 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | z :: tl => String (ascii_of_z_154 z) (string_of_list_z_154 tl)
  end.

Definition bool_of_z_154 (z : Z) : bool := Z.eqb z 1.

Definition problem_154_pre_z (a b : list Z) : Prop :=
  problem_154_pre (string_of_list_z_154 a) (string_of_list_z_154 b).

Definition problem_154_spec_z (a b : list Z) (res : Z) : Prop :=
  problem_154_spec
    (string_of_list_z_154 a)
    (string_of_list_z_154 b)
    (bool_of_z_154 res).

Definition rotate_at_154 (b : list Z) (i : Z) : list Z :=
  sublist i (Zlength b) b ++ sublist 0 i b.

Definition rotation_prefix_154
    (b : list Z) (i j : Z) (out : list Z) : Prop :=
  0 <= i < Zlength b /\
  0 <= j <= Zlength b /\
  out = sublist 0 j (rotate_at_154 b i).

Definition rotation_scan_state_154
    (a b : list Z) (i : Z) : Prop :=
  0 <= i <= Zlength b /\
  forall r out,
    0 <= r < i ->
    rotation_prefix_154 b r (Zlength b) out ->
    forall pos, 0 <= pos <= Zlength a -> ~ substring_at a out pos.

Definition rotation_success_154
    (a b : list Z) (i : Z) (out : list Z) : Prop :=
  rotation_prefix_154 b i (Zlength b) out /\
  exists pos, substring_at a out pos.

Lemma rotate_at_154_length : forall b i,
  0 <= i <= Zlength b ->
  Zlength (rotate_at_154 b i) = Zlength b.
Proof.
  intros b i Hi.
  unfold rotate_at_154.
  rewrite Zlength_app.
  rewrite !Zlength_sublist by lia.
  lia.
Qed.

Lemma rotation_prefix_154_zero : forall b i,
  0 <= i < Zlength b ->
  rotation_prefix_154 b i 0 [].
Proof.
  intros b i Hi.
  unfold rotation_prefix_154.
  repeat split; try lia.
Qed.

Lemma rotate_at_154_Znth : forall b i j,
  0 <= i < Zlength b ->
  0 <= j < Zlength b ->
  Znth j (rotate_at_154 b i) 0 =
  Znth ((i + j) mod Zlength b) b 0.
Proof.
  intros b i j Hi Hj.
  unfold rotate_at_154.
  assert (Hlen1 : Zlength (sublist i (Zlength b) b) = Zlength b - i).
  { rewrite Zlength_sublist by lia. lia. }
  destruct (Z_lt_ge_dec j (Zlength b - i)) as [Hleft | Hright].
  - rewrite app_Znth1 by lia.
    rewrite Znth_sublist by lia.
    rewrite Z.mod_small by lia.
    f_equal; lia.
  - rewrite app_Znth2 by lia.
    rewrite Hlen1.
    rewrite Znth_sublist by lia.
    assert (Hmod : (i + j) mod Zlength b = i + j - Zlength b).
    { replace (i + j) with ((i + j - Zlength b) + 1 * Zlength b) by lia.
      rewrite Z.mod_add by lia.
      rewrite Z.mod_small by lia.
      lia. }
    rewrite Hmod.
    f_equal; lia.
Qed.

Lemma rotation_prefix_154_step : forall b i j out ch,
  rotation_prefix_154 b i j out ->
  j < Zlength b ->
  ch = Znth ((i + j) mod Zlength b) b 0 ->
  rotation_prefix_154 b i (j + 1) (out ++ [ch]).
Proof.
  intros b i j out ch Hpref Hj Hch.
  unfold rotation_prefix_154 in *.
  destruct Hpref as [Hi [Hjb Hout]].
  repeat split; try lia.
  subst out.
  rewrite (sublist_split 0 (j + 1) j (rotate_at_154 b i)) by
      (try lia; rewrite rotate_at_154_length; lia).
  rewrite (sublist_single 0 j (rotate_at_154 b i)) by
      (rewrite rotate_at_154_length; lia).
  rewrite rotate_at_154_Znth by lia.
  now subst ch.
Qed.

Lemma all_ascii_rotate_at_154 : forall b i,
  all_ascii b ->
  0 <= i <= Zlength b ->
  all_ascii (rotate_at_154 b i).
Proof.
  intros b i Hall Hi k Hk.
  destruct (Z.eq_dec i (Zlength b)) as [-> | Hne].
  - assert (Hkb : 0 <= k < Zlength b).
    { rewrite rotate_at_154_length in Hk by lia; exact Hk. }
    unfold rotate_at_154.
    rewrite sublist_self by reflexivity.
    assert (Hempty : sublist (Zlength b) (Zlength b) b = []).
    { apply length_zero_iff_nil.
      pose proof (Zlength_sublist (Zlength b) (Zlength b) b ltac:(lia)).
      rewrite Zlength_correct in H; lia. }
    rewrite Hempty; simpl.
    apply Hall; exact Hkb.
  - assert (Hkb : 0 <= k < Zlength b).
    { rewrite rotate_at_154_length in Hk by lia; exact Hk. }
    rewrite rotate_at_154_Znth by lia.
    apply Hall.
    apply Z.mod_pos_bound; lia.
Qed.

Lemma no_inner_nul_rotate_at_154 : forall b i,
  no_inner_nul b ->
  0 <= i <= Zlength b ->
  no_inner_nul (rotate_at_154 b i).
Proof.
  intros b i Hnul Hi k Hk.
  destruct (Z.eq_dec i (Zlength b)) as [-> | Hne].
  - assert (Hkb : 0 <= k < Zlength b).
    { rewrite rotate_at_154_length in Hk by lia; exact Hk. }
    unfold rotate_at_154.
    rewrite sublist_self by reflexivity.
    assert (Hempty : sublist (Zlength b) (Zlength b) b = []).
    { apply length_zero_iff_nil.
      pose proof (Zlength_sublist (Zlength b) (Zlength b) b ltac:(lia)).
      rewrite Zlength_correct in H; lia. }
    rewrite Hempty; simpl.
    apply Hnul; exact Hkb.
  - assert (Hkb : 0 <= k < Zlength b).
    { rewrite rotate_at_154_length in Hk by lia; exact Hk. }
    rewrite rotate_at_154_Znth by lia.
    apply Hnul.
    apply Z.mod_pos_bound; lia.
Qed.

Lemma valid_string_rotate_at_154 : forall b i,
  valid_string b ->
  0 <= i <= Zlength b ->
  valid_string (rotate_at_154 b i).
Proof.
  intros b i [Hall Hnul] Hi; split.
  - now apply all_ascii_rotate_at_154.
  - now apply no_inner_nul_rotate_at_154.
Qed.

Lemma rotation_scan_state_154_zero : forall a b,
  rotation_scan_state_154 a b 0.
Proof.
  intros a b.
  unfold rotation_scan_state_154.
  split; [pose proof (Zlength_nonneg b); lia |].
  intros r out Hr; lia.
Qed.

Lemma strstr_result_154_success : forall a out ret base,
  ret <> 0 ->
  strstr_result a out ret base ->
  exists pos, substring_at a out pos.
Proof.
  intros a out ret base Hret Hstr.
  unfold strstr_result in Hstr.
  destruct Hstr as [[pos [Hsub [_ [_ Hnz]]]] | [_ Hzero]].
  - now exists pos.
  - contradiction.
Qed.

Lemma rotation_scan_state_154_step : forall a b i out ret base,
  rotation_scan_state_154 a b i ->
  rotation_prefix_154 b i (Zlength b) out ->
  ret = 0 ->
  strstr_result a out ret base ->
  rotation_scan_state_154 a b (i + 1).
Proof.
  intros a b i out ret base Hscan Hpref Hret Hstr.
  pose proof Hpref as Hpref_bounds.
  unfold rotation_prefix_154 in Hpref_bounds.
  destruct Hpref_bounds as [Hib _].
  unfold rotation_scan_state_154 in *.
  destruct Hscan as [Hi Hprev].
  split; [lia |].
  intros r rot Hr Hrot pos Hpos.
  destruct (Z_lt_ge_dec r i) as [Hlt | Hge].
  - eapply Hprev; eauto; lia.
  - assert (r = i) by lia; subst r.
    unfold strstr_result in Hstr.
    destruct Hstr as [[p [_ [_ [_ Hnz]]]] | [Hnone Hzero]].
    + lia.
    + subst ret.
      assert (rot = out).
      { unfold rotation_prefix_154 in Hrot, Hpref.
        destruct Hrot as [_ [_ ->]].
        destruct Hpref as [_ [_ ->]].
        reflexivity. }
      subst rot.
      eapply Hnone; eauto.
Qed.

Definition ascii_list_154 (l : list Z) : list ascii :=
  map ascii_of_z_154 l.

Lemma list_ascii_of_string_of_list_z_154 : forall l,
  list_ascii_of_string (string_of_list_z_154 l) = ascii_list_154 l.
Proof.
  induction l as [|z tl IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma Zlength_map_154 : forall {A B : Type} (f : A -> B) l,
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  rewrite !Zlength_correct, map_length; reflexivity.
Qed.

Lemma map_sublist_154 : forall {A B : Type} (f : A -> B) lo hi l,
  map f (sublist lo hi l) = sublist lo hi (map f l).
Proof.
  intros A B f lo hi l.
  unfold sublist.
  rewrite firstn_map, skipn_map.
  reflexivity.
Qed.

Lemma Znth_ascii_list_154 : forall l i,
  Znth i (ascii_list_154 l) (ascii_of_z_154 0) =
  ascii_of_z_154 (Znth i l 0).
Proof.
  intros l i.
  unfold ascii_list_154, Znth.
  apply map_nth.
Qed.

Lemma ascii_of_z_154_inj_range : forall x y,
  0 <= x <= 127 ->
  0 <= y <= 127 ->
  ascii_of_z_154 x = ascii_of_z_154 y ->
  x = y.
Proof.
  intros x y Hx Hy Heq.
  unfold ascii_of_z_154 in Heq.
  apply (f_equal N_of_ascii) in Heq.
  assert (HxN : (Z.to_N x < 256)%N).
  { change (Z.to_N x < Z.to_N 256)%N.
    apply (proj1 (Z2N.inj_lt x 256 ltac:(lia) ltac:(lia))); lia. }
  assert (HyN : (Z.to_N y < 256)%N).
  { change (Z.to_N y < Z.to_N 256)%N.
    apply (proj1 (Z2N.inj_lt y 256 ltac:(lia) ltac:(lia))); lia. }
  rewrite (N_ascii_embedding (Z.to_N x) HxN) in Heq.
  rewrite (N_ascii_embedding (Z.to_N y) HyN) in Heq.
  eapply Z2N.inj; eauto; lia.
Qed.

Lemma all_ascii_sublist_154 : forall l lo hi,
  all_ascii l ->
  0 <= lo <= hi ->
  hi <= Zlength l ->
  all_ascii (sublist lo hi l).
Proof.
  intros l lo hi Hall Hlo Hhi k Hk.
  rewrite Zlength_sublist in Hk by lia.
  rewrite Znth_sublist by lia.
  apply Hall.
  lia.
Qed.

Lemma ascii_list_154_inj : forall l1 l2,
  all_ascii l1 ->
  all_ascii l2 ->
  ascii_list_154 l1 = ascii_list_154 l2 ->
  l1 = l2.
Proof.
  intros l1 l2 H1 H2 Hmap.
  apply (proj2 (list_eq_ext l1 l2 0)).
  split.
  - apply (f_equal (@Zlength ascii)) in Hmap.
    unfold ascii_list_154 in Hmap.
    rewrite !Zlength_map_154 in Hmap; exact Hmap.
  - intros i Hi.
    apply ascii_of_z_154_inj_range.
    + apply H1; exact Hi.
    + apply H2.
      apply (f_equal (@Zlength ascii)) in Hmap.
      unfold ascii_list_154 in Hmap.
      rewrite !Zlength_map_154 in Hmap; lia.
    + rewrite <- !Znth_ascii_list_154.
      now rewrite Hmap.
Qed.

Lemma substring_at_154_to_is_substring : forall main sub pos,
  substring_at main sub pos ->
  is_substring (ascii_list_154 sub) (ascii_list_154 main).
Proof.
  intros main sub pos Hsub.
  unfold substring_at in Hsub.
  destruct Hsub as [Hpos [Hfit Hpoint]].
  unfold string_length in Hpos, Hfit, Hpoint.
  pose proof (Zlength_nonneg sub) as Hsub_len.
  assert (Hmiddle : sublist pos (pos + Zlength sub) main = sub).
  { apply (proj2 (list_eq_ext (sublist pos (pos + Zlength sub) main) sub 0)).
    split.
    - assert (Hbounds : 0 <= pos <= pos + Zlength sub /\
                         pos + Zlength sub <= Zlength main) by (repeat split; lia).
      rewrite (Zlength_sublist pos (pos + Zlength sub) main Hbounds); lia.
    - intros k Hk.
      assert (Hbounds : 0 <= pos <= pos + Zlength sub /\
                         pos + Zlength sub <= Zlength main) by (repeat split; lia).
      rewrite Zlength_sublist in Hk by exact Hbounds.
      rewrite Znth_sublist by lia.
      replace (k + pos) with (pos + k) by lia.
      apply Hpoint; lia. }
  assert (Hdecomp :
      main = sublist 0 pos main ++ sub ++
             sublist (pos + Zlength sub) (Zlength main) main).
  { transitivity (sublist 0 (Zlength main) main).
    - symmetry; apply sublist_self; reflexivity.
    - rewrite (sublist_split 0 (Zlength main) pos main) by lia.
      rewrite (sublist_split pos (Zlength main) (pos + Zlength sub) main) by lia.
      rewrite Hmiddle, app_assoc; reflexivity. }
  exists (ascii_list_154 (sublist 0 pos main)).
  exists (ascii_list_154 (sublist (pos + Zlength sub) (Zlength main) main)).
  unfold ascii_list_154.
  rewrite Hdecomp at 1.
  rewrite !map_app; reflexivity.
Qed.

Lemma rotate_at_154_is_rotation : forall b i,
  0 <= i <= Zlength b ->
  is_rotation_of (ascii_list_154 (rotate_at_154 b i)) (ascii_list_154 b).
Proof.
  intros b i Hi.
  exists (ascii_list_154 (sublist 0 i b)).
  exists (ascii_list_154 (sublist i (Zlength b) b)).
  split.
  - unfold ascii_list_154.
    rewrite <- map_app.
    f_equal.
    rewrite <- (sublist_split 0 (Zlength b) i b) by lia.
    symmetry; apply sublist_self; reflexivity.
  - unfold ascii_list_154, rotate_at_154.
    now rewrite map_app.
Qed.

Lemma rotation_success_154_problem_spec : forall a b i out,
  valid_string a ->
  valid_string b ->
  rotation_success_154 a b i out ->
  problem_154_spec_z a b 1.
Proof.
  intros a b i out Hva Hvb Hsuccess.
  destruct Hsuccess as [Hpref [pos Hsub]].
  unfold rotation_prefix_154 in Hpref.
  destruct Hpref as [Hi [_ Hout]].
  rewrite sublist_self in Hout by
      (rewrite rotate_at_154_length; lia).
  subst out.
  unfold problem_154_spec_z, problem_154_spec, bool_of_z_154.
  rewrite !list_ascii_of_string_of_list_z_154.
  simpl.
  split.
  - intros _.
    split.
    + unfold ascii_list_154.
      intro Hnil.
      apply map_eq_nil in Hnil.
      subst b; rewrite Zlength_nil in Hi; lia.
    + exists (ascii_list_154 (rotate_at_154 b i)).
      split.
      * apply rotate_at_154_is_rotation; lia.
      * now apply (substring_at_154_to_is_substring a (rotate_at_154 b i) pos).
  - intros _; reflexivity.
Qed.

Lemma is_substring_154_to_substring_at : forall main sub,
  all_ascii main ->
  all_ascii sub ->
  is_substring (ascii_list_154 sub) (ascii_list_154 main) ->
  exists pos, substring_at main sub pos.
Proof.
  intros main sub Hmain Hsub [prefix [suffix Heq]].
  set (pos := Zlength prefix).
  assert (Hlen : Zlength (ascii_list_154 main) =
                 Zlength prefix + Zlength (ascii_list_154 sub) + Zlength suffix).
  { rewrite Heq, !Zlength_app; lia. }
  unfold ascii_list_154 in Hlen.
  rewrite !Zlength_map_154 in Hlen.
  assert (Hpos : 0 <= pos) by (unfold pos; apply Zlength_nonneg).
  assert (Hfit : pos + Zlength sub <= Zlength main).
  { unfold pos; pose proof (Zlength_nonneg suffix); lia. }
  assert (Hmiddle_ascii :
      sublist pos (pos + Zlength sub) (ascii_list_154 main) =
      ascii_list_154 sub).
  { rewrite Heq.
    rewrite (sublist_split_app_r pos (pos + Zlength sub) pos prefix
              (ascii_list_154 sub ++ suffix)) by
        (unfold pos; pose proof (Zlength_nonneg sub);
         repeat split; try reflexivity; lia).
    replace (pos - pos) with 0 by lia.
    replace (pos + Zlength sub - pos) with (Zlength sub) by lia.
    rewrite sublist_split_app_l by
        (unfold ascii_list_154; rewrite ?Zlength_map_154;
         pose proof (Zlength_nonneg sub); lia).
    apply sublist_self.
    unfold ascii_list_154; rewrite Zlength_map_154; reflexivity. }
  assert (Hmiddle : sublist pos (pos + Zlength sub) main = sub).
  { apply ascii_list_154_inj.
    - apply all_ascii_sublist_154; [exact Hmain | | exact Hfit].
      pose proof (Zlength_nonneg sub); lia.
    - exact Hsub.
    - unfold ascii_list_154 at 1.
      rewrite map_sublist_154.
      exact Hmiddle_ascii. }
  exists pos.
  unfold substring_at, string_length.
  split.
  - pose proof (Zlength_nonneg sub); lia.
  - split; [exact Hfit |].
  intros k Hk.
  rewrite <- Hmiddle.
  rewrite Znth_sublist by lia.
  f_equal; lia.
Qed.

Lemma is_rotation_154_to_rotate_at : forall b rotated,
  0 < Zlength b ->
  is_rotation_of rotated (ascii_list_154 b) ->
  exists i,
    0 <= i < Zlength b /\
    rotated = ascii_list_154 (rotate_at_154 b i).
Proof.
  intros b rotated Hb_nonempty [p1 [p2 [Hb Hrot]]].
  unfold ascii_list_154 in Hb.
  set (cut := Zlength p1).
  assert (Hlength : Zlength b = Zlength p1 + Zlength p2).
  { pose proof (f_equal (@Zlength ascii) Hb) as Hb_len.
    rewrite Zlength_map_154, Zlength_app in Hb_len; lia. }
  assert (Hcut : 0 <= cut <= Zlength b).
  { unfold cut; pose proof (Zlength_nonneg p1); pose proof (Zlength_nonneg p2); lia. }
  assert (Hp1 : p1 = ascii_list_154 (sublist 0 cut b)).
  { unfold ascii_list_154.
    rewrite map_sublist_154.
    symmetry.
    rewrite Hb.
    rewrite sublist_split_app_l by (unfold cut; lia).
    apply sublist_self; unfold cut; reflexivity. }
  assert (Hp2 : p2 = ascii_list_154 (sublist cut (Zlength b) b)).
  { unfold ascii_list_154.
    rewrite map_sublist_154.
    symmetry.
    rewrite Hb.
    rewrite (sublist_split_app_r cut (Zlength b) cut p1 p2) by
        (unfold cut; repeat split; try reflexivity; lia).
    replace (cut - cut) with 0 by lia.
    replace (Zlength b - cut) with (Zlength p2) by (unfold cut; lia).
    apply sublist_self; reflexivity. }
  destruct (Z_lt_ge_dec cut (Zlength b)) as [Hproper | Hend].
  - exists cut; split; [lia |].
    rewrite Hrot, Hp1, Hp2.
    unfold rotate_at_154, ascii_list_154.
    now rewrite map_app.
  - assert (Hp2_nil : p2 = []).
    { destruct p2 as [|x xs]; [reflexivity |].
      rewrite Zlength_cons in Hlength.
      pose proof (Zlength_nonneg xs).
      unfold cut in *; lia. }
    exists 0; split; [lia |].
    rewrite Hp2_nil in Hb, Hrot.
    rewrite app_nil_r in Hb.
    simpl in Hrot.
    rewrite <- Hb in Hrot.
    rewrite Hrot.
    unfold rotate_at_154, ascii_list_154.
    rewrite sublist_self by reflexivity.
    unfold sublist; simpl; rewrite app_nil_r.
    reflexivity.
Qed.

Lemma rotation_scan_state_154_problem_spec : forall a b,
  valid_string a ->
  valid_string b ->
  rotation_scan_state_154 a b (Zlength b) ->
  problem_154_spec_z a b 0.
Proof.
  intros a b Hva Hvb Hscan.
  destruct Hva as [Haa Hna].
  destruct Hvb as [Hab Hnb].
  unfold problem_154_spec_z, problem_154_spec, bool_of_z_154.
  rewrite !list_ascii_of_string_of_list_z_154.
  simpl.
  split.
  - discriminate.
  - intros [Hb_not_nil [rotated [Hrotation Hsubstring]]].
    assert (Hb_pos : 0 < Zlength b).
    { destruct b as [|x xs].
      - exfalso; apply Hb_not_nil; reflexivity.
      - rewrite Zlength_cons.
        pose proof (Zlength_nonneg xs); lia. }
    destruct (is_rotation_154_to_rotate_at b rotated Hb_pos Hrotation)
      as [i [Hi Hrotated]].
    subst rotated.
    assert (Harot : all_ascii (rotate_at_154 b i)).
    { apply all_ascii_rotate_at_154; [exact Hab | lia]. }
    destruct (is_substring_154_to_substring_at
                a (rotate_at_154 b i) Haa Harot Hsubstring)
      as [pos Hsub].
    unfold rotation_scan_state_154 in Hscan.
    destruct Hscan as [_ Hnone].
    assert (Hprefix : rotation_prefix_154 b i (Zlength b)
                        (rotate_at_154 b i)).
    { unfold rotation_prefix_154.
      split; [exact Hi |].
      split; [pose proof (Zlength_nonneg b); lia |].
      rewrite sublist_self.
      - reflexivity.
      - symmetry; apply rotate_at_154_length; lia. }
    exfalso.
    eapply (Hnone i (rotate_at_154 b i) Hi Hprefix pos); eauto.
    unfold substring_at, string_length in Hsub.
    destruct Hsub as [Hpos _]; exact Hpos.
Qed.
