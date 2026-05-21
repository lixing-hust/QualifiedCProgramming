Load "../spec/134".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_alpha_z (x : Z) : Prop :=
  65 <= x <= 90 \/ 97 <= x <= 122.

Definition ends_with_single_letter_z (l : list Z) : Prop :=
  1 <= Zlength l /\
  is_alpha_z (Znth (Zlength l - 1) l 0) /\
  (Zlength l = 1 \/ Znth (Zlength l - 2) l 0 = 32).

Definition problem_134_pre_z (s : list Z) : Prop :=
  problem_134_pre (string_of_list_z s).

Definition problem_134_spec_z (s : list Z) (output : Z) : Prop :=
  problem_134_spec (string_of_list_z s) (bool_of_z output).

Lemma is_alpha_z_to_is_alpha : forall x,
  0 <= x < 256 ->
  is_alpha_z x ->
  is_alpha (ascii_of_z x).
Proof.
  intros x Hrange Halpha.
  unfold is_alpha_z in Halpha.
  unfold is_alpha.
  rewrite nat_of_ascii_ascii_of_z by exact Hrange.
  lia.
Qed.

Lemma is_alpha_to_is_alpha_z : forall x,
  0 <= x < 256 ->
  is_alpha (ascii_of_z x) ->
  is_alpha_z x.
Proof.
  intros x Hrange Halpha.
  unfold is_alpha_z.
  unfold is_alpha in Halpha.
  rewrite nat_of_ascii_ascii_of_z in Halpha by exact Hrange.
  lia.
Qed.

Lemma ascii_of_z_space : ascii_of_z 32 = space.
Proof.
  unfold ascii_of_z, space.
  reflexivity.
Qed.

Lemma ascii_of_z_eq_space_to_z : forall x,
  0 <= x < 256 ->
  ascii_of_z x = space ->
  x = 32.
Proof.
  intros x Hrange Hspace.
  apply (f_equal nat_of_ascii) in Hspace.
  rewrite nat_of_ascii_ascii_of_z in Hspace by exact Hrange.
  unfold space in Hspace.
  change (nat_of_ascii (ascii_of_nat 32)) with 32%nat in Hspace.
  lia.
Qed.

Lemma nth_Znth_last : forall {A : Type} (l : list A) (d : A),
  l <> [] ->
  nth (Datatypes.length l - 1) l d = Znth (Zlength l - 1) l d.
Proof.
  intros A l d Hnonempty.
  unfold Znth.
  replace (Z.to_nat (Zlength l - 1)) with (Datatypes.length l - 1)%nat.
  - reflexivity.
  - rewrite Zlength_correct.
    change 1 with (Z.of_nat 1).
    rewrite <- Nat2Z.inj_sub by (destruct l; simpl in *; try contradiction; lia).
    rewrite Nat2Z.id.
    reflexivity.
Qed.

Lemma nth_Znth_prev : forall {A : Type} (l : list A) (d : A),
  (1 < Datatypes.length l)%nat ->
  nth (Datatypes.length l - 2) l d = Znth (Zlength l - 2) l d.
Proof.
  intros A l d Hlen.
  unfold Znth.
  replace (Z.to_nat (Zlength l - 2)) with (Datatypes.length l - 2)%nat.
  - reflexivity.
  - rewrite Zlength_correct.
    change 2 with (Z.of_nat 2).
    rewrite <- Nat2Z.inj_sub by lia.
    rewrite Nat2Z.id.
    reflexivity.
Qed.

Lemma firstn_succ_snoc_134 : forall {A : Type} n (l : list A) d,
  (n < Datatypes.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma list_last_split_134 : forall {A : Type} (l : list A) (d : A),
  l <> [] ->
  l = List.app (firstn (Datatypes.length l - 1) l) [nth (Datatypes.length l - 1) l d].
Proof.
  intros A l d Hnonempty.
  rewrite <- (firstn_all l) at 1.
  replace (Datatypes.length l) with (S (Datatypes.length l - 1)) at 1 by
    (destruct l; simpl in *; try contradiction; lia).
  rewrite (firstn_succ_snoc_134 (Datatypes.length l - 1) l d) by
    (destruct l; simpl in *; try contradiction; lia).
  reflexivity.
Qed.

Lemma list_last2_split_134 : forall {A : Type} (l : list A) (d : A),
  (1 < Datatypes.length l)%nat ->
  l = List.app (firstn (Datatypes.length l - 2) l)
      [nth (Datatypes.length l - 2) l d; nth (Datatypes.length l - 1) l d].
Proof.
  intros A l d Hlen.
  rewrite (list_last_split_134 l d) at 1 by
    (destruct l; simpl in *; try lia; discriminate).
  replace (Datatypes.length l - 1)%nat with (S (Datatypes.length l - 2)) by lia.
  rewrite (firstn_succ_snoc_134 (Datatypes.length l - 2) l d) by lia.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma ends_with_single_letter_z_to_pred : forall s,
  ascii_range_z s ->
  ends_with_single_letter_z s ->
  ends_with_single_letter_pred (string_of_list_z s).
Proof.
  intros s Hrange Hends.
  unfold ends_with_single_letter_z in Hends.
  destruct Hends as [Hnonempty [Halpha Hlast_case]].
  unfold ends_with_single_letter_pred.
  rewrite list_ascii_of_string_string_of_list_z.
  assert (Hs_nonempty : s <> []).
  { destruct s; simpl in *; rewrite ?Zlength_nil, ?Zlength_cons in *; try lia; discriminate. }
  assert (Hlast_range : 0 <= Znth (Zlength s - 1) s 0 < 256).
  { apply Hrange. lia. }
  exists (map ascii_of_z (firstn (Datatypes.length s - 1) s)).
  exists (ascii_of_z (Znth (Zlength s - 1) s 0)).
  split.
  - rewrite (list_last_split_134 s 0) at 1 by exact Hs_nonempty.
    rewrite map_app.
    simpl.
    rewrite nth_Znth_last by exact Hs_nonempty.
    reflexivity.
  - split.
    + apply is_alpha_z_to_is_alpha; assumption.
    + destruct Hlast_case as [Hsingle | Hspace_case].
      * left.
        rewrite Zlength_correct in Hsingle.
        replace (Datatypes.length s - 1)%nat with 0%nat by lia.
        reflexivity.
      * right.
        assert (Hlen_nat : (1 < Datatypes.length s)%nat).
        {
          assert (Hnot_one : Zlength s <> 1).
          {
            intro Hlen1.
            rewrite Hlen1 in Hspace_case.
            rewrite Hlen1 in Halpha.
            unfold Znth in Hspace_case.
            unfold Znth in Halpha.
            simpl in Hspace_case.
            simpl in Halpha.
            rewrite Hspace_case in Halpha.
            unfold is_alpha_z in Halpha.
            lia.
          }
          rewrite Zlength_correct in Hnonempty, Hnot_one.
          lia.
        }
        exists (map ascii_of_z (firstn (Datatypes.length s - 2) s)).
        replace (Datatypes.length s - 1)%nat with (S (Datatypes.length s - 2)) by lia.
        rewrite (firstn_succ_snoc_134 (Datatypes.length s - 2) s 0) by lia.
        rewrite map_app.
        simpl.
        rewrite nth_Znth_prev by exact Hlen_nat.
        rewrite Hspace_case.
        rewrite ascii_of_z_space.
        reflexivity.
Qed.

Lemma pred_to_ends_with_single_letter_z : forall s,
  ascii_range_z s ->
  ends_with_single_letter_pred (string_of_list_z s) ->
  ends_with_single_letter_z s.
Proof.
  intros s Hrange Hpred.
  unfold ends_with_single_letter_pred in Hpred.
  rewrite list_ascii_of_string_string_of_list_z in Hpred.
  destruct Hpred as [pre [c [Hsplit [Halpha Hpre_case]]]].
  assert (Hlen_map : Datatypes.length s = (Datatypes.length pre + 1)%nat).
  {
    apply (f_equal (@Datatypes.length ascii)) in Hsplit.
    rewrite map_length, app_length in Hsplit.
    simpl in Hsplit.
    lia.
  }
  assert (Hs_nonempty : s <> []) by (destruct s; simpl in *; try lia; discriminate).
  assert (Hlast_eq : ascii_of_z (Znth (Zlength s - 1) s 0) = c).
  {
    assert (Hnth :
      nth (Datatypes.length s - 1) (map ascii_of_z s) (ascii_of_z 0) =
      nth (Datatypes.length s - 1) (pre ++ [c]) (ascii_of_z 0)).
    { rewrite Hsplit. reflexivity. }
    rewrite (List_lemma.map_nth_len Z ascii ascii_of_z s
               (Datatypes.length s - 1) (ascii_of_z 0) 0) in Hnth by lia.
    rewrite nth_Znth_last in Hnth by exact Hs_nonempty.
    rewrite app_nth2 in Hnth by lia.
    replace (Datatypes.length s - 1 - Datatypes.length pre)%nat with 0%nat in Hnth by lia.
    simpl in Hnth.
    exact Hnth.
  }
  unfold ends_with_single_letter_z.
  repeat split.
  - rewrite Zlength_correct. lia.
  - apply is_alpha_to_is_alpha_z.
    + apply Hrange. rewrite Zlength_correct. lia.
    + rewrite Hlast_eq. exact Halpha.
  - destruct Hpre_case as [Hpre_empty | Hpre_space].
    + left.
      subst pre.
      simpl in Hlen_map.
      rewrite Zlength_correct.
      lia.
    + right.
      destruct Hpre_space as [pre' Hpre_space].
      assert (Hlen_nat : (1 < Datatypes.length s)%nat).
      { subst pre. rewrite app_length in Hlen_map. simpl in Hlen_map. lia. }
      assert (Hprev_eq : ascii_of_z (Znth (Zlength s - 2) s 0) = space).
      {
        assert (Hnth :
          nth (Datatypes.length s - 2) (map ascii_of_z s) (ascii_of_z 0) =
          nth (Datatypes.length s - 2) (pre ++ [c]) (ascii_of_z 0)).
        { rewrite Hsplit. reflexivity. }
        rewrite (List_lemma.map_nth_len Z ascii ascii_of_z s
                   (Datatypes.length s - 2) (ascii_of_z 0) 0) in Hnth by lia.
        rewrite nth_Znth_prev in Hnth by exact Hlen_nat.
        rewrite app_nth1 in Hnth.
        - subst pre.
          rewrite app_nth2 in Hnth by
            (rewrite app_length in Hlen_map; simpl in Hlen_map; lia).
          replace (Datatypes.length s - 2 - Datatypes.length pre')%nat with 0%nat in Hnth by
            (rewrite app_length in Hlen_map; simpl in Hlen_map; lia).
          simpl in Hnth.
          exact Hnth.
        - subst pre.
          rewrite app_length in Hlen_map.
          simpl in Hlen_map.
          rewrite app_length.
          simpl.
          lia.
      }
      apply ascii_of_z_eq_space_to_z.
      * apply Hrange. rewrite Zlength_correct. lia.
      * exact Hprev_eq.
Qed.

Lemma problem_134_spec_z_true : forall s,
  ascii_range_z s ->
  ends_with_single_letter_z s ->
  problem_134_spec_z s 1.
Proof.
  intros s Hrange H.
  unfold problem_134_spec_z, problem_134_spec, bool_of_z.
  simpl.
  split; intros _.
  - apply ends_with_single_letter_z_to_pred; assumption.
  - reflexivity.
Qed.

Lemma problem_134_spec_z_false : forall s,
  ascii_range_z s ->
  ~ ends_with_single_letter_z s ->
  problem_134_spec_z s 0.
Proof.
  intros s Hrange H.
  unfold problem_134_spec_z, problem_134_spec, bool_of_z.
  simpl.
  split; intros Hfalse.
  - discriminate.
  - exfalso.
    apply H.
    apply pred_to_ends_with_single_letter_z; assumption.
Qed.

Lemma ends_with_single_letter_z_intro_single : forall s,
  Zlength s = 1 ->
  is_alpha_z (Znth (Zlength s - 1) s 0) ->
  ends_with_single_letter_z s.
Proof.
  intros s Hlen Halpha.
  unfold ends_with_single_letter_z.
  repeat split; try assumption; lia.
Qed.

Lemma ends_with_single_letter_z_intro_space : forall s,
  1 < Zlength s ->
  is_alpha_z (Znth (Zlength s - 1) s 0) ->
  Znth (Zlength s - 2) s 0 = 32 ->
  ends_with_single_letter_z s.
Proof.
  intros s Hlen Halpha Hspace.
  unfold ends_with_single_letter_z.
  repeat split; try assumption; lia.
Qed.

Lemma not_ends_with_single_letter_z_empty : forall s,
  Zlength s = 0 ->
  ~ ends_with_single_letter_z s.
Proof.
  unfold ends_with_single_letter_z.
  intros s Hlen H.
  lia.
Qed.

Lemma not_ends_with_single_letter_z_not_alpha : forall s,
  1 <= Zlength s ->
  ~ is_alpha_z (Znth (Zlength s - 1) s 0) ->
  ~ ends_with_single_letter_z s.
Proof.
  unfold ends_with_single_letter_z.
  intros s Hlen Hnot H.
  tauto.
Qed.

Lemma not_ends_with_single_letter_z_prev_not_space : forall s,
  1 < Zlength s ->
  is_alpha_z (Znth (Zlength s - 1) s 0) ->
  Znth (Zlength s - 2) s 0 <> 32 ->
  ~ ends_with_single_letter_z s.
Proof.
  unfold ends_with_single_letter_z.
  intros s Hlen _ Hnot H.
  destruct H as [_ [_ [Hsingle | Hspace]]].
  - lia.
  - contradiction.
Qed.
