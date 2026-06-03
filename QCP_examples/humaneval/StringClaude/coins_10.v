Load "../spec/10".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_10_pre_z (input : list Z) : Prop :=
  problem_10_pre.

Definition problem_10_spec_z (input output : list Z) : Prop :=
  problem_10_spec (string_of_list_z input) (string_of_list_z output).

Definition pal_suffix_z (start : Z) (input : list Z) : Prop :=
  0 <= start <= Zlength input /\
  forall k,
    0 <= k < Zlength input - start ->
    k < Zlength input - start - 1 - k ->
    Znth (start + k) input 0 = Znth (Zlength input - 1 - k) input 0.

Definition first_pal_suffix_z (best : Z) (input : list Z) : Prop :=
  0 <= best <= Zlength input /\
  pal_suffix_z best input /\
  forall t, 0 <= t < best -> ~ pal_suffix_z t input.

Definition make_pal_output_z (best : Z) (input : list Z) : list Z :=
  input ++ rev (firstn (Z.to_nat best) input).

Lemma pal_suffix_empty_10 : forall input,
  Zlength input = 0 ->
  pal_suffix_z 0 input.
Proof.
  intros input Hlen.
  unfold pal_suffix_z.
  split; [lia |].
  intros k Hk _.
  lia.
Qed.

Lemma pal_suffix_last_10 : forall input,
  0 < Zlength input ->
  pal_suffix_z (Zlength input - 1) input.
Proof.
  intros input Hlen.
  unfold pal_suffix_z.
  split; [lia |].
  intros k Hk Hmirror.
  lia.
Qed.

Lemma ascii_of_z_inj_range_10 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of_z a = ascii_of_z b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  repeat rewrite nat_of_ascii_ascii_of_z in Heq by lia.
  lia.
Qed.

Lemma first_pal_suffix_empty_10 : forall input,
  Zlength input = 0 ->
  first_pal_suffix_z 0 input.
Proof.
  intros input Hlen.
  unfold first_pal_suffix_z.
  split; [lia |].
  split.
  - apply pal_suffix_empty_10; assumption.
  - intros t Ht.
    lia.
Qed.

Lemma Zlength_rev_10 : forall {A : Type} (l : list A),
  Zlength (rev l) = Zlength l.
Proof.
  intros A l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.

Lemma Znth_rev_10 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l i d Hi.
  unfold Znth.
  rewrite rev_nth by (rewrite Zlength_correct in Hi; lia).
  replace (Datatypes.length l - S (Z.to_nat i))%nat
    with (Z.to_nat (Zlength l - 1 - i)).
  - reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma Znth_firstn_10 : forall {A : Type} n (l : list A) i d,
  0 <= i ->
  i < Z.of_nat n ->
  Znth i (firstn n l) d = Znth i l d.
Proof.
  intros A n l i d Hi Hlt.
  unfold Znth.
  rewrite List.nth_firstn.
  destruct (Z.to_nat i <? n)%nat eqn:Hcmp.
  - reflexivity.
  - apply Nat.ltb_ge in Hcmp.
    lia.
Qed.

Lemma Zlength_make_pal_output_z_10 : forall best input,
  0 <= best <= Zlength input ->
  Zlength (make_pal_output_z best input) = Zlength input + best.
Proof.
  intros best input Hbest.
  unfold make_pal_output_z.
  rewrite Zlength_app.
  rewrite Zlength_rev_10.
  rewrite !Zlength_correct.
  rewrite firstn_length.
  rewrite Zlength_correct in Hbest.
  replace (Init.Nat.min (Z.to_nat best) (Datatypes.length input))
    with (Z.to_nat best) by lia.
  lia.
Qed.

Lemma make_pal_output_z_prefix_10 : forall best input k,
  0 <= best <= Zlength input ->
  0 <= k < Zlength input ->
  Znth k (make_pal_output_z best input) 0 = Znth k input 0.
Proof.
  intros best input k Hbest Hk.
  unfold make_pal_output_z.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma make_pal_output_z_suffix_10 : forall best input k,
  0 <= best <= Zlength input ->
  0 <= k < best ->
  Znth (Zlength input + k) (make_pal_output_z best input) 0 =
  Znth (best - 1 - k) input 0.
Proof.
  intros best input k Hbest Hk.
  unfold make_pal_output_z.
  rewrite app_Znth2 by lia.
  rewrite Zlength_correct.
  replace (Zlength input + k - Z.of_nat (Datatypes.length input)) with k
    by (rewrite Zlength_correct; lia).
  assert (Hfirst_len : Zlength (firstn (Z.to_nat best) input) = best).
  {
    rewrite Zlength_correct, firstn_length.
    replace (Init.Nat.min (Z.to_nat best) (Datatypes.length input))
      with (Z.to_nat best) by (rewrite Zlength_correct in Hbest; lia).
    lia.
  }
  rewrite Znth_rev_10 by (rewrite Hfirst_len; lia).
  rewrite Hfirst_len.
  rewrite Znth_firstn_10 by lia.
  replace (Z.of_nat (Datatypes.length input) + k -
    Z.of_nat (Datatypes.length input)) with k by lia.
  reflexivity.
Qed.

Lemma Zlength_map_10 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.

Lemma Znth_map_10 : forall {A B : Type} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.

Lemma string_of_list_z_app_10 : forall a b,
  string_of_list_z (a ++ b) =
  String.append (string_of_list_z a) (string_of_list_z b).
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_length_append_nat_10 : forall a b,
  String.length (String.append a b) =
  (String.length a + String.length b)%nat.
Proof.
  induction a as [| c rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_length_append_z_10 : forall a b,
  Z.of_nat (String.length (String.append a b)) =
  Z.of_nat (String.length a) + Z.of_nat (String.length b).
Proof.
  intros a b.
  rewrite string_length_append_nat_10.
  lia.
Qed.

Lemma string_of_list_z_as_ascii_10 : forall l,
  string_of_list_z l = string_of_list_ascii (map ascii_of_z l).
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_of_list_z_rev_10 : forall l,
  string_of_list_ascii (rev (list_ascii_of_string (string_of_list_z l))) =
  string_of_list_z (rev l).
Proof.
  intros l.
  rewrite list_ascii_of_string_string_of_list_z.
  rewrite <- map_rev.
  rewrite string_of_list_z_as_ascii_10.
  reflexivity.
Qed.

Lemma list_ascii_of_string_app_10 : forall a b,
  list_ascii_of_string (String.append a b) =
  list_ascii_of_string a ++ list_ascii_of_string b.
Proof.
  induction a as [| c rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma string_of_list_ascii_list_ascii_of_string_10 : forall s,
  string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma list_ascii_of_string_string_of_list_ascii_10 : forall l,
  list_ascii_of_string (string_of_list_ascii l) = l.
Proof.
  induction l as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma Zlength_list_ascii_of_string_10 : forall s,
  Zlength (list_ascii_of_string s) = Z.of_nat (String.length s).
Proof.
  induction s as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.

Lemma prefix_append_true_10 : forall s t,
  prefix s (String.append s t) = true.
Proof.
  induction s as [| c rest IH]; intros t; simpl.
  - destruct t; reflexivity.
  - destruct (ascii_dec c c) as [_ | Hneq].
    + apply IH.
    + contradiction.
Qed.

Lemma prefix_true_exists_suffix_10 : forall s p,
  prefix s p = true ->
  exists q, p = String.append s q.
Proof.
  induction s as [| c rest IH]; intros p Hprefix.
  - exists p. reflexivity.
  - destruct p as [| d prest]; simpl in Hprefix; try discriminate.
    destruct (ascii_dec c d) as [Heq | Hneq]; try discriminate.
    subst d.
    destruct (IH prest Hprefix) as [q ->].
    exists q. reflexivity.
Qed.

Lemma Zlength_skipn_10 : forall n (l : list Z),
  0 <= n <= Zlength l ->
  Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros n l Hn.
  rewrite !Zlength_correct.
  rewrite skipn_length.
  replace (Datatypes.length l - Z.to_nat n)%nat
    with (Z.to_nat (Z.of_nat (Datatypes.length l) - n)) by lia.
  rewrite Z2Nat.id by (rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.

Lemma Znth_skipn_10 : forall n i (l : list Z) d,
  0 <= n <= Zlength l ->
  0 <= i < Zlength l - n ->
  Znth i (skipn (Z.to_nat n) l) d = Znth (n + i) l d.
Proof.
  intros n i l d Hn Hi.
  unfold Znth.
  rewrite nth_skipn.
  replace (Z.to_nat i + Z.to_nat n)%nat with (Z.to_nat (n + i)) by lia.
  reflexivity.
Qed.

Lemma pal_suffix_z_skipn_rev_10 : forall best input,
  pal_suffix_z best input ->
  skipn (Z.to_nat best) input = rev (skipn (Z.to_nat best) input).
Proof.
  intros best input [Hbest Hpal].
  apply (proj2 (@list_eq_ext Z 0 _ _)).
  split.
  - rewrite Zlength_rev_10. reflexivity.
  - intros i Hi.
    rewrite Znth_rev_10 by lia.
    rewrite Zlength_skipn_10 by lia.
    rewrite Zlength_skipn_10 in Hi by lia.
    rewrite (Znth_skipn_10 best i input 0) by lia.
    rewrite (Znth_skipn_10 best (Zlength input - best - 1 - i) input 0) by lia.
    replace (best + (Zlength input - best - 1 - i))
      with (Zlength input - 1 - i) by lia.
    destruct (Z_lt_ge_dec i (Zlength input - best - 1 - i)) as [Hmirror | Hmirror].
    + apply Hpal; lia.
    + destruct (Z.eq_dec i (Zlength input - best - 1 - i)) as [Heq | Hneq].
      * replace (Zlength input - 1 - i) with (best + i) by lia.
        reflexivity.
      * symmetry.
        replace (best + i) with
          (Zlength input - 1 - (Zlength input - best - 1 - i)) by lia.
        replace (Zlength input - 1 - i) with
          (best + (Zlength input - best - 1 - i)) by lia.
        apply Hpal; lia.
Qed.

Lemma make_pal_output_z_palindrome_list_10 : forall best input,
  first_pal_suffix_z best input ->
  make_pal_output_z best input = rev (make_pal_output_z best input).
Proof.
  intros best input [Hbest [Hpal Hmin]].
  unfold make_pal_output_z.
  set (pre := firstn (Z.to_nat best) input).
  set (suf := skipn (Z.to_nat best) input).
  assert (Hsplit : input = pre ++ suf).
  { subst pre suf. rewrite firstn_skipn. reflexivity. }
  assert (Hsuf : suf = rev suf).
  { subst suf. apply pal_suffix_z_skipn_rev_10. exact Hpal. }
  rewrite Hsplit.
  rewrite rev_app_distr.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  rewrite <- Hsuf.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma make_pal_output_z_ext_10 : forall len input best out_l,
  Zlength input = len ->
  0 <= best <= len ->
  Zlength out_l = len + best ->
  (forall p, 0 <= p < len -> Znth p out_l 0 = Znth p input 0) ->
  (forall p, 0 <= p < best ->
    Znth (len + p) out_l 0 = Znth (best - 1 - p) input 0) ->
  out_l = make_pal_output_z best input.
Proof.
  intros len input best out_l Hlen Hbest Hout_len Hprefix Hsuffix.
  apply (proj2 (@list_eq_ext Z 0 _ _)).
  split.
  - rewrite Hout_len.
    rewrite Zlength_make_pal_output_z_10; lia.
  - intros i Hi.
    rewrite Hout_len in Hi.
    destruct (Z_lt_ge_dec i len) as [Hlt | Hge].
    + rewrite Hprefix by lia.
      symmetry.
      rewrite make_pal_output_z_prefix_10 by lia.
      reflexivity.
    + replace i with (len + (i - len)) by lia.
      rewrite Hsuffix by lia.
      symmetry.
      rewrite <- Hlen.
      rewrite make_pal_output_z_suffix_10 by lia.
      reflexivity.
Qed.

Lemma prefix_palindrome_implies_pal_suffix_z_10 : forall input q t,
  ascii_range_z input ->
  t = Z.of_nat (String.length q) ->
  t <= Zlength input ->
  palindrome (String.append (string_of_list_z input) q) ->
  pal_suffix_z t input.
Proof.
  intros input q t Hrange Ht Ht_bound Hpal.
  unfold palindrome in Hpal.
  set (p := String.append (string_of_list_z input) q) in *.
  assert (Hpal_list :
    list_ascii_of_string p = rev (list_ascii_of_string p)).
  {
    rewrite Hpal at 1.
    apply list_ascii_of_string_string_of_list_ascii_10.
  }
  unfold pal_suffix_z.
  split; [lia |].
  intros k Hk Hmirror.
  assert (HP :
    list_ascii_of_string p =
    map ascii_of_z input ++ list_ascii_of_string q).
  {
    subst p.
    rewrite list_ascii_of_string_app_10.
    rewrite list_ascii_of_string_string_of_list_z.
    reflexivity.
  }
  assert (Hidx :
    Znth (t + k) (list_ascii_of_string p) " "%char =
    Znth (Zlength (list_ascii_of_string p) - 1 - (t + k))
      (list_ascii_of_string p) " "%char).
  {
    rewrite Hpal_list at 1.
    rewrite Znth_rev_10.
    - reflexivity.
    - rewrite HP, Zlength_app, Zlength_map_10.
      rewrite Zlength_list_ascii_of_string_10.
      rewrite <- Ht.
      lia.
  }
  rewrite HP in Hidx.
  rewrite Zlength_app, Zlength_map_10 in Hidx.
  rewrite Zlength_list_ascii_of_string_10 in Hidx.
  rewrite <- Ht in Hidx.
  replace (Zlength (map ascii_of_z input ++ list_ascii_of_string q) - 1 - (t + k))
    with (Zlength input - 1 - k) in Hidx.
  2:{
    rewrite Zlength_app, Zlength_map_10.
    rewrite Zlength_list_ascii_of_string_10.
    rewrite <- Ht.
    lia.
  }
  rewrite app_Znth1 in Hidx by (rewrite Zlength_map_10; lia).
  rewrite app_Znth1 in Hidx by (rewrite Zlength_map_10; lia).
  rewrite (@Znth_map_10 Z ascii ascii_of_z input (t + k) 0 " "%char) in Hidx by lia.
  replace (Zlength input + t - 1 - (t + k)) with (Zlength input - 1 - k) in Hidx by lia.
  rewrite (@Znth_map_10 Z ascii ascii_of_z input (Zlength input - 1 - k) 0 " "%char) in Hidx by lia.
  apply ascii_of_z_inj_range_10; try apply Hrange; try lia.
  exact Hidx.
Qed.

Lemma problem_10_spec_z_make_pal_output_10 : forall input best,
  ascii_range_z input ->
  first_pal_suffix_z best input ->
  problem_10_spec_z input (make_pal_output_z best input).
Proof.
  intros input best Hrange Hfirst.
  destruct Hfirst as [Hbest [Hpal Hmin]].
  unfold problem_10_spec_z, problem_10_spec.
  split.
  - unfold make_pal_output_z.
    rewrite string_of_list_z_app_10.
    apply prefix_append_true_10.
  - split.
    + unfold palindrome.
    rewrite string_of_list_z_rev_10.
    f_equal.
    apply make_pal_output_z_palindrome_list_10.
    unfold first_pal_suffix_z.
    exact (conj Hbest (conj Hpal Hmin)).
    + intros p [Hpref Hp_pal].
    destruct (prefix_true_exists_suffix_10 _ _ Hpref) as [q ->].
    apply Nat2Z.inj_le.
    rewrite string_of_list_z_length_z.
    rewrite string_length_append_z_10.
    rewrite string_of_list_z_length_z.
    rewrite Zlength_make_pal_output_z_10 by lia.
    assert (Hbest_le_q : best <= Z.of_nat (String.length q)).
    {
      destruct (Z_le_gt_dec (Z.of_nat (String.length q)) (Zlength input))
        as [Hq_bound | Hq_big]; [| lia].
      destruct (Z_lt_ge_dec (Z.of_nat (String.length q)) best) as [Hlt | Hge]; [| lia].
      exfalso.
      apply (Hmin (Z.of_nat (String.length q))); [lia |].
      eapply prefix_palindrome_implies_pal_suffix_z_10; eauto.
    }
    lia.
Qed.
