Load "../spec/119".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_z_119 (z : Z) : string :=
  if Z.eqb z 1 then "Yes" else "No".

Definition problem_119_pre_z (s1 s2 : list Z) : Prop :=
  problem_119_pre [string_of_list_z s1; string_of_list_z s2].

Definition problem_119_spec_z (s1 s2 : list Z) (output : Z) : Prop :=
  problem_119_spec [string_of_list_z s1; string_of_list_z s2] (yesno_of_z_119 output).

Definition paren_delta (x : Z) : Z :=
  if Z.eqb x 40 then 1 else if Z.eqb x 41 then -1 else 0.

Fixpoint paren_level_upto_nat (n : nat) (l : list Z) : Z :=
  match n with
  | O => 0
  | S n' => paren_level_upto_nat n' l + paren_delta (Znth (Z.of_nat n') l 0)
  end.

Definition paren_level_upto (i : Z) (l : list Z) : Z :=
  paren_level_upto_nat (Z.to_nat i) l.

Fixpoint paren_good_prefix_bool_nat (n : nat) (l : list Z) : bool :=
  match n with
  | O => true
  | S n' =>
      paren_good_prefix_bool_nat n' l &&
      Z.leb 0 (paren_level_upto (Z.of_nat n' + 1) l)
  end.

Definition paren_good_prefix_flag (i : Z) (l : list Z) : Z :=
  if paren_good_prefix_bool_nat (Z.to_nat i) l then 1 else 0.

Definition paren_balanced_by_scan (l : list Z) : bool :=
  Z.eqb (paren_level_upto (Zlength l) l) 0 &&
  Z.eqb (paren_good_prefix_flag (Zlength l) l) 1.

Fixpoint check_parens_z_inner (l : list Z) (counter : Z) : bool :=
  match l with
  | [] => Z.eqb counter 0
  | c :: rest =>
      if Z.eqb c 40 then
        check_parens_z_inner rest (counter + 1)
      else if Z.eqb c 41 then
        if Z.eqb counter 0 then false else check_parens_z_inner rest (counter - 1)
      else
        check_parens_z_inner rest counter
  end.

Definition is_balanced_z (l : list Z) : bool :=
  check_parens_z_inner l 0.

Lemma paren_level_upto_0 : forall l,
  paren_level_upto 0 l = 0.
Proof.
  reflexivity.
Qed.

Lemma paren_good_prefix_flag_0 : forall l,
  paren_good_prefix_flag 0 l = 1.
Proof.
  reflexivity.
Qed.

Lemma paren_delta_bound : forall x,
  -1 <= paren_delta x <= 1.
Proof.
  unfold paren_delta.
  intro x.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); simpl
  end; lia.
Qed.

Lemma paren_level_upto_step : forall i l,
  0 <= i ->
  paren_level_upto (i + 1) l =
  paren_level_upto i l + paren_delta (Znth i l 0).
Proof.
  intros i l Hi.
  unfold paren_level_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma paren_level_upto_step_open : forall i l,
  0 <= i ->
  Znth i l 0 = 40 ->
  paren_level_upto (i + 1) l = paren_level_upto i l + 1.
Proof.
  intros i l Hi Hx.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  rewrite Hx, Z.eqb_refl.
  reflexivity.
Qed.

Lemma paren_level_upto_step_close : forall i l,
  0 <= i ->
  Znth i l 0 = 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l - 1.
Proof.
  intros i l Hi Hx.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  rewrite Hx.
  replace (Z.eqb 41 40) with false by reflexivity.
  rewrite Z.eqb_refl.
  lia.
Qed.

Lemma paren_level_upto_step_other : forall i l,
  0 <= i ->
  Znth i l 0 <> 40 ->
  Znth i l 0 <> 41 ->
  paren_level_upto (i + 1) l = paren_level_upto i l.
Proof.
  intros i l Hi H40 H41.
  rewrite paren_level_upto_step by lia.
  unfold paren_delta.
  replace (Z.eqb (Znth i l 0) 40) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Znth i l 0) 41) with false by
    (symmetry; apply Z.eqb_neq; lia).
  lia.
Qed.

Lemma paren_good_prefix_flag_step_nonneg : forall i l level,
  0 <= i ->
  paren_good_prefix_flag i l = 1 ->
  level = paren_level_upto (i + 1) l ->
  0 <= level ->
  paren_good_prefix_flag (i + 1) l = 1.
Proof.
  intros i l level Hi Hflag Hlevel Hnonneg.
  unfold paren_good_prefix_flag in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); try discriminate.
  rewrite <- Hlevel.
  replace (Z.leb 0 level) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma paren_good_prefix_flag_step_neg : forall i l level,
  0 <= i ->
  level = paren_level_upto (i + 1) l ->
  level < 0 ->
  paren_good_prefix_flag (i + 1) l = 0.
Proof.
  intros i l level Hi Hlevel Hneg.
  unfold paren_good_prefix_flag.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  rewrite <- Hlevel.
  replace (Z.leb 0 level) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); reflexivity.
Qed.

Lemma paren_good_prefix_flag_step_bad : forall i l,
  0 <= i ->
  paren_good_prefix_flag i l = 0 ->
  paren_good_prefix_flag (i + 1) l = 0.
Proof.
  intros i l Hi Hflag.
  unfold paren_good_prefix_flag in *.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); try discriminate.
  reflexivity.
Qed.

Lemma paren_good_prefix_flag_bool : forall i l,
  paren_good_prefix_flag i l = 0 \/ paren_good_prefix_flag i l = 1.
Proof.
  intros i l.
  unfold paren_good_prefix_flag.
  destruct (paren_good_prefix_bool_nat (Z.to_nat i) l); auto.
Qed.

Lemma Znth_app_left_119 : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
    lia.
Qed.

Lemma Znth_app_right_119 : forall (l1 l2 : list Z) i d,
  Zlength l1 <= i < Zlength l1 + Zlength l2 ->
  Znth i (l1 ++ l2) d = Znth (i - Zlength l1) l2 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth2.
  - replace (Datatypes.length l1) with (Z.to_nat (Zlength l1)).
    + pose proof (Zlength_nonneg l1).
      rewrite <- Z2Nat.inj_sub by lia.
      reflexivity.
    + rewrite Zlength_correct.
      apply Nat2Z.id.
  - rewrite Zlength_correct in Hi.
    assert ((Datatypes.length l1 <= Z.to_nat i)%nat).
    { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
    lia.
Qed.

Lemma paren_level_bound : forall i l,
  0 <= i ->
  -i <= paren_level_upto i l <= i.
Proof.
  intros i l Hi.
  unfold paren_level_upto.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (Hiz : i = Z.of_nat n) by lia.
  subst i.
  induction n as [| n IH]; simpl.
  - lia.
  - pose proof (paren_delta_bound (Znth (Z.of_nat n) l 0)).
    lia.
Qed.

Fixpoint paren_sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | c :: rest => paren_delta c + paren_sum_list rest
  end.

Lemma paren_level_upto_nat_cons : forall n c rest,
  paren_level_upto_nat (S n) (c :: rest) =
  paren_delta c + paren_level_upto_nat n rest.
Proof.
  induction n as [| n IH]; intros c rest.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - change (paren_level_upto_nat (S n) (c :: rest) +
            paren_delta (Znth (Z.of_nat (S n)) (c :: rest) 0) =
            paren_delta c + paren_level_upto_nat (S n) rest).
    rewrite IH.
    rewrite Znth_cons by lia.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    rewrite <- Z.add_assoc.
    reflexivity.
Qed.

Lemma paren_level_upto_cons_succ : forall c rest k,
  0 <= k ->
  paren_level_upto (k + 1) (c :: rest) =
  paren_delta c + paren_level_upto k rest.
Proof.
  intros c rest k Hk.
  unfold paren_level_upto.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite paren_level_upto_nat_cons.
  reflexivity.
Qed.

Lemma paren_level_upto_Zlength_sum : forall l,
  paren_level_upto (Zlength l) l = paren_sum_list l.
Proof.
  induction l as [| c rest IH].
  - reflexivity.
  - rewrite Zlength_cons.
    unfold paren_level_upto.
    replace (Z.to_nat (Z.succ (Zlength rest))) with (S (Z.to_nat (Zlength rest))) by
      (pose proof (Zlength_nonneg rest); lia).
    rewrite paren_level_upto_nat_cons.
    fold (paren_level_upto (Zlength rest) rest).
    rewrite IH.
    reflexivity.
Qed.

Lemma paren_sum_list_app : forall l1 l2,
  paren_sum_list (l1 ++ l2) = paren_sum_list l1 + paren_sum_list l2.
Proof.
  induction l1 as [| c rest IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma paren_total_app_comm : forall l1 l2,
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) =
  paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1).
Proof.
  intros l1 l2.
  repeat rewrite paren_level_upto_Zlength_sum.
  repeat rewrite paren_sum_list_app.
  lia.
Qed.

Lemma check_parens_z_inner_true_level : forall l depth,
  0 <= depth ->
  check_parens_z_inner l depth = true ->
  depth + paren_level_upto (Zlength l) l = 0.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hcheck.
  - simpl in Hcheck.
    apply Z.eqb_eq in Hcheck.
    unfold paren_level_upto; simpl.
    lia.
  - simpl in Hcheck.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + specialize (IH (depth + 1) ltac:(lia) Hcheck).
      rewrite Zlength_cons.
      unfold paren_level_upto.
      replace (Z.to_nat (Z.succ (Zlength rest))) with
        (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
      rewrite paren_level_upto_nat_cons.
      unfold paren_delta.
      rewrite Hopen, Z.eqb_refl.
      fold (paren_level_upto (Zlength rest) rest).
      lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * destruct (Z.eqb_spec depth 0); try discriminate.
        specialize (IH (depth - 1) ltac:(lia) Hcheck).
        rewrite Zlength_cons.
        unfold paren_level_upto.
        replace (Z.to_nat (Z.succ (Zlength rest))) with
          (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
        rewrite paren_level_upto_nat_cons.
        unfold paren_delta.
        rewrite Hclose.
        replace (Z.eqb 41 40) with false by reflexivity.
        rewrite Z.eqb_refl.
        fold (paren_level_upto (Zlength rest) rest).
        lia.
      * specialize (IH depth Hdepth Hcheck).
        rewrite Zlength_cons.
        unfold paren_level_upto.
        replace (Z.to_nat (Z.succ (Zlength rest))) with
          (S (Z.to_nat (Zlength rest))) by (pose proof (Zlength_nonneg rest); lia).
        rewrite paren_level_upto_nat_cons.
        unfold paren_delta.
        replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
        fold (paren_level_upto (Zlength rest) rest).
        lia.
Qed.

Lemma is_balanced_z_false_from_level : forall l,
  paren_level_upto (Zlength l) l <> 0 ->
  is_balanced_z l = false.
Proof.
  intros l Hlevel.
  unfold is_balanced_z.
  destruct (check_parens_z_inner l 0) eqn:Hcheck; auto.
  pose proof (check_parens_z_inner_true_level l 0 ltac:(lia) Hcheck).
  lia.
Qed.

Lemma check_parens_z_inner_true_prefix : forall l depth,
  0 <= depth ->
  check_parens_z_inner l depth = true ->
  forall k, 0 <= k < Zlength l ->
    0 <= depth + paren_level_upto (k + 1) l.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hcheck k Hk.
  - rewrite Zlength_nil in Hk. lia.
  - simpl in Hcheck.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + destruct (Z.eq_dec k 0) as [-> | Hk0].
      * replace (paren_level_upto (0 + 1) (c :: rest)) with 1.
        -- lia.
        -- replace (0 + 1) with 1 by lia.
           unfold paren_level_upto; simpl.
           unfold paren_delta. rewrite Hopen, Z.eqb_refl. lia.
      * assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
        specialize (IH (depth + 1) ltac:(lia) Hcheck (k - 1) H).
        rewrite paren_level_upto_cons_succ by lia.
        unfold paren_delta.
        rewrite Hopen, Z.eqb_refl.
        replace (k - 1 + 1) with k in IH by lia.
        replace (k + 1 - 1) with k by lia.
        lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * destruct (Z.eqb_spec depth 0); try discriminate.
        destruct (Z.eq_dec k 0) as [-> | Hk0].
        -- replace (paren_level_upto (0 + 1) (c :: rest)) with (-1).
           ++ assert (1 <= depth) by lia. lia.
           ++ replace (0 + 1) with 1 by lia.
              unfold paren_level_upto; simpl.
              unfold paren_delta. rewrite Hclose.
              change (Znth 0 (c :: rest) 0) with c.
              replace (Z.eqb 41 40) with false by reflexivity.
              rewrite Z.eqb_refl. reflexivity.
        -- assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
           specialize (IH (depth - 1) ltac:(lia) Hcheck (k - 1) H).
           rewrite paren_level_upto_cons_succ by lia.
           unfold paren_delta.
           rewrite Hclose.
           replace (Z.eqb 41 40) with false by reflexivity.
           rewrite Z.eqb_refl.
           replace (k - 1 + 1) with k in IH by lia.
           replace (k + 1 - 1) with k by lia.
           lia.
      * destruct (Z.eq_dec k 0) as [-> | Hk0].
        -- replace (paren_level_upto (0 + 1) (c :: rest)) with 0.
           ++ lia.
           ++ replace (0 + 1) with 1 by lia.
              unfold paren_level_upto; simpl.
              unfold paren_delta.
              change (Znth 0 (c :: rest) 0) with c.
              replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
              replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
              reflexivity.
        -- assert (0 <= k - 1 < Zlength rest) by (rewrite Zlength_cons in Hk; lia).
           specialize (IH depth Hdepth Hcheck (k - 1) H).
           rewrite paren_level_upto_cons_succ by lia.
           unfold paren_delta.
           replace (Z.eqb c 40) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false by (symmetry; apply Z.eqb_neq; lia).
           replace (k - 1 + 1) with k in IH by lia.
           replace (k + 1 - 1) with k by lia.
           lia.
Qed.

Lemma paren_good_prefix_bool_nat_true_iff : forall n l,
  paren_good_prefix_bool_nat n l = true <->
  forall k, 0 <= k < Z.of_nat n -> 0 <= paren_level_upto (k + 1) l.
Proof.
  induction n as [| n IH]; intros l; simpl.
  - split.
    + intros _ k Hk. lia.
    + intros _. reflexivity.
  - rewrite andb_true_iff.
    rewrite IH.
    split.
    + intros [Hprefix Hlast] k Hk.
      destruct (Z_lt_ge_dec k (Z.of_nat n)).
      * apply Hprefix. lia.
      * assert (k = Z.of_nat n) by lia. subst k.
        apply Z.leb_le in Hlast. exact Hlast.
    + intros Hprefix.
      split.
      * intros k Hk. apply Hprefix. lia.
      * apply Z.leb_le. apply Hprefix. lia.
Qed.

Lemma check_parens_z_inner_true_from_scan : forall l depth,
  0 <= depth ->
  (forall k, 0 <= k < Zlength l ->
    0 <= depth + paren_level_upto (k + 1) l) ->
  depth + paren_level_upto (Zlength l) l = 0 ->
  check_parens_z_inner l depth = true.
Proof.
  induction l as [| c rest IH]; intros depth Hdepth Hprefix Hfinal.
  - rewrite Zlength_nil in Hfinal.
    rewrite paren_level_upto_0 in Hfinal.
    replace depth with 0 by lia.
    reflexivity.
  - simpl.
    pose proof (Hprefix 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia))
      as Hfirst.
    rewrite paren_level_upto_cons_succ in Hfirst by lia.
    replace (0 + 1 - 1) with 0 in Hfirst by lia.
    rewrite paren_level_upto_0 in Hfirst.
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + apply IH.
      * lia.
      * intros k Hk.
        specialize (Hprefix (k + 1)).
        rewrite paren_level_upto_cons_succ in Hprefix by lia.
        replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
        specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
        unfold paren_delta in Hprefix. rewrite Hopen, Z.eqb_refl in Hprefix. lia.
      * rewrite Zlength_cons in Hfinal.
        replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
        rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
        replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
        unfold paren_delta in Hfinal. rewrite Hopen, Z.eqb_refl in Hfinal. lia.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * assert (depth <> 0).
        { unfold paren_delta in Hfirst.
          rewrite Hclose in Hfirst.
          replace (Z.eqb 41 40) with false in Hfirst by reflexivity.
          rewrite Z.eqb_refl in Hfirst.
          lia. }
        replace (Z.eqb depth 0) with false by (symmetry; apply Z.eqb_neq; lia).
        apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Hprefix (k + 1)).
           rewrite paren_level_upto_cons_succ in Hprefix by lia.
           replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
           specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
           unfold paren_delta in Hprefix. rewrite Hclose in Hprefix.
           replace (Z.eqb 41 40) with false in Hprefix by reflexivity.
           rewrite Z.eqb_refl in Hprefix. lia.
        -- rewrite Zlength_cons in Hfinal.
           replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
           rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
           replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
           unfold paren_delta in Hfinal. rewrite Hclose in Hfinal.
           replace (Z.eqb 41 40) with false in Hfinal by reflexivity.
           rewrite Z.eqb_refl in Hfinal. lia.
      * apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Hprefix (k + 1)).
           rewrite paren_level_upto_cons_succ in Hprefix by lia.
           replace (k + 1 + 1 - 1) with (k + 1) in Hprefix by lia.
           specialize (Hprefix ltac:(rewrite Zlength_cons; lia)).
           unfold paren_delta in Hprefix.
           replace (Z.eqb c 40) with false in Hprefix by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false in Hprefix by (symmetry; apply Z.eqb_neq; lia).
           lia.
        -- rewrite Zlength_cons in Hfinal.
           replace (Z.succ (Zlength rest)) with (Zlength rest + 1) in Hfinal by lia.
           rewrite paren_level_upto_cons_succ in Hfinal by (pose proof (Zlength_nonneg rest); lia).
           replace (Z.succ (Zlength rest) - 1) with (Zlength rest) in Hfinal by lia.
           unfold paren_delta in Hfinal.
           replace (Z.eqb c 40) with false in Hfinal by (symmetry; apply Z.eqb_neq; lia).
           replace (Z.eqb c 41) with false in Hfinal by (symmetry; apply Z.eqb_neq; lia).
           lia.
Qed.

Lemma check_parens_z_true_from_scan : forall l,
  paren_level_upto (Zlength l) l = 0 ->
  paren_good_prefix_flag (Zlength l) l = 1 ->
  is_balanced_z l = true.
Proof.
  intros l Hlevel Hflag.
  unfold is_balanced_z.
  apply check_parens_z_inner_true_from_scan.
  - lia.
  - intros k Hk.
    unfold paren_good_prefix_flag in Hflag.
    destruct (paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l) eqn:Hb; try discriminate.
    pose proof (proj1 (paren_good_prefix_bool_nat_true_iff (Z.to_nat (Zlength l)) l) Hb) as Hprefix.
    apply Hprefix.
    rewrite Z2Nat.id by (pose proof (Zlength_nonneg l); lia).
    lia.
  - lia.
Qed.

Lemma is_balanced_z_false_from_flag : forall l,
  paren_level_upto (Zlength l) l = 0 ->
  paren_good_prefix_flag (Zlength l) l = 0 ->
  is_balanced_z l = false.
Proof.
  intros l Hlevel Hflag.
  destruct (is_balanced_z l) eqn:Hbal; auto.
  unfold is_balanced_z in Hbal.
  pose proof (check_parens_z_inner_true_prefix l 0 ltac:(lia) Hbal) as Hprefix.
  unfold paren_good_prefix_flag in Hflag.
  destruct (paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l) eqn:Hb; try discriminate.
  exfalso.
  assert (Htrue : paren_good_prefix_bool_nat (Z.to_nat (Zlength l)) l = true).
  {
    apply (proj2 (paren_good_prefix_bool_nat_true_iff (Z.to_nat (Zlength l)) l)).
    intros k Hk.
    apply Hprefix.
    rewrite Z2Nat.id in Hk by (pose proof (Zlength_nonneg l); lia).
    lia.
  }
  rewrite Hb in Htrue. discriminate.
Qed.

Lemma ascii_of_z_paren_open : ascii_of_z 40 = "("%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_paren_close : ascii_of_z 41 = ")"%char.
Proof. reflexivity. Qed.

Lemma check_parens_z_inner_correct : forall l depth,
  ascii_range_z l ->
  check_parens_inner (map ascii_of_z l) depth =
  check_parens_z_inner l (Z.of_nat depth).
Proof.
  induction l as [| c rest IH]; intros depth Hrange.
  - simpl.
    destruct depth; reflexivity.
  - simpl.
    assert (Hc : 0 <= c < 256).
    { change c with (Znth 0 (c :: rest) 0).
      apply Hrange.
      rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest); lia. }
    assert (Hrest : ascii_range_z rest).
    { intros i Hi.
      pose proof (Hrange (i + 1)) as Htail.
      rewrite Znth_cons in Htail by lia.
      replace (i + 1 - 1) with i in Htail by lia.
      apply Htail.
      rewrite Zlength_cons.
      lia. }
    destruct (Z.eqb_spec c 40) as [Hopen | Hnopen].
    + subst c. rewrite ascii_of_z_paren_open. simpl.
      replace (Z.of_nat depth + 1) with (Z.of_nat (S depth)) by lia.
      apply IH. exact Hrest.
    + destruct (Z.eqb_spec c 41) as [Hclose | Hnclose].
      * subst c. rewrite ascii_of_z_paren_close. simpl.
        destruct depth as [| depth']; simpl.
        -- reflexivity.
        -- replace (match Pos.of_succ_nat depth' with
                    | (p~1)%positive => Z.pos p~0
                    | (p~0)%positive => Z.pos (Pos.pred_double p)
                    | 1%positive => 0
                    end) with (Z.of_nat (S depth') - 1) by reflexivity.
           replace (Z.of_nat (S depth') - 1) with (Z.of_nat depth') by lia.
           apply IH. exact Hrest.
      * destruct (ascii_dec (ascii_of_z c) "("%char) as [Ha | Ha].
        -- apply f_equal with (f := nat_of_ascii) in Ha.
           rewrite nat_of_ascii_ascii_of_z in Ha by lia.
           change (nat_of_ascii "("%char) with 40%nat in Ha.
           lia.
        -- destruct (ascii_dec (ascii_of_z c) ")"%char) as [Hb | Hb].
           ++ apply f_equal with (f := nat_of_ascii) in Hb.
              rewrite nat_of_ascii_ascii_of_z in Hb by lia.
              change (nat_of_ascii ")"%char) with 41%nat in Hb.
              lia.
           ++ destruct (ascii_of_z c) as [b0 b1 b2 b3 b4 b5 b6 b7] eqn:Hasc;
              destruct b0, b1, b2, b3, b4, b5, b6, b7;
              simpl in *; try contradiction; apply IH; exact Hrest.
Qed.

Lemma is_balanced_string_of_list_z_correct : forall l,
  ascii_range_z l ->
  is_balanced (list_ascii_of_string (string_of_list_z l)) = is_balanced_z l.
Proof.
  intros l Hrange.
  rewrite list_ascii_of_string_string_of_list_z.
  unfold is_balanced_z.
  unfold is_balanced.
  apply check_parens_z_inner_correct.
  exact Hrange.
Qed.

Lemma ascii_of_z_open_inv : forall z,
  0 <= z < 256 ->
  ascii_of_z z = "("%char ->
  z = 40.
Proof.
  intros z Hz H.
  apply f_equal with (f := nat_of_ascii) in H.
  rewrite nat_of_ascii_ascii_of_z in H by lia.
  change (nat_of_ascii "("%char) with 40%nat in H.
  lia.
Qed.

Lemma ascii_of_z_close_inv : forall z,
  0 <= z < 256 ->
  ascii_of_z z = ")"%char ->
  z = 41.
Proof.
  intros z Hz H.
  apply f_equal with (f := nat_of_ascii) in H.
  rewrite nat_of_ascii_ascii_of_z in H by lia.
  change (nat_of_ascii ")"%char) with 41%nat in H.
  lia.
Qed.

Lemma problem_119_pre_z_l1_char : forall l1 l2 i,
  problem_119_pre_z l1 l2 ->
  ascii_range_z l1 ->
  0 <= i < Zlength l1 ->
  Znth i l1 0 = 40 \/ Znth i l1 0 = 41.
Proof.
  intros l1 l2 i Hpre Hrange Hi.
  unfold problem_119_pre_z, problem_119_pre in Hpre.
  destruct Hpre as [_ Hforall].
  inversion Hforall as [| ? ? Hs1 Htail]; subst.
  rewrite list_ascii_of_string_string_of_list_z in Hs1.
  assert (Hin : In (Znth i l1 0) l1).
  {
    unfold Znth.
    apply nth_In.
    rewrite <- z_to_nat_Zlength.
    lia.
  }
  apply In_nth_error in Hin as [n Hnth].
  assert (Hmap : In (ascii_of_z (Znth i l1 0)) (map ascii_of_z l1)).
  { apply in_map. apply nth_error_In in Hnth. exact Hnth. }
  rewrite Forall_forall in Hs1.
  specialize (Hs1 _ Hmap).
  destruct Hs1 as [Hopen | Hclose].
  - left. apply ascii_of_z_open_inv; [apply Hrange; lia | exact Hopen].
  - right. apply ascii_of_z_close_inv; [apply Hrange; lia | exact Hclose].
Qed.

Lemma problem_119_pre_z_l2_char : forall l1 l2 i,
  problem_119_pre_z l1 l2 ->
  ascii_range_z l2 ->
  0 <= i < Zlength l2 ->
  Znth i l2 0 = 40 \/ Znth i l2 0 = 41.
Proof.
  intros l1 l2 i Hpre Hrange Hi.
  unfold problem_119_pre_z, problem_119_pre in Hpre.
  destruct Hpre as [_ Hforall].
  inversion Hforall as [| ? ? _ Htail]; subst.
  inversion Htail as [| ? ? Hs2 _]; subst.
  rewrite list_ascii_of_string_string_of_list_z in Hs2.
  assert (Hin : In (Znth i l2 0) l2).
  {
    unfold Znth.
    apply nth_In.
    rewrite <- z_to_nat_Zlength.
    lia.
  }
  apply In_nth_error in Hin as [n Hnth].
  assert (Hmap : In (ascii_of_z (Znth i l2 0)) (map ascii_of_z l2)).
  { apply in_map. apply nth_error_In in Hnth. exact Hnth. }
  rewrite Forall_forall in Hs2.
  specialize (Hs2 _ Hmap).
  destruct Hs2 as [Hopen | Hclose].
  - left. apply ascii_of_z_open_inv; [apply Hrange; lia | exact Hopen].
  - right. apply ascii_of_z_close_inv; [apply Hrange; lia | exact Hclose].
Qed.

Lemma problem_119_spec_z_true_left : forall l1 l2,
  ascii_range_z l1 ->
  ascii_range_z l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l1 ++ l2)) (l1 ++ l2) = 1 ->
  problem_119_spec_z l1 l2 1.
Proof.
  intros l1 l2 Hrange1 Hrange2 Hlevel Hflag.
  unfold problem_119_spec_z, problem_119_spec, match_parens, match_parens_impl, yesno_of_z_119.
  simpl.
  replace (Z.eqb 1 1) with true by reflexivity.
  rewrite !list_ascii_of_string_string_of_list_z.
  rewrite <- map_app.
  rewrite <- list_ascii_of_string_string_of_list_z.
  rewrite is_balanced_string_of_list_z_correct.
  rewrite check_parens_z_true_from_scan by eauto.
  reflexivity.
  intros i Hi.
  rewrite Zlength_app in Hi.
  destruct (Z_lt_ge_dec i (Zlength l1)).
  - rewrite Znth_app_left_119 by lia. apply Hrange1. lia.
  - rewrite Znth_app_right_119 by lia. apply Hrange2. lia.
Qed.

Lemma problem_119_spec_z_true_right : forall l1 l2,
  ascii_range_z l1 ->
  ascii_range_z l2 ->
  paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) = 0 ->
  paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 1 ->
  problem_119_spec_z l1 l2 1.
Proof.
  intros l1 l2 Hrange1 Hrange2 Hlevel Hflag.
  unfold problem_119_spec_z, problem_119_spec, match_parens, match_parens_impl, yesno_of_z_119.
  simpl.
  replace (Z.eqb 1 1) with true by reflexivity.
  rewrite !list_ascii_of_string_string_of_list_z.
  repeat rewrite <- map_app.
  repeat rewrite <- list_ascii_of_string_string_of_list_z.
  rewrite is_balanced_string_of_list_z_correct.
  destruct (is_balanced_z (l1 ++ l2)); simpl; try reflexivity.
  2:{
    intros i Hi.
    rewrite Zlength_app in Hi.
    destruct (Z_lt_ge_dec i (Zlength l1)).
    - rewrite Znth_app_left_119 by lia. apply Hrange1. lia.
    - rewrite Znth_app_right_119 by lia. apply Hrange2. lia.
  }
  rewrite is_balanced_string_of_list_z_correct.
  rewrite check_parens_z_true_from_scan by eauto.
  reflexivity.
  intros i Hi.
  rewrite Zlength_app in Hi.
  destruct (Z_lt_ge_dec i (Zlength l2)).
  - rewrite Znth_app_left_119 by lia. apply Hrange2. lia.
  - rewrite Znth_app_right_119 by lia. apply Hrange1. lia.
Qed.

Lemma problem_119_spec_z_false_from_level : forall l1 l2,
  ascii_range_z l1 ->
  ascii_range_z l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) <> 0 ->
  problem_119_spec_z l1 l2 0.
Proof.
  intros l1 l2 Hrange1 Hrange2 Hlevel.
  unfold problem_119_spec_z, problem_119_spec, match_parens, match_parens_impl, yesno_of_z_119.
  simpl.
  replace (Z.eqb 0 1) with false by reflexivity.
  rewrite !list_ascii_of_string_string_of_list_z.
  repeat rewrite <- map_app.
  repeat rewrite <- list_ascii_of_string_string_of_list_z.
  repeat rewrite is_balanced_string_of_list_z_correct.
  rewrite is_balanced_z_false_from_level by exact Hlevel.
  assert (Hlevel2 : paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) <> 0).
  { rewrite <- paren_total_app_comm. exact Hlevel. }
  rewrite is_balanced_z_false_from_level by exact Hlevel2.
  reflexivity.
  - intros i Hi.
    rewrite Zlength_app in Hi.
    destruct (Z_lt_ge_dec i (Zlength l2)).
    + rewrite Znth_app_left_119 by lia. apply Hrange2. lia.
    + rewrite Znth_app_right_119 by lia. apply Hrange1. lia.
  - intros i Hi.
    rewrite Zlength_app in Hi.
    destruct (Z_lt_ge_dec i (Zlength l1)).
    + rewrite Znth_app_left_119 by lia. apply Hrange1. lia.
    + rewrite Znth_app_right_119 by lia. apply Hrange2. lia.
Qed.

Lemma problem_119_spec_z_false_from_flags : forall l1 l2,
  ascii_range_z l1 ->
  ascii_range_z l2 ->
  paren_level_upto (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l1 ++ l2)) (l1 ++ l2) = 0 ->
  paren_good_prefix_flag (Zlength (l2 ++ l1)) (l2 ++ l1) = 0 ->
  problem_119_spec_z l1 l2 0.
Proof.
  intros l1 l2 Hrange1 Hrange2 Hlevel Hflag12 Hflag21.
  unfold problem_119_spec_z, problem_119_spec, match_parens, match_parens_impl, yesno_of_z_119.
  simpl.
  replace (Z.eqb 0 1) with false by reflexivity.
  rewrite !list_ascii_of_string_string_of_list_z.
  repeat rewrite <- map_app.
  repeat rewrite <- list_ascii_of_string_string_of_list_z.
  repeat rewrite is_balanced_string_of_list_z_correct.
  rewrite is_balanced_z_false_from_flag by eauto.
  assert (Hlevel2 : paren_level_upto (Zlength (l2 ++ l1)) (l2 ++ l1) = 0).
  { rewrite <- paren_total_app_comm. exact Hlevel. }
  rewrite is_balanced_z_false_from_flag by eauto.
  reflexivity.
  - intros i Hi.
    rewrite Zlength_app in Hi.
    destruct (Z_lt_ge_dec i (Zlength l2)).
    + rewrite Znth_app_left_119 by lia. apply Hrange2. lia.
    + rewrite Znth_app_right_119 by lia. apply Hrange1. lia.
  - intros i Hi.
    rewrite Zlength_app in Hi.
    destruct (Z_lt_ge_dec i (Zlength l1)).
    + rewrite Znth_app_left_119 by lia. apply Hrange1. lia.
    + rewrite Znth_app_right_119 by lia. apply Hrange2. lia.
Qed.
