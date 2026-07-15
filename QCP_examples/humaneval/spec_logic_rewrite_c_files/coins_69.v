Load "../spec/69".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_69_pre_z (lst : list Z) : Prop :=
  problem_69_pre lst.

Definition problem_69_spec_z (lst : list Z) (y : Z) : Prop :=
  problem_69_spec lst y.

Definition count_z_69 (z : Z) (lst : list Z) : Z :=
  Z.of_nat (count z lst).

Definition count_prefix_69 (z i : Z) (lst : list Z) : Z :=
  count_z_69 z (sublist 0 i lst).

Definition find_max_prefix_69 (lst : list Z) (i : Z) : Z :=
  find_max_satisfying lst (sublist 0 i lst) (-1).

Definition update_best_69 (best x freq : Z) : Z :=
  if freq >=? x then Z.max x best else best.

Definition list_positive_int_range_69 (lst : list Z) : Prop :=
  Forall (fun x => 1 <= x <= INT_MAX) lst.

Lemma sublist_snoc_Znth_69 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma count_app_single_69 : forall x y l,
  count x (l ++ [y]) =
    (count x l + if Z.eqb x y then 1 else 0)%nat.
Proof.
  intros x y l.
  unfold count.
  rewrite filter_app, app_length.
  cbn [filter length].
  destruct (Z.eqb x y); reflexivity.
Qed.

Lemma count_prefix_step_hit_69 : forall x i l,
  0 <= i < Zlength l ->
  Znth i l 0 = x ->
  count_prefix_69 x (i + 1) l = count_prefix_69 x i l + 1.
Proof.
  intros x i l Hi Hx.
  unfold count_prefix_69, count_z_69.
  rewrite sublist_snoc_Znth_69 by lia.
  rewrite count_app_single_69.
  rewrite Hx, Z.eqb_refl.
  lia.
Qed.

Lemma count_prefix_step_miss_69 : forall x i l,
  0 <= i < Zlength l ->
  Znth i l 0 <> x ->
  count_prefix_69 x (i + 1) l = count_prefix_69 x i l.
Proof.
  intros x i l Hi Hx.
  unfold count_prefix_69, count_z_69.
  rewrite sublist_snoc_Znth_69 by lia.
  rewrite count_app_single_69.
  destruct (Z.eqb_spec x (Znth i l 0)); lia.
Qed.

Lemma count_prefix_full_69 : forall x l n,
  n = Zlength l ->
  count_prefix_69 x n l = count_z_69 x l.
Proof.
  intros x l n Hn.
  subst n.
  unfold count_prefix_69.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma count_prefix_nonneg_69 : forall x i l,
  0 <= count_prefix_69 x i l.
Proof.
  intros x i l.
  unfold count_prefix_69, count_z_69.
  lia.
Qed.

Lemma count_prefix_le_len_69 : forall x i l,
  0 <= i <= Zlength l ->
  count_prefix_69 x i l <= i.
Proof.
  intros x i l Hi.
  unfold count_prefix_69, count_z_69, count.
  pose proof (filter_length (fun h : Z => (x =? h)%Z) (sublist 0 i l)) as Hlen_nat.
  assert (Hlen_nat_le :
            (length (filter (fun h : Z => (x =? h)%Z) (sublist 0 i l)) <=
             length (sublist 0 i l))%nat).
  {
    rewrite <- Hlen_nat.
    apply Nat.le_add_r.
  }
  assert (Hlen : Z.of_nat (length (filter (fun h : Z => (x =? h)%Z) (sublist 0 i l))) <=
                 Z.of_nat (length (sublist 0 i l))).
  {
    apply Nat2Z.inj_le.
    exact Hlen_nat_le.
  }
  replace (Z.of_nat (length (sublist 0 i l))) with (Zlength (sublist 0 i l)) in Hlen
    by (rewrite Zlength_correct; reflexivity).
  rewrite Zlength_sublist0 in Hlen by lia.
  exact Hlen.
Qed.

Lemma Znth_In_range_69 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma list_positive_int_range_Znth_69 : forall l i,
  list_positive_int_range_69 l ->
  0 <= i < Zlength l ->
  1 <= Znth i l 0 <= INT_MAX.
Proof.
  intros l i Hrange Hi.
  unfold list_positive_int_range_69 in Hrange.
  rewrite Forall_forall in Hrange.
  apply Hrange.
  apply Znth_In_range_69.
  exact Hi.
Qed.

Lemma update_best_miss_69 : forall best x freq,
  freq < x ->
  update_best_69 best x freq = best.
Proof.
  intros best x freq Hlt.
  unfold update_best_69.
  destruct (Z.geb_spec freq x); lia.
Qed.

Lemma update_best_hit_gt_69 : forall best x freq,
  freq >= x ->
  x > best ->
  update_best_69 best x freq = x.
Proof.
  intros best x freq Hge Hgt.
  unfold update_best_69.
  destruct (Z.geb_spec freq x); [apply Z.max_l; lia | lia].
Qed.

Lemma update_best_hit_le_69 : forall best x freq,
  freq >= x ->
  x <= best ->
  update_best_69 best x freq = best.
Proof.
  intros best x freq Hge Hle.
  unfold update_best_69.
  destruct (Z.geb_spec freq x); [apply Z.max_r; lia | lia].
Qed.

Lemma update_best_bounds_69 : forall best x freq,
  -1 <= best <= INT_MAX ->
  1 <= x <= INT_MAX ->
  -1 <= update_best_69 best x freq <= INT_MAX.
Proof.
  intros best x freq Hbest Hx.
  unfold update_best_69.
  destruct (freq >=? x); pose proof (Z.max_spec x best); lia.
Qed.

Lemma find_max_prefix_step_69 : forall l i,
  0 <= i < Zlength l ->
  find_max_prefix_69 l (i + 1) =
  update_best_69 (find_max_prefix_69 l i) (Znth i l 0) (count_z_69 (Znth i l 0) l).
Proof.
  intros l i Hi.
  unfold find_max_prefix_69, update_best_69, count_z_69.
  rewrite sublist_snoc_Znth_69 by lia.
  unfold find_max_satisfying.
  rewrite fold_left_app.
  cbn [fold_left].
  reflexivity.
Qed.

Lemma find_max_prefix_init_69 : forall l,
  find_max_prefix_69 l 0 = -1.
Proof.
  intros l.
  unfold find_max_prefix_69.
  unfold sublist.
  cbn.
  reflexivity.
Qed.

Lemma find_max_prefix_bounds_69 : forall l i,
  0 <= i <= Zlength l ->
  list_positive_int_range_69 l ->
  -1 <= find_max_prefix_69 l i <= INT_MAX.
Proof.
  intros l i Hi Hrange.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  assert (Hle : Z.of_nat (Z.to_nat i) <= Zlength l) by lia.
  clear Hi.
  induction (Z.to_nat i) as [| n IH].
  - rewrite Nat2Z.inj_0, find_max_prefix_init_69; lia.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite find_max_prefix_step_69 by lia.
    apply update_best_bounds_69.
    + apply IH; lia.
    + apply list_positive_int_range_Znth_69; lia || exact Hrange.
Qed.

Lemma find_max_prefix_full_spec_69 : forall l y,
  problem_69_pre_z l ->
  y = find_max_prefix_69 l (Zlength l) ->
  problem_69_spec_z l y.
Proof.
  intros l y Hpre Hy.
  unfold problem_69_spec_z, problem_69_spec, search_impl.
  destruct l as [| h t].
  - unfold problem_69_pre_z, problem_69_pre in Hpre.
    destruct Hpre as [Hne _].
    contradiction Hne; reflexivity.
  - subst y.
    unfold find_max_prefix_69.
    rewrite sublist_self by reflexivity.
    destruct (find_max_satisfying (h :: t) (h :: t) (-1) =? -1) eqn:Hm.
    + apply Z.eqb_eq in Hm. exact Hm.
    + reflexivity.
Qed.
