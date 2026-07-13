Load "../spec/121".

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Logic.LogicGenerator.demo932.Interface.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_121_pre_z (lst : list Z) : Prop :=
  problem_121_pre (map Z.to_nat lst).

Definition problem_121_spec_z (lst : list Z) (out : Z) : Prop :=
  problem_121_spec (map Z.to_nat lst) (Z.to_nat out).

Definition even_pos_indices_121 (i : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat i)).

Definition add_term_121 (lst : list Z) (k : Z) : Z :=
  let x := Znth (2 * k) lst 0 in
  if Z.eqb (Z.rem x 2) 1 then x else 0.

Definition sum_prefix_121 (i : Z) (lst : list Z) : Z :=
  fold_left Z.add (map (add_term_121 lst) (even_pos_indices_121 i)) 0.

Definition INT_MIN_121 : Z := -2147483648.

Definition sum_121_int_range (lst : list Z) : Prop :=
  Forall (fun x => 0 <= x <= INT_MAX) lst /\
  forall i,
    0 <= i ->
    2 * i < Zlength lst ->
    0 <= sum_prefix_121 i lst <= INT_MAX /\
    0 <= sum_prefix_121 i lst + Znth (2 * i) lst 0 <= INT_MAX /\
    0 <= sum_prefix_121 (i + 1) lst <= INT_MAX.

Lemma sum_121_int_range_nonneg : forall lst,
  sum_121_int_range lst ->
  Forall (fun x => 0 <= x) lst.
Proof.
  intros lst [Hall _].
  eapply Forall_impl; [| exact Hall].
  intros x Hx. destruct Hx; lia.
Qed.

Definition selected_indices_nat_121 (l : list nat) : list nat :=
  filter (fun i => Nat.even i && Nat.odd (nth i l 0%nat)) (seq 0 (length l)).

Definition selected_values_nat_121 (l : list nat) : list nat :=
  map (fun i => nth i l 0%nat) (selected_indices_nat_121 l).

Lemma selected_Forall2_map_121 : forall l ids,
  Forall
    (fun i => nth_error l i = Some (nth i l 0%nat) /\
              Nat.Even i /\
              Nat.Odd (nth i l 0%nat))
    ids ->
  Forall2
    (fun i x => nth_error l i = Some x /\ Nat.Even i /\ Nat.Odd x)
    ids
    (map (fun i => nth i l 0%nat) ids).
Proof.
  intros l ids H.
  induction H as [| i ids Hi _ IH]; cbn.
  - constructor.
  - constructor; [exact Hi | exact IH].
Qed.

Lemma selected_indices_nat_121_spec : forall l,
  selected l (selected_indices_nat_121 l) (selected_values_nat_121 l).
Proof.
  intros l.
  unfold selected, selected_values_nat_121.
  split.
  - unfold selected_indices_nat_121.
    apply NoDup_filter. apply seq_NoDup.
  - split.
    + apply selected_Forall2_map_121.
      unfold selected_indices_nat_121.
      apply Forall_forall.
      intros i Hin.
      apply filter_In in Hin as [Hinseq Hpred].
      apply in_seq in Hinseq as [_ Hlt].
      apply andb_true_iff in Hpred as [Heven Hodd].
      repeat split.
      * apply nth_error_nth'. lia.
      * apply Nat.even_spec. exact Heven.
      * apply Nat.odd_spec. exact Hodd.
    + intros i x Hnth Heven Hodd.
      unfold selected_indices_nat_121.
      apply filter_In.
      split.
      * apply in_seq.
        split; [lia |].
        apply (proj1 (nth_error_Some l i)).
        rewrite Hnth.
        discriminate.
      * apply andb_true_iff.
        split.
        -- apply Nat.even_spec. exact Heven.
        -- rewrite (nth_error_nth l i 0%nat Hnth).
           apply Nat.odd_spec. exact Hodd.
Qed.

Fixpoint pair_sum_nat_121 (l : list nat) : nat :=
  match l with
  | [] => 0
  | [a] => if Nat.odd a then a else 0
  | a :: _ :: xs => (if Nat.odd a then a else 0) + pair_sum_nat_121 xs
  end.

Fixpoint pair_indices_nat_121 (base : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | [a] => if Nat.odd a then [base] else []
  | a :: _ :: xs =>
      (if Nat.odd a then [base] else []) ++ pair_indices_nat_121 (base + 2)%nat xs
  end.

Fixpoint pair_values_nat_121 (l : list nat) : list nat :=
  match l with
  | [] => []
  | [a] => if Nat.odd a then [a] else []
  | a :: _ :: xs =>
      (if Nat.odd a then [a] else []) ++ pair_values_nat_121 xs
  end.

Lemma pair_values_nat_sum_121 : forall l,
  fold_right Nat.add 0%nat (pair_values_nat_121 l) = pair_sum_nat_121 l.
Proof.
  fix IH 1.
  intros [| a [| b xs]]; cbn.
  - reflexivity.
  - destruct (Nat.odd a); cbn; lia.
  - rewrite <- IH.
    destruct (Nat.odd a); cbn; lia.
Qed.

Lemma pair_indices_nat_ge_121 : forall l base i,
  In i (pair_indices_nat_121 base l) ->
  (base <= i)%nat.
Proof.
  fix IH 1.
  intros [| a [| b xs]] base i Hin; cbn in Hin.
  - contradiction.
  - destruct (Nat.odd a); cbn in Hin; lia.
  - destruct (Nat.odd a); cbn in Hin.
    + destruct Hin as [-> | Hin]; [lia |].
      specialize (IH xs (base + 2)%nat i Hin). lia.
    + specialize (IH xs (base + 2)%nat i Hin). lia.
Qed.

Lemma pair_indices_nat_NoDup_121 : forall l base,
  NoDup (pair_indices_nat_121 base l).
Proof.
  fix IH 1.
  intros [| a [| b xs]] base; cbn.
  - constructor.
  - destruct (Nat.odd a).
    + constructor; [cbn; tauto | constructor].
    + constructor.
  - destruct (Nat.odd a) eqn:Ha; cbn.
    + constructor.
      * intros Hin.
        pose proof (pair_indices_nat_ge_121 xs (base + 2)%nat base Hin).
        lia.
      * apply (IH xs).
    + apply (IH xs).
Qed.

Lemma pair_indices_nat_complete_121 : forall l base i x,
  Nat.Even base ->
  nth_error l i = Some x ->
  Nat.Even (base + i) ->
  Nat.Odd x ->
  In (base + i)%nat (pair_indices_nat_121 base l).
Proof.
  fix IH 1.
  intros [| a [| b xs]] base i x Hbase Hnth Heven Hodd; cbn in *.
  - destruct i; discriminate Hnth.
  - destruct i as [| i]; cbn in Hnth; [| destruct i; discriminate Hnth].
    injection Hnth as ->.
    apply Nat.odd_spec in Hodd.
    rewrite Hodd.
    cbn. auto.
  - destruct i as [| [| i]]; cbn in Hnth.
    + injection Hnth as ->.
      apply Nat.odd_spec in Hodd.
      rewrite Hodd.
      cbn. auto.
    + exfalso.
      destruct Hbase as [k Hbase].
      destruct Heven as [m Heven].
      lia.
    + destruct (Nat.odd a) eqn:Ha; cbn.
      * right.
        replace (base + S (S i))%nat with ((base + 2) + i)%nat by lia.
        eapply (IH xs).
        -- destruct Hbase as [k ->]. exists (S k). lia.
        -- exact Hnth.
        -- replace ((base + 2) + i)%nat with (base + S (S i))%nat by lia.
           exact Heven.
        -- exact Hodd.
      * replace (base + S (S i))%nat with ((base + 2) + i)%nat by lia.
        eapply (IH xs).
        -- destruct Hbase as [k ->]. exists (S k). lia.
        -- exact Hnth.
        -- replace ((base + 2) + i)%nat with (base + S (S i))%nat by lia.
           exact Heven.
        -- exact Hodd.
Qed.

Lemma pair_indices_values_Forall2_121 : forall l base,
  Nat.Even base ->
  Forall2
    (fun i x => (base <= i)%nat /\ nth_error l (i - base) = Some x /\ Nat.Even i /\ Nat.Odd x)
    (pair_indices_nat_121 base l)
    (pair_values_nat_121 l).
Proof.
  fix IH 1.
  intros [| a [| b xs]] base Hbase; cbn.
  - constructor.
  - destruct (Nat.odd a) eqn:Ha; cbn.
    + constructor; [| constructor].
      repeat split.
      * lia.
      * replace (base - base)%nat with 0%nat by lia. reflexivity.
      * exact Hbase.
      * apply Nat.odd_spec. exact Ha.
    + constructor.
  - destruct (Nat.odd a) eqn:Ha; cbn.
	    + constructor.
	      * repeat split.
	        -- lia.
	        -- replace (base - base)%nat with 0%nat by lia. reflexivity.
	        -- exact Hbase.
	        -- apply Nat.odd_spec. exact Ha.
      * eapply (@Forall2_impl nat nat
            (fun i x => (base + 2 <= i)%nat /\ nth_error xs (i - (base + 2)) = Some x /\ Nat.Even i /\ Nat.Odd x)
            (fun i x => (base <= i)%nat /\ nth_error (a :: b :: xs) (i - base) = Some x /\ Nat.Even i /\ Nat.Odd x)).
	        -- intros i x (Hge & Hnth & Heven & Hodd).
	           repeat split.
	           ++ lia.
	           ++ replace (i - base)%nat with (S (S (i - (base + 2))))%nat by lia.
	              cbn. exact Hnth.
	           ++ exact Heven.
	           ++ exact Hodd.
        -- apply (IH xs). destruct Hbase as [k ->]. exists (S k). lia.
    + eapply (@Forall2_impl nat nat
          (fun i x => (base + 2 <= i)%nat /\ nth_error xs (i - (base + 2)) = Some x /\ Nat.Even i /\ Nat.Odd x)
          (fun i x => (base <= i)%nat /\ nth_error (a :: b :: xs) (i - base) = Some x /\ Nat.Even i /\ Nat.Odd x)).
	      * intros i x (Hge & Hnth & Heven & Hodd).
	        repeat split.
	        -- lia.
	        -- replace (i - base)%nat with (S (S (i - (base + 2))))%nat by lia.
	           cbn. exact Hnth.
	        -- exact Heven.
	        -- exact Hodd.
      * apply (IH xs). destruct Hbase as [k ->]. exists (S k). lia.
Qed.

Lemma pair_selected_nat_121 : forall l,
  selected l (pair_indices_nat_121 0 l) (pair_values_nat_121 l).
Proof.
  intros l.
  unfold selected.
  split.
  - apply pair_indices_nat_NoDup_121.
  - split.
    + eapply (@Forall2_impl nat nat
          (fun i x => (0 <= i)%nat /\ nth_error l (i - 0) = Some x /\ Nat.Even i /\ Nat.Odd x)
          (fun i x => nth_error l i = Some x /\ Nat.Even i /\ Nat.Odd x)).
      * intros i x (_ & Hnth & Heven & Hodd).
        replace (i - 0)%nat with i in Hnth by lia.
        repeat split; assumption.
      * apply pair_indices_values_Forall2_121. exists 0%nat. reflexivity.
    + intros i x Hnth Heven Hodd.
      replace i with (0 + i)%nat by lia.
      eapply pair_indices_nat_complete_121; eauto.
      exists 0%nat. reflexivity.
Qed.

Lemma pair_sum_nat_problem_spec_121 : forall l,
  problem_121_spec l (pair_sum_nat_121 l).
Proof.
  intros l.
  exists (pair_indices_nat_121 0 l), (pair_values_nat_121 l).
  split.
  - apply pair_selected_nat_121.
  - symmetry. apply pair_values_nat_sum_121.
Qed.

Fixpoint pair_sum_z_121 (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | [a] => if Z.eqb (Z.rem a 2) 1 then a else 0
  | a :: _ :: xs => (if Z.eqb (Z.rem a 2) 1 then a else 0) + pair_sum_z_121 xs
  end.

Lemma zrem_1_nat_odd_121 : forall x,
  0 <= x ->
  Z.eqb (Z.rem x 2) 1 = Nat.odd (Z.to_nat x).
Proof.
  intros x Hx.
  destruct (Nat.odd (Z.to_nat x)) eqn:Hodd.
  - apply Z.eqb_eq.
    apply Nat.odd_spec in Hodd.
    destruct Hodd as [k Hk].
    replace x with (Z.of_nat (Z.to_nat x)) by lia.
    rewrite Hk.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    replace (Z.of_nat 2) with 2 by reflexivity.
    replace (Z.of_nat 1) with 1 by reflexivity.
    replace (2 * Z.of_nat k + 1) with (1 + Z.of_nat k * 2) by lia.
    rewrite Z.rem_add by lia.
    apply Z.rem_small. lia.
  - apply Z.eqb_neq.
    intros Hrem.
    assert (Hevenb : Nat.even (Z.to_nat x) = true).
    { rewrite <- Nat.negb_odd. rewrite Hodd. reflexivity. }
    apply Nat.even_spec in Hevenb.
    destruct Hevenb as [k Hk].
    replace x with (Z.of_nat (Z.to_nat x)) in Hrem by lia.
    rewrite Hk in Hrem.
    rewrite Nat2Z.inj_mul in Hrem.
    replace (Z.of_nat 2) with 2 in Hrem by reflexivity.
    replace (2 * Z.of_nat k) with (Z.of_nat k * 2) in Hrem by lia.
    rewrite Z.rem_mul in Hrem by lia.
    lia.
Qed.

Lemma pair_sum_z_nat_121 : forall lst,
  Forall (fun x => 0 <= x) lst ->
  pair_sum_z_121 lst = Z.of_nat (pair_sum_nat_121 (map Z.to_nat lst)).
Proof.
  fix IH 1.
  intros [| a [| b xs]] Hall; cbn in *.
  - reflexivity.
  - inversion Hall as [| ? ? Ha _].
    rewrite zrem_1_nat_odd_121 by lia.
    destruct (Nat.odd (Z.to_nat a)); cbn; lia.
  - inversion Hall as [| ? ? Ha Hall']; subst.
    inversion Hall' as [| ? ? Hb Hxs]; subst.
    rewrite zrem_1_nat_odd_121 by lia.
    rewrite IH by exact Hxs.
    destruct (Nat.odd (Z.to_nat a)); cbn.
    + rewrite Nat2Z.inj_add.
      replace (Z.of_nat (Z.to_nat a)) with a by lia.
      lia.
    + reflexivity.
Qed.

Lemma pair_sum_z_nonneg_121 : forall lst,
  Forall (fun x => 0 <= x) lst ->
  0 <= pair_sum_z_121 lst.
Proof.
  intros lst Hall.
  rewrite pair_sum_z_nat_121 by exact Hall.
  lia.
Qed.

Lemma problem_121_spec_z_of_pair_sum : forall lst out,
  Forall (fun x => 0 <= x) lst ->
  out = pair_sum_z_121 lst ->
  problem_121_spec_z lst out.
Proof.
  intros lst out Hall ->.
  unfold problem_121_spec_z.
  rewrite pair_sum_z_nat_121 by exact Hall.
  rewrite Nat2Z.id.
  apply pair_sum_nat_problem_spec_121.
Qed.

Lemma fold_left_Zadd_acc_121 : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [| x xs IH]; intros acc.
  - cbn. lia.
  - cbn. rewrite IH. rewrite (IH x). lia.
Qed.

Lemma even_pos_indices_121_snoc : forall i,
  0 <= i ->
  even_pos_indices_121 (i + 1) = even_pos_indices_121 i ++ [i].
Proof.
  intros i Hi.
  unfold even_pos_indices_121.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite seq_S.
  rewrite map_app.
  cbn.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma sum_prefix_121_0 : forall lst,
  sum_prefix_121 0 lst = 0.
Proof.
  intros lst. reflexivity.
Qed.

Lemma sum_prefix_121_step : forall lst i,
  0 <= i ->
  sum_prefix_121 (i + 1) lst =
    sum_prefix_121 i lst + add_term_121 lst i.
Proof.
  intros lst i Hi.
  unfold sum_prefix_121.
  rewrite even_pos_indices_121_snoc by lia.
  rewrite map_app.
  rewrite fold_left_app.
  cbn [map fold_left].
  rewrite fold_left_Zadd_acc_121.
  lia.
Qed.

Lemma sum_prefix_121_step_take : forall lst i,
  0 <= i ->
  Z.rem (Znth (2 * i) lst 0) 2 = 1 ->
  sum_prefix_121 (i + 1) lst =
    sum_prefix_121 i lst + Znth (2 * i) lst 0.
Proof.
  intros lst i Hi Hrem.
  rewrite sum_prefix_121_step by lia.
  unfold add_term_121.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma sum_prefix_121_step_skip : forall lst i,
  0 <= i ->
  Z.rem (Znth (2 * i) lst 0) 2 <> 1 ->
  sum_prefix_121 (i + 1) lst =
    sum_prefix_121 i lst.
Proof.
  intros lst i Hi Hrem.
  rewrite sum_prefix_121_step by lia.
  unfold add_term_121.
  destruct (Z.eqb (Z.rem (Znth (2 * i) lst 0) 2) 1) eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - lia.
Qed.

Lemma sum_prefix_121_range : forall lst i,
  sum_121_int_range lst ->
  0 <= i ->
  2 * i < Zlength lst ->
  0 <= sum_prefix_121 i lst <= INT_MAX /\
  0 <= sum_prefix_121 i lst + Znth (2 * i) lst 0 <= INT_MAX /\
  0 <= sum_prefix_121 (i + 1) lst <= INT_MAX.
Proof.
  intros lst i [_ Hrange] Hi Hbound.
  apply Hrange; lia.
Qed.

Lemma add_term_121_cons2 : forall a b xs k,
  0 <= k ->
  add_term_121 (a :: b :: xs) (k + 1) = add_term_121 xs k.
Proof.
  intros a b xs k Hk.
  unfold add_term_121.
  replace (2 * (k + 1)) with (2 * k + 2) by lia.
  rewrite Znth_cons by lia.
  rewrite Znth_cons by lia.
  replace (2 * k + 2 - 1 - 1) with (2 * k) by lia.
  reflexivity.
Qed.

Lemma sum_prefix_121_cons2 : forall a b xs i,
  0 <= i ->
  sum_prefix_121 (i + 1) (a :: b :: xs) =
    (if Z.eqb (Z.rem a 2) 1 then a else 0) + sum_prefix_121 i xs.
Proof.
  intros a b xs i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  induction (Z.to_nat i) as [| n IH].
  - change (Z.of_nat 0) with 0.
    rewrite sum_prefix_121_step by lia.
    repeat rewrite sum_prefix_121_0.
    unfold add_term_121.
    rewrite Znth0_cons.
    change (pair_sum_z_121 [a]) with (if Z.eqb (Z.rem a 2) 1 then a else 0).
    destruct (Z.eqb (Z.rem a 2) 1); ring.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    replace (Z.of_nat n + 1 + 1) with ((Z.of_nat n + 1) + 1) by lia.
    rewrite sum_prefix_121_step by lia.
    rewrite IH.
    rewrite add_term_121_cons2 by lia.
    rewrite sum_prefix_121_step by lia.
    lia.
Qed.

Lemma sum_prefix_121_exit_pair_sum : forall lst i,
  0 <= i ->
  2 * i >= Zlength lst ->
  2 * i <= Zlength lst + 1 ->
  sum_prefix_121 i lst = pair_sum_z_121 lst.
Proof.
  fix IH 1.
  intros [| a [| b xs]] i Hi Hge Hle.
  - rewrite Zlength_nil in Hge, Hle.
    assert (i = 0) by lia. subst.
    reflexivity.
  - rewrite !Zlength_cons in Hge, Hle.
    rewrite Zlength_nil in Hge, Hle.
    assert (i = 1) by lia. subst.
    replace 1 with (0 + 1) by lia.
    rewrite sum_prefix_121_step by lia.
    repeat rewrite sum_prefix_121_0.
    unfold add_term_121.
    rewrite Znth0_cons.
    change (pair_sum_z_121 [a]) with (if Z.eqb (Z.rem a 2) 1 then a else 0).
    destruct (Z.eqb (Z.rem a 2) 1); ring.
  - rewrite !Zlength_cons in Hge, Hle.
    pose proof (Zlength_nonneg xs).
    assert (Hi1 : 0 <= i - 1) by lia.
    replace i with ((i - 1) + 1) by lia.
    rewrite sum_prefix_121_cons2 by lia.
    rewrite (IH xs (i - 1)) by lia.
    reflexivity.
Qed.

Lemma problem_121_spec_z_of_prefix_exit : forall lst i out,
  Forall (fun x => 0 <= x) lst ->
  0 <= i ->
  2 * i >= Zlength lst ->
  2 * i <= Zlength lst + 1 ->
  out = sum_prefix_121 i lst ->
  problem_121_spec_z lst out.
Proof.
  intros lst i out Hall Hi Hge Hle Hout.
  apply problem_121_spec_z_of_pair_sum; [exact Hall |].
  rewrite <- sum_prefix_121_exit_pair_sum with (i := i) by lia.
  exact Hout.
Qed.
