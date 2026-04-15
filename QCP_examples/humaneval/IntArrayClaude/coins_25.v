Load "../spec/25".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.
Import ListNotations.

Definition list_Z_to_nat (l : list Z) : list nat :=
  map Z.to_nat l.

Definition problem_25_pre_z (n : Z) : Prop :=
  problem_25_pre (Z.to_nat n).

Definition problem_25_spec_z (n : Z) (output : list Z) : Prop :=
  problem_25_spec (Z.to_nat n) (list_Z_to_nat output).

Fixpoint zprod (l : list Z) : Z :=
  match l with
  | nil => 1
  | x :: xs => x * zprod xs
  end.

Definition zprime (n : Z) : Prop :=
  IsPrime (Z.to_nat n).

Definition no_small_factor (n i : Z) : Prop :=
  forall d, 2 <= d < i -> Z.rem n d <> 0.

Definition factorize_loop_state
  (n0 n i : Z) (factors : list Z) : Prop :=
  2 <= n <= n0 /\
  2 <= i <= n0 /\
  Zlength factors + n <= n0 /\
  Forall (fun x => 2 <= x <= n0) factors /\
  zprod factors * n = n0 /\
  Sorted Z.le factors /\
  Forall zprime factors /\
  Forall (fun x => x <= i) factors /\
  Forall (fun x => x <= n) factors /\
  no_small_factor n i.

Lemma zprod_app : forall l1 l2,
  zprod (l1 ++ l2) = zprod l1 * zprod l2.
Proof.
  induction l1 as [|x xs IH]; intros l2; simpl.
  - destruct (zprod l2); reflexivity.
  - rewrite IH. ring.
Qed.

Lemma zprod_nonneg : forall l,
  Forall (fun x => 0 <= x) l ->
  0 <= zprod l.
Proof.
  induction l as [|x xs IH]; intros Hrange; simpl.
  - lia.
  - inversion Hrange; subst.
    match goal with
    | Htail : Forall _ xs |- _ => pose proof (IH Htail)
    end.
    nia.
Qed.

Lemma fold_nat_mul_map_zprod : forall l,
  Forall (fun x => 0 <= x) l ->
  fold_right Nat.mul 1%nat (list_Z_to_nat l) = Z.to_nat (zprod l).
Proof.
  induction l as [|x xs IH]; intros Hrange; simpl.
  - reflexivity.
  - inversion Hrange; subst.
    rewrite IH by assumption.
    rewrite Z2Nat.inj_mul by (try lia; apply zprod_nonneg; assumption).
    reflexivity.
Qed.

Lemma hdrel_z_to_nat : forall x l,
  0 <= x ->
  Forall (fun y => 0 <= y) l ->
  HdRel Z.le x l ->
  HdRel le (Z.to_nat x) (list_Z_to_nat l).
Proof.
  intros x l Hx Hrange Hrel.
  induction Hrel; simpl.
  - constructor.
  - inversion Hrange; subst.
    constructor.
    apply Z2Nat.inj_le; lia.
Qed.

Lemma sorted_z_to_nat : forall l,
  Forall (fun x => 0 <= x) l ->
  Sorted Z.le l ->
  Sorted le (list_Z_to_nat l).
Proof.
  induction l as [|x xs IH]; intros Hrange Hsorted; simpl.
  - constructor.
  - inversion Hrange; subst.
    inversion Hsorted; subst.
    constructor.
    + apply IH; assumption.
    + apply hdrel_z_to_nat; assumption.
Qed.

Lemma sorted_append_last : forall l x,
  Sorted Z.le l ->
  Forall (fun y => y <= x) l ->
  Sorted Z.le (l ++ [x]).
Proof.
  induction l as [|a xs IH]; intros x Hsorted Hle; simpl.
  - constructor; constructor.
  - pose proof (Sorted_inv Hsorted) as [Hsorted_tail Hhd].
    inversion Hle; subst.
    constructor.
    + apply IH; assumption.
    + destruct xs as [|b ys].
      * constructor.
        match goal with
        | H : a <= x |- _ => exact H
        end.
      * inversion Hhd; subst.
        constructor. assumption.
Qed.

Lemma Forall_zprime_map : forall l,
  Forall (fun z => IsPrime (Z.to_nat z)) l ->
  Forall IsPrime (list_Z_to_nat l).
Proof.
  induction l as [|x xs IH]; intros Hprime; simpl.
  - constructor.
  - inversion Hprime; subst.
    constructor; [assumption | apply IH; assumption].
Qed.

Lemma problem_25_spec_z_of_state_exit : forall n0 n factors,
  2 <= n <= n0 ->
  zprod factors * n = n0 ->
  Sorted Z.le factors ->
  Forall zprime factors ->
  Forall (fun x => 2 <= x <= n0) factors ->
  Forall (fun x => x <= n) factors ->
  zprime n ->
  problem_25_spec_z n0 (factors ++ [n]).
Proof.
  intros n0 n factors Hn Hprod Hsorted Hprime Hrange Hle_n Hnprime.
  unfold problem_25_spec_z, problem_25_spec.
  unfold zprime in Hprime, Hnprime.
  assert (Hnonneg_factors: Forall (fun x => 0 <= x) factors).
  { apply Forall_forall. intros x HIn.
    pose proof (proj1 (Forall_forall _ _) Hrange x HIn) as Hx.
    destruct Hx as [Hx _].
    exact (Z.le_trans 0 2 x ltac:(lia) Hx). }
  repeat split.
  - apply sorted_z_to_nat.
    + apply (proj2 (Forall_app _ _ _)); split.
      * exact Hnonneg_factors.
      * constructor; [lia | constructor].
    + apply sorted_append_last; assumption.
  - rewrite fold_nat_mul_map_zprod.
    + rewrite zprod_app. simpl.
      rewrite Z.mul_1_r.
      rewrite Hprod.
      reflexivity.
    + apply (proj2 (Forall_app _ _ _)); split.
      * exact Hnonneg_factors.
      * constructor; [lia | constructor].
  - unfold list_Z_to_nat.
    rewrite map_app.
    apply (proj2 (Forall_app _ _ _)); split; [apply Forall_zprime_map; exact Hprime |].
    constructor; [exact Hnprime | constructor].
Qed.

Lemma divisor_prime_from_no_small : forall n i,
  2 <= i ->
  Z.rem n i = 0 ->
  no_small_factor n i ->
  zprime i.
Proof.
  intros n i Hi Hdiv Hsmall.
  unfold zprime, IsPrime.
  split.
  - change (Z.to_nat 1 < Z.to_nat i)%nat.
    apply Z2Nat.inj_lt; lia.
  - intros d Hdmod.
    destruct d as [|d'].
    + simpl in Hdmod.
      assert (0 < Z.to_nat i)%nat.
      { change (Z.to_nat 0 < Z.to_nat i)%nat.
        apply Z2Nat.inj_lt; lia. }
      lia.
    + destruct d' as [|d''].
      * left; reflexivity.
      * set (dz := Z.of_nat (S (S d''))).
        assert (Hdz_ge : 2 <= dz) by lia.
        destruct (lt_eq_lt_dec (S (S d'')) (Z.to_nat i)) as [[Hd_lt | Hd_eq] | Hd_gt].
        -- exfalso.
           assert (Hdiv_i : exists c, Z.to_nat i = ((S (S d'')) * c)%nat).
           { apply (proj1 (Nat.Div0.mod_divides _ _)); exact Hdmod. }
           destruct Hdiv_i as [c Hc].
           assert (Hi_eq : i = dz * Z.of_nat c).
           { pose proof (f_equal Z.of_nat Hc) as Hz.
             rewrite Nat2Z.inj_mul in Hz.
             rewrite Z2Nat.id in Hz by lia.
             exact Hz. }
           assert (Hdz_lt_i : dz < i).
           { apply Z2Nat.inj_lt; lia. }
           apply (Hsmall dz ltac:(lia)).
           apply (proj2 (Z.rem_divide n dz ltac:(lia))).
           apply (proj1 (Z.rem_divide n i ltac:(lia))) in Hdiv.
           destruct Hdiv as [q Hn].
           exists (Z.of_nat c * q).
           rewrite Hn, Hi_eq.
           ring.
        -- right.
           exact Hd_eq.
        -- exfalso.
           rewrite Nat.mod_small in Hdmod by lia.
           assert (0 < Z.to_nat i)%nat.
           { change (Z.to_nat 0 < Z.to_nat i)%nat.
             apply Z2Nat.inj_lt; lia. }
           lia.
Qed.

Lemma no_small_factor_after_div : forall n i,
  2 <= i ->
  Z.rem n i = 0 ->
  no_small_factor n i ->
  no_small_factor (n ÷ i) i.
Proof.
  intros n i Hi Hdiv Hsmall d Hd.
  intro Hrem.
  apply (Hsmall d Hd).
  apply (proj2 (Z.rem_divide n d ltac:(lia))).
  apply (proj1 (Z.rem_divide (n ÷ i) d ltac:(lia))) in Hrem.
  destruct Hrem as [q Hq].
  assert (Hn : n = i * (n ÷ i)).
  { apply Z.quot_exact; lia. }
  exists (i * q).
  rewrite Hn, Hq.
  ring.
Qed.

Lemma no_small_factor_after_skip : forall n i,
  2 <= i ->
  Z.rem n i <> 0 ->
  no_small_factor n i ->
  no_small_factor n (i + 1).
Proof.
  intros n i Hi Hnot Hsmall d Hd.
  assert (d < i \/ d = i) by lia.
  destruct H as [Hd_lt | ->].
  - apply Hsmall; lia.
  - exact Hnot.
Qed.

Lemma Forall_app_intro_local : forall {A} (P : A -> Prop) l1 l2,
  Forall P l1 ->
  Forall P l2 ->
  Forall P (l1 ++ l2).
Proof.
  intros A P l1 l2 H1 H2.
  induction H1; simpl; auto using Forall.
Qed.

Lemma Forall_le_bound_trans : forall l a b,
  a <= b ->
  Forall (fun x : Z => x <= a) l ->
  Forall (fun x : Z => x <= b) l.
Proof.
  intros l a b Hab H.
  induction H; constructor; auto.
  lia.
Qed.

Lemma final_prime_from_no_small_exit : forall n i,
  2 <= n ->
  2 <= i ->
  i > n ÷ i ->
  no_small_factor n i ->
  zprime n.
Proof.
  intros n i Hn Hi Hexit Hsmall.
  unfold zprime, IsPrime.
  assert (Hn_lt_square : n < i * i).
  { pose proof (Z.mul_succ_quot_gt n i ltac:(lia) ltac:(lia)) as Hlt.
    assert (Z.succ (n ÷ i) <= i) by lia.
    nia. }
  split.
  - change (Z.to_nat 1 < Z.to_nat n)%nat.
    apply Z2Nat.inj_lt; lia.
  - intros d Hdmod.
    destruct d as [|d'].
    + simpl in Hdmod.
      assert (0 < Z.to_nat n)%nat.
      { change (Z.to_nat 0 < Z.to_nat n)%nat.
        apply Z2Nat.inj_lt; lia. }
      lia.
    + destruct d' as [|d''].
      * left; reflexivity.
      * set (dz := Z.of_nat (S (S d''))).
        assert (Hdz_ge : 2 <= dz) by lia.
        destruct (lt_eq_lt_dec (S (S d'')) (Z.to_nat n)) as [[Hd_lt | Hd_eq] | Hd_gt].
        -- assert (Hdiv_n : exists c, Z.to_nat n = ((S (S d'')) * c)%nat).
           { apply (proj1 (Nat.Div0.mod_divides _ _)); exact Hdmod. }
           destruct Hdiv_n as [c Hc].
           assert (Hc_pos : (0 < c)%nat).
           { destruct c; simpl in Hc; lia. }
           assert (Hc_ge_2_or_d_small : dz < i \/ Z.of_nat c < i).
           {
             assert (Hn_eq : n = dz * Z.of_nat c).
             { pose proof (f_equal Z.of_nat Hc) as Hz.
               rewrite Nat2Z.inj_mul in Hz.
               rewrite Z2Nat.id in Hz by lia.
               exact Hz. }
             destruct c as [|c']; [lia|].
             destruct c' as [|c''].
             { right; simpl; lia. }
             assert (2 <= Z.of_nat (S (S c''))) by lia.
             assert (Hsmall_factor : dz < i \/ Z.of_nat (S (S c'')) < i) by nia.
             destruct Hsmall_factor as [Hleft | Hright]; [left | right]; assumption.
           }
           destruct Hc_ge_2_or_d_small as [Hd_small | Hc_small].
           ++ exfalso.
              apply (Hsmall dz ltac:(lia)).
              apply (proj2 (Z.rem_divide n dz ltac:(lia))).
              exists (Z.of_nat c).
              pose proof (f_equal Z.of_nat Hc) as Hz.
              rewrite Nat2Z.inj_mul in Hz.
              rewrite Z2Nat.id in Hz by lia.
              subst dz.
              rewrite Hz.
              ring.
           ++ exfalso.
              assert (Hc_ge2 : 2 <= Z.of_nat c).
              { destruct c as [|c']; [lia|].
                destruct c' as [|c'']; simpl in Hc; lia. }
              apply (Hsmall (Z.of_nat c) ltac:(lia)).
              apply (proj2 (Z.rem_divide n (Z.of_nat c) ltac:(lia))).
              exists dz.
              pose proof (f_equal Z.of_nat Hc) as Hz.
              rewrite Nat2Z.inj_mul in Hz.
              rewrite Z2Nat.id in Hz by lia.
              subst dz.
              rewrite Hz.
              ring.
        -- right.
           exact Hd_eq.
        -- exfalso.
           rewrite Nat.mod_small in Hdmod by lia.
           assert (0 < Z.to_nat n)%nat.
           { change (Z.to_nat 0 < Z.to_nat n)%nat.
             apply Z2Nat.inj_lt; lia. }
           lia.
Qed.
