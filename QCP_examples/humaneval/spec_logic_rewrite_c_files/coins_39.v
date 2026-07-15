Load "../spec/39".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition problem_39_pre_z (n : Z) : Prop :=
  problem_39_pre (Z.to_nat n).

Definition problem_39_spec_z (n output : Z) : Prop :=
  0 <= output /\ problem_39_spec (Z.to_nat n) (Z.to_nat output).

Definition prime_fib_safe_z (n : Z) : Prop :=
  1 <= n <= 5.

Definition finite_prime_candidate_z (f : Z) : Prop :=
  f = 2 \/ f = 3 \/ f = 5 \/ f = 13 \/ f = 89.

Definition finite_nonprime_candidate_z (f : Z) : Prop :=
  f = 8 \/ f = 21 \/ f = 34 \/ f = 55.

Definition pf_loop_state_z (count f1 f2 : Z) : Prop :=
  (count = 0 /\ f1 = 1 /\ f2 = 2) \/
  (count = 1 /\ f1 = 2 /\ f2 = 3) \/
  (count = 2 /\ f1 = 3 /\ f2 = 5) \/
  (count = 3 /\ f1 = 5 /\ f2 = 8) \/
  (count = 3 /\ f1 = 8 /\ f2 = 13) \/
  (count = 4 /\ f1 = 13 /\ f2 = 21) \/
  (count = 4 /\ f1 = 21 /\ f2 = 34) \/
  (count = 4 /\ f1 = 34 /\ f2 = 55) \/
  (count = 4 /\ f1 = 55 /\ f2 = 89) \/
  (count = 5 /\ f1 = 89 /\ f2 = 144).

Definition pf_after_advance_z (count f1 f2 : Z) : Prop :=
  (count = 0 /\ f1 = 2 /\ f2 = 3) \/
  (count = 1 /\ f1 = 3 /\ f2 = 5) \/
  (count = 2 /\ f1 = 5 /\ f2 = 8) \/
  (count = 3 /\ f1 = 8 /\ f2 = 13) \/
  (count = 3 /\ f1 = 13 /\ f2 = 21) \/
  (count = 4 /\ f1 = 21 /\ f2 = 34) \/
  (count = 4 /\ f1 = 34 /\ f2 = 55) \/
  (count = 4 /\ f1 = 55 /\ f2 = 89) \/
  (count = 4 /\ f1 = 89 /\ f2 = 144).

Definition no_divisor_before_z (f w : Z) : Prop :=
  forall k, 2 <= k < w -> Z.rem f k <> 0.

Definition found_divisor_before_z (f w : Z) : Prop :=
  exists k, 2 <= k <= w /\ k <= f / k /\ Z.rem f k = 0.

Definition prime_scan_state_z (f w isprime : Z) : Prop :=
  2 <= w /\
  (isprime <> 0 -> no_divisor_before_z f w) /\
  (isprime = 0 -> found_divisor_before_z f w).

Ltac split_pf_cases :=
  unfold pf_loop_state_z, pf_after_advance_z,
    finite_prime_candidate_z, finite_nonprime_candidate_z in *;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H|H]
  | H : _ /\ _ |- _ => destruct H as [? ?]
  end; subst; simpl in *; try lia; eauto 12.

Ltac destruct_pf_after H :=
  unfold pf_after_advance_z in H;
  repeat match type of H with
  | _ \/ _ => destruct H as [H|H]
  | _ /\ _ => destruct H as [? H]
  end; subst; simpl in *; try lia.

Lemma pf_initial_state :
  pf_loop_state_z 0 1 2.
Proof. unfold pf_loop_state_z; eauto 12. Qed.

Lemma pf_advance_from_loop : forall count f1 f2,
  pf_loop_state_z count f1 f2 ->
  count < 5 ->
  pf_after_advance_z count f2 (f1 + f2).
Proof.
  intros. split_pf_cases.
Qed.

Lemma pf_after_advance_bounds : forall count f1 f2,
  pf_after_advance_z count f1 f2 ->
  2 <= f1 <= 89 /\ f2 <= 144.
Proof.
  intros. split_pf_cases.
Qed.

Lemma pf_loop_sum_safe : forall count f1 f2,
  pf_loop_state_z count f1 f2 ->
  count < 5 ->
  INT_MIN <= f1 + f2 <= INT_MAX.
Proof.
  intros. split_pf_cases.
Qed.

Lemma w_range_2_10 : forall w,
  2 <= w ->
  w <= 10 ->
  w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/
  w = 7 \/ w = 8 \/ w = 9 \/ w = 10.
Proof.
  intros; lia.
Qed.

Ltac destruct_zrange H :=
  repeat match type of H with
  | _ \/ _ => destruct H as [H|H]; [subst|]
  | _ = _ => subst
  end.

Ltac close_nonprime_scan Hno :=
  first
    [ apply (Hno 2); [lia|vm_compute; reflexivity]
    | apply (Hno 3); [lia|vm_compute; reflexivity]
    | apply (Hno 5); [lia|vm_compute; reflexivity] ].

Lemma pf_prime_step : forall count f1 f2,
  pf_after_advance_z count f1 f2 ->
  finite_prime_candidate_z f1 ->
  pf_loop_state_z (count + 1) f1 f2.
Proof.
  intros. split_pf_cases.
Qed.

Lemma pf_nonprime_step : forall count f1 f2,
  pf_after_advance_z count f1 f2 ->
  ~ finite_prime_candidate_z f1 ->
  pf_loop_state_z count f1 f2.
Proof.
  intros. split_pf_cases.
Qed.

Lemma pf_scan_start : forall f,
  2 <= f <= 89 ->
  prime_scan_state_z f 2 1.
Proof.
  intros.
  unfold prime_scan_state_z, no_divisor_before_z, found_divisor_before_z.
  repeat split; try lia.
Qed.

Lemma pf_scan_found : forall f w,
  prime_scan_state_z f w 1 ->
  w <= f / w ->
  Z.rem f w = 0 ->
  prime_scan_state_z f w 0.
Proof.
  intros f w Hscan Hcond Hrem.
  unfold prime_scan_state_z, found_divisor_before_z in *.
  destruct Hscan as [Hw [_ _]].
  repeat split; try lia.
  intros _. exists w. repeat split; lia.
Qed.

Lemma pf_scan_next : forall f w,
  prime_scan_state_z f w 1 ->
  Z.rem f w <> 0 ->
  w <= f / w ->
  pf_after_advance_z 0 f 3 \/
  pf_after_advance_z 1 f 5 \/
  pf_after_advance_z 2 f 8 \/
  pf_after_advance_z 3 f 13 \/
  pf_after_advance_z 4 f 21 \/
  pf_after_advance_z 4 f 34 \/
  pf_after_advance_z 4 f 55 \/
  pf_after_advance_z 4 f 89 \/
  pf_after_advance_z 4 f 144 ->
  prime_scan_state_z f (w + 1) 1.
Proof.
  intros f w Hscan Hrem Hcond Hcand.
  unfold prime_scan_state_z, no_divisor_before_z in *.
  destruct Hscan as [Hw [Hno Hfound]].
  split; [lia|].
  split.
  - intros _ k Hk.
    assert (k < w \/ k = w) as Hor by lia.
    destruct Hor as [Hlt|Heq].
    + apply Hno; lia.
    + subst k. exact Hrem.
  - intros Hz. lia.
Qed.

Lemma pf_scan_next_prime : forall count f1 f2 w,
  pf_after_advance_z count f1 f2 ->
  prime_scan_state_z f1 w 1 ->
  Z.rem f1 w <> 0 ->
  w <= f1 / w ->
  prime_scan_state_z f1 (w + 1) 1.
Proof.
  intros count f1 f2 w Hadv Hscan Hrem Hcond.
  unfold prime_scan_state_z, no_divisor_before_z in *.
  destruct Hscan as [Hw [Hno Hfound]].
  split; [lia|].
  split.
  - intros _ k Hk.
    assert (k < w \/ k = w) as Hor by lia.
    destruct Hor as [Hlt|Heq].
    + apply Hno; lia.
    + subst k. exact Hrem.
  - intros Hz. lia.
Qed.

Lemma pf_scan_next_found : forall f w,
  prime_scan_state_z f w 0 ->
  prime_scan_state_z f (w + 1) 0.
Proof.
  intros f w Hscan.
  unfold prime_scan_state_z, found_divisor_before_z in *.
  destruct Hscan as [Hw [Hno Hfound]].
  split; [lia|].
  split; [intros Hz; lia|].
  intros _. destruct (Hfound eq_refl) as [k [Hkr [Hkdiv Hrem]]].
  exists k. repeat split; try lia; assumption.
Qed.

Lemma pf_not_prime_scan_false : forall count f1 f2,
  pf_after_advance_z count f1 f2 ->
  finite_nonprime_candidate_z f1 ->
  ~ finite_prime_candidate_z f1.
Proof.
  intros. split_pf_cases.
Qed.

Lemma pf_divisor_not_finite : forall count f1 f2 w,
  pf_after_advance_z count f1 f2 ->
  2 <= w ->
  w <= 10 ->
  w <= f1 / w ->
  Z.rem f1 w = 0 ->
  ~ finite_prime_candidate_z f1.
Proof.
  intros count f1 f2 w Hadv Hwlo Hwhi Hcond Hrem Hprime.
  unfold finite_prime_candidate_z in Hprime.
  destruct Hprime as [Hf|[Hf|[Hf|[Hf|Hf]]]]; subst f1;
    pose proof (w_range_2_10 w Hwlo Hwhi) as Hwcase;
    destruct_zrange Hwcase;
    vm_compute in Hcond; vm_compute in Hrem;
    try discriminate; try (exfalso; apply Hcond; reflexivity); lia.
Qed.

Lemma pf_found_not_finite : forall count f1 f2 w,
  pf_after_advance_z count f1 f2 ->
  w <= 10 ->
  found_divisor_before_z f1 w ->
  ~ finite_prime_candidate_z f1.
Proof.
  intros count f1 f2 w Hadv Hwhi Hfound.
  unfold found_divisor_before_z in Hfound.
  destruct Hfound as [k [Hkr [Hkdiv Hrem]]].
  eapply pf_divisor_not_finite with (count := count) (f1 := f1) (f2 := f2) (w := k);
    eauto; lia.
Qed.

Lemma pf_scan_exit_prime : forall count f1 f2 w,
  pf_after_advance_z count f1 f2 ->
  2 <= w ->
  w <= 10 ->
  prime_scan_state_z f1 w 1 ->
  (w >= 10 \/ w > f1 / w) ->
  finite_prime_candidate_z f1.
Proof.
  intros count f1 f2 w Hadv Hwlo Hwhi Hscan Hexit.
  unfold prime_scan_state_z, no_divisor_before_z in Hscan.
  destruct Hscan as [_ [Hno _]].
  specialize (Hno ltac:(lia)).
  destruct_pf_after Hadv; try solve
    [left; reflexivity
    |right; left; reflexivity
    |right; right; left; reflexivity
    |right; right; right; left; reflexivity
    |right; right; right; right; reflexivity].
  all: pose proof (w_range_2_10 w Hwlo Hwhi) as Hwcase;
    destruct_zrange Hwcase;
    destruct Hexit as [Hge|Hgt];
    try lia;
    try (vm_compute in Hgt; discriminate);
    exfalso; close_nonprime_scan Hno.
Qed.

Lemma pf_return_value : forall n f1 f2,
  1 <= n <= 5 ->
  pf_loop_state_z n f1 f2 ->
  finite_prime_candidate_z f1 ->
  (n = 1 /\ f1 = 2) \/
  (n = 2 /\ f1 = 3) \/
  (n = 3 /\ f1 = 5) \/
  (n = 4 /\ f1 = 13) \/
  (n = 5 /\ f1 = 89).
Proof.
  intros. split_pf_cases.
Qed.

Lemma is_prime_2 : IsPrime 2.
Proof.
  unfold IsPrime. split; [lia|].
  intros d H.
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  rewrite Nat.mod_small in H by lia. lia.
Qed.

Lemma is_prime_3 : IsPrime 3.
Proof.
  unfold IsPrime. split; [lia|].
  intros d H.
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  rewrite Nat.mod_small in H by lia. lia.
Qed.

Lemma is_prime_5 : IsPrime 5.
Proof.
  unfold IsPrime. split; [lia|].
  intros d H.
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  destruct d as [|d]; [simpl in H; lia|].
  rewrite Nat.mod_small in H by lia. lia.
Qed.

Lemma is_prime_13 : IsPrime 13.
Proof.
  unfold IsPrime. split; [lia|].
  intros d H.
  do 14 (destruct d as [|d]; [simpl in H; lia|]).
  rewrite Nat.mod_small in H by lia. lia.
Qed.

Lemma is_prime_89 : IsPrime 89.
Proof.
  unfold IsPrime. split; [lia|].
  intros d Hmod.
  destruct d as [|d0].
  { simpl in Hmod; lia. }
  destruct (Nat.eq_dec (S d0) 1%nat) as [Hd1|Hd1].
  { left; exact Hd1. }
  destruct (Nat.eq_dec (S d0) 89%nat) as [Hd89|Hd89].
  { right; exact Hd89. }
  exfalso.
  apply Nat.mod_divide in Hmod; [|lia].
  destruct Hmod as [k Hk].
  assert (Hd_ge : (2 <= S d0)%nat) by lia.
  destruct k as [|[|k0]].
  - nia.
  - assert (S d0 = 89%nat) by nia. contradiction.
  - assert (Hsmall : (S d0 <= 9 \/ S (S k0) <= 9)%nat) by nia.
    destruct Hsmall as [Hdsmall|Hksmall].
    + do 9 (destruct d0 as [|d0]; try nia).
    + do 8 (destruct k0 as [|k0]; try nia).
Qed.

Lemma fib_2 : IsFib 2.
Proof. exists 3%nat. vm_compute. reflexivity. Qed.

Lemma fib_3 : IsFib 3.
Proof. exists 4%nat. vm_compute. reflexivity. Qed.

Lemma fib_5 : IsFib 5.
Proof. exists 5%nat. vm_compute. reflexivity. Qed.

Lemma fib_13 : IsFib 13.
Proof. exists 7%nat. vm_compute. reflexivity. Qed.

Lemma fib_89 : IsFib 89.
Proof. exists 11%nat. vm_compute. reflexivity. Qed.

Lemma is_prime_fib_2 : IsPrimeFib 2.
Proof. split; [apply is_prime_2|apply fib_2]. Qed.

Lemma is_prime_fib_3 : IsPrimeFib 3.
Proof. split; [apply is_prime_3|apply fib_3]. Qed.

Lemma is_prime_fib_5 : IsPrimeFib 5.
Proof. split; [apply is_prime_5|apply fib_5]. Qed.

Lemma is_prime_fib_13 : IsPrimeFib 13.
Proof. split; [apply is_prime_13|apply fib_13]. Qed.

Lemma is_prime_fib_89 : IsPrimeFib 89.
Proof. split; [apply is_prime_89|apply fib_89]. Qed.

Definition fib_pair_nat (n : nat) : nat * nat :=
  Nat.iter n (fun p : nat * nat => (snd p, (fst p + snd p)%nat)) (0%nat, 1%nat).

Lemma fib_pair_order : forall n,
  let p := fib_pair_nat n in
  (fst p <= snd p)%nat.
Proof.
  induction n; simpl; [lia|].
  unfold fib_pair_nat in *.
  remember (Nat.iter n (fun p : nat * nat => (snd p, (fst p + snd p)%nat)) (0%nat, 1%nat))
    as p eqn:Hp.
  destruct p as [a b]. simpl in *. lia.
Qed.

Lemma fib_step : forall n,
  fib (S n) = snd (fib_pair_nat n).
Proof.
  intros n. unfold fib, fib_pair_nat. simpl. reflexivity.
Qed.

Lemma fib_monotone_step : forall n, (fib n <= fib (S n))%nat.
Proof.
  intros n.
  unfold fib at 1.
  rewrite fib_step.
  pose proof (fib_pair_order n).
  simpl in H. exact H.
Qed.

Lemma fib_monotone : forall i j,
  (i <= j)%nat -> (fib i <= fib j)%nat.
Proof.
  intros i j Hle.
  induction Hle; [lia|].
  pose proof (fib_monotone_step m).
  lia.
Qed.

Lemma fib_ge_11 : forall i,
  (11 <= i)%nat -> (89 <= fib i)%nat.
Proof.
  intros i Hi.
  replace 89%nat with (fib 11) by (vm_compute; reflexivity).
  apply fib_monotone. lia.
Qed.

Lemma small_primefib_under_89 : forall y,
  (y < 89)%nat ->
  IsPrimeFib y ->
  y = 2%nat \/ y = 3%nat \/ y = 5%nat \/ y = 13%nat.
Proof.
  intros y Hy [Hp [i Hfib]].
  assert (i < 11)%nat.
  { destruct (le_gt_dec 11 i) as [Hge|Hlt]; [|lia].
    pose proof (fib_ge_11 i Hge).
    lia. }
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; destruct Hp as [Hgt _]; lia|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; destruct Hp as [Hgt _]; lia|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; destruct Hp as [Hgt _]; lia|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; left; reflexivity|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; right; left; reflexivity|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; right; right; left; reflexivity|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib;
    [symmetry in Hfib; subst y;
     destruct Hp as [_ Hdiv]; specialize (Hdiv 2%nat eq_refl); lia
    |fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib; [symmetry in Hfib; subst y; right; right; right; reflexivity|fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib;
    [symmetry in Hfib; subst y;
     destruct Hp as [_ Hdiv]; specialize (Hdiv 3%nat eq_refl); lia
    |fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib;
    [symmetry in Hfib; subst y;
     destruct Hp as [_ Hdiv]; specialize (Hdiv 2%nat eq_refl); lia
    |fold fib in Hfib].
  destruct i as [|i]; unfold fib in Hfib; simpl in Hfib;
    [symmetry in Hfib; subst y;
     destruct Hp as [_ Hdiv]; specialize (Hdiv 5%nat eq_refl); lia
    |fold fib in Hfib].
  lia.
Qed.

Lemma small_primefib_under_13 : forall y,
  (y < 13)%nat ->
  IsPrimeFib y ->
  y = 2%nat \/ y = 3%nat \/ y = 5%nat.
Proof.
  intros y Hy Hpf.
  pose proof (small_primefib_under_89 y ltac:(lia) Hpf) as H.
  intuition lia.
Qed.

Lemma small_primefib_under_5 : forall y,
  (y < 5)%nat ->
  IsPrimeFib y ->
  y = 2%nat \/ y = 3%nat.
Proof.
  intros y Hy Hpf.
  pose proof (small_primefib_under_89 y ltac:(lia) Hpf) as H.
  intuition lia.
Qed.

Lemma small_primefib_under_3 : forall y,
  (y < 3)%nat ->
  IsPrimeFib y ->
  y = 2%nat.
Proof.
  intros y Hy Hpf.
  pose proof (small_primefib_under_89 y ltac:(lia) Hpf) as H.
  intuition lia.
Qed.

Lemma small_primefib_under_2 : forall y,
  (y < 2)%nat ->
  IsPrimeFib y ->
  False.
Proof.
  intros y Hy [Hp _].
  unfold IsPrime in Hp. lia.
Qed.

Lemma problem_39_spec_1 : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split; [apply is_prime_fib_2|].
  exists nil.
  split; [simpl; lia|].
  split; [constructor|].
  intros z. split; intros H.
  - contradiction.
  - destruct H as [Hy Hpf].
    exfalso. eapply small_primefib_under_2; eauto.
Qed.

Lemma problem_39_spec_2 : problem_39_spec 2 3.
Proof.
  unfold problem_39_spec.
  split; [apply is_prime_fib_3|].
  exists [2%nat].
  split; [simpl; lia|].
  split; [repeat constructor; simpl; lia|].
  intros z. split; intros H.
  - destruct H as [<-|[]]. split; [lia|apply is_prime_fib_2].
  - destruct H as [Hy Hpf].
    pose proof (small_primefib_under_3 z Hy Hpf). subst.
    simpl. auto.
Qed.

Lemma problem_39_spec_3 : problem_39_spec 3 5.
Proof.
  unfold problem_39_spec.
  split; [apply is_prime_fib_5|].
  exists [2%nat; 3%nat].
  split; [simpl; lia|].
  split; [repeat constructor; simpl; lia|].
  intros z. split; intros H.
  - destruct H as [<-|[<-|[]]]; split; try lia;
      [apply is_prime_fib_2|apply is_prime_fib_3].
  - destruct H as [Hy Hpf].
    pose proof (small_primefib_under_5 z Hy Hpf) as Hsmall.
    destruct Hsmall as [Hz|Hz]; subst z; simpl; auto.
Qed.

Lemma problem_39_spec_4 : problem_39_spec 4 13.
Proof.
  unfold problem_39_spec.
  split; [apply is_prime_fib_13|].
  exists [2%nat; 3%nat; 5%nat].
  split; [simpl; lia|].
  split; [repeat constructor; simpl; lia|].
  intros z. split; intros H.
  - destruct H as [<-|[<-|[<-|[]]]]; split; try lia;
      [apply is_prime_fib_2|apply is_prime_fib_3|apply is_prime_fib_5].
  - destruct H as [Hy Hpf].
    pose proof (small_primefib_under_13 z Hy Hpf) as Hsmall.
    destruct Hsmall as [Hz|[Hz|Hz]]; subst z; simpl; auto.
Qed.

Lemma problem_39_spec_5 : problem_39_spec 5 89.
Proof.
  unfold problem_39_spec.
  split.
  - apply is_prime_fib_89.
  - exists [2%nat; 3%nat; 5%nat; 13%nat].
    split; [simpl; lia|].
    split; [repeat constructor; simpl; lia|].
    intros z. split; intros H.
    + destruct H as [<-|[<-|[<-|[<-|[]]]]]; split; try lia;
        [apply is_prime_fib_2|apply is_prime_fib_3|apply is_prime_fib_5|apply is_prime_fib_13].
    + destruct H as [Hy Hpf].
      pose proof (small_primefib_under_89 z Hy Hpf) as Hsmall.
      destruct Hsmall as [Hz|[Hz|[Hz|Hz]]]; subst z; simpl; auto.
Qed.

Lemma problem_39_spec_z_from_finite : forall n r,
  1 <= n <= 5 ->
  ((n = 1 /\ r = 2) \/
   (n = 2 /\ r = 3) \/
   (n = 3 /\ r = 5) \/
   (n = 4 /\ r = 13) \/
   (n = 5 /\ r = 89)) ->
  problem_39_spec_z n r.
Proof.
  intros n r Hn Hcase.
  unfold problem_39_spec_z.
  destruct Hcase as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
    split; try lia; cbn [Z.to_nat]; try apply problem_39_spec_1;
    try apply problem_39_spec_2; try apply problem_39_spec_3;
    try apply problem_39_spec_4; try apply problem_39_spec_5.
Qed.

Lemma pf_loop_state_spec : forall n f1 f2,
  1 <= n <= 5 ->
  pf_loop_state_z n f1 f2 ->
  finite_prime_candidate_z f1 ->
  problem_39_spec_z n f1.
Proof.
  intros n f1 f2 Hn Hstate Hprime.
  apply problem_39_spec_z_from_finite; [assumption|].
  apply pf_return_value with (f2 := f2); assumption.
Qed.
