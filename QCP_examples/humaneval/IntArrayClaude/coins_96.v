Load "../spec/96".

Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.

Close Scope nat_scope.
Open Scope Z_scope.

Definition problem_96_pre_z (n : Z) : Prop :=
  problem_96_pre (Z.to_nat n).

Definition problem_96_spec_z (n : Z) (result : list Z) : Prop :=
  problem_96_spec (Z.to_nat n) (map Z.to_nat result).

Definition count_up_to_state (i : Z) (result : list Z) : Prop :=
  2 <= i /\
  Zlength result <= i /\
  (forall p, In p result -> 2 <= p < i /\ prime p) /\
  (forall p, 2 <= p < i -> prime p -> In p result) /\
  Sorted Z.lt result /\
  NoDup result.

Definition prime_test_state (candidate : Z) (result : list Z) (j isp : Z) : Prop :=
  0 <= j <= Zlength result /\
  0 <= isp <= 1 /\
  (isp <> 0 ->
   forall k,
     0 <= k < j ->
     Znth k result 0 <= candidate / Znth k result 0 ->
     candidate mod Znth k result 0 <> 0) /\
  (isp = 0 ->
   exists k,
     0 <= k < j /\
     Znth k result 0 <= candidate / Znth k result 0 /\
     candidate mod Znth k result 0 = 0).

Lemma HdRel_map_Z_to_nat_96 : forall x l,
  0 <= x ->
  (forall y, In y l -> 0 <= y) ->
  HdRel Z.lt x l ->
  HdRel lt (Z.to_nat x) (map Z.to_nat l).
Proof.
  intros x l Hx Hnonneg Hhd.
  induction Hhd.
  - constructor.
  - simpl.
    constructor.
    + apply Z2Nat.inj_lt.
      * exact Hx.
      * apply Hnonneg. left. reflexivity.
      * assumption.
Qed.

Lemma Sorted_map_Z_to_nat_96 : forall l,
  (forall x, In x l -> 0 <= x) ->
  Sorted Z.lt l ->
  Sorted lt (map Z.to_nat l).
Proof.
  intros l Hnonneg Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    constructor.
    + apply IHHsorted.
      intros z Hz.
      apply Hnonneg. right. exact Hz.
    + apply HdRel_map_Z_to_nat_96.
      * apply Hnonneg. left. reflexivity.
      * intros z Hz. apply Hnonneg. right. exact Hz.
      * exact H.
Qed.

Lemma NoDup_map_Z_to_nat_96 : forall l,
  (forall x, In x l -> 0 <= x) ->
  NoDup l ->
  NoDup (map Z.to_nat l).
Proof.
  intros l Hnonneg Hnodup.
  induction Hnodup.
  - constructor.
  - simpl.
    constructor.
    + intro Hin_map.
      apply in_map_iff in Hin_map.
      destruct Hin_map as [z [Hz_eq Hz_in]].
      apply H.
      assert (z = x).
      {
        eapply Z2Nat.inj.
        - apply Hnonneg. right. exact Hz_in.
        - apply Hnonneg. left. reflexivity.
        - exact Hz_eq.
      }
      subst z.
      exact Hz_in.
    + apply IHHnodup.
      intros z Hz.
      apply Hnonneg. right. exact Hz.
Qed.

Lemma count_up_to_state_init :
  count_up_to_state 2 [].
Proof.
  unfold count_up_to_state.
  split; [lia |].
  split.
  - rewrite Zlength_nil. lia.
  - split.
    + intros p Hp. contradiction.
    + split.
      * intros p Hp _. lia.
      * split; constructor.
Qed.

Lemma count_up_to_state_after_two :
  count_up_to_state 3 [2].
Proof.
  unfold count_up_to_state.
  split; [lia |].
  split.
  - simpl. rewrite Zlength_cons, Zlength_nil. lia.
  - split.
    + intros p Hp.
      simpl in Hp.
      destruct Hp as [Hp | []].
      subst p.
      split; [lia | exact prime_2].
    + split.
      * intros p Hp Hprime.
        assert (p = 2) by lia.
        subst p.
        simpl.
        auto.
      * split.
        -- constructor.
           ++ constructor.
           ++ constructor.
        -- constructor.
           ++ simpl. intros Hp. contradiction.
           ++ constructor.
Qed.

Lemma problem_96_spec_z_of_state :
  forall n result,
    count_up_to_state n result ->
    problem_96_spec_z n result.
Proof.
  intros n result Hstate.
  unfold problem_96_spec_z, problem_96_spec.
  destruct Hstate as [Hn [_ [Hprime [Hcomplete [Hsorted Hnodup]]]]].
  assert (Hnonneg : forall z, In z result -> 0 <= z).
  {
    intros z Hz.
    destruct (Hprime z Hz) as [[Hz_ge _] _].
    lia.
  }
  split.
  - intros p Hp.
    apply in_map_iff in Hp.
    destruct Hp as [z [Hp Hz]].
    subst p.
    destruct (Hprime z Hz) as [_ Hzprime].
    rewrite Z2Nat.id by (apply Hnonneg; exact Hz).
    exact Hzprime.
  - split.
    + intros p Hp.
      apply in_map_iff in Hp.
      destruct Hp as [z [Hp Hz]].
      subst p.
      destruct (Hprime z Hz) as [[_ Hz_lt] _].
      apply Nat2Z.inj_lt.
      rewrite !Z2Nat.id; try lia.
      apply Hnonneg; exact Hz.
    + split.
      * intros p Hpprime Hp_lt.
        replace p with (Z.to_nat (Z.of_nat p)) by lia.
        apply in_map.
        apply Hcomplete.
        -- split.
           ++ inversion Hpprime; lia.
           ++ apply Nat2Z.inj_lt in Hp_lt.
              rewrite Z2Nat.id in Hp_lt by lia.
              exact Hp_lt.
        -- exact Hpprime.
      * split.
        -- apply Sorted_map_Z_to_nat_96; assumption.
        -- apply NoDup_map_Z_to_nat_96; assumption.
Qed.

Lemma Znth_In_range_96 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma In_Znth_exists_96 : forall (x : Z) l,
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l 0 = x.
Proof.
  intros x l Hin.
  apply In_nth_error in Hin.
  destruct Hin as [n Hn].
  exists (Z.of_nat n).
  split.
  - assert ((n < length l)%nat) as Hlt.
    { apply nth_error_Some. rewrite Hn. discriminate. }
    rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    apply nth_error_nth with (d := 0) in Hn.
    exact Hn.
Qed.

Lemma count_up_to_state_Znth_prime : forall i result k,
  count_up_to_state i result ->
  0 <= k < Zlength result ->
  2 <= Znth k result 0 < i /\ prime (Znth k result 0).
Proof.
  intros i result k Hstate Hk.
  unfold count_up_to_state in Hstate.
  destruct Hstate as [_ [_ [Hall _]]].
  apply Hall.
  apply Znth_In_range_96.
  exact Hk.
Qed.

Lemma prime_test_state_init : forall candidate result,
  0 <= Zlength result ->
  prime_test_state candidate result 0 1.
Proof.
  intros candidate result Hlen.
  unfold prime_test_state.
  repeat split; intros; lia.
Qed.

Lemma prime_test_state_step_zero : forall candidate result j isp,
  count_up_to_state candidate result ->
  prime_test_state candidate result j isp ->
  0 <= j < Zlength result ->
  Znth j result 0 <= candidate / Znth j result 0 ->
  candidate mod Znth j result 0 = 0 ->
  prime_test_state candidate result (j + 1) 0.
Proof.
  intros candidate result j isp Hcount Hstate Hj Hquot Hmod.
  unfold prime_test_state in *.
  destruct Hstate as [Hjold [_ [_ _]]].
  split; [lia |].
  split; [lia |].
  split.
  - intros Hfalse. lia.
  - intros _.
    exists j.
    repeat split; try lia; assumption.
Qed.

Lemma prime_test_state_step_keep : forall candidate result j isp,
  count_up_to_state candidate result ->
  prime_test_state candidate result j isp ->
  0 <= j < Zlength result ->
  candidate mod Znth j result 0 <> 0 ->
  prime_test_state candidate result (j + 1) isp.
Proof.
  intros candidate result j isp Hcount Hstate Hj Hmod.
  unfold prime_test_state in *.
  destruct Hstate as [Hjold [Hisp [Hnonzero Hzero]]].
  split; [lia |].
  split; [lia |].
  split.
  - intros Hisp_ne k Hk Hquot.
    assert (k < j \/ k = j) as [Hlt | ->] by lia.
    + apply Hnonzero; try lia; assumption.
    + exact Hmod.
  - intros Hisp_zero.
    destruct (Hzero Hisp_zero) as [k [Hk [Hq Hm]]].
    exists k.
    repeat split; try lia; assumption.
Qed.

Lemma problem_96_spec_z_empty : forall n,
  0 <= n <= 2 ->
  problem_96_spec_z n [].
Proof.
  intros n Hn.
  unfold problem_96_spec_z.
  split.
  - intros q Hq. contradiction.
  - split.
    + intros q Hq. contradiction.
    + split.
      * intros q Hq Hq_lt.
        inversion Hq.
        apply Nat2Z.inj_lt in Hq_lt.
        rewrite Z2Nat.id in Hq_lt by lia.
        lia.
      * split; constructor.
Qed.

Lemma count_up_to_state_empty_i2 : forall i,
  count_up_to_state i [] ->
  2 <= i ->
  i = 2.
Proof.
  intros i Hstate Hi.
  destruct (Z.eq_dec i 2) as [-> | Hneq]; [reflexivity |].
  assert (2 < i) by lia.
  unfold count_up_to_state in Hstate.
  destruct Hstate as [_ [_ [_ [Hcomplete _]]]].
  specialize (Hcomplete 2 ltac:(lia) prime_2).
  contradiction.
Qed.

Lemma count_up_to_state_skip_not_prime : forall i result,
  count_up_to_state i result ->
  ~ prime i ->
  count_up_to_state (i + 1) result.
Proof.
  intros i result Hstate Hnot.
  unfold count_up_to_state in *.
  destruct Hstate as [Hi [Hlen [Hall [Hcomplete [Hsorted Hnodup]]]]].
  split; [lia |].
  split; [lia |].
  split.
  - intros p Hp.
    destruct (Hall p Hp) as [[Hp_ge Hp_lt] Hpprime].
    split; [lia | exact Hpprime].
  - split.
    + intros p Hp Hprime.
      assert (p < i \/ p = i) as [Hlt | ->] by lia.
      * apply Hcomplete; lia || assumption.
      * contradiction.
    + split; assumption.
Qed.

Lemma Sorted_lt_app_last_96 : forall l x,
  Sorted Z.lt l ->
  (forall y, In y l -> y < x) ->
  Sorted Z.lt (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x Hsorted Hall; simpl.
  - constructor; constructor.
  - pose proof (Sorted_inv Hsorted) as [Htail Hhd].
    constructor.
    + apply IH; auto.
      intros y Hy. apply Hall. right; exact Hy.
    + destruct l as [|b l'].
      * constructor. apply Hall. left; reflexivity.
      * inversion Hhd; subst.
        constructor. assumption.
Qed.

Lemma count_up_to_state_append_prime : forall i result,
  count_up_to_state i result ->
  prime i ->
  count_up_to_state (i + 1) (result ++ [i]).
Proof.
  intros i result Hstate Hprime.
  unfold count_up_to_state in *.
  destruct Hstate as [Hi [Hlen [Hall [Hcomplete [Hsorted Hnodup]]]]].
  split; [lia |].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - split.
    + intros p Hp.
      apply in_app_or in Hp.
      destruct Hp as [Hp | Hp].
      * destruct (Hall p Hp) as [[Hp_ge Hp_lt] Hpprime].
        split; [lia | exact Hpprime].
      * simpl in Hp. destruct Hp as [-> | []].
        split; [lia | exact Hprime].
    + split.
      * intros p Hp Hpprime.
        assert (p < i \/ p = i) as [Hlt | ->] by lia.
        -- apply in_or_app. left. apply Hcomplete; lia || assumption.
        -- apply in_or_app. right. simpl. auto.
      * split.
        -- apply Sorted_lt_app_last_96; auto.
           intros y Hy.
           destruct (Hall y Hy) as [[_ Hy_lt] _].
           exact Hy_lt.
        -- apply NoDup_app.
           ++ exact Hnodup.
           ++ constructor; [intros [] | constructor].
           ++ intros y Hy Hin.
              simpl in Hin. destruct Hin as [Hy_eq | []].
              subst y.
              destruct (Hall i Hy) as [[_ Hlt] _].
              lia.
Qed.

Lemma divide_trans_96 : forall a b c,
  (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [x Hx] [y Hy].
  exists (y * x).
  rewrite Hy, Hx.
  ring.
Qed.

Lemma exists_prime_divisor_96 : forall n,
  1 < n ->
  exists p, prime p /\ (p | n) /\ 2 <= p <= n.
Proof.
  apply (well_founded_induction
           (Z.lt_wf 0)
           (fun n => 1 < n -> exists p, prime p /\ (p | n) /\ 2 <= p <= n)).
  intros n IH Hn.
  destruct (prime_dec n) as [Hprime | Hnot].
  - exists n.
    split; [exact Hprime |].
    split.
    + exists 1. lia.
    + lia.
  - destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
    assert (Hrec : 0 <= d < n) by lia.
    destruct (IH d Hrec ltac:(lia)) as [p [Hp [Hpdiv Hrange]]].
    exists p.
    split; [exact Hp |].
    split.
    + eapply divide_trans_96; eauto.
    + lia.
Qed.

Lemma composite_small_prime_divisor_96 : forall n,
  1 < n ->
  ~ prime n ->
  exists p, prime p /\ (p | n) /\ 2 <= p < n /\ p <= n / p.
Proof.
  intros n Hn Hnot.
  destruct (not_prime_divide n Hn Hnot) as [d [[Hd_gt Hd_lt] Hdiv]].
  destruct Hdiv as [q Hn_eq].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hq_gt1 : 1 < q).
  {
    destruct (Z_le_gt_dec q 1); [| lia].
    assert (q <= 0 \/ q = 1) as [Hqle | ->] by lia.
    - nia.
    - nia.
  }
  assert (Hq_pos : 0 < q) by lia.
  assert (Hd_case : d <= q \/ q < d) by lia.
  destruct Hd_case as [Hd_le_q | Hq_lt_d].
  - destruct (exists_prime_divisor_96 d ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split; [exact Hp |].
    split.
    + eapply divide_trans_96; eauto. exists q. exact Hn_eq.
    + split; [lia |].
      assert (p <= d) by lia.
      assert (d <= n / d).
      {
        apply Z.div_le_lower_bound; nia.
      }
      assert (n / d <= n / p).
      {
        apply Z.div_le_lower_bound; try lia.
        pose proof (Z.mul_div_le n d ltac:(lia)).
        nia.
      }
      lia.
  - destruct (exists_prime_divisor_96 q ltac:(lia)) as [p [Hp [Hpdiv [Hp_ge Hp_le]]]].
    exists p.
    split; [exact Hp |].
    split.
    + destruct Hpdiv as [m Hq_eq].
      exists (d * m).
      rewrite Hn_eq, Hq_eq.
      ring.
    + split; [lia |].
      assert (p <= q) by lia.
      assert (q <= n / q).
      {
        rewrite Hn_eq.
        apply Z.div_le_lower_bound; nia.
      }
      assert (n / q <= n / p).
      {
        apply Z.div_le_lower_bound; try lia.
        pose proof (Z.mul_div_le n q ltac:(lia)).
        nia.
      }
      lia.
Qed.

Lemma prime_test_state_exit_prime_full : forall i result j isp,
  count_up_to_state i result ->
  prime_test_state i result j isp ->
  j >= Zlength result ->
  isp <> 0 ->
  prime i.
Proof.
  intros i result j isp Hcount Htest Hj Hisp.
  destruct (prime_dec i) as [Hprime | Hnot]; [exact Hprime |].
  unfold count_up_to_state in Hcount.
  destruct Hcount as [Hi [_ [_ [Hcomplete _]]]].
  unfold prime_test_state in Htest.
  destruct Htest as [_ [_ [Hchecked _]]].
  destruct (composite_small_prime_divisor_96 i ltac:(lia) Hnot)
    as [p [Hp [Hdiv [[Hp_ge Hp_lt] Hple]]]].
  assert (Hin : In p result) by (apply Hcomplete; lia || assumption).
  destruct (In_Znth_exists_96 p result Hin) as [k [Hk Hkval]].
  specialize (Hchecked Hisp k ltac:(lia)).
  rewrite Hkval in Hchecked.
  exfalso.
  apply Hchecked; [exact Hple |].
  apply Z.mod_divide; try lia.
  exact Hdiv.
Qed.

Lemma Sorted_lt_to_le_96 : forall l,
  Sorted Z.lt l ->
  Sorted Z.le l.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
    induction H0; constructor; auto; lia.
Qed.

Lemma Sorted_cons_all_le_96 : forall x l y,
  Sorted Z.le (x :: l) ->
  In y (x :: l) ->
  x <= y.
Proof.
  intros x l.
  revert x.
  induction l; intros x y Hsorted Hin.
  - simpl in Hin. destruct Hin as [-> | []]. lia.
  - simpl in Hin. destruct Hin as [-> | Hin]; [lia |].
    pose proof (Sorted_inv Hsorted) as [Htail Hhd].
    assert (x <= a).
    { inversion Hhd; subst. assumption. }
    assert (a <= y).
    { apply IHl.
      - exact Htail.
      - simpl. exact Hin. }
    lia.
Qed.

Lemma nth_sorted_le_nat_96 : forall l n m d,
  Sorted Z.le l ->
  (n <= m < length l)%nat ->
  nth n l d <= nth m l d.
Proof.
  induction l; intros n m d Hsorted Hrange.
  - simpl in Hrange. lia.
  - destruct n; destruct m; simpl.
    + lia.
    + apply (Sorted_cons_all_le_96 a l (nth m l d)).
      * exact Hsorted.
      * right. apply nth_In. simpl in Hrange. lia.
    + lia.
    + pose proof (Sorted_inv Hsorted) as [Htail _].
      apply IHl; auto.
      simpl in Hrange. lia.
Qed.

Lemma Sorted_Znth_le_96 : forall l i j,
  Sorted Z.le l ->
  0 <= i <= j ->
  j < Zlength l ->
  Znth i l 0 <= Znth j l 0.
Proof.
  intros l i j Hsorted Hij Hj.
  unfold Znth.
  apply nth_sorted_le_nat_96.
  - exact Hsorted.
  - rewrite Zlength_correct in Hj.
    split.
    + apply Z2Nat.inj_le; lia.
    + apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia.
Qed.

Lemma divisor_mod_zero_96 : forall a b,
  b <> 0 ->
  a mod b = 0 ->
  (b | a).
Proof.
  intros a b Hb Hmod.
  apply Z.mod_divide; assumption.
Qed.

Lemma prime_test_state_zero_not_prime : forall i result j,
  count_up_to_state i result ->
  prime_test_state i result j 0 ->
  ~ prime i.
Proof.
  intros i result j Hcount Htest Hprime_i.
  unfold prime_test_state in Htest.
  destruct Htest as [Hj [_ [_ Hzero]]].
  destruct (Hzero eq_refl) as [k [Hk [Hquot Hmod]]].
  pose proof (count_up_to_state_Znth_prime i result k Hcount ltac:(lia))
    as [[Hz_ge Hz_lt] Hz_prime].
  assert (Hdiv : (Znth k result 0 | i)).
  { apply Z.mod_divide; lia. }
  pose proof (prime_divisors i Hprime_i (Znth k result 0) Hdiv)
    as [Heq | [Heq | [Heq | Heq]]]; lia.
Qed.

Lemma prime_test_state_exit_prime_early : forall i result j isp,
  count_up_to_state i result ->
  prime_test_state i result j isp ->
  0 <= j < Zlength result ->
  Znth j result 0 > i / Znth j result 0 ->
  isp <> 0 ->
  prime i.
Proof.
  intros i result j isp Hcount Htest Hj Hexit Hisp.
  destruct (prime_dec i) as [Hprime | Hnot]; [exact Hprime |].
  unfold count_up_to_state in Hcount.
  destruct Hcount as [Hi [Hlen [Hall [Hcomplete [Hsorted Hnodup]]]]].
  unfold prime_test_state in Htest.
  destruct Htest as [_ [_ [Hchecked _]]].
  destruct (composite_small_prime_divisor_96 i ltac:(lia) Hnot)
    as [p [Hp [Hdiv [[Hp_ge Hp_lt] Hp_le_div]]]].
  assert (Hin : In p result) by (apply Hcomplete; lia || assumption).
  destruct (In_Znth_exists_96 p result Hin) as [k [Hk Hkval]].
  assert (k < j).
  {
    destruct (Z_lt_ge_dec k j) as [Hlt | Hge]; [exact Hlt | exfalso].
    assert (Hj_le_p : Znth j result 0 <= p).
    {
      rewrite <- Hkval.
      eapply Sorted_Znth_le_96.
      - apply Sorted_lt_to_le_96. exact Hsorted.
      - lia.
      - lia.
    }
    assert (Hj_pos : 0 < Znth j result 0).
    {
      pose proof (count_up_to_state_Znth_prime i result j
                    (conj Hi (conj Hlen (conj Hall (conj Hcomplete (conj Hsorted Hnodup)))))
                    Hj) as [[Hpos _] _].
      lia.
    }
    assert (Hp_pos : 0 < p) by lia.
    assert (i / p <= i / Znth j result 0).
    {
      apply Z.div_le_lower_bound; try lia.
      pose proof (Z.mul_div_le i p ltac:(lia)).
      nia.
    }
    lia.
  }
  specialize (Hchecked Hisp k ltac:(lia)).
  rewrite Hkval in Hchecked.
  exfalso.
  apply Hchecked; [exact Hp_le_div |].
  apply Z.mod_divide; try lia.
  exact Hdiv.
Qed.

Local Open Scope Z_scope.
