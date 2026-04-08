Load "../spec/150".
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Definition problem_150_spec_z (n x y r : Z) : Prop :=
  problem_150_spec (Z.to_nat n) (Z.to_nat x) (Z.to_nat y) (Z.to_nat r).

Lemma problem_150_spec_z_prime :
  forall n x y : Z,
  2 <= n ->
  prime n ->
  problem_150_spec_z n x y x.
Proof.
  intros n x y Hn Hp.
  unfold problem_150_spec_z, problem_150_spec.
  rewrite !Z2Nat.id by lia.
  split; intro H.
  - reflexivity.
  - contradiction.
Qed.

Lemma problem_150_spec_z_not_prime :
  forall n x y : Z,
  2 <= n ->
  ~ prime n ->
  problem_150_spec_z n x y y.
Proof.
  intros n x y Hn Hnp.
  unfold problem_150_spec_z, problem_150_spec.
  rewrite !Z2Nat.id by lia.
  split; intro H.
  - contradiction.
  - reflexivity.
Qed.

Lemma composite_has_small_prime_divisor :
  forall n : Z,
  2 <= n ->
  ~ prime n ->
  exists p : Z, prime p /\ Z.divide p n /\ p * p <= n.
Proof.
  refine (well_founded_induction_type (Z.lt_wf 1)
    (fun n => 2 <= n -> ~ prime n -> exists p, prime p /\ Z.divide p n /\ p * p <= n) _).
  intros n IH Hn2 Hn_not_prime.
  assert (Hn_gt1 : 1 < n) by lia.
  destruct (not_prime_divide n Hn_gt1 Hn_not_prime) as [d [[Hd_gt1 Hd_lt_n] Hd_div_n]].
  destruct Hd_div_n as [k Hn_eq].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hk_pos : 0 < k) by (subst n; nia).
  assert (Hk_gt1 : 1 < k) by (subst n; nia).
  set (m := Z.min d k).
  assert (Hm_lt_n : m < n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_gt1 : 1 < m).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_div_n : Z.divide m n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia. exists k. exact Hn_eq.
    - rewrite Z.min_r by lia. exists d. subst n. ring.
  }
  destruct (prime_dec m) as [Hm_prime|Hm_not_prime].
  - exists m. split; [exact Hm_prime|].
    split; [exact Hm_div_n|].
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    + rewrite Z.min_l by lia. subst n. nia.
    + rewrite Z.min_r by lia. subst n. nia.
  - specialize (IH m).
    assert (Hm_range : 1 <= m < n) by lia.
    specialize (IH Hm_range).
    assert (Hm_ge2 : 2 <= m) by lia.
    specialize (IH Hm_ge2 Hm_not_prime).
    destruct IH as [p [Hp_prime [Hp_div_m Hp_sq_le_m]]].
    exists p. split; [exact Hp_prime|].
    split.
    + eapply Z.divide_trans; eauto.
    + lia.
Qed.

Lemma prime_of_no_divisors_upto_sqrt :
  forall n i : Z,
  2 <= n ->
  2 <= i ->
  i * i > n ->
  (forall k : Z, 2 <= k /\ k < i -> Z.rem n k <> 0) ->
  prime n.
Proof.
  intros n i Hn2 Hi2 Hexit Hnodiv.
  destruct (prime_dec n) as [Hp|Hnp]; [exact Hp|].
  exfalso.
  destruct (composite_has_small_prime_divisor n Hn2 Hnp) as [p [Hp_prime [Hp_div_n Hp_sq_le_n]]].
  assert (Hp_ge2 : 2 <= p) by (apply prime_ge_2; exact Hp_prime).
  assert (Hp_lt_i : p < i).
  {
    apply Z.nle_gt; intro Hp_ge_i.
    assert (Hi_sq_le_p_sq : i * i <= p * p) by nia.
    lia.
  }
  assert (Hprem0 : Z.rem n p = 0).
  {
    pose proof (Z.rem_divide n p ltac:(lia)) as Hiff.
    apply (proj2 Hiff).
    exact Hp_div_n.
  }
  specialize (Hnodiv p (conj Hp_ge2 Hp_lt_i)).
  contradiction.
Qed.

Lemma div_square_lt_from_exit :
  forall n i : Z,
  2 <= i ->
  i > n / i ->
  n < i * i.
Proof.
  intros n i Hi2 Hexit.
  assert (Hi_pos : 0 < i) by lia.
  pose proof (Z.div_mod n i (not_eq_sym (Z.lt_neq _ _ Hi_pos))) as Hmod.
  assert (Hr_bound : 0 <= n mod i < i) by (apply Z.mod_pos_bound; lia).
  destruct Hr_bound as [_ Hr_lt].
  nia.
Qed.

Lemma square_le_from_loop_guard :
  forall n i : Z,
  2 <= i ->
  i <= n / i ->
  i * i <= n.
Proof.
  intros n i Hi2 Hguard.
  assert (Hi_pos : 0 < i) by lia.
  pose proof (Z.div_mod n i (not_eq_sym (Z.lt_neq _ _ Hi_pos))) as Hmod.
  assert (Hr_bound : 0 <= n mod i < i) by (apply Z.mod_pos_bound; lia).
  destruct Hr_bound as [Hr_nonneg _].
  nia.
Qed.

Lemma not_prime_of_small_divisor :
  forall n d : Z,
  2 <= n ->
  2 <= d ->
  d < n ->
  Z.rem n d = 0 ->
  ~ prime n.
Proof.
  intros n d Hn2 Hd2 Hdlt Hrem Hp.
  assert (Hd_div_n : Z.divide d n).
  {
    pose proof (Z.rem_divide n d ltac:(lia)) as Hiff.
    apply (proj1 Hiff).
    exact Hrem.
  }
  destruct (prime_divisors n Hp d Hd_div_n) as [Hd|[Hd|[Hd|Hd]]]; lia.
Qed.
