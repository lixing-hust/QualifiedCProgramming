Load "../spec/59".
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Definition lpf_inv (n_pre n i : Z) : Prop :=
  n >= 2 /\
  n_pre mod n = 0 /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n \/ n = p) /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n -> p <= n) /\
  (forall q : Z, prime q -> q >= i -> Z.divide q n_pre -> Z.divide q n).

Definition lpf_while_inv (n_pre n i : Z) : Prop :=
  i + 1 <= 2147483647 /\
  n >= 2 /\
  n_pre mod n = 0 /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n \/ n = p) /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n -> p <= n) /\
  (forall q : Z, prime q -> q > i -> Z.divide q n_pre -> Z.divide q n).

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

Lemma lpf_spec_from_exit :
  forall n_pre n i : Z,
  problem_59_pre n_pre ->
  2 <= n_pre ->
  n_pre <= 2147483647 ->
  2 <= i ->
  i > n / i ->
  lpf_inv n_pre n i ->
  problem_59_spec n_pre n.
Proof.
  intros n_pre n i _ _ _ Hi2 Hexit Hinv.
  destruct Hinv as [Hn2 [Hmod [Hsmall_div [Hsmall_bound Hlarge_div]]]].
  assert (Hn_div_npre : Z.divide n n_pre).
  {
    apply Z.mod_divide in Hmod; [exact Hmod|lia].
  }
  assert (Hprime_n : prime n).
  {
    assert (Hn2_le : 2 <= n) by lia.
    destruct (prime_dec n) as [Hprime|Hnot_prime]; [exact Hprime|].
    exfalso.
    destruct (composite_has_small_prime_divisor n Hn2_le Hnot_prime) as [p [Hp_prime [Hp_div_n Hp_sq_le_n]]].
    assert (Hn_lt_ii : n < i * i) by (apply div_square_lt_from_exit; auto).
    assert (Hp_ge2 : 2 <= p) by (apply prime_ge_2; exact Hp_prime).
    assert (Hp_lt_i : p < i).
    {
      apply Z.nle_gt; intros Hp_ge_i.
      assert (Hi_sq_le_p_sq : i * i <= p * p) by nia.
      lia.
    }
    specialize (Hsmall_div p Hp_prime Hp_ge2 Hp_lt_i).
    destruct Hsmall_div as [Hp_not_div_n | Hn_eq_p].
    - contradiction.
    - subst n. contradiction.
  }
  split.
  - exact Hprime_n.
  - split.
    + exact Hn_div_npre.
    + intros q [Hq_prime Hq_div_npre].
      destruct (Z_lt_ge_dec q i) as [Hq_lt_i | Hq_ge_i].
      * assert (Hq_ge2 : 2 <= q) by (apply prime_ge_2; exact Hq_prime).
        specialize (Hsmall_div q Hq_prime Hq_ge2 Hq_lt_i).
        destruct Hsmall_div as [Hq_not_div_n | Hn_eq_q].
        -- apply Hsmall_bound; auto.
        -- subst q. lia.
      * assert (Hq_div_n : Z.divide q n).
        {
          apply Hlarge_div; auto.
        }
        apply Z.divide_pos_le.
        -- lia.
        -- exact Hq_div_n.
Qed.
