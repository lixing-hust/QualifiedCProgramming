Load "../spec/76".
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto.

Open Scope Z_scope.

(* Adapt bool result to Z: r <> 0 means true *)
Definition is_simple_power_spec (x n r : Z) : Prop :=
  r <> 0 <-> (exists k : nat, x = n ^ Z.of_nat k).

Definition sp_inv (x n count p : Z) : Prop :=
  0 <= count /\
  p = n ^ count /\
  (forall k : Z, 0 <= k < count -> n ^ k <> x).

Lemma sp_inv_init :
  forall x n,
    sp_inv x n 0 1.
Proof.
  intros x n.
  unfold sp_inv.
  split.
  - lia.
  - split.
    + rewrite Z.pow_0_r. reflexivity.
    + intros k Hk.
      lia.
Qed.

Lemma sp_inv_step :
  forall x n count p,
    sp_inv x n count p ->
    p <> x ->
    sp_inv x n (count + 1) (p * n).
Proof.
  intros x n count p Hinv Hpneq.
  unfold sp_inv in *.
  destruct Hinv as [Hc0 [Hp Hno]].
  repeat split.
  - lia.
  - rewrite Hp.
    replace (n ^ (count + 1)) with (n ^ count * n).
    + ring.
    + rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      ring.
  - intros k Hk.
    assert (Hsplit : k < count \/ k = count) by lia.
    destruct Hsplit as [Hlt | Heq].
    + apply Hno. lia.
    + subst k.
      intro Hpow.
      apply Hpneq.
      rewrite Hp.
      exact Hpow.
Qed.

Lemma sp_inv_hit_witness :
  forall x n count p,
    sp_inv x n count p ->
    p = x ->
    count < 100 ->
    exists k : nat, x = n ^ Z.of_nat k.
Proof.
  intros x n count p Hinv Hpeq Hlt100.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp _]].
  exists (Z.to_nat count).
  assert (Hcount : Z.of_nat (Z.to_nat count) = count) by (apply Z2Nat.id; lia).
  rewrite Hcount.
  assert (Hx : x = n ^ count).
  {
    rewrite <- Hpeq.
    exact Hp.
  }
  exact Hx.
Qed.

Lemma no_power_if_gt :
  forall x n count p,
    sp_inv x n count p ->
    p > x ->
    1 <= n ->
    ~(exists k : nat, x = n ^ Z.of_nat k).
Proof.
  intros x n count p Hinv Hpgt Hn1 Hex.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp Hno]].
  destruct Hex as [k Hxk].
  set (kz := Z.of_nat k).
  assert (Hsplit : kz < count \/ count <= kz) by lia.
  destruct Hsplit as [Hlt | Hge].
  - specialize (Hno kz).
    assert (Hneq : n ^ kz <> x) by (apply Hno; lia).
    apply Hneq.
    subst kz.
    symmetry.
    exact Hxk.
  - subst kz.
    assert (Hmono : n ^ count <= n ^ Z.of_nat k).
    {
      apply Z.pow_le_mono_r; lia.
    }
    rewrite <- Hp in Hmono.
    rewrite <- Hxk in Hmono.
    lia.
Qed.

Lemma no_power_if_cutoff :
  forall x n count p,
    sp_inv x n count p ->
    count >= 100 ->
    p <= x ->
    x <= 2147483647 ->
    1 <= n ->
    ~(exists k : nat, x = n ^ Z.of_nat k).
Proof.
  intros x n count p Hinv Hc100 Hpx Hxmax Hn1 Hex.
  unfold sp_inv in Hinv.
  destruct Hinv as [Hc0 [Hp Hno]].
  destruct (Z_lt_ge_dec n 2) as [Hnlt2 | Hnge2].
  - assert (Hn1eq : n = 1) by lia.
    subst n.
    destruct Hex as [k Hxk].
    assert (Hx1 : x = 1).
    {
      rewrite Z.pow_1_l in Hxk by lia.
      exact Hxk.
    }
    assert (Hneq : 1 ^ 0 <> x).
    {
      apply Hno.
      lia.
    }
    rewrite Z.pow_0_r in Hneq.
    apply Hneq.
    symmetry.
    exact Hx1.
  - assert (H31 : 2 ^ 31 = 2147483648) by (vm_compute; reflexivity).
    assert (Hpow2_31 : 2147483647 < 2 ^ 31).
    {
      rewrite H31.
      lia.
    }
    assert (Hpow2_100 : 2 ^ 31 <= 2 ^ 100) by (apply Z.pow_le_mono_r; lia).
    assert (Hpow2 : 2147483647 < 2 ^ 100) by lia.
    assert (Hbase : 2 ^ 100 <= n ^ 100) by (apply Z.pow_le_mono_l; lia).
    assert (Hexp : n ^ 100 <= n ^ count) by (apply Z.pow_le_mono_r; lia).
    assert (Hintmax_lt_p : 2147483647 < p).
    {
      rewrite Hp.
      eapply Z.lt_le_trans; [exact Hpow2 |].
      eapply Z.le_trans; [exact Hbase | exact Hexp].
    }
    lia.
Qed.
