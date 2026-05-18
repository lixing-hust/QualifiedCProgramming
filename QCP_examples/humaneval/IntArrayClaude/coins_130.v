Load "../spec/130".

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition list_Z_to_nat (l : list Z) : list nat :=
  map Z.to_nat l.

Definition tri_z (i : Z) : Z :=
  Z.of_nat (tri (Z.to_nat i)).

Definition tri_sequence (n : Z) : list Z :=
  map tri_z (Zseq 0 (Z.to_nat (n + 1))).

Definition problem_130_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_130_pre (Z.to_nat n).

Definition problem_130_spec_z (n : Z) (out : list Z) : Prop :=
  0 <= n /\ problem_130_spec (Z.to_nat n) (list_Z_to_nat out).

Definition tri_seq_int_range (n : Z) : Prop :=
  (forall i, 0 <= i <= n -> INT_MIN <= tri_z i <= INT_MAX) /\
  (forall i, 2 <= i <= n ->
     INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
     INT_MIN <= tri_z (i - 1) + tri_z (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX).

Lemma tri_z_0 :
  tri_z 0 = 1.
Proof. reflexivity. Qed.

Lemma tri_z_1 :
  tri_z 1 = 3.
Proof. reflexivity. Qed.

Lemma tri_sequence_Zlength : forall n,
  0 <= n ->
  Zlength (tri_sequence n) = n + 1.
Proof.
  intros n Hn.
  unfold tri_sequence.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma tri_sequence_Znth : forall n i,
  0 <= i <= n ->
  Znth i (tri_sequence n) 0 = tri_z i.
Proof.
  intros n i Hi.
  assert (Hn : 0 <= n) by lia.
  unfold tri_sequence, Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.

Lemma tri_sequence_sublist_snoc : forall n i,
  0 <= i <= n ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ tri_z i :: nil.
Proof.
  intros n i Hi.
  pose proof (tri_sequence_Zlength n ltac:(lia)) as Hlen.
  rewrite (sublist_split 0 (i + 1) i).
  - rewrite (sublist_single i (tri_sequence n) 0).
    + rewrite tri_sequence_Znth by lia.
      reflexivity.
    + rewrite <- Zlength_correct.
      rewrite Hlen.
      lia.
  - lia.
  - rewrite <- Zlength_correct.
    rewrite Hlen.
    lia.
Qed.

Lemma tri_sequence_sublist_Znth : forall n i j,
  0 <= j < i ->
  i <= n + 1 ->
  Znth (j - 0) (sublist 0 i (tri_sequence n)) 0 = tri_z j.
Proof.
  intros n i j Hj Hi.
  replace (j - 0) with j by lia.
  rewrite Znth_sublist0 by lia.
  apply tri_sequence_Znth.
  lia.
Qed.

Lemma Z_even_of_nat : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n.
  - reflexivity.
  - rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    rewrite Z.even_add.
    simpl.
    rewrite IHn.
    destruct (Nat.even n); reflexivity.
Qed.

Lemma Nat_even_of_Z_nonneg : forall z,
  0 <= z ->
  Nat.even (Z.to_nat z) = Z.even z.
Proof.
  intros z Hz.
  rewrite <- Z_even_of_nat.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma Z_quot_2_of_nat_nonneg : forall z,
  0 <= z ->
  Z.of_nat (Z.to_nat z / 2) = Z.quot z 2.
Proof.
  intros z Hz.
  rewrite Nat2Z.inj_div by lia.
  rewrite Z2Nat.id by lia.
  rewrite Z.quot_div_nonneg; lia.
Qed.

Lemma tri_even_nat : forall n,
  (2 <= n)%nat ->
  Nat.even n = true ->
  tri n = (1 + n / 2)%nat.
Proof.
  intros n Hn Heven.
  destruct n as [|[|k]]; try lia.
  simpl.
  replace (Nat.even k) with true by (symmetry; exact Heven).
  reflexivity.
Qed.

Lemma tri_odd_nat : forall n,
  (2 <= n)%nat ->
  Nat.even n = false ->
  tri n = (1 + (n - 1) / 2 + tri (n - 2) + (1 + (n + 1) / 2))%nat.
Proof.
  intros n Hn Hodd.
  destruct n as [|[|k]]; try lia.
  simpl.
  replace (Nat.even k) with false by (symmetry; exact Hodd).
  replace (k - 0)%nat with k by lia.
  reflexivity.
Qed.

Lemma tri_z_even_quot : forall i,
  2 <= i ->
  Z.rem i 2 = 0 ->
  tri_z i = 1 + Z.quot i 2.
Proof.
  intros i Hi Hrem.
  unfold tri_z.
  assert (Heven : Nat.even (Z.to_nat i) = true).
  {
    rewrite Nat_even_of_Z_nonneg by lia.
    rewrite Zeven_mod.
    rewrite Z.rem_mod_nonneg in Hrem by lia.
    rewrite Hrem.
    reflexivity.
  }
  rewrite tri_even_nat; [|lia|exact Heven].
  rewrite Nat2Z.inj_add.
  rewrite Z_quot_2_of_nat_nonneg by lia.
  lia.
Qed.

Lemma tri_z_odd_quot : forall i,
  2 <= i ->
  Z.rem i 2 <> 0 ->
  tri_z i = tri_z (i - 1) + tri_z (i - 2) + 1 + Z.quot (i + 1) 2.
Proof.
  intros i Hi Hrem.
  assert (Hmod : i mod 2 <> 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact Hrem. }
  assert (Hodd_nat : Nat.even (Z.to_nat i) = false).
  {
    rewrite Nat_even_of_Z_nonneg by lia.
    destruct (Z.even i) eqn:Heven; [|reflexivity].
    apply Z.even_spec in Heven.
    destruct Heven as [q Hq].
    exfalso.
    apply Hrem.
    subst i.
    replace (2 * q) with (q * 2) by lia.
    rewrite Z.rem_mul; lia.
  }
  unfold tri_z at 1.
  rewrite tri_odd_nat; [|lia|exact Hodd_nat].
  rewrite !Nat2Z.inj_add.
  replace (Z.of_nat (Z.to_nat i - 2)) with (i - 2) by
    (rewrite Nat2Z.inj_sub; replace (Z.of_nat (Z.to_nat i)) with i by lia; lia).
  replace (Z.of_nat (Z.to_nat i - 1)) with (i - 1) by
    (rewrite Nat2Z.inj_sub; replace (Z.of_nat (Z.to_nat i)) with i by lia; lia).
  replace (Z.of_nat (Z.to_nat i + 1)) with (i + 1) by
    (rewrite Nat2Z.inj_add; replace (Z.of_nat (Z.to_nat i)) with i by lia; lia).
  replace (Z.of_nat (tri (Z.to_nat i - 2))) with (tri_z (i - 2)) by
    (unfold tri_z; replace (Z.to_nat (i - 2)) with (Z.to_nat i - 2)%nat by lia; reflexivity).
  assert (Hi_odd_ge3 : 3 <= i).
  {
    assert (i <> 2) by (intro Hcontra; subst i; apply Hrem; reflexivity).
    lia.
  }
  replace (Z.of_nat 1 + Z.of_nat ((Z.to_nat i - 1) / 2)) with (tri_z (i - 1)).
  2:{
    rewrite tri_z_even_quot; [|lia|].
    - replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)) by lia.
      rewrite Z_quot_2_of_nat_nonneg by lia.
      lia.
    - assert (Heveni : Z.even i = false).
      {
        rewrite <- Nat_even_of_Z_nonneg by lia.
        exact Hodd_nat.
      }
      assert (Hevenm : Z.even (i - 1) = true).
      {
        replace (i - 1) with (i + (-1)) by lia.
        rewrite Z.even_add.
        rewrite Heveni.
        reflexivity.
      }
      apply Z.even_spec in Hevenm.
      destruct Hevenm as [q Hq].
      rewrite Hq.
      replace (2 * q) with (q * 2) by lia.
      rewrite Z.rem_mul; lia.
  }
  replace (Z.of_nat 1 + Z.of_nat ((Z.to_nat i + 1) / 2)) with (1 + Z.quot (i + 1) 2) by
    (replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia;
     rewrite Z_quot_2_of_nat_nonneg by lia;
     lia).
  lia.
Qed.

Lemma tri_z_nonneg : forall i,
  0 <= tri_z i.
Proof.
  intros i.
  unfold tri_z.
  lia.
Qed.

Lemma tri_even_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [H _].
  exact H.
Qed.

Lemma tri_odd_expr_range : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri_z (i - 1) + tri_z (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  destruct Hrange as [_ Hstep].
  pose proof (Hstep i Hi) as [_ H].
  exact H.
Qed.

Lemma tri_odd_expr_partial_range_1 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri_z (i - 1) + tri_z (i - 2) <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_z_nonneg (i - 1)).
  pose proof (tri_z_nonneg (i - 2)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma tri_odd_expr_partial_range_2 : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= tri_z (i - 1) + tri_z (i - 2) + 1 <= INT_MAX.
Proof.
  intros n i Hrange Hi.
  pose proof (tri_odd_expr_range n i Hrange Hi) as Hfull.
  pose proof (tri_z_nonneg (i - 1)).
  pose proof (tri_z_nonneg (i - 2)).
  assert (0 <= Z.quot (i + 1) 2) by (apply Z.quot_pos; lia).
  lia.
Qed.

Lemma tri_sequence_even_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 = 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++ (1 + Z.quot i 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_z_even_quot by lia.
  reflexivity.
Qed.

Lemma tri_sequence_odd_snoc : forall n i,
  2 <= i <= n ->
  Z.rem i 2 <> 0 ->
  sublist 0 (i + 1) (tri_sequence n) =
  sublist 0 i (tri_sequence n) ++
  (Znth (i - 1 - 0) (sublist 0 i (tri_sequence n)) 0 +
   Znth (i - 2 - 0) (sublist 0 i (tri_sequence n)) 0 +
   1 + Z.quot (i + 1) 2) :: nil.
Proof.
  intros n i Hi Hrem.
  rewrite tri_sequence_sublist_snoc by lia.
  rewrite tri_z_odd_quot by lia.
  rewrite !tri_sequence_sublist_Znth by lia.
  reflexivity.
Qed.

Lemma tri_sequence_sublist_2 : forall n,
  1 <= n ->
  sublist 0 2 (tri_sequence n) = 1 :: 3 :: nil.
Proof.
  intros n Hn.
  rewrite tri_sequence_sublist_snoc with (i := 1) by lia.
  rewrite tri_sequence_sublist_snoc with (i := 0) by lia.
  rewrite sublist_nil by lia.
  rewrite tri_z_0, tri_z_1.
  reflexivity.
Qed.

Lemma tri_sequence_spec_z : forall n,
  0 <= n ->
  problem_130_spec_z n (tri_sequence n).
Proof.
  intros n Hn.
  split; [lia|].
  unfold problem_130_spec_z in *.
  unfold problem_130_spec, list_Z_to_nat.
  split.
  - rewrite length_map.
    unfold tri_sequence.
    rewrite length_map, Zseq_length.
    rewrite Z2Nat.inj_add by lia.
    simpl.
    lia.
  - intros i Hi.
    rewrite nth_indep with (d' := Z.to_nat 0).
    + rewrite <- map_map.
      unfold tri_sequence.
      rewrite map_map.
      rewrite map_nth with (d := 0%Z).
      unfold tri_z.
      rewrite nth_indep with (d' := (fun i0 : Z => Z.of_nat (tri (Z.to_nat i0))) 0%Z).
      2:{
        rewrite length_map, Zseq_length.
        rewrite Z2Nat.inj_add by lia.
        simpl.
        lia.
      }
      rewrite map_nth with (d := 0%Z).
      rewrite Zseq_nth by lia.
      rewrite Nat2Z.id.
      replace (Z.to_nat (0 + Z.of_nat i)) with i by lia.
      reflexivity.
    + rewrite length_map.
      unfold tri_sequence.
      rewrite length_map, Zseq_length.
      rewrite Z2Nat.inj_add by lia.
      simpl.
      lia.
Qed.

Lemma tri_seq_int_range_value : forall n i,
  tri_seq_int_range n ->
  0 <= i <= n ->
  INT_MIN <= tri_z i <= INT_MAX.
Proof.
  intros n i [Hrange _] Hi.
  apply Hrange; lia.
Qed.

Lemma tri_seq_int_range_step : forall n i,
  tri_seq_int_range n ->
  2 <= i <= n ->
  INT_MIN <= 1 + Z.quot i 2 <= INT_MAX /\
  INT_MIN <= tri_z (i - 1) + tri_z (i - 2) + 1 + Z.quot (i + 1) 2 <= INT_MAX.
Proof.
  intros n i [_ Hstep] Hi.
  apply Hstep; lia.
Qed.
