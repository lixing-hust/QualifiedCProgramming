Load "../spec/79".
Load "../spec/103".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
From SimpleC.EE Require Import string_bridge.
From SimpleC.EE Require Export coins_44 coins_103.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_79_pre_z (decimal : Z) : Prop :=
  problem_79_pre (Z.to_nat decimal).

Definition problem_79_spec_z (decimal : Z) (output : list Z) : Prop :=
  problem_79_spec (Z.to_nat decimal) (string_of_list_z output).

Definition decorated_binary_digits_z (decimal : Z) : list Z :=
  [100; 98] ++ binary_digits_z decimal ++ [100; 98].

Definition decimal_binary_full_state_z
  (orig x digits : Z) (out_l : list Z) : Prop :=
  exists payload,
    binary_fill_full_state_z orig x digits payload /\
    out_l = [100; 98] ++ payload ++ [100; 98].

Lemma string_of_list_z_db : string_of_list_z [100; 98] = "db".
Proof. reflexivity. Qed.

Lemma nat_of_xO : forall n p,
  Z.of_nat n = Z.pos (xO p) -> n = (2 * Pos.to_nat p)%nat.
Proof.
  intros n p H.
  rewrite <- (Nat2Z.id n).
  rewrite H.
  rewrite Pos2Z.inj_xO.
  rewrite Z2Nat.inj_mul by lia.
  simpl.
  lia.
Qed.

Lemma nat_of_xI : forall n p,
  Z.of_nat n = Z.pos (xI p) -> n = (2 * Pos.to_nat p + 1)%nat.
Proof.
  intros n p H.
  rewrite <- (Nat2Z.id n).
  rewrite H.
  rewrite Pos2Z.inj_xI.
  rewrite Z2Nat.inj_add by lia.
  rewrite Z2Nat.inj_mul by lia.
  simpl.
  lia.
Qed.

Lemma div_xO : forall n p,
  Z.of_nat n = Z.pos (xO p) -> Z.of_nat (n / 2) = Z.pos p.
Proof.
  intros n p H.
  rewrite Nat2Z.inj_div by lia.
  rewrite H.
  rewrite Pos2Z.inj_xO.
  rewrite Z.mul_comm.
  rewrite Z.div_mul by lia.
  reflexivity.
Qed.

Lemma div_xI : forall n p,
  Z.of_nat n = Z.pos (xI p) -> Z.of_nat (n / 2) = Z.pos p.
Proof.
  intros n p H.
  rewrite Nat2Z.inj_div by lia.
  rewrite H.
  rewrite Pos2Z.inj_xI.
  replace (2 * Z.pos p + 1) with (Z.pos p * 2 + 1) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small by lia.
  lia.
Qed.

Lemma even_xO : forall n p,
  Z.of_nat n = Z.pos (xO p) -> Nat.even n = true.
Proof.
  intros n p H.
  apply Nat.even_spec.
  exists (Pos.to_nat p).
  apply nat_of_xO in H.
  lia.
Qed.

Lemma even_xI : forall n p,
  Z.of_nat n = Z.pos (xI p) -> Nat.even n = false.
Proof.
  intros n p H.
  destruct (Nat.even n) eqn:Hev; auto.
  apply Nat.even_spec in Hev.
  destruct Hev as [k Hk].
  apply nat_of_xI in H.
  lia.
Qed.

Local Open Scope nat_scope.

Lemma divmod_100 : forall n,
  fst (Nat.divmod n 1 0 0) = (S n / 2)%nat.
Proof.
  intros n.
  remember (Nat.divmod n 1 0 0) as r eqn:Hd.
  destruct r as [q u]. symmetry in Hd.
  pose proof (Nat.divmod_spec n 1 0 0 ltac:(lia)) as H.
  rewrite Hd in H.
  simpl in H. destruct H as [Heq Hu]. simpl.
  rewrite Hd. simpl.
  destruct u as [|[|u]]; try lia;
  exact (Nat.div_unique (S n) 2 q (1 - u) ltac:(lia) ltac:(lia)).
Qed.

Lemma divmod_111 : forall n,
  fst (Nat.divmod n 1 1 1) = (S (S n) / 2)%nat.
Proof.
  intros n.
  remember (Nat.divmod n 1 1 1) as r eqn:Hd.
  destruct r as [q u]. symmetry in Hd.
  pose proof (Nat.divmod_spec n 1 1 1 ltac:(lia)) as H.
  rewrite Hd in H.
  simpl in H. destruct H as [Heq Hu]. simpl.
  rewrite Hd. simpl.
  destruct u as [|[|u]]; try lia;
  exact (Nat.div_unique (S (S n)) 2 q (1 - u) ltac:(lia) ltac:(lia)).
Qed.

Lemma div_odd_same : forall n,
  Nat.even n = false -> (S n / 2 = S (S n) / 2)%nat.
Proof.
  intros n Hev.
  destruct (Nat.Even_or_Odd n) as [He | Ho].
  - destruct He as [k Hk].
    subst n.
    rewrite Nat.even_even in Hev.
    discriminate.
  - destruct Ho as [k Hk].
    subst n.
    assert ((S (2 * k + 1) / 2)%nat = S k).
    { symmetry. apply Nat.div_unique with (r := 0); lia. }
    assert ((S (S (2 * k + 1)) / 2)%nat = S k).
    { symmetry. apply Nat.div_unique with (r := 1); lia. }
    lia.
Qed.

Lemma nat_lt_pow2_self : forall n,
  (0 < n)%nat -> (n < 2 ^ n)%nat.
Proof.
  induction n; intros Hn; try lia.
  destruct n.
  - simpl. lia.
  - replace (2 ^ S (S n))%nat with (2 * 2 ^ S n)%nat by (simpl; lia).
    pose proof (IHn ltac:(lia)).
    assert (1 <= 2 ^ S n)%nat.
    { pose proof (Nat.pow_nonzero 2 (S n) ltac:(lia)). lia. }
    lia.
Qed.

Lemma nat_to_binary_string_aux_to_binary : forall fuel n,
  (0 < n)%nat -> (n < Nat.pow 2 fuel)%nat ->
  nat_to_binary_string_aux n fuel = to_binary (Z.of_nat n).
Proof.
  induction fuel; intros n Hn Hbound.
  - simpl in Hbound. lia.
  - destruct n as [|[|n']]; try lia.
    + reflexivity.
    + simpl nat_to_binary_string_aux.
      destruct (Z.of_nat (S (S n'))) as [|p|p] eqn:HZ; [lia| |lia].
      destruct p.
      * change (Nat.even n') with (Nat.even (S (S n'))).
        rewrite (even_xI (S (S n')) p HZ).
        rewrite divmod_100.
        rewrite (div_odd_same n').
        2:{ change (Nat.even n') with (Nat.even (S (S n'))).
            apply even_xI with (p := p); exact HZ. }
        rewrite IHfuel.
        -- rewrite (div_xI (S (S n')) p HZ). reflexivity.
        -- apply Nat.div_str_pos. lia.
        -- apply Nat.div_lt_upper_bound; [lia |].
           replace (2 ^ S fuel)%nat with (2 * 2 ^ fuel)%nat in Hbound
             by (simpl; lia).
           lia.
      * change (Nat.even n') with (Nat.even (S (S n'))).
        rewrite (even_xO (S (S n')) p HZ).
        rewrite divmod_111.
        rewrite IHfuel.
        -- rewrite (div_xO (S (S n')) p HZ). reflexivity.
        -- apply Nat.div_str_pos. lia.
        -- apply Nat.div_lt_upper_bound; [lia |].
           replace (2 ^ S fuel)%nat with (2 * 2 ^ fuel)%nat in Hbound
             by (simpl; lia).
           lia.
      * simpl in HZ. lia.
Qed.

Lemma nat_to_binary_string_to_binary : forall n,
  nat_to_binary_string n = to_binary (Z.of_nat n).
Proof.
  intros n.
  destruct n.
  - reflexivity.
  - unfold nat_to_binary_string.
    apply nat_to_binary_string_aux_to_binary.
    + lia.
    + apply nat_lt_pow2_self. lia.
Qed.

Local Open Scope Z_scope.

Lemma string_of_list_z_decorated_binary : forall decimal,
  0 <= decimal ->
  string_of_list_z (decorated_binary_digits_z decimal) =
  ("db" ++ to_binary decimal ++ "db")%string.
Proof.
  intros decimal Hdecimal.
  unfold decorated_binary_digits_z, binary_digits_z.
  repeat rewrite string_of_list_z_app.
  rewrite string_of_list_z_db.
  rewrite base_digits_z_two_to_binary by lia.
  reflexivity.
Qed.

Lemma problem_79_spec_z_intro : forall decimal out_l,
  0 <= decimal ->
  out_l = decorated_binary_digits_z decimal ->
  problem_79_spec_z decimal out_l.
Proof.
  intros decimal out_l Hdecimal Hout.
  subst out_l.
  unfold problem_79_spec_z, problem_79_spec, decimal_to_binary_impl.
  rewrite string_of_list_z_decorated_binary by lia.
  rewrite nat_to_binary_string_to_binary.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma decorated_binary_digits_z_zero :
  decorated_binary_digits_z 0 = [100; 98; 48; 100; 98].
Proof.
  unfold decorated_binary_digits_z, binary_digits_z.
  rewrite base_digits_z_zero by lia.
  reflexivity.
Qed.

Lemma problem_79_spec_z_zero :
  problem_79_spec_z 0 [100; 98; 48; 100; 98].
Proof.
  apply problem_79_spec_z_intro.
  - lia.
  - rewrite decorated_binary_digits_z_zero. reflexivity.
Qed.

Lemma decimal_binary_full_state_init : forall orig,
  0 < orig ->
  decimal_binary_full_state_z orig orig (Zlength (binary_digits_z orig))
    ([100; 98] ++ repeat_Z 0 (Zlength (binary_digits_z orig)) ++ [100; 98]).
Proof.
  intros orig Horig.
  exists (repeat_Z 0 (Zlength (binary_digits_z orig))).
  split.
  - apply binary_fill_full_state_init. lia.
  - reflexivity.
Qed.

Lemma decimal_binary_full_state_step : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  decimal_binary_full_state_z orig x (digits + 1) out_l ->
  decimal_binary_full_state_z orig (x / 2) digits
    (replace_Znth (digits + 2) (signed_last_nbits (48 + x mod 2) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits
    [payload [Hpayload Hout]].
  exists (replace_Znth digits (signed_last_nbits (48 + x mod 2) 8) payload).
  split.
  - apply binary_fill_full_state_step; lia || exact Hpayload.
  - rewrite Hout.
    destruct Hpayload as [suffix [[_ [_ [_ Hsplit]]] Hpayload_eq]].
    rewrite replace_Znth_app_r.
    2:{ rewrite Zlength_cons, Zlength_cons, Zlength_nil. lia. }
    replace (replace_Znth (digits + 2)
      (signed_last_nbits (48 + x mod 2) 8) [100; 98]) with [100; 98].
    2:{
      unfold replace_Znth.
      replace (Z.to_nat (digits + 2)) with (S (S (Z.to_nat digits))) by lia.
      simpl.
      destruct (Z.to_nat digits);
      reflexivity.
    }
    replace (digits + 2 - Zlength [100; 98]) with digits
      by (rewrite Zlength_cons, Zlength_cons, Zlength_nil; lia).
    rewrite replace_Znth_app_l by
      (try lia;
       rewrite Hpayload_eq;
       rewrite Zlength_app;
       rewrite Zlength_repeat_Z by lia;
       pose proof (Zlength_nonneg suffix);
       lia).
    reflexivity.
Qed.

Lemma decimal_binary_full_state_positive_digits : forall orig x digits out_l,
  0 < x ->
  decimal_binary_full_state_z orig x digits out_l ->
  1 <= digits.
Proof.
  intros orig x digits out_l Hx [payload [Hpayload _]].
  apply (base_fill_full_state_positive_digits orig 2 x digits payload);
    lia || exact Hpayload.
Qed.

Lemma decimal_binary_full_state_done : forall orig out_l,
  0 <= orig ->
  decimal_binary_full_state_z orig 0 0 out_l ->
  out_l = decorated_binary_digits_z orig.
Proof.
  intros orig out_l Horig [payload [Hpayload Hout]].
  pose proof (binary_fill_full_state_done orig payload Hpayload) as Hpayload_done.
  subst payload.
  unfold decorated_binary_digits_z.
  exact Hout.
Qed.
