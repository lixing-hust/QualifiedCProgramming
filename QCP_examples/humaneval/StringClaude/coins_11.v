Load "../spec/11".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.EE Require Export string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition problem_11_pre_z (a b : list Z) : Prop :=
  problem_11_pre (string_of_list_z a) (string_of_list_z b).

Definition problem_11_spec_z (a b output : list Z) : Prop :=
  problem_11_spec (string_of_list_z a) (string_of_list_z b) (string_of_list_z output).

Lemma ascii_of_z_inj_binary : forall a b,
  (a = 48 \/ a = 49) ->
  (b = 48 \/ b = 49) ->
  ascii_of_z a = ascii_of_z b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  destruct Ha as [-> | ->]; destruct Hb as [-> | ->];
    cbn in Heq; try reflexivity; discriminate.
Qed.

Lemma ascii_of_z_48 : ascii_of_z 48 = "0"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_49 : ascii_of_z 49 = "1"%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_eq_48_range : forall x,
  0 <= x < 256 ->
  ascii_of_z x = "0"%char ->
  x = 48.
Proof.
  intros x Hrange Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite nat_of_ascii_ascii_of_z in Heq by lia.
  cbn in Heq.
  lia.
Qed.

Lemma ascii_of_z_eq_49_range : forall x,
  0 <= x < 256 ->
  ascii_of_z x = "1"%char ->
  x = 49.
Proof.
  intros x Hrange Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite nat_of_ascii_ascii_of_z in Heq by lia.
  cbn in Heq.
  lia.
Qed.

Lemma problem_11_pre_z_left_binary : forall a b k,
  problem_11_pre_z a b ->
  ascii_range_z a ->
  0 <= k < Zlength a ->
  Znth k a 0 = 48 \/ Znth k a 0 = 49.
Proof.
  intros a b k Hpre Hrange Hk.
  unfold problem_11_pre_z, problem_11_pre in Hpre.
  destruct Hpre as [_ Hchars].
  specialize (Hchars (Z.to_nat k)).
  assert (Hi : (Z.to_nat k < String.length (string_of_list_z a))%nat).
  {
    rewrite string_of_list_z_length.
    rewrite <- z_to_nat_Zlength.
    lia.
  }
  specialize (Hchars Hi).
  destruct Hchars as [Ha _].
  rewrite (string_get_string_of_list_z_z a k Hk) in Ha.
  destruct Ha as [Ha | Ha]; inversion Ha as [Heq].
  - left. apply ascii_of_z_eq_48_range; [apply Hrange; lia | exact Heq].
  - right. apply ascii_of_z_eq_49_range; [apply Hrange; lia | exact Heq].
Qed.

Lemma problem_11_pre_z_right_binary : forall a b k,
  problem_11_pre_z a b ->
  ascii_range_z b ->
  0 <= k < Zlength b ->
  Znth k b 0 = 48 \/ Znth k b 0 = 49.
Proof.
  intros a b k Hpre Hrange Hk.
  unfold problem_11_pre_z, problem_11_pre in Hpre.
  destruct Hpre as [Hlen Hchars].
  assert (Hzlen : Zlength a = Zlength b).
  {
    rewrite <- !string_of_list_z_length_z.
    rewrite Hlen.
    reflexivity.
  }
  specialize (Hchars (Z.to_nat k)).
  assert (Hi : (Z.to_nat k < String.length (string_of_list_z a))%nat).
  {
    rewrite string_of_list_z_length.
    rewrite <- z_to_nat_Zlength.
    apply Z2Nat.inj_lt; lia.
  }
  specialize (Hchars Hi).
  destruct Hchars as [_ Hb].
  rewrite (string_get_string_of_list_z_z b k Hk) in Hb.
  destruct Hb as [Hb | Hb]; inversion Hb as [Heq].
  - left. apply ascii_of_z_eq_48_range; [apply Hrange; lia | exact Heq].
  - right. apply ascii_of_z_eq_49_range; [apply Hrange; lia | exact Heq].
Qed.

Lemma problem_11_spec_z_intro :
  forall a b output n,
    problem_11_pre_z a b ->
    ascii_range_z a ->
    ascii_range_z b ->
    Zlength a = n ->
    Zlength b = n ->
    Zlength output = n ->
    (forall k,
      0 <= k < n ->
      ((Znth k a 0 = Znth k b 0 /\ Znth k output 0 = 48) \/
       (Znth k a 0 <> Znth k b 0 /\ Znth k output 0 = 49))) ->
    problem_11_spec_z a b output.
Proof.
  intros a b output n Hpre Hrange_a Hrange_b Ha Hb Ho Hxor.
  unfold problem_11_spec_z.
  unfold problem_11_spec.
    split.
    + apply Nat2Z.inj.
      repeat rewrite string_of_list_z_length_z.
      lia.
    + split.
      * apply Nat2Z.inj.
        repeat rewrite string_of_list_z_length_z.
        lia.
      * intros i Hi.
        assert (Hiz : 0 <= Z.of_nat i < Zlength output).
        {
          split; [lia |].
          apply Nat2Z.inj_lt in Hi.
          repeat rewrite string_of_list_z_length in Hi.
          rewrite Zlength_correct.
          lia.
        }
        assert (Hia : 0 <= Z.of_nat i < Zlength a) by lia.
        assert (Hib : 0 <= Z.of_nat i < Zlength b) by lia.
        pose proof (problem_11_pre_z_left_binary a b (Z.of_nat i) Hpre Hrange_a Hia) as Ha_digit.
        pose proof (problem_11_pre_z_right_binary a b (Z.of_nat i) Hpre Hrange_b Hib) as Hb_digit.
        specialize (Hxor (Z.of_nat i)).
        rewrite <- Ho in Hxor.
        specialize (Hxor Hiz).
        replace (String.get i (string_of_list_z a)) with
          (String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z a))
          by now rewrite Nat2Z.id.
        replace (String.get i (string_of_list_z b)) with
          (String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z b))
          by now rewrite Nat2Z.id.
        replace (String.get i (string_of_list_z output)) with
          (String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z output))
          by now rewrite Nat2Z.id.
        rewrite (string_get_string_of_list_z_z a (Z.of_nat i) Hia).
        rewrite (string_get_string_of_list_z_z b (Z.of_nat i) Hib).
        rewrite (string_get_string_of_list_z_z output (Z.of_nat i) Hiz).
        destruct Hxor as [[Heq_z Hout] | [Hneq_z Hout]].
        -- split.
           ++ intros _. rewrite Hout, ascii_of_z_48. reflexivity.
           ++ intros Hneq_get. exfalso. apply Hneq_get.
              rewrite Heq_z. reflexivity.
        -- split.
           ++ intros Heq_get.
              exfalso. apply Hneq_z.
              inversion Heq_get as [Heq_ascii].
              apply ascii_of_z_inj_binary; assumption.
           ++ intros _. rewrite Hout, ascii_of_z_49. reflexivity.
Qed.
