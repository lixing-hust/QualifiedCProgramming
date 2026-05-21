Load "../spec/48".

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

Definition problem_48_pre_z (input : list Z) : Prop :=
  problem_48_pre (string_of_list_z input).

Definition palindrome_z (input : list Z) : Prop :=
  forall k,
    0 <= k < Zlength input ->
    k < Zlength input - 1 - k ->
    Znth k input 0 = Znth (Zlength input - 1 - k) input 0.

Definition problem_48_spec_z (input : list Z) (output : Z) : Prop :=
  problem_48_spec (string_of_list_z input) (bool_of_z output).

Lemma ascii_of_z_inj_range : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of_z a = ascii_of_z b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  repeat rewrite nat_of_ascii_ascii_of_z in Heq by lia.
  lia.
Qed.

Lemma half_index_mirror_z : forall len i,
  (i < len / 2)%nat ->
  Z.of_nat i < Z.of_nat len - 1 - Z.of_nat i.
Proof.
  intros len i Hi.
  assert (S i <= len / 2)%nat by lia.
  pose proof (Nat.Div0.mul_div_le len 2) as Hmul.
  assert (2 * S i <= len)%nat by nia.
  lia.
Qed.

Lemma mirror_index_half_nat : forall len k,
  0 <= k ->
  k < Z.of_nat len - 1 - k ->
  (Z.to_nat k < len / 2)%nat.
Proof.
  intros len k Hk Hmirror.
  assert (2 * S (Z.to_nat k) <= len)%nat by lia.
  apply Nat.div_le_lower_bound; lia.
Qed.

Lemma palindrome_z_to_problem_48_true : forall input,
  palindrome_z input ->
  problem_48_spec (string_of_list_z input) true.
Proof.
  intros input Hpal.
  unfold problem_48_spec.
  split.
  - intros _ i Hi.
    pose proof (half_index_mirror_z (String.length (string_of_list_z input)) i Hi) as Hmirror.
    rewrite string_of_list_z_length_z in Hmirror.
    assert (Hk : 0 <= Z.of_nat i < Zlength input) by lia.
    replace (String.get i (string_of_list_z input)) with
      (String.get (Z.to_nat (Z.of_nat i)) (string_of_list_z input))
      by now rewrite Nat2Z.id.
    replace (String.length (string_of_list_z input) - 1 - i)%nat with
      (Z.to_nat (Zlength input - 1 - Z.of_nat i)).
    + rewrite (string_get_string_of_list_z_z input (Z.of_nat i) Hk).
      rewrite (string_get_string_of_list_z_z input (Zlength input - 1 - Z.of_nat i)).
      * rewrite Hpal by lia. reflexivity.
      * lia.
    + rewrite string_of_list_z_length.
      rewrite Zlength_correct.
      lia.
  - intros _. reflexivity.
Qed.

Lemma problem_48_property_to_palindrome_z : forall input,
  ascii_range_z input ->
  (forall i : nat,
    (i < String.length (string_of_list_z input) / 2)%nat ->
    String.get i (string_of_list_z input) =
    String.get (String.length (string_of_list_z input) - 1 - i) (string_of_list_z input)) ->
  palindrome_z input.
Proof.
  intros input Hrange Hprop.
  unfold palindrome_z.
  intros k Hk Hmirror.
  pose proof (mirror_index_half_nat (String.length (string_of_list_z input)) k ltac:(lia)) as Hhalf.
  rewrite string_of_list_z_length_z in Hhalf.
  specialize (Hhalf Hmirror).
  specialize (Hprop (Z.to_nat k) Hhalf).
  replace (String.length (string_of_list_z input) - 1 - Z.to_nat k)%nat with
    (Z.to_nat (Zlength input - 1 - k)) in Hprop.
  2:{
    rewrite string_of_list_z_length.
    rewrite Zlength_correct.
    lia.
  }
  rewrite (string_get_string_of_list_z_z input k Hk) in Hprop.
  rewrite (string_get_string_of_list_z_z input (Zlength input - 1 - k)) in Hprop by lia.
  inversion Hprop as [Heq].
  apply ascii_of_z_inj_range.
  - apply Hrange. lia.
  - apply Hrange. lia.
  - exact Heq.
Qed.

Lemma problem_48_spec_z_empty :
  forall input,
    Zlength input = 0 ->
    problem_48_spec_z input 1.
Proof.
  intros input Hlen.
  unfold problem_48_spec_z, problem_48_spec, bool_of_z.
  simpl.
  split.
  - intros _ i Hi.
    pose proof (string_of_list_z_length_z input) as Hslen.
    rewrite Hlen in Hslen.
    assert (String.length (string_of_list_z input) = 0)%nat by lia.
    rewrite H in Hi.
    simpl in Hi.
    lia.
  - intros _. reflexivity.
Qed.

Lemma problem_48_spec_z_true :
  forall input n i j,
    Zlength input = n ->
    0 <= i ->
    0 <= j ->
    i >= j ->
    i + j = n - 1 ->
    (forall k, 0 <= k < i -> Znth k input 0 = Znth (n - 1 - k) input 0) ->
    problem_48_spec_z input 1.
Proof.
  intros input n i j Hlen Hi Hj Hexit Hsum Hchecked.
  assert (Hpal : palindrome_z input).
  {
    unfold palindrome_z.
    intros k Hk Hmirror.
    rewrite Hlen in Hmirror.
    rewrite Hlen.
    apply Hchecked.
    lia.
  }
  unfold problem_48_spec_z.
  apply palindrome_z_to_problem_48_true.
  exact Hpal.
Qed.

Lemma problem_48_spec_z_false :
  forall input n i j,
    ascii_range_z input ->
    Zlength input = n ->
    0 <= i ->
    i < j ->
    i + j = n - 1 ->
    Znth i input 0 <> Znth j input 0 ->
    problem_48_spec_z input 0.
Proof.
  intros input n i j Hrange Hlen Hi Hij Hsum Hneq.
  assert (Hnotpal : ~ palindrome_z input).
  {
    unfold palindrome_z.
    intros Hpal.
    specialize (Hpal i).
    rewrite Hlen in Hpal.
    assert (Hbounds : 0 <= i < n) by lia.
    assert (Hmirror : i < n - 1 - i) by lia.
    specialize (Hpal Hbounds Hmirror).
    replace (n - 1 - i) with j in Hpal by lia.
    contradiction.
  }
  unfold problem_48_spec_z, problem_48_spec, bool_of_z.
  simpl.
  split; intros Hbad.
  - discriminate.
  - exfalso. apply Hnotpal.
    apply problem_48_property_to_palindrome_z; assumption.
Qed.
