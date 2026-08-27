Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import SeparationLogic.
From Flocq.Core Require Import Raux.

Load "../spec/92".

(* Trusted standard-library boundary: this records only the generic fixed-point
   property of roundf that is observed by C_92.  The implementation of roundf
   itself is outside this verification. *)
Definition roundf_fixed_bits_92 (input_bits result_bits : Z) : Prop :=
  fp32_isFinite (fp32_of_bits input_bits) /\
  fp32_isFinite (fp32_of_bits result_bits) /\
  (fp32_eq (fp32_of_bits result_bits) (fp32_of_bits input_bits) <->
   fp32_is_integer_92 (fp32_of_bits input_bits)).

Lemma fp32_eq_to_R_92 :
  forall x y,
    fp32_isFinite x ->
    fp32_isFinite y ->
    fp32_eq x y ->
    fp32_to_R_total x = fp32_to_R_total y.
Proof.
  intros x y Hx Hy Heq.
  unfold fp32_eq, fp32_compare in Heq.
  rewrite Binary.Bcompare_correct in Heq; try assumption.
  inversion Heq.
  now apply Rcompare_Eq_inv.
Qed.

Lemma fp32_eq_of_R_92 :
  forall x y,
    fp32_isFinite x ->
    fp32_isFinite y ->
    fp32_to_R_total x = fp32_to_R_total y ->
    fp32_eq x y.
Proof.
  intros x y Hx Hy Heq.
  unfold fp32_to_R_total in Heq.
  unfold fp32_eq, fp32_compare.
  rewrite Binary.Bcompare_correct; try assumption.
  rewrite Heq, Rcompare_Eq; reflexivity.
Qed.

Lemma fp32_eq_sym_92 :
  forall x y,
    fp32_isFinite x ->
    fp32_isFinite y ->
    fp32_eq x y ->
    fp32_eq y x.
Proof.
  intros x y Hx Hy Hxy.
  apply fp32_eq_of_R_92; try assumption.
  symmetry; now apply fp32_eq_to_R_92.
Qed.

Lemma fp32_eq_trans_92 :
  forall x y z,
    fp32_isFinite x ->
    fp32_isFinite y ->
    fp32_isFinite z ->
    fp32_eq x y ->
    fp32_eq y z ->
    fp32_eq x z.
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  apply fp32_eq_of_R_92; try assumption.
  transitivity (fp32_to_R_total y).
  - now apply fp32_eq_to_R_92.
  - now apply fp32_eq_to_R_92.
Qed.

Lemma fp32_is_integer_eq_92 :
  forall x y,
    fp32_isFinite x ->
    fp32_isFinite y ->
    fp32_eq x y ->
    (fp32_is_integer_92 x <-> fp32_is_integer_92 y).
Proof.
  intros x y Hx Hy Hxy.
  unfold fp32_is_integer_92.
  pose proof (fp32_eq_to_R_92 x y Hx Hy Hxy) as Hreal.
  split; intros [_ [z Hz]]; split; try assumption; exists z.
  - now rewrite <- Hreal.
  - now rewrite Hreal.
Qed.

Lemma roundf_observed_eq_integer_92 :
  forall input_bits result_bits input result,
    fp32_isFinite input ->
    fp32_isFinite result ->
    fp32_eq input (fp32_of_bits input_bits) ->
    fp32_eq result (fp32_of_bits result_bits) ->
    roundf_fixed_bits_92 input_bits result_bits ->
    fp32_eq result input ->
    fp32_is_integer_92 input.
Proof.
  intros input_bits result_bits input result Hinput Hresult
    Hinput_bits Hresult_bits Hround Hobserved.
  unfold roundf_fixed_bits_92 in Hround.
  destruct Hround as [Hinput_bits_finite [Hresult_bits_finite Hfixed]].
  apply (proj2 (fp32_is_integer_eq_92 input (fp32_of_bits input_bits)
    Hinput Hinput_bits_finite Hinput_bits)).
  apply Hfixed.
  assert (Hbits_result : fp32_eq (fp32_of_bits result_bits) result).
  { apply fp32_eq_sym_92; assumption. }
  assert (Hbits_input : fp32_eq (fp32_of_bits result_bits) input).
  { eapply fp32_eq_trans_92;
      [exact Hresult_bits_finite | exact Hresult | exact Hinput |
       exact Hbits_result | exact Hobserved]. }
  eapply fp32_eq_trans_92;
    [exact Hresult_bits_finite | exact Hinput | exact Hinput_bits_finite |
     exact Hbits_input | exact Hinput_bits].
Qed.

Lemma roundf_observed_ne_not_integer_92 :
  forall input_bits result_bits input result,
    fp32_isFinite input ->
    fp32_isFinite result ->
    fp32_eq input (fp32_of_bits input_bits) ->
    fp32_eq result (fp32_of_bits result_bits) ->
    roundf_fixed_bits_92 input_bits result_bits ->
    fp32_ne result input ->
    ~ fp32_is_integer_92 input.
Proof.
  intros input_bits result_bits input result Hinput Hresult
    Hinput_bits Hresult_bits Hround Hne Hinteger.
  unfold fp32_ne in Hne.
  apply Hne.
  unfold roundf_fixed_bits_92 in Hround.
  destruct Hround as [Hinput_bits_finite [Hresult_bits_finite Hfixed]].
  assert (Hinteger_bits : fp32_is_integer_92 (fp32_of_bits input_bits)).
  { apply (proj1 (fp32_is_integer_eq_92 input (fp32_of_bits input_bits)
      Hinput Hinput_bits_finite Hinput_bits)); exact Hinteger. }
  assert (Hresult_input_bits : fp32_eq result (fp32_of_bits input_bits)).
  { eapply fp32_eq_trans_92;
      [exact Hresult | exact Hresult_bits_finite | exact Hinput_bits_finite |
       exact Hresult_bits | exact (proj2 Hfixed Hinteger_bits)]. }
  assert (Hinput_bits_input : fp32_eq (fp32_of_bits input_bits) input).
  { apply fp32_eq_sym_92; assumption. }
  eapply fp32_eq_trans_92;
    [exact Hresult | exact Hinput_bits_finite | exact Hinput |
     exact Hresult_input_bits | exact Hinput_bits_input].
Qed.
