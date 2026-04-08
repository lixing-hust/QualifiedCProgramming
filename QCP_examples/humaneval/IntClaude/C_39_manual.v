Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import C_39_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_39.
Local Open Scope sac.

Lemma proof_of_prime_fib_safety_wit_5 : prime_fib_safety_wit_5.
Proof.
  unfold prime_fib_safety_wit_5.
  intros.
  Intros.
  match goal with
  | H : pf_state _ _ _ |- _ =>
      pose proof (pf_state_sum_bound _ _ _ H)
  end.
  entailer!.
Qed.

Lemma proof_of_prime_fib_safety_wit_8 : prime_fib_safety_wit_8.
Proof.
  unfold prime_fib_safety_wit_8.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_prime_fib_entail_wit_1 : prime_fib_entail_wit_1.
Proof.
  unfold prime_fib_entail_wit_1.
  intros.
  Intros.
  entailer!.
  apply pf_state_init.
Qed.

Lemma proof_of_prime_fib_entail_wit_2 : prime_fib_entail_wit_2.
Proof.
  unfold prime_fib_entail_wit_2.
  intros.
  Intros.
  match goal with
  | H : pf_state _ _ _ |- _ =>
      pose proof (pf_state_bounds _ _ _ H);
      pose proof (pf_state_sum_bound _ _ _ H)
  end.
  entailer!.
Qed.

Lemma proof_of_prime_fib_entail_wit_3 : prime_fib_entail_wit_3.
Proof.
  unfold prime_fib_entail_wit_3.
  intros.
  Intros.
  entailer!.
  intros Hnz k Hk.
  assert (k < w \/ k = w) by lia.
  destruct H17 as [Hlt | ->].
  - apply (H9 Hnz k). lia.
  - exact H.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_1 : prime_fib_entail_wit_4_1.
Proof.
  unfold prime_fib_entail_wit_4_1.
  intros.
  Intros.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - eapply (pf_state_prime_step count f1 f2 n_pre w); eauto.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_2 : prime_fib_entail_wit_4_2.
Proof.
  unfold prime_fib_entail_wit_4_2.
  intros.
  Intros.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - eapply (pf_state_nonprime_step count f1 f2); eauto.
    + intro Heq. subst f1. exfalso.
      pose proof (prime_candidate_mod_nonzero 2 w H4 H1 (or_introl eq_refl)).
      contradiction.
    + intro Heq. subst f1. exfalso.
      pose proof (prime_candidate_mod_nonzero 3 w H4 H1 (or_intror (or_introl eq_refl))).
      contradiction.
    + intro Heq. subst f1. exfalso.
      pose proof (prime_candidate_mod_nonzero 5 w H4 H1 (or_intror (or_intror (or_introl eq_refl)))).
      contradiction.
    + intro Heq. subst f1. exfalso.
      pose proof (prime_candidate_mod_nonzero 13 w H4 H1 (or_intror (or_intror (or_intror (or_introl eq_refl))))).
      contradiction.
    + intro Heq. subst f1. exfalso.
      pose proof (prime_candidate_mod_nonzero 89 w H4 H1 (or_intror (or_intror (or_intror (or_intror eq_refl))))).
      contradiction.
Qed.

Lemma proof_of_prime_fib_entail_wit_4_3 : prime_fib_entail_wit_4_3.
Proof.
  unfold prime_fib_entail_wit_4_3.
  intros.
  Intros.
  entailer!.
  - sep_apply store_int_undef_store_int.
    entailer!.
  - pose proof (H8 H17) as Hnz.
    destruct Hnz as [[[[Hneq2 Hneq3] Hneq5] Hneq13] Hneq89].
    eapply (pf_state_nonprime_step count f1 f2); eauto.
Qed.

Lemma proof_of_prime_fib_return_wit_1 : prime_fib_return_wit_1.
Proof.
  unfold prime_fib_return_wit_1.
  intros.
  Intros.
  entailer!.
  match goal with
  | Hst : pf_state ?count ?f1 ?f2,
    Hall : (_ -> forall kk, _),
    Hnz : ?isprime <> 0,
    Hw : 2 <= ?w,
    Hexit : ?w * ?w > ?f1,
    Hcount : ?count < ?n,
    Hn : ?n <= 5,
    Heq : ?count + 1 = ?n |- _ =>
      eapply (pf_state_prime_return count f1 f2 n w); eauto;
      intros; apply (Hall Hnz); auto
  end.
Qed.
