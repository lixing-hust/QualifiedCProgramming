Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import C_10_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import coins_10.
Local Open Scope sac.

Lemma proof_of_is_pal_suffix_entail_wit_2 : is_pal_suffix_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k (i - start_pre)).
  - apply H12; lia.
  - assert (k = i - start_pre) by lia.
    subst k.
    match goal with
    | Heq : Znth i (app l (cons 0 nil)) 0 =
            Znth j (app l (cons 0 nil)) 0 |- _ =>
        rewrite app_Znth1 in Heq by lia;
        rewrite app_Znth1 in Heq by lia;
        replace (start_pre + (i - start_pre)) with i by lia;
        replace (n_pre - 1 - (i - start_pre)) with j by lia;
        exact Heq
    end.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_1 : is_pal_suffix_return_wit_1.
Proof.
  pre_process.
  Right.
  entailer!.
  unfold pal_suffix_z.
  split.
  - lia.
  - intros k Hk Hmirror.
    rewrite H4.
    apply H11; lia.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_2 : is_pal_suffix_return_wit_2.
Proof.
  pre_process.
  Left.
  entailer!.
  unfold pal_suffix_z.
  intros [_ Hpal].
  match goal with
  | Hneq : Znth i (app l (cons 0 nil)) 0 <>
           Znth j (app l (cons 0 nil)) 0 |- _ =>
      apply Hneq;
      repeat rewrite app_Znth1 by lia;
      specialize (Hpal (i - start_pre));
      replace (start_pre + (i - start_pre)) with i in Hpal by lia;
      replace (Zlength l - 1 - (i - start_pre)) with j in Hpal by lia;
      apply Hpal; lia
  end.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_3 : is_pal_suffix_return_wit_3.
Proof.
  pre_process.
  Right.
  entailer!.
  unfold pal_suffix_z.
  split.
  - lia.
  - intros k Hk _.
    lia.
Qed. 

Lemma proof_of_make_palindrome_safety_wit_14 : make_palindrome_safety_wit_14.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_make_palindrome_safety_wit_16 : make_palindrome_safety_wit_16.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_make_palindrome_safety_wit_18 : make_palindrome_safety_wit_18.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_make_palindrome_entail_wit_3_1 : make_palindrome_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hlen0 : len = 0).
  {
    destruct (Z_lt_ge_dec 0 len) as [Hpos | Hzero]; [exfalso | lia].
    match goal with
    | Hnone : forall t : Z, 0 <= t /\ t < i -> ~ pal_suffix_z t l |- _ =>
        apply (Hnone (len - 1)); [lia | idtac]
    end.
    replace (len - 1) with (Zlength l - 1) by lia.
    apply pal_suffix_last_10.
    lia.
  }
  subst len.
  subst best.
  Exists (@nil Z).
  rewrite Hlen0.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 ((0 + 0) + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - rewrite (CharArray.undef_seg_empty retval 0).
    entailer!.
  - apply first_pal_suffix_empty_10.
    lia.
Qed. 

Lemma proof_of_make_palindrome_entail_wit_3_2 : make_palindrome_entail_wit_3_2.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 ((len + best) + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - rewrite (CharArray.undef_seg_empty retval 0).
    entailer!.
  - change (Z.quot 2147483647 2) with 1073741823 in *; lia.
  - unfold first_pal_suffix_z.
    split.
    + lia.
    + split; [exact H14 | exact H15].
Qed. 

Lemma proof_of_make_palindrome_entail_wit_4 : make_palindrome_entail_wit_4.
Proof.
  pre_process.
  Exists (app out_l_2 (cons (Znth i (app l (cons 0 nil)) 0) nil)).
  entailer!.
  - intros p Hp.
    destruct (Z_lt_ge_dec p i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hprefix : forall p : Z, 0 <= p < i -> _ |- _ =>
          apply Hprefix; lia
      end.
    + assert (p = i) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_make_palindrome_entail_wit_5 : make_palindrome_entail_wit_5.
Proof.
  pre_process.
  assert (Hi_len : i = len) by lia.
  subst i.
  Exists out_l_2.
  entailer!.
  - replace (len + 0) with (Zlength out_l_2) by lia.
    entailer!.
  - intros p Hp.
    apply H16; lia.
Qed. 

Lemma proof_of_make_palindrome_entail_wit_6 : make_palindrome_entail_wit_6.
Proof.
  pre_process.
  Exists (app out_l_2 (cons (Znth (best - 1 - k) (app l (cons 0 nil)) 0) nil)).
  entailer!.
  - replace (len + (k + 1)) with (len + k + 1) by lia.
    entailer!.
  - intros p Hp.
    destruct (Z_lt_ge_dec p k) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hsuffix : forall p : Z, 0 <= p < k -> _ |- _ =>
          apply Hsuffix; lia
      end.
    + assert (p = k) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (len + k - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      reflexivity.
  - intros p Hp.
    rewrite app_Znth1 by lia.
    match goal with
    | Hprefix : forall p : Z, 0 <= p < len -> _ |- _ =>
        apply Hprefix; lia
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_make_palindrome_entail_wit_7 : make_palindrome_entail_wit_7.
Proof.
  pre_process.
  assert (Hkbest : k = best) by lia.
  subst k.
  assert (Hout_eq : out_l_2 = make_pal_output_z best l).
  {
    eapply make_pal_output_z_ext_10; eauto; try lia.
  }
  Exists (make_pal_output_z best l).
  entailer!.
  - rewrite <- Hout_eq.
    rewrite H11.
    rewrite (CharArray.undef_seg_empty out (len + best + 1)).
    entailer!.
  - apply problem_10_spec_z_make_pal_output_10; assumption.
  - rewrite Zlength_make_pal_output_z_10; lia.
Qed. 

Lemma proof_of_make_palindrome_return_wit_1 : make_palindrome_return_wit_1.
Proof.
  pre_process.
  Exists out_l_2.
  entailer!.
  match goal with
  | Hlen : out_len = Zlength out_l_2 |- _ => rewrite Hlen
  end.
  entailer!.
Qed. 

Lemma proof_of_make_palindrome_partial_solve_wit_2_pure : make_palindrome_partial_solve_wit_2_pure.
Proof.
  pre_process.
  entailer!.
  change (Z.quot 2147483647 2) with 1073741823 in *.
  lia.
Qed. 
