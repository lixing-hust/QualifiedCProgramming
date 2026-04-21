Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications.alpha_equiv Require Import alpha_equiv_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_democases Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From SimpleC.EE.Applications.alpha_equiv Require Import ast_lib.
From SimpleC.EE.Applications Require Import malloc.
From SimpleC.EE.Applications Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_alpha_equiv_safety_wit_16 : alpha_equiv_safety_wit_16.
Proof. 
  pre_process.
  unfold termtypeID in *.
  destruct term1; lia.
Qed.

Lemma proof_of_alpha_equiv_return_wit_15 : alpha_equiv_return_wit_15.
Proof. 
  pre_process.
  rewrite H.
  apply store_null_right.
Qed.

Lemma proof_of_alpha_equiv_return_wit_14 : alpha_equiv_return_wit_14.
Proof.
  pre_process.
  rewrite H.
  apply store_null_left.
Qed.

Lemma proof_of_alpha_equiv_return_wit_13 : alpha_equiv_return_wit_13.
Proof.
  pre_process.
  entailer!.
  2: {
    destruct term1; destruct term2; simpl in H; try lia.
    all: unfold term_alpha_eqn, term_alpha_eq; reflexivity.
  }
  pose proof (store_term_fold_out t2_pre term2) H1.
  sep_apply H4.
  pose proof (store_term_fold_out t1_pre term1) H0.
  sep_apply H5.
  entailer!.
Qed.

Lemma proof_of_alpha_equiv_return_wit_12 : alpha_equiv_return_wit_12.
Proof.
  pre_process.
  unfold list_Z_cmp in H0.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ contradiction | ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite H3, H4.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_11 : alpha_equiv_return_wit_11.
Proof.
  pre_process.
  rewrite H in H0.
  unfold list_Z_cmp in H0.
  destruct (list_Z_eqb str1 str2) eqn:Heq; [ | discriminate ].
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite H3, H4.
  Exists y z.
  entailer!.
  rewrite Heq.
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_10 : alpha_equiv_return_wit_10.
Proof.
  pre_process.
  unfold store_term, term_alpha_eqn, term_alpha_eq.
  rewrite H2, H3.
  entailer!.
  destruct (ctID typ1 =? ctID typ2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    contradiction.
  + reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_9 : alpha_equiv_return_wit_9.
Proof. 
  pre_process.
  unfold store_term.
  rewrite H4, H5.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite H1 at 1.
  rewrite Z.eqb_refl.
  destruct (con1 =? con2)%Z eqn:E.
  + apply Z.eqb_eq in E.
    contradiction.
  + unfold negb.
    rewrite H0.
    reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_8 : alpha_equiv_return_wit_8.
Proof.
  pre_process.
  unfold store_term.
  rewrite H4, H5.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite H1 at 1.
  rewrite Z.eqb_refl.
  destruct (con1 =? con2)%Z eqn:E.
  + unfold negb.
    rewrite H0.
    reflexivity. 
  + apply Z.eqb_neq in E.
    contradiction.
Qed.

Lemma proof_of_alpha_equiv_return_wit_7 : alpha_equiv_return_wit_7.
Proof.
  pre_process.
  unfold store_term.
  rewrite H3, H4.
  entailer!.
  unfold term_alpha_eqn, term_alpha_eq.
  rewrite H0 at 1.
  rewrite Z.eqb_refl.
  destruct (con1 =? con2)%Z eqn:E.
  + unfold negb.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in E, Eq.
    contradiction.
  + unfold negb.
    apply Z.eqb_neq in E.
    destruct (ctID typ1 =? 0)%Z eqn:Eq; [ | reflexivity].
    apply Z.eqb_eq in Eq.
    contradiction.
Qed.  

Lemma proof_of_alpha_equiv_return_wit_6 : alpha_equiv_return_wit_6.
Proof.
  pre_process.
  unfold store_term.
  rewrite H3, H4.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | reflexivity].
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_5 : alpha_equiv_return_wit_5.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | contradiction].
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | contradiction].
  reflexivity.
Qed.

Lemma proof_of_alpha_equiv_return_wit_4 : alpha_equiv_return_wit_4.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (term_alpha_eq lt1 lt2) eqn:Eql; [ | contradiction].
  destruct (term_alpha_eq rt1 rt2) eqn:Eqr; [ | reflexivity].
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_3 : alpha_equiv_return_wit_3.
Proof.
  pre_process.
  unfold store_term.
  rewrite H2, H3.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq; [ | reflexivity].
  apply Z.eqb_eq in Eq.
  congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_2 : alpha_equiv_return_wit_2.
Proof.
  pre_process.
  unfold store_term.
  rewrite H5, H6.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  rewrite H0 in H1. 
  unfold list_Z_cmp in H1.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    pose proof list_Z_eqb2eq qv1 qv2 vEq as vvEq.
    pose proof (term_subst_v_same_name qv1 qv2 qterm2 vvEq) as qtEq.
    rewrite qtEq.
    tauto.
  + destruct (list_Z_eqb qv1 qv2) eqn:vEq; [ | congruence].
    rewrite Z.eqb_neq in Eq.
    congruence.
Qed.

Lemma proof_of_alpha_equiv_return_wit_1 : alpha_equiv_return_wit_1.
Proof.
  pre_process.
  unfold store_term.
  rewrite H9, H10.
  fold store_term.
  Exists y1 z1 y2 z2.
  entailer!.  
  unfold term_alpha_eqn in *.
  unfold term_alpha_eq.
  fold term_alpha_eq.
  destruct (qtID qt1 =? qtID qt2)%Z eqn:Eq.
  + auto.
  + rewrite Z.eqb_neq in Eq.
    congruence.
Qed.


Lemma proof_of_alpha_equiv_which_implies_wit_1 : alpha_equiv_which_implies_wit_1.
Proof. 
  pre_process.
  sep_apply store_term_unfold.
  sep_apply store_term_unfold.
  unfold NULL.
  entailer!.
Qed.
   
Lemma proof_of_alpha_equiv_which_implies_wit_2 : alpha_equiv_which_implies_wit_2.
Proof. 
  pre_process.
  sep_apply store_term'_Var; unfold NULL.
  Intros v1 y1.
  sep_apply store_term'_Var; unfold NULL.
  Intros v2 y2.
  Exists y2 y1 v2 v1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed.  

Lemma proof_of_alpha_equiv_which_implies_wit_3 : alpha_equiv_which_implies_wit_3.
Proof. 
  pre_process. 
  sep_apply store_term'_Const; unfold NULL.
  Intros ty1 c1.
  sep_apply store_term'_Const; unfold NULL.
  Intros ty2 c2.
  Exists ty2 c2 ty1 c1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_4 : alpha_equiv_which_implies_wit_4.
Proof. 
  pre_process.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt1 rtt1 yy1 zz1.
  sep_apply store_term'_Apply; unfold NULL.
  Intros ltt2 rtt2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists ltt2 rtt2 ltt1 rtt1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_5 : alpha_equiv_which_implies_wit_5.
Proof.  
  pre_process.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt1 qvv1 bb1 yy1 zz1.
  sep_apply store_term'_Quant; unfold NULL.
  Intros qtt2 qvv2 bb2 yy2 zz2.
  Exists zz2 zz1 yy2 yy1.
  Exists qtt2 qvv2 bb2.
  Exists qtt1 qvv1 bb1.
  entailer!.
  + auto.
  + rewrite <- H2; auto.
  + auto.
  + auto.
Qed. 

Lemma proof_of_alpha_equiv_which_implies_wit_6 : alpha_equiv_which_implies_wit_6.
Proof. 
  pre_process.
  unfold store_string.
  unfold NULL.
  Intros x n.
  Exists x n.
  entailer!.
Qed. 