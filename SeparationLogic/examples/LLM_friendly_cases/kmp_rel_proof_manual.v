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
From SimpleC.EE.LLM_friendly_cases Require Import kmp_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.


From SimpleC.EE.LLM_friendly_cases Require Import kmp_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Ltac kmp_solve :=
  repeat first
    [ split_pure_spatial
    | split_pures
    | apply derivable1_refl
    | dump_pre_spatial
    | progress subst
    | progress cbn in *
    | progress unfold applyf in *
    | lia
    | reflexivity
    | easy
    ].

Lemma proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Proof.
  pre_process.
  prop_apply CharArray.full_Zlength.
  prop_apply IntArray.full_Zlength.
  rewrite Zlength_app.
  replace (Zlength (0::nil)) with 1 by easy.
  pose proof H as H'.
  unfold inner_loop in H.
  unfold_loop in H.
  unfold inner_body at 1 in H.
  safe_step H.
  split_pure_spatial.
  - Intros_p H4.
    Intros_p H5.
    apply derivable1_refl.
  - split_pures.
    + Intros_p H6.
      Intros_p H7.
      dump_pre_spatial.
      lia.
    + Intros_p H6.
      Intros_p H7.
      dump_pre_spatial.
      lia.
    + Intros_p H6.
      Intros_p H7.
      dump_pre_spatial.
      exact H'.
    + Intros_p H6.
      Intros_p H7.
      dump_pre_spatial.
      lia.
    + Intros_p H6.
      Intros_p H7.
      dump_pre_spatial.
      lia.
Qed. 

Lemma proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Proof. 
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in *.
      unfold_loop in H3.
      unfold inner_body at 1 in H3.
      safe_step H3.
      rewrite app_Znth1 in H0 by auto.
      safe_choice_r H3.
      safe_choice_r H3; auto.
      unfold continue in H3.
      prog_nf in H3. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_inner_return_wit_2 : inner_return_wit_2.
Proof. 
  pre_process.
  split_pure_spatial.
  - apply derivable1_refl.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in H2.
      unfold_loop in H2.
      unfold inner_body at 1 in H2.
      repeat (prog_nf in H2 ; safe_step H2).
      rewrite app_Znth1 in H by lia.
      safe_choice_l H2; auto.
      unfold break in H2.
      prog_nf in H2. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_inner_return_wit_1 : inner_return_wit_1.
Proof. 
  pre_process.
  split_pure_spatial.
  - apply derivable1_refl.
  - split_pures.
    + dump_pre_spatial.
      unfold inner_loop in H3.
      unfold_loop in H3.
      unfold inner_body at 1 in H3.
      safe_step H3.
      rewrite app_Znth1 in H0 by lia.
      safe_choice_r H3.
      safe_choice_l H3.
      unfold break in H3.
      prog_nf in H3.
      auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Proof. 
  pre_process; subst.
  Exists (sublist 1 n_low_level_spec l) (0::nil).
  kmp_solve.
  prop_apply IntArray.full_Zlength; Intros.
  destruct l.
  rewrite Zlength_nil in H; lia.
  replace (z::l) with ((z::nil) ++ l) by easy.
  rewrite (replace_Znth_app_l 0 0); try lia.
  2:{ lazy; auto. }
  replace (replace_Znth 0 0 (z::nil)) with (0::nil) by easy.
  rewrite (IntArray.full_split_to_full retval 1 n_low_level_spec); try lia.
  rewrite sublist_split_app_l; [ | lia | easy].
  assert (Zlength (0::nil) = 1). 
  { lazy; auto. }
  rewrite sublist_self; eauto.
  replace ((0::nil) ++ l) with (0::l) by easy.
  replace ((z::nil) ++ l) with (z::l) by easy.
  rewrite replace_Znth_length in H.
  rewrite (sublist_cons2 1 n_low_level_spec); try lia.
  2:{
    rewrite Zlength_cons.
    rewrite Zlength_cons in H. lia. 
  }
  rewrite (sublist_cons2 1 n_low_level_spec); try lia.
  cancel.
  dump_pre_spatial.
  unfold constr_loop in H1.
  cbn in H1.
  unfold constr_loop_from.
  cbn.
  exact H0.
  dump_pre_spatial.
  lia.
  dump_pre_spatial.
  lia.
Qed. 

Lemma proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Proof. 
  pre_process.
  Exists (vnext0 ++ l0).
  prop_apply (IntArray.full_Zlength vnext).
  split_pure_spatial.
  - Intros_p Hz_spatial.
    rewrite (logic_equiv_sepcon_comm
      (IntArray.full vnext i vnext0)
      (CharArray.full patn_pre (n_low_level_spec + 1) (app str_low_level_spec (cons 0 nil)) **
       IntArray.full (vnext + i * sizeof ( INT )) (n_low_level_spec - i) l0)).
    cancel (CharArray.full patn_pre (n_low_level_spec + 1) (app str_low_level_spec (cons 0 nil))).
    sep_apply (IntArray.full_merge_to_full vnext i n_low_level_spec vnext0 l0).
    + apply derivable1_refl.
    + lia.
  - Intros_p Hz.
    split_pures.
    + dump_pre_spatial.
      exact H.
    + dump_pre_spatial.
      exact H3.
    + dump_pre_spatial.
      exact H4.
    + dump_pre_spatial.
      exact H2.
    + dump_pre_spatial.
      reflexivity.
    + dump_pre_spatial.
      exact Hz.
    + dump_pre_spatial.
      exact H0.
    + dump_pre_spatial.
      exact H1.
Qed. 

Lemma proof_of_constr_entail_wit_3 : constr_entail_wit_3.
Proof. 
  pre_process.
  unfold constr_loop_from_after in H0.
  destruct l0_2.
  - prop_apply (IntArray.full_Zlength vnext).
    Intros.
    rewrite H3 in H7.
    rewrite replace_Znth_length in H7.
    rewrite Zlength_app, Zlength_nil in H7.
    lia.
  - subst l.
    Exists l0_2 (vnext0_2 ++ (j :: nil)).
    rewrite (replace_Znth_app_r i j vnext0_2 (z :: l0_2)) by (rewrite H4; lia).
    rewrite replace_Znth_nothing by (rewrite H4; lia).
    replace (i - Zlength vnext0_2) with 0 by lia.
    cbn.
    split_pure_spatial.
    + cancel (CharArray.full patn_pre (n_low_level_spec + 1) (app str_low_level_spec (cons 0 nil))).
      prop_apply (IntArray.full_Zlength vnext).
      Intros_p Hlen.
      replace (vnext0_2 ++ j :: l0_2) with ((vnext0_2 ++ (j :: nil)) ++ l0_2) in Hlen by (rewrite <- app_assoc; reflexivity).
      replace (vnext0_2 ++ j :: l0_2) with ((vnext0_2 ++ (j :: nil)) ++ l0_2) by (rewrite <- app_assoc; reflexivity).
      rewrite (IntArray.full_split_to_full vnext (i + 1) n_low_level_spec) by lia.
      assert (Hzj: Zlength (vnext0_2 ++ (j :: nil)) = i + 1) by (rewrite Zlength_app; cbn; lia).
      assert (Hprefix: sublist 0 (i + 1) (((vnext0_2 ++ (j :: nil)) ++ l0_2)) = (vnext0_2 ++ (j :: nil))).
      {
        rewrite sublist_split_app_l.
        - rewrite sublist_self.
          + reflexivity.
          + symmetry; exact Hzj.
        - lia.
        - lia. 
      }
      assert (Hsuffix: sublist (i + 1) n_low_level_spec (((vnext0_2 ++ (j :: nil)) ++ l0_2)) = l0_2).
      {
        rewrite sublist_split_app_r with (len := Zlength (vnext0_2 ++ (j :: nil))).
        - replace (i + 1 - Zlength (vnext0_2 ++ (j :: nil))) with 0 by (rewrite Hzj; lia).
          rewrite (sublist_self l0_2 (n_low_level_spec - Zlength (vnext0_2 ++ (j :: nil)))).
          + reflexivity.
          + rewrite Zlength_app in Hlen. cbn in Hlen. lia.
        - lia.
        - rewrite Hzj. lia.
      }
      rewrite Hprefix, Hsuffix.
      apply derivable1_refl.
    + split_pures.
      * dump_pre_spatial.
        exact H.
      * dump_pre_spatial.
        lia.
      * dump_pre_spatial.
        lia.
Qed. 

Lemma proof_of_constr_return_wit_1 : constr_return_wit_1.
Proof. 
  pre_process.
  prop_apply (IntArray.full_length (vnext_2 + i * sizeof ( INT ))); Intros.
  assert (i = n_low_level_spec) by lia; subst i; clear H3.
  prop_apply CharArray.full_Zlength.
  Intros_p Hstr.
  Exists vnext0.
  prop_apply (IntArray.full_Zlength (vnext_2 + n_low_level_spec * sizeof ( INT ))).
  split_pure_spatial.
  - Intros_p Hnil.
    replace (n_low_level_spec - n_low_level_spec) with 0 in Hnil by lia.
    apply Zlength_nil_inv in Hnil; subst l0.
    cbn.
     Intros_p Hzero.
     Intros_p Hnil_eq.
    rewrite
      (logic_equiv_sepcon_comm
         (IntArray.full vnext_2 n_low_level_spec vnext0)
         (CharArray.full patn_pre (n_low_level_spec + 1)
            (str_low_level_spec ++ 0 :: nil))).
    apply derivable1_refl.
  - apply string_Zlength in Hstr.
    unfold constr_loop_from in H0.
    unfold_loop in H0.
    prog_nf in H0.
    safe_choice_r H0; try lia.
    dump_pre_spatial.
    exact H0.
Qed. 

Lemma proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Proof. 
  pre_process.
  prop_apply (IntArray.full_length vnext).
  Intros_p Hvnext_len.
  prop_apply CharArray.full_Zlength.
  Intros_p Hstr.
  apply string_Zlength in Hstr.
  split_pures.
  - dump_pre_spatial.
    unfold constr_loop_from in H0.
    rewrite Hstr in H0.
    unfold_loop in H0.
    prog_nf in H0.
    safe_choice_l H0; try lia.
    unfold constr_body at 1 in H0.
    prog_nf in H0.
    safe_step H0.
    prog_nf in H0.
    unfold constr_loop_from_after.
    rewrite app_Znth1 by lia.
    unfold constr_loop_from.
    rewrite Hstr.
    exact H0.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    exact H1.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia.
    unfold constr_loop_from_after.
    unfold constr_loop_from.
    rewrite Hstr.
    rewrite range_iter_unfold.
    prog_nf. rewrite choice_l_equiv.
    2:{ prog_nf. apply assume_false_equiv; lia. }
    rewrite assume_equiv by lia.
    unfold constr_body at 1.
    prog_nf.
    rewrite assert_equiv by lia.
    prog_nf.
    easy.
Qed.

Lemma proof_of_match_entail_wit_1 : match_entail_wit_1.
Proof.
  pre_process.
  subst; kmp_solve.
  - rewrite (logic_equiv_sepcon_comm
      (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil))
      (&( "patn_len") # Int |-> n_low_level_spec **
       (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil) **
        (&( "text_len") # Int |-> m_low_level_spec **
         IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec)))).
    repeat rewrite <- logic_equiv_sepcon_assoc.
    rewrite (logic_equiv_sepcon_comm
      (&( "patn_len") # Int |-> n_low_level_spec)
      (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil) **
       (&( "text_len") # Int |-> m_low_level_spec **
        (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec **
         CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil))))).
    rewrite (logic_equiv_sepcon_comm
      (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil))
      (&( "text_len") # Int |-> m_low_level_spec **
       (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec **
        CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)))).
    repeat rewrite logic_equiv_sepcon_assoc.
    cancel (&( "text_len") # Int |-> m_low_level_spec).
    cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    rewrite (logic_equiv_sepcon_comm
      (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec)
      (&( "patn_len") # Int |-> n_low_level_spec)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
    cancel (&( "patn_len") # Int |-> n_low_level_spec).
  - dump_pre_spatial.
    unfold match_loop_from.
    unfold match_loop in H1.
    exact H1.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
Qed. 

Lemma proof_of_match_entail_wit_2 : match_entail_wit_2.
Proof. 
  pre_process.
  prop_apply CharArray.full_Zlength.
  Intros_p Htext.
  kmp_solve.
  - apply string_Zlength in Htext.
    rewrite (logic_equiv_sepcon_comm
      (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec)
      (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil))).
    cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - apply string_Zlength in Htext.
    dump_pre_spatial.
    unfold match_loop_from_after, applyf in H0.
    rewrite Htext in H0.
    safe_choice_r H0; [auto | lia].
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
Qed. 

Lemma proof_of_match_return_wit_2 : match_return_wit_2.
Proof.
  pre_process; subst.
  unfold match_loop_from_after, applyf in H0.
  prop_apply CharArray.full_Zlength.
  Intros_p Hpatn.
  apply string_Zlength in Hpatn.
  rewrite Hpatn in *; clear Hpatn.
  Exists (Some (i - n_low_level_spec + 1)).
  kmp_solve.
  - rewrite (logic_equiv_sepcon_comm
      (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec)
      (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil))).
    cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - dump_pre_spatial.
    safe_choice_l H0; auto.
  - dump_pre_spatial.
    reflexivity.
Qed. 

Lemma proof_of_match_return_wit_1 : match_return_wit_1.
Proof. 
  pre_process.
  prop_apply (CharArray.full_Zlength text_pre).
  Intros_p Htext.
  Exists None.
  kmp_solve.
  - cancel (CharArray.full patn_pre (n_low_level_spec + 1) (patn0_low_level_spec ++ 0 :: nil)).
    cancel (CharArray.full text_pre (m_low_level_spec + 1) (text0_low_level_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre n_low_level_spec vnext0_low_level_spec).
  - apply string_Zlength in Htext.
    dump_pre_spatial.
    unfold match_loop_from in H0.
    rewrite Htext in H0.
    unfold_loop in H0.
    prog_nf in H0.
    safe_choice_r H0; try lia.
    unfold continue in H0.
    prog_nf in H0.
    auto.
  - dump_pre_spatial.
    reflexivity.
Qed. 

Lemma proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Proof. 
  pre_process.
  prop_apply CharArray.full_Zlength.
  Intros_p Htext.
  apply string_Zlength in Htext.
  split_pures.
  - dump_pre_spatial.
    eapply safeExec_proequiv.
    2: exact H0.
    rewrite app_Znth1 by lia.
    unfold match_loop_from_after.
    unfold match_loop_from.
    rewrite Htext.
    rewrite (range_iter_break_unfold _ _ i).
    prog_nf.
    rewrite choice_l_equiv.
    2:{ prog_nf. apply assume_false_equiv; lia. }
    rewrite assume_equiv by lia.
    unfold match_body at 1.
    prog_nf.
    rewrite assert_equiv by lia.
    prog_nf.
    apply common_step_equiv; intros.
    unfold break, continue.
    prog_nf.
    easy.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia.
    unfold match_loop_from_after.
    unfold match_loop_from.
    rewrite Htext.
    rewrite (range_iter_break_unfold _ _ i).
    prog_nf.
    rewrite choice_l_equiv.
    2:{ prog_nf. apply assume_false_equiv; lia. }
    rewrite assume_equiv by lia.
    unfold match_body at 1.
    prog_nf.
    rewrite assert_equiv by lia.
    prog_nf.
    apply common_step_equiv; intros.
    unfold break, continue.
    prog_nf.
    easy.
Qed. 

Lemma proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  Exists patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec n_high_level_spec.
  remember (match_loop 0 patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec) as prog.
  Exists m_high_level_spec (fun (r: option Z) x => prog.(MonadErr.nrm) tt r x).
  do 2 prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_length; Intros.
  apply string_Zlength in H3.
  apply string_Zlength in H4.
  rewrite <- Zlength_correct in H5.
  assert (Zlength patn0_high_level_spec > 0) by lia.
  rewrite <- Zlength_nonnil in H6.
  pose proof match_loop_sound 0 patn0_high_level_spec text0_high_level_spec vnext0_high_level_spec H6 ltac:(lia) H.
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  apply _derivable1_andp_intros.
  {
    apply (derivable1s_coq_prop_r
      (safeExec ATrue prog (fun (r : option Z) (x : unit) => MonadErr.nrm prog tt r x))).
    pose proof H7 as Hloop.
    destruct Hloop as [_ Herr].
    specialize (Herr tt).
    subst prog.
    apply safeExec_monad_Atrue_finnal; tauto.
  }
  apply _derivable1_andp_intros.
  {
    apply (derivable1s_coq_prop_r (n_high_level_spec > 0)); lia.
  }
  apply _derivable1_andp_intros.
  {
    apply (derivable1s_coq_prop_r (n_high_level_spec < 2147483647)); lia.
  }
  apply _derivable1_andp_intros.
  {
    apply (derivable1s_coq_prop_r (m_high_level_spec < 2147483647)); lia.
  }
  cancel.
  apply derivable1_wand_sepcon_adjoint.
  Intros ret retval.
  pose proof H7 as Hloop.
  destruct Hloop as [Hpost _].
  apply safeExec_ret_Atrue_finnal in H8.
  destruct H8 as [σ H8]; subst prog.
  specialize (Hpost ret tt σ I H8).
  destruct ret; simpl in H9.
  - Left; Exists z.
    subst retval; kmp_solve.
    + repeat cancel.
    + apply (derivable1s_coq_prop_r (z >= 0)).
      apply first_occur_nonneg in Hpost; auto.
    + apply (derivable1s_coq_prop_r (first_occur patn0_high_level_spec text0_high_level_spec z)).
      exact Hpost.
  - Right; Exists (-1).
    subst retval; kmp_solve.
    + repeat cancel.
    + apply (derivable1s_coq_prop_r (-1 = -1)); lia.
    + apply (derivable1s_coq_prop_r (no_occurance patn0_high_level_spec text0_high_level_spec)).
      exact Hpost.
Qed.

Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Proof. 
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  apply string_Zlength in H1.
  Exists str_high_level_spec n_high_level_spec.
  assert (Zlength str_high_level_spec > 0) by lia.
  apply Zlength_nonnil in H2.
  pose proof constr_loop_sound 0 str_high_level_spec H2.
  Exists (fun r x => (constr_loop 0 str_high_level_spec).(MonadErr.nrm) tt r x).
  kmp_solve.
  apply _derivable1_andp_intros.
  kmp_solve.
  {
    apply (derivable1s_coq_prop_r
      (safeExec ATrue (constr_loop 0 str_high_level_spec)
        (fun (r : list Z) (x : unit) => MonadErr.nrm (constr_loop 0 str_high_level_spec) tt r x))).
    pose proof H3 as Hloop.
    destruct Hloop as [_ Herr].
    specialize (Herr tt I).
    apply safeExec_monad_Atrue_finnal; tauto.
  }
  {
    apply (derivable1s_coq_prop_r (n_high_level_spec > 0)); lia.
  }
  {
    apply (derivable1s_coq_prop_r (n_high_level_spec < 2147483647)); lia.
  }
  cancel.
  apply derivable1_wand_sepcon_adjoint.
  kmp_solve; Intros vnext retval.
  Exists vnext retval; kmp_solve.
  - cancel.
  - pose proof H3 as Hloop.
    destruct Hloop as [Hpost _].
    apply safeExec_ret_Atrue_finnal in H4.
    destruct H4 as [σ H4].
    specialize (Hpost vnext tt σ I H4).
    destruct Hpost as [Hprefix _].
    apply (derivable1s_coq_prop_r (vnext is_prefix_func_of str_high_level_spec)).
    exact Hprefix.
Qed. 

Lemma proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply CharArray.full_Zlength; Intros.
  prop_apply IntArray.full_Zlength; Intros.
  apply string_Zlength in H2.
  apply safeExec_bind in H as (X' & H7 & H8).
  Exists str0_bind_spec vnext0_bind_spec.
  Exists n_bind_spec m_bind_spec X'; kmp_solve.
  repeat rewrite logic_equiv_coq_prop_andp_sepcon.
  apply _derivable1_andp_intros.
  apply _derivable1_andp_intros.
  apply _derivable1_andp_intros.
  - apply (derivable1s_coq_prop_r
      (safeExec ATrue (inner_loop 0 str0_bind_spec vnext0_bind_spec ch_pre j_pre) X')).
    exact H7.
  - apply (derivable1s_coq_prop_r (m_bind_spec <= n_bind_spec)).
    exact H0.
  - apply (derivable1s_coq_prop_r (n_bind_spec < 2147483647)).
    exact H1.
  - rewrite (logic_equiv_sepcon_comm
      (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec)
      (CharArray.full str_pre (n_bind_spec + 1) (str0_bind_spec ++ 0 :: nil))).
    cancel (CharArray.full str_pre (n_bind_spec + 1) (str0_bind_spec ++ 0 :: nil)).
    cancel (IntArray.full vnext_pre m_bind_spec vnext0_bind_spec).
    apply derivable1_wand_sepcon_adjoint.
    kmp_solve.
    Intros ret.
    Exists ret; kmp_solve.
    + cancel.
    + apply (derivable1s_coq_prop_r
        (safeExec ATrue (applyf f_bind_spec ret) X_bind_spec)).
      apply H8.
      exact H.
    + apply (derivable1s_coq_prop_r (0 <= ret)).
      exact H4.
    + apply (derivable1s_coq_prop_r (ret < m_bind_spec + 1)).
      exact H5.
Qed. 
