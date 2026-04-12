Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications.fme Require Import fme_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications.fme Require Import fme_lib.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Proof.
  pre_process.
  entailer!.
  rewrite <- Z.gcd_comm in H.
  rewrite Z.gcd_rem in H.
  - rewrite Z.gcd_comm. auto.
  - auto.
Qed.

Lemma proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Proof.
  pre_process.
  entailer!.
  rewrite H.
  rewrite Z.gcd_0_r_nonneg.
  - reflexivity.
  - lia.
Qed.

Lemma proof_of_gcd_partial_solve_wit_1_pure : gcd_partial_solve_wit_1_pure.
Proof. 
  pre_process.
  entailer!.
  - apply Z.rem_nonneg; lia.
  - apply Z.le_trans with a_pre.
    + apply Z.rem_le; lia.
    + lia.
Qed.

Lemma proof_of_free_InequList_return_wit_3 : free_InequList_return_wit_3.
Proof.
  pre_process. subst.
  sep_apply inequlist_0_implies_nil. entailer!.
Qed.

Lemma proof_of_free_InequList_return_wit_2 : free_InequList_return_wit_2.
Proof.
  pre_process. subst.
  sep_apply inequlist_0_implies_nil. entailer!.
Qed.

Lemma proof_of_eliminate_entail_wit_2 : eliminate_entail_wit_2.
Proof.
  pre_process.
  Exists nil nil nil.
  Exists {| upper := nil; lower := nil; remain := nil |}.
  Exists nil l.
  entailer!; simpl.
  - entailer!.
  - unfold form_BP. tauto.
  - split; intros; simpl; tauto.
Qed.

Lemma proof_of_eliminate_entail_wit_3_3 : eliminate_entail_wit_3_3.
Proof.
  pre_process.
  set (re := x::re_2) in *.
  Exists up_2 lo_2 re.
  Exists {| upper := up_2; lower := lo_2; remain := re|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef remain. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_re l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x.
    apply H16; try tauto.
    lia.
  - rewrite H3, H0.
    unfold l1.
    apply list_split_adjust.
Qed.

(* similar to wit_3_1 *)
Lemma proof_of_eliminate_entail_wit_3_2 : eliminate_entail_wit_3_2.
Proof.
  pre_process.
  set (lo := x::lo_2) in *.
  Exists up_2 lo re_2.
  Exists {| upper := up_2; lower := lo; remain := re_2|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef lower. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_lo l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x.
    apply H17; try tauto; try lia.
  - rewrite H4, H1.
    unfold l1.
    apply list_split_adjust.
Qed.

Lemma proof_of_eliminate_entail_wit_3_1 : eliminate_entail_wit_3_1.
Proof.
  pre_process.
  set (up := x::up_2) in *.
  Exists up lo_2 re_2.
  Exists {| upper := up; lower := lo_2; remain := re_2|}.
  set (l1 := l1_2 ++ x::nil).
  Exists l1 l3.
  entailer!; simpl.
  - Exists cur_coef upper. 
    entailer!. 
    sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - unfold form_BP. tauto.
  - pose proof eliminate_xn_step_up l1_2 l1 up_2 lo_2 re_2 bp_2 num_pre x.
    apply H17; try tauto; try lia.
  - rewrite H4, H1.
    unfold l1.
    apply list_split_adjust. 
Qed.

Lemma proof_of_eliminate_return_wit_1 : eliminate_return_wit_1.
Proof.
  pre_process.
  Exists remain lower upper.
  Exists up_2 lo_2 re_2 bp.
  Intros.
  rewrite H.
  sep_apply inequlist_0_implies_nil; clear H.
  Intros.
  rewrite H in H0; clear H.
  rewrite app_nil_r in H0.
  rewrite H0 in *; clear H0.
  entailer!;
  induction H1;
  destruct H2 as [BP1 [BP2 BP3]];
  rewrite <- BP1 in elim_upper;
  rewrite <- BP2 in elim_lower;
  rewrite <- BP3 in elim_remain;
  clear BP1 BP2 BP3.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply H12.
    specialize elim_remain with c.
    tauto.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply H12.
    specialize elim_lower with c.
    tauto.
  - unfold LP_abs_in_int_range in *.
    intros.
    apply H12.
    specialize elim_upper with c.
    tauto.
  - unfold InequList_nth_neg.
    intros.
    rewrite elim_lower in H.
    destruct H.
    rewrite coef_Znth_nth; try lia.
    split; try lia.
    unfold LP_abs_in_int_range in H12.
    specialize H12 with c.
    apply H12 in H.
    unfold abs_in_int_range in H.
    specialize H with num_pre.
    rewrite coef_Znth_nth in H; lia.
  - unfold InequList_nth_pos.
    intros.
    rewrite elim_upper in H.
    destruct H.
    rewrite coef_Znth_nth; try lia.
    split; try lia.
    unfold LP_abs_in_int_range in H12.
    specialize H12 with c.
    apply H12 in H.
    unfold abs_in_int_range in H.
    specialize H with num_pre.
    rewrite coef_Znth_nth in H; lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_2 : generate_new_constr_safety_wit_2.
Proof.
  pre_process.
  entailer!.
  assert (retval = 0 \/ retval <> 0) by lia.
  destruct H9.
  + rewrite H in H9.
    apply Z.gcd_eq_0_l in H9.
    lia.
  + lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_3 : generate_new_constr_safety_wit_3.
Proof.
  pre_process.
  entailer!.
  assert (retval = 0 \/ retval <> 0) by lia.
  destruct H9.
  + rewrite H in H9.
    apply Z.gcd_eq_0_l in H9.
    lia.
  + lia.
Qed.  

Lemma proof_of_generate_new_constr_safety_wit_4 : generate_new_constr_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (- coef_Znth cur_num_pre c2 0 ÷ retval > 0).
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
  + lia.
Qed. 

Lemma proof_of_generate_new_constr_safety_wit_6 : generate_new_constr_safety_wit_6.
Proof.
  pre_process.
  assert (- coef_Znth cur_num_pre c2 0 ÷ retval > 0).
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
  + entailer!.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_9 : generate_new_constr_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  assert (coef_Znth cur_num_pre c1 0 ÷ retval > 0).
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_11 : generate_new_constr_safety_wit_11.
Proof.
  pre_process.
  assert (coef_Znth cur_num_pre c1 0 ÷ retval > 0).
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + entailer!.
Qed. 

Lemma proof_of_generate_new_constr_safety_wit_24 : generate_new_constr_safety_wit_24.
Proof.
  pre_process.
  unfold in_int_range in H5.
  entailer!.
  + pose proof H5 i.
    lia.
  + pose proof H5 i.
    lia.
Qed.

Lemma proof_of_generate_new_constr_safety_wit_25 : generate_new_constr_safety_wit_25.
Proof.
  pre_process.
  unfold in_int_range in H4.
  entailer!.
  + pose proof H4 i.
    lia.
  + pose proof H4 i.
    lia.
Qed. 

Lemma proof_of_generate_new_constr_entail_wit_2 : generate_new_constr_entail_wit_2.
Proof.
  pre_process.
  entailer! ; subst m1v m2v ; try lia.
  + unfold in_int_range.
    intros.
    lia.
  + unfold in_int_range.
    intros.
    lia.
  + apply gcd_quot_left_pos.
    exists (- coef_Znth cur_num_pre c2 0).
    lia.
  + apply gcd_quot_right_pos.
    exists (coef_Znth cur_num_pre c1 0).
    lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_3 : generate_new_constr_entail_wit_3.
Proof.
  pre_process.
  entailer!.
  + unfold in_int_range.
    unfold in_int_range in H13.
    intros.
    assert (i0 < i \/ i0 >= i) by lia.
    destruct H27.
    - apply H13.
      lia.
    - assert (i0 = i) by lia.
      rewrite H28.
      assert (m2v * lb2 <= m2v * coef_Znth i c2 0 <= m2v * ub2) by nia.
      assert (-INT_MAX <= m2v * lb2 /\ m2v * ub2 <= INT_MAX).
      * split.
        ++ rewrite H11. apply Zquot.Z_mult_quot_ge. lia.
        ++ rewrite H10. apply Zquot.Z_mult_quot_le. lia.
      * lia.
  + unfold in_int_range.
    unfold in_int_range in H12.
    intros.
    assert (i0 < i \/ i0 >= i) by lia.
    destruct H27.
    - apply H12.
      lia.
    - assert (i0 = i) by lia.
      rewrite H28.
      assert (m1v * lb1 <= m1v * coef_Znth i c1 0 <= m1v * ub1) by nia.
      assert (-INT_MAX <= m1v * lb1 /\ m1v * ub1 <= INT_MAX).
      * split.
        ++ rewrite H9. apply Zquot.Z_mult_quot_ge. lia.
        ++ rewrite H8. apply Zquot.Z_mult_quot_le. lia.
      * lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_4 : generate_new_constr_entail_wit_4.
Proof.
  pre_process.
  Exists l.
  prop_apply (coef_array_length r1_pre).
  prop_apply (coef_array_length r2_pre).
  entailer!.
  + unfold generate_new_constraint_partial.
    split ; [ | split ; [ | split]] ; try auto.
    - assert (m1v * coef_Znth cur_num_pre c1 0 = m2v * (- coef_Znth cur_num_pre c2 0)).
      {
        subst m1v m2v.
        assert (retval > 0). {
          subst retval.
          pose proof Z.gcd_nonneg (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0).
          destruct (Z.eq_dec (Z.gcd (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0)) 0).
          + apply Z.gcd_eq_0_l in e. lia.
          + lia.
        }
        subst retval.
        repeat rewrite zdiv_equiv ; try lia.
        rewrite Z.gcd_comm.
        rewrite Z.gcd_div_swap.
        lia.
      }
      lia.
    - intros. lia.
  + assert (i = num_pre + 1) by lia.
    rewrite H28 in H11.
    apply H11.
  + assert (i = num_pre + 1) by lia.
    rewrite H28 in H10.
    apply H10.
  + unfold NULL ; lia. 
  + unfold NULL ; lia.
Qed.

Lemma proof_of_generate_new_constr_entail_wit_5 : generate_new_constr_entail_wit_5.
Proof.
  pre_process.
  destruct (Z.eq_dec i_2 0).
  {
    sep_apply IntArray.missing_i_merge_to_full; try lia.
    subst i_2.
    unfold coef_array at 5.
    unfold Constraint_list.
    Exists ({| const := (m2v * coef_Znth 0 c2 0 +
    m1v * coef_Znth 0 c1 0) ; coef := coef c3_2|}). simpl. 
    unfold replace_Znth. simpl. 
    Right. entailer!.
    * unfold abs_in_int_range. intros.
      unfold coef_Znth, Constraint_list. simpl.
      unfold abs_in_int_range, coef_Znth, Constraint_list in H12 ; simpl in H12.
      unfold coef_Znth, Constraint_list in H2, H1 ; simpl in H2, H1.
      destruct (Z.eq_dec i0 0).
      - subst. unfold Znth in *. simpl in *. lia.
      - specialize (H12 i0 (ltac:(lia))).
        unfold Znth in H12. unfold Znth.
        simpl. destruct (Zto_nat i0) eqn : En; try lia.
        simpl in H12. lia.  
    * unfold generate_new_constraint_partial.
      split ; [ | split ; [ | split]] ; try auto.
      - assert (m1v * coef_Znth cur_num_pre c1 0 = m2v * (- coef_Znth cur_num_pre c2 0)).
        {
          subst m1v m2v.
          assert (retval > 0). {
            subst retval.
            pose proof Z.gcd_nonneg (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0).
            destruct (Z.eq_dec (Z.gcd (coef_Znth cur_num_pre c1 0) (- coef_Znth cur_num_pre c2 0)) 0).
            + apply Z.gcd_eq_0_l in e. lia.
            + lia.
          }
          subst retval.
          repeat rewrite zdiv_equiv ; try lia.
          rewrite Z.gcd_comm.
          rewrite Z.gcd_div_swap.
          lia.
        }
        lia.
      - intros. 
        assert (i0 = 0) by lia. subst.
        unfold coef_Znth, Constraint_list in H2, H1 ; simpl in H2, H1.
        unfold coef_Znth, Constraint_list. simpl.
        unfold Znth in * ; simpl in * ; lia.
  }
  {
    Exists (coef_replace_Znth i_2 (m2v * coef_Znth i_2 c2 0 + m1v * coef_Znth i_2 c1 0) c3_2).
    sep_apply coef_array_merge ; try (unfold NULL ; lia). clear H38 H39.
    prop_apply (coef_array_length res) ; try lia .
    entailer!.
    * unfold abs_in_int_range.
      intros.
      assert (i0 = i_2 \/ i0 < i_2 \/ i0 > i_2) by lia.
      destruct H42.
      + rewrite H42.
        rewrite coef_replace_Znth_eq. lia.
        rewrite H39. lia.
      + destruct H42.
        - rewrite coef_replace_Znth_le.
          ++ unfold abs_in_int_range in H12.
            pose proof H12 i0.
            lia.
          ++ lia.
        - rewrite coef_replace_Znth_ge.
          ++ unfold abs_in_int_range in H12.
            pose proof H12 i0.
            lia.
          ++ lia.
    * unfold generate_new_constraint_partial.
      unfold generate_new_constraint_partial in H10.
      destruct H10 as [? [? [?  ?]]].
      split ; [ | split ; [ | split]] ; try auto.
      intros.
      assert (i0 < i_2 \/ i0 >= i_2) by lia.
      destruct H45.
      + assert (coef_Znth i0 c3_2 0 = m1v * coef_Znth i0 c1 0 + m2v * coef_Znth i0 c2 0).
        - apply H43. lia.
        - rewrite <-H43. 
          apply coef_replace_Znth_le.
          lia. lia.
      + assert (i0 = i_2) by lia.
        rewrite H46.
        assert (m1v * coef_Znth i_2 c1 0 + m2v * coef_Znth i_2 c2 0 =
                m2v * coef_Znth i_2 c2 0 + m1v * coef_Znth i_2 c1 0) by lia.
        rewrite H47.
        apply coef_replace_Znth_eq.
        lia.
  }
Qed. 

Lemma proof_of_generate_new_constr_return_wit_6 : generate_new_constr_return_wit_6.
Proof.  
  pre_process.
  prop_apply (coef_array_length r2_pre). 
  Left.
  Exists c3_2. Intros.
  prop_apply (coef_array_length r1_pre).
  prop_apply (coef_array_length res).
  entailer!.
  all : try (unfold NULL ; lia).
  apply generate_new_constraint_complete ; try lia.
  exists (num_pre + 1), m1v, m2v.
  split ; [ lia | split ; [lia | split ; [lia | ]]].
  assert (num_pre + 1 = i_2) by lia.
  rewrite H40.
  apply H6.
Qed.

Lemma proof_of_generate_new_constr_partial_solve_wit_11_pure : generate_new_constr_partial_solve_wit_11_pure.
Proof.
  pre_process.
  entailer! ; 
  pose proof H4 i ; pose proof H5 i ; lia.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_1 : generate_new_constraint_list_entail_wit_1.
Proof.
  pre_process.
  Exists l_init nil nil l1.
  entailer!.
  + unfold InequList_seg.
    entailer!.
  + unfold generate_new_constraints.
    intros.
    tauto.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_2 : generate_new_constraint_list_entail_wit_2.
Proof.
  pre_process.
  Exists p1_next_2.
  Exists p1_coef.
  Exists l3 l4.
  Exists nil l2.
  Exists l11 x l13.
  entailer!.
  + unfold InequList_seg.
    entailer!.
  + unfold generate_new_constraints_partial.
    destruct l12.
    - exists l4, nil.
      split.
      * intros.
        unfold In.
        tauto.
      * split.
        ++ apply H8.
        ++ intros.
           destruct H20.
    - exists l4, nil.
      split.
      * intros.
        split; try tauto.
        unfold In. tauto.
      * split.
        ++ apply H8.
        ++ intros.
           destruct H20.
  + rewrite <-H.
    auto.
Qed. 

Lemma proof_of_generate_new_constraint_list_entail_wit_3 : generate_new_constraint_list_entail_wit_3.
Proof.
  pre_process.
  Exists p1_next_2 p1_coef_3.
  Exists (c3 :: l3_3).
  Exists (c3 :: l4_3).
  Exists (l21_2 ++ x_2 :: nil) l23.
  Exists l11_3 x1_2 l12_3.
  entailer!.
  + rewrite H6.
    entailer!.
    sep_apply InequList_seg_append; [entailer! | easy | unfold NULL ; lia].
  + unfold LP_abs_in_int_range.
    intros.
    destruct H39.
    - rewrite <-H39.
      rewrite H6.
      auto.
    - auto.
  + rewrite H15.
    apply app_comm_cons.
  + apply generate_new_constraints_step.
    split.
    - rewrite <-H3; auto.
    - apply H1.
  + rewrite <-list_split_adjust.
    rewrite <-H3. auto.
Qed.

Lemma proof_of_generate_new_constraint_list_entail_wit_4 : generate_new_constraint_list_entail_wit_4.
Proof. 
  pre_process.
  Exists l3_3 l4_3.
  Exists (l11_3 ++ x1 :: nil) l12_3.
  rewrite H.
  sep_apply (inequlist_0_implies_nil l22).
  entailer!.
  + sep_apply InequList_seg_append; try easy.
    entailer!.
    sep_apply InequList_seg_degeneration.
    rewrite H6.
    rewrite H33.
    rewrite app_nil_r.
    entailer!.
  + apply generate_new_constraints_complete.
    rewrite H6.
    subst l22.
    rewrite app_nil_r.
    auto.
  + rewrite <-list_split_adjust.
    auto.
Qed. 

Lemma proof_of_generate_new_constraint_list_return_wit_1 : generate_new_constraint_list_return_wit_1.
Proof.
  pre_process.
  Left.
  rewrite <-H4.
  entailer!.
  sep_apply (InequList_seg_append_list l11_2); try easy.
  sep_apply (InequList_seg_append_list l21); try easy.
  subst.
  entailer!.
Qed.

Lemma proof_of_generate_new_constraint_list_return_wit_2 : generate_new_constraint_list_return_wit_2.
Proof.
  pre_process.
  Right.
  rewrite H.
  sep_apply inequlist_0_implies_nil.
  Exists l3_2 l4_2.
  entailer!.
  + sep_apply InequList_seg_degeneration.
    subst.
    rewrite app_nil_r.
    entailer!.
  + subst.
    rewrite app_nil_r.
    auto.
Qed.

Lemma proof_of_generate_new_constraint_list_partial_solve_wit_3_pure : generate_new_constraint_list_partial_solve_wit_3_pure.
Proof.
  pre_process.
  unfold InequList_nth_pos in H20.
  unfold InequList_nth_neg in H21.
  subst.
  specialize (H33 x ltac:(apply in_elt) cur_num_pre).
  specialize (H32 x1 ltac:(apply in_elt) cur_num_pre).
  specialize (H31 x ltac:(apply in_elt)).
  specialize (H30 x1 ltac:(apply in_elt)).
  entailer!.
Qed.

Lemma proof_of_real_shadow_entail_wit_1 : real_shadow_entail_wit_1.
Proof. 
  pre_process.
  Exists l1.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - apply InequList_Zeros_range_empty.
  - apply self_LP_implies.
Qed.

Lemma proof_of_real_shadow_entail_wit_2_2 : real_shadow_entail_wit_2_2.
Proof. 
  pre_process.
  Exists l3.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - pose proof (eliminate_keep_Zeros _ _ _ _ _ H7 H20 (ltac:(lia)) (ltac:(lia)) _ _ _ H8). 
    pose proof (eliminate_add_Zeros _ _ _ _ _ H7 H20 H21 (ltac:(lia)) (ltac:(lia)) _ _ _ H8).
    pose proof (generate_new_contraints_keep_Zeros _ _ _ _ _ _ H0 (proj1 H31) (proj1 (proj2 H31)) (ltac:(lia)) (ltac:(lia))).
    pose proof (generate_new_contraints_add_Zeros _ _ _ _ (cnt + 1) (n_pre + 1) H0 (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
    replace (cnt - 1 + 1) with cnt in * by lia.
    apply InequList_Zeros_range_extend_left ; try auto.
    + subst l3. apply InequList_Zeros_app ; try tauto.
    + subst l3. apply InequList_nth_zero_app ; try tauto. 
  - apply LP_implies_trans with (lp2:=l2_2); try tauto.
    apply FME_step_sound with cnt.
    rewrite H1.
    unfold form_BP in H7.
    destruct H8 as [BP1 [BP2 BP3]].
    rewrite BP3.
    rewrite BP1, BP2 in H0.
    constructor; tauto.
Qed. 

Lemma proof_of_real_shadow_entail_wit_2_1 : real_shadow_entail_wit_2_1.
Proof. 
  pre_process.
  Exists l3.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    entailer!.
  - pose proof (eliminate_keep_Zeros _ _ _ _ _ H5 H18 (ltac:(lia)) (ltac:(lia)) _ _ _ H6). 
    pose proof (eliminate_add_Zeros _ _ _ _ _ H5 H18 H19 (ltac:(lia)) (ltac:(lia)) _ _ _ H6).
    pose proof (generate_new_contraints_keep_Zeros _ _ _ _ _ _ H0 (proj1 H29) (proj1 (proj2 H29)) (ltac:(lia)) (ltac:(lia))).
    pose proof (generate_new_contraints_add_Zeros _ _ _ _ (cnt + 1) (n_pre + 1) H0 (ltac:(tauto)) (ltac:(tauto)) (ltac:(lia)) (ltac:(lia))).
    replace (cnt - 1 + 1) with cnt in * by lia.
    apply InequList_Zeros_range_extend_left ; try auto.
    + subst l3. apply InequList_Zeros_app ; try tauto.
    + subst l3. apply InequList_nth_zero_app ; try tauto.
  - apply LP_implies_trans with (lp2:=l2_2); try tauto.
    apply FME_step_sound with cnt.
    rewrite H1.
    unfold form_BP in H5.
    destruct H6 as [BP1 [BP2 BP3]].
    rewrite BP3.
    rewrite BP1, BP2 in H0.
    constructor; tauto.
Qed.

Lemma proof_of_real_shadow_return_wit_1 : real_shadow_return_wit_1.
Proof. 
  pre_process.
  Right.
  rewrite H, H0.
  repeat sep_apply inequlist_0_implies_nil.
  Exists 0 nil.
  entailer!.
  - repeat sep_apply store_ptr_undef_store_ptr.
    simpl.
    entailer!.
  - apply InequList_Zeros_nil.
  - apply LP_implies_nil.
Qed.

Lemma proof_of_real_shadow_return_wit_2 : real_shadow_return_wit_2.
Proof. 
  pre_process. subst.
  Right; Exists 0 nil.
  entailer!.
  - do 3 sep_apply store_ptr_undef_store_ptr.
    repeat sep_apply inequlist_0_implies_nil.
    simpl. entailer!.
  - apply InequList_Zeros_nil.
  - apply LP_implies_nil.
Qed.


Lemma proof_of_real_shadow_return_wit_6 : real_shadow_return_wit_6.
Proof.
  pre_process.
  Left. entailer!. do 3 sep_apply (store_ptr_undef_store_ptr).
  entailer!. subst.
  sep_apply inequlist_0_implies_nil. entailer!.
Qed.

Lemma proof_of_real_shadow_return_wit_4 : real_shadow_return_wit_4.
Proof.
  pre_process.
  Left. entailer!. do 3 sep_apply (store_ptr_undef_store_ptr).
  entailer!. subst.
  sep_apply inequlist_0_implies_nil. entailer!.
Qed.

Lemma proof_of_lia_deduction_entail_wit_1 : lia_deduction_entail_wit_1.
Proof.
  pre_process.
  Exists nil l2.
  rewrite app_nil_l.
  simpl. 
  entailer!.
  hnf. intros.
  inversion H12.
Qed.
  
Lemma proof_of_lia_deduction_entail_wit_2 : lia_deduction_entail_wit_2.
Proof.
  pre_process.
  Exists (l21_2 ++ (x :: nil)) l0.
  entailer!.
  - sep_apply InequList_seg_append ; try (unfold NULL; lia).
    entailer!.
  - hnf. intros.
    apply in_app_or in H19.
    destruct H19.
    + apply H4 ; auto.
    + destruct H19 ; try lia.
      subst. lia.
      inversion H19.
  - rewrite <- app_assoc. simpl.
    subst. auto.
Qed.

Lemma proof_of_lia_deduction_return_wit_3 : lia_deduction_return_wit_3.
Proof.
  pre_process.
  Left. Right.
  Exists BP0_4 p2_3.
  entailer!.
  eapply LP_Implies_UNSAT ; eauto.
  hnf. unfold satisfy_LP, satisfy_constraint, assignment.
  intros. intro.
  assert (In x l2_2).
  {
    subst l2_2.
    apply in_app_iff.
    right. subst l22.
    left. auto.
  }
  specialize (H20 _ H21).
  specialize (H11 _ H21).
  rewrite sum_prod_zeros in H20 ; try auto.
  rewrite H. auto.
Qed.
  
Lemma proof_of_lia_deduction_return_wit_4 : lia_deduction_return_wit_4.
Proof.
  pre_process.
  Right.
  Exists BP0_4 p2_3 l2_2.
  entailer!.
  sep_apply InequList_seg_append_list; try (unfold NULL; lia).
  subst l2_2 l22.
  entailer!.
Qed.

Lemma proof_of_lia_deduction_which_implies_wit_1 : lia_deduction_which_implies_wit_1.
Proof.
  pre_process.
  prop_apply InequList_length.
  entailer!.
  sep_apply InequList_seg_app. 
  entailer!.
Qed.