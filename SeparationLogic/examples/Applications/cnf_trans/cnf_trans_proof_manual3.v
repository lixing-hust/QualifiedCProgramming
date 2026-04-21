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
From SimpleC.EE.Applications.cnf_trans Require Import cnf_trans_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.Applications.cnf_trans Require Import smt_lang_lib.
From SimpleC.EE.Applications.cnf_trans Require Import cnf_trans_lib.
From SimpleC.EE.Applications Require Import malloc.
From SimpleC.EE.Applications Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_clause_gen_binary_return_wit_5 : clause_gen_binary_return_wit_5.
Proof.
  pre_process.
  clear H27.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H28.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H27 into H25.
  remember (- p1_pre :: p3_pre :: 0 :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.
    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      apply Z.abs_le.
      split.
      - repeat apply Z.min_glb; try lia.
      - pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_6 : clause_gen_binary_return_wit_6.
Proof.
  pre_process.
  clear H27.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_AND). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H28.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H27 into H25.
  remember (- p1_pre :: - p2_pre :: p3_pre :: nil) as c1 eqn:H_c1.
  remember (p2_pre :: - p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: - p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.

    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.

      apply Z.abs_le.
      split.
      - 
        repeat apply Z.min_glb; try lia.
      - 
        pose proof Z.le_min_l (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min (- p3_pre) (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0)))
        (Z.min (Z.min p2_pre (Z.min (- p3_pre) (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_7 : clause_gen_binary_return_wit_7.
Proof.
  pre_process.
  clear H28 H27.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IMPLY). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H29.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H27 into H25.
  remember (- p1_pre :: p2_pre :: - p3_pre :: nil) as c1 eqn:H_c1.
  remember (- p2_pre :: p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (p1_pre :: p3_pre :: 0 :: nil) as c3 eqn:H_c3.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_7 c1 retval_3); try easy.
  sep_apply (H23 retval_6 c2 retval_2); try easy.
  sep_apply (H23 retval_5 c3 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c3 retval_6); try easy.
  sep_apply (H23 retval_6 c2 retval_7); try easy.
  sep_apply (H23 retval_7 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_7 y (c1 :: nil) clist); try easy.
  sep_apply (H23 retval_6 retval_7 (c2 :: nil) ((c1 :: nil) ++ clist)); try easy.
  sep_apply (H23 retval_5 retval_6 (c3 :: nil) ((c2 :: nil) ++ (c1 :: nil) ++ clist)); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1, <- H_c2, <- H_c3.
  assert (Zlength (c3 :: c2 :: c1 :: clist) = ccnt + 3). {
    repeat rewrite Zlength_cons.
    rewrite H3.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c3 :: c2 :: c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26 H27 H28 H29 H30.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.

    rewrite H_c1, H_c2, H_c3.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.

      apply Z.abs_le.
      split.
      - 
        repeat apply Z.min_glb; try lia.
      - 
        pose proof Z.le_min_l (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))).
        pose proof Z.le_min_l p1_pre (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min p1_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1 : clause_gen_binary_return_wit_1.
Proof.
  pre_process.
  (* clear H24 H25.
  rename H26 into H24. *)
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IMPLY). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H25 H26.
  rename H22 into Hs1.
  rename H23 into Hs2.
  rename H24 into Hs3.
  rename H27 into H22.
  rename H28 into H25.
  remember (p3_pre :: 0 :: 0 :: nil) as c1 eqn:H_c1.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_5 c1 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_5 y (c1 :: nil) clist); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1.
  assert (Zlength (c1 :: clist) = ccnt + 1). {
    repeat rewrite Zlength_cons.
    rewrite H1.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.

    rewrite H_c1.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.

      apply Z.abs_le.
      split.
      - 
        repeat apply Z.min_glb; try lia.
      - 
        pose proof Z.le_min_r (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist).
        remember (Z.min (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  }
  clear - H0 H27 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_2 : clause_gen_binary_return_wit_2.
Proof.
  pre_process.
  clear H25.
  rename H26 into H25.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_IFF). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H27 H25.
  rename H22 into Hs1.
  rename H23 into Hs2.
  rename H24 into Hs3.
  rename H28 into H22.
  rename H26 into H25.
  remember (p3_pre :: 0 :: 0 :: nil) as c1 eqn:H_c1.
  pose proof store_cnf_list_fold.
  sep_apply (H23 retval_5 c1 retval); try easy.
  clear H23.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H23 retval_5 c1 y); try easy.
  clear H23.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H23 retval_5 y (c1 :: nil) clist); try easy.
  clear H23.
  unfold store_predata.
  Exists retval_5.
  rewrite H25.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  repeat rewrite <- app_comm_cons.
  unfold app.
  rewrite <- H_c1.
  assert (Zlength (c1 :: clist) = ccnt + 1). {
    repeat rewrite Zlength_cons.
    rewrite H1.
    lia.
  }
  rewrite H23.
  assert (prop_cnt_inf (c1 :: clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H24 H26.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H26.
    pose proof Z.max_lub_l _ _ _ H26.
    pose proof Z.max_lub_r _ _ _ H26.

    rewrite H_c1.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.

      apply Z.abs_le.
      split.
      - 
        repeat apply Z.min_glb; try lia.
      - 
        pose proof Z.le_min_r (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist).
        remember (Z.min (Z.min p3_pre (Z.min 0 (Z.min 0 0))) (min_cnf clist)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  }
  clear - H0 H27 Hs1 Hs2 Hs3.
  entailer!.
Qed.


Lemma proof_of_clause_gen_binary_which_implies_wit_1 : clause_gen_binary_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
Qed. 