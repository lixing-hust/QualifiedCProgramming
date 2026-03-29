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
Require Import cnf_trans_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import smt_lang_lib.
Require Import cnf_trans_lib.
Require Import malloc.
Require Import super_poly_sll2.
Local Open Scope sac.

Lemma proof_of_clause_gen_unary_return_wit_1 : clause_gen_unary_return_wit_1.
Proof.
  pre_process.
  rename H8 into H100.
  rename H9 into H200.
  rename H10 into H300.
  rename H11 into H400.
  rename H12 into H500.
  rename H13 into H600.
  rename H14 into H700.
  assert ( all_zero_list 3 = 0 :: 0 :: 0 :: nil). {
    unfold all_zero_list.
    unfold all_zero_list_nat.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite H8.
  assert ((-p2_pre) :: (-p3_pre) :: 0 :: nil = (replace_Znth 1 (- p3_pre) (replace_Znth 0 (- p2_pre) (0::0::0::nil)))). {
    unfold replace_Znth.
    unfold replace_nth.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite <- H9.
  clear H9.
  assert ( p2_pre :: p3_pre :: 0 :: nil = (replace_Znth 1 p3_pre (replace_Znth 0 p2_pre (0 :: 0 :: 0 :: nil)))). {
    unfold replace_Znth.
    unfold replace_nth.
    unfold Z.to_nat.
    simpl; easy.
  }
  rewrite <- H9.
  clear H9 H8.
  assert (retval_3 <> NULL) by easy.
  sep_apply (store_cnf_list_fold retval_3 (p2_pre :: p3_pre :: 0 :: nil) retval).
  assert (retval_4 <> NULL) by easy.
  sep_apply (store_cnf_list_fold retval_4 (- p2_pre :: - p3_pre :: 0 :: nil) retval_2).
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H12 retval_3 (p2_pre :: p3_pre :: 0 :: nil) retval_4).
  sep_apply (H12 retval_4 (- p2_pre :: - p3_pre :: 0 :: nil) y).
  clear H12 H13 H14.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  specialize (H12 retval_4 y ((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) clist).
  pose proof derivable1_sepcon_comm.
  pose proof derivable1_sepcon_assoc1.
  entailer!.
  sep_apply H12.
  clear H12.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  specialize (H12 retval_3 retval_4 ((p2_pre :: p3_pre :: 0 :: nil) :: nil)(((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)).
  repeat rewrite H14.
  rewrite (H13 (sll store_cnf_list_cell "cnf_list" "next" retval_4 (((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)) _).
  sep_apply H12.
  clear H12.
  unfold iff2cnf_unary.
  unfold store_predata.
  Exists retval_3.
  entailer!.
  unfold sll_cnf_list.
  assert ((((p2_pre :: p3_pre :: 0 :: nil) :: nil) ++ ((- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist) = (((p2_pre :: p3_pre :: 0 :: nil) :: (- p2_pre :: - p3_pre :: 0 :: nil) :: nil) ++ clist)). {
    easy.
  }
  rewrite <- H12.
  repeat rewrite H14.
  3: easy.
  3: easy.
  3: easy.
  3: easy.
  2: {
    pose proof app_comm_cons.
    rewrite <- H12.
    pose proof Zlength_cons.
    rewrite H15.
    unfold app.
    rewrite H15.
    lia.
  }
  1: {
    pose proof prop_cnt_nneg clist.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H17.
    pose proof Z.max_lub_l _ _ _ H17.
    pose proof Z.max_lub_r _ _ _ H17.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      apply Z.abs_le.
      split.
      - repeat apply Z.min_glb; try lia.
      - pose proof Z.le_min_l (Z.min p2_pre (Z.min p3_pre (Z.min 0 0))) (Z.min (Z.min (- p2_pre) (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist)).
        pose proof Z.le_min_l p2_pre (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min p2_pre (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist))) as tmp2 eqn:H2000.
        remember (Z.min p2_pre (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
Qed.

Lemma proof_of_clause_gen_unary_which_implies_wit_1 : clause_gen_unary_which_implies_wit_1.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_80 : clause_gen_binary_safety_wit_80.
Proof.
  pre_process.
  entailer!.
  destruct bop; simpl in * ; try lia.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_1 : clause_gen_binary_return_wit_1.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H27 into H24.
  rename H28 into H25.
  rename H29 into H26.
  rename H30 into H27.
  pose proof store_cnf_list_fold.
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) retval_4); try easy.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_3); try easy.
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_2); try easy.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval); try easy.
  clear H28.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_7); try easy.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_8); try easy.
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) y); try easy.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval_6); try easy.
  clear H28.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H28 retval_8 y ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) clist); try easy.
  sep_apply (H28 retval_7 retval_8 ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) (((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  sep_apply (H28 retval_6 retval_7 ((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) (((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++
  ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  sep_apply (H28 retval_5 retval_6 ((p1_pre :: p2_pre :: p3_pre :: nil) :: nil) (((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) ++
  ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++ ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); try easy.
  unfold store_predata.
  Exists retval_5.
  assert (bop = SMTPROP_IFF). {
    destruct bop; unfold SmtPBID in *; try lia.
    reflexivity.
  }
  rewrite H37.
  unfold iff2cnf_length_binary, iff2cnf_binary.
  destruct (p1_pre ==? p2_pre); try contradiction.
  assert (Zlength
  (((p1_pre :: p2_pre :: p3_pre :: nil)
    :: (- p1_pre :: - p2_pre :: p3_pre :: nil)
       :: (p1_pre :: - p2_pre :: - p3_pre :: nil)
          :: (- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist) = 
              ccnt + 4). {
    pose proof app_comm_cons.
    repeat rewrite <- H38.
    pose proof Zlength_cons.
    repeat rewrite H39.
    unfold app.
    rewrite H3.
    lia.
  }
  rewrite H38.
  clear H38 H28 H H0 H1 H24 H25 H26.
  assert (prop_cnt_inf
  (((p1_pre :: p2_pre :: p3_pre :: nil)
    :: (- p1_pre :: - p2_pre :: p3_pre :: nil)
       :: (p1_pre :: - p2_pre :: - p3_pre :: nil)
          :: (- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist) <= pcnt). {
    pose proof prop_cnt_nneg clist.
    clear H29 H30 H31 H32 H33 H34 H35 H36.
    assert (pcnt >= 1) by lia.
    assert (prop_cnt_inf clist <= pcnt - 1) by lia.
    unfold prop_cnt_inf in H1.
    pose proof Z.max_lub_l _ _ _ H1.
    pose proof Z.max_lub_r _ _ _ H1.
    unfold prop_cnt_inf.
    apply Z.max_lub.
    + simpl.
      repeat apply Z.max_lub; try lia.
    + simpl.
      apply Z.abs_le.
      split.
      - repeat apply Z.min_glb; try lia.
      - pose proof Z.le_min_l (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0))) (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0)))
        (Z.min (Z.min p1_pre (Z.min (- p2_pre) (Z.min (- p3_pre) 0)))
           (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))).
        pose proof Z.le_min_l p1_pre (Z.min p2_pre (Z.min p3_pre 0)).
        remember (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0)))
        (Z.min (Z.min (- p1_pre) (Z.min (- p2_pre) (Z.min p3_pre 0)))
           (Z.min (Z.min p1_pre (Z.min (- p2_pre) (Z.min (- p3_pre) 0)))
              (Z.min (Z.min (- p1_pre) (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))))) as tmp2 eqn:H2000.
        remember (Z.min p1_pre (Z.min p2_pre (Z.min p3_pre 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  repeat rewrite <- app_comm_cons.
  unfold app.
  clear - H H2 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_6 : clause_gen_binary_return_wit_6.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_OR). {
    destruct bop; unfold SmtPBID in *;  try lia.
    reflexivity.
  }
  clear H23 H27.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H28 into H25.
  remember ((p1_pre :: - p3_pre :: 0 :: nil)) as c1 eqn:H_c1.
  remember ((- p2_pre :: p3_pre :: 0 :: nil)) as c2 eqn:H_c2.
  remember ((- p1_pre :: p3_pre :: 0 :: nil)) as c3 eqn:H_c3.
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
      - pose proof Z.le_min_l (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist))).
        pose proof Z.le_min_l (- p1_pre) (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min (- p3_pre) (Z.min 0 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_5 : clause_gen_binary_return_wit_5.
Proof.
  pre_process.
  rewrite all_zero_list_3.
  repeat rewrite replace_0th.
  repeat rewrite replace_1st.
  repeat rewrite replace_2nd.
  assert (bop = SMTPROP_OR). {
    destruct bop; unfold SmtPBID in *; try contradiction; try lia.
    reflexivity.
  }
  clear H23 H27.
  rename H24 into Hs1.
  rename H25 into Hs2.
  rename H26 into Hs3.
  rename H28 into H25.
  remember (p1_pre :: p2_pre :: - p3_pre :: nil) as c1 eqn:H_c1.
  remember (- p2_pre :: p3_pre :: 0 :: nil) as c2 eqn:H_c2.
  remember (- p1_pre :: p3_pre :: 0 :: nil) as c3 eqn:H_c3.
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
      - pose proof Z.le_min_l (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist))).
        pose proof Z.le_min_l (- p1_pre) (Z.min p3_pre (Z.min 0 0)).
        remember (Z.min (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0)))
        (Z.min (Z.min (- p2_pre) (Z.min p3_pre (Z.min 0 0)))
           (Z.min (Z.min p1_pre (Z.min p2_pre (Z.min (- p3_pre) 0))) (min_cnf clist)))) as tmp2 eqn:H2000.
        remember (Z.min (- p1_pre) (Z.min p3_pre (Z.min 0 0))) as tmp1 eqn:H1000.
        clear H1000 H2000.
        lia.
  }
  clear - H2 H31 Hs1 Hs2 Hs3.
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_return_wit_4 : clause_gen_binary_return_wit_4.
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

Lemma proof_of_clause_gen_binary_return_wit_3 : clause_gen_binary_return_wit_3.
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

Lemma proof_of_clause_gen_binary_return_wit_2 : clause_gen_binary_return_wit_2.
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

Lemma proof_of_clause_gen_binary_return_wit_8 : clause_gen_binary_return_wit_8.
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

Lemma proof_of_clause_gen_binary_return_wit_7 : clause_gen_binary_return_wit_7.
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

Lemma proof_of_clause_gen_binary_safety_wit_97 :
  clause_gen_binary_safety_wit_97.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_99 : clause_gen_binary_safety_wit_99.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_125 : clause_gen_binary_safety_wit_125.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.


Lemma proof_of_clause_gen_binary_safety_wit_127 : clause_gen_binary_safety_wit_127.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_129 : clause_gen_binary_safety_wit_129.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_131 : clause_gen_binary_safety_wit_131.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_133 : clause_gen_binary_safety_wit_133.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
  entailer!.
Qed.

Lemma proof_of_clause_gen_binary_safety_wit_135 : clause_gen_binary_safety_wit_135.
Proof.
  pre_process.
  pose proof (Zlength_nonneg clist).
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

Lemma proof_of_prop2cnf_safety_wit_9 : prop2cnf_safety_wit_9.
Proof.
  pre_process.
  entailer!.
  destruct prop; simpl in * ; try lia.
Qed.

Lemma proof_of_prop2cnf_return_wit_1 : prop2cnf_return_wit_1.
Proof.
  pre_process.
  clear H8 H7.
  rename H4 into Hs1.
  rename H5 into Hs2.
  rename H6 into Hs3.
  rename H9 into H4.
  Exists clist pcnt ccnt var.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!; rewrite H in *.
  2: {
    pose proof SmtProp_size_nonneg (SmtV var).
    lia.
  }
  2: {
    pose proof SmtProp_size_nonneg (SmtV var).
    lia.
  }
  + unfold SmtPTID, store_SmtProp.
    unfold SmtPTID.
    entailer!.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + rewrite prop_cnt_inf_var in *.
    lia.
  + unfold make_predata, make_prop2cnf_ret.
    unfold prop2cnf_logic.
    reflexivity.
Qed.

Opaque Z.add Z.sub Z.mul Z.opp Z.of_nat Z.of_N Z.succ.

Lemma proof_of_prop2cnf_return_wit_2 : prop2cnf_return_wit_2.
Proof.
  pre_process.
  clear H25.
  rewrite H18 in *.
  unfold SmtPTID in *.
  clear H26.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_unary.
  repeat rewrite <- app_comm_cons.
  unfold app.
  remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
  remember (- p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
  Exists (c1 :: c2 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 2) (pcnt'_2 + 1) y0.
  entailer!.
  1: {
    simpl store_SmtProp.
    subst.
    Exists v.
    entailer!.
  }
  2: {
    simpl SmtProp_size.
    repeat rewrite Zlength_cons.
    pose proof SmtProp_size_nonneg sub_prop'.
    lia.
  }
  2: {
    unfold make_prop2cnf_ret, make_predata.
    simpl.
    remember (prop2cnf_logic (sub_prop') (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
    destruct step1 as [data1 p1''].  
    destruct data1 as [tmp clause_cnt].
    destruct tmp as [cnf_res prop_cnt].
    unfold make_prop2cnf_ret, make_predata in H11.
    rewrite <- H11 in Hstep1.
    inversion Hstep1.
    subst.
    reflexivity.
  }
  (* unfold make_prop2cnf_ret, make_predata in H5. *)
  unfold prop_cnt_inf.
  unfold prop_cnt_inf in H9.
    pose proof Z.max_lub_l _ _ _ H9.
    pose proof Z.max_lub_r _ _ _ H9.
  apply Z.max_lub; rewrite H_c1, H_c2.
  + simpl.
    assert (p1 <= pcnt'_2 + 1) by lia.
    assert (- p1 <= pcnt'_2 + 1) by lia.
    assert (0 <= pcnt'_2 + 1) by lia.
    assert (max_cnf clist'_2 <= pcnt'_2 + 1) by lia.
    repeat apply Z.max_lub; try lia.
  + simpl.
    apply Z.abs_le.
    split.
    - 
      repeat apply Z.min_glb; try lia.
    - 
      pose proof Z.le_min_l (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
      (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2)).
      pose proof Z.le_min_l p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
      remember (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
      (Z.min (Z.min (- p1) (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))) as tmp1 eqn:H1000.
      remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
      clear H1000.
      clear H2000.
      lia.
Qed.

Lemma proof_of_prop2cnf_return_wit_3 : prop2cnf_return_wit_3.
Proof.
  pre_process.
  rename H into Hs.
  rename H0 into Hs0.
  rename H1 into Hs1.
  rename H2 into Hs2.
  rename H5 into Hs3.
  rename H6 into Hs4.
  rename H15 into Hs5.
  rename H16 into Hs6.
  rename H23 into Hs7.
  rename H24 into Hs8.
  rename H31 into Hs9.
  rename H32 into Hs10.
  rename H33 into Hs11.
  rename H25 into Hs12.
  rename H26 into Hs13.
  rename H3 into H.
  rename H4 into H0.
  rename H7 into H1.
  rename H8 into H2.
  rename H9 into H3.
  rename H10 into H4.
  rename H11 into H5.
  rename H12 into H6.
  rename H13 into H7.
  rename H14 into H8.
  rename H17 into H11.
  rename H18 into H10.
  rename H19 into H9.
  rename H20 into H12.
  rename H21 into H13.
  rename H22 into H14.
  rename H27 into H15.
  rename H28 into H16.
  rename H29 into H17.
  rename H30 into H18.
  rename H34 into H19.
  rename H35 into H20.
  rename H36 into H21.
  rename H37 into H22.
  rewrite H15 in *.
  unfold SmtPTID in *.
  clear H19.
  unfold store_predata.
  Intros y0.
  unfold iff2cnf_binary, iff2cnf_length_binary.
  destruct op'; destruct (p1 ==? p2);
  repeat rewrite <- app_comm_cons;
  unfold app.
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)).
        remember (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c1 eqn:H_c1.
    remember (p2 :: - (pcnt'_2 + 1) :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)).
        remember ( Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
        (Z.min (Z.min p2 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - (pcnt'_2 + 1) :: 0 :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min (- (pcnt'_2 + 1)) (Z.min 0 0))) (min_cnf clist'_2))) ) as tmp1 eqn:H1000.
        remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (- p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1''].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min p1 (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min (- p1) (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      rewrite Zlength_cons, H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_r (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2).
        remember (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  + remember (p1 :: pcnt'_2 + 1 :: 0 :: nil) as c1 eqn:H_c1.
    remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    Exists (c1 :: c2 :: c3 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 3) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2))).
        pose proof Z.le_min_l p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)).
        remember (Z.min (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
        (Z.min (Z.min (- p2) (Z.min (pcnt'_2 + 1) (Z.min 0 0)))
           (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min (pcnt'_2 + 1) (Z.min 0 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
  + remember (pcnt'_2 + 1 :: 0 :: 0 :: nil) as c1 eqn:H_c1.
    (* remember (- p2 :: pcnt'_2 + 1 :: 0 :: nil) as c2 eqn:H_c2.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3. *)
    Exists (c1 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 1) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_r (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2).
        remember (Z.min (Z.min (pcnt'_2 + 1) (Z.min 0 (Z.min 0 0))) (min_cnf clist'_2)) as tmp1 eqn:H1000.
        clear H1000.
        lia.
  + remember (p1 :: p2 :: pcnt'_2 + 1 :: nil) as c1 eqn:H_c1.
    remember (- p1 :: - p2 :: pcnt'_2 + 1 :: nil) as c2 eqn:H_c2.
    remember (p1 :: - p2 :: - (pcnt'_2 + 1) :: nil) as c3 eqn:H_c3.
    remember (- p1 :: p2 :: - (pcnt'_2 + 1) :: nil) as c4 eqn:H_c4.
    Exists (c1 :: c2 :: c3 :: c4 :: clist'_2) (pcnt'_2 + 1) (ccnt'_2 + 4) (pcnt'_2 + 1) y0.
    entailer!.
    1: {
      simpl store_SmtProp.
      subst.
      Exists v_2 v.
      simpl.
      entailer!.
    }
    2: {
      repeat rewrite Zlength_cons.
      lia.
    }
    2: {
      repeat rewrite Zlength_cons.
      rewrite H2.
      lia.
    }
    2: {
      unfold make_prop2cnf_ret, make_predata.
      simpl.
      remember (prop2cnf_logic lt' (clist, pcnt, ccnt)) as step1 eqn:Hstep1.
      destruct step1 as [data1 p1'].
      remember (prop2cnf_logic rt' data1) as step2 eqn:Hstep2.
      destruct step2 as [tmp clause_cnt].
      destruct tmp as [cnf_res prop_cnt].
      destruct cnf_res as [cnf_res0 prop_cnt0].
      unfold make_prop2cnf_ret, make_predata in H5, H9.
      rewrite <- H9 in Hstep1.
      inversion Hstep1.
      rewrite H26 in Hstep2.
      rewrite <- H5 in Hstep2.
      inversion Hstep2.
      destruct (p1 ==? p2); try contradiction.
      subst.
      reflexivity.
    }
    unfold prop_cnt_inf.
    unfold prop_cnt_inf in H3.
    pose proof Z.max_lub_l _ _ _ H3.
    pose proof Z.max_lub_r _ _ _ H3.
    unfold make_prop2cnf_ret, make_predata in H5.
    pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H5.
    apply Z.max_lub; rewrite H_c1, H_c2, H_c3, H_c4.
    - simpl.
      repeat apply Z.max_lub; try lia.
    - simpl.
      apply Z.abs_le.
      split.
      * 
        repeat apply Z.min_glb; try lia.
      * 
        pose proof Z.le_min_l (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
        (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
           (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
              (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) .
        pose proof Z.le_min_l p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)).
        remember (Z.min (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0)))
        (Z.min (Z.min (- p1) (Z.min (- p2) (Z.min (pcnt'_2 + 1) 0)))
           (Z.min (Z.min p1 (Z.min (- p2) (Z.min (- (pcnt'_2 + 1)) 0)))
              (Z.min (Z.min (- p1) (Z.min p2 (Z.min (- (pcnt'_2 + 1)) 0))) (min_cnf clist'_2)))) ) as tmp1 eqn:H1000.
        remember (Z.min p1 (Z.min p2 (Z.min (pcnt'_2 + 1) 0))) as tmp2 eqn:H2000.
        clear H1000.
        clear H2000.
        lia.
Qed.

Lemma proof_of_prop2cnf_partial_solve_wit_19_pure : prop2cnf_partial_solve_wit_19_pure.
Proof.
  pre_process.
  rewrite H25 in *.
  unfold make_predata, make_prop2cnf_ret in H9.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H9.
  assert (p1 <= pcnt'_2 + 1) by lia.
  assert (- p1 <= pcnt'_2 + 1) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_1 : prop2cnf_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply store_SmtProp_unfold.
  Exists (SmtPTID prop).
  entailer!.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_2 : prop2cnf_which_implies_wit_2.
Proof.
  pre_process.
  rewrite H0.
  rewrite <- H, H0.
  sep_apply store_SmtProp'_Binary.
  Intros op lt rt y z.
  Exists z y op lt rt.
  entailer!.
  lia.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_3 : prop2cnf_which_implies_wit_3.
Proof.
  pre_process.
  rewrite H0 in H.
  pose proof prop_cnt_inf_Binary_l _ _ _ _ H.
  pose proof prop_cnt_inf_Binary_r _ _ _ _ H.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_4 : prop2cnf_which_implies_wit_4.
Proof.
  pre_process.
  rewrite H0 in H.
  simpl in H.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (SmtProp_size lt <= 10000) by lia.
  assert (SmtProp_size rt <= 10000) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_5 : prop2cnf_which_implies_wit_5.
Proof.
  pre_process.
  rewrite H0 in H.
  simpl in H.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (Zlength clist <= 40000 - 4 * SmtProp_size lt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_6 : prop2cnf_which_implies_wit_6.
Proof.
  pre_process.
  rewrite H0 in *.
  simpl in H.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (pcnt <= 40000 - SmtProp_size lt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_7 : prop2cnf_which_implies_wit_7.
Proof.
  pre_process.
  rewrite H1 in *.
  simpl in H0.
  pose proof SmtProp_size_nonneg lt.
  pose proof SmtProp_size_nonneg rt.
  assert (Zlength clist' <= 40000 - 4 * SmtProp_size rt) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_8 : prop2cnf_which_implies_wit_8.
Proof.
  pre_process.
  unfold make_predata, make_prop2cnf_ret in H.
  pose proof pcnt_upper_incr _ _ _ _ _ _ _ _ H.
  assert (prop_cnt_inf_SmtProp rt <= pcnt') by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_9 : prop2cnf_which_implies_wit_9.
Proof.
  pre_process.
  rewrite H1 in *.
  simpl in H0.
  pose proof SmtProp_size_nonneg lt.
  assert (pcnt' <= 39999 - SmtProp_size rt) by lia.
  entailer!.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_10 : prop2cnf_which_implies_wit_10.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
  pose proof prop_cnt_nneg clist'_2.
  lia.
Qed. 

Lemma proof_of_prop2cnf_which_implies_wit_11 : prop2cnf_which_implies_wit_11.
Proof.
  pre_process.
  rewrite H2 in *.
  simpl in H1.
  simpl.
  pose proof SmtProp_size_nonneg lt'.
  pose proof SmtProp_size_nonneg rt'.
  assert (pcnt'_2 <= pcnt + (1 + SmtProp_size lt' + SmtProp_size rt') - 1) by lia.
  assert (pcnt'_2 <= 39999) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_13 : prop2cnf_which_implies_wit_13.
Proof.
  pre_process.
  unfold store_predata.
  Exists y''.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_15 : prop2cnf_which_implies_wit_15.
Proof.
  pre_process.
  rewrite H1.
  simpl.
  assert (Zlength clist'_2 <= Zlength clist + 4 * (1 + SmtProp_size lt' + SmtProp_size rt') - 4) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_17 : prop2cnf_which_implies_wit_17.
Proof.
  pre_process.
  rewrite H0.
  rewrite <- H, H0.
  sep_apply store_SmtProp'_Unary.
  Intros op prop0 y.
  Exists y op prop0.
  entailer!.
  lia.
Qed. 


Lemma proof_of_prop2cnf_which_implies_wit_18 : prop2cnf_which_implies_wit_18.
Proof.
  pre_process.
  rewrite H0 in H.
  pose proof prop_cnt_inf_Unary_r _ _ _ H.
  entailer!.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_19 : prop2cnf_which_implies_wit_19.
Proof.
  pre_process.
  rewrite H0 in H.
  simpl in H.
  assert (SmtProp_size sub_prop <= 10000) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_20 : prop2cnf_which_implies_wit_20.
Proof.
  pre_process.
  rewrite H0 in H.
  simpl in H.
  pose proof SmtProp_size_nonneg sub_prop.
  assert (Zlength clist <= 40000 - 4 * SmtProp_size sub_prop) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_21 : prop2cnf_which_implies_wit_21.
Proof.
  pre_process.
  rewrite H0 in *.
  simpl in H.
  pose proof SmtProp_size_nonneg sub_prop.
  assert (pcnt <= 40000 - SmtProp_size sub_prop) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_22 : prop2cnf_which_implies_wit_22.
Proof.
  pre_process.
  unfold store_predata.
  Intros y.
  Exists y.
  entailer!.
  pose proof prop_cnt_nneg clist'.
  lia.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_23 : prop2cnf_which_implies_wit_23.
Proof.
  pre_process.
  rewrite H1 in *.
  simpl in H0.
  simpl.
  pose proof SmtProp_size_nonneg sub_prop'.
  assert (pcnt' <= pcnt + (1 + SmtProp_size sub_prop') - 1) by lia.
  assert (pcnt' <= 39999) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_25 : prop2cnf_which_implies_wit_25.
Proof.
  pre_process.
  unfold store_predata.
  Exists y''.
  entailer!.
Qed.


Lemma proof_of_prop2cnf_which_implies_wit_27 : prop2cnf_which_implies_wit_27.
Proof.
  pre_process.
  rewrite H0.
  simpl.
  assert (Zlength clist' <= Zlength clist + 4 * (1 + SmtProp_size sub_prop') - 4) by lia.
  entailer!.
Qed.

Lemma proof_of_prop2cnf_which_implies_wit_29 : prop2cnf_which_implies_wit_29.
Proof.
  pre_process.
  rewrite H.
  rewrite <- H0, H.
  sep_apply store_SmtProp'_Var.
  Intros var.
  Exists var.
  entailer!.
  lia.
Qed.
