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
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) retval_4) ; auto.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_3); auto.
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_2); auto.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval); auto.
  clear H28.
  pose proof @sllseg_len1 cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  sep_apply (H28 retval_6 (- p1_pre :: - p2_pre :: p3_pre :: nil) retval_7); auto.
  sep_apply (H28 retval_7 (p1_pre :: - p2_pre :: - p3_pre :: nil) retval_8); auto.
  sep_apply (H28 retval_8 (- p1_pre :: p2_pre :: - p3_pre :: nil) y); auto.
  sep_apply (H28 retval_5 (p1_pre :: p2_pre :: p3_pre :: nil) retval_6); auto.
  clear H28.
  pose proof @sllseg_sll cnf_list_cell store_cnf_list_cell "cnf_list" "next".
  unfold sll_cnf_list.
  sep_apply (H28 retval_8 y ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) clist); auto.
  sep_apply (H28 retval_7 retval_8 ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) (((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); auto.
  sep_apply (H28 retval_6 retval_7 ((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) (((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++
  ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); auto.
  sep_apply (H28 retval_5 retval_6 ((p1_pre :: p2_pre :: p3_pre :: nil) :: nil) (((- p1_pre :: - p2_pre :: p3_pre :: nil) :: nil) ++
  ((p1_pre :: - p2_pre :: - p3_pre :: nil) :: nil) ++ ((- p1_pre :: p2_pre :: - p3_pre :: nil) :: nil) ++ clist)); auto.
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