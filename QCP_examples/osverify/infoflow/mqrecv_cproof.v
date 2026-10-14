Require Import if_assms.
Require Import base_tac.
Require Import if_common_lemmas.
Require Import confidentiality_lemmas.
Require Import confidentiality_tactics.
Require Import ct_pp_lemmas.
Require Import equiv_prop. 
Require Import if_language.
Require Import if_opsem.
Require Import memory.
Require Import mqrecv_lemmas.
Require Import mq_apispecs.
Require Import osspecs. 
Require Import properties.
Require Import sem_prop. 
Require Import if_succ_gen.

Set Keyed Unification.
Lemma obsr_equiv_tskd_upd2_preserve'_lemma :
  forall td pr T1 T2 t1 t2 O1 O2 c1 c2 cd1 cd2
      ke ks1 ks2 vl vl1 vl2 cst1 cst2, 
    bind_all vl vl1 vl2 cd1 cd2 ->
    code_equiv_tskd td T1 T2 O1 O2 ->
    data_equiv_tskd td cst1 cst2 O1 O2 ->
    get T1 t1 = Some (c1, (ke, ks1)) ->
    get T2 t2 = Some (c2, (ke, ks2)) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    cont_equiv pr ks1 ks2 O1 O2 ->
    head_asrt_sat pr cd1 O1 ->
    head_asrt_sat pr cd2 O2 ->
    vl_equiv cd1 cd2 ->
    ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2) ->
    length vl = 4%nat ->
    length vl1 = 4%nat ->
    length vl2 = 4%nat ->
    (exists k, 
      nth_error (get_all_succs (mqreceive (vl ++ vl1))) k = Some cd1 /\
      nth_error (get_all_succs (mqreceive (vl ++ vl2))) k = Some cd2) ->
    code_equiv_tskd td (set T1 t1 (curs (hapi_code cd1), (ke, ks1))) 
      (set T2 t2 (curs (hapi_code cd2), (ke, ks2))) O1 O2 /\
      data_equiv_tskd td cst1 cst2 O1 O2. 
Proof.
  split.
  - eapply code_equiv_upd2_preserve'; eauto.
    right; do 2 eexists. splits; auto.
    right; split.
    + auto.
    + right; left.
      simpljoin.
      exists vl vl1 vl2 x.
      splits; auto.
  - auto.
Qed.
Ltac obsr_equiv_tskd_upd2_preserve' k :=
  join_Oeq;
  match goal with H: bind_all ?vl ?vl1 ?vl2 ?cd1 ?cd2 |- _ => 
    assert (exists k', 
      nth_error (get_all_succs (mqreceive (vl ++ vl1))) k' = Some cd1 /\
      nth_error (get_all_succs (mqreceive (vl ++ vl2))) k' = Some cd2 )
    by (exists k; splits; auto)
  end;
  eapply obsr_equiv_tskd_upd2_preserve'_lemma; simpl; eauto.

Lemma hidapistep_hidapistep_mqreceive_lemma:
forall
  (pc : progunit) (pr : priority) (i : taskdom) (act : action)
  (T1 T2 : tasks) (t1 t2 : addrval) (O1 O2 O1' O2' : osabst)
  (cst1' cst2' : clientst) (cd1 cd2 cd1' cd2' : spec_code)
  (ke : exprcont) (ks1 ks2 : stmtcont),
  get T1 t1 = Some (curs (hapi_code cd1), (ke, ks1)) ->
  get T2 t2 = Some (curs (hapi_code cd2), (ke, ks2)) ->
  nabt (set T1 t1 (curs (hapi_code cd1'), (ke, ks1))) ->
  nabt (set T2 t2 (curs (hapi_code cd2'), (ke, ks2))) ->
  reachable (pc, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1 ->
  reachable (pc, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  ~ in_intr T1 O1 ->
  ~ in_intr T2 O2 ->
  get O1 curtid = Some (oscurt t1) ->
  get O2 curtid = Some (oscurt t2) ->
  task_prio_id O1 pr t1 ->
  task_prio_id O2 pr t2 ->
  head_asrt_sat pr cd1 O1 ->
  head_asrt_sat pr cd2 O2 ->
  spec_step get_hprio_d cd1 O1 cd1' O1' act ->
  spec_step get_hprio_d cd2 O2 cd2' O2' act ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2) ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1 pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\ cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1 pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  no_common_fid pc (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2 ->
  ctid_equiv (dom_for_prio pr) O1 O2 ->
  ports_equiv (dom_for_prio pr) O1 O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
  kernel_task_equiv (dom_for_prio pr) O1 O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2 ->
  kernel_data_equiv (dom_for_prio pr) O1 O2 ->
  bufs_equiv (dom_for_prio pr) O1 O2 ->
  cap_equiv (dom_for_prio pr) O1 O2 ->
  cont_equiv pr ks1 ks2 O1 O2 ->
  vl_equiv cd1 cd2 ->
  (act = TauAct \/ act = SendAct \/ act = RecvAct) ->
  ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2) ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2 ->
  mqrecv_equiv cd1 cd2 ->
  code_equiv_tskd i (set T1 t1 (curs (hapi_code cd1'), (ke, ks1)))
    (set T2 t2 (curs (hapi_code cd2'), (ke, ks2))) O1' O2' /\
  data_equiv_tskd i cst1' cst2' O1' O2'. 
Proof.
  intros.
  rename H into HC1. rename H0 into HC2.
  rename H1 into Hnabt1. rename H2 into Hnabt2.
  rename H3 into Hrch1. rename H4 into Hrch2. 
  rename H5 into Hnint1. rename H6 into Hnint2.
  rename H7 into Hcurt1. rename H8 into Hcurt2.
  rename H9 into Htpi1. rename H10 into Htpi2.
  rename H11 into Hhsat1. rename H12 into Hhsat2.
  rename H13 into Hstep1. rename H14 into Hstep2.
  rename H15 into Hstepdm. rename H16 into Hfloweq. rename H17 into Hceq.
  rename H18 into Hfa. rename H19 into Hncfid. rename H20 into Hpu.
  rename H21 into Htmeq. rename H22 into Hsceq.
  rename H23 into Hd'eq. rename H24 into Hctideq. rename H25 into Hportseq.
  rename H26 into Hkmeq. rename H27 into Hkteq. rename H28 into Hcdeq.
  rename H29 into Hkdeq. rename H30 into Hbufseq. rename H31 into Hcapeq.
  rename H32 into Hconteq. rename H33 into Hvleq. rename H34 into Hact.
  rename H35 into Hnex. rename H36 into Htdeq. rename H37 into Hrecv.

  apply step1_lemma in Hstep1; apply step2_lemma in Hstep2.

  unfold obsr_equiv_tskd in Htdeq. 
  destruct Htdeq as (Hce & Hde).
  unfolds in Hsceq.
  unfolds in Hsceq.
  destruct Hsceq as (Hce_sch & Hde_sch).
  lets Hkmeq_sym: knl_mq_equiv_sym Hkmeq.
  lets Hkteq_sym: kernel_task_equiv_sym Hkteq.
  lets Hvleq_sym: vl_equiv_sym Hvleq.
  lets Hcapeq_sym: cap_equiv_sym Hcapeq.
  lets Hde_sch_sym: data_equiv_schd_sym Hde_sch.

  assert (Hnex':
    match (cd1', cd2') with
      (spec_done _, spec_done _) => True
    | (_, _) => ~ (exists vo1 vo2, cd1' = END vo1 /\ cd2' = END vo2)
    end).
  {
    destruct cd1'; try (unfolds; intros; simpljoin; congruence).
    destruct cd2'; try (unfolds; intros; simpljoin; congruence).
    auto.
  }

  apply Hfloweq in Hstepdm.

  unfolds in Hrecv.
  destruct Hrecv as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  
  assert (Hbind_all : bind_all vl vl1 vl2 cd1' cd2') by ( unfolds; apply n_block_cross_part).

  do 5 try destruct vl; tryfalse.
  do 5 try destruct vl1; tryfalse.
  do 5 try destruct vl2; tryfalse.

  simpl in Hnth1.
  destruct v;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).
  destruct v1;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).
  destruct v3;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).
  destruct v5;
    try (eapply abt_succs_contra in Hnth1; inverts Hstep1; tryfalse; fail).

  simpl in Hnth2.
  destruct v7;
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).
  destruct v9;
    try (eapply abt_succs_contra in Hnth2; inverts Hstep2; tryfalse; fail).
  

  rename i0 into mqd; rename v0 into msg_ptr;
  rename i1 into msg_len; rename v2 into msgprio;
  rename i2 into re_size1; rename v4 into rv_ptr1;
  rename i3 into rv_flag1; rename v6 into rv_post1;
  rename i4 into re_size2; rename v8 into rv_ptr2;
  rename i5 into rv_flag2; rename v10 into rv_post2.

  start k.
  (* k=0 *)
  { step1; step2; step1; step2. obsr_equiv_tskd_upd2_preserve' 1%nat. }

  start k. 
  (* k=1 *)
  {
    step1; step2.
    { step1; step2; rv_equal_end. }
    { congruence. }
    { congruence. }
    {
      step1; step2.
      { step1; step2; rv_equal_end. }
      { efalse dct_mid_false. }
      { efalse dct_mid_false. }
      {
        step1; step2; step1; step2.
        lets Htemp1: skip_Oeq H3; lets Htemp2: skip_Oeq H4. subst.
        obsr_equiv_tskd_upd2_preserve' 2%nat.
        - eapply mqd_in_cdom_holds; eauto.
        - eapply mqd_in_cdom_holds; eauto.
      }
    }
  }

  start k.
  (* k=2 *)
  {
    step1; step2; step1; step2.
    lets Htemp1: get_msize_Oeq H3; lets Htemp2: get_msize_Oeq H4. subst.
    obsr_equiv_tskd_upd2_preserve' 3%nat.
    - eapply veq_vlequiv; simpl; eauto.
      eapply mqequiv_get_msize_veq; eauto.
  }

  start k.
  (* k=3 *)
  {
    step1; step2.
    { step1; step2. rv_equal_end. }
    { vl_equiv_subst. }
    { vl_equiv_subst. }
    {
      step1; step2; step1; step2.
      lets Htemp1: skip_Oeq H3; lets Htemp2: skip_Oeq H4. subst.
      obsr_equiv_tskd_upd2_preserve' 4%nat.
      - apply vl_equiv_nil; auto.
    }
  }

  start k.
  (* k=4 *)
  {
    step1; step2.
    { step1; step2. rv_equal_end. }
    { congruence. }
    { congruence. }
    {
      step1; step2; step1; step2.
      lets Htemp1: ms_getep_Oeq H3; lets Htemp2: ms_getep_Oeq H4. subst.
      obsr_equiv_tskd_upd2_preserve' 5%nat.
      - eapply idm_getep_dom_qptr; eauto.
      - eapply idm_getep_dom_qptr; eauto.
    }
  }

  start k.
  (* k=5 *)
  {
    step1; step2.
    { step1; step2. rv_equal_end. }
    { efalse mq_equiv_null_false. }
    { efalse mq_equiv_null_false. }
    {
      step1; step2; step1; step2.
      lets Htemp1: skip_Oeq H3; lets Htemp2: skip_Oeq H4. subst.
      obsr_equiv_tskd_upd2_preserve' 6%nat.
    }
  }

  start k.
  (* k=6 *)
  {
    step1; step2; step1; step2.
    lets Htemp1: mqgf_Oeq H3; lets Htemp2: mqgf_Oeq H4. subst.
    obsr_equiv_tskd_upd2_preserve' 7%nat.
    - eapply veq_vlequiv; simpl; eauto.
      eapply mq_equiv_flg_veq; eauto.
  }

  start k.
  (* k=7 *)
  {
    step1; step2.
    { step1; step2. rv_equal_end. }
    { vl_equiv_subst. }
    { vl_equiv_subst. }
    {
      step1; step2.
      { step1; step2. rv_equal_end. }
      { vl_equiv_subst; efalse cap_equiv_recvcap_equiv. }
      { vl_equiv_subst; efalse cap_equiv_recvcap_equiv. }
      {
        step1; step2; step1; step2.
        lets Htemp1: skip_Oeq H3; lets Htemp2: skip_Oeq H4. subst.
        obsr_equiv_tskd_upd2_preserve' 8%nat.
      }
    }
  }

  start k.
  (* k=8 *)
  {
    step1. 
    { step1. }
    {
      step2.
      { step2. }
      {
        step1; step2.
        {
          obsr_equiv_tskd_upd2_preserve' 9%nat.
          - apply vl_equiv_nil; auto.
        }
        { vl_equiv_subst. }
        { vl_equiv_subst. }
        {
          obsr_equiv_tskd_upd2_preserve' 16%nat.
          - apply vl_equiv_nil; auto.
        }
      }
    }
  }

  start k.
  (* k=9 *)
  {
    step1.
    {
      step2.
      {
        step1.
        {
          step2.
          {
            step1; step2.
            {
              step1; step2.
              lets Htemp1: aar_Oeq H3; lets Htemp2: aar_Oeq H4. subst.
              lets Htemp1: aar_veq H3; lets Htemp2: aar_veq H4. subst.
              obsr_equiv_tskd_upd2_preserve' 17%nat.
              - apply vl_equiv_refl.
            }
            { efalse mq_equiv_null_false. }
            { efalse mq_equiv_null_false. }
            {
              qid_unique qid.

              step1.
              {
                false. eapply mq_equiv_noque_false.
                apply Hhsat1. apply Hhsat2. apply Hkmeq. simpljoin. do 2 eexists. splits; eauto.
              }
              {
                step2.
                {
                  false. eapply mq_equiv_noque_false.
                  apply Hhsat2. apply Hhsat1. apply Hkmeq_sym. simpljoin. do 2 eexists. splits; eauto.
                }
                {
                  step1; step2; step1; step2.
                  step1.
                  {
                    step2.
                    {
                      step1; step2.
                      split.
                      - lets Hpp1: qpend_nopwl_succ_prio_preserved v; specializes Hpp1; eauto.
                        lets Hpp2: qpend_nopwl_succ_prio_preserved v0; specializes Hpp2; eauto.
                        apply11 qpend_get_no_pwl_succ_body qpend_get_no_pwl_succ_body
                          qpend_get_no_pwl_succ_cpid_same Hcpeq2 Hcpeq1.
                        specializes Hcpeq1; eauto.
                        specializes Hcpeq2; eauto. 
                        eapply code_equiv_upd2_preserve_st'; eauto.
                        {
                          unfolds.
                          right.
                          do 2 eexists.
                          split; eauto. split; eauto.
                          split. simpl; auto.
                          split. simpl; auto.
                          split. eapply veq_vlequiv; simpl; eauto.
                          {
                            unfold qpend_get_no_pwl_succ_body in *.
                            simpljoin.
                            inverts H. inverts H0. inverts H1. inverts H2.
                            destruct H26; simpljoin; tryfalse.
                            destruct H36; simpljoin; tryfalse.
                            assert (get O1 absecblsid = Some (absecblist x24)).
                            { eapply join_sem1; eauto. }
                            assert (get O2 absecblsid = Some (absecblist x16)).
                            { eapply join_sem1; eauto. }
                            lets H_: mq_equiv_unfolded Hkmeq; eauto.
                            simpljoin. 
                            l_rew12_inv2 (get O1 absecblsid).
                            l_rew12_inv2 (get O2 absecblsid).
                            rewrite H22 in H32; inverts H32.
                            rewrite H26 in H18; inverts H18.
                            unfolds in H33.
                            simpljoin. 
                            inverts H18. inverts H19.
                            reflexivity.
                          }
                          unfolds.
                          right.
                          split. introv Hf; simpljoin; tryfalse.
                          right; left.
                          (* mqsend_equiv *)
                          unfolds. 
                          match type of Hlenvl with length ?vl = _ => exists vl end. 
                          match type of Hlenvl1 with length ?vl = _ => exists vl end.
                          match type of Hlenvl2 with length ?vl = _ => exists vl end.
                          exists 17%nat. splits; auto.
                        }
                        {
                          eapply cont_equiv_qref_preserve; eauto.
                          eapply qpend_get_no_pwl_succ_mqref_preserve; eauto.
                          eapply qpend_get_no_pwl_succ_mqref_preserve; eauto.
                          eapply qpend_get_no_pwl_succ_qprt_preserve; eauto. 
                          eapply qpend_get_no_pwl_succ_qprt_preserve; eauto.
                          eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
                          eapply eqdom_frm_domimpl; eauto.
                        }
                        {
                          lets H__: code_equiv_hsat_neq_st'; eauto.
                          eapply H__; eauto. 
                          eapply qpend_get_no_pwl_succ_mqref_preserve; eauto.
                          eapply qpend_get_no_pwl_succ_mqref_preserve; eauto. 
                          eapply qpend_get_no_pwl_succ_qprt_preserve; eauto. 
                          eapply qpend_get_no_pwl_succ_qprt_preserve; eauto.   
                          eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
                          eapply eqdom_frm_domimpl; eauto.
                        }
                      - eapply qpend_get_no_pwl_succ_body_dteq_preserve2; eauto.
                    }
                    { step2; step2; step2. }
                  }
                  { step1; step1; step1. }
                }
              }
            }
          }
        }
      }
      {
        step1; step2; step2.
        { step2. }
        {
          step1.
          { efalse mq_equiv_null_false. }
          {
            qid_unique qid.
            step2.
            { step2. }
            {
              step1.
              { efalse absmsgq_false. }
              {
                step1; step1; step1.
                {
                  step2; step2; step2.
                  { step2. }
                  { efalse absmsgq2_false. }
                }
                { step1; step1; step1. }
              }
            }
          }
        }
      }
    }
    {
      step2.
      {
        step2; step1; step1.
        { step1. }
        {
          step2.
          { efalse mq_equiv_null_false. }
          {
            qid_unique qid.
            step1.
            { step1. }
            {
              step2.
              { efalse absmsgq_false. }
              {
                step2; step2; step2.
                {
                  step1; step1; step1.
                  { step1. }
                  { efalse absmsgq2_false. }
                }
                { step2; step2; step2. }
              }
            }
          }
        }
      }
      {
        step1; step2; step1; step2; step1; step2;
        step1; step2; step1; step2; step1; step2.
        step1.  step1.  step2.

        qid_unique qid; step1; step2.
        {
          step1; step2; step1; step2. 
          split.
          - lets Hpp1: qpend_get_expwl_before_sched_prio_preserved O O'; eauto.
            specializes Hpp1; eauto.
            lets Hpp2: qpend_get_expwl_before_sched_prio_preserved O0 O'0; eauto.
            specializes Hpp2; eauto. 
            apply11 qpend_get_ex_pwl_before_sched_body qpend_get_ex_pwl_before_sched_body
            qpend_get_ex_pwl_before_sched_cpid_same Hcpeq2 Hcpeq1.
            specializes Hcpeq1; eauto.
            specializes Hcpeq2; eauto.

            eapply code_equiv_upd2_preserve_st'; eauto.
            {
              (* cmd_equiv *)
              unfolds.
              right.
              do 2 eexists.
              split; eauto. split; eauto.
              split. simpl; auto. split. simpl; auto.
              split.
              eapply veq_vlequiv; simpl; eauto.
              {
                unfold qpend_get_ex_pwl_before_sched_body in *.
                simpljoin.
                inverts H. inverts H0. inverts H1. inverts H2.
                destruct H34; simpljoin; tryfalse.
                destruct H44; simpljoin; tryfalse.
                assert (get O1 absecblsid = Some (absecblist x32)).
                { eapply join_sem1; eauto. }
                assert (get O2 absecblsid = Some (absecblist x17)).
                { eapply join_sem1; eauto. }
                lets H_: mq_equiv_unfolded Hkmeq; eauto.
                simpljoin. 
                l_rew12_inv2 (get O1 absecblsid).
                l_rew12_inv2 (get O2 absecblsid).
                rewrite H30 in H37; inverts H37.
                rewrite H31 in H6; inverts H6.
                unfolds in H34.
                simpljoin. 
                inverts H6. inverts H8.
                reflexivity.
              }
              unfolds. simpl.
              right.
              split. introv Hf. simpljoin. tryfalse.
              right; left.
              (* mqsend_equiv *)
              unfolds. 
              match type of Hlenvl with length ?vl = _ => exists vl end. 
              match type of Hlenvl1 with length ?vl = _ => exists vl end.
              match type of Hlenvl2 with length ?vl = _ => exists vl end.
              exists 10%nat. splits; auto.
            }
            eapply cont_equiv_qref_preserve; eauto. 
            eapply qpend_get_ex_pwl_before_sched_mqref_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_mqref_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_qprt_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_qprt_preserve; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            eapply eqdom_frm_domimpl; eauto.

            lets H__: code_equiv_hsat_neq_st'; eauto.
            eapply H__; eauto.
            eapply qpend_get_ex_pwl_before_sched_mqref_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_mqref_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_qprt_preserve; eauto.
            eapply qpend_get_ex_pwl_before_sched_qprt_preserve; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            eapply eqdom_frm_domimpl; eauto. 
          - (* data_equiv *)           
            eapply qpend_get_ex_pwl_before_sched_dteq_preserve2; eauto.
        }
        { efalse absmsgq3_false. }
        { efalse absmsgq3_false. }

        {
          step1; step2; step1; step2; step2; step1.
          split.
          - (* code_equiv *) 
            lets Hpp1: qpend_block_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
            specializes Hpp1; eauto.
            lets Hpp2: qpend_block_prio_preserved O O' Of O2 O2'; eauto.
            specializes Hpp2; eauto.
            apply11 qpend_block_body qpend_block_body
              qpend_block_cpid_same Hcpeq2 Hcpeq1.
            specializes Hcpeq1; eauto.
            specializes Hcpeq2; eauto. 

            eapply code_equiv_upd2_preserve_st'; eauto.
              
            (* cmd_equiv *)
            unfolds.
            right.
            do 2 eexists.
            split; eauto. split; eauto.
            split. simpl; auto.
            eapply qpend_block_mqd_impl; eauto. 
            split. simpl; auto.
            eapply qpend_block_mqd_impl with (O0:=O) (O0':=O'); eauto. 
            split.
            eapply vl_equiv_nil; eauto.
            unfolds.
            right.
            split. introv Hf. simpljoin. tryfalse.
            right; left.
            (* mqsend_equiv *)
            unfolds. 
            match type of Hlenvl with length ?vl = _ => exists vl end. 
            match type of Hlenvl1 with length ?vl = _ => exists vl end.
            match type of Hlenvl2 with length ?vl = _ => exists vl end.
            exists 12%nat. splits; auto.   
            
            (* cont_equiv *)
            eapply cont_equiv_qref_preserve; eauto.  
            eapply qpend_block_mqref_preserve; eauto. 
            eapply qpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto.
            eapply qpend_block_qprt_preserve; eauto. 
            eapply qpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            
            lets H__: code_equiv_hsat_neq_st'; eauto.
            eapply H__; eauto. 
            eapply qpend_block_mqref_preserve; eauto.
            eapply qpend_block_mqref_preserve with (O0:=O) (O0':=O'); eauto. 
            eapply qpend_block_qprt_preserve; eauto. 
            eapply qpend_block_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

          - (* data_equiv *)
            eapply qpend_block_dteq_preserve2 with (O10:=O0) (O20:=O); eauto.
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
        }
      }
    }
  }

  start k.
  (* k=10 *)
  {
    step1.
    { step1. }
    {
      step2.
      { step2. }
      {  step1; step2; step1; step2. obsr_equiv_tskd_upd2_preserve' 11%nat. }
    }
  }

  start k.
  (* k=11 *)
  {
    step1; step2; step1; step2.
    lets Htemp1: rv_Oeq H3; lets Htemp2: rv_Oeq H4. subst.
    obsr_equiv_tskd_upd2_preserve' 17%nat.
  }

  start k.
  (* k=12 *)
  {
    step1.
    { step1. }
    {
      step2.
      { step2. }
      { step1; step2; step1; step2. obsr_equiv_tskd_upd2_preserve' 13%nat. }
    }
  }

  start k.
  (* k=13 *)
  {
    step1; step2; step1; step2; step1; step2.
    lets Htemp1 : qst_Oeq H3; lets Htemp2 : qst_Oeq H4. subst.
    obsr_equiv_tskd_upd2_preserve' 14%nat.
  }

  start k.
  (* k=14 *)
  {
    step1; step2.
    {
      step1.
      { step1. }
      {
        step2.
        { step2. }
        {
          step1.
          {
            step2.
            {
              step2; step1.
              split.
              - (* code_equiv *) 
                lets Hpp1: qpend_block_get_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
                specializes Hpp1; eauto.
                lets Hpp2: qpend_block_get_prio_preserved O O' Of O2 O2'; eauto.
                specializes Hpp2; eauto.
                apply11 qpend_block_get_body qpend_block_get_body
                  qpend_block_get_cpid_same Hcpeq2 Hcpeq1.
                specializes Hcpeq1; eauto.
                specializes Hcpeq2; eauto. 

                eapply code_equiv_upd2_preserve_st'; eauto.
                  
                (* cmd_equiv *)
                unfolds.
                right.
                do 2 eexists.
                split; eauto. split; eauto.
                split. simpl; auto.
                split. simpl; auto.
                split. 
                {
                  clear H10; clear H9; clear H8; clear H11.
                  unfolds in Hkteq.
                  unfold qpend_block_get_body in *.
                  simpljoin.
                  assert (get O1 curtid = Some (oscurt x10)) by (eapply join_get_get_l; eauto).
                  assert (get O2 curtid = Some (oscurt x18)) by (eapply join_get_get_l; eauto).
                  l_rew21_inv1 (get O1 curtid).
                  l_rew21_inv1 (get O2 curtid).
                  assert (get O1 abstcblsid = Some (abstcblist x5)) by (eapply join_get_get_l; eauto).
                  assert (get O2 abstcblsid = Some (abstcblist x13)) by (eapply join_get_get_l; eauto).
                  l_rew21_inv1 (get O1 abstcblsid).
                  l_rew21_inv1 (get O2 abstcblsid).
                  specialize(H25 pr ltac:(tauto)).
                  destruct H25 as (_ & H25).
                  assert (task_prio_id O1 x12 t1) by (unfolds; do 5 eexists; split; eauto).
                  assert (task_prio_id O2 x20 t2) by (unfolds; do 5 eexists; split; eauto).
                  assert (x12 = pr) by (eapply prio_unique; eauto).
                  assert (x20 = pr) by (eapply prio_unique; eauto).
                  subst.
                  lets H_: H25 H4 H14.
                  inverts H. inverts H0.
                  destruct H10; simpljoin; tryfalse.
                  destruct H23; simpljoin; tryfalse.
                  apply vl_equiv_refl.
                }
                unfolds.
                right.
                split. introv Hf. simpljoin. tryfalse.
                right; left.
                (* mqsend_equiv *)
                unfolds. 
                match type of Hlenvl with length ?vl = _ => exists vl end. 
                match type of Hlenvl1 with length ?vl = _ => exists vl end.
                match type of Hlenvl2 with length ?vl = _ => exists vl end.
                exists 17%nat. splits; auto.
                
                (* cont_equiv *)
                eapply cont_equiv_qref_preserve; eauto.  
                eapply qpend_block_get_mqref_preserve; eauto. 
                eapply qpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto.
                eapply qpend_block_get_qprt_preserve; eauto. 
                eapply qpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
                eapply eqdom_frm_domimpl; eauto.
                eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
                
                lets H__: code_equiv_hsat_neq_st'; eauto.
                eapply H__; eauto. 
                eapply qpend_block_get_mqref_preserve; eauto.
                eapply qpend_block_get_mqref_preserve with (O0:=O) (O0':=O'); eauto. 
                eapply qpend_block_get_qprt_preserve; eauto. 
                eapply qpend_block_get_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
                eapply eqdom_frm_domimpl; eauto.
                eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

              - (* data_equiv *)
                eapply qpend_block_get_dteq_preserve2; eauto.
                eapply eqdom_frm_domimpl; eauto.
                eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            }
          }
        }
      }
    }
    {
      step2.
      { step1; step1; efalse os_stat_q_false. }
      { step2; step2. }
    }
    {
      step1. 
      { step2; step2; efalse os_stat_q_false. }
      { step1; step1. }
    }
    {
      step1.
      {
        step2. 
        {
          step1; step2; step2; step1.
          split.
          - (* code_equiv *) 
            lets Hpp1: qpend_to_body_prio_preserved O0 O'0 Of0 O1 O1'; eauto. 
            specializes Hpp1; eauto.
            lets Hpp2: qpend_to_body_prio_preserved O O' Of O2 O2'; eauto.
            specializes Hpp2; eauto.
            apply11 qpend_to_body qpend_to_body
              qpend_to_cpid_same Hcpeq2 Hcpeq1.
            specializes Hcpeq1; eauto.
            specializes Hcpeq2; eauto. 

            eapply code_equiv_upd2_preserve_st'; eauto.
              
            (* cmd_equiv *)
            unfolds.
            right.
            do 2 eexists.
            split; eauto. split; eauto.
            split. simpl; auto.
            split. simpl; auto.
            split.
            {
              unfold qpend_to_body in *.
               simpljoin. inverts H. inverts H0.
              destruct H30; simpljoin; tryfalse.
              destruct H19; simpljoin; tryfalse.
              subst.
              apply vl_equiv_refl.
            }
            unfolds.
            right.
            split. introv Hf. simpljoin. tryfalse.
            right; left.
            (* mqsend_equiv *)
            unfolds. 
            match type of Hlenvl with length ?vl = _ => exists vl end. 
            match type of Hlenvl1 with length ?vl = _ => exists vl end.
            match type of Hlenvl2 with length ?vl = _ => exists vl end.
            exists 15%nat. splits; auto.
            
            (* cont_equiv *)
            eapply cont_equiv_qref_preserve; eauto.  
            eapply qpend_to_mqref_preserve; eauto. 
            eapply qpend_to_mqref_preserve with (O0:=O) (O0':=O'); eauto.
            eapply qpend_to_qprt_preserve; eauto. 
            eapply qpend_to_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
            
            lets H__: code_equiv_hsat_neq_st'; eauto.
            eapply H__; eauto. 
            eapply qpend_to_mqref_preserve; eauto.
            eapply qpend_to_mqref_preserve with (O0:=O) (O0':=O'); eauto. 
            eapply qpend_to_qprt_preserve; eauto. 
            eapply qpend_to_qprt_preserve with (O0:=O) (O0':=O'); eauto.   
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 

          - (* data_equiv *)
            eapply qpend_to_dteq_preserve2; eauto.
            eapply eqdom_frm_domimpl; eauto.
            eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
          }
        { step2; step2. }
      }
      { step1; step1. }
    }
  }

  start k.
  (* k=15 *)
  {
    step1; step2; step1; step2.
    lets Htemp1: aar_Oeq H3; lets Htemp2: aar_Oeq H4. subst.
    lets Htemp1: aar_veq H3; lets Htemp2: aar_veq H4. subst.
    obsr_equiv_tskd_upd2_preserve' 17%nat.
  }

  start k.
  (* k=16 *)
  {
    step1.
    {
      step2.
      {
        step1; step2. 
        {
          step1. step2.
          lets Htemp1: aar_Oeq H3; lets Htemp2: aar_Oeq H4. subst.
          lets Htemp1: aar_veq H3; lets Htemp2: aar_veq H4. subst.
          obsr_equiv_tskd_upd2_preserve' 17%nat.
          - apply vl_equiv_refl.
        }
        { efalse mq_equiv_null_false. }
        { efalse mq_equiv_null_false. }
        { 
          
          qid_unique qid.
          step1; step2.
          {
            step1. step2.
            lets Htemp1: aar_Oeq H3; lets Htemp2: aar_Oeq H4. subst.
            lets Htemp1: aar_veq H3; lets Htemp2: aar_veq H4. subst.
            obsr_equiv_tskd_upd2_preserve' 17%nat.
            - apply vl_equiv_refl.
          }
          { efalse absmsgq4_false. }
          { efalse absmsgq4_false. }
          {
            step1; step2.
            {
              step1. step2.
              lets Htemp1: aar_Oeq H3; lets Htemp2: aar_Oeq H4. subst.
              lets Htemp1: aar_veq H3; lets Htemp2: aar_veq H4. subst.
              obsr_equiv_tskd_upd2_preserve' 17%nat.
              - apply vl_equiv_refl.
            }
            { efalse absmsgq5_false. }
            { efalse absmsgq5_false. }
            {
              step1.
              {
                step2.
                {
                  step1; step2.
                  split.
                  - lets Hpp1: aqcc_succ_prio_preserved  O O'; eauto.
                    specializes Hpp1; eauto.
                    lets Hpp2: aqcc_succ_prio_preserved O0 O'0; eauto.
                    specializes Hpp2; eauto.
                    apply11 qacc_succ_body qacc_succ_body
                      qacc_succ_cpid_same Hcpeq2 Hcpeq1.
                    specializes Hcpeq1; eauto.
                    specializes Hcpeq2; eauto. 
                    eapply code_equiv_upd2_preserve_st'; eauto.
                    {
                      unfolds.
                      right.
                      do 2 eexists.
                      split; eauto. split; eauto.
                      split. simpl; auto.
                      split. simpl; auto.
                      split. eapply veq_vlequiv; simpl; eauto.
                      {
                        unfold qacc_succ_body in *.
                        simpljoin.
                        destruct H26; simpljoin; tryfalse.
                        destruct H15; simpljoin; tryfalse.
                        inverts H. inverts H0. inverts H1. inverts H2.
                        assert (get O1 absecblsid = Some (absecblist x21)).
                        { eapply join_sem1; eauto. }
                        assert (get O2 absecblsid = Some (absecblist x15)).
                        { eapply join_sem1; eauto. }
                        lets H_: mq_equiv_unfolded Hkmeq; eauto.
                        simpljoin. 
                        l_rew12_inv2 (get O1 absecblsid).
                        l_rew12_inv2 (get O2 absecblsid).
                        rewrite H3 in H23; inverts H23.
                        rewrite H17 in H14; inverts H14.
                        unfolds in H18.
                        simpljoin. 
                        inverts H1. inverts H2.
                        reflexivity.
                      }
                      unfolds.
                      right.
                      split. introv Hf; simpljoin; tryfalse.
                      right; left.
                      (* mqsend_equiv *)
                      unfolds. 
                      match type of Hlenvl with length ?vl = _ => exists vl end. 
                      match type of Hlenvl1 with length ?vl = _ => exists vl end.
                      match type of Hlenvl2 with length ?vl = _ => exists vl end.
                      exists 17%nat. splits; auto.
                    }
                    {
                      eapply cont_equiv_qref_preserve; eauto.
                      eapply qacc_succ_mqref_preserve; eauto.
                      eapply qacc_succ_mqref_preserve; eauto.
                      eapply qacc_succ_qprt_preserve; eauto. 
                      eapply qacc_succ_qprt_preserve; eauto.
                      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto.
                      eapply eqdom_frm_domimpl; eauto.
                    }
                    {
                      lets H__: code_equiv_hsat_neq_st'; eauto.
                      eapply H__; eauto. 
                      eapply qacc_succ_mqref_preserve; eauto.
                      eapply qacc_succ_mqref_preserve; eauto. 
                      eapply qacc_succ_qprt_preserve; eauto. 
                      eapply qacc_succ_qprt_preserve; eauto.   
                      eapply eqdom_frm_domimpl with (O10:=O) (O20:=O'); eauto. 
                      eapply eqdom_frm_domimpl; eauto.
                    }
                  - eapply qacc_succ_body_dteq_preserve2; eauto.
                }
              }
            }
          }
        }
      }
      { step2; step2; step2; step2; step2. }
    }
    { step1; step1; step1; step1; step1. }
  }


  start k.
  (* k=17 *)
  {
    step1; step2.
    { step1; step2; rv_equal_end. }
    { efalse rv_post_null_false. }
    { efalse rv_post_null_false. }
    {
      step1; step2; step1; step2.
      lets Htemp1: me_Oeq H3; lets Htemp2: me_Oeq H4. subst.
      obsr_equiv_tskd_upd2_preserve' 18%nat.
      - apply vl_equiv_refl.
    }
  }

  start k.
  (* k=18 *)
  { step1; step2; eapply rv_equal_end_lemma; eauto. }
  
  start k.
  (* k=19 *)
  inverts Hnth1.

  Unshelve.
  trivial.
  trivial.
Qed.

     
