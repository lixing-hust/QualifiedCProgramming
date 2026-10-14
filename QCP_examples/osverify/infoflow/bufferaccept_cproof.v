Require Import if_assms.
Require Import base_tac.
Require Import buffer_apispecs.
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
Require Import spec_aux_defs.
Require Import if_succ_gen.

Set Keyed Unification.
Set Nested Proofs Allowed. 

Lemma obsr_equiv_tskd_upd2_preserve'_lemma:
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
    length vl = 1%nat ->
    length vl1 = 1%nat ->
    length vl2 = 1%nat ->
    (exists k, 
      nth_error (get_all_succs (bufferaccept (vl ++ vl1))) k = Some cd1 /\
      nth_error (get_all_succs (bufferaccept (vl ++ vl2))) k = Some cd2) ->
    code_equiv_tskd td (set T1 t1 (curs (hapi_code cd1), (ke, ks1))) 
      (set T2 t2 (curs (hapi_code cd2), (ke, ks2))) O1 O2 /\
      data_equiv_tskd td cst1 cst2 O1 O2. 
Proof.
  split.
  - eapply code_equiv_upd2_preserve'; eauto.
    right; do 2 eexists. splits; auto.
    right; split.
    + auto.
    + right; right; right; right; right; right; right; right; left.
      destruct H14 as (k & Hnth1 & Hnth2).
      exists vl vl1 vl2 k.
      splits; auto.
  - auto.
Qed.
Ltac obsr_equiv_tskd_upd2_preserve' k :=
  join_Oeq;
  match goal with H: bind_all ?vl ?vl1 ?vl2 ?cd1 ?cd2 |- _ => 
    assert (exists k', 
      nth_error (get_all_succs (bufferaccept (vl ++ vl1))) k' = Some cd1 /\
      nth_error (get_all_succs (bufferaccept (vl ++ vl2))) k' = Some cd2 )
    by (exists k; splits; auto)
  end;
  eapply obsr_equiv_tskd_upd2_preserve'_lemma; simpl; eauto.
    
Lemma dct_bid_false:
  forall O1' O2' vp,
    (forall (td : taskdom) (eid : addrval),
        spec_aux_defs.dom_cur_tsk O1' td ->
        vp = Vptr eid -> spec_aux_defs.buf_in_dom eid td = false) ->
    ~ ((forall (td : taskdom) (eid : addrval),
           spec_aux_defs.dom_cur_tsk O2' td ->
           vp = Vptr eid -> spec_aux_defs.buf_in_dom eid td = false)) ->
    data_equiv_schd O1' O2' ->
    False.
Proof.
  introv Ht Hf Hdeqs; apply Hf. introv Hdct.
  lets H: data_equiv_schd_dom_equiv Hdeqs.
  specialize (H td); destruct H as (_ & H).
  apply H in Hdct. auto.
Qed.
Lemma n_buf_in_dom_false_dest:
  forall vp O pr t,
    task_prio_id O pr t ->
    get O curtid = Some (oscurt t) -> 
    (~ (forall (td : taskdom) (eid : addrval),
           spec_aux_defs.dom_cur_tsk O td ->
           vp = Vptr eid -> spec_aux_defs.buf_in_dom eid td = false)) ->
    vp = Vnull \/ (exists a, vp = Vptr a) -> 
    buffer_indom vp O pr. 
Proof.
  introv Htpi Hcurt Hf H.
  unfolds.
  destruct H as [H | (a & H)].
  - left; auto.
  - right; exists a.
    split; auto.
    destruct (buf_in_dom a (dom_for_prio pr)) eqn: E.
    + auto.
    + false; apply Hf.
      introv Hdct H2.
      subst; inverts H2.
      unfolds in Hdct.
      destruct Hdct as (t' & pr' & Hcurt' & Htpi' & Hdfp).
      l_rew21_inv1 (get O curtid).
      apply2 (task_prio_id O) (task_prio_id O) prio_unique.
      auto. 
Qed. 
Lemma buffer_equiv_noque_false_: 
    forall vp O1 O2 pr, 
      buffer_equiv (dom_for_prio pr) O1 O2 ->
      buffer_indom vp O1 pr -> 
      (exists qid els,
          vp = Vptr qid /\
            get O1 absecblsid = Some (absecblist els) /\
            ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
      (exists qid els,
          vp = Vptr qid /\
            get O2 absecblsid = Some (absecblist els) /\
            ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))). 
  Proof.
    introv Hbe Hbi1 Hex.
    unfolds in Hbe.
    simpljoin.
    unfolds in Hbi1.
    rem_dis.
    match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
    match goal with H: forall _, _ |- _ => specializes H; eauto end.
    l_rew12_inv2 (get O1 absecblsid).
    simpljoin.
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hex.
    match goal with H: ~_ |- _ => apply H end.
    match goal with
      H1: context [absecblist ?x1], H2: context [absecblist ?x2] |- _ =>
        rename x1 into els1; rename x2 into els2
    end.
    match goal with H: buf_in_dom ?x _ = true |- _ => rename x into eid end.
    simpljoin.
    assert (Hex: exists ed ws, get els2 eid = Some (ed, ws))
      by (do 2 eexists; eauto).
    match goal with H: _ <-> _ |- _ => apply H in Hex end.
    simpljoin.
    match goal with H: forall _, _ |- _ => specializes H; eauto end.
    simpljoin.
    unfold mq_ed_equiv in *.
    simpljoin.
    do 4 eexists; eauto. 
  Qed.
Lemma buffer_equiv_noque_false: 
    forall vp O1 O2 pr, 
      (exists qid els,
          vp = Vptr qid /\
            get O1 absecblsid = Some (absecblist els) /\
            ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
      ~(exists qid els,
            vp = Vptr qid /\
              get O2 absecblsid = Some (absecblist els) /\
              ~ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl, wls))) ->
      buffer_equiv (dom_for_prio pr) O1 O2 ->
      buffer_indom vp O1 pr -> 
      False. 
  Proof.
    introv Hex Hnex Hbe Hbi.
    lets H__: buffer_equiv_noque_false_ Hex; eauto. 
  Qed.
Lemma buffer_equiv_noque_false_2: 
    forall vp O1 O2 pr, 
      buffer_equiv (dom_for_prio pr) O1 O2 ->
      buffer_indom vp O1 pr -> 
      (exists qid qls,
        vp = Vptr qid /\
        get O1 absecblsid = Some (absecblist qls) /\
        (exists wls n pwl, get qls qid = Some (absmsgq nil n pwl, wls))) ->
      (exists qid qls,
         vp = Vptr qid /\
         get O2 absecblsid = Some (absecblist qls) /\
         (exists wls n pwl, get qls qid = Some (absmsgq nil n pwl, wls))). 
  Proof.
    introv Hbe Hbi1 Hex.
    unfolds in Hbe.
    simpljoin.
    unfolds in Hbi1.
    rem_dis.
    match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
    match goal with H: forall _, _ |- _ => specializes H; eauto end.
    l_rew12_inv2 (get O1 absecblsid).
    simpljoin.
    do 2 eexists.
    split; eauto.
    split; eauto.
    destruct H as (H & _).
    assert (exists ed ws, get x2 x6 = Some (ed, ws)).
    { apply H. do 2 eexists. apply H2. }
    simpljoin.
    specializes H1; eauto.
    destruct H1 as (H1 & _).
    unfolds in H1.
    simpljoin.
    inverts H1.
    do 3 eexists. apply H4.
  Qed.
Lemma buffer_equiv_noque_false2: 
    forall vp O1 O2 pr, 
      (exists qid qls,
        vp = Vptr qid /\
        get O1 absecblsid = Some (absecblist qls) /\
        (exists wls n pwl, get qls qid = Some (absmsgq nil n pwl, wls))) ->
      ~(exists qid qls,
         vp = Vptr qid /\
         get O2 absecblsid = Some (absecblist qls) /\
         (exists wls n pwl, get qls qid = Some (absmsgq nil n pwl, wls))) ->
      buffer_equiv (dom_for_prio pr) O1 O2 ->
      buffer_indom vp O1 pr -> 
      False. 
  Proof.
    introv Hex Hnex Hbe Hbi.
    lets H__: buffer_equiv_noque_false_2 Hex; eauto. 
  Qed.  
Lemma mq_equiv_buffer_ref_preserve2:
    forall td mq1 mq2 O1 O2 O1' O2' els1 els2 els1' els2' eid ecb1 ecb2 pr mqs1 idx, 
      mq_equiv td mq1 mq2 O1 O2 ->
      get O1 absecblsid = Some (absecblist els1) ->
      get O2 absecblsid = Some (absecblist els2) ->
      get O1' absecblsid = Some (absecblist els1') ->
      get O2' absecblsid = Some (absecblist els2') ->
      els1' = set els1 eid ecb1 ->
      els2' = set els2 eid ecb2 ->
      get O1 absmqattrid = Some (absmqattr mqs1) ->
      get mqs1 idx = Some mq1 ->
      buffer_indom (Vptr eid) O1 pr ->
      prio_preserved O1 O1' ->
      prio_preserved O2 O2' -> 
      mq_equiv td mq1 mq2 O1' O2'.
  Proof.
    introv Hme Hge1 Hge2 Hge1' Hge2' He1' He2' Hmqs Hmq Hbi. 
    introv Hpp1 Hpp2.
    unfold mq_equiv in *.
    simpljoin.
    unfolds in Hbi.
    match goal with
      H: _ \/ _ \/ _ |- _ => destruct H as [Hf | [Hf | Hf]]; simpljoin; tryfalse
    end.
    - rem_dis. do 8 eexists; eauto.
    - rem_dis.
      do 8 eexists.
      split; eauto. 
    - rem_dis.
      match goal with H: Vptr _ = Vptr _ |- _ => inverts H  end.
      do 8 eexists.
      split; eauto.
      split; eauto.
      right. right.
      match goal with
        H: buf_in_dom ?x _ = _, H1: get _ ?x' = _, H2: get _ ?x' = _ |- _ =>
          rename x into eid; rename x' into eid'
      end.
      casetac eid eid' Ht Hf.
      + subst.
        false. lets H__: not_both_mq_and_buffer Hmqs Hmq; eauto.
      +
        l_rew21_inv1 (get O1 absecblsid).
        l_rew21_inv1 (get O2 absecblsid).
        do 7 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        split; eauto.
        rewrite set_a_get_a'; eauto.
        rewrite set_a_get_a'; eauto.
        split; eauto.
        split; eauto.
        split.
        unfold mq_ed_equiv in *.
        simpljoin.
        do 4 eexists. split; eauto. split; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
        eapply tidls_equiv_pp_preserve2; eauto.
  Qed.

Lemma qacc_succ_body_kme_buffer_indom_preserve2: 
    forall vp rv_post1 rv_post2 td O1 O2 O1' O2' Of1 Of2 O10 O20 O10' O20' act v1 v2 pr, 
      kernel_mq_equiv td O1 O2 ->
      join O10 Of1 O1 ->
      join O20 Of2 O2 -> 
      qacc_succ_body (vp :: rv_post1 :: nil) O10 act (v1, Some O10') ->
      qacc_succ_body (vp :: rv_post2 :: nil) O20 act (v2, Some O20') ->
      join O10' Of1 O1' ->
      join O20' Of2 O2' -> 
      buffer_indom vp O1 pr -> 
      kernel_mq_equiv td O1' O2'.
  Proof.
    introv Hkme Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbi.
    lets Hpp1: aqcc_succ_prio_preserved Hqn1; eauto.
    specializes Hpp1; eauto.
    lets Hpp2: aqcc_succ_prio_preserved Hqn2; eauto.
    specializes Hpp2; eauto. 
    inverts Hqn1.
    inverts Hqn2.
    simpljoin.
    do 2 inv_lst.
    do 2 rem_dis.
    do 2 inv_some.
    unfold kernel_mq_equiv in *.
    simpljoin.
    assert (get O1 absmqattrid = get O1' absmqattrid).
    {
      lets H__: join_get_same_l Hjo1 Hjo1'; eauto.
      repeat rewsimp. auto. 
    }
    assert (get O2 absmqattrid = get O2' absmqattrid).
    {
      lets H__: join_get_same_l Hjo2 Hjo2'; eauto.
      repeat rewsimp. auto. 
    }
    match goal with
      H: get O1 absmqattrid = Some (absmqattr ?x) |- _ =>
        assert (get O1' absmqattrid = Some (absmqattr x)) by congruence 
    end.
    match goal with
      H: get O2 absmqattrid = Some (absmqattr ?x) |- _ =>
        assert (get O2' absmqattrid = Some (absmqattr x)) by congruence 
    end.
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hd.
    match goal with H: forall _, _ |- _ => lets H__: H Hd; eauto end.
    destruct H__ as (Hiff & Ha).
    split; auto.
    introv Hgm1 Hgm2.
    specializes Ha; eauto. 
    kvext_h Hjo1' absecblsid O1'.
    kvext_h Hjo2' absecblsid O2'.
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    eapply mq_equiv_buffer_ref_preserve2; eauto.
  Qed. 

Ltac inv_msgq :=
    match goal with H: absmsgq _ _ _ = _ |- _ => inverts H end.

Lemma qacc_succ_body_buffer_equiv_preserve2:
    forall td O1 O2 rv_post1 rv_post2 vp  v1 v2 act pr Of1 Of2 O10 O20 O10' O20' O1' O2',  
      buffer_equiv td O1 O2 ->
      buffer_equiv (dom_for_prio pr) O1 O2 ->
      join O10 Of1 O1 -> 
      join O20 Of2 O2 ->       
      qacc_succ_body (vp :: rv_post1 :: nil) O10 act (v1, Some O10') ->
      qacc_succ_body (vp :: rv_post2 :: nil) O20 act (v2, Some O20') ->
      join O10' Of1 O1' -> 
      join O20' Of2 O2' -> 
      buffer_indom vp O1 pr -> 
      buffer_equiv td O1' O2'.
  Proof.
    introv Hbe Hbe' Hjo1 Hjo2 Hqn1 Hqn2 Hjo1' Hjo2' Hbid.
    lets Hpp1: aqcc_succ_prio_preserved Hqn1 Hjo1 Hjo1'; eauto.
    lets Hpp2: aqcc_succ_prio_preserved Hqn2 Hjo2 Hjo2'; eauto. 
    inverts Hqn1.
    inverts Hqn2.
    simpljoin.
    do 2 inv_lst.
    do 2 rem_dis.
    do 2 inv_some.
    kvext_h Hjo1' absecblsid O1'.
    kvext_h Hjo2' absecblsid O2'.
    unfold buffer_equiv in *.
    destruct Hbe as (els1 & els2 & Hge1 & Hge2 & Ha).
    kvext O10 absecblsid O1.
    kvext O20 absecblsid O2.
    l_rew21_inv1 (get O1 absecblsid).
    l_rew21_inv1 (get O2 absecblsid).
    do 2 eexists.
    split; eauto.
    split; eauto.
    introv Hd.
    specializes Ha; eauto.
    destruct Ha as (Hiff & Ha).
    casetac x eid Ht Hf.
    - subst.
      repeat rewrite set_a_get_a.
      split.
      + split; 
          introv Hex; simpljoin; do 2 eexists; eauto.
      + introv Hso1 Hso2.
        inverts Hso1.
        inverts Hso2.
        specializes Ha; eauto.
        destruct Ha as (Hme & Hte).
        split.
        *
          unfold mq_ed_equiv in *.
          simpljoin.
          do 2 inv_msgq. 
          do 4 eexists. split; eauto. split; eauto.
          eapply tidls_equiv_pp_preserve2; eauto.
        *
          eapply tidls_equiv_pp_preserve2; eauto.
    -
      repeat (rewrite set_a_get_a'; eauto).
      split.
      + auto.
      + introv Hg1 Hg2.
        specializes Ha; eauto.
        simpljoin.
        split.
        * eapply mq_ed_equiv_pp_preserve2; eauto. 
        * eapply  tidls_equiv_pp_preserve2; eauto. 
  Qed. 

Lemma qacc_succ_body_dteq_preserve2:
    forall td cst1 cst2 O1 O2 pr vp rv1 rv2 v1 v2 O10 O20 O10' O20' O1' O2' act Of1 Of2, 
      data_equiv_tskd td cst1 cst2 O1 O2 -> 
      buffer_equiv (dom_for_prio pr) O1 O2 -> 
      buffer_indom vp O1 pr -> 
      join O10 Of1 O1 ->
      join O20 Of2 O2 ->
      qacc_succ_body (vp :: rv1 :: nil) O10 act (v1, Some O10') ->
      qacc_succ_body (vp :: rv2 :: nil) O20 act (v2, Some O20') ->
      join O10' Of1 O1' ->
      join O20' Of2 O2' -> 
      data_equiv_tskd td cst1 cst2 O1' O2'. 
  Proof.
    introv Hde Hbfe_ Hbi Hjo1 Hjo2 Hpost1 Hpost2.
    introv Hjo1' Hjo2'.
    unfold data_equiv_tskd in *.
    destruct Hde as (Hctide & Hbfe & Hkde & Hcde).
    split.
    eapply qacc_succ_body_ctid_equiv_preserve2; eauto.
    split.
    eapply qacc_succ_body_bufs_equiv_preserve2; eauto.
    split.
    2: {
      eapply cde_prio_preserved_preserve2; eauto.
      lets H__: aqcc_succ_prio_preserved Hpost1; eauto.
      lets H__: aqcc_succ_prio_preserved Hpost2; eauto.
    }
    unfold kernel_data_equiv.

    split.
    { (* kernel_task_equiv *)
      destructs Hkde.
      eapply knl_tsk_equiv_same_tls_preserve2; eauto.
      lets H__: join_get_same_l abstcblsid Hjo1 Hjo1'.
      eapply qacc_succ_body_get_tcbid_eq; eauto.
      auto.
      lets H__: join_get_same_l abstcblsid Hjo2 Hjo2'.
      eapply qacc_succ_body_get_tcbid_eq; eauto.
      auto.
    }
    split.
    {
      (* kernel_mq_equiv *)
      destructs Hkde.
      eapply qacc_succ_body_kme_buffer_indom_preserve2; eauto. 
    }
    split.
    { (* ports_equiv *)
      destructs Hkde.
      eapply ports_equiv_same_prts_preserve2; eauto.
      
      lets H__: qacc_succ_dpid_same Hjo1 Hjo1'; eauto.
      lets H__: qacc_succ_dpid_same Hjo2 Hjo2'; eauto.
      lets H__: qacc_succ_kpid_same Hjo1 Hjo1'; eauto.
      lets H__: qacc_succ_kpid_same Hjo2 Hjo2'; eauto.
      lets H__: qacc_succ_same_prt_ecbs Hjo1 Hjo1'; eauto.
      lets H__: qacc_succ_same_prt_ecbs Hjo2 Hjo2'; eauto.
      lets H__: qacc_succ_dom_impl Hjo1 Hjo1'; eauto.
      lets H__: qacc_succ_dom_impl Hjo2 Hjo2'; eauto.
      lets H__: aqcc_succ_prio_preserved Hjo1 Hjo1'; eauto.
      lets H__: aqcc_succ_prio_preserved Hjo2 Hjo2'; eauto.
    }

    split.
    (* buffer_equiv *)
    destructs Hkde.        
    eapply qacc_succ_body_buffer_equiv_preserve2; eauto. 
    
    (* cap_equiv *)
    destructs Hkde.
    eapply cap_equiv_preserve2; eauto.
    lets H__: qacc_succ_cpid_same Hjo1 Hjo1'; eauto.
    lets H__: qacc_succ_cpid_same Hjo2 Hjo2'; eauto.
    lets H__: qacc_succ_mqptr_iff Hjo1 Hjo1'; eauto.
    lets H__: qacc_succ_mqptr_iff Hjo2 Hjo2'; eauto.
  Qed. 
Lemma hidapistep_hidapistep_bufferaccept_lemma:
  forall pc0 pr t1 t2 T1 T2 cst1' cst2' O1 O2
  O1' O2' act i ks1 ke0 ks2 cd1 cd2 cd1' cd2',
  no_common_fid pc0 (api_spec, int_spec, get_hprio_d) ->
  pu_noabs pc0 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T2 cst2' O2 ->
  reachable (pc0, (api_spec, int_spec, get_hprio_d)) T1 cst1' O1 ->
  (flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
          obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2) ->
  obsr_equiv get_hprio_d SchedDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv get_hprio_d TransDom T1 T2 cst1' cst2' O1 O2 ->
  obsr_equiv_tskd get_hprio_d i T1 T2 cst1' cst2' O1 O2 ->
  act = TauAct \/ act = SendAct \/ act = RecvAct ->
  ~ in_intr T1 O1 ->
  get O1 curtid = Some (oscurt t1) ->
  task_prio_id O1 pr t1 ->
  nabt (set T1 t1 (curs (hapi_code cd1'), (ke0, ks1))) ->
  ~ in_intr T2 O2 ->
  get O2 curtid = Some (oscurt t2) ->
  dom_for_prio pr = dom_for_prio pr ->
  task_prio_id O2 pr t2 ->
  nabt (set T2 t2 (curs (hapi_code cd2'), (ke0, ks2))) ->
  get T1 t1 = Some (curs (hapi_code cd1), (ke0, ks1)) ->
  (forall (pr0 : priority) (t1 t2 : tid),
       dom_for_prio pr0 = dom_for_prio pr ->
       task_prio_id O1 pr0 t1 ->
       task_prio_id O2 pr0 t2 ->
       exists c1 c2 ke ks1 ks2,
       get T1 t1 = Some (c1, (ke, ks1)) /\
       get T2 t2 = Some (c2, (ke, ks2)) /\
       cmd_equiv pr0 c1 c2 O1 O2 /\ cont_equiv pr0 ks1 ks2 O1 O2) ->
  obsr_equiv get_hprio_d (TaskDom (dom_for_prio pr)) T1 T2 cst1' cst2' O1 O2 ->
  flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
  (forall pr1 pr2 : priority,
      task_prio_id O1 pr1 t1 ->
      task_prio_id O2 pr2 t2 -> dom_for_prio pr1 = dom_for_prio pr -> pr1 = pr2) ->
  get O1 curtid = Some (oscurt t1) ->
  get O2 curtid = Some (oscurt t2) ->
  bufs_equiv (dom_for_prio pr) O1 O2 ->
  kernel_data_equiv (dom_for_prio pr) O1 O2 ->
  client_data_equiv (dom_for_prio pr) cst1' cst2' O1 O2 ->
  kernel_task_equiv (dom_for_prio pr) O1 O2 ->
  kernel_mq_equiv (dom_for_prio pr) O1 O2 ->
  ports_equiv (dom_for_prio pr) O1 O2 ->
  buffer_equiv (dom_for_prio pr) O1 O2 ->
  ctid_equiv (dom_for_prio pr) O1 O2 ->
  hapistep (api_spec, int_spec, get_hprio_d) (curs (hapi_code cd2), (ke0, ks2)) O2
       (curs (hapi_code cd2'), (ke0, ks2)) O2' act ->
  cap_equiv (dom_for_prio pr) O1 O2 ->
  head_asrt_sat pr cd1 O1 ->
  head_asrt_sat pr cd2 O2 ->
  vl_equiv cd1 cd2 ->
  ~ (exists vo1 vo2, cd1 = END vo1 /\ cd2 = END vo2) ->
  cont_equiv pr ks1 ks2 O1 O2 ->
  get T2 t2 = Some (curs (hapi_code cd2), (ke0, ks2)) ->
  spec_step get_hprio_d cd1 O1 cd1' O1' act ->
  spec_step get_hprio_d cd2 O2 cd2' O2' act ->
  bufferaccept_equiv cd1 cd2 ->
  code_equiv_tskd i (set T1 t1 (curs (hapi_code cd1'), (ke0, ks1)))
    (set T2 t2 (curs (hapi_code cd2'), (ke0, ks2))) O1' O2' /\
  data_equiv_tskd i cst1' cst2' O1' O2'.
Proof.
  intros.

  destruct H4 as (Hceqs & Hdeqs);
  lets Hdeqs_sym: data_equiv_schd_sym Hdeqs.
  destruct H6 as (Hceqt & Hdeqt).
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
  rename H30 into Hbeq; 
  lets Hbeq_sym: buffer_equiv_sym Hbeq.
  rename H34 into Hsat1; rename H35 into Hsat2.
  rename H40 into Hstep1; rename H41 into Hstep2.
  apply step1_lemma in Hstep1; apply step2_lemma in Hstep2.
  destruct H42 as (vl & vl1 & vl2 & k & Hlenvl & Hlenvl1 & Hlenvl2 & Hnth1 & Hnth2).
  assert (Hbind_all : bind_all vl vl1 vl2 cd1' cd2') by (unfolds; apply n_block_cross_part).
  do 2 try destruct vl; tryfalse.
  do 2 try destruct vl1; tryfalse.
  do 2 try destruct vl2; tryfalse.
  rename v into vp; rename v0 into rv1; rename v1 into rv2.

  (* k=0 *)
  start k.
  { step1; step2; step1; step2. obsr_equiv_tskd_upd2_preserve' 1%nat. }

  start k.
  (* k=1 *)
  {
    step1;step2.
    { obsr_equiv_tskd_upd2_preserve' 2%nat. }
    { efalse dct_bid_false. }
    { efalse dct_bid_false. }
    {
      obsr_equiv_tskd_upd2_preserve' 3%nat.
      - eapply n_buf_in_dom_false_dest; eauto.
      - eapply n_buf_in_dom_false_dest; eauto.
    }
  }

  start k.
  (* k=2 *)
  { step1; step2. rv_equal_end. }

  start k.
  (* k=3 *)
  {
    step1.
    {
      step2.
      {
        step1; step2.
        {
          step1; step2.
          lets Htemp1: aar_Oeq H35; lets Htemp2: aar_Oeq H40. subst.
          lets Htemp1: aar_veq H35; lets Htemp2: aar_veq H40. subst.
          obsr_equiv_tskd_upd2_preserve' 4%nat.
          - eapply veq_vlequiv; simpl; eauto.
        }
        { congruence. }
        { congruence. }
        {
          step1; step2.
          {
            step1; step2.
            lets Htemp1: aar_Oeq H35; lets Htemp2: aar_Oeq H40. subst.
            lets Htemp1: aar_veq H35; lets Htemp2: aar_veq H40. subst.
            obsr_equiv_tskd_upd2_preserve' 4%nat.
            - eapply veq_vlequiv; simpl; eauto.
          }


          { efalse buffer_equiv_noque_false. }
          { efalse buffer_equiv_noque_false. }
          {
            step1; step2.
            {
              step1; step2.
              lets Htemp1: aar_Oeq H35; lets Htemp2: aar_Oeq H40. subst.
              lets Htemp1: aar_veq H35; lets Htemp2: aar_veq H40. subst.
              obsr_equiv_tskd_upd2_preserve' 4%nat.
              - eapply veq_vlequiv; simpl; eauto.
            }



            { efalse buffer_equiv_noque_false2. }
            { efalse buffer_equiv_noque_false2. }
            {
              step1; step2. step1; step2.
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
                  split.
                  {
                    clear H50; clear H51.
                    unfolds in H35; unfolds in H40. unfolds in Hbeq.
                    simpljoin.
                    destruct H59; simpljoin; tryfalse.
                    destruct H50; simpljoin; tryfalse.
                    inverts H6; inverts H4.
                    assert (get O1 absecblsid = Some (absecblist x11)) by (eapply join_get_get_l; eauto).
                    assert (get O2 absecblsid = Some (absecblist x5)) by (eapply join_get_get_l; eauto).
                    l_rew21_inv1(get O1 absecblsid).
                    l_rew21_inv1(get O2 absecblsid).
                    destruct Hsat1; simpljoin; tryfalse. inverts H14.
                    specializes H63; eauto. destruct H63 as (_ & H63).
                    specializes H63; eauto. destruct H63 as (H63 & _).
                    unfolds in H63; simpljoin.
                    inverts H14; inverts H50.
                    eapply vl_equiv_refl; eauto.
                  }
                  right.
                  split. introv Hf; simpljoin; tryfalse.
                  right; right; right; right; right; right; right; right; left.
                  (* mqsend_equiv *)
                  unfolds. 
                  match type of Hlenvl with length ?vl = _ => exists vl end. 
                  match type of Hlenvl1 with length ?vl = _ => exists vl end.
                  match type of Hlenvl2 with length ?vl = _ => exists vl end.
                  exists 4%nat. splits; auto.
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
              -
                eapply qacc_succ_body_dteq_preserve2; eauto.
            }
          }
        }
      }
      { step2; step2; step2; step2; step2. }
    }
    { step1; step1; step1; step1; step1. }
  }
  
  start k.
  (* k=4 *)
  {
    step1; step2.
    assert (rv1 = rv2). {
      unfolds in H36; simpl in H36.
      specializes H36; eauto.
      instantiate(1:=0%nat). auto. auto.
    }
    lets Htemp1: rv_veq H34; lets Htemp2: rv_veq H40. subst.
    rv_equal_end.
  }

  start k.
  inverts Hnth1.
Qed.



