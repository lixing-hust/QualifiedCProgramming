
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.

Require Import os_q_cap.
Require Import abs_op.
Require Import ifun_spec.

Require Import include_frm.
Require Import os_inv.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import init_spec.

Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import pos_list_common.
Require Import ev_aux_code.
Require Import sem_common.
Require Import gjb_common.
Require Import gjb_q_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.

Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Require Import abs_infer_abt.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Local Open Scope code_scope.
Local Open Scope list_scope.

Definition ume_div3 := $ (OS_USER_MAX_EVENTS / 3). 

Lemma int_lt_lt_false:
  forall i, 
    Int.ltu i ($ 0) = true -> 
    Int.ltu ume_div3 i = true -> 
    False. 
Proof.
  intros.
  int auto.
  mauto. 
Qed. 

Lemma mqdelete_absimp_mqdeserr: 
  forall mqdes v P sch vr_temp_dom vr_temp_num vr_temp_dom' vr_temp_num',
    (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ mqdes = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqdelete (Vint32 mqdes :: v :: vr_temp_dom :: vr_temp_num :: vr_temp_dom' :: vr_temp_num' :: nil) ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof.
  introv Hrgn Hcop.
  unfold mqdelete.
  infer_solver 0%nat. 
Qed.

Lemma mqdelete_absimp_eptr_null:
  forall qeibs mqdes wtp flgs mm ms cm mqc P sch s,
    get qeibs mqdes = Some (Null, wtp, flgs, mm, ms, cm, mqc) -> 
    can_change_aop P ->
    absinfer sch
             (<|| mqdelete_ecb_ptr_null (| Vint32 mqdes :: nil |) ?? s ||> ** HQAttr qeibs ** P)
             (<|| END (Some (Vint32 (Int.mone))) ||> ** HQAttr qeibs ** P). 
Proof.
  introv Hrgn Hcop.
  infer_solver 0%nat.
Qed.

Lemma mqdelete_absimp_eptr_holder_abt:
  forall qeibs mqdes wtp flgs mm ms cm mqc P sch s1 s2,  
    get qeibs mqdes = Some (Holder, wtp, flgs, mm, ms, cm, mqc) -> 
    can_change_aop P ->
    absinfer sch
             (<|| s1 ?? mqdelete_ecb_ptr_holder_abt (| Vint32 mqdes :: nil |) ?? s2 ||> ** HQAttr qeibs ** P)
             (<|| ABORT ||> ** HQAttr qeibs ** P). 
Proof.
  introv Hget Hcop.
  eapply absinfer_trans; try eapply absinfer_choice2; [ | | eauto | ]; can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_choice1; [ | | eauto | ]; can_change_aop_solver.
  eapply absinfer_abt; can_change_aop_solver.
  absimp_abt_solver.
  can_change_aop_solver.
Qed.

Lemma mqdelete_absimp_inest_err: 
  forall P mqdes sch s1 s2 s3,
    can_change_aop P ->
    absinfer sch
             (<|| s1 ?? s2 ?? mqdelete_int_nst_err (| Vint32 mqdes :: nil |) ?? s3||> ** P)
             (<|| END (Some (Vint32 (Int.mone))) ||> ** P).  
Proof.
  introv Hcop.
  infer_solver 2%nat.
Qed.

Lemma mqdelete_absimp_get_set_ecb_ptr_ok: 
  forall qeibs qeibs' mqdes wtp flgs mm ms cm mqc locmp ptrmp locmp' ptrmp' t eid P sch s1 s2 s3,
    get qeibs mqdes = Some (Valid_Addr eid, wtp, flgs, mm, ms, cm, mqc) ->
    get locmp t = Some (V$ __EvLoc_normal) ->
    get ptrmp t = Some (Vnull, Vnull, Vnull) ->
    qeibs' = set qeibs mqdes (Null, wtp, flgs, mm, ms, cm, mqc) ->
    locmp' = set locmp t (V$ __EvLoc_ecbdel) ->
    ptrmp' = set ptrmp t (Vnull, Vnull, Vptr eid) ->
    can_change_aop P ->
    absinfer sch
             (<|| s1 ?? s2 ?? s3 ??
                     mqdelete_get_set_ecb_ptr (| Vint32 mqdes :: Vptr eid :: nil |)
                     ;; spec_code_cons (qdel (Vptr eid :: nil)) (mqdelete_reset_loc (|Vint32 mqdes :: nil|)) ||> **
                  HQAttr qeibs ** HCurTCB t ** HEvLoc locmp ** HEvPtr ptrmp ** P) 
             (<|| spec_code_cons (qdel (Vptr eid :: nil)) (mqdelete_reset_loc (|Vint32 mqdes :: nil|))  ||> **
                  HQAttr qeibs' ** HCurTCB t ** HEvLoc locmp' ** HEvPtr ptrmp' ** P).   
Proof.
  introv Hgetl Hgetp Hget' Hlmp' Hpmp' Hcop.
  infer_solver 3%nat.
  unfold tidsame.
  do 3 (rewrite abst_set_get_neq''; eauto). 
Qed.

Lemma mqdelete_absimp_get_ecb_ptr_abt: 
  forall qeibs mqdes wtp flgs mm ms cm mqc locmp ptrmp v t eid P sch s1 s2 s3 s4,  
    get qeibs mqdes = Some (Valid_Addr eid, wtp, flgs, mm, ms, cm, mqc) ->
    get locmp t = Some (V$ __EvLoc_normal) ->
    get ptrmp t = Some (Vnull, Vnull, Vnull) ->
    v <> Vptr eid -> 
    can_change_aop P ->
    absinfer sch
             (<|| s1 ?? s2 ?? s3 ??  mqdelete_get_set_ecb_ptr (| Vint32 mqdes :: v :: nil |)  ;; s4 ||> **
                  HQAttr qeibs ** HCurTCB t ** HEvLoc locmp ** HEvPtr ptrmp ** P) 
             (<|| ABORT ||> ** 
                  HQAttr qeibs ** HCurTCB t ** HEvLoc locmp ** HEvPtr ptrmp ** P).   
Proof.
  introv Hget Hgetl Hgetp Hneq Hcop.
  eapply absinfer_trans; try eapply absinfer_choice2; [ | | eauto | ]; can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_choice2; [ | | eauto | ]; can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_choice2; [ | | eauto | ]; can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_seq_abt;  [ | | | eauto ]; can_change_aop_solver.
  eapply absinfer_seq; can_change_aop_solver.
  eapply absinfer_abt; can_change_aop_solver.
  absimp_abt_solver; try instantiate (3:= s); sep pauto.
  can_change_aop_solver.
  Unshelve.
  exact (END None).
  exact (END None).
  exact (END None).
Qed.

Lemma mqdelete_absimp_reset_loc_ok: 
  forall locmp locmp' ptrmp t i sch P,
    get locmp t = Some (V$ __EvLoc_ecbdel) -> 
    get ptrmp t = Some (Vnull, Vnull, Vnull) ->
    locmp' = set locmp t (V$ __EvLoc_normal) -> 
    can_change_aop P -> 
    absinfer sch
             (<|| mqdelete_reset_loc (|Vint32 i :: nil|) ||> ** HCurTCB t ** HEvLoc locmp ** HEvPtr ptrmp ** P)
             (<|| END (Some (Vint32 Int.zero)) ||> ** HCurTCB t ** HEvLoc locmp' ** HEvPtr ptrmp ** P).  
Proof.
  introv Hgetl Hgetp Hlmp' Hcop.
  infer_solver 0%nat.
Qed.

Lemma RH_EIB_ECB_Q_P_set_null_preserve: 
  forall els mqeibs i wty flg maxm ms cm mqc, 
    RH_EIBlk_ECBlk_Q_P els mqeibs -> 
    RH_EIBlk_ECBlk_Q_P els (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)).
Proof.
  introv Hrh.
  unfold RH_EIBlk_ECBlk_Q_P in *.
  introv Hget.
  casetac i pos Heq Hne.
  subst.
  rewrite set_a_get_a in Hget.
  inverts Hget.
  rewrite set_a_get_a' in Hget; auto. 
  eapply Hrh; eauto. 
Qed.

Lemma eib_ref_no_cre: 
  forall semeibs muxeibs mqeibs qid tid locmp ptrmp els fecbh fecbvl, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs -> 
    eib_ref semeibs muxeibs mqeibs qid ->
    get locmp tid = Some (V$ __EvLoc_normal) -> 
    ~(exists t0,
         (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/ get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\
         evptr_of_tsk t0 ptrmp qid).
Proof.
  introv Hsep Hmep Hqep Heref Hgetl Hex.
  simpljoin1.
  unfold evptr_of_tsk in H0.
  destruct H0 as [Hs | [Hm | Hq]]; simpljoin1.
  - 
    destruct H as [Hcre1 | Hcre2].
    +
      lets H00: mux_ecb_cre1 Hmep Hcre1 H0.
      simpljoin1. apply H1 in Heref; tryfalse.
    +
      lets H00: mux_ecb_cre2 Hmep Hcre2 H0.
      simpljoin1. apply H in Heref; tryfalse.
  -
    destruct H as [Hcre1 | Hcre2].
    +
      lets H00: sem_ecb_cre1 Hsep Hcre1 H0. 
      simpljoin1. apply H1 in Heref; tryfalse.
    +
      lets H00: sem_ecb_cre2 Hsep Hcre2 H0. 
      simpljoin1. apply H in Heref; tryfalse.
  -
    destruct H as [Hcre1 | Hcre2].
    +
      lets H00: q_ecb_cre1 Hqep Hcre1 H0. 
      simpljoin1. apply H1 in Heref; tryfalse.
    +
      lets H00: q_ecb_cre2 Hqep Hcre2 H0. 
      simpljoin1. apply H in Heref; tryfalse.
Qed.

Lemma ecbdel_nex_eptr_diff:
  forall locmp ptrmp eptr1 eptr2 t2, 
    ~ (exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eptr1) -> 
    evptr_of_tsk t2 ptrmp eptr2 -> 
    get locmp t2 = Some (V$ __EvLoc_ecbdel) ->
    eptr1 <> eptr2.
Proof.
  introv Hnex Hevptr2 Hgetl2.
  unfold evptr_of_tsk in Hevptr2.
  destruct Hevptr2 as [Hmp | [Hsp | Hqp]]. 
  -
    introv Heq. subst.
    apply Hnex.
    simpljoin1.
    exists t2.
    unfold tsk_loc_ev.
    splits; auto.
    do 3 eexists; splits; eauto.
  -
    introv Heq. subst.
    apply Hnex.
    simpljoin1.
    exists t2.
    unfold tsk_loc_ev.
    splits; auto.
    do 3 eexists; splits; eauto.
  -
    introv Heq. subst.
    apply Hnex.
    simpljoin1.
    exists t2.
    unfold tsk_loc_ev.
    splits; auto.
    do 3 eexists; splits; eauto.
Qed. 

Lemma evdel_nodup_qdel_preserve:
  forall locmp ptrmp qid tid, 
    evdel_nodup locmp ptrmp -> 
    ~ (exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel qid) -> 
    evdel_nodup (set locmp tid (V$ __EvLoc_ecbdel)) (set ptrmp tid (Vnull, Vnull, Vptr qid)). 
Proof.
  introv Hdnp Hnex.
  unfold evdel_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  casetac tid t1 Heq Hneq.
  -
    subst.
    unfold evptr_of_tsk in Het1.
    rewrite set_a_get_a in Het1.
    destruct Het1 as [Hmp | [Hsp | Hqp]].
    simpljoin1. tryfalse.
    simpljoin1. tryfalse.
    simpljoin1. 
    inverts H.
    rewrite set_a_get_a' in Hget2; eauto. 
    unfold evptr_of_tsk in Het2.
    rewrite set_a_get_a' in Het2; eauto. 
    eapply ecbdel_nex_eptr_diff; eauto. 
  -
    casetac tid t2 Heq' Hneq'. 
    +
      subst.
      rewrite set_a_get_a' in Hget1; eauto.
      unfold evptr_of_tsk in Het1.
      rewrite set_a_get_a' in Het1; eauto.
      assert (eptr2 = qid).
      {
        unfold evptr_of_tsk in Het2.
        rewrite set_a_get_a in Het2; eauto.
        destruct Het2 as [? | [? | ?]]; simpljoin1.
        inverts H. inverts H. inverts H.
        auto. 
      }
      subst.
      lets H00: ecbdel_nex_eptr_diff Hnex Hget1.
      instantiate (1:=eptr1). clear -Het1. auto.
      eauto. 
    +
      rewrite set_a_get_a' in Hget1; eauto.
      rewrite set_a_get_a' in Hget2; eauto.
      unfold evptr_of_tsk in Het1, Het2.
      rewrite set_a_get_a' in Het1, Het2; eauto. 
Qed. 

Lemma evcre_nodup_set_qdel_preserve: 
  forall locmp ptrmp tid qid, 
    evcre_nodup locmp ptrmp -> 
    evcre_nodup (set locmp tid (V$ __EvLoc_ecbdel)) (set ptrmp tid (Vnull, Vnull, Vptr qid)). 
Proof.
  introv Hndp.
  unfold evcre_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  unfold evptr_of_tsk in Het1, Het2.
  casetac tid t1 Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hget1.
    destruct Hget1.
    inverts H. inverts H.
  -
    casetac tid t2 Ht' Hf'.
    +
      subst.
      rewrite set_a_get_a in Hget2.
      destruct Hget2.
      inverts H. inverts H.
    +
      rewrite set_a_get_a' in Het1, Het2; eauto.
      rewrite set_a_get_a' in Hget1, Hget2; eauto. 
Qed.

Lemma eibref_sametype_qdel_preserve:
  forall eptr semeibs muxeibs mqeibs wty flg maxm ms cm mqc i, 
    evref_same_type eptr semeibs muxeibs mqeibs ->
    evref_same_type eptr semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)). 
Proof.
  introv Hst.
  unfold evref_same_type in *.
  simpljoin1.
  splits.
  -
    introv Hsr.
    apply H in Hsr.
    simpljoin1.
    splits; auto.
    introv Hqr. apply H3.
    unfold mqeib_ref in Hqr. unfold mqeib_ref.
    simpljoin1.
    casetac i x He Hne.
    subst. rewrite set_a_get_a in H4.
    inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists. eauto.
  -
    introv Hmr.
    apply H0 in Hmr.
    simpljoin1.
    splits; auto.
    introv Hqr. apply H3.
    unfold mqeib_ref in Hqr. unfold mqeib_ref.
    simpljoin1.
    casetac i x He Hne.
    subst. rewrite set_a_get_a in H4.
    inverts H4.
    rewrite set_a_get_a' in H4; eauto.
    repeat eexists. eauto.
  -
    introv Hqr.
    apply H1.
    unfold mqeib_ref in Hqr. unfold mqeib_ref.
    simpljoin1.
    casetac i x He Hne.
    subst.
    rewrite set_a_get_a in H2. inverts H2.
    rewrite set_a_get_a' in H2; eauto.
    repeat eexists; eauto. 
Qed.

Lemma mqref_distinct_mqdel_preserve: 
  forall qeibs eptr wty flg maxm ms cm mqc i, 
    mqref_distinct qeibs eptr ->
    mqref_distinct (set qeibs i (Null, wty, flg, maxm, ms, cm, mqc)) eptr.  
Proof.
  introv Hqr.
  unfold mqref_distinct in *.
  introv Hget1 Hget2.
  casetac i pos1 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget1; eauto.
  inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac i pos2 Heq' Hneq'.
  subst.
  rewrite set_a_get_a in Hget2; eauto.
  inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma eibref_distinct_semdel_preserve:
  forall semeibs muxeibs mqeibs wty flg maxm ms cm mqc i, 
    eibref_distinct semeibs muxeibs mqeibs ->
    eibref_distinct semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)). 
Proof.
  introv Hed.
  unfold eibref_distinct in *.
  intro eptr.
  specialize (Hed eptr).
  simpljoin1.
  splits; auto.
  eapply eibref_sametype_qdel_preserve; eauto.
  eapply mqref_distinct_mqdel_preserve; eauto.
Qed.

Lemma eib_ref_qdel_preserve: 
  forall semeibs muxeibs mqeibs i wty flg maxm ms cm mqc eptr, 
    eib_ref semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)) eptr ->
    eib_ref semeibs muxeibs mqeibs eptr. 
Proof.
  introv Her.
  unfold eib_ref in *.
  destruct Her.
  left. auto.
  destruct H.
  right; left. auto.
  right; right.
  unfold mqeib_ref in H.
  unfold mqeib_ref.
  simpljoin1.
  casetac i x Ht Hf.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
  repeat eexists. eauto. 
Qed.

Lemma sem_ecb_p_qdel_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid qid wty flg maxm ms cm mqc i, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_ecbdel)) (set ptrmp tid (Vnull, Vnull, Vptr qid))
              els fecbh fecbvl semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)). 
Proof.
  introv Hsep.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto. 
    rewrite set_a_get_a'; eauto. 
    lets H00: Hsep Hgetp'. clear Hsep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]]; simpljoin1.
    +
      left. splits; eauto.
      introv Her. apply H1.
      eapply eib_ref_qdel_preserve; eauto.
    +
      right. left. splits; eauto.
      introv Her. apply H0.
      eapply eib_ref_qdel_preserve; eauto.
    +
      right; right. splits; eauto. 
Qed.

Lemma mux_ecb_p_qdel_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid qid wty flg maxm ms cm mqc i, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_ecbdel)) (set ptrmp tid (Vnull, Vnull, Vptr qid)) 
              els fecbh fecbvl semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)). 
Proof.
  introv Hmep.
  unfold MUX_ECB_P in *.
  introv Hgetp'.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto. 
    rewrite set_a_get_a'; eauto. 
    lets H00: Hmep Hgetp'. clear Hmep.
    destruct H00 as [Hcre1 | [Hcre2 | Hnml]]; simpljoin1.
    +
      left. splits; eauto.
      introv Her. apply H1.
      eapply eib_ref_qdel_preserve; eauto.
    +
      right. left. splits; eauto.
      introv Her. apply H0.
      eapply eib_ref_qdel_preserve; eauto.
    +
      right; right. splits; eauto. 
Qed.

Lemma eibref_distinct_mqref_nsemref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    mqeib_ref mqeibs eid ->
    ~semeib_ref semeibs eid.  
Proof.
  introv Hd Hqr Hsr.
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H1 in Hqr.
  simpljoin1.
  tryfalse.
Qed.

Lemma eibref_distinct_mqref_nmuxref:
  forall semeibs muxeibs mqeibs eid, 
    eibref_distinct semeibs muxeibs mqeibs ->
    mqeib_ref mqeibs eid ->
    ~muxeib_ref muxeibs eid.   
Proof.
  introv Hd Hqr Hmr. 
  unfold eibref_distinct in Hd.
  lets H00: Hd eid.
  clear Hd.
  destruct H00 as (Hst & Hsd & Hmd & Hqd).
  unfold evref_same_type in Hst.
  simpljoin1.
  apply H1 in Hqr.
  simpljoin1.
  tryfalse.
Qed.

Lemma mqref_distinct_clear_ref_contra:
  forall mqeibs qid wty flg maxm ms cm mqc i, 
    mqref_distinct mqeibs qid ->
    get mqeibs i = Some (Valid_Addr qid, wty, flg, maxm, ms, cm, mqc) -> 
    mqeib_ref (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)) qid ->
    False. 
Proof.
  introv Hrd Hget Href.
  unfold mqref_distinct in Hrd.
  unfold mqeib_ref in Href.
  simpljoin1.
  casetac i x Ht Hf.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma eibref_distinct_mqref_clear_neibref: 
  forall semeibs muxeibs mqeibs qid wty flg maxm ms cm mqc i,
    eibref_distinct semeibs muxeibs mqeibs ->
    get mqeibs i = Some (Valid_Addr qid, wty, flg, maxm, ms, cm, mqc) -> 
    ~eib_ref semeibs muxeibs (set mqeibs i (Null, wty, flg, maxm, ms, cm, mqc)) qid. 
Proof.
  introv Hed Hget Href. 
  assert (Hqr: mqeib_ref mqeibs qid).
  {
    unfold mqeib_ref.
    repeat eexists. eauto. 
  }
  lets Hnsr: eibref_distinct_mqref_nsemref Hed Hqr.
  lets Hnmr: eibref_distinct_mqref_nmuxref Hed Hqr.
  unfold eib_ref in Href.
  destruct Href as [? | [? | ?]]; tryfalse.
  unfold eibref_distinct in Hed.
  specialize (Hed qid).
  simpljoin1.
  eapply mqref_distinct_clear_ref_contra; eauto. 
Qed.

Lemma mq_ecb_p_qdel_preserve:
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs qid tid i wty fl maxm ms cm mqc, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    is_que els qid ->
    ~ (exists t0, 
          (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/
           get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\ evptr_of_tsk t0 ptrmp qid) ->
    ~ eib_ref semeibs muxeibs (set mqeibs i (Null, wty, fl, maxm, ms, cm, mqc)) qid -> 
    Q_ECB_P (set locmp tid (V$ __EvLoc_ecbdel)) (set ptrmp tid (Vnull, Vnull, Vptr qid)) els
            fecbh fecbvl semeibs muxeibs (set mqeibs i (Null, wty, fl, maxm, ms, cm, mqc)). 
Proof.
  introv Hqep Hque Hnex Href.
  unfold Q_ECB_P in *.
  introv Hgetp'.
  casetac tid t Heq Hne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    rewrite set_a_get_a.
    split.
    right; right.
    split.
    right; auto.
    left. unfold is_evt. auto.
    introv Hdeleq.
    splits; eauto.
    introv Hf. apply Hnex.
    simpljoin1.
    casetac t x Ht Hf.
    subst. rewrite set_a_get_a in H. destruct H; tryfalse.
    rewrite set_a_get_a' in H; eauto.
    exists x. splits; eauto.
    unfold evptr_of_tsk in H0.
    rewrite set_a_get_a' in H0; eauto.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hqep Hgetp'.
    clear Hqep.
    rewrite set_a_get_a'; eauto.
    destruct H00 as (Hor3 & Hdel).
    split.
    destruct Hor3 as [Hcre1 | [Hcre2 | Hnm]]; simpljoin1.
    left. splits; eauto. 
    introv Her. apply H1. eapply eib_ref_qdel_preserve; eauto.
    right; left. splits; eauto.
    introv Her. apply H0. eapply eib_ref_qdel_preserve; eauto.
    right; right. splits; eauto.

    introv Hdel'.
    apply Hdel in Hdel'. clear Hdel.
    simpljoin1.
    splits; eauto.
    2: { introv Her. apply H1. eapply eib_ref_qdel_preserve; eauto. }
    introv Hex. apply H0. clear H0.
    simpljoin1.
    casetac tid x Ht Hf.
    subst. rewrite set_a_get_a in H0; destruct H0; tryfalse.
    rewrite set_a_get_a' in H0; eauto.
    unfold evptr_of_tsk in H2.
    rewrite set_a_get_a' in H2; eauto. 
Qed.

Lemma evdel_nodup_set_normal_loc_preserve: 
  forall locmp ptrmp tid, 
    evdel_nodup locmp ptrmp ->
    evdel_nodup (set locmp tid (V$ __EvLoc_normal)) ptrmp. 
Proof.
  introv Hnd.
  unfold evdel_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  casetac tid t1 Heq Hneq.
  - subst.
    rewrite set_a_get_a in Hget1; inverts Hget1.
  - casetac tid t2 Heq' Hneq'.
    + subst.
      rewrite set_a_get_a in Hget2; inverts Hget2.
    + rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.

Lemma evcre_nodup_set_normal_loc_preserve: 
  forall locmp ptrmp tid, 
    evcre_nodup locmp ptrmp ->
    evcre_nodup (set locmp tid (V$ __EvLoc_normal)) ptrmp.  
Proof.
  introv Hnc.
  unfold evcre_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  casetac tid t1 Heq Hneq.
  - subst.
    rewrite set_a_get_a in Hget1.
    destruct Hget1; tryfalse.
  - casetac tid t2 Heq' Hneq'.
    + subst.
      rewrite set_a_get_a in Hget2.
      destruct Hget2; tryfalse.
    + rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.       

Lemma sem_ecb_p_set_normal_loc_preserve:
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    SEM_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp
              els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hsep Hgetp.
  unfold SEM_ECB_P in *.
  introv Hgetp'.
  lets H00: Hsep Hgetp'. clear Hsep.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a'; eauto.  
Qed.

Lemma mux_ecb_p_set_normal_loc_preserve:
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    MUX_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp
              els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hmep Hgetp. 
  unfold MUX_ECB_P in *. 
  introv Hgetp'.
  lets H00: Hmep Hgetp'. clear Hmep. 
  casetac tid t Ht Hf.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a'; eauto.  
Qed.

Lemma mq_ecb_p_set_normal_loc_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs tid, 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs mqeibs ->
    get ptrmp tid = Some (Vnull, Vnull, Vnull) -> 
    Q_ECB_P (set locmp tid (V$ __EvLoc_normal)) ptrmp
              els fecbh fecbvl semeibs muxeibs mqeibs. 
Proof.
  introv Hqep Hgetp. 
  unfold Q_ECB_P in *. 
  introv Hgetp'.
  lets H00: Hqep Hgetp'. clear Hqep. 
  casetac tid t Ht Hf.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    destruct H00 as (Hor3 & Hdel).
    rewrite set_a_get_a'; eauto.
    split.
    auto.
    introv Hgetl.
    apply Hdel in Hgetl. clear Hdel. 
    simpljoin1.
    splits; eauto.
    introv Hex. apply H0. clear H0.
    simpljoin1.
    casetac tid x Heq' Hneq'.
    subst. rewrite set_a_get_a in H0. destruct H0; tryfalse.
    rewrite set_a_get_a' in H0; eauto.
Qed.

Lemma MqDeleteAProof:  
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api mq_delete (mqdelete,(Tint32, mqd_t::nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api mq_delete (mqdelete,(Tint32, mqd_t::nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api mq_delete = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 6 try (destruct v'; try apply absabort_rule).
  rename v0 into vr_temp_dom.
  rename v1 into vr_temp_num.
  rename v2 into vr_temp_dom'.
  rename v3 into vr_temp_num'.

  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  assert (Hdiveq: (Int.divs ($ OS_USER_MAX_EVENTS) ($ 3) = $ (OS_USER_MAX_EVENTS / 3))).
  { unfold Int.divs in *.
     rewrite zdiv_equiv in *.
     rewrite Hsieq in *.
     auto.
     clear -Hrgn5 Hrgn6. int auto.
     clear. int auto.
  }

  assert (Hchg: Int.eq ($ 3) Int.zero ||
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && Int.eq ($ 3) Int.mone = false).
  {
    unfold nat_of_Z in *.
    rewrite Heqf.
    change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
    pure_auto.
  }

  lzh_hoare_if; try rewrite Hchg in *; try solve [simpl; pure_auto].

  assert (Hposv_cond: Int.ltu i Int.zero = true \/ Int.ltu ($ OS_USER_MAX_EVENTS / 3) i = true \/ i = $ OS_USER_MAX_EVENTS / 3).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    simpl in *; auto.
    rewrite Hdiveq in LHift_true.
    destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) i) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq i ($ OS_USER_MAX_EVENTS / 3)) eqn: eq3;
    simpl in *; try (apply semacc_int_eq_true in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in * ).
    simpljoin.
    tryfalse.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqdelete_absimp_mqdeserr; eauto. 
  go.
  eapply absinfer_eq.
  (* return -1 *)
  hoare forward.
  (************** "mqdes" in legal range ****************)
  (* new code about part_pos_rgn *)
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply absinfer_pos_rgn_choice2_cons; eauto.
   go.
   eapply absinfer_eq.
   hoare_lifts_trms_pre (Aop, mqdes, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
   eapply part_pos_rgn_proof.
   introv Hsat; sep auto.
   pure_auto.
   can_change_aop_solver.
   simpl; auto.
   simpl; auto.
   simpl;auto.
   hoare normal pre.
   eapply ex_intro_rule; intro vtemp_num.
   eapply ex_intro_rule; intro vtemp_dom.
   clear v'1 v'2. rename v'3 into v'1.
   (* end of new code *)

  assert (Hposv_range: Int.ltu i Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  { rename Hif_false into H.
     simpl val_inj in*.
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in H.
    destruct (Int.ltu i Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) i) eqn: eq2;
    destruct (Int.eq i ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply semacc_int_eq_true in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in * );
    try destruct H;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear Hif_false Hchg.
  destruct Hposv_range as (E1 & E2 & E3).
  lets Hposv_neq: Int.eq_false E3.
  (* ENTER_CRITICAL *) 
  hoare forward prim.
  unfold EvtInv.
  hoare unfold. 
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  destruct v'12.
  hoare_assert_pure (length v'32 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr.  clear HeqH0. sep destroy Hsat. 
    eapply amqattr_len with (s:= x); eauto. } 
  eapply pure_split_rule'; introv Hl.

  eapply backward_rule1.
  introv Hsat.
  eapply AMqAttr_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned i)).
  sep cancel AMqAttr.
  eauto.
  rewrite Hl.
  unfold nat_of_Z.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare_split_pure_all.
  subst.
  lets Hgetp: new_array_type_vallist_match_que_getp H0.
  destruct Hgetp as (vv & Hvv & Hisptr).
  simpljoin1.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H10 E1 Hlemu.  
  destruct H00 as (et & wty & fl & maxm & ms & cm & mqc & Hget & H').
  destruct H' as (Hcs & Hwaittype & Hflags & Hmaxmsg & Hmsgsize & Hcurmsgs).
  rewrite Hvv in Hcs.
  assert (Hvv': nth_val' 5 v'41 = vv). 
  {
    eapply nth_val_nth_val'_some_eq; eauto. 
  }
  destruct Hcs as [Hnull | [Hholder | Hptr]]; simpljoin1. 
  (* pevent in EIB is Vnull *) 
  assert (Hnull: nth_val' 5 v'41 = Vnull).
  { clear -H18. congruence. }
  hoare forward.
  eapply lzh_if_then_rule.

  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  eapply bop_rv; eauto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split'; eauto. 
  sep get rv.
  {
    asserts_rewrite (nth_val' 5 v'41 = Vnull).
    { congruence. }
    simpl. pure_auto. 
  }
  go.

  (* EXIT_CRITICAL *)
  hoare_split_pure_all.
  clear H17.

  hoare_lifts_trms_pre (Aop, absmqattrid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqdelete_absimp_eptr_null; eauto.
  go. 
  eapply absinfer_eq.

  (* EXIT_CRITICAL in case event pointer is NULL *)  
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel AMqCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold AMqEIBs.
  sep split; eauto.
  eapply AMqAttr_select_sn_ex_strong; eauto. 
  sep pauto.
  auto. auto. auto. auto. auto. auto.
  auto.
  go.

  (* return -1 in case event pointer is NULL *)  
  hoare forward. 

  (* impossible path: ECB pointer is NULL while reaching return -1 *)
  hoare forward.
  hoare_split_pure_all.
  apply pfalse_rule.
  hoare_split_pure_all.
  rename H17 into Hinjor.
  rewrite Hnull in Hinjor.
  simpl in Hinjor.
  destruct Hinjor; tryfalse.

  (* case where the ECB pointer is the placeholder -- ruled out by assumption *)
  hoare_lifts_trms_pre (Aop, absmqattrid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqdelete_absimp_eptr_holder_abt; eauto. 
  go.
  eapply absinfer_eq.
  apply absabort_rule.

  (* ECB pointer is a valid pointer *)
  assert (Hvv': nth_val' 5 v'41 = Vptr x).
  { congruence. }
  hoare forward.
  eapply lzh_if_then_rule.

  (* impossible path *)
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  eapply bop_rv; eauto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split'; eauto. 
  sep get rv.
  { rewrite Hvv'.
    simpl. destruct x. pure_auto. 
  }
  go.

  (* impossibility of the current path *)
  hoare_split_pure_all.
  rename H17 into Hinj3.
  rewrite Hvv' in Hinj3. simpl in Hinj3. 
  destruct x. simpl in Hinj3.
  simpljoin1; tryfalse.

  (* if (OSIntNesting > 0) *)  
  instantiate (1:=Afalse).
   hoare forward.
  hoare_split_pure_all.
  apply pfalse_rule.
  hoare_split_pure_all.
  clear H17.

  unfold AGVars.
  hoare unfold.
  lzh_hoare_if.
  pure_auto.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply mqdelete_absimp_inest_err; eauto. 
  go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  hoare forward prim. 
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold AGVars.
  unfold AOSIntNesting.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel Aier.
  sep cancel AMqCap.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep normal. sep split; eauto.
  eapply AMqAttr_select_sn_ex_strong; eauto.  
  sep pauto.
  auto. auto. auto. auto. auto. auto.
  auto.
  go.
  (* return -1 *)
  hoare forward.

  assert (Hvptr: nth_val' 5 v'41 = Vptr x).
  {
    unfold nth_val'. auto.
  }
  clear H22.

  hoare_lifts_trms_pre Aop.
  eapply seq_rule.

  (* p ′ =ₑ efield (Mq_Attr ′ [mqdes ′]) pevent *)
  eapply assign_rule_lvar.
  split; introv Hsat.
  sep_lifts_trms_in Hsat (Alvarmapsto p).
  eauto.
  sep_lifts_trms (Alvarmapsto p).
  auto.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split'; eauto.
  { go. apply eq_vptr. do 2 eexists. splits; eauto. } 
  { sep pauto. sep cancel p_local. sep pauto. }

  lets Hsplit: H0.  (* new_array_type_vallist_match mq_attr_t ... *)
  eapply new_array_type_vallist_match_split' in Hsplit; eauto.
  destruct Hsplit as (Hmt1 & Hmt2 & Hstmt).
  lets Hvl: struct_type_vallist_match_elim_7 Hstmt.
  simpljoin1.
  simpl in Hvptr.
  subst.

  (* efield (Mq_Attr ′ [mqdes ′]) pevent =ₑ NULL;ₛ *)
  hoare_lifts_trms_pre Aop.
  eapply seq_rule.
  hoare_assign_array_struct_part.
  apply eq_tnull; eauto.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local). 
  eapply backward_rule1. 
  introv Hsat. 
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  hoare_assign_evaux.
  unfold isevloc; auto.
  rename v'38 into locmp.
  rename v'39 into ptrmp.
  rename v'33 into semeibs.
  rename v'34 into muxeibs.
  rename v'35 into mqeibs.
  rename v'9 into els.
  rename x into qid.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).   
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_normal)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hque: is_que els qid).
  { eapply H16; eauto. }
  assert (Href: eib_ref semeibs muxeibs mqeibs qid). 
  {
    unfold eib_ref. 
    right; right.
    unfold mqeib_ref. do 6 eexists; eauto. 
  }
  assert (Hncre: ~ (exists t0, (get locmp t0 = Some (V$ __EvLoc_ecbcre1) \/ get locmp t0 = Some (V$ __EvLoc_ecbcre2)) /\ evptr_of_tsk t0 ptrmp qid)). 
  { eapply eib_ref_no_cre; eauto. }
  assert (Hndel: ~exists t, tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel qid).
  {
    introv Hex.
    destruct Hex as (t0 & Htle).
    lets H00: ecb_del H1 H2 H3 Htle.
    simpljoin1.
    tryfalse.
  }
  fold_evaux_q_loc (V$ __EvLoc_ecbdel) ( Vptr qid).

  hoare_lifts_trms_pre (Aop, absmqattrid, curtid, evlocid, evptrid).
  casetac v (Vptr qid) He Hne.
  2: {
    (* v <> Vptr qid *)
    eapply abscsq_rule.
    apply noabs_oslinv. 
    eapply mqdelete_absimp_get_ecb_ptr_abt; eauto.
    unfold CurTid. go.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  (* v = Vptr qid *) 
  subst.
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply mqdelete_absimp_get_set_ecb_ptr_ok; eauto. 
  unfold CurTid. go.
  eapply absinfer_eq.

  lets Hq_nc': Hq_nc Hget.

  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  unfold p_local, LINV, OSLInv.
  unfold AGVars.
  unfold EvtInv.
  unfold tcbllsegevaux.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel Aier.
  sep cancel llsegevaux.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel AMqCap.
  get_hsat Hsat.
  simpl nth_val' in Hsat.
  instantiate (2:=(v'12++((x6 :: x0 :: x1 :: x2 :: x3 :: Vnull :: x5 :: nil)::v'40))). 
  eapply AMqAttr_select_sn_ex_strong; eauto.
  sep pauto.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel Astruct.
  eauto.
  
  clear -E1 E2 E3 Hrgn3 Hrgn4.
  assert (Int.unsigned i < OS_USER_MAX_EVENTS / 3).
  {
    apply Intlt_false_is_Zge in E2.
    rewrite Int.unsigned_repr in E2.
    assert (Int.unsigned i <> OS_USER_MAX_EVENTS / 3).
    { intro Hf. apply E3. destruct Hf. clear - E3. int auto. }
    auto with zarith.
    int auto.
  }
  (* change (OS_USER_MAX_EVENTS / 3) with 6. *)
  lets H00: unsigned_ge0 i.
  clear -H H00 Hrgn3 Hrgn4.
  auto with zarith.
  split; auto.
  rewrite <- Hl.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.
  apply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_semdel_preserve; eauto.
  eapply evdel_nodup_qdel_preserve; eauto.
  eapply evcre_nodup_set_qdel_preserve; eauto.
  assert (Hnqref: ~eib_ref semeibs muxeibs (set mqeibs i (Null, wty, fl, maxm, ms, cm, mqc)) qid).  
  {
    introv Her.
    lets H00: eibref_distinct_mqref_clear_neibref H6 Hget Her. auto.
  }
  eapply mq_ecb_p_qdel_preserve; eauto. 
  eapply mux_ecb_p_qdel_preserve; eauto.
  eapply sem_ecb_p_qdel_preserve; eauto.
  eapply RH_Q_NOT_IN_CORE_P_hold_neid; eauto.
  introv Hf; simpljoin; tryfalse.
  eapply RH_EIB_ECB_Q_P_set_null_preserve; eauto.
  auto.
  eapply MqCapArray_P_hold; eauto.
  asserts_rewrite (
      (x6 :: x0 :: x1 :: x2 :: x3 :: Vnull :: x5 :: nil) =
      update_nth_val 5 (x6 :: x0 :: x1 :: x2 :: x3 :: Vptr qid :: x5 :: nil) Vnull).
  { simpl. auto. }
  eapply MqEIBAarray_P_set_null_preserve_zero; eauto.
  unfold isevloc. splits; eauto.
  auto.
  pure_auto.

  (********* call OSQDel *********)
  simpl nth_val'.
  hoare forward.
  intros. pauto.
  pure_auto.

  sep pauto. sep cancel p_local. sep auto.
  sep pauto. sep cancel p_local. sep auto.

  hoare unfold.
  inverts H26. (* eq. on logic val. *)
  clear -E1 E2 E3 Hq_nc'.

  (* ENTER_CRITICAL *)
  hoare forward prim.
  unfold EvtInv.
  hoare_split_pure_all.

  hoare_lifts_trms_pre (tcbllsegevaux, AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegevaux_split3_join2_frm'' in Hsat; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_evaux.
  unfold isevloc; auto.
  rename v'37 into locmp.
  rename v'38 into ptrmp. 
  rename v'31 into semeibs.
  rename v'32 into muxeibs.
  rename v'34 into mqeibs.
  rename v'7 into els.
  assert (Hevptr: get ptrmp tid = Some (Vnull, Vnull, Vnull)).    
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hloc: get locmp tid = Some (V$ __EvLoc_ecbdel)). 
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }

  hoare_lifts_trms_pre (Aop, curtid, evlocid, evptrid). 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqdelete_absimp_reset_loc_ok; eauto. 
  go. unfold CurTid. go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *)
  fold_evaux_q_loc (V$ os_code_defs.__EvLoc_normal) Vnull.
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold p_local, LINV, OSLInv.
  sep pauto; eauto.
  unfold EvtInv.
  unfold tcbllsegevaux.
  sep pauto; eauto.
  lets Hset: Hevptr.
  eapply get_set_same in Hset.
  unfold set in Hset; simpl in Hset.
  rewrite Hset in *.
  trycancel.
  sep cancel llsegevaux.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  eapply evdel_nodup_set_normal_loc_preserve; eauto.
  eapply evcre_nodup_set_normal_loc_preserve; eauto. 
  eapply mq_ecb_p_set_normal_loc_preserve; eauto. 
  eapply mux_ecb_p_set_normal_loc_preserve; eauto. 
  eapply sem_ecb_p_set_normal_loc_preserve; eauto.
  unfold isevloc. splits; eauto.
  auto.
  pure_auto.

  (*************** return 0 **************)
  hoare forward. 

  Unshelve.
  exact 0%nat. exact 0%nat. exact 0%nat.
Qed.

