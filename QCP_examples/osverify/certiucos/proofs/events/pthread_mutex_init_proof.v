
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import os_mutex_cap.
Require Import abs_op.
Require Import ifun_spec.

(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt. 
Require Import ucos_frmaop.

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

Require Import partition_common.
Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import protect.
Require Import partinv_lemmas.

Require Import evt_spec_defs.
Require Import sem_common.
Require Import gjb_common.
Require Import gjb_sem_common.
Require Import gjb_mutex_common.
Require Import err_list_common.
Require Import ev_aux_code.
Require Import pos_list_common.
Require Import evauxvar_lemmas.
Require Import evaux_pure.
Require Import seplog_trm_tacs.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Open Scope int_scope.

Lemma mutex_init_absimp_muxerr:
  forall sch vmux vattr ventity verr rv_attr posv rv_prioc rv_cre  rv_verr P vr_temp_dom vr_temp_num,
    can_change_aop P ->
    (vmux = Vnull \/
     (exists a,
         vmux = Vptr a /\
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true))) ->
    absinfer sch 
             (<|| mutex_init (vmux :: vattr :: ventity :: verr :: rv_attr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_attr_null:
  forall sch vmux vattr ventity verr rv_attr posv rv_prioc rv_cre  rv_verr P vr_temp_dom vr_temp_num,
    can_change_aop P ->
    vattr = Vnull ->
    absinfer sch 
             (<|| mutex_init (vmux :: vattr :: ventity :: verr :: rv_attr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||>  ** P)
             (<|| mutexattrinit (ventity :: rv_attr :: nil);;
                      (mutex_init_attr_no_free (|rv_attr :: nil|)
                          ?? mutex_init_attr_succ (|(* vattr :: ventity :: *) rv_attr :: nil|);;
                          mutex_init_after_get_attr (vmux :: ventity :: verr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil)) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma mutex_init_absimp_attr_no_free:
  forall sch rv_attr P s,
    can_change_aop P ->
    Int.eq rv_attr Int.zero = false ->
    absinfer sch 
             (<|| mutex_init_attr_no_free (| Vint32 rv_attr :: nil|)  ?? s ||>  ** P)
             (<|| END (Some (Vint32 (Int.repr EINVAL))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_attr_succ:
  forall sch vmux (* vattr *) verr posv rv_prioc rv_cre ventity  rv_verr P s vr_temp_dom vr_temp_num,
    can_change_aop P ->
(*     vattr = ventity  -> *)
    absinfer sch 
             (<|| s ?? (mutex_init_attr_succ (|(* vattr :: ventity :: *) Vint32 Int.zero :: nil|);;
                          mutex_init_after_get_attr (vmux :: ventity :: verr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil)) ||>  ** P)
             (<|| mutex_init_after_get_attr (vmux :: ventity :: verr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||> ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma mutex_init_absimp_after_get_attr:
  forall sch vmux vattr ventity verr rv_attr posv rv_prioc rv_cre  rv_verr P attr vr_temp_dom vr_temp_num,
    can_change_aop P ->
    vattr = Vptr attr  ->
    absinfer sch 
             (<|| mutex_init (vmux :: vattr :: ventity :: verr :: rv_attr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||>  ** P)
             (<|| mutex_init_after_get_attr (vmux :: vattr :: verr :: posv :: rv_prioc :: rv_cre ::  rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||> ** P).
Proof.
  intros.
  do 2 (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
Qed.


Lemma mutex_init_absimp_pos_abt:
  forall sch posv P muxinfo cpn idx left right s,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~(exists pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
                    MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
                      left <= Int.unsigned pos < right) /\ 
            posv <> V$ 255 \/
        (exists pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
                      MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
                      posv <> Vint32 pos)) ->
    absinfer sch 
             (<|| mutex_init_pos (| posv :: Vint32 idx :: Vint32 cpn :: nil |);; s ||>  ** HMuxInfo muxinfo ** P)
             (<|| ABORT ||> ** HMuxInfo muxinfo ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HMuxInfo muxinfo ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
  trivial. trivial.
Qed.

Lemma mutex_init_absimp_pos_cons:
  forall sch posv P muxinfo s cpn idx left right,
    can_change_aop P ->
    left = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx ->
    right = OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * (Int.unsigned idx + 1) ->
    (~(exists pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
                    MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
                      left <= Int.unsigned pos < right) /\ 
            posv = V$ 255 \/
        (exists pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
                      MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
                      posv = Vint32 pos)) ->
    absinfer sch 
             (<|| mutex_init_pos (| posv :: Vint32 idx :: Vint32 cpn :: nil |);; s ||>  ** HMuxInfo muxinfo ** P)
             (<|| s ||> ** HMuxInfo muxinfo ** P).
Proof.
  infer_solver 0%nat.
  exists posv muxinfo. do 4 eexists.
  left. splits; eauto.
  destruct s0 as [[[[[]]]]].
  destruct H3. simpljoin1.
  simpl in *.
  destruct H7.
  subst x. subst x2.
  eapply OSAbstMod.join_sig_get in H6.
  auto.
  Unshelve.
  exact None.
Qed.

Lemma mutex_init_absimp_poserr:
  forall sch pos P s,
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = true ->
    absinfer sch 
             (<|| mutex_init_poserr (|Vint32 pos :: nil|) ?? s  ||>  ** P) 
             (<|| END (Some (Vint32 (Int.repr EAGAIN))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_set_placeholder: 
  forall sch pos muxinfo muxinfo' e ow tp rcnt prot prioc wq cnsa s0 P mc,
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<||mutex_init_poserr (|Vint32 pos :: nil|) ?? (mutex_init_set_placeholder (|Vint32 pos :: nil|) ;; s0) ||> ** 
                 HMuxInfo muxinfo ** P)
             (<|| s0 ||> ** HMuxInfo muxinfo' ** P). 
Proof.
  intros.
  infer_solver 1%nat. 
Qed.

Lemma mutex_init_absimp_attr_none: 
  forall sch P s1 s2 evstructheapb attr t l,
    can_change_aop P ->
    (Get_struct evstructheapb attr = None \/
      Get_struct evstructheapb attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ->
    absinfer sch 
             (<|| (mutex_init_attr_none (|Vptr attr :: nil|) ?? s1) ;; s2 ||> ** 
                 HEvStructHeap evstructheapb ** P)
             (<|| ABORT ||> ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HEvStructHeap evstructheapb ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  (eapply absinfer_trans; try (eapply absinfer_choice1; try eauto)).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Lemma mutex_init_absimp_get_attr_prioceiling_abt: 
  forall sch P s1 s2 evstructheapb attr rv_prioc attr_vl pip,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_prioceiling attr_vl = Some (Vint32 pip) ->
    0 <= Int.unsigned pip < 64 ->
     rv_prioc <> Vint32 pip (* \/ ~(0 <= Int.unsigned pip < 64) *) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_get_attr_prioceiling (|Vptr attr :: rv_prioc :: nil|)) ;; s2 ||> ** 
                 HEvStructHeap evstructheapb ** P)
             (<|| ABORT ||> ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HEvStructHeap evstructheapb ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_abt; try eauto.
  absimp_abt_solver'.
Qed.

Lemma mutex_init_absimp_get_attr_prioceiling: 
  forall sch P s1 s2 evstructheapb attr rv_prioc attr_vl pip,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_prioceiling attr_vl = Some (Vint32 pip) ->
     rv_prioc = Vint32 pip ->
     (0 <= Int.unsigned pip < 64) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_get_attr_prioceiling (|Vptr attr :: rv_prioc :: nil|)) ;; s2 ||> ** 
                 HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HEvStructHeap evstructheapb ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_end; try eauto);
  try eauto.
  infer_solver 1%nat.
Qed.

Lemma mutex_init_absimp_set_ecb_ptr_null:
  forall sch P s0 pos muxinfo muxinfo' e ow tp rcnt prot prioc wq cnsa mc
                locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (Vnull, semp, qp) -> 
    muxinfo' = set muxinfo pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<|| (mutex_init_set_ecb_ptr (|Vint32 pos :: Vnull :: nil|) ??
                        mutex_init_holder_abt (| Vnull :: nil |)) ;; s0 ||> ** 
              HMuxInfo muxinfo ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HMuxInfo muxinfo' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HMuxInfo muxinfo' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
Qed.

Lemma mutex_init_absimp_set_ecb_ptr_n_null:
  forall sch P s0 pos muxinfo muxinfo' e ow tp rcnt prot prioc wq cnsa eid mc
                locmp ptrmp locmp' ptrmp' ct muxp semp qp, 
    can_change_aop P -> 
    Int.eq pos (Int.repr 255) = false -> 
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    locmp' = set locmp ct (Vint32 (Int.repr __EvLoc_normal)) ->
    get ptrmp ct = Some (muxp, semp, qp) -> 
    ptrmp' = set ptrmp ct (Vnull, semp, qp) -> 
    muxinfo' = set muxinfo pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    eid <> vhold_addr -> 
    absinfer sch 
             (<|| (mutex_init_set_ecb_ptr (|Vint32 pos :: Vptr eid :: nil|) ??
                        mutex_init_holder_abt (| Vptr eid :: nil |)) ;; s0 ||> ** 
              HMuxInfo muxinfo ** HEvLoc locmp ** HEvPtr ptrmp ** HCurTCB ct ** P) 
             (<|| s0 ||> ** HMuxInfo muxinfo' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).   
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto. 
  instantiate (1:= HMuxInfo muxinfo' ** HEvLoc locmp' ** HEvPtr ptrmp' ** HCurTCB ct ** P).
  pure_auto.
  instantiate (1:=END None).
  infer_solver 0%nat.
  unfold tidsame.
  repeat (rewrite set_a_get_a'; eauto).
  eapply absinfer_seq_end; pure_auto.
Qed.

Lemma mutex_init_absimp_set_ecb_holder_abt: 
  forall sch P s0 pos,
    can_change_aop P -> 
    absinfer sch 
             (<|| (mutex_init_set_ecb_ptr (|Vint32 pos :: Vptr vhold_addr :: nil|) ??
                        mutex_init_holder_abt (| Vptr vhold_addr :: nil |)) ;; s0 ||> ** P)
             (<|| ABORT ||> ** P).   
Proof.
  introv Hcop.
   eapply absinfer_trans;
  try eapply absinfer_seq;
  try (eapply absinfer_seq_abt; try eauto);
  try eauto.
  (eapply absinfer_trans; try (eapply absinfer_choice2; try eauto)).
  eapply absinfer_abt; eauto.
  absimp_abt_solver. 
  Unshelve.
  exact None.
Qed.

Lemma mutex_init_absimp_err_none:
  forall P sch verr ebls s1 s2,
    can_change_aop P ->
    ((exists errid, verr = Vptr errid /\ get ebls errid = None) \/
       verr = Vnull) ->
    absinfer sch
             ( <|| mutex_init_err_none (| verr :: nil|) ?? s1 ;; s2 ||> ** Hebls ebls ** P)
             (<|| ABORT ||> ** Hebls ebls ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (Hebls ebls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
   eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutex_init_absimp_get_verr:
  forall s1 s2 sch P errid ed ebls rv_verr, 
    can_change_aop P ->
    get ebls errid = Some ed ->
    rv_verr = Vint32 ed ->
    absinfer sch 
             (<|| s1 ?? mutex_init_get_verr (| Vptr errid :: rv_verr :: nil|) ;; s2 ||> ** Hebls ebls ** P) 
             (<|| s2 ||> ** Hebls ebls ** P). 
Proof.
  infer_solver 1%nat. 
Qed.

Lemma mutex_init_absimp_get_verr_abt:
  forall s1 s2 sch P errid ed ebls rv_verr, 
    can_change_aop P ->
    get ebls errid = Some ed ->
    rv_verr <> Vint32 ed ->
    absinfer sch 
             (<|| s1 ?? mutex_init_get_verr (| Vptr errid :: rv_verr :: nil|) ;; s2 ||> ** Hebls ebls ** P) 
             (<|| ABORT ||> ** Hebls ebls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (Hebls ebls ** P)) by can_change_aop_solver.
  eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
   eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma mutex_init_absimp_create_error:
  forall pos s1 s2 sch P err, 
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false -> 
    Int.eq err ($ OS_NO_ERR) = false ->
    absinfer sch 
             (<|| mutex_init_create_err (|Vint32 pos :: Vint32 err :: nil|) ?? s1 ;; s2 ||> ** P) 
             (<|| END (Some (Vint32 (Int.repr EAGAIN))) ||> ** P). 
Proof.
  infer_solver 0%nat. 
Qed.

Lemma mutex_init_absimp_create_succ:
  forall pos s1 s2 sch P, 
    can_change_aop P ->
    Int.eq pos (Int.repr 255) = false -> 
    absinfer sch 
             (<|| s1 ?? mutex_init_create_succ (|Vint32 pos :: Vint32 (Int.repr OS_NO_ERR) :: nil|) ;; s2 ||> ** P) 
             (<|| s2 ||> ** P). 
Proof.
  infer_solver 1%nat. 
Qed.


Lemma mutex_init_absimp_set_cancel: 
  forall sch P s1 s2 evstructheapb attr attr_vl muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa cnsa' mc,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_cancelsafe attr_vl = Some (Vint32 cnsa') ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq, cnsa', mc) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_set_cancel (| Vint32 pos :: Vptr attr :: nil|)) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  eapply absinfer_trans; try eapply absinfer_seq_end.
  instantiate (1:= HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P).
  eapply absinfer_seq; can_change_aop_solver.
  infer_solver 1%nat.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma mutex_init_absimp_set_protocol: 
  forall sch P s1 s2 evstructheapb attr attr_vl muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa prot' mc,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_protocol attr_vl = Some (Vint32 prot') ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot', prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_set_protocol (| Vint32 pos :: Vptr attr :: nil|)) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  eapply absinfer_trans; try eapply absinfer_seq_end.
  instantiate (1:= HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P).
  eapply absinfer_seq; can_change_aop_solver.
  infer_solver 1%nat.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma mutex_init_absimp_set_prioceiling: 
  forall sch P s1 s2 evstructheapb attr attr_vl muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa prioc' mc,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_prioceiling attr_vl = Some (Vint32 prioc') ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc', wq, cnsa, mc) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_set_prioceiling (| Vint32 pos :: Vptr attr :: nil|)) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  eapply absinfer_trans; try eapply absinfer_seq_end.
  instantiate (1:= HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P).
  eapply absinfer_seq; can_change_aop_solver.
  infer_solver 1%nat.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma mutex_init_absimp_set_type: 
  forall sch P s1 s2 evstructheapb attr attr_vl muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa rec mc,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_recursive attr_vl = Some (Vint32 rec) ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, rec, rcnt, prot, prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_set_type (| Vint32 pos :: Vptr attr :: nil|)) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  eapply absinfer_trans; try eapply absinfer_seq_end.
  instantiate (1:= HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P).
  eapply absinfer_seq; can_change_aop_solver.
  infer_solver 1%nat.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma mutex_init_absimp_set_waitq: 
  forall sch P s1 s2 evstructheapb attr attr_vl muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa wq' mc,
    can_change_aop P ->
    Get_struct evstructheapb attr = Some (attr, pthread_mutexattr_t, attr_vl) ->
    V_muxattr_waitq attr_vl = Some (Vint32 wq') ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq', cnsa, mc) ->
    absinfer sch 
             (<|| (s1 ?? mutex_init_set_waitq (| Vint32 pos :: Vptr attr :: nil|)) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** HEvStructHeap evstructheapb ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P). 
Proof.
  intros.
  eapply absinfer_trans; try eapply absinfer_seq_end.
  instantiate (1:= HMuxInfo muxinfo' ** HEvStructHeap evstructheapb ** P).
  eapply absinfer_seq; can_change_aop_solver.
  infer_solver 1%nat.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma mutex_init_absimp_set_recursive: 
  forall sch P s2  muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa mc,
    can_change_aop P ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, ow, tp, Int.zero, prot, prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<|| mutex_init_set_recursive (| Vint32 pos :: nil|) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_set_owner: 
  forall sch P s2  muxinfo muxinfo' pos
                e ow tp rcnt prot prioc wq cnsa mc,
    can_change_aop P ->
    get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa, mc) -> 
    muxinfo' = set muxinfo pos (e, None, tp, rcnt, prot, prioc, wq, cnsa, mc) ->
    absinfer sch 
             (<|| mutex_init_set_owner (| Vint32 pos :: nil|) ;; s2 ||> ** 
                 HMuxInfo muxinfo ** P)
             (<|| s2 ||> ** HMuxInfo muxinfo' ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_mux_pos:
  forall sch P vmux pos pbls,
    can_change_aop P ->
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true ->
    (exists posv, get pbls vmux = Some posv) ->
    absinfer sch 
             (<|| mutex_init_set_mux (| Vptr vmux :: Vint32 pos :: nil |) ||>  ** Hpbls pbls **P)
             (<|| END (Some (Vint32 Int.zero)) ||> ** Hpbls (set pbls vmux pos) ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mutex_init_absimp_mux_pos_abt:
  forall sch P vmux pos pbls,
    can_change_aop P ->
    cmpaddr Clt userAddrStart vmux = true ->
    cmpaddr Cle vmux userAddrEnd = true ->
    ~(exists posv, get pbls vmux = Some posv) ->
    absinfer sch 
             (<|| mutex_init_set_mux (| Vptr vmux :: Vint32 pos :: nil |) ||>  ** Hpbls pbls ** P)
             (<|| ABORT ||> ** Hpbls pbls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (Hpbls pbls ** P)) by can_change_aop_solver.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
Qed.

Open Scope code_scope.

Lemma muxb_get_not_null':
  forall muxvl embls hld vll1 vll2 idx cpn,
    EIBMAarray_P (Vint32 Int.zero) muxvl embls hld ->
    PthreadMutex_full_P' vll1 idx cpn ->
    vll1 ++ vll2 = muxvl ->
    length vll1 = ∘ (((OS_USER_MAX_EVENTS / 3)/(Int.unsigned cpn)) * (Int.unsigned idx + 1)) ->
    length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) ->
   ~(exists  pos ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
          MibMod.get embls pos = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\ 
         OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn * Int.unsigned idx <= (Int.unsigned pos) < Z.of_nat (length vll1)).
Proof.
introv He Hf Heq Hl1 Hl.
funfold Hf.
introv H.
simpljoin.
eapply muxb_corr_alt' in He; eauto.
instantiate (1:= x) in He.
simpljoin.
unfold get in *.
unfold MibMap in *.
match goal with H: MibMod.get embls _ = _, H': MibMod.get embls _ = _ |- _ => rewrite H' in H; inverts H end.
destruct H4 as [ | [ | ]]; simpljoin; tryfalse.
eapply Hf; eauto.
erewrite <- nth_error_eq_nth_vallist in *.
unfold nat_of_Z in *.
match goal with H: nth_error (_ ++ _) _ = _ |- _ => rewrite nth_error_app1 in H; auto with zarith end.
eapply ge0_z_nat_le; auto with zarith.
apply Int.unsigned_range_2.
rewrite app_length.
auto with zarith.
Qed.

Lemma muxb_getnull':
  forall vl vll1 vll2 embls hld i idx cpn,
    EIBMAarray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) embls hld ->
    nth_PthreadMutex_free_P' i (vll1 ++ vl :: vll2) idx cpn ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    exists  ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
      MibMod.get embls (Int.repr i) = Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
      V_OSMUXINFOPevent vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  unfold nat_of_Z in *.
  rewrite <- Hl1 in H0.
  rewrite nth_vallist_get_idx in H0; inverts H0.
  rewrite app_length in Hl2.
  simpl in Hl2.
  rewrite Hl1 in Hl2.
  assert (Hi: ( i < (OS_USER_MAX_EVENTS / 3))).
  auto with zarith.
  assert (Hi': 0 <= i <= Int.max_unsigned).
  split.
  eapply Z.le_trans; eauto.
  eapply Ztac.mul_le; try apply Int.unsigned_range_2.
  assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
  destruct Hc as [Hc | Hc].
  rewrite Hc.
  rewrite Zdiv_0_r; auto with zarith.
  eapply Z.div_pos; try solve_usr_max_evts_rgn.
  pose proof (Int.unsigned_range_2 cpn).
  auto with zarith.
  solve_usr_max_evts_rgn.
  eapply muxb_corr with (i:= Int.repr i) in He; auto with zarith.
  simpljoin.
  unfold V_OSMUXINFOPevent in *.
  unfold get in *; simpl in *.
  match goal with H: MibMod.get _ _ = _ |- _ => rewrite H end.
  match goal with H: _ \/ _ \/ _ |- _ => destruct H as [ ? | [ ? | ? ]]; simpljoin;
  match goal with
  H: nth_val ?n _ = _ , H': nth_val ?n _ = _ |- _ => rewrite H in H'; inverts H'; try rewrite H end
  end.
  repeat eexists; eauto.
  rewrite Int.unsigned_repr; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  rewrite Int.unsigned_repr; auto with zarith.
Qed.

Lemma MutexInitPartProof:
forall (tid : tid) (attr' x: addrval) verr ventity posv rv_prioc rv_cre rv_verr v'0 v'1 v'2 v'3 er  vr_temp_dom vr_temp_num,
 isptr verr ->
 cmpaddr Clt userAddrStart x = true ->
 cmpaddr Cle x userAddrEnd = true ->
{|OS_spec, GetHPrio, OSLInv, I,
fun v : option val =>
( <|| END v ||>  **
 p_local OSLInv tid init_lg **
 ((EX v0 : val, LV err @ (char_t) ∗ |-> v0) **
  (EX v0 : val, LV attrEntity @ pthread_mutexattr_t ∗ |-> v0) **
  (EX v0 : val, LV attr @ pthread_mutexattr_t ∗ |-> v0) **
  (EX v0 : val, LV mutex @ pthread_mutex_t ∗ |-> v0) **
  (EX v0 : val, LV i @ long |-> v0) **
  (EX v0 : val, LV prio @ long |-> v0) **
  (EX v0 : val, LV os_code_defs.pos @ long |-> v0) **
  (EX v0 : val, LV os_code_defs.x @ char_t |-> v0) **
  (EX v0 : val, LV y @ long |-> v0) **
  (EX v0 : val, LV z @ long |-> v0) **
  (EX v0 : val, LV p @ OS_EVENT ∗ |-> v0) ** Aemp) **
 Aie true ** Ais nil ** Acs nil ** Aisr empisr ** (EX er, Aier er)) **
A_dom_lenv
  ((err, (char_t) ∗)
   :: (attrEntity, pthread_mutexattr_t ∗)
      :: (attr, pthread_mutexattr_t ∗)
         :: (mutex, pthread_mutex_t ∗)
            :: (i, long)
               :: (prio, long)
                  :: (os_code_defs.pos, long)
                     :: (os_code_defs.x, char_t)
                        :: (y, long) :: (z, long) :: (p, OS_EVENT ∗) :: nil),
Afalse|}|- tid
{{Aie true **
   Ais nil **
   Acs nil **
   Aisr empisr **
   Aier er  **
    <||
   mutex_init_after_get_attr
     (Vptr x :: Vptr attr' :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr ::  vr_temp_dom :: vr_temp_num :: nil) ||>  **
   p_local OSLInv tid init_lg **
   LV z @ long |-> v'0 **
   LV os_code_defs.x @ char_t |-> (V$ 1) **
   LV prio @ long |-> Vint32 ($ 0 -ᵢ $ 1) **
   LV i @ long |-> (V$ 0) **
   LV p @ OS_EVENT ∗ |-> v'1 **
   LV y @ long |-> v'3 **
   LV os_code_defs.pos @ long |-> v'2 **
   LV err @ (char_t) ∗ |-> verr **
   LV attrEntity @ pthread_mutexattr_t ∗ |-> ventity **
   LV attr @ pthread_mutexattr_t ∗ |-> Vptr attr' **
   LV mutex @ pthread_mutex_t ∗ |-> Vptr x **
   A_dom_lenv
     ((err, (char_t) ∗)
      :: (attrEntity, pthread_mutexattr_t ∗)
         :: (attr, pthread_mutexattr_t ∗)
            :: (mutex, pthread_mutex_t ∗)
               :: (i, long)
                  :: (prio, long)
                     :: (os_code_defs.pos, long)
                        :: (os_code_defs.x, char_t)
                           :: (y, long) :: (z, long) ::  (p, OS_EVENT ∗) :: nil)}}
ENTER_CRITICAL;ₛ
os_code_defs.x′ =ᶠ getFreePos(·′1·);ₛ 
os_code_defs.pos′ =ₑ 〈Int32〉 os_code_defs.x′;ₛ
If (os_code_defs.pos ′ ==ₑ ′ 255){EXIT_CRITICAL;ₛ
RETURN ′ EAGAIN};ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent =ₑ
〈 OS_EVENT ∗ 〉 PlaceHolder;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
y ′ =ₑ attr ′ → prio_ceiling;ₛ
EXIT_CRITICAL;ₛ
p ′ =ᶠ OSMutexCreate (·〈Int8u〉y ′, err ′·);ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent =ₑ p ′;ₛ
OSTCBCur ′ → __OSTskMuxPtr =ₑ NULL;ₛ
OSTCBCur ′ → __OSTskEvLoc =ₑ ′ os_code_defs.__EvLoc_normal;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
os_code_defs.x′ =ₑ ∗err′;ₛ
EXIT_CRITICAL;ₛ
If (os_code_defs.x′ !=ₑ ′OS_NO_ERR){RETURN ′ EAGAIN};ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) cancel_safe =ₑ
attr ′ → cancel_safe;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) protocol =ₑ attr ′ → protocol;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) recursive_cnt =ₑ ′ 0;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) mutex_owner =ₑ ′ 255;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) prio_ceiling =ₑ
attr ′ → prio_ceiling;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) mutex_type =ₑ
attr ′ → recursive;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
efield (Pthread_Mutex ′ [os_code_defs.pos ′]) waitq_type =ₑ
attr ′ → waitq_type;ₛ
EXIT_CRITICAL;ₛ
ENTER_CRITICAL;ₛ
∗ mutex ′ =ₑ os_code_defs.pos ′;ₛ
EXIT_CRITICAL;ₛ
RETURN ′ 0 {{Afalse}}.
Proof.
 introv Hptr_verr Hmux_start Hux_end.
 
   lets Hrgn: usr_max_evts_rgn.
   destruct Hrgn as (Hrgn3 & Hrgn4).
   assert (Hevt: Z.of_nat ∘ (OS_USER_MAX_EVENTS / 3) = (OS_USER_MAX_EVENTS / 3)).
   { clear - Hrgn3 Hrgn4. unfold nat_of_Z. auto with zarith. }

  (*ENTER_CRITICAL;ₛ*)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat PartitionInv.
  eapply unfold_PartitionInv_frm; eauto.
  unfold PartitionInv_part2.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (R_Cpartnum_Dom2idx_P).
  eapply pure_split_rule'; introv Hrcpn0.
  hoare_lifts_trms_pre (AMqEIBs, ASemEIBs, AMuxEIBs).
  unfold AMqEIBs.
  unfold ASemEIBs.
  unfold AMuxEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (AMqCap, AMuxCap, ASemCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMqCap ?l1 ?vl1 ** AMuxCap ?l2 ?vl2 ** ASemCap ?l3 ?vl3 ** _ }} _ {{ _ }} =>
  rename l1 into lmq; rename l2 into lmux; rename l3 into lsem;
  rename vl1 into mqcapvl; rename vl2 into muxcapvl; rename vl3 into semcapvl end.
  hoare_lifts_trms_pre ( MqCapArray_P, length  mqcapvl, MuxCapArray_P, length muxcapvl,
                                              SemCapArray_P, length semcapvl).
  eapply pure_split_rule'; introv Hmqcap_vl.
  eapply pure_split_rule'; introv Hmqcap_len.
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  eapply pure_split_rule'; introv Hsemcap_vl.
  eapply pure_split_rule'; introv Hsemcap_len.
  hoare_lifts_trms_pre ( RH_SEM_NOT_IN_CORE_P, RH_Q_NOT_IN_CORE_P ).
  eapply pure_split_rule'; introv Hs_nc.
  eapply pure_split_rule'; introv Hq_nc.
  hoare unfold.
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  hoare_lifts_trms_pre (array_type_vallist_match, RLH_Dom2idx_P, RHL_Dom2idx_P, Int.mone).
  eapply pure_split_rule'; introv Hdom_mat; destruct Hdom_mat as (Hdom_mat & Hlen_dom).
  eapply pure_split_rule'; introv Hlh_dom.
  eapply pure_split_rule'; introv Hhl_dom.
  eapply pure_split_rule'; introv Hcd_cases.
  hoare_lifts_trms_pre (Aisr, Ais).
  transform_pre elim_aemp_isr_is_prop ltac:(idtac).

  hoare_lifts_trms_pre (Aop, kscurdom).
  match goal with
  | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** HKsCurDomain ?idx ** _ }} _ {{ _ }} =>
     rename idx into vcurd
  end.
  assert(Hvcurd : vcurd = Int.mone \/ vcurd <> Int.mone) by tauto.
  destruct Hvcurd as [Habt | Hvcurd].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_kscurdom_ext_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_kscurdom_ext; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  destruct Hcd_cases as [Hcd_rgn | Hf]; try subst; tryfalse; auto.

  hoare_lifts_trms_pre (Aop, Domain2Index, ksCurDomain).
  match goal with
  | H: length ?vl = ?len
    |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ Domain2Index _ ?vl ** GV ksCurDomain @ _ |-> Vint32 ?idx ** _ }} _ {{ _ }} =>
     assert (Hle_len: (Z.to_nat (Int.unsigned idx) < len)%nat)
  end.
  solve_part_int_rgn.
  lets Hnth: Hle_len.
  eapply pure_lib.nthval'_has_value in Hnth; eauto.
  destruct Hnth as (rv_dom & Hnth & Hmat).
  hoare_lifts_trms_pre (Aop, kscurdom, domindexlist).
  match goal with
    H: RLH_Dom2idx_P _ _ |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** _ ** HDomain2index ?absdomls ** _ }} _ {{ _ }} =>
     rename absdomls into domls
  end.
  assert (Hget_dom:get domls  vcurd = Some rv_dom).
  eapply Hlh_dom; eauto.
  eapply inline_bittblfunctions.nth_val'2nth_val; eauto.

  assert (Hrv_dom: vr_temp_dom <> Vint32 rv_dom \/ vr_temp_dom = Vint32 rv_dom) by tauto.
  destruct Hrv_dom as [Habt | Hrv_dom].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_dom_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_dom.

  hoare_lifts_trms_pre (Aop, cpartnum).
  match goal with
    | |- {| _ , _, _, _, _, _ |} |- _ {{ <|| _ ||> ** Hcorepartnum ?cpn ** _ }} _ {{ _ }} =>
     rename cpn into rv_cpn
  end.
  assert (Hrv_num: vr_temp_num <> Vint32 rv_cpn \/ vr_temp_num = Vint32 rv_cpn) by tauto.
  destruct Hrv_num as [Habt | Hrv_num].
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_get_temp_num_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  subst vr_temp_num.

  (*x ′ =ᶠ getFreePos (·′ 1·);ₛ*)
  eapply seq_rule.
  hoare_lifts_trms_pre Aop.
  eapply calle_rule_lvar'; 
            [ intuition eauto  | 
              intros; do 5 try 
                         (apply rvl_elim;[ symbolic_execution | ]);
              first [apply rvl_nil | simpl;auto] | 
              intros;  unfold_spec |
              idtac |
              idtac |
              simpl;eauto | 
              sep_unfold_funpost |
              sep_unfold_funpre 
              ].
  (* hoare forward. *)
  unfold Adomain2index.
  unfold Adomain2index'.
  unfold AKsCurDomain.
  unfold ACorepartnum.
  sep normal. sep eexists.
  sep cancel Domain2Index.
  sep cancel ksCurDomain.
  sep cancel ACorepartnum'.
  sep cancel domindexlist.
  sep cancel cpartnum.
  sep cancel APthreadMutex.
  sep cancel p_local.
  sep cancel ASeminfo.
  sep cancel AMqAttr.
  trycancel.
  sep cancel A_isr_is_prop.
  sep cancel Aier.
  sep cancel Aop.
  sep cancel os_code_defs.x.
  sep split; eauto.
  simpl. eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat;
  do 5 try (get_hsat Hsat; destruct Hsat; sep pauto).

  introv Hsat. 
  sep destruct Hsat.
  destruct Hsat as [Hsat | Hsat];
  do 5 (try destruct Hsat as [Hsat | Hsat];
   try (sep destruct Hsat;
  eexists; sep cancel p_local; simpl; auto)).

   introv Hsat. 
  sep destruct Hsat.
  eexists; sep cancel p_local; simpl; auto.

  hoare_ex_intro.
(*   hoare_lifts_trms_pre ( RH_SEM_NOT_IN_CORE_P, RH_Q_NOT_IN_CORE_P ).
  eapply pure_split_rule'; introv Hs_nc.
  eapply pure_split_rule'; introv Hq_nc. *)
  hoare unfold.
  eapply backward_rule1.
  introv Hsat; 
  do 2 (eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat];
  [ sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse| idtac]).
  eapply disj_split in Hsat; eapply adisj_intro;
    destruct Hsat as [Hsat | Hsat]; [left; eauto | right].
  eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat]; [eauto | idtac].
  false.
  eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat];
  try (sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse).
  eapply disj_split in Hsat;
  destruct Hsat as [Hsat | Hsat];
  try (sep normal in Hsat; sep destruct Hsat;
                   sep split in Hsat; tryfalse).
  change ($ 1) with Int.one in *.
  simpl nth_val in *.
  match goal with H: Some _ = Some _ /\ _ /\ _ /\ _ |- _ =>
  destruct H as (Heq & _ & Hf & _); inverts Heq end.
  tryfalse.
  rename H0 into Hsem_p; rename H10 into Hrh_sem; 
  rename H2 into Hmq_p; rename H12 into Hrh_mq. (* new add *)

  hoare forward;
  hoare normal pre;
  [ do 7 try (eapply ex_intro_rule; intros) | do 6 try (eapply ex_intro_rule; intros)];
  eapply ex_intro_rule; intro dom2index;
  eapply ex_intro_rule; intro domls';
  eapply ex_intro_rule; intro kscurd;
  eapply ex_intro_rule; intro cpn;
  eapply ex_intro_rule; intro idx;
  [ eapply ex_intro_rule; intro lsem';
    eapply ex_intro_rule; intro lmux';
    eapply ex_intro_rule; intro lmq'
   | eapply ex_intro_rule; intro muxvll1;
     eapply ex_intro_rule; intro muxvll2;
     eapply ex_intro_rule; intro lsem';
     eapply ex_intro_rule; intro lmux';
     eapply ex_intro_rule; intro lmq'];
  hoare_lifts_trms_pre (DOMAIN_SIZE, R_Cpartnum_Dom2idx_P, nth_val');
  try (eapply pure_split_rule'; introv Hvcd_rgn;
           destruct Hvcd_rgn as (Hvcd_rgn1 & Hvcd_rgn2);
          eapply pure_split_rule'; introv Hrcpn;
          eapply pure_split_rule'; introv Hnth_dom);
  try (hoare_lifts_trms_pre ( muxvll2, length muxvll1);
           eapply pure_split_rule'; introv Hmux_eq;
           eapply pure_split_rule'; introv Hlen_muxvll1;
           protect Hmux_eq);
  hoare unfold; try inverts H12; (* eq. on logicl *) 
  rewrite Hnth_dom in Hnth; inverts Hnth.

  (* start PthreadMutex_full_P *)
  2: {
    (* pos ′ =ₑ 〈 long 〉 x ′;ₛ *)
    hoare forward.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split; sep pauto.
    intros.
    eapply cast_rv_tint8_tint32.
    symbolic_execution.
    simpl; auto.
    apply assign_type_match_true; simpl; auto.

    intros.
    sep pauto. sep cancel p_local. sep pauto.

    (* If (pos ′ ==ₑ ′ 255) *)
    hoare forward.
    rewrite Int.eq_true.
    hoare unfold.
    hoare_lifts_trms_pre (APthreadMutex).
    match goal with | |- {| _ , _, _, _, _, _ |} |- _ {{ APthreadMutex _ ?vl ** _ }} _ {{ _ }} =>
    hoare_assert_pure (length vl = ∘ (OS_USER_MAX_EVENTS / 3))
    end.
    {
      get_hsat Hsat.
      sep_lift_context_in Hsat APthreadMutex.
      eapply apthreadmutex_len_frm in Hsat.
      auto.
  Optimize Proof.
  Optimize Heap.
    }
    hoare_split_pure_all.
    lets Hget_full: muxb_get_not_null' H H2 Hmux_eq Hlen_muxvll1 H15.
    rewrite Hlen_muxvll1 in Hget_full.
    unfold nat_of_Z in Hget_full.
    rewrite Z2Nat.id in Hget_full; auto with zarith.
    2:{ pose proof (Int.unsigned_range_2 rv_dom).
           eapply Ztac.mul_le; auto with zarith.
           assert (Hc: Int.unsigned cpn = 0 \/ Int.unsigned cpn <> 0) by tauto.
           destruct Hc as [Hc | Hc].
            rewrite Hc.
            rewrite Zdiv_0_r; auto with zarith.
            eapply Z.div_pos; try solve_usr_max_evts_rgn.
            pose proof (Int.unsigned_range_2 cpn).
            auto with zarith. }
(*     rewrite Hevt in Hget_full. *)
    hoare_lifts_trms_pre (Aop, absmutinfoid). 
    assert (Hposv: posv = V$ 255 \/ posv <> V$ 255) by tauto.
    destruct Hposv as [Hposv | Hposv].
    (* posv <> V$ 255 *)
    2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mutex_init_absimp_pos_abt.
      can_change_aop_solver.
      eauto. eauto.
      left. splits; auto.
      eapply absinfer_eq.
      apply absabort_rule.
    }
    (* posv = V$ 255 *)
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutex_init_absimp_pos_cons.
    can_change_aop_solver.
    eauto. eauto.
    left. splits; auto.
    eapply absinfer_eq.
    instantiate (1:= Afalse).
    subst posv.

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutex_init_absimp_poserr.
    can_change_aop_solver. rewrite Int.eq_true; auto.
    apply absinfer_eq.

    (*EXIT_CRITICAL;ₛ*)
    transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
    hoare forward prim.
    unfold EvtInv.
    unfold AMuxEIBs.
    sep cancel Aier.
    sep normal; sep eexists.
    sep cancel AMuxCap.
    sep pauto; eauto.
    trycancel.
    sep cancel APthreadMutex.
    sep cancel p_local.
    unfold ASemEIBs.
    unfold AMqEIBs.
    sep normal; sep eexists.
    sep cancel ASeminfo.
    sep cancel AMqAttr.
    sep cancel APthreadAttr.
    sep cancel ASemCap.
    sep cancel AMqCap.
    sep split; eauto.
    eapply fold_PartitionInv_frm.
    unfold PartitionInv_part2.
    sep normal; sep eexists.
    trycancel_PartitionInv.
    sep pauto; eauto.
    sep cancel CapabilityInv.
    eauto.
    auto.
    pure_auto.
    hoare forward. (*RETURN *)

    eapply hoare_disj_afalseP_l_pre.
    rewrite Int.eq_true. hoare_split_pure_all.
    match goal with H: val_inj _ = _ \/ _ |- _ => simpl in H; destruct H; tryfalse end.
  }
  (* end PthreadMutex_full_P *)


  (* start nth_PthreadMutex_free_P *)
   match goal with
   H: nth_PthreadMutex_free_P' ?vy _ ?vidx ?vcpn |- _ =>
   assert (Hpos_range: 
                  (OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * Int.unsigned vidx <= vy <
                  OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1))%Z) by
   (funfold H; auto);
   rename vy into pos;
   hoare_assert_pure (1 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned vcpn * (Int.unsigned vidx + 1) 
                                        <= OS_USER_MAX_EVENTS / 3)
   end.
   { get_hsat Hsat.
      unfold ACorepartnum, ACorepartnum' in Hsat.
      sep split in Hsat. simpljoin.
      eapply user_max_evts_part_succ_rgn; auto with zarith.
      eapply Hrcpn0; eauto.
      eapply inline_bittblfunctions.nth_val'2nth_val; eauto.
    }
   eapply pure_split_rule'; introv Hpos_range'.
   destruct Hpos_range' as (Hpos_rgn1 & Hpos_rgn2).
   assert (Hdiv_rgn: 0 <= OS_USER_MAX_EVENTS / 3 / Int.unsigned cpn
                                                * Int.unsigned rv_dom).
  {
     eapply Ztac.mul_le; auto with zarith.
     apply Int.unsigned_range_2.
  }

  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; sep pauto.
  intros.
  eapply cast_rv_tint8_tint32. 
  symbolic_execution.
  clear -Hpos_range Hpos_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
  change (Byte.max_unsigned) with 255.
  simpljoin.
  rewrite Int.unsigned_repr; try (split; solve_usr_max_evts_rgn).
  match goal with | |- (if ?p then _ else _) = _ => destruct p eqn:eq1; auto with zarith end.
  simpl; auto.
  apply assign_type_match_true; simpl; auto.

  intros.
  sep pauto. sep cancel p_local. sep pauto. 

  assert (Hif_false: Int.eq ($ pos) ($ 255) = false). 
  {
    clear -Hpos_range Hpos_rgn2 Hdiv_rgn Hrgn3 Hrgn4.
    int auto.
  }

  hoare forward. 
  pure_auto.
  rewrite Hif_false.
  hoare unfold.
  simpl val_inj in *. tryfalse.
  instantiate (1:=Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
   match goal with H: val_inj _ = _ \/ _  |- _ => clear H end.
  (* val_inj ... = ... \/ ...*)
  (*split APthreadMutex*)
  destruct lmux' as (lmux_b & lmux_i).
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat.
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range Hpos_rgn2 Hdiv_rgn.
  rewrite Hl.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.
  match goal with H: EIBMAarray_P _ (_ ++ ?vl :: _) ?abs _ |- _ =>
  rename abs into muxls; rename vl into muxvl end.
  assert (Hget_null:
                  exists ow tp rcnt prot0 prioc0 wq0 cnsa0 mc,
                    MibMod.get muxls ($ pos) =
                          Some (Null, ow, tp, rcnt, prot0, prioc0, wq0, cnsa0, mc) /\
                    V_OSMUXINFOPevent muxvl = Some Vnull).
  {
    eapply muxb_getnull'; eauto. 
  }
  destruct Hget_null as (ow & tp & rcnt & prot & prioc & wq & cnsa & mc & Hget_null & Hvnull). 

  hoare_lifts_trms_pre (Aop, absmutinfoid).
  assert (Hposv: posv = Vint32 ($ pos) \/ posv <> Vint32 ($ pos)) by tauto.  
  destruct Hposv as [Hposv | Hposv].
  (* posv <> Vint32 ($ pos) *)
  2: {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutex_init_absimp_pos_abt.
    can_change_aop_solver.
    eauto. eauto.
    right. repeat eexists; eauto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  (* posv = Vint32 ($ pos) *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_pos_cons.
  can_change_aop_solver.
  eauto. eauto.
  right. repeat eexists; eauto.
  eapply absinfer_eq.
  subst posv.

  (*efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent =ₑ 〈 OS_EVENT ∗ 〉 os_mutex.PlaceHolder;ₛ *)
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H0.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst muxvl.

  unfold AOSTCBPrioTbl.
  hoare normal pre.
  hoare_ex_intro.
  hoare forward.
  auto with zarith.
  {
   introv Hsat.
   unfold PlaceHolder.
   eapply cast_rv_tptr.
   eapply addrof_gvar_rv.
   apply astar_l_anotinlenv_intro.
   sep cancel (Agvarenv' OSPlaceHolder).
   eauto.
    sep_lift_context_in Hsat A_dom_lenv.
    apply astar_l_adomlenv_elim in Hsat.
    destruct Hsat.
    match goal with H: eq_dom_env _ _ |- _ => clear -H; unfolds in H; rename H into Henv end.
    unfold EnvMod.indom.
    pure_auto.
    destruct H as [[]].
    assert (~ (ListSet.set_In (OSPlaceHolder, t)
                              ((err, (char_t) ∗)
         :: (attrEntity, pthread_mutexattr_t ∗)
            :: (attr, pthread_mutexattr_t ∗)
               :: (mutex, pthread_mutex_t ∗)
                  :: (i, long)
                     :: (prio, long)
                        :: (os_code_defs.pos, long)
                           :: (x, char_t)
                              :: (y, long) :: (z, long) :: (p, OS_EVENT ∗) :: nil))).
    simpl.
    repeat (eapply Classical_Prop.and_not_or; split; [pure_auto | idtac]).
    auto.
  Optimize Proof.
  Optimize Heap.
    eapply H0. rewrite Henv. eauto.
    simpl; auto.
  }
  (* end of assign PlaceHolder *)

  hoare unfold.
  hoare_lifts_trms_pre (Aop, absmutinfoid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_set_placeholder; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.

  (* EXIT_CRITICAL;ₛ *)
  transform_pre add_aemp_isr_is_prop ltac:(sep cancel Aisr;
                                        sep cancel Ais; sep cancel Aier).
  hoare forward prim.
  sep cancel tcbdllflag.
  unfold AOSTCBPrioTbl.
  unfold EvtInv.
  unfold AMuxEIBs.
  assert (Hup: ((x9 :: x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: Vptr vhold_addr :: x5 :: nil)) = 
               update_nth_val 8 (x9 :: x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: nil) (Vptr vhold_addr))
  by (simpl; auto).
  sep normal; sep eexists.
  sep cancel AMuxCap.
  sep pauto; eauto.
  sep cancel (Aptrmapsto).
  unfold ASemEIBs. unfold AMqEIBs.
  sep normal; sep eexists.
  sep cancel ASemCap. sep cancel AMqCap.
  sep cancel ASeminfo. sep cancel AMqAttr.
  sep cancel Aier.
  sep cancel APthreadAttr.
  trycancel.
  sep split; eauto.
  sep cancel OSPlaceHolder.
  sep cancel p_local.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (x9 :: x8 :: x7 :: x6 :: x0 :: x1 :: x2 :: x3 :: Vptr vhold_addr :: x5 :: nil).
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep_lifts_trms PartitionInv.
  eapply fold_PartitionInv_frm.
  unfold PartitionInv_part2.
  sep normal; sep eexists.
  trycancel_PartitionInv.
  sep pauto; eauto.
  sep cancel CapabilityInv.
  eauto.
  match goal with H: length (_ ++ _ :: _) = ∘ (OS_USER_MAX_EVENTS / 3) |- _ =>
  rewrite <- H end.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & _).
  simpl. splits; auto.

  eapply eibref_distinct_null_holder_preserve_mux; eauto.
  3: {
    eapply SEM_ECB_P_null_holder_preserve_mux; eauto.
  }
  2: { 
    eapply MUX_ECB_P_null_holder_preserve_mux; eauto.
  }
  eapply Q_ECB_P_null_holder_preserve_mux; eauto. 
  eapply RH_ECBlk_EIBlk_Mux_P_set_to_hold; eauto.
  eapply MuxCapArray_P_hold; eauto.
  {
    rewrite Hup.
    assert (Hpos_eq: (Int.unsigned ($ pos)) = pos).
    { rewrite Int.unsigned_repr; auto.
       split; auto with zarith.  try solve_usr_max_evts_rgn. }
    eapply EIBMAarray_P_hold_for_update_to_hold'; eauto.
    rewrite Hpos_eq; auto.
    eapply Int.unsigned_range_2.
  }
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)

  (* ENTER_CRITICAL;ₛ y ′ =ₑ attr ′ → prio_ceiling;ₛ EXIT_CRITICAL;ₛ *)
  rename H18 into Hpos_range1.
  rename H19 into Hpos_range2.
  assert (Hpos_ge: 0 <= pos).
  { auto with zarith. }
  clear -Hptr_verr Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hrgn3 Hrgn4
              Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* y ′ =ₑ attr ′ → prio_ceiling;ₛ *)
   hoare forward.
   go.
   assert (Hrv_prioc_range: (0 <= Int.unsigned i3 < 64)).
   { clear -H9.
      funfold H9.
      assert (Heq: pthread_mutexattr_t = pthread_mutexattr_t) by auto.
      eapply H9 in Heq.
      mytac.
      inverts H.
      split; auto.
    }
   hoare_lifts_trms_pre (Aop, evstructheapid).
   assert (Hrv_prioc: rv_prioc = Vint32 i3 \/ rv_prioc <> Vint32 i3) by tauto.
   destruct Hrv_prioc as [Hrv_prioc | Hrv_prioc].
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_get_attr_prioceiling_abt; eauto. 
            can_change_aop_solver.
            unfold V_muxattr_prioceiling; simpl. auto.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst rv_prioc.
   rename i3 into rv_prioc.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_get_attr_prioceiling; eauto. 
   can_change_aop_solver.
   unfold V_muxattr_prioceiling; simpl. auto.
   eapply absinfer_eq.
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists.
   sep split; eauto.
   sep cancel Astruct.
   sep cancel attr.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel tcbdllflag.
   sep cancel p_local.
   sep cancel Aier.
   unfold EvtInv.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMuxEIBs.
   sep cancel AMqEIBs.
   sep cancel APthreadAttr.
   sep cancel CapabilityInv.
   eauto.
   auto.
  Optimize Proof.
  Optimize Heap.
   pure_auto.
   (* end of get attr ′ → prio_ceiling *)
    clear -Hptr_verr Hmux_start Hux_end Hif_false Hrv_prioc_range Hpos_range1 Hpos_range2 Hrgn3 Hrgn4
                Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.

  (*p ′ =ᶠ OSMutexCreate (·〈Int8u〉y ′, err ′·);ₛ;ₛ*)
  (* Int.modu x ($ Byte.modulus) *)
  assert (Hrv_prioc_eq: (Int.modu rv_prioc ($ Byte.modulus)) = rv_prioc).
  { eapply OSMutex_common.mutexpost_intlemma1. destruct Hrv_prioc_range; auto. }
  change (Vint32 rv_prioc :: verr :: rv_cre :: nil) with ((Vint32 rv_prioc :: verr :: nil) ++ (rv_cre :: nil)).
  eapply seq_rule.
  eapply forward_rule2.
  Ltac hoare_calle_lvar' :=
  match goal with
  | |- {|_, _, ?li, _, _, _|}|- ?ct {{?P}} scalle ?x ′ _ ?el {{_}} =>
        match find_aop P with
        | some ?n =>
            hoare lifts (n :: nil) pre; eapply calle_rule_lvar';
             [ intuition
             eauto
             | intros; do 5 try (apply rvl_elim; [ symbolic_execution |  ]); (first
                [ apply rvl_nil | simpl; auto ])
             | intros; unfold_spec; sep normal; sep eexists; sep_cancel_iers(* ; sep pauto *)
             | 
             | 
             | simpl; eauto
             | sep_unfold_funpost
             | sep_unfold_funpre ]
        | none _ => idtac
        end
  end.
  hoare_calle_lvar'.
  2: {
      sep cancel p_local.
      rewrite Hrv_prioc_eq.
      sep cancel Aop.
      sep pauto.
  }
  pure_auto.
  pure_auto.

  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat. sep destruct Hsat.
  sep split in Hsat. simpljoin1. pure_auto.
  
  rewrite Hrv_prioc_eq.
  assert (Hprioc_range': Int.unsigned rv_prioc <= 255) by (clear -Hrv_prioc_range; int auto).
  eapply mutex_pend_pure.mund_int_a2 in Hprioc_range'; rewrite Hprioc_range'.
  pure_auto.

  introv Hsat. sep destruct Hsat.
  sep pauto. sep cancel p_local. sep auto.

  introv Hsat. sep destruct Hsat. 
  sep pauto. sep cancel p_local. sep auto.

  try sep_unfold_funpost;
  first [ intros s H; exact H
            | sep pauto ].

  hoare unfold.
  rename H1 into Hretor.
  inverts H. (* logic_val ... = logic_val ... *)

 (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.

  (* efield (Pthread_Mutex ′ [os_code_defs.pos ′]) pevent =ₑ p ′;ₛ*)
  (*split APthreadMutex*)
  destruct lmux as (lmux_b & lmux_i).
  eapply backward_rule1.
  intros.
  get_hsat Hsat.
   sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
 instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  mytac.

  (*assign rule*)
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)  
  lets Hsplit : H1. (* new_array_type_vallist_match ... *)
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.

  hoare forward.
  pure_auto.
  (* end of assign *) 

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
  match goal with H: SEM_ECB_P ?loc ?ptr ?ecb ?fecbh ?fecbvl ?sem ?mux ?mq |- _ =>
  rename loc into locmp; rename ptr into ptrmp; rename ecb into ecbls;
  rename sem into semeibs; rename mux into muxeibs; rename mq into mqeibs
  end.
  match goal with H: join (sig _ (?vp , _, _)) _ _ |- _ => rename vp into cur_evp end.
  match goal with H : join (sig tid ?vt) _ ?abs, H' : join _ ?abs locmp |- _ => rename vt into vct end.
  assert (Hloc: get locmp tid = Some vct).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Hevptr: get ptrmp tid = Some (cur_evp, Vnull, Vnull)).
  {
    eapply join_get_get_r; eauto.
    eapply join_get_get_l; eauto.
    join auto.
  }
  assert (Heid: forall eid, cur_evp = Vptr eid -> (~ eib_ref semeibs muxeibs mqeibs eid) /\ is_mux ecbls eid).  
  {
    introv Hevp.
    subst cur_evp.
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull; tryfalse.
    destruct Heptr as (_ & Hcre2).
    subst.
    eapply mux_ecb_cre2; eauto.
  } 
  assert (Hncre1: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre1 eid)). 
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. subst.
    eapply evcre_nodup_cre1_cre2_contra_mux; eauto.
  }
  assert (Hncre2: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbcre2 eid)).
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. subst.
    eapply evcre_nodup_cre2_cre2_contra_mux; eauto.
  }
  assert (Hndel: forall eid,
             cur_evp = Vptr eid ->
             ~(exists t, t <> tid /\ tsk_loc_ev locmp ptrmp t __EvLoc_ecbdel eid)).  
  {
    introv Hcp Hex. subst cur_evp.
    destruct Hex as (t & Htneq & Htle).
    destruct Hretor as [Hnull | Heptr].
    destruct Hnull. tryfalse.
    destruct Heptr. subst.
    specialize (Heid eid (eq_refl _)). destruct Heid.
    eapply ecbdel_mux_contra; eauto.    
  }
  (* end of assign evaux *)
  assert (Hposv_eq: pos = Int.unsigned (Int.repr pos)).  
  {
    rewrite int_usign_eq; auto.
    solve_usr_max_evts_rgn.
  }
  rewrite Hposv_eq in H15.
  lets H00: muxb_corr H H15.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H23 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  destructs H26. (* isflag ... /\ isevloc ... /\ ... *)
  unfold isevptr, isptr in H26.
  eapply seq_rule.
  instantiate (1:= ( 
<|| mutex_init_err_none (|verr :: nil|)
  ?? mutex_init_get_verr (|verr :: rv_verr :: nil|);;
     (mutex_init_create_err (|V$ pos :: rv_verr :: nil|)
      ?? mutex_init_create_succ (|V$ pos :: rv_verr :: nil|);;
         (mutex_init_attr_none (|Vptr attr' :: nil|)
          ?? mutex_init_set_cancel (|V$ pos :: Vptr attr' :: nil|));;
         (mutex_init_attr_none (|Vptr attr' :: nil|)
          ?? mutex_init_set_protocol (|V$ pos :: Vptr attr' :: nil|));;
         mutex_init_set_recursive (|V$ pos :: nil|);;
         mutex_init_set_owner (|V$ pos :: nil|);;
         (mutex_init_attr_none (|Vptr attr' :: nil|)
          ?? mutex_init_set_prioceiling (|V$ pos :: Vptr attr' :: nil|));;
         (mutex_init_attr_none (|Vptr attr' :: nil|)
          ?? mutex_init_set_type (|V$ pos :: Vptr attr' :: nil|));;
         (mutex_init_attr_none (|Vptr attr' :: nil|)
          ?? mutex_init_set_waitq (|V$ pos :: Vptr attr' :: nil|));;
         mutex_init_set_mux (|Vptr x :: V$ pos :: nil|)) ||>  **
  Aisr empisr **
  Aie true **
  Ais nil **
  Acs nil **
  Aier v'6 **
  p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ os_code_defs.__EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
  LV os_code_defs.pos @ long |-> (V$ pos) **
  A_dom_lenv
    ((err, (char_t) ∗)
     :: (attrEntity, pthread_mutexattr_t ∗)
        :: (attr, pthread_mutexattr_t ∗)
           :: (mutex, pthread_mutex_t ∗)
              :: (i, long)
                 :: (prio, long)
                    :: (os_code_defs.pos, long)
                       :: (os_code_defs.x, char_t)
                          :: (y, long) :: (z, long) :: (p, OS_EVENT ∗) :: nil) **
  LV p @ OS_EVENT ∗ |-> cur_evp **
  LV attr @ pthread_mutexattr_t ∗ |-> Vptr attr' **
  LV y @ long |-> Vint32 rv_prioc **
  LV os_code_defs.x @ char_t |-> (V$ pos) **
  LV z @ long |-> v'0 **
  LV prio @ long |-> Vint32 ($ 0 -ᵢ Int.one) **
  LV i @ long |-> (V$ 0) **
  LV err @ (char_t) ∗ |-> verr **
  LV attrEntity @ pthread_mutexattr_t ∗ |-> ventity **
  LV mutex @ pthread_mutex_t ∗ |-> Vptr x )).

  destruct H25 as [Hvp_eq | (eid & Hvp)];
  subst cur_evp.
  destruct Hretor as [(Hvp_eq & Hvloc) | (Hvp_eq & Hvloc)]; tryfalse; subst. (* new add *)

  (* p is null *)
  hoare_lifts_trms_pre (Aop, absmutinfoid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_set_ecb_ptr_null; eauto.
  can_change_aop_solver.
  simpl. intros; auto.  
  eapply absinfer_eq.

  (* preparation for EXIT_CRITICAL;ₛ *)
  fold_evaux_mux Vnull.
  assert (Hset_loc: set locmp tid (V$ __EvLoc_normal) = locmp) 
    by (rewrite get_set_same; eauto).
  assert (Hset: set ptrmp tid (Vnull, Vnull, Vnull) = ptrmp) 
    by (rewrite get_set_same; eauto).
  unfold set in *. unfold EvAuxPtrMap, EvAuxLocMap, MibMap in *.
(*   rewrite Hset_loc. *)
 rewrite Hset.
  assert (Hup: (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: Vnull :: x5 :: nil)  = 
               update_nth_val 8 (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) Vnull) 
    by (simpl; auto).
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel Aier.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  unfold EvtInv.
  unfold AMuxEIBs.
  unfold tcbllsegevaux.
  sep normal; sep eexists.
  sep cancel AMuxCap.
  sep pauto; eauto.
  rewrite Hset_loc.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: Vnull :: x5 :: nil) .
  sep cancel AMqEIBs.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  splits; auto. rewrite Hposv_eq; auto.
  rewrite <- H13. 
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & _).
  simpl. splits; auto.

  eapply eibref_distinct_infonull_preserve_mux; eauto.
  eapply evdel_nodup_normal_preserve; eauto.
  eapply evcre_nodup_normal_preserve; eauto.
  3: { eapply sem_ecb_p_infonull_preserve_mux; eauto. }
  2: { eapply mux_ecb_p_infonull_preserve_mux; eauto. }
  eapply q_ecb_p_infonull_preserve_mux; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_null_preserve; eauto.
  eapply MuxCapArray_P_hold; eauto.
   {
    rewrite Hup.
    eapply EIBMAarray_P_hold_for_update_to_null'; eauto.
    apply Int.unsigned_range_2.
  }
  unfold isevptr. unfold isptr. unfold isevloc.
  splits; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  sep auto.
  (* end of EXIT_CRITICAL;ₛ *)

  (* p is not null *)
  destruct Hretor as [(Hvp_eq & Hvloc) | (Hvp_eq & Hvloc)]; tryfalse; subst.

  specialize (Heid eid (eq_refl _)).
  destruct Heid as (Hnref & Hismux).

  casetac eid vhold_addr Heq Hne.
  (* eid = vhold_addr *)
  subst eid.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_set_ecb_holder_abt; eauto.
  can_change_aop_solver.
  simpl. intros; auto.
  eapply absinfer_eq.
  apply absabort_rule.
  
  hoare_lifts_trms_pre (Aop, absmutinfoid, evlocid, evptrid, curtid).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_set_ecb_ptr_n_null; eauto.
  can_change_aop_solver.
  simpl. intros; auto.  
  eapply absinfer_eq.

  (* preparation for EXIT_CRITICAL;ₛ *)
  fold_evaux_mux_loc (V$ __EvLoc_normal) (Vnull).
  assert (Hup: (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: Vptr eid :: x5 :: nil)  = 
               update_nth_val 8 (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vptr eid)) 
    by (simpl; auto).
(*   rewrite <- Hset. *)
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel CurTid.
  sep cancel flag_off.
  try_cancel_evaux_asst.
  unfold EvtInv.
  unfold AMuxEIBs.
  unfold tcbllsegevaux.
  sep normal; sep eexists.
  sep cancel AMuxCap.
  sep pauto; auto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel llsegevaux.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa ::
                                                 x1 :: Vint32 rcnt :: x3 :: Vptr eid :: x5 :: nil) .
  sep cancel AMqEIBs.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  splits; auto. rewrite Hposv_eq; auto.
  rewrite <- H13. 
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Hup.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & _).
  simpl. splits; auto.

  eapply eibref_distinct_noref_eid_preserve_mux; eauto.
  eapply evdel_nodup_normal_null_preserve; eauto.
  eapply evcre_nodup_normal_null_preserve; eauto. 
  3: { eapply SEM_ECB_P_normal_null_preserve_mux; eauto. }
  2: { eapply MUX_ECB_P_normal_null_preserve_mux; eauto. }
  eapply Q_ECB_P_normal_null_preserve_mux; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_ptr_preserve; eauto.
  eapply MuxCapArray_P_hold; eauto.
   { rewrite Hup.
    eapply EIBMAarray_P_hold_for_update_to_ptr'; eauto.
    apply Int.unsigned_range_2.
  }
  unfold isevptr. unfold isptr. unfold isevloc.
  splits; eauto.
  auto.
  pure_auto.
  sep auto.
  (* end of EXIT_CRITICAL;ₛ *)

  (* ENTER_CRITICAL;ₛ os_code_defs.x ′ =ₑ ∗ err ′;ₛ EXIT_CRITICAL;ₛ  *)
   clear -Hptr_verr Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hrgn3 Hrgn4
                Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
   hoare unfold.
   hoare_lifts_trms_pre (Aop, eblsid, AErrblkList).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** Hebls ?abs ** _}} _ {{ _ }} =>
  rename abs into ebls end.
   destruct Hptr_verr as [Hverr_eq | (errid & Hverr_eq)];
   subst verr.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_err_none; eauto. 
   can_change_aop_solver.
   eapply absinfer_eq.
   apply absabort_rule.

   destruct (get ebls errid) eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_err_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   (* split AErrblkList ebls *)
   rename e into verr.
   hoare_lifts_trms_pre (AErrblkList).
   eapply backward_rule1.
   introv Hsat.
   eapply err_list_split_frm; eauto.
   unfold node.
   hoare unfold.
   inverts H8. inverts H9.
   (* os_code_defs.x ′ =ₑ ∗ err ′;ₛ *)
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat.
  sep cancel (Alvarmapsto os_code_defs.x). eauto.
  sep auto.
  introv Hsat.
  eapply deref_rv.
  sep get rv.
  simpl Astruct in Hsat.
  sep normal in Hsat.
  sep cancel 1%nat 1%nat. eauto.
  unfolds; pure_auto.
  eapply eq_int; auto.
   intros. eexists. sep cancel p_local. simpl; auto.
   hoare_lifts_trms_pre (Aop, eblsid).
   assert (Hrv_verr: rv_verr = Vint32 verr \/ rv_verr <> Vint32 verr) by tauto.
   destruct Hrv_verr as [Hrv_verr | Hrv_verr].
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_get_verr_abt; eauto.
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst rv_verr.
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_get_verr; eauto. 
   can_change_aop_solver.
   eapply absinfer_eq.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AErrblkList.
   sep pauto; eauto.
   trycancel.
   sep cancel ASemEIBs.
   sep cancel AMuxEIBs.
   sep cancel AMqEIBs.
   sep cancel APthreadAttr.
   eapply err_list_common.err_sllseg_merge; eauto.
   sep cancel err_sllseg.
   sep cancel err_sllseg.
   unfold node.
   sep cancel CapabilityInv.
   sep pauto; eauto.
   sep cancel Astruct.
   eauto.
   unfolds; simpl; auto.
   unfolds; simpl; auto.
   split; auto. go.
   auto.
  Optimize Proof.
  Optimize Heap.
   pure_auto.
   (* end of EXIT_CRITICAL *)

    rename H12 into Hverr_range.
    assert (Hpos_eq: (Int.unsigned ($ pos)) = pos).
    {  rewrite Int.unsigned_repr;auto.
        split; auto with zarith. solve_usr_max_evts_rgn. }
    clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
                Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   (* If ( os_code_defs.x ′ !=ₑ ′ OS_NO_ERR) *)
    hoare forward.
    pure_auto.
    pure_auto.
    pure_auto.
    instantiate (1:= Afalse).
    hoare unfold.
    destruct (Int.eq verr ($ OS_NO_ERR)) eqn: eq1;
    simpl in H; try change (Int.notbool Int.one) with Int.zero in H; tryfalse.
    hoare abscsq.
   apply noabs_oslinv.
   eapply mutex_init_absimp_create_error; eauto. 
   can_change_aop_solver.
   (* RETURN ′ EAGAIN  *)
   hoare forward.
   eapply hoare_disj_afalseP_l_pre.
   hoare unfold.
   destruct (Int.eq verr ($ OS_NO_ERR)) eqn: eq1;
   simpl in H; try change (Int.notbool Int.zero) with Int.one in H; 
   destruct H; tryfalse.
   eapply semacc_int_eq_true in eq1; subst verr.
    hoare abscsq.
   apply noabs_oslinv.
   eapply mutex_init_absimp_create_succ; eauto. 
   can_change_aop_solver.

  (* start assign cancel_safe *)
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).
   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H0 H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  (* process attr evheap*)
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* efield (Pthread_Mutex ′ [os_code_defs.pos ′]) cancel_safe =ₑ
         attr ′ → cancel_safe;ₛ *)
   hoare forward.
   go.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid, evstructheapid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_cancel; eauto.
   can_change_aop_solver.
   unfolds; simpl; eauto.
   eapply absinfer_eq.
   
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists.
   sep split; eauto.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   sep cancel attr.
   sep cancel (Astruct attr').
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 i :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 4 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 i))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. 
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 i :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H2.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_cancel'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of set cancel_safe *)

   (* start assign protocol *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z.
  eapply Z2Nat.inj_lt;  auto with zarith.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  (* process attr evheap*)
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* assign protocol *)
   hoare forward.
   go.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid, evstructheapid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_protocol; eauto.
   can_change_aop_solver.
   unfolds; simpl; eauto.
   eapply absinfer_eq.
   
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists.
   sep split; eauto.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   sep cancel attr.
   sep cancel (Astruct attr').
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 i2 :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 1 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 i2))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. 
  sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 i2 :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_protocol'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  pure_auto.
  (* end of set protocol *)

  (* start assign recursive_cnt *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z. int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  apply int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

   (* assign protocol *)
   hoare forward.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_recursive; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.

   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 ($ 0) :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 6 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 ($ 0)))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 ($ 0) :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_recurcnt_for_update_to_recurcnt'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of set protocol *)

  (* start assign owner *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z. int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

   (* assign owner *)
   hoare forward.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_owner; eauto.
   can_change_aop_solver.
   eapply absinfer_eq.

   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: Vint32 (Int.repr OS_MUTEX_AVAILABLE) :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 5 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 (Int.repr OS_MUTEX_AVAILABLE)))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: Vint32 ($ OS_MUTEX_AVAILABLE) :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  unfold OS_MUTEX_AVAILABLE.
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  clear -Hsp Heidor.
  simpl in Hsp. destruct Hsp as (Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & _).
  simpl. splits; auto. try splits; auto.
  unfold V_OSMUXINFOPevent in *; simpl in *.
  destruct Heidor as [ (_ & Heid) | [( _ & Heid) | (eid & _ & Heid & _)]];
  inverts Heid; auto.

  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { fold OS_MUTEX_AVAILABLE.
     rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_owner_none'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  pure_auto.
  (* end of set owner *)

  (* start assign prioceiling *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z. int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  (* process attr evheap*)
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* assign prioceiling *)
   hoare forward.
   go.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid, evstructheapid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_prioceiling; eauto.
   can_change_aop_solver.
   unfolds; simpl; eauto.
   eapply absinfer_eq.
   
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists.
   sep split; eauto.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   sep cancel attr.
   sep cancel (Astruct attr').
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 prot :: Vint32 i3 :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 2 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 i3))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 prot :: Vint32 i3 :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_prioceiling'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of set prioceiling *)

  (* start assign type *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
   eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z. int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
 lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  (* process attr evheap*)
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* assign type *)
   hoare forward.
   go.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid, evstructheapid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_type; eauto.
   can_change_aop_solver.
   unfolds; simpl; eauto.
   eapply absinfer_eq.
   
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists.
   sep split; eauto.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   sep cancel attr.
   sep cancel (Astruct attr').
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 i1  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 0 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 i1))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 i1  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_type'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  pure_auto.
  (* end of set type *)

  (* start assign waitq_type *)
   clear -Hmux_start Hux_end Hif_false Hpos_range1 Hpos_range2 Hverr_range Hpos_eq Hrgn3 Hrgn4
               Hpos_rgn1 Hpos_rgn2 Hdiv_rgn Hpos_ge.
   hoare forward prim.
   unfold EvtInv.
   unfold AMuxEIBs.
   hoare normal pre. hoare_ex_intro.
   hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
   hoare_lifts_trms_pre (AMuxCap).
  match goal with
  | |- {| _, _ , _, _, _, _ |} |- _ {{ AMuxCap ?l ?vl ** _ }} _ {{ _ }} =>
  rename l into lmux; rename vl into muxcapvl end.
  hoare_lifts_trms_pre (MuxCapArray_P, length muxcapvl).
  eapply pure_split_rule'; introv Hmuxcap_vl.
  eapply pure_split_rule'; introv Hmuxcap_len.
  hoare unfold.
  destruct lmux as (lmux_b & lmux_i).

   (*split APthreadMutex*)
  eapply backward_rule1.
  introv Hsat.
  sep_lift_context_in Hsat APthreadMutex.
  eapply APthreadMutex_unfold_any_idx_frm in Hsat.
  instantiate (1:= Z.to_nat pos) in Hsat. 
  eauto.
  lets Hl: apthreadmutex_len_frm Hsat.
  clear -Hl Hpos_range2 Hrgn3 Hrgn4 Hpos_rgn2 Hdiv_rgn Hpos_ge.
  rewrite Hl.
  unfold nat_of_Z. int auto.
  hoare unfold.
  (* unfold the vallist of  efield (Pthread_Mutex ′ [pos ′]) *)
  lets Hsplit : H1.
  eapply new_array_type_vallist_match_split1 in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_10 Hsp.
  repeat try (destruct Hvl as (? & Hvl)). subst.
  rewrite <- Hpos_eq in H12.
  lets H00: muxb_corr H H12.
  match type of H00 with _ -> _ -> ?R => assert (R); [apply H00 | ] end.
  rewrite int_ltu_zero_eq_false; auto.
  apply Int.unsigned_range_2.
  clear H00.
  destruct H11 as (eid_t & ow & tp & rcnt & prot & prioc & wq & cnsa & mc &(Hget & Heidor & Hvow)).
  destruct Hvow as (Hvow & Hvtp & Hvrcnt & Hvprioc & Hvprot & Hvwq & Hvcnsa).
  inverts Hvtp. inverts Hvrcnt. inverts Hvprioc. inverts Hvprot. inverts Hvwq. inverts Hvcnsa.

  (* process attr evheap*)
  hoare_lifts_trms_pre (Aop, evstructheapid, AEvStructHeap, (Alvarmapsto attr)).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** HEvStructHeap ?heap ** _}} _ {{ _ }} =>
  rename heap into evstructheap end.
  destruct (Get_struct evstructheap attr') eqn: eq1.
  2 : { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   destruct p as [[]].
   lets Hattr_eq: Get_struct_some_eq eq1.
   subst a.
   assert (Hattr_case: t = pthread_mutexattr_t \/ t <> pthread_mutexattr_t) by tauto.
   destruct Hattr_case.
   2: { eapply abscsq_rule.
            apply noabs_oslinv.
            eapply mutex_init_absimp_attr_none; eauto. 
            can_change_aop_solver.
            eapply absinfer_eq.
            apply absabort_rule.
         }
   subst t.
   rename l into attr_vl.
   (* split attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_unfold; eauto.
   hoare unfold.
   (* assign waitq_type *)
   hoare forward.
   go.
  (* end of assign *) 

   hoare_lifts_trms_pre (Aop, absmutinfoid, evstructheapid).
   eapply abscsq_rule.
   apply noabs_oslinv.
   eapply mutex_init_absimp_set_waitq; eauto.
   can_change_aop_solver.
   unfolds; simpl; eauto.
   eapply absinfer_eq.
   
   (* compose attr heap *)
   hoare_lifts_trms_pre (AEvStructHeap,(Alvarmapsto attr)).
   eapply backward_rule1.
   introv Hsat.
   eapply AEvStructHeap_fold; eauto.
   sep eexists. sep split; eauto.
   sep cancel AEvStructHeap.
   sep cancel AEvStructHeap.
   sep cancel attr.
   sep cancel (Astruct attr').
   eauto.
   go.
   (* exit critical *)
   hoare forward prim.
   sep cancel Aier.
   sep cancel tcbdllflag.
   sep cancel p_local.
   unfold EvtInv.
   unfold AMuxEIBs.
   sep normal; sep eexists.
   sep cancel AMuxCap.
   assert (Hup: (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 i0 :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) = 
               update_nth_val 3 (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 wq :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil) (Vint32 i0))
  by (simpl; auto).
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  eapply APthreadMutex_select_sn_ex_strong.
  eexists. exists (Z.to_nat pos). eexists.
  exists (Vint32 tp  :: Vint32 prot :: Vint32 prioc :: Vint32 i0 :: Vint32 cnsa :: x1 :: Vint32 rcnt :: x3 :: x4 :: x5 :: nil). 
  sep cancel Aarray_new.
  sep cancel Aarray_new.
  sep cancel CapabilityInv.
  sep pauto.
  rewrite Hpos_eq in H12.
  splits; auto.
  rewrite <- H10.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.

  eapply new_array_type_vallist_match_compose_struct; auto.
  eapply eibref_distinct_set_pos_muxeib_gen; eauto.
  eapply Q_ECB_P_set_mux_preserve_gen; eauto.
  eapply MUX_ECB_P_set_mux_preserve_gen; eauto.
  eapply SEM_ECB_P_set_mutex_preserve_gen; eauto.
  eapply RH_ECBlk_EIBlk_Mux_P_set_preserve_gen; eauto.
  eapply MuxCapArray_P_hold; eauto.
  { rewrite Hup.
     eapply EIBMAarray_P_hold_for_update_to_waitq'; eauto.
     apply Int.unsigned_range_2.
  }
  auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto.
  (* end of set waitq_type *)

  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
   hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata'.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, pblsid).
  match goal with
  | |- {| _, _, _, _, _, _ |} |- _ {{_ ** Hpbls ?abs ** _}} _ {{ _ }} =>
  rename abs into pbls end.
  assert (Hmux: (exists posv, get pbls x = Some posv) 
                \/ ~ (exists posv, get pbls x = Some posv)) by tauto.
  hoare_lifts_trms_pre (Aop, pblsid).
  destruct Hmux as [Hmux | Hmux].
  2 : {
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply mutex_init_absimp_mux_pos_abt; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  destruct Hmux as (posv & Hmux).
  (* split poslist *)
  eapply backward_rule1. 
  intros.
  eapply pos_list_split_frm.
  sep cancel APosblkList.
  eauto.
  eauto.
  unfold node.
  hoare unfold.
  inverts H25. inverts H26.
  (* ∗ mutex ′ =ₑ os_code_defs.pos ′;ₛ *)
  hoare_lifts_trms_pre (Aop, pblsid).
  hoare forward.
  simpl Astruct.
  match goal with
    | |- {| _, _, ?li, _, _, _ |} |- ?ct {{ ?P }} (sassign (ederef _) _) {{ _ }} =>
      match find_aop P with
        | none _ => fail 1
        | some ?a =>
          hoare lift a pre;
            eapply assign_rule_deref_ptr;
            [ symbolic execution
            | match goal with
                | |- ?P' <==> PV ?l @ _ |-> _ ** _ =>
                  match find_ptrmapsto P' l with
                    | none _ => fail 2
                    | some ?b => 
                      intros until s; split; intros Hnew;
                      [ sep lift b in Hnew; exact Hnew
                      | sep lift b;  exact Hnew ]
                  end
              end
            | symbolic execution
            | apply assign_type_match_true; simpl; auto
            | li_sepauto li ]
      end
  end.
  hoare_lifts_trms_pre (Aop, pblsid).

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mutex_init_absimp_mux_pos; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (*  EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  sep cancel Aier.
  sep cancel tcbdllflag.
  unfold EvtInv.
  unfold APosblkList.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel CapabilityInv.
  eapply pos_sllseg_merge.
  sep cancel pos_sllseg.
  sep cancel pos_sllseg.
  sep cancel p_local. sep cancel AMuxEIBs. sep cancel AMqEIBs.
  sep cancel APthreadAttr.
  instantiate (2:= (set v'84 (v'86, Int.zero) ($ pos))).
  instantiate (3:= (V$ pos :: v'82 :: nil)).
  unfold node.
  simpl Astruct.
  sep pauto.
  eapply PbMod.joinsig_set_set;eauto.
  instantiate (1:= $ pos).
  clear -H27.
  unfold TcbJoin in *. unfold join,sig,set in *. unfold PbMap in *.
  unfold PbMod.join in *.
  intros.
  specialize H27 with (a:= a).
  rewrite PbMod.sig_sem in *.
  rewrite PbMod.set_sem in *. 
  destruct (tidspec.beq (v'86, Int.zero) a) eqn: eq1;
  destruct (PbMod.get v'85 a); tryfalse; auto.
  unfold ev_aux_code.V_posblk_pos. simpl. auto.
  split; auto. go.
  rewrite PbMod.map_get_set. auto.
  auto.
  pure_auto.
  (* end of EXIT_CRITICAL;ₛ *)
  hoare forward.
  Unshelve.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
  exact Tnull.
  exact nil.
Qed.


Lemma MutexInitProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api pthread_mutex_init
              (mutex_init, (Tint32, Tptr pthread_mutex_t :: Tptr pthread_mutexattr_t :: Tptr pthread_mutexattr_t :: Tptr Int8u :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api pthread_mutex_init
              (mutex_init, (Tint32, Tptr pthread_mutex_t :: Tptr pthread_mutexattr_t :: Tptr pthread_mutexattr_t :: Tptr Int8u :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api pthread_mutex_init = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 8 (destruct v'; try apply absabort_rule).
  rename v'7 into er.
  rename x2 into vmux.
  rename x1 into vattr.
  rename x0 into ventity.
  rename v into rv_attr.
  rename v0 into posv.
  rename v1 into rv_prioc.
  rename x into verr.
  rename v2 into rv_cre.
  rename v3 into rv_verr.
  rename v4 into vr_temp_dom.
  rename v5 into vr_temp_num.

  rename H1 into Hptr_verr.
  rename H2 into Hptr_ventity.
  rename H3 into Hptr_vattr.
  rename H4 into Hptr_vmux.

  (* i ′ =ₑ ′ 0;ₛ *)
   hoare forward.
  (* prio ′ =ₑ ′ 0 − ′ 1;ₛ *)
   hoare forward.
  (* x ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 mutex ′·);ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.
  simpl.
  inverts Hptr_vmux; mytac; try eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  pure_auto.

  intros.
  destruct H.
  destruct H; try (sep pauto; instantiate (1:=init_lg); sep pauto).

  intros.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  (* x = 0 *)
  hoare unfold.
  inverts H1.

  hoare forward.
  hoare unfold.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutex_init_absimp_muxerr.
  can_change_aop_solver.
  destruct H. inverts H. pauto.
  do 2 destruct H. inverts H. pauto.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre. 
  change (Int.eq ($ 0) ($ 0)) with true. simpl.
  hoare unfold.
  destruct H0; tryfalse.

  (*x != 0*)
  hoare unfold.
  inverts H1.

  hoare forward.
  change (Int.eq ($ 1) ($ 0)) with false.
  simpl.
  hoare unfold; tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  clear H.

  (* destruct Hptr_vattr as [Hvattr_eq | (attr & Hvattr_eq)];
  subst vattr. *)
  (* If (attr ′ ==ₑ NULL) *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  instantiate (1:= (
  Aie true **
  Ais nil **
  Acs nil **
  Aisr empisr **
  (EX er, Aier er) **
    <|| mutex_init_after_get_attr
                (Vptr x :: ventity :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: vr_temp_dom :: vr_temp_num :: nil) ||>  **
  p_local OSLInv tid init_lg **
  LV z @ long |-> Vint32 Int.zero **
  LV os_code_defs.x @ char_t |-> (V$ 1) **
  LV prio @ long |-> Vint32 ($ 0 -ᵢ $ 1) **
  LV i @ long |-> (V$ 0) **
  LV p @ OS_EVENT ∗ |-> v'6 **
  LV y @ long |-> v'4 **
  LV os_code_defs.pos @ long |-> v'2 **
  LV err @ (char_t) ∗ |-> verr **
  LV attrEntity @ pthread_mutexattr_t ∗ |-> ventity **
  LV attr @ pthread_mutexattr_t ∗ |-> ventity **
  LV mutex @ pthread_mutex_t ∗ |-> Vptr x **
  A_dom_lenv
    ((err, (char_t) ∗)
     :: (attrEntity, pthread_mutexattr_t ∗)
        :: (attr, pthread_mutexattr_t ∗)
           :: (mutex, pthread_mutex_t ∗)
              :: (i, long)
                 :: (prio, long)
                    :: (os_code_defs.pos, long)
                       :: (os_code_defs.x, char_t)
                          :: (y, long) :: (z, long) :: (p, OS_EVENT ∗) :: nil) **
 [| ventity = Vnull -> Int.zero = $ EINVAL |])).
  destruct Hptr_vattr as [Hvattr_eq | ((attr_b & attr_i) & Hvattr_eq)];
  subst vattr; simpl in H; tryfalse.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutex_init_absimp_attr_null; eauto.
  can_change_aop_solver.
  (* z ′ =ᶠ pthread_mutexattr_init (·attrEntity ′·);ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.

  unfold retpost.
  unfold MutexAttrInitPost.
  unfold MutexAttrInitPost'.
  unfold getasrt.
  introv Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  mytac.

  pure_auto.

  introv Hsat. sep destruct Hsat.
  eexists. sep cancel p_local. simpl; auto.

  introv Hsat. sep destruct Hsat.
  eexists. sep cancel p_local. simpl; auto.

  hoare unfold.
   inverts H4.
   simpl nth_val' in *.
   rename v'10 into rv_attr.
   rename v'11 into ier.
  (* If (z ′ !=ₑ ′ 0){RETURN ′ EINVAL};ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.
  instantiate (1:= Afalse).
  change ($ 0) with Int.zero.
  hoare unfold.
  destruct (Int.eq rv_attr Int.zero) eqn: eq1;
  simpl in H4; try change (Int.notbool Int.one) with Int.zero in H4; tryfalse.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutex_init_absimp_attr_no_free; eauto.
  can_change_aop_solver.
  hoare forward.
  (* z = 0 *)
  eapply hoare_disj_afalseP_l_pre. 
  change ($ 0) with Int.zero.
  hoare unfold.
  destruct (Int.eq rv_attr Int.zero) eqn: eq1;
  simpl in H4; try change (Int.notbool Int.zero) with Int.one in H4; destruct H4; tryfalse.
  eapply semacc_int_eq_true in eq1; subst rv_attr.
  (* attr ′ =ₑ attrEntity ′ *)
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutex_init_absimp_attr_succ; eauto.
  can_change_aop_solver.
  hoare forward.
  pure_auto.
  sep cancel Aier.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  (* end of get attr *)
  hoare forward;
  hoare unfold.
  destruct Hptr_ventity as [Hventity_eq | (entity & Hventity_eq)];
  subst ventity.
  assert (Hf: Vnull = Vnull) by auto.
  eapply H in Hf; tryfalse.
  eapply backward_rule1; [idtac | eapply MutexInitPartProof with (verr:= verr); eauto].
  introv Hsat.
  sep cancel Aier.
  sep cancel Aop.
  sep auto.

  destruct Hptr_vattr as [Hvattr_eq | ((attr_b & attr_i) & Hvattr_eq)];
  subst vattr; simpl in H; destruct H; tryfalse.
  hoare abscsq.
  apply noabs_oslinv.
  eapply mutex_init_absimp_after_get_attr; eauto.
  can_change_aop_solver.
  eapply backward_rule1; [idtac | eapply MutexInitPartProof with (verr:= verr); eauto].
  introv Hsat.
  sep cancel Aier.
  sep cancel Aop.
  sep auto.
  Qed.
