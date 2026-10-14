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
Require Import OSTimeTickPure.
Require Import seplog_trm_tacs.
Require Import protect.
Require Import sempend_pure_ext.
Require Import MapLib.
Require Import gjb_mutex_common.
Require Import mq_getinfo_pure.
Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Require Import evt_spec_defs.

Lemma mqgetinfo_absimp_mqdeserr:
  forall mqdes P sch s,
    (Int.ltu mqdes Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = true \/ 
       mqdes = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_mqdes_err (|Vint32 mqdes :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.  
Qed.

Lemma mqgetinfo_absimp_mqdesok_choice:
  forall mqdes P sch s,
    (Int.ltu mqdes Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) mqdes = false /\ 
       mqdes <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_mqdes_err (|Vint32 mqdes :: nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  auto.
Qed.

Lemma mqgetinfo_absimp_mq_info_err:
  forall   msg_ptr P sch s  ,
  ( msg_ptr = Vnull \/    exists a,   msg_ptr = Vptr a /\ 
         (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true) ) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_mq_info_err (|msg_ptr :: nil|) ?? s ||>  ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||>  ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mqgetinfo_absimp_mq_info_ok:
  forall   msg_ptr P sch s  ,
      ( exists a,
             msg_ptr = Vptr a /\ 
               (cmpaddr Clt userAddrStart a  = true \/ cmpaddr Cle a userAddrEnd  = true)
        ) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_mq_info_err (|msg_ptr :: nil|) ?? s ||>  ** P) 
      (<|| s ||>  ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  auto.
Qed.

Lemma mqgetinfo_absimp_get_eid_hold_abt:
  forall mqdes v P sch s qattrb  i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (Holder, i1', i2, i3, i4, i5, i6) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv Hget Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq. pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:= ABORT).
  eapply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  right. split; auto.
  left. split. intro. destruct H0. inv H0. intro. inv H0.
  pure_auto.
  eapply absinfer_seq_abt;eauto.
  pure_auto. pure_auto.
  Unshelve. 
  exact None.
Qed.

Lemma mqgetinfo_absimp_get_eid_abt:
  forall mqdes v P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    ((exists eid, et = Valid_Addr eid /\ v <> Vptr eid) \/ et = Null /\ v <> Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| ABORT ||> ** HQAttr qattrb ** P). 
Proof.
  introv  Hget Heid Hcaop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= HQAttr qattrb ** P).
  pure_auto.
  instantiate (1:= ABORT).
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  pure_auto.
  apply absinfer_seq_abt.
  pure_auto.
  pure_auto.
  auto.
  Unshelve. 
  exact None.
Qed.

Lemma mqgetinfo_absimp_get_eid_ok:
  forall mqdes v P sch s qattrb et i1' i2 i3 i4 i5 i6,
    get qattrb mqdes = Some (et, i1', i2, i3, i4, i5, i6) -> 
    ((exists eid, et = Valid_Addr eid /\ v = Vptr eid) \/ et = Null /\ v = Vnull) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_get_ecb_ptr (|(Vint32 mqdes) :: v :: nil|) ;; s ||> ** HQAttr qattrb ** P) 
      (<|| s ||> ** HQAttr qattrb ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve. 
  exact None.
Qed.


Lemma mqgetinfo_absimp_if_null_yes:
  forall  v P sch s ,
    v = Vnull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_if_null_yes (|v  :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  introv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
Qed.

Lemma mqgetinfo_absimp_if_null_no:
  forall v P sch s,
    (exists eid, v =Vptr eid) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_if_null_yes (|v :: nil|) ?? 
             mqgetinfo_if_null_no  (|v :: nil|) ;; s ||> ** P) 
      (<|| s||> ** P). 
Proof. 
  introv Hv Hcaop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  eauto.
  instantiate (1:=P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.  
  destruct Hv. exists x.
  splits; eauto. 
  subst v. auto.
Qed.

Lemma mqgetinfo_absimp_pdata_not_null:
  forall pdata pdata' P sch s,
    pdata = Vptr pdata' ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_pdata_not_null (|pdata :: nil|) ;; s ||> ** P) 
      (<|| s ||> ** P). 
Proof. 
  infer_solver 0%nat.
  Unshelve.
  exact (None). 
Qed.

Lemma mqgetinfo_absimp_pdata_not_null_abt:
  forall pdata P sch s,
    pdata = Vnull ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_pdata_not_null (|pdata :: nil|) ;; s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
  Unshelve.
  exact (None). 
  exact ( 1%positive , $0).
Qed.

Lemma mqgetinfo_absimp_query_err:
  forall query_rv P sch s,
    Int.eq query_rv Int.zero = false ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_err_ret (|Vint32 query_rv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof.
  infer_solver 0%nat.  
Qed. 

Lemma mqgetinfo_absimp_queryok_choice:
  forall query_rv P sch s,
    Int.eq query_rv Int.zero = true -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_err_ret (|Vint32 query_rv :: nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  auto.
Qed.



Lemma mqgetinfo_absimp_mq_info_validptr_err_abt:
  forall mq_info evheap t l P sch s,
  ( Get_struct evheap mq_info = None \/
        (Get_struct evheap mq_info = Some (mq_info, t, l) /\ t <> mq_info_t) ) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_mq_info_validptr_err (|Vptr mq_info :: nil|) ?? s ||> ** HEvStructHeap evheap ** P) 
      (<|| ABORT||> ** HEvStructHeap evheap ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:= HEvStructHeap evheap ** P).
  pure_auto.
  pure_auto.
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed. 

Lemma mqgetinfo_absimp_ok2: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s2 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice2.
  pure_auto. pure_auto.
  auto.
Qed.

Lemma mqgetinfo_absimp_pdata_validptr_err_abt:
  forall pdata evheap t l P sch s,
  ( Get_struct evheap pdata = None \/
        (Get_struct evheap pdata = Some (pdata, t, l) /\ t <> OS_Q_DATA) ) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_pdata_validptr_err (|Vptr pdata :: nil|) ?? s ||> ** HEvStructHeap evheap ** P) 
      (<|| ABORT||> ** HEvStructHeap evheap ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:= HEvStructHeap evheap ** P).
  pure_auto.
  pure_auto.
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  pure_auto.
Qed. 

Lemma mqgetinfo_absimp_get_mq_curmsgs:
  forall mqdes mq_info pdata evheap evheap' l l' P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l') ->
    evheap' = Set_struct' evheap mq_info mq_curmsgs (nth_val' 1 l') ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_mq_curmsgs (|Vint32 mqdes :: Vptr mq_info :: Vptr pdata :: nil|) ;; s ||> ** HEvStructHeap evheap ** P) 
      (<|| s ||> ** HEvStructHeap evheap' ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.  
  exact (mqdes). 
Qed. 

Lemma mqgetinfo_absimp_get_mq_maxmsg:
  forall mqdes mq_info pdata evheap evheap' l l' P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    Get_struct evheap pdata = Some (pdata, OS_Q_DATA, l') ->
    evheap' = Set_struct' evheap mq_info mq_maxmsg (nth_val' 2 l') ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_mq_maxmsg (|Vint32 mqdes :: Vptr mq_info :: Vptr pdata :: nil|) ;; s ||> ** HEvStructHeap evheap ** P) 
      (<|| s ||> ** HEvStructHeap evheap' ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.  
  exact (mqdes). 
Qed. 

Lemma mqgetinfo_absimp_get_mq_msgsize:
  forall mqdes mq_info  evheap evheap' qtls e wtype flag maxm msize curm en l  P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    get qtls mqdes =Some ( e ,wtype ,flag ,maxm ,msize ,curm , en) ->
    evheap' = Set_struct' evheap mq_info mq_msgsize (Vint32 msize)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_mq_msgsize (|Vint32 mqdes :: Vptr mq_info :: nil|) ;; s ||> ** HEvStructHeap evheap ** HQAttr qtls ** P) 
      (<|| s ||> ** HEvStructHeap evheap' ** HQAttr qtls ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.  
Qed. 

Lemma mqgetinfo_absimp_get_mq_waittype:
  forall mqdes mq_info evheap evheap' qtls e wtype flag maxm msize curm en l  P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    get qtls mqdes =Some (e ,wtype ,flag ,maxm ,msize ,curm , en) ->
    evheap' = Set_struct' evheap mq_info mq_waittype (Vint32 wtype)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_mq_waittype (|Vint32 mqdes :: Vptr mq_info :: nil|) ;; s ||> ** HEvStructHeap evheap ** HQAttr qtls ** P) 
      (<|| s ||> ** HEvStructHeap evheap' ** HQAttr qtls ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.  
Qed. 

Lemma mqgetinfo_absimp_get_mq_flags:
  forall mqdes mq_info evheap evheap' qtls e wtype flag maxm msize curm en l  P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    get qtls mqdes =Some (e ,wtype ,flag ,maxm ,msize ,curm , en) ->
    evheap' = Set_struct' evheap mq_info mq_flags (Vint32 flag)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_mq_flags (|Vint32 mqdes :: Vptr mq_info :: nil|) ;; s ||> ** HEvStructHeap evheap ** HQAttr qtls ** P) 
      (<|| s ||> ** HEvStructHeap evheap' ** HQAttr qtls ** P). 
Proof.
  infer_solver 0%nat.
  Unshelve.  
Qed. 

Lemma mqgetinfo_absimp_get_task_blocked:
  forall  mq_info evheap evheap'  l  P sch s,
    Get_struct evheap mq_info = Some (mq_info, mq_info_t, l) ->
    evheap' = Set_struct' evheap mq_info os_code_defs.task_blocked (Vint32 Int.zero)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_get_task_blocked (| Vptr mq_info :: nil|) ;; s ||> ** HEvStructHeap evheap ** P) 
      (<|| s ||> ** HEvStructHeap evheap'  ** P). 
Proof.
  infer_solver 0%nat.
Qed. 

Lemma mqgetinfo_absimp_blocked_end:
  forall   evhp evhp'  P sch  els vblocked eid tcbls l vh s mq_info,
    evhp' = Set_struct' evhp mq_info os_code_defs.task_blocked (Vint32 (Int_add_n vblocked vh Int.one)) ->
   can_change_aop P ->
    Get_struct evhp mq_info = Some (mq_info, mq_info_t, l) ->
    vblocked = (get_tls_blocked_q_num (TcbMod.lst tcbls) eid) ->
    Vint32 vh = (nth_val' 5 l)  ->
   absinfer sch
      (<|| mqgetinfo_query_after_while_set_blocked(|Vptr  eid :: Vptr mq_info  ::nil|);;s ||> **
               HECBList els ** HTCBList tcbls **
               HEvStructHeap evhp ** P)
      (<|| s ||> ** HECBList els ** HTCBList tcbls **
           HEvStructHeap evhp' ** P). 
Proof.
  infer_solver 0%nat.
Qed.

Lemma mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl_abt:
  forall mq_info oseventtbl P sch s v1,
    ~(v1 = Vptr oseventtbl /\ Some oseventtbl = id_addrval mq_info OSEventTbl mq_info_t)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_memcpy_get_mq_info_oseventtbl (|Vptr mq_info :: v1 :: nil|) ;; s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl:
  forall mq_info oseventtbl v1 P sch s,
    v1 = Vptr oseventtbl /\ Some oseventtbl = id_addrval mq_info OSEventTbl mq_info_t  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_memcpy_get_mq_info_oseventtbl (|Vptr mq_info ::v1 :: nil|) ;; s ||> ** P) 
      (<|| s ||> ** P). 
Proof. 
  infer_solver 0%nat.
Qed.

Lemma mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl_abt:
  forall pdata oseventtbl v1 P sch s,
    ~(v1 = Vptr oseventtbl /\ Some oseventtbl = id_addrval pdata OSEventTbl OS_Q_DATA)  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_memcpy_get_pdata_oseventtbl (|Vptr pdata ::v1 :: nil|) ;; s ||> ** P) 
      (<|| ABORT ||> ** P). 
Proof. 
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  instantiate (1:=ABORT).
  apply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt; auto.
Qed.

Lemma mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl:
  forall pdata oseventtbl v1 P sch s,
    v1 = Vptr oseventtbl /\Some oseventtbl = id_addrval pdata OSEventTbl OS_Q_DATA  ->
    can_change_aop P -> 
    absinfer sch 
      (<|| mqgetinfo_query_memcpy_get_pdata_oseventtbl (|Vptr pdata ::v1 :: nil|) ;; s ||> ** P) 
      (<|| s ||> ** P). 
Proof. 
  infer_solver 0%nat.
Qed.

Lemma mqgetinfo_absimp_succ_end:
  forall   sch P ,
   can_change_aop P ->
   absinfer sch
      (<|| mqgetinfo_succ_ret(|nil|)||>  ** P)
      (<||  END (Some (Vint32 (Int.zero)))||>  ** P). 
Proof.
  infer_solver 0%nat.
Qed.


Lemma new_array_type_vallist_match_split2': 
  forall mqvl vll1 vll2 t, 
    new_array_type_vallist_match t mqvl ->
    mqvl = vll1 ++ vll2 ->
    new_array_type_vallist_match t vll1 /\
      new_array_type_vallist_match t vll2.
Proof.
  inductions mqvl.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0. 
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    simpl in Hmt1.
    destruct t;
      (destruct Hmt1 as (Hmta & Hmtb);
       specialize (IHmqvl vll1 vll2 _ Hmtb (eq_refl _));
       split; [simpl; mytac | mytac]).
Qed.          

Lemma new_array_type_vallist_match_split': 
  forall mqvl vll1 vll2 vl, 
    new_array_type_vallist_match mq_attr_t mqvl ->
    mqvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match mq_attr_t vll1 /\
      new_array_type_vallist_match mq_attr_t vll2 /\ 
      struct_type_vallist_match mq_attr_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2' Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.   
  
Lemma option2val:
  forall T (x y: T),
    Some x = Some y -> x = y.
Proof.
  intros T x y.
  intros F1.
  inversion F1.
  trivial.
Qed.

Local Open Scope code_scope.

Lemma length6_ex:
  forall v'40 :list vallist,
    length v'40 = ∘ 6 ->
    exists v1 v2 v3 v4 v5 v6 ,
      v'40 = v1::v2::v3::v4::v5::v6::nil.
Proof.
  introv Hlen.
  try do 6  (destruct v'40; simpl in Hlen; tryfalse).
  do 6 eexists; eauto.
  assert (length v'40 = 0)%nat.
  unfold Pos.to_nat in Hlen.
  simpl in Hlen.
  inverts Hlen.
  auto.
  assert (v'40 = nil).
  destruct v'40.
  auto.
  simpl in H; tryfalse.
  subst.
  eauto.
Qed.
  
Lemma dllseg_compose:
  forall (s : RstateOP) (P : asrt) (h hp t1 tn1 t2 tn2 : val)
         (l1 l2 : list vallist),
    s |= dllseg h hp t1 tn1 l1 OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** dllseg tn1 t1 t2 tn2 l2  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl)** P ->
    s |= dllseg h hp t2 tn2 (l1 ++ l2)  OS_TCB_flag
      (fun vl : vallist => nth_val 1 vl)
      (fun vl : vallist => nth_val 0 vl) ** P.
Proof.
  intros.
  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.

  apply astar_r_aemp_elim.
  eapply IHl1.
  sep auto.
  auto.
Qed.
  
Lemma OSMqgetinfoProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api mq_getinfo
              (mqgetinfo, (Tint32, mqd_t :: Tptr mq_info_t  :: Tptr OS_Q_DATA :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api mq_getinfo
              (mqgetinfo, (Tint32, mqd_t :: Tptr mq_info_t  :: Tptr OS_Q_DATA :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api mq_getinfo = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 18 try (destruct v'; try apply absabort_rule).
  rename v12 into vr_temp_dom.
  rename v13 into vr_temp_num.
  rename v14 into vr_temp_dom'.
  rename v15 into vr_temp_num'.

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
                Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) && 
                Int.eq ($ 3) Int.mone = false).
  { rewrite Heqf.
     change (Int.eq ($ 3) Int.zero || false && Int.eq ($ 3) Int.mone) with false.
     auto.
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
  simpl in LHift_true.
  destruct LHift_true as (Ha & Hb & Hc). clear Hb Hc.
  destruct (Int.ltu i ($ 0)) eqn: E1;
  destruct (Int.ltu ($ OS_USER_MAX_EVENTS / 3) i) eqn: E2;
  destruct (Int.eq i ($ OS_USER_MAX_EVENTS / 3)) eqn: E3.
  rewrite Hdiveq in Ha.
  rewrite E2 in Ha.
  simpl in Ha.
  apply ltu_eq_false in E2. tryfalse.
  rewrite Hdiveq in Ha.
  rewrite E2 in Ha.
  lets Hf: int_lt_gt_false' E1 E2. inv Hf.
  lets Hf: int_lt_eq_false' E1 E3. inv Hf.
  
  (* i < 0 *)
  2: { apply ltu_eq_false in E2. tryfalse. }
  (* i > OS_USER_MAX_EVENTS / 3 *)
  (* i = OS_USER_MAX_EVENTS / 3 *) 
  4: { pure_auto_try_false. }

  (* i < 0 *)
  clear E2. clear E3. clear Ha.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mqdeserr; eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mqdeserr; eauto.
  can_change_aop_solver.  
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.

  (* i = 6 *)
  clear E1. clear E2. clear Ha.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mqdeserr; eauto.
  right. right.
  eapply semacc_int_eq_true in E3. eauto.
  can_change_aop_solver.
  instantiate (1 := Afalse).
  apply absinfer_eq. 
  hoare forward.

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
  
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mqdesok_choice.
  splits; eauto.
  can_change_aop_solver.
  apply absinfer_eq.

   (* new code about part_pos_rgn *)
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
   (* end of new code *)

  (* Val_uacheck ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 mq_info ′·);ₛ *)
  rename x0 into vmq_info.
  assert (Hptr: vmq_info = Vnull \/ (exists p, vmq_info = Vptr p)).
  {
    clear - H2.
    destruct vmq_info.
    unfold isptr in H2. inversion H2. tryfalse. mytac. 
    left. auto.
    right. eexists; eauto.
    unfold isptr in H2. inversion H2. tryfalse. mytac. tryfalse.
    right. eexists; eauto.
  }
  
  hoare forward.
  pure_auto.
  pure_auto.
  simpl.
  inversion Hptr. left; subst; auto. right. mytac; eexists; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
  do 2 destruct H. simpl_sat H. simpljoin1. intro Hf. inv Hf.
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
  
  hoare unfold.
  inverts H3.
  
  lzh_hoare_if.
  pure_auto.

  hoare abscsq.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_err;eauto.
  inversion H.
  left. inverts H0;subst;eauto.
  right. mytac. eexists; splits;eauto.
  inverts H0; eauto.
  pure_auto.

  hoare forward.
  (* x = 0 false*)
  tryfalse.
  
  hoare unfold.
  inverts H3.
  
  lzh_hoare_if.
  pure_auto.
  (* x = 1 true*)
  change (Int.eq ($ 1) ($ 0) ) with false in LHift_true. tryfalse.
  (* x = 1 false*)
  hoare abscsq.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_ok; eauto.
  pure_auto.

  clear - E1 E2 E3 H1 Hdiveq Hrgn3 Hrgn4.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'37  = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH3. sep destroy Hsat.
    destruct v'17. 
    eapply amqattr_len with (s:= x1). eauto. } 
  eapply pure_split_rule'; introv Hl.
  
  destruct v'17. 
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

  (*L12: p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  
  eapply assign_rule_lvar with (v2:=nth_val' 5%nat v'46).
  split;intros.
  sep cancel (Alvarmapsto p).
  eauto.
  sep cancel (Alvarmapsto p).
  auto.
  Optimize Proof.
  Optimize Heap.

  instantiate (1:=(OS_EVENT∗)).
  2: { apply eq_vptr. do 2 eexists. splits; auto. }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H3; eauto.
  mytac.  
  
  subst v'37.
  destruct H12.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H14 H11 E1 Hlemu.  
  destruct H00 as (et & wty & fl & maxm & msize & curm & mgc &Hget & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'46 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'46 = Some Vnull) \/ et = Holder /\ V_QATTRpevent v'46 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget.
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  
  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v = Vptr eid) \/ et = Null /\ v = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v <> Vptr eid) \/ et = Null /\ v <> Vnull)).
  {
    inv Hok. destruct H18 as (eid & H'). 
    assert (Hvcs: v = Vptr eid \/ v <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v = Vnull \/ v <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H18. split; auto.
    right. right. destructs H18. split; auto.
  }
  
  hoare_lifts_trms_pre (Aabsdata absmqattrid).
  hoare_lifts_trms_pre Aop.
  inversion Hcases.
  2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; auto.
      eauto.
      auto.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.
  
  (* prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'17. exists (Z.to_nat (Int.unsigned i)).
  exists v'45. exists v'46.
  sep pauto.

  (*exit critical*)
  hoare forward prim.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  auto. pure_auto. pure_auto.
  pure_auto. pure_auto.
  
  assert (H_prm_cases: (exists eid, v = Vptr eid /\ nth_val' 5%nat v'46 = Vptr eid) \/ (v = Vnull /\ nth_val' 5%nat v'46 = Vnull)).
  {
    inversion Hok as [Heo1 | Heo2]; inversion H18 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_QATTRpevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_QATTRpevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  
  assert (Heq: nth_val' 5%nat v'46 = v).
  {
    inversion H_prm_cases.
    destruct H19. destruct H19. congruence.
    destruct H19. congruence.
  }
  rewrite Heq. clear Heq. 
  assert (Hvptr: isptr v).
  {
    inversion H_prm_cases.
    destruct H19. destructs H19.
    rewrite H19. 
    apply ptr_isptr.
    destructs H19.
    rewrite H19.
    apply Vnull_is_ptr.
  }
  rename H1 into Hx'.
  clear - E1 E2 E3 H_prm_cases Hvptr Hx' Hdiveq Hrgn3 Hrgn4.
  
  (* If p = NULL { RETURN -1; } *)
  hoare forward. 
  pure_auto.
  pure_auto.
  hoare unfold.
  assert (Hv0null: v = Vnull) by pure_auto.
  subst v.

  (* ... = -1 *) 
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_if_null_yes; auto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* the RETURN in case p = NULL *)
  hoare forward.
  
 (* p <> NULL *)
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  assert (exists eid, v = Vptr eid).
  {
    destruct v. 
    inversion H; tryfalse.
    inversion H; tryfalse.
    inversion H; tryfalse.
    eexists; eauto.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_if_null_no; auto.
  can_change_aop_solver.
  eapply absinfer_eq.

  clear H.
  destruct H0. 
  clear H.
  clear H_prm_cases.
  
  clear - E1 E2 E3 Hx' Hvptr Hdiveq Hrgn3 Hrgn4.
  (* encrit *)
  hoare forward prim.
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  destruct v'16.
  hoare_assert_pure (length v'36 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x1); eauto. } 
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
  
  (*L12: p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare_split_pure_all.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_lvar with (v2:=nth_val' 5%nat v'45).
  split; intros.
  sep cancel (Alvarmapsto p). eauto.
  sep cancel (Alvarmapsto p). 
  auto.
  Optimize Proof.
  Optimize Heap.
  
  instantiate (1:=(OS_EVENT∗)).
  2: { apply eq_vptr. do 2 eexists. splits; auto. }
  2: { sep pauto. sep cancel p_local. sep pauto. }
  introv Hsat.
  sep_lifts_trms_in Hsat Astruct.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.

  subst v'36.
  destruct H11.
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H10 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'45 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'45 = Some Vnull) \/ et = Holder /\ V_QATTRpevent v'45 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget.
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  
  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v0 = Vptr eid) \/ et = Null /\ v0 = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v0 <> Vptr eid) \/ et = Null /\ v0 <> Vnull)).
  {
    inv Hok. destruct H17 as (eid & H'). 
    assert (Hvcs: v0 = Vptr eid \/ v0 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v0 = Vnull \/ v0 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H17. split; auto.
    right. right. destructs H17. split; auto.
  }
  
  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; auto.
      eauto.
      auto.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aabsdata absmqattrid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.
  
  (* prepare for exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'16. exists (Z.to_nat (Int.unsigned i)). exists v'44.
  exists v'45.
  sep pauto.

  (*exit critical*)
  hoare forward prim.
  sep pauto.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  auto.
  pure_auto. pure_auto.
  pure_auto. pure_auto.
  
  assert (H_prm_cases: (exists eid, v0 = Vptr eid /\ nth_val' 5%nat v'45 = Vptr eid) \/ (v0 = Vnull /\ nth_val' 5%nat v'45 = Vnull)).
  {
    inversion Hok as [Heo1 | Heo2]; inversion H17 as [Heo1' | Heo2'].
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq).
    destruct Heo1' as (eid' & Heoeq1' & Hv'_).
    rewrite Heoeq1' in Heoeq1. inverts Heoeq1.
    unfold V_QATTRpevent in Hv_.
    apply nth_val_nth_val'_some_eq in Hv_.
    left. eexists. split; eauto.
    destruct Heo1 as (eid & Heoeq1 & Hv_ & Hneq);
    destruct Heo2' as (Heoeq2' & Hv_');
    tryfalse.
    destruct Heo2 as (Heoeq2 & Hv_);
    destruct Heo1' as (eid & Heoeq1' & Hv_');
    tryfalse.
    unfold V_QATTRpevent in Heo2.
    destruct Heo2. destruct Heo2'.
    right.
    split; auto. 
    apply nth_val_nth_val'_some_eq; auto.
  }
  
  assert (Heq: nth_val' 5%nat v'45 = v0).
  {
    inversion H_prm_cases.
    destruct H18. destruct H18. congruence.
    destruct H18. congruence.
  }
  rewrite Heq. clear Heq.
  clear Hvptr. 
  assert (Hvptr: isptr v0).
  {
    inversion H_prm_cases.
    destruct H18. destructs H18.
    rewrite H18. 
    apply ptr_isptr.
    destructs H18.
    rewrite H18.
    apply Vnull_is_ptr.
  }

  unfold isptr in Hx'.
  destruct Hx'.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_not_null_abt; auto.
  can_change_aop_solver.
  eapply absinfer_eq. 
  apply absabort_rule.

  destruct H18.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_not_null; auto.
  eapply H18.
  can_change_aop_solver.
  eapply absinfer_eq. 
  inverts H18.
 
  hoare forward.
  clear - Hvptr.
  unfold isptr in Hvptr.
  destruct Hvptr.
  inverts H; auto.
  destruct H.
  inverts H;auto.

  pure_auto.
  unfold retpost. introv Hsat. inverts Hsat.
  do 3 destruct H18.
  sep split in H18.
  destruct H21.
  pure_auto.
  
  clear - Hvptr.
  unfold isptr in Hvptr.
  destruct Hvptr. subst. auto.
  destruct H. subst. auto.
  
  sep pauto. instantiate (1:=init_lg). sep pauto.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  unfold OSQQueryPost.
  unfold OSQQueryPost'.
  inverts H18.
  
  (*If (Val_osqquery ′ !=ₑ ′ 0){RETURN ′ (-1)};ₛ*)
  hoare forward.
  clear -H22 H23.
  pure_auto.
  pure_auto.
  pure_auto.

  hoare unfold.
  assert(Int.eq v'48 ($ 0) = false).
  clear - H18 H19 H20.
  destruct (Int.eq v'48 ($ 0)).
  unfold val_inj in *; unfold notint in *; unfold Int.notbool in *.
  change (Int.eq Int.one Int.zero ) with false in *.
  simpl in *.
  tryfalse.
  auto.
  Optimize Proof.
  Optimize Heap.
  
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_query_err;eauto.
  pure_auto.
  eapply absinfer_eq.
  
  (*RETURN ′  (-1)*)
  hoare forward.
  
  hoare forward.
  hoare unfold.
  assert(Int.eq v'48 ($ 0) = true).
  clear - H18.
  destruct H18; destruct (Int.eq v'48 ($ 0) ); auto;
  unfold val_inj in H; unfold notint in H; unfold Int.notbool in H;
  change (Int.eq Int.zero Int.zero ) with true in H; simpl in H; tryfalse.
  
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_queryok_choice;eauto.
  pure_auto.
  eapply absinfer_eq.
  
  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim.
  unfold EvtInv.
 (*mq_info ′ → mq_curmsgs =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  intros.
  assert (exists t, Get_struct v'30 x0 = t) by eauto.
  destruct H0.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H0 as (ev & Hget).
  destruct ev as (a& l). destruct a as (a & t).
  assert (Ha: a = x0).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p.
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  assert (Hg: Get_struct v'30 x1 = None \/ exists t, Get_struct v'30 x1 = Some t).
  intros.
  assert (exists t, Get_struct v'30 x1 = t) by eauto.
  destruct H0.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H0 as (ev & Hget').
  destruct ev as (a& l'). destruct a as (a & t').
  assert (Ha: a = x1).
  clear - Hget'.
  inductions v'30.
  simpl in Hget'; tryfalse.
  unfold Get_struct in Hget'.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x1) eqn: eq1.
  eapply option2val in Hget'.
  inverts Hget'; auto.
  fold Get_struct in Hget'.
  apply IHv'30 in Hget'.
  auto.
  subst a.

  assert (Ht: t' = OS_Q_DATA \/ t' <> OS_Q_DATA) by tauto.
  destruct Ht as [Hteq' | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_OS_Q_DATA; eauto. sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  instantiate (1:= l').
  rewrite Hteq' in Hget'.
  auto.
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA.
  exists l'. exists v'14. exists v'42.
  sep pauto.

  inverts H10.
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.

  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin.

  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_struct_aop.
  split. 
  intros. sep lift 2%nat in H12.
  eapply H12.
  intros. sep lift 2%nat in H12. auto.
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  intros.

  eapply struct_member_rv.
  eapply AEvStructHeap_fold_mq_info_t' in H12.
  4:eauto.
  3:{
     instantiate (1:= v'30 ++ (x0, mq_info_t, l) :: v'43).
     auto.
  }
  sep lifts (1::3::nil)%nat in H12.
  rewrite H14 in H.
  eapply AEvStructHeap_unfold_OS_Q_DATA in H12.
  2: eauto.
  do 2 destruct H12.
  sep lifts (3::1::nil)%nat in H12.
  instantiate (2:= l').
  instantiate (2:= OS_Q_DATA).
  instantiate (2:= x1).
  instantiate (2:= true).
  sep pauto.
  inverts H14.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.

  lets Hl': struct_type_vallist_match_elim_5 H0.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & Hl).
  subst l'.
  simpl. auto with zarith.
  auto.
  Optimize Proof.
  Optimize Heap.

  instantiate (1:= nth_val' 1 l').   auto.
  pure_auto.
  
  eapply eq_int.
  pure_auto.
  
  lets Hl': struct_type_vallist_match_elim_7 H10.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & v6' & v7' & Hl).
  subst l.
  simpl. auto with zarith.
  instantiate (1:= update_nth_val 4 l (nth_val' 1 l')). auto.
  
  intros.
  sep pauto. sep cancel p_local. sep pauto.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_mq_curmsgs;eauto.
  pure_auto.
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists (update_nth_val 4 l (nth_val' 1 l')). exists v'30. exists v'43.
  sep pauto.
  unfold R_MutexAttr_P; intros; tryfalse.

  clear - H0 H10.
  lets Hsp: struct_type_vallist_match_elim_7 H10.
  lets Hsp': struct_type_vallist_match_elim_5 H0.
  destruct Hsp.
  do 6 destruct  H.
  substs. 
  simpl in *.
  heat; jeauto2.

  do 7 (try destruct n); simpl; try splits; eauto.
  clear -H0.
  simpl in H0.
  simpljoin1.
  destruct x7; tryfalse. auto.
  rewrite H14.

  assert((Set_struct' (v'30 ++ (x0, mq_info_t, l) :: v'43) x0 mq_curmsgs (nth_val' 1 l')) = (v'30 ++ (x0, mq_info_t, update_nth_val 4 l (nth_val' 1 l')) :: v'43)). 
  rewrite H14 in Hget.
  eapply set_struct_update_nth_val;eauto.
  rewrite H12.
  
  (*exit critical*)
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  rewrite H14 in *.
  clear -H Hget' H15.
  eapply R_Q_Data_P_hold1;eauto.
  pure_auto. pure_auto.
  
  clear - E1 E2 E3.  
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim.
  unfold EvtInv.
 (*mq_info ′ → mq_curmsgs =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  eapply get_struct_or.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H0 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.
  
  assert (Hg: Get_struct v'30 x1 = None \/ exists t, Get_struct v'30 x1 = Some t).
  eapply get_struct_or.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H0 as (ev & Hget').
  destruct ev as (a& l' ). destruct a as (a & t').
  assert (Ha: a = x1 ).
  clear - Hget'.
  inductions v'30.
  simpl in Hget'; tryfalse.
  unfold Get_struct in Hget'.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x1) eqn: eq1.
  eapply option2val in Hget'.
  inverts Hget'; auto.
  fold Get_struct in Hget'.
  apply IHv'30 in Hget'.
  auto.
  subst a.

  assert (Ht: t' = OS_Q_DATA \/ t' <> OS_Q_DATA) by tauto.
  destruct Ht as [Hteq' | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_OS_Q_DATA; eauto. sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  instantiate (1:= l').
  rewrite Hteq' in Hget'.
  auto.
  hoare_split_pure_all.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA.
  exists l'. exists v'14. exists v'42.
  sep pauto.

  inverts H10.
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.

  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_struct_aop.
  split. intros.
  sep lift 2%nat in H12.
  eapply H12.
  intros. sep lift 2%nat in H12. auto.
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto.
  intros.

  eapply struct_member_rv.
  eapply AEvStructHeap_fold_mq_info_t' in H12.
  3:{
     instantiate (1:= v'30 ++ (x0, mq_info_t, l) :: v'43).
     auto.
  Optimize Proof.
  Optimize Heap.
  }
  sep lifts (1::3::nil)%nat in H12.
  eapply AEvStructHeap_unfold_OS_Q_DATA in H12.
  2: eauto.
  do 2 destruct H12.
  sep lifts (3::1::nil)%nat in H12.
  instantiate (2:= l').
  instantiate (2:= OS_Q_DATA).
  instantiate (2:= x1).
  instantiate (2:= true).
  sep pauto.
  inverts H14.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  lets Hl': struct_type_vallist_match_elim_5 H0.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & Hl).
  subst l'.
  simpl. auto with zarith.
  auto.
  instantiate (1:= nth_val' 2 l').   auto.
  pure_auto.
  eapply eq_int.
  pure_auto.
  lets Hl': struct_type_vallist_match_elim_7 H10.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & v6' & v7' & Hl).
  subst l.
  simpl. auto with zarith.
  instantiate (1:= update_nth_val 2 l (nth_val' 2 l') ). auto.
  
  intros.
  sep pauto. sep cancel OSLInv. sep pauto.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_mq_maxmsg;eauto.
  pure_auto.
  eapply absinfer_eq.
   
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists (update_nth_val 2 l (nth_val' 2 l')). exists v'30. exists v'43.
  sep pauto.
  unfold R_MutexAttr_P; intros; tryfalse.

  clear - H0 H10.
  lets Hsp: struct_type_vallist_match_elim_7 H10.
  lets Hsp': struct_type_vallist_match_elim_5 H0.
  destruct Hsp.
  do 6 destruct  H.
  substs. 
  simpl in *.
  heat; jeauto2.

  do 7 (try destruct n); simpl; try splits; eauto.
  clear -H0.
  simpl in H0.
  simpljoin1.
  destruct x8; tryfalse. auto.
  rewrite H14.

  assert((Set_struct' (v'30 ++ (x0, mq_info_t, l) :: v'43) x0 mq_maxmsg (nth_val' 2 l'))  = (v'30 ++ (x0, mq_info_t, update_nth_val 2 l (nth_val' 2 l')) :: v'43)).
  rewrite H14 in Hget.
  eapply set_struct_update_nth_val; eauto.
  rewrite H12.

  (*exit critical*)
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  
  rewrite H14 in *.
  clear -H Hget' H15.
  eapply R_Q_Data_P_hold1; eauto.
  pure_auto. pure_auto.

  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
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

  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'34 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'14. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x); eauto. } 
  eapply pure_split_rule'; introv Hl.
  destruct v'14.
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
  (*L12:   p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare unfold.
  hoare normal pre.
  unfold EvtInv.
 (*mq_info ′ → mq_curmsgs =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  intros.
  assert (exists t, Get_struct v'30 x0 = t) by eauto.
  destruct H10.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H10 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.

  sep cancel AEvStructHeap.
  sep pauto. 
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.

  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_struct_aop.
  split. intros.
  sep lifts (2::1::nil)%nat in H10.
  eapply H10.
  intros. sep lifts (2::1::nil)%nat in H10. auto.
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto.
  intros.

  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.

  eapply eq_int.
  pure_auto.
  simpl.
  pure_auto.
  instantiate(1:= (Vint32 i6 :: Vint32 i5 :: Vint32 i4 ::  nth_val' 3 v'43 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)).
  unfold update_nth_val.
  simpl. auto.
  sep pauto. sep cancel p_local. sep pauto.

  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H11 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget' & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'43 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'43 = Some Vnull) \/ et = Holder /\ V_QATTRpevent v'43 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget'.
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v1 = Vptr eid) \/ et = Null /\ v1 = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v1 <> Vptr eid) \/ et = Null /\ v1 <> Vnull)).
  {
    inv Hok. destruct H10 as (eid & H'). 
    assert (Hvcs: v1 = Vptr eid \/ v1 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v1= Vnull \/ v1 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H10. split; auto.
    right. right. destructs H10. split; auto.
  }
  
  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; auto.
      eauto.
      auto.
  Optimize Proof.
  Optimize Heap.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aabsdata absmqattrid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.

  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_mq_msgsize;eauto.
  pure_auto.
  eapply absinfer_eq.
   
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists ((Vint32 i6 :: Vint32 i5
           :: Vint32 i4
                 :: nth_val' 3 v'43
                    :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)).
  exists v'34. exists v'44.
  sep pauto.
  unfold struct_type_vallist_match.
  simpl.
  splits;auto.
  do 4 (destruct v'43; tryfalse).
  destruct v7; tryfalse; auto.
  pure_auto.
  
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'14. exists (Z.to_nat (Int.unsigned i)). exists v'42.
   exists v'43.
  sep pauto.
  
  (*exit critical*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto.
  trycancel.
  assert( (Set_struct'
        (v'34 ++
         (x0, mq_info_t,
        Vint32 i6::
         Vint32 i5
         :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
         :: v'44) x0 mq_msgsize (Vint32 msize)) = (v'34 ++
           (x0, mq_info_t,
          Vint32 i6::
           Vint32 i5
           :: Vint32 i4
               :: nth_val' 3 v'43 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
           :: v'44)).  
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   unfold update_nth_val. unfold nth_val'.
   do 4 (destruct v'43; tryfalse).
   unfold V_QATTRmq_msgsize in e2.
   unfold nth_val in e2.
   inverts e2. eauto.
  }

  rewrite H21.
  sep cancel AEvStructHeap. 
  sep cancel AMuxEIBs. 
  sep cancel ASemEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold AMqEIBs.
  
  sep pauto.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep auto.
  pure_auto. pure_auto. pure_auto.
  pure_auto. pure_auto. pure_auto.
  assert((Set_struct'
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6
         :: Vint32 i5
            :: Vint32 i4
               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
         :: v'44) x0 mq_msgsize (Vint32 msize)) = (v'34 ++
      (x0, mq_info_t,
      Vint32 i6
      :: Vint32 i5
         :: Vint32 i4
            :: nth_val' 3 v'43 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
      :: v'44)).
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   simpl.
   do 4 (destruct v'43; tryfalse).
   unfold V_QATTRmq_msgsize in e2.
   unfold nth_val in e2.
   inverts e2. eauto.
  }
  rewrite H21 in *.
  clear - H1 Hget.
  eapply R_Q_Data_P_hold2; eauto.
  pure_auto. pure_auto.

  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'34 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'14. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x); eauto. }
  eapply pure_split_rule'; introv Hl.
  
  destruct v'14.
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
  (*L12:   p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare unfold.
  hoare normal pre.
  unfold EvtInv.
 (*mq_info ′ → mq_curmsgs =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  eapply get_struct_or.
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H10 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  Optimize Proof.
  Optimize Heap.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. 
  sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin.

  hoare_lifts_trms_pre Aop.
  hoare normal pre.
  hoare unfold.

  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_struct_aop.
  split. intros.

  sep lifts (2::1::nil)%nat in H10.
  eapply H10.
  intros. sep lifts (2::1::nil)%nat in H10. auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  intros.

  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.

  eapply eq_int.
  pure_auto.
  simpl.
  mauto.
  instantiate(1:= (nth_val' 0 v'43 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2  :: Vint32 i1  :: x6 :: nil)).
  unfold update_nth_val.
  simpl. auto.
  sep pauto. sep cancel p_local. sep pauto.
  
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H11 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget' & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'43 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'43 = Some Vnull) \/ et = Holder /\ V_QATTRpevent v'43 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget'.
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }

  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v2 = Vptr eid) \/ et = Null /\ v2 = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v2 <> Vptr eid) \/ et = Null /\ v2 <> Vnull)).
  {
    inv Hok. destruct H10 as (eid & H'). 
    assert (Hvcs: v2 = Vptr eid \/ v2 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v2= Vnull \/ v2 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H10. split; auto.
    right. right. destructs H10. split; auto.
  }
  
  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; auto.
      eauto.
      auto.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aabsdata absmqattrid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.
  
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_mq_waittype;eauto.
  pure_auto.
  eapply absinfer_eq.
   
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists ((nth_val' 0 v'43 :: Vint32 i5
           :: Vint32 i4
              :: Vint32 i3
                 :: Vint32 i2
                    :: Vint32 i1 :: x6 :: nil)).
  exists v'34. exists v'44.
  sep pauto.
  unfold struct_type_vallist_match.
  simpl.
  splits;auto.
  destruct v'43; tryfalse.
  destruct v; tryfalse; auto.
  pure_auto.
  
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'14. exists (Z.to_nat (Int.unsigned i)). exists v'42.
  exists v'43.
  sep pauto.
  
  (*exit critical*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto.
  assert((Set_struct'
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'44) x0 mq_waittype (Vint32 wty)) = (v'34 ++
           (x0, mq_info_t,
           nth_val' 0 v'43 :: Vint32 i5 
           :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'44)).
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   simpl.
   destruct v'43. tryfalse.
   unfold V_QATTRmq_waittype in e.
   unfold nth_val in e.
   inverts e. eauto.
  }
  rewrite H21.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  unfold AMqEIBs.
  sep pauto.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  pure_auto. pure_auto. pure_auto.
  pure_auto. pure_auto. pure_auto.
  assert((Set_struct'
        (v'34++
         (x0, mq_info_t,
         Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
         :: v'44) x0 mq_waittype (Vint32 wty)) = 
        (v'34 ++
         (x0, mq_info_t,
           nth_val' 0 v'43 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil)
           :: v'44)).
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   simpl.
   destruct v'43. tryfalse.
   unfold V_QATTRmq_waittype in e.
   unfold nth_val in e.
   inverts e. eauto.
  }
  rewrite H21 in *.
  eapply R_Q_Data_P_hold2;eauto.
  pure_auto. pure_auto.

  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  hoare unfold.
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'34 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct v'14. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH2. sep destroy Hsat.
    eapply amqattr_len with (s:= x); eauto. }
  eapply pure_split_rule'; introv Hl.
  destruct v'14.
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
  (*L12:   p′ =ₑ efield (Mq_Attr′[mqdes′]) pevent;ₛ*)
  hoare unfold.
  hoare normal pre.
  unfold EvtInv.
 (*mq_info ′ → mq_flags =ₑ os_code_defs.pdata ′ → OSNMsgs;ₛ*)
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.

  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  intros.
  assert (exists t, Get_struct v'30 x0 = t) by eauto.
  destruct H10.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H10 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin.

  hoare_lifts_trms_pre Aop.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  hoare forward.
  eapply assign_rule_struct_aop.
  split. intros.
  sep lifts (2::1::nil)%nat in H10.
  eapply H10.
  intros. sep lifts (2::1::nil)%nat in H10. auto.
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto. 
  pure_auto.
  intros.

  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq.
  lets Hposv_neq: Int.eq_false E3. auto.
  eapply new_array_type_vallist_match_split' in H2; eauto.
  mytac.
  eapply eq_int.
  pure_auto.
  simpl.
  mauto.
  instantiate(1:= (Vint32 i6 :: nth_val' 1 v'43 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)).
  unfold update_nth_val.
  simpl. auto.
  sep pauto. sep cancel p_local. sep pauto.
  
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  lets H00: mqattr_corr H13 H11 E1 Hlemu.
  destruct H00 as (et & wty & fl & maxm & msize & curm & mqc & Hget' & H').
  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent v'43 = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent v'43 = Some Vnull) \/ et = Holder /\ V_QATTRpevent v'43 = Some (Vptr vhold_addr)). 
  { clear -H'. intuition. }
  assert (H01 := H').
  clear H'. 
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      rewrite Habt1 in Hget'.
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt.
      eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }

  assert (Hcases: 
         ((exists eid, et = Valid_Addr eid /\ v3 = Vptr eid) \/ et = Null /\ v3 = Vnull)
      \/ ((exists eid, et = Valid_Addr eid /\ v3 <> Vptr eid) \/ et = Null /\ v3 <> Vnull)).
  {
    inv Hok. destruct H10 as (eid & H'). 
    assert (Hvcs: v3 = Vptr eid \/ v3 <> Vptr eid) by tauto.
    inv Hvcs.
    left. left. exists eid. destructs H'. split; auto.
    right. left. exists eid. destructs H'. split; auto.
    assert (Hvcs: v3= Vnull \/ v3 <> Vnull) by tauto.
    inv Hvcs.
    left. right. destructs H10. split; auto.
    right. right. destructs H10. split; auto.
  }
  
  inversion Hcases.
  2: {
      hoare_lifts_trms_pre (Aabsdata absmqattrid).
      hoare_lifts_trms_pre Aop.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; auto.
      eauto.
      auto.
  Optimize Proof.
  Optimize Heap.
      pure_auto.
      eapply absinfer_eq. 
      apply absabort_rule.
  }
  hoare_lifts_trms_pre (Aabsdata absmqattrid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; auto.
  eauto.
  auto.
  pure_auto.
  eapply absinfer_eq. 
  clear Hcases.
  
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_mq_flags;eauto.
  pure_auto.
  eapply absinfer_eq.
   
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists ((Vint32 i6 :: nth_val' 1 v'43 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)).
  exists v'34. exists v'44.
  sep pauto.
  
  unfold struct_type_vallist_match.
  simpl.
  splits;auto.
  do 2 (destruct v'43; tryfalse).
  destruct v1; tryfalse; auto.
  pure_auto.
  
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'14. exists (Z.to_nat (Int.unsigned i)). exists v'42.
   exists v'43.
  sep pauto.
  
  (*exit critical*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  sep pauto.
  trycancel.
  assert((Set_struct'
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)
         :: v'44) x0 mq_flags (Vint32 fl)) = 
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6 :: nth_val' 1 v'43 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil)
         :: v'44)).
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   simpl.
   destruct v'43. tryfalse.
   destruct v'43. tryfalse.
   unfold V_QATTRmq_flags in e0.
   unfold nth_val in e0.
   inverts e0. eauto.
  }
  rewrite H21.
  sep cancel AEvStructHeap. 
  sep cancel ASemEIBs. 
  sep cancel AMuxEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  unfold AMqEIBs.
  sep pauto.
  sep cancel AMqAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep auto.
  pure_auto. pure_auto. pure_auto.
  pure_auto. pure_auto. pure_auto.
  assert((Set_struct'
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1:: x6 :: nil)
         :: v'44) x0 mq_flags (Vint32 fl)) = 
        (v'34 ++
         (x0, mq_info_t,
         Vint32 i6 :: nth_val' 1 v'43 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil)
         :: v'44)).
  {
   eapply set_struct_update_nth_val'; eauto.
   unfold id_nth. unfold id_nth'. simpl. eauto. 
   simpl.
   destruct v'43. tryfalse.
   destruct v'43. tryfalse.
   unfold V_QATTRmq_flags in e0.
   unfold nth_val in e0.
   inverts e0. eauto.
  }
  rewrite H21.
  eapply R_Q_Data_P_hold2;eauto.
  pure_auto. pure_auto.

  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
 (* ENTER_CRITICAL;ₛ*) 
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.

  assert (Hg: Get_struct v'30 x0 = None \/ exists t, Get_struct v'30 x0 = Some t).
  eapply get_struct_or.

  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H0 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'30.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'30 in Hget.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. 
  sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin.

  hoare_lifts_trms_pre Aop.
  hoare forward.
  lets Hl': struct_type_vallist_match_elim_7 H0.
  destruct Hl' as (v1' & v2' & v3' & v4' & v5' & v6' & v7' & Hl).
  subst l.
  simpl. auto with zarith.

  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_task_blocked;eauto.
  pure_auto.
  eapply absinfer_eq.
   
  eapply backward_rule1. 
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists (update_nth_val 5 l (V$ 0)). exists v'14. exists v'42.
  sep pauto.
  unfold R_MutexAttr_P; intros; tryfalse.

  clear - H0.
  lets Hsp: struct_type_vallist_match_elim_7 H0.
  destruct Hsp.
  do 6 destruct H.
  substs. 
  simpl in *.
  heat; jeauto2.
  splits;eauto.

  assert(Set_struct' (v'14 ++ (x0, mq_info_t, l) :: v'42) x0 os_code_defs.task_blocked (Vint32 Int.zero)  = (v'14 ++ (x0, mq_info_t, update_nth_val 5 l (V$ 0)) :: v'42)).
  {
    eapply set_struct_update_nth_val; eauto.
  }
  rewrite H10.

  (*exit critical*)
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto.
  eapply R_Q_Data_P_hold2;eauto.
  pure_auto. pure_auto.

  clear - E1 E2 E3 Hdiveq Hrgn3 Hrgn4.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim. 
  hoare unfold.
  unfold EvtInv.
  (* hoare unfold. *)
  unfold AMqEIBs.
  hoare normal pre. hoare_ex_intro.
  hoare_lifts_trms_pre (R_Q_Data_P, RH_Q_NOT_IN_CORE_P).
  eapply pure_split_rule'; introv Hrqdata.
  eapply pure_split_rule'; introv Hq_nc.
  hoare_assert_pure (length v'34 = ∘ (OS_USER_MAX_EVENTS / 3)).
  { destruct  v'42. get_hsat Hsat. sep_rmb_trms_in Hsat AMqAttr. clear HeqH1. sep destroy Hsat.
    eapply amqattr_len with (s:= x); eauto. }
  eapply pure_split_rule'; introv Hl.
  destruct v'42.
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

  hoare unfold.
  hoare normal pre.
  hoare_lifts_trms_pre (Aop).
  assert (Hlemu: Int.unsigned i <= Int.max_unsigned).
  { clear -E2 Hrgn3 Hrgn4. int auto. }
  rename v'44 into qvl.
  lets Hsls: mqattr_corr H6 H4 E1 Hlemu.
  destruct Hsls as (et & wty & fl & maxm & msize & curm & mqc & Hget & Hsls).

  assert (Hcases: ((exists eid, et = Valid_Addr eid /\ V_QATTRpevent qvl = Some (Vptr eid) /\ eid <> vhold_addr) \/ et = Null /\ V_QATTRpevent qvl = Some Vnull) \/ et = Holder /\ V_QATTRpevent qvl = Some (Vptr vhold_addr)). 
  { clear -Hsls. intuition. }
  clear Hsls.
  hoare_lifts_trms_pre (Aop, absmqattrid).
  destruct Hcases as [ Hok | Habt ].
  2: {
      destruct Habt as (Habt1 & Habt2).
      subst et.
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_hold_abt; eauto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  rename v4 into rv_ptr.
  assert (Hveid: 
         ((exists eid, et = Valid_Addr eid /\ rv_ptr = Vptr eid) \/ et = Null /\ rv_ptr = Vnull) 
      \/ ((exists eid, et = Valid_Addr eid /\ rv_ptr <> Vptr eid) \/ et = Null /\ rv_ptr <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst et.
    assert (Hv: rv_ptr = Vptr eid \/ rv_ptr <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: rv_ptr = Vnull \/ rv_ptr <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
  }
  destruct Hveid as [Hveid | Habt].
  2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_get_eid_abt; eauto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_get_eid_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Mq_Attr,Astruct, A_dom_lenv, Alvarmapsto mqdes).
  hoare remember (1:: 2 :: 3 :: 4 :: nil)%nat pre.
  
  assert (Hget_rv: forall P, (GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b, i0) **
  Astruct
    (b,
    i0 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen mq_attr_t))
    mq_attr_t qvl **
  A_dom_lenv
    ((os_code_defs.pdata, OS_Q_DATA ∗)
     :: (mq_info, mq_info_t ∗)
        :: (mqdes, long)
           :: (os_code_defs.i, long)
              :: (Val_uacheck, char_t) :: (p, OS_EVENT ∗) :: (Val_osqquery, char_t)  :: (ptcb, OS_TCB ∗)::(x, (char_t) ∗) :: (y, (char_t) ∗)
               :: (temp_dom, char_t) :: (temp_num, char_t) :: nil)  **
  LV mqdes @ long |-> Vint32 i **
  P) ==> Rv efield (Mq_Attr ′ [mqdes ′]) pevent @ (OS_EVENT∗) == (nth_val' 5%nat qvl)).
  { introv Hsat.
    sep_get_rv_array_struct.
    rewrite Hdiveq; eauto.
    rewrite Hdiveq.
    lets Hposv_neq: Int.eq_false E3. auto.
    eapply new_array_type_vallist_match_split' in H1; eauto.
    mytac.
  }
  
  lets Hq_vll: H1.
  rename H1 into Hq_vl.
  eapply new_array_type_vallist_match_split' in Hq_vl; eauto.
  destruct Hq_vl as (_ & _ & Hq_vl).
  lets Hq_vl_eq: struct_type_vallist_match_mq_attr_t_vl Hq_vl.
  lets Hvp_ptr: struct_type_vallist_match_mq_attr_t_ptr Hq_vl.
  destruct Hq_vl_eq as (v1' & v2' & v3' & v4' & v5'  & vp & v6' & Hsem_vl_eq).
  subst qvl.
  simpl nth_val' in *.
  assert (Heq_rv: vp = rv_ptr).
  { clear -Hok Hveid.
    unfold V_OSSINFOPevent in Hok.
    simpl nth_val in Hok.
    destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
    subst et; inverts Hvp;
    destruct Hveid as [(ed & Heq & Hrv) | (Heq & Hrv)];
    subst rv_ptr; inverts Heq;
    auto.
  Optimize Proof.
  Optimize Heap.
  }
  subst vp.

  hoare forward.
  eapply ift_rule''; eauto.
  introv Hsat.
  eapply bop_rv; eauto.
  sep get rv.
  clear -Hvp_ptr. simpl. 
  destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst; pure_auto.
  go.
  simpl bop_eval.
  hoare unfold.
  destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst;
  simpl in H1; tryfalse.

  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_if_null_yes; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* exit critical *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'42 (Z.to_nat (Int.unsigned i)) v'43 .
  sep pauto.
  
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel AMqAttr.
  sep cancel AMuxEIBs.
  sep cancel ASemEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  eauto.
  pure_auto. pure_auto.

   (* return -1 *)
  hoare forward.

  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst;
  simpl in H1; destruct H1; tryfalse.

  (*(efield (Mq_Attr ′ [mqdes ′]) pevent) = Vptr (pb, pi) *)
(*   hoare abscsq. *)
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_if_null_no; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  
  hoare_lifts_trms_pre (Aop, evstructheapid).
  rename v'30 into evstruct.
  assert (Hg: Get_struct evstruct x0 = None \/ exists t, Get_struct evstruct x0 = Some t).
  intros.
  assert ( exists t, Get_struct evstruct x0 = t) by eauto.
  destruct H3.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H3 as (ev & Hget').
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget'.
  inductions evstruct.
  simpl in Hget'; tryfalse.
  unfold Get_struct in Hget'.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget'.
  inverts Hget'; auto.
  fold Get_struct in Hget'.
  apply IHevstruct in Hget'.
  auto.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. 
  sep pauto.
  sep cancel AEvStructHeap.
  sep pauto.
  rewrite Hteq in Hget'.
  eauto.
  hoare_split_pure_all.
  simpljoin. 
  hoare unfold.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto. 
  exists (Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) v'14 v'30.
  sep pauto.
  pure_auto.

  (* compose tcbdllseg *)
  eapply backward_rule1.
  introv Hsat.
  eapply tcbdllseg_compose' with (h:= v'1).
  sep cancel (tcbdllseg v'1).
  sep cancel tcbdllseg.
  eauto.
  (* compose TCBList_P *)
  hoare_split_pure_all.
  rename H3 into Htls_last_case.
  rename H20 into Htls_left; rename H21 into Htls_right.
  rename H18 into Htj; rename H1 into Hhead_neq.
  assert (Htls_whole: TCBList_P v'1 (v'3 ++ v'7 :: v'8) v'9 v'12).
  { destruct Htls_last_case as [ (Hnil & Heq) | (vl & Hnnil & Hlast & Heq)];
    subst. 
    simpl in Htls_left. subst.
    eapply join_emp_eq in Htj; subst.
    rewrite nil_simp. auto.
    eapply TCBList_P_combine; eauto.
  }
  hoare_assert_pure (isptr v'1).
  {  unfold tcbdllseg in *.
     eapply dllseg_head_isptr with (s:= s0); eauto.
  }
  eapply pure_split_rule'; introv Hptr_ptcb.

  (* ptcb ′ =ₑ OSTCBList ′;ₛ *)
  hoare forward.
  pure_auto.

  destruct Hptr_ptcb as [Hf | (tls_head & Htls_head)]; subst v'1; tryfalse.
  hoare_assert_pure (array_type_vallist_match Int8u v'9 /\ length v'9 = ∘ OS_RDY_TBL_SIZE).
  {
   unfold AOSRdyTblGrp in H1.
   unfold AOSRdyTbl in H1.
   sep normal in H1.
   sep split in H1.
   mytac.
  }

  eapply pure_split_rule'; introv Hrtbl.
  destruct Hrtbl as (Hrtbl_mat & Hrtbl_len).
  (*WHILE (ptcb ′) *)

  (*1: remember irrelevant sep-conjunctions*)
  hoare_lifts_trms_pre (Mq_Attr, v2', A_dom_lenv, Alvarmapsto mqdes, Aop, p_local, tcbdllseg, OSTCBList, OSTCBCur, Alvarmapsto ptcb, Alvarmapsto mq_info, evstructheapid, AEvStructHeap).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 13 :: nil)%nat pre.
  protect HeqH1.
  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
  *)

(*change*)
  eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX evstruct' vblock vptcb vl1 vl2 tls1 tls2 ptcb_addr,
      GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b, i0) **
      Astruct
        (b, i0 +ᵢ $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen mq_attr_t))
        mq_attr_t
      (v1' :: v2' :: v3' :: v4' :: v5' :: Vptr (pb, pi) :: v6' :: nil) **
  A_dom_lenv
    ((os_code_defs.pdata, OS_Q_DATA ∗)
     :: (mq_info, mq_info_t ∗)
        :: (mqdes, long)
           :: (os_code_defs.i, long)
              :: (Val_uacheck, char_t)
                 :: (p, OS_EVENT ∗)
                    :: (Val_osqquery, char_t)
                       :: (ptcb, OS_TCB ∗)  :: (x, (char_t) ∗) :: (y, (char_t) ∗)
                        :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
     LV mqdes @ long |-> Vint32 i **
      <||
      mqgetinfo_query_after_while_set_blocked (|Vptr (pb, pi) :: Vptr x0  :: nil|);;
          (mqgetinfo_mq_info_validptr_err (|Vptr x0 :: nil|)
           ?? mqgetinfo_pdata_validptr_err (|Vptr x1 :: nil|)
              ??mqgetinfo_query_memcpy_get_mq_info_oseventtbl (|Vptr x0 :: v10 :: nil|);;
                 mqgetinfo_query_memcpy_get_pdata_oseventtbl (|Vptr x1 :: v11 :: nil|);; 
                 memcpy_empty (|v10 :: v11 :: V$ OS_EVENT_TBL_SIZE :: nil|);;
                 mqgetinfo_succ_ret (|nil|)) ||>  **
      p_local OSLInv tid (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal) :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
     tcbdllseg (Vptr tls_head) Vnull v'44 Vnull (v'3 ++ v'7 :: v'8) ** 
      [| (vptcb = Vptr ptcb_addr /\  (* in the loop *)
          join tls1 tls2 v'12 /\
         TCBList_P (Vptr tls_head) vl1 v'9 tls1 /\
         TCBList_P vptcb vl2 v'9 tls2 /\ vl2 <> nil /\
          (vl1 = nil /\ Vptr ptcb_addr = Vptr tls_head \/
          (exists vl,
                  vl1 <> nil /\
                  last vl1 nil = vl /\ nth_val 0 vl = Some (Vptr ptcb_addr))))
         \/ ( vptcb = Vnull /\   (* out of loop *)
                  vl1 = (v'3 ++ v'7 :: v'8) /\ vl2 = nil /\
                  tls1 = v'12 /\ tls2 = TcbMod.emp /\
                  TCBList_P (Vptr tls_head) (v'3 ++ v'7 :: v'8) v'9 v'12) |] **
      [| vl1 ++ vl2 = (v'3 ++ v'7 :: v'8) |] **
      GV OSTCBList @ OS_TCB ∗ |-> (Vptr tls_head) **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
      LV ptcb @ OS_TCB ∗ |-> vptcb **
      LV mq_info @ mq_info_t ∗ |-> Vptr x0 **
      [|  vblock = get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi) |] **
      [| ( (0 < vblock)%nat /\ evstruct' = Set_struct' (v'14 ++
     (x0, mq_info_t,
     Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 os_code_defs.task_blocked  (Vint32 (Int_add_n vblock i1 Int.one)) ) \/
     ((vblock = 0)%nat /\ evstruct' = (v'14 ++
     (x0, mq_info_t,
     Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) ) |] **
     HEvStructHeap (v'14 ++
     (x0, mq_info_t,
     Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) **
     AEvStructHeap evstruct' ** H1)).

    introv Hsat.
    exists (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) (0%nat) (Vptr tls_head) (nil: list vallist) (v'3 ++ v'7 :: v'8).
    exists (TcbMod.emp) v'12 tls_head.
    sep pauto.
    left.
    splits; auto.
    apply map_tactics.old.Unnamed_thm.
    simpl; auto.
    clear. introv Hf. rewrite <- length_zero_iff_nil in Hf.
    rewrite app_length in Hf. simpl in Hf.
    auto with zarith.

   (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'*)
   eapply seq_rule.
   (*4: prove the condition expression of while is legal *)
   eapply while_rule with (tp := OS_TCB ∗).
   introv Hsat. sep destruct Hsat. eexists. sep get rv.
   sep split in Hsat. 
   destruct H3 as [ (Heq_ptcb & _) | (Heq_ptcb & _)];
   subst; simpl; auto.
   
  (* Aistrue ptcb ′ *)
  (*5: the cond-expr of while hold implies the part of the loop-inv*)
  hoare normal pre.
  apply ex_intro_rule; intro evstruct'.
  apply ex_intro_rule; intro vblock.
  apply ex_intro_rule; intro vptcb'.
  apply ex_intro_rule; intro vl1.
  apply ex_intro_rule; intro vl2.
  apply ex_intro_rule; intro tls1.
  apply ex_intro_rule; intro tls2.
  apply ex_intro_rule; intro ptcb_addr.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar; eauto.
  introv Hsat. 
  sep get rv.
  sep split in Hsat.
  destruct H3 as [ (Heq_ptcb & _) | (Heq_ptcb & _)];
  subst; simpl; auto.
  hoare_split_pure_all.
  destruct H22 as (_ & Histrue & _).
  destruct H3 as [ (Heq_ptcb & Htj' & Htls_left' & Htls_right' & Hvl2_nnil & Htls_last_case') | (Heq_ptcb & Hvl1_eq & Hvl2_eq & Htls1_eq & Htls2_eq & Htls_whole')];
   subst vptcb'; tryfalse.
  (* ptcb = Vptr ptcb_addr *)
  rename H18 into Htls_eq_alt; rename H21 into Hblk_cases.
  assert (Hvl2_alt: exists vl vl2', vl2 = vl :: vl2').
  { clear - Hvl2_nnil. destruct vl2; eauto. tryfalse. }
  destruct Hvl2_alt as (vl & vl2' & Hvl2_eq); subst vl2; rename vl2' into vl2.
  rewrite <- Htls_eq_alt.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (tcbdllseg).
  eapply tcbdllseg_split in Hsat; eauto.
  hoare unfold.
  rename H3 into Htls_last_case''.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  hoare unfold.
  assert (Hptcb_eq: (v'50, Int.zero) = ptcb_addr).
  { clear -Htls_last_case' Htls_last_case''.
    destruct Htls_last_case' as [ (Hnil & Heq) | (vl & Hnnil & Hlast & Heq)];
    subst; inverts Heq;
    destruct Htls_last_case'' as [ ( Hnnil' & Hlast) | (Hnil & Heq)];
    subst; try inverts Heq;
    auto; tryfalse.
    rewrite Hlast in H0. inverts H0.
    auto.
  Optimize Proof.
  Optimize Heap.
  }
  rewrite Hptcb_eq in *.

  assert (Hget_vblock: exists vblock', Get_struct evstruct' x0 = Some (x0, mq_info_t,
     Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3  :: Vint32 i2 :: vblock' :: x6 :: nil) /\ (((get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi) = 0)%nat /\ vblock' = Vint32 i1) \/ ((0 < get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi))%nat /\ vblock' = (Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) i1 Int.one))))).
  {
    clear - H19 Hblk_cases.
     destruct Hblk_cases as [ (Hblk_lt & Hevatom) | (Hblk_eq & Hevatom)];
     subst evstruct'; eauto.
     assert(Hget:Get_struct (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil) :: v'30) x0 = Some (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil)).
   {
    induction v'14.
    change ((nil ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30)) with ( (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)  :: v'30).
    simpl. rewrite beq_tid_true. auto.
    destruct a; destruct p.
    assert (a <> x0 \/ a = x0) by tauto.
    destruct H.
    simpl.
    destruct (os_inv.beq_addrval a x0) eqn :eq1.
    eapply beq_tid_true_eq in eq1. tryfalse.
    assert(Get_struct ((a, t, l) :: v'14) x0  = Get_struct (v'14) x0 ).
    simpl. rewrite eq1. auto.
    unfold opsem.Get_struct in H19.
    unfold Get_struct in H0.
    rewrite H0 in H19.
    eapply IHv'14 in H19. auto.
    inverts H.
    simpl in H19;rewrite beq_tid_true in H19;tryfalse.
   }
   2:{
      exists ( Vint32 i1 ).
      splits; eauto.
      induction v'14.
      change ((nil ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30)) with ((x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil)  :: v'30).
      simpl. rewrite beq_tid_true. auto.
      destruct a; destruct p.
      assert (a <> x0 \/ a = x0) by tauto.
      destruct H.
      simpl.
      destruct (os_inv.beq_addrval a x0) eqn :eq1.
      eapply beq_tid_true_eq in eq1. tryfalse.
      assert(Get_struct ((a, t, l) :: v'14) x0  = Get_struct (v'14) x0 ).
      simpl. rewrite eq1. auto.
      unfold opsem.Get_struct in H19.
      unfold Get_struct in H0.
      rewrite H0 in H19.
      eapply IHv'14 in H19. auto.
      inverts H.
      simpl in H19;rewrite beq_tid_true in H19;tryfalse.
   }
   eexists.
   splits. 
   instantiate (1:= Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) i1 Int.one)).
   assert(Set_struct' (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) i1 Int.one)) = 
  (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 ::  Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30)).
   {
    eapply set_struct_update_nth_val';eauto.
    unfold id_nth. unfold id_nth'. simpl. eauto. 
    simpl. eauto.
   }
   rewrite H.
   clear H Hget.
   induction v'14.
   change ((nil ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: V$ Z.of_nat (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) :: x6 :: nil) :: v'30)) with ((x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2  :: V$ Z.of_nat (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) :: x6 :: nil) :: v'30).
   simpl. rewrite beq_tid_true. auto.
   destruct a; destruct p.
   assert (a <> x0 \/ a = x0) by tauto.
   destruct H.
   simpl.
   destruct (os_inv.beq_addrval a x0) eqn :eq1.
   eapply beq_tid_true_eq in eq1. tryfalse.
   assert(Get_struct ((a, t, l) :: v'14) x0  = Get_struct (v'14) x0 ).
   simpl. rewrite eq1. auto.
   unfold opsem.Get_struct in H19.
   unfold Get_struct in H0.
   rewrite H0 in H19.
   eapply IHv'14 in H19. auto.
   inverts H.
   simpl in H19;rewrite beq_tid_true in H19;tryfalse.
   eauto.
  }
  destruct Hget_vblock as ( vblock' & Hget_vblock' & Hvblock'_eq).
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t with (evheap := evstruct'); eauto. sep pauto.
  hoare normal pre.
  apply ex_intro_rule; intro v'2.
  apply ex_intro_rule; intro v'100.
  hoare_split_pure_all.
  subst evstruct'.
  simpl in H3. destruct vblock'. simpljoin1; tryfalse. 
  simpljoin1; tryfalse.
  2:simpljoin1; tryfalse. 
  rename i14 into vblock. 
  rename H35 into Hget_struct_none.
  
  (*If (ptcb ′ → OSTCBEventPtr ==ₑ efield (Mq_Attr ′ [mqdes ′]) pevent)*)
  hoare forward.
  hoare_lifts_trms_pre (Mq_Attr, v2', A_dom_lenv, Alvarmapsto mqdes).
  eapply ift_rule''; eauto.
  introv Hsat.
  eapply bop_rv; eauto.
  sep get rv.
  go.
  simpl. 
  clear -H25. destruct H25 as [Heq | ((pb' & pi') & Heq) ]; subst; simpl; pure_auto.
  simpl; eauto.
  simpl bop_eval.
  hoare unfold.
  destruct H25 as [Heq | ((pb' & pi') & Heq) ]; subst; simpl in H20; tryfalse.
  destruct (Int.eq pi' pi) eqn: ifeq2;
  destruct (peq pb' pb) eqn: ifeq1; simpl in H20; tryfalse.
  eapply semacc_int_eq_true in ifeq2; subst pi'; subst pb'.
  (*++ mq_info ′ → task_blocked*)
  hoare_lifts_trms_pre Aop.
  hoare forward.
  pure_auto.

  (* ptcb ′ =ₑ ptcb ′ → OSTCBNext *)
  simpl bop_eval.
  eapply backward_rule1 with (p:= (
       <||
   mqgetinfo_query_after_while_set_blocked (|Vptr (pb, pi) :: Vptr x0 :: nil|);;
    (mqgetinfo_mq_info_validptr_err (|Vptr x0 :: nil|)
    ?? mqgetinfo_pdata_validptr_err (|Vptr x1 :: nil|)
       ?? mqgetinfo_query_memcpy_get_mq_info_oseventtbl (|Vptr x0 :: v10 :: nil|);;
            mqgetinfo_query_memcpy_get_pdata_oseventtbl (|Vptr x1 :: v11 :: nil|);;
            memcpy_empty (|v10 :: v11 :: V$ OS_EVENT_TBL_SIZE :: nil|);;
            mqgetinfo_succ_ret (|nil|)) ||>  **
   LV mq_info @ mq_info_t ∗ |-> Vptr x0 **
   Astruct x0 mq_info_t
     (Vint32 i6
      :: Vint32 i5
      :: Vint32 i4
         :: Vint32 i3 :: Vint32 i2  :: (if val_eq' x10 (Vptr (pb, pi)) then Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))  else Vint32 vblock) :: x6 :: nil) **
   GV Mq_Attr @ mq_attr_t ∗ |-> Vptr (b, i0) **
   Astruct (b, i0 +ᵢ $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen mq_attr_t))
     mq_attr_t (v1' :: v2' :: v3' :: v4' :: v5' :: Vptr (pb, pi) :: v6' :: nil) **
   A_dom_lenv
     ((os_code_defs.pdata, OS_Q_DATA ∗)
      :: (mq_info, mq_info_t ∗)
         :: (mqdes, long)
            :: (os_code_defs.i, long)
               :: (Val_uacheck, char_t)
                  :: (p, OS_EVENT ∗) :: (Val_osqquery, char_t) :: (ptcb, OS_TCB ∗) ::  (x, (char_t) ∗) :: (y, (char_t) ∗)
                   :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
   LV mqdes @ long |-> Vint32 i **
   AEvStructHeap v'2 **
   AEvStructHeap v'100 **
   Astruct ptcb_addr OS_TCB_flag
     (v'47
      :: v'1
         :: x10
            :: x9 :: Vint32 i13
               :: Vint32 i12
                  :: Vint32 i11
                     :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: nil) **
   dllseg v'47 (Vptr ptcb_addr) v'44 Vnull vl2 OS_TCB_flag (fun vl : vallist => nth_val 1 vl)
     (fun vl : vallist => nth_val 0 vl) **
   dllseg (Vptr tls_head) Vnull v'1 (Vptr ptcb_addr) vl1 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   p_local OSLInv tid
     (logic_val (V$ 1)
      :: logic_val (V$ __EvLoc_normal)
         :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
   GV OSTCBList @ OS_TCB ∗ |-> Vptr tls_head **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
   LV ptcb @ OS_TCB ∗ |-> Vptr ptcb_addr **
   HEvStructHeap
     (v'14 ++
      (x0, mq_info_t,
      Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) **  H1)).
  introv Hsat.
  destruct Hsat as [Hsat | Hsat].
  (* x10 = Vptr (pb, pi) *)
  clear -Hsat H25.
  sep split in Hsat. destruct H as (H & _).
  destruct H25 as [Heq | ((pb' & pi') & Heq) ]; subst; simpl in H; tryfalse.
  simpl val_eq'.
  destruct (Int.eq pi' pi) eqn: ifeq2;
  destruct (peq pb' pb) eqn: ifeq1; simpl in H; tryfalse.
  eapply semacc_int_eq_true in ifeq2; subst pi'; subst pb'.
  change (left eq_refl && true) with true.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  (* x10 <> Vptr (pb, pi) *)
  clear -Hsat H25.
  sep split in Hsat.
  destruct H25 as [Heq | ((pb' & pi') & Heq) ]; subst; simpl in H;
  destruct H; tryfalse;
  simpl val_eq';  try (destruct (Int.eq pi' pi) eqn: ifeq2;
  destruct (peq pb' pb) eqn: ifeq1; simpl in H; tryfalse);
  try rewrite andb_false_r; try  change (right n && true) with false;
  sep auto.

  (* compose AEvStructHeap*)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  eexists. exists v'2 v'100.
  sep pauto.

  destruct (val_eq' x10 (Vptr (pb, pi))) ;
  simpl; auto.
  splits;auto.
  eapply OSMutex_common.postintlemma1.
  splits;eauto.
  (* actrual assign ptcb *)
  eapply conseq_rule.
  eauto.
  2: { hoare forward. go. }
  introv Hsat.
  subst ptcb_addr.
  lets Hcp: Htls_right'.
  simpl in Hcp.
  simpljoin.
  inverts H20.
  inverts H35.
  rename H36 into Htj_sig; rename H37 into Hptcb_node; rename H38 into Hptcb_right.
  assert (Hget_ptcb: exists st sus', TcbMod.get tls2 (v'50, Int.zero) = Some (i11, st, x9, sus')).
  { eapply TCBListP_head_in_tcb'; eauto. }
  destruct Hget_ptcb as (st & sus' & Hget_ptcb).
  lets Hget_ptcb': Hget_ptcb.
  eapply TcbMod.join_get_r in Hget_ptcb'; eauto.
  lets Hcp: Htj_sig. unfold join,sig in Hcp; unfold TcbMap in Hcp.
  eapply TcbMod.join_sig_get in Hcp.
  destruct x4 as (((prio & tcb_st) & msg) & sus).
  rewrite Hget_ptcb in Hcp; inverts Hcp.
  
  assert(Hgetq: exists x y pwl wls, EcbMod.get v'11 (pb, pi) = Some (absmsgq x y pwl, wls)).
  {
   clear -H9 Hget Hveid  .
   destruct Hveid .
   simpljoin1.
   unfold RH_EIBlk_ECBlk_Q_P in H9.
   eapply H9 in Hget.
   inverts H0. 
   eauto.
   destruct H; tryfalse.
  }
  
  destruct Hgetq. do 3 destruct H3.
  rename H3 into Hgetq.
  assert (Hst_case: ((val_eq' x10 (Vptr (pb, pi)) = true -> exists wt, (tcb_st = wait (os_stat_q(pb, pi)) wt) \/ (tcb_st = wait (os_stat_postq(pb, pi)) wt)) /\ 
  (val_eq' x10 (Vptr (pb, pi)) = false -> ~(exists wt, tcb_st = wait (os_stat_q (pb, pi)) wt \/ tcb_st = wait (os_stat_postq (pb, pi)) wt)))).
  { clear -H Hgetq Htls_right' Htj_sig Hptcb_node Hget_ptcb' Hget_ptcb.
    rename pb into pb'; rename pi into pi'.
    funfold Hptcb_node.
    funfold H2.
    destruct H3 as (Hlh_rdy & Hhl_rdy & Hlh_suspend & Hhl_suspend & Hlh_wait & Hhl_wait).
    destruct Hhl_wait as (Hhl_time & Hhl_sem & Hhl_q & Hhl_mb & Hhl_ms & Hhl_pq & Hhl_semsuspend & Hhl_qsuspend & Hhl_pqsuspend & Hhl_mbsuspend & Hhl_mssuspend & Hhl_port & Hhl_portsuspend).
    destruct H as (Hrhq & Hrhsem & Hrhmb & Hrhmx & Hrhport).
    (* tcb_st = rdy *)
    destruct tcb_st.
    eapply get_tcb_stat_rdy_sus in Hget_ptcb; eauto.
    destruct Hget_ptcb as (Hst & Heptr); invert Heptr.
    simpl val_eq'.
    split; introv Hcond; tryfalse.
    introv Hf; destruct Hf as (wt & Hf); destruct Hf; tryfalse.
    (* tcb_st = wait os_stat_time i1 *)
    destruct t.
    Focus 4.
    eapply get_tcb_stat_rdy_sus in Hget_ptcb; eauto.
    destruct Hget_ptcb as (Hst & Heptr); invert Heptr.
    simpl val_eq'.
    split; introv Hcond; tryfalse.
    introv Hf; destruct Hf as (wt & Hf); destruct Hf; tryfalse.
    (* tcb_st = wait (os_stat_sem e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus ; subst;
         [ specialize (Hhl_semsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_semsuspend;
            destruct Hhl_semsuspend as (Hhl_sem' & Heptr & Hst)
           | specialize (Hhl_sem _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_sem;
            destruct Hhl_sem as (Hhl_sem' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb pb') eqn: eq_b;
        destruct (Int.eq pi pi') eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); 
        try (destruct Hf); tryfalse; auto.
        eapply Hrhsem in Hget_ptcb'; eauto.
        destruct Hget_ptcb' as (mn & mwl & Hget_ptcb' & Hin).
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb'.
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
        eapply Hrhsem in Hget_ptcb'; eauto.
        destruct Hget_ptcb' as (mn & mwl & Hget_ptcb' & Hin).
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb'.
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
    (*  tcb_st = wait (os_stat_q e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus ; subst;
      [ specialize (Hhl_qsuspend _ _ _ _ (eq_refl _)) ;
        unfold WaitTCBblk in Hhl_qsuspend;
        destruct Hhl_qsuspend as (Hhlq' & Heptr & Hst)
     | specialize (Hhl_q _ _ _ _ (eq_refl _)) ;
       unfold WaitTCBblk in Hhl_q;
       destruct Hhl_q as (Hhlq' & Heptr & Hst) ];
     inverts Heptr; inverts Hst;
     destruct e as (pb & pi);
     simpl val_eq';
     destruct (peq pb pb') eqn: eq_b;
     destruct (Int.eq pi pi') eqn: eq_i;
     try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r; 
         split; introv Hcond; tryfalse; eauto;
         introv Hf; destruct Hf as (wt & Hf); inverts Hf;
         try rewrite Int.eq_true in eq_i; tryfalse. 
         inverts H. rewrite Int.eq_true in eq_i. tryfalse.
         inverts H. rewrite Int.eq_true in eq_i. tryfalse.
    (* tcb_st = wait (os_stat_postq e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus; subst;
         [ specialize (Hhl_pqsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_pqsuspend;
            destruct Hhl_pqsuspend as (Hhl_pq' & Hdlyzero & Heptr & Hst)
           | specialize (Hhl_pq _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_pq;
            destruct Hhl_pq as (Hhl_pq' & Hdlyzero & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
       destruct e as (pb & pi);
       simpl val_eq';
       destruct (peq pb pb') eqn: eq_b;
       destruct (Int.eq pi pi') eqn: eq_i;
       try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
       try rewrite andb_true_r; try rewrite andb_false_r;
       split; introv Hcond; tryfalse; eauto;
       introv Hf; destruct Hf as (wt & Hf); inverts Hf;
       try rewrite Int.eq_true in eq_i; tryfalse. 
       inverts H. rewrite Int.eq_true in eq_i. tryfalse.
       inverts H. rewrite Int.eq_true in eq_i. tryfalse.
    (*  tcb_st = wait (os_stat_mbox e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus ; subst;
         [ specialize (Hhl_mbsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_mbsuspend;
            destruct Hhl_mbsuspend as (Hhl_mb' & Heptr & Hst)
           | specialize (Hhl_mb _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_mb;
            destruct Hhl_mb as (Hhl_mb' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb pb') eqn: eq_b;
        destruct (Int.eq pi pi') eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); 
        try (destruct Hf); tryfalse; auto.
        eapply Hrhmb in Hget_ptcb'; eauto;
        destruct Hget_ptcb' as (mn & mwl & Hget_ptcb' & Hin);
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
        eapply Hrhmb in Hget_ptcb'; eauto;
        destruct Hget_ptcb' as (mn & mwl & Hget_ptcb' & Hin);
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
    (* tcb_st = wait (os_stat_mutexsem e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus ; subst;
         [ specialize (Hhl_mssuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_mssuspend;
            destruct Hhl_mssuspend as (Hhl_ms' & Heptr & Hst)
           | specialize (Hhl_ms _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_ms;
            destruct Hhl_ms as (Hhl_ms' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb pb') eqn: eq_b;
        destruct (Int.eq pi pi') eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); 
        try (destruct Hf); tryfalse; auto.
         destruct Hrhmx as (_ & Hrhmx & _);
         eapply Hrhmx in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mn1 & mn2 & mwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
         destruct Hrhmx as (_ & Hrhmx & _);
         eapply Hrhmx in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mn1 & mn2 & mwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
    (* tcb_st = wait (os_stat_port e) i1 *)
    lets Hcp: Hget_ptcb.
    destruct sus ; subst;
         [ specialize (Hhl_portsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_portsuspend;
            destruct Hhl_portsuspend as (Hhl_sem' & Heptr & Hst)
           | specialize (Hhl_port _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_port;
            destruct Hhl_port as (Hhl_port' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb pb') eqn: eq_b;
        destruct (Int.eq pi pi') eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); 
        try (destruct Hf); tryfalse; auto.
        eapply Hrhport  in Hget_ptcb'; eauto.
        destruct Hget_ptcb' as (wl & Hget_ptcb' & Hin).
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb'.
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
        eapply Hrhport in Hget_ptcb'; eauto.
        destruct Hget_ptcb' as (wl & Hget_ptcb' & Hin).
        unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb'.
        rewrite Hgetq in Hget_ptcb'; inverts Hget_ptcb'.
  }
  
  destruct Hst_case as (Hst_same & Hst_diff).
  (* exit while loop  *)
  assert (Hnone: TcbMod.get tls1 (v'50, Int.zero) = None).
  { eapply tjoin_get_none_l. instantiate (2:= tls2). eauto. eauto. }
    
  assert (Hblked_eq: get_tls_blocked_q_num (TcbMod.lst (TcbMod.merge tls1 (TcbMod.sig (v'50, Int.zero) (prio, tcb_st, msg, sus)))) (pb, pi) = 
    (get_tls_blocked_q_num (((v'50, Int.zero),(prio, tcb_st, msg, sus))::nil) (pb, pi)  + get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi))%nat).
  { assert (Hmerge: TcbMod.join (TcbMod.sig (v'50, Int.zero) (prio, tcb_st, msg, sus)) tls1(TcbMod.merge (TcbMod.sig (v'50, Int.zero) (prio, tcb_st, msg, sus)) tls1)).
    { clear -Htj' Htj_sig.
      eapply TcbMod.join_whole2part;
      eapply TcbMod.join_comm; eauto.
    }
    eapply TcbMod.join_comm in Hmerge.
    eapply TcbMod.join_meq_eql in Hmerge.
    rewrite <- Hmerge.
    eapply get_tls_blocked_q_succ_eq; eauto.
  }
  exists ((v'2 ++ (x0, mq_info_t,
             Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 
             :: (if val_eq' x10 (Vptr (pb, pi))
                    then Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))
                 else Vint32 vblock) :: x6 :: nil) :: v'100)).
  exists (get_tls_blocked_q_num (TcbMod.lst (TcbMod.merge tls1 (TcbMod.sig (v'50, Int.zero) (prio, tcb_st, msg, sus)))) (pb, pi)).
  exists x2.
  exists (vl1 ++ (x2
          :: v'1 :: x10 :: msg :: Vint32 i13 :: Vint32 i12  :: Vint32 prio  :: Vint32 i10 :: Vint32 i9 :: Vint32 i8 :: Vint32 i7 :: nil) :: nil).
  exists vl2 (TcbMod.merge tls1 (sig (v'50, Int.zero) (prio, tcb_st, msg, sus))) x3.
  (* discuss where ptcb is null *)
  destruct H23 as [Hptcb_null | (pnext & Hptcb_ptr)];
  subst x2.
  (* new ptcb = Vnull, get out of the loop *)
  assert (Heq_right: vl2 = nil /\ x3 = TcbMod.emp).
  { clear -Hptcb_right. destruct vl2; auto. simpl in *. simpljoin. tryfalse. }
  destruct Heq_right; subst vl2; subst x3.
  assert (Hmerge_eq: (TcbMod.merge tls1 (TcbMod.sig (v'50, Int.zero) (prio, tcb_st, msg, sus))) = v'12).
  { clear -Htj' Htj_sig.
    eapply TcbMod.join_comm in Htj_sig.
    eapply TcbMod.join_emp_eq in Htj_sig; subst.
    eapply TcbMod.join_meq_eql in Htj'; subst.
    auto.
  Optimize Proof.
  Optimize Heap.
  }
    
  eexists.
  sep pauto.
  sep_lifts_trms dllseg.
  eapply dllseg_compose.
  sep cancel (dllseg (Vptr tls_head)).
  simpl dllseg at 1.
  unfold node.
  simpl dllseg in Hsat.
  sep cancel Aop.
  sep cancel A_dom_lenv.
  sep pauto.
  split; auto. go.
  2: { rewrite app_nil_r. auto. }
  2: { right. splits; auto.
       clear -Htls_whole Htls_eq_alt.
       rewrite Htls_eq_alt. auto. }
  { rewrite Hblked_eq.
    lets Hblk_num_pos: get_tls_blocked_q_pos (TcbMod.lst tls1) (pb, pi).
    remember (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) as blk_num.
    destruct (val_eq' x10 (Vptr (pb, pi))) eqn: blk_cond.
    (* found new bocked tcb *)
    specialize (Hst_same (eq_refl _)). 
    destruct Hst_same as (wt & Hst_same).
    destruct Hst_same. subst tcb_st.
    unfold get_tls_blocked_q_num. rewrite tid_beq_true.
    rewrite Nat.add_0_r.
    left. 
    clear -Hblk_cases Hvblock'_eq Hblk_num_pos Hget_struct_none Hget_vblock' Hget' H19.
    split. eapply Nat.add_pos_nonneg; auto with zarith.
    assert(Set_struct'
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 vblock :: x6 :: nil) :: v'100) x0 task_blocked (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) = 
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) :: x6 :: nil) :: v'100)).
    {
     eapply set_struct_update_nth_val';eauto.
     unfold id_nth. unfold id_nth'. simpl. eauto. 
     simpl. eauto.
    }
        
    rewrite <- H. clear H.
    simpl Int_add_n.
    destruct Hvblock'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
    subst blk_num. inverts Heq.
    simpl Int_add_n in *.
    destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
    apply Nat.lt_irrefl in Hlt.
    tryfalse.
    rewrite <- Heq.
    change ($ 1) with Int.one. auto.
    change ($ 1) with Int.one.
    destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
    2: { subst blk_num. apply Nat.lt_irrefl in Hblk_lt. tryfalse. } 
    rewrite Heq'. inverts Heq. 
    { assert((Set_struct'
       (v'14++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1  :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n blk_num i1 Int.one))) =  
       (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2  :: Vint32 (Int_add_n blk_num i1 Int.one):: x6 :: nil) :: v'30)).
      {
       eapply set_struct_update_nth_val';eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. 
       simpl. eauto.
      }
      rewrite H.
      assert((Set_struct'
       (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one) :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus)))) =  
       (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus))):: x6 :: nil) :: v'30)).
      {
       eapply set_struct_update_nth_val'. fold mq_info_t. 
       rewrite <- Heq' in H. rewrite H in Hget_vblock'. eauto. eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
      }
      rewrite H0.
      assert((Set_struct'
       (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus))) =  
       (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus)):: x6 :: nil) :: v'30))).
      { eapply set_struct_update_nth_val';eauto.
        unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
      }
      rewrite  H1. auto.
    }

    subst tcb_st.
     unfold get_tls_blocked_q_num. rewrite tid_beq_true.
    rewrite Nat.add_0_r.
    left.
    clear -Hblk_cases Hvblock'_eq Hblk_num_pos Hget_struct_none Hget_vblock' Hget' H19.
    split. eapply Nat.add_pos_nonneg; auto with zarith.
    assert(Set_struct'
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 vblock :: x6 :: nil) :: v'100) x0 task_blocked (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) = 
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) :: x6 :: nil) :: v'100)).
    { eapply set_struct_update_nth_val';eauto.
      unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
    }
    rewrite <- H. clear H.
    simpl Int_add_n.
    destruct Hvblock'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
    subst blk_num. inverts Heq.
    simpl Int_add_n in *.
    destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
    apply Nat.lt_irrefl in Hlt. 
    tryfalse.
    rewrite <- Heq.
    change ($ 1) with Int.one. auto.
    change ($ 1) with Int.one.
    destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
    2: { subst blk_num. apply Nat.lt_irrefl in Hblk_lt. tryfalse. } 
    rewrite Heq'. inverts Heq. 
    { assert((Set_struct'
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n blk_num i1 Int.one))) =
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2  :: Vint32 (Int_add_n blk_num i1 Int.one):: x6 :: nil) :: v'30)).
      { eapply set_struct_update_nth_val';eauto.
        unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
      }
      rewrite H.
      assert((Set_struct'
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one) :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus)))) =  
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus))):: x6 :: nil) :: v'30)).
      { eapply set_struct_update_nth_val'. fold mq_info_t. rewrite <- Heq' in H  . rewrite H in Hget_vblock'. eauto. eauto.
        unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
      }
      rewrite H0. 
      assert((Set_struct'
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus))) = 
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus)):: x6 :: nil) :: v'30))).
      { eapply set_struct_update_nth_val';eauto.
        unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
      }
      rewrite  H1. auto.
    }

    (* not found the new blocked tcb *)
    specialize (Hst_diff (eq_refl _)).
    assert (Heq: (get_tls_blocked_q_num ((v'50, Int.zero, (prio, tcb_st, msg, sus)) :: nil) (pb, pi) = 0)%nat).
    { clear -Hst_diff. simpl.
      destruct tcb_st; auto.
      destruct t; auto.
      destruct ( tidspec.beq e (pb, pi) ) eqn: eq1; auto.
      eapply tidspec.beq_true_eq in eq1; subst.
      false. eapply Hst_diff; eauto.
      destruct ( tidspec.beq e (pb, pi) ) eqn: eq1; auto.
      eapply tidspec.beq_true_eq in eq1; subst.
      false. eapply Hst_diff; eauto.
    }
    rewrite Heq. auto.
  }
   
  (* new ptcb = Vptr pnext, still in the loop *)
  assert (Hnnil: vl2 <> nil).
  { destruct vl2; auto.
    sep_lifts_trms_in Hsat (dllseg (Vptr pnext)).
    sep remember (1:: nil) in Hsat.
    clear -Hsat.
    simpl dllseg in Hsat.
    sep split in Hsat.
    tryfalse.
  }
  exists pnext.
  sep pauto.
  sep_lifts_trms dllseg.
  eapply dllseg_compose.
  sep cancel (dllseg (Vptr tls_head)).
  simpl dllseg at 1.
  unfold node.
  sep cancel Aop.
  sep cancel A_dom_lenv.
  sep pauto.
  split; auto. go.
  2: {clear. rewrite <- app_assoc. rewrite list_prop1. auto. }
  2: { left. splits; auto.
       eapply TcbMod.join_comm.
       eapply join_join_merge'; eapply TcbMod.join_comm; eauto.
       eapply OSQPostPure.TCBList_P_Combine; eauto.
       eapply OSQPostPure.tcbdllseg_get_last_tcb_ptr with (s:= s).
       unfold tcbdllseg. sep cancel (dllseg (Vptr tls_head)); eauto.
       eapply TcbMod.join_merge_disj.
       eapply join_join_disj; eauto.
       unfold TCBList_P.
       unfold V_OSTCBNext; simpl val_inj.
       repeat eexists; eauto.
       unfold TcbJoin. apply TcbMod.map_join_emp.
       right.
       rewrite last_get.
       eexists. splits; eauto.
       clear; introv Hf.
       rewrite <- length_zero_iff_nil in Hf.
       rewrite last_length in Hf.
       auto with zarith.
  }
  { rewrite Hblked_eq.
    lets Hblk_num_pos: get_tls_blocked_q_pos (TcbMod.lst tls1) (pb, pi).
    remember (get_tls_blocked_q_num (TcbMod.lst tls1) (pb, pi)) as blk_num.
    destruct (val_eq' x10 (Vptr (pb, pi))) eqn: blk_cond.
    (* found new bocked tcb *)
    specialize (Hst_same (eq_refl _));
    destruct Hst_same as (wt & Hst_same);
    destruct Hst_same; subst tcb_st.
    unfold get_tls_blocked_q_num. rewrite tid_beq_true.
    rewrite Nat.add_0_r.
    left.
    clear -Hblk_cases Hvblock'_eq Hblk_num_pos Hget_struct_none Hget_vblock' Hget' H19.
    split. eapply Nat.add_pos_nonneg; auto with zarith.
    assert(Set_struct'
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 vblock :: x6 :: nil) :: v'100) x0 task_blocked (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) = 
        (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (vblock +ᵢ $ 1) ($ Byte.modulus))) :: x6 :: nil) :: v'100)).
    { eapply set_struct_update_nth_val';eauto.
      unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
    }
    rewrite <- H. clear H.
    simpl Int_add_n.
    destruct Hvblock'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
    subst blk_num. inverts Heq.
    simpl Int_add_n in *.
    destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
    apply Nat.lt_irrefl in Hlt. 
    tryfalse.
    rewrite <- Heq.
    change ($ 1) with Int.one. auto.
    change ($ 1) with Int.one.
    destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
    2: {  subst blk_num.  apply Nat.lt_irrefl in Hblk_lt. tryfalse. } 
    rewrite Heq'. inverts Heq.
    { 
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n blk_num i1 Int.one)))  = 
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one):: x6 :: nil) :: v'30)).
     {
      eapply set_struct_update_nth_val';eauto.
      unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
     }
     rewrite H.
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one) :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus)))) =
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus))):: x6 :: nil) :: v'30)).
     { eapply set_struct_update_nth_val'. fold mq_info_t. 
       rewrite <- Heq' in H  . rewrite H in Hget_vblock'. eauto. eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
     }
     rewrite H0.
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus))) = 
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 ::  Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus)):: x6 :: nil) :: v'30))).
     {
      eapply set_struct_update_nth_val';eauto.
      unfold id_nth. unfold id_nth'. simpl. eauto. 
      simpl. eauto.
     }
     rewrite  H1. auto.
    }

    unfold get_tls_blocked_q_num. rewrite tid_beq_true.
    rewrite Nat.add_0_r.
    left.
    clear -Hblk_cases Hvblock'_eq Hblk_num_pos Hget_struct_none Hget_vblock' Hget' H19.
    split. eapply Nat.add_pos_nonneg; auto with zarith.
    assert(Set_struct'
     (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 vblock :: x6 :: nil) :: v'100) x0 task_blocked (Vint32 (Int.modu (vblock +ᵢ  $ 1) ($ Byte.modulus))) = 
     (v'2 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (vblock +ᵢ  $ 1) ($ Byte.modulus))) :: x6 :: nil) :: v'100)).
    { eapply set_struct_update_nth_val';eauto.
      unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
    }
    rewrite <- H. clear H.
    simpl Int_add_n.
    destruct Hvblock'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
    subst blk_num. inverts Heq.
    simpl Int_add_n in *.
    destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
    apply Nat.lt_irrefl in Hlt.
    tryfalse.
    rewrite <- Heq.
    change ($ 1) with Int.one. auto.
    change ($ 1) with Int.one.
    destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
    2: { subst blk_num. apply Nat.lt_irrefl in Hblk_lt. tryfalse. } 
    rewrite Heq'. inverts Heq.
    {
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n blk_num i1 Int.one))) =  
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one):: x6 :: nil) :: v'30)).
     { eapply set_struct_update_nth_val';eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
     }
     rewrite H.
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n blk_num i1 Int.one) :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus)))) = 
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus))):: x6 :: nil) :: v'30)).
     { eapply set_struct_update_nth_val'. fold mq_info_t. 
       rewrite <- Heq' in H. rewrite H in Hget_vblock'. eauto. eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
     }
     rewrite H0.
     assert((Set_struct'
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ Int.one) ($ Byte.modulus))) =
      (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int.modu (Int_add_n blk_num i1 Int.one +ᵢ  Int.one) ($ Byte.modulus)):: x6 :: nil) :: v'30))).
     { eapply set_struct_update_nth_val';eauto.
       unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
     }
     rewrite  H1. auto.
    }

    (* not found the new blocked tcb *)
    specialize (Hst_diff (eq_refl _)).
    assert (Heq: (get_tls_blocked_q_num ((v'50, Int.zero, (prio, tcb_st, msg, sus)) :: nil) (pb, pi) = 0)%nat).
    { clear -Hst_diff. simpl.
      destruct tcb_st; auto.
      destruct t; auto.
      destruct ( tidspec.beq e (pb, pi) ) eqn: eq1; auto.
      eapply tidspec.beq_true_eq in eq1; subst.
      false. eapply Hst_diff; eauto.
      destruct ( tidspec.beq e (pb, pi) ) eqn: eq1; auto.
      eapply tidspec.beq_true_eq in eq1; subst.
      false. eapply Hst_diff; eauto.
    }
    rewrite Heq. auto.
  }
   
  (* Aisfalse ptcb ′  *)
  hoare unfold.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
  introv Hsat.
  sep get rv.
  sep split in Hsat.
  clear -H3. destruct H3 as [ (Heq & _) | (Heq & _)]; subst; simpl; auto.
  unprotect HeqH1.
  hoare unfold.
  destruct H3 as [ (Heq & _) | (Heq & Heq2)];subst v'47; simpl in H22; destruct H22; tryfalse.
  simpljoin.
  substs.

  (* fold AMqAttr *)
  eapply backward_rule1. 
  intros.
  eapply AMqAttr_select_sn_ex_strong.
  exists v'42 (Z.to_nat (Int.unsigned i)) v'43.
  sep pauto.
  
  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat tcbdllseg.
  eapply tcbdllseg_split in Hsat; eauto.
  hoare unfold.
  assert (Hct_eq: v'47 = tid).
  { clear -H1 Htls_last_case.
     destruct Htls_last_case as [ (Hnil & Heq) | (vl & Hnnil & Hlast & Heq)];
    subst; inverts Heq;
    destruct H1 as [ ( Hnnil' & Hlast) | (Hnil & Heq)];
    subst; try inverts Heq;
    auto; tryfalse.
    rewrite Hlast in H0. inverts H0.
   auto.
  Optimize Proof.
  Optimize Heap.
  }
  subst v'47.

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, evstructheapid).
  destruct H21 as [(Hblk_lt & Hevstruct') | (Hblk_0 & Hevstruct')];
  subst v'1.
  
  (* the blocked tasks exists *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_blocked_end; eauto.
  pure_auto.
  simpl. eauto.
  eapply absinfer_eq.
  
  (*EXIT_CRITICAL*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep_lifts_trms AOSTCBList.
  unfold AOSTCBList.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel Aier.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel (tcbdllseg (Vptr tls_head)).
  sep cancel tcbdllseg.
  sep cancel APthreadAttr.
  sep cancel AMqCap.
  sep cancel CapabilityInv.
  sep split; eauto.
  unfold R_Q_Data_P.
  clear -Hrqdata H19.
  { intros.
    assert((Set_struct'
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one))) = 
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30)).
    { clear -H19.
      induction v'14.
      change ((nil ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 ::Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one):: x6 :: nil) :: v'30))  with (((x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30)).
     simpl.
     rewrite beq_tid_true;auto.
     assert(Get_struct ((a :: v'14) ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30) x0 =
     Get_struct (v'14 ++ (x0, mq_info_t,  Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32  (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30) x0).
     unfold Get_struct.
     destruct a. destruct p.
     simpl.
     assert(os_inv.beq_addrval a x0 = false).
     {
      clear -H19.
      unfold opsem.Get_struct in H19.
      destruct (os_inv.beq_addrval a x0); tryfalse. auto.
     }
     rewrite H; auto.
     assert(Get_struct v'14 x0 = Get_struct (a :: v'14) x0).
     {
      destruct a; destruct p.
      unfold Get_struct; simpl.
      assert(os_inv.beq_addrval a x0 = false).
      {
       clear -H19.
       unfold opsem.Get_struct in H19.
       destruct (os_inv.beq_addrval a x0); tryfalse. auto.
      }
      rewrite H0.
      auto.
     }
     unfold opsem.Get_struct in IHv'14.
     unfold Get_struct in H0.
     rewrite H0 in IHv'14.
     lets Hx: IHv'14 H19.
     unfold Set_struct'.
     destruct a; destruct p.
     simpl.
     assert(os_inv.beq_addrval a x0 = false).
     {
      clear -H19.
      unfold opsem.Get_struct in H19.
      destruct (os_inv.beq_addrval a x0); tryfalse.
      auto.
     }
     fold Set_struct'.
     rewrite H1.
     rewrite Hx. auto.
    }
    rewrite H0 in H. clear H0.
    unfold R_Q_Data_P in Hrqdata.
    assert(qid = x0 \/ qid <> x0) by tauto.
    destruct H0. inverts H0.
    assert(Get_struct
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30) x0 = 
     Some (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil)).
    {
     clear -H19.
     induction v'14.
     change ((nil ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30)) with ((x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30).
     simpl. rewrite beq_tid_true. auto.
     destruct a; destruct p.
     assert (a <> x0 \/ a = x0) by tauto.
     destruct H.
     simpl.
     destruct (os_inv.beq_addrval a x0) eqn :eq1.
     eapply beq_tid_true_eq in eq1. tryfalse.
     assert(Get_struct ((a, t, l) :: v'14) x0  = Get_struct (v'14) x0 ).
     simpl. rewrite eq1. auto.
     unfold opsem.Get_struct in H19.
     unfold Get_struct in H0.
     rewrite H0 in H19.
     eapply IHv'14 in H19. auto.
     inverts H.
     simpl in H19;rewrite beq_tid_true in H19;tryfalse.
    }
    rewrite H0 in H . inverts H.
    assert(Get_struct
     (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 ::  Vint32 (Int_add_n (get_tls_blocked_q_num (TcbMod.lst v'12) (pb, pi)) i1 Int.one) :: x6 :: nil) :: v'30) qid =
     Get_struct (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 ::  x6 :: nil) :: v'30) qid).
    {
     clear -H19 H0.
     induction v'14.
     simpl.
     destruct (os_inv.beq_addrval x0 qid) eqn:H.
     eapply beq_tid_true_eq in H. tryfalse. auto.
     destruct a ; destruct p.
     assert(a = x0 \/ a <> x0) by tauto.
     destruct H. inverts H.
     simpl in H19; rewrite beq_tid_true in H19. tryfalse.
     simpl in H19.
     destruct (os_inv.beq_addrval a x0) eqn : H1.
     eapply beq_tid_true_eq in H1. tryfalse.
     eapply IHv'14 in H19.
     simpl.
     destruct (os_inv.beq_addrval a qid) eqn: H2. auto. auto.
    }
    rewrite H1 in H.
    eapply Hrqdata in H.
    eauto.
  }
  pure_auto. pure_auto.
  
  (*memcpy*)
  clear -E1 E2 E3.
  hoare forward prim.
  hoare unfold.
  hoare normal pre.
  
  unfold EvtInv.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'29 x0 = None \/ exists t, Get_struct v'29 x0 = Some t).
  intros.
  assert (exists t, Get_struct v'29 x0 = t) by eauto.
  destruct H2.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H2 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'29.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'29 in Hget.
  auto.
  Optimize Proof.
  Optimize Heap.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.
  

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.

  sep cancel AEvStructHeap.
  sep pauto. 
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.
  destruct x0.
  hoare forward.
  unfold field_offset. 
  unfold field_offsetfld.
  simpl.
  eauto.
  
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto. 
  exists l v'13 v'41.
  sep pauto.

  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto. pure_auto.
  
  clear -E1 E2 E3.
  hoare forward prim.
  hoare unfold.
  hoare normal pre.
  
  unfold EvtInv.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg: Get_struct v'28 x1 = None \/ exists t, Get_struct v'28 x1 = Some t).
  intros.
  assert (exists t, Get_struct v'28 x1 = t) by eauto.
  destruct H2.
  destruct x.
  right; eauto.
  left; eauto.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H2 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x1 ).
  clear - Hget.
  inductions v'28.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x1) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'28 in Hget.
  auto.
  subst a.

  assert (Ht: t = OS_Q_DATA \/ t <> OS_Q_DATA) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.
  
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_OS_Q_DATA; eauto. sep pauto.

  sep cancel AEvStructHeap.
  sep pauto. 
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.
  destruct x1.
  hoare forward.
  unfold field_offset. 
  unfold field_offsetfld.
  simpl.
  eauto.
  
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA; eauto.
  exists l v'12 v'40.
  sep pauto.
  
  (* EXIT_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto. pure_auto.
  assert((exists oseventtbl,v10 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b, i0) OSEventTbl mq_info_t) \/ ~(exists oseventtbl, v10 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b, i0) OSEventTbl mq_info_t)) by tauto.
  destruct H10.
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     apply absabort_rule. 
  }
    simpljoin1.
    eapply abscsq_rule. 
    apply noabs_oslinv.
    
    eapply mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl; eauto.
    pure_auto.
    eapply absinfer_eq.
    
  assert((exists oseventtbl,v11 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b0, i1) OSEventTbl OS_Q_DATA) \/ ~(exists oseventtbl, v11 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b0, i1) OSEventTbl OS_Q_DATA)) by tauto.
  destruct H10.
  2:{
      eapply abscsq_rule. 
      apply noabs_oslinv.
      eapply mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl_abt; eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule. 
  
  }
  simpljoin1.
  eapply abscsq_rule. 
  apply noabs_oslinv.

  eapply mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl; eauto.
  pure_auto.
  eapply absinfer_eq.

  hoare forward.
  instantiate (2:= mqgetinfo_succ_ret (|nil|)).
  unfold spec_code_cons.
  unfold memcpy_spec.
  sep pauto.
  sep cancel p_local.
  inverts H12; inverts H13.
  sep pauto.
  pure_auto.

  sep pauto. instantiate (1:=init_lg). sep pauto.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  inverts H10.

  hoare_lifts_trms_pre (Aop).
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_succ_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  (* return -1 *)
  hoare forward.

  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_blocked_end; eauto.
  pure_auto.
  simpl. eauto.
  eapply absinfer_eq.
  rewrite Hblk_0.
  
  (*EXIT_CRITICAL*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep_lifts_trms AOSTCBList.
  unfold AOSTCBList.
  unfold EvtInv.
  unfold AMqEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqAttr.
  sep cancel (tcbdllseg (Vptr tls_head)).
  sep cancel tcbdllseg.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  unfold Int_add_n.
  assert((Set_struct'
   (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 i1)) = 
   (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30)).
  { eapply set_struct_update_nth_val';eauto.
    unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
  }
  rewrite H20.
  sep pauto.
  sep split; eauto.
  unfold Int_add_n.

  assert((Set_struct'
   (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) x0 task_blocked (Vint32 i1)) =
   (v'14 ++ (x0, mq_info_t, Vint32 i6 :: Vint32 i5 :: Vint32 i4 :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: x6 :: nil) :: v'30) 
         ).
  { eapply set_struct_update_nth_val';eauto.
    unfold id_nth. unfold id_nth'. simpl. eauto. simpl. eauto.
  }
  rewrite H21. eauto.
  pure_auto. pure_auto.
  
  (*memcpy*)
  clear -E1 E2 E3.
  hoare forward prim.
  hoare unfold.
  hoare normal pre.
  
  unfold EvtInv.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg:  Get_struct v'29 x0 = None \/ exists t, Get_struct v'29 x0 = Some t).
  eapply get_struct_or.

  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.

  destruct H2 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x0 ).
  clear - Hget.
  inductions v'29.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x0) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'29 in Hget.
  auto.
  Optimize Proof.
  Optimize Heap.
  subst a.

  assert (Ht: t = mq_info_t \/ t <> mq_info_t) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_mq_info_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule. 
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_mq_info_t; eauto. sep pauto.
  sep cancel AEvStructHeap.
  sep pauto. 
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.
  destruct x0.
  hoare forward.
  unfold field_offset. 
  unfold field_offsetfld.
  simpl.
  eauto.
  
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_mq_info_t; eauto.
  exists l v'13 v'41.
  sep pauto.
  
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto. pure_auto.

  
  clear -E1 E2 E3.
  hoare forward prim.
  hoare unfold.
  hoare normal pre.
  
  unfold EvtInv.
  hoare normal pre.
  hoare unfold.
  hoare_lifts_trms_pre (Aabsdata evstructheapid).
  hoare_lifts_trms_pre Aop.
  
  assert (Hg:  Get_struct v'28 x1 = None \/ exists t, Get_struct v'28 x1 = Some t).
  eapply get_struct_or.
  
  destruct Hg.
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 

  destruct H2 as (ev & Hget).
  destruct ev as (a& l ). destruct a as (a & t).
  assert (Ha: a = x1 ).
  clear - Hget.
  inductions v'28.
  simpl in Hget; tryfalse.
  unfold Get_struct in Hget.
  destruct a. destruct p. 
  destruct (os_inv.beq_addrval a x1) eqn: eq1.
  eapply option2val in Hget.
  inverts Hget; auto.
  fold Get_struct in Hget.
  apply IHv'28 in Hget.
  auto.
  subst a.

  assert (Ht: t = OS_Q_DATA \/ t <> OS_Q_DATA) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_pdata_validptr_err_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     eapply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_ok2. pure_auto. 
  eapply absinfer_eq.

  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_unfold_OS_Q_DATA; eauto. sep pauto.
  sep cancel AEvStructHeap.
  sep pauto. 
  instantiate (1:= l).
  rewrite Hteq in Hget.
  eauto.
  hoare_split_pure_all.
  simpljoin. 

  hoare_lifts_trms_pre Aop.
  destruct x1.
  hoare forward.
  unfold field_offset. 
  unfold field_offsetfld.
  simpl.
  eauto.
  
  eapply backward_rule1.
  intros.
  eapply AEvStructHeap_fold_OS_Q_DATA; eauto.
  exists l v'12 v'40.
  sep pauto.
  
  hoare forward prim.
  unfold EvtInv.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel p_local.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep pauto.
  pure_auto. pure_auto. pure_auto. pure_auto. pure_auto.
  
  assert((exists oseventtbl,v10 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b, i0) OSEventTbl mq_info_t) \/ ~(exists oseventtbl, v10 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b, i0) OSEventTbl mq_info_t)) by tauto.
  destruct H10.
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     apply absabort_rule. 
  }
  simpljoin1.
  eapply abscsq_rule. 
  apply noabs_oslinv.

  eapply mqgetinfo_absimp_query_memcpy_get_mq_info_oseventtbl; eauto.
  pure_auto.
  eapply absinfer_eq.
    
  assert((exists oseventtbl,v11 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b0, i1) OSEventTbl OS_Q_DATA) \/ ~(exists oseventtbl, v11 = Vptr oseventtbl /\ Some oseventtbl = id_addrval (b0, i1) OSEventTbl OS_Q_DATA)) by tauto.
  destruct H10.
  2:{
     eapply abscsq_rule. 
     apply noabs_oslinv.
     eapply mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl_abt; eauto.
     pure_auto.
     eapply absinfer_eq.
     apply absabort_rule. 
  
  }
  simpljoin1.
  eapply abscsq_rule. 
  apply noabs_oslinv.

  eapply mqgetinfo_absimp_query_memcpy_get_pdata_oseventtbl; eauto.
  pure_auto.
  eapply absinfer_eq.

  hoare forward.
  instantiate (2:= mqgetinfo_succ_ret (|nil|)).
  unfold spec_code_cons.
  unfold memcpy_spec.
  sep pauto.
  sep cancel p_local.
  inverts H12; inverts H13.
  sep pauto.
  pure_auto.

  sep pauto. instantiate (1:=init_lg). sep pauto.
  sep pauto. instantiate (1:=init_lg). sep pauto.

  hoare unfold.
  inverts H10.

  hoare_lifts_trms_pre (Aop).
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply mqgetinfo_absimp_succ_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  hoare forward.

  Unshelve.
  exact vhold_addr.
  exact 0%nat.
  exact 0%nat.
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact 0%nat.
  exact Tnull.
  exact (Vnull::nil).
  exact 0%nat.
  exact Tnull.
  exact (Vnull::nil).
  exact 0%nat.
  exact Tnull.
  exact (Vnull::nil).
  exact 0%nat.
  exact Tnull.
  exact (Vnull::nil).
  exact vhold_addr.
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact vhold_addr.
  exact vhold_addr.
  exact Tnull.
  exact (Vnull::nil).
  exact Tnull.
  exact (Vnull::nil).
  exact vhold_addr.
  exact vhold_addr.
Qed.