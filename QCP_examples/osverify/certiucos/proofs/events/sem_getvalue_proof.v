Require Import include_frm.
Require Import NPeano.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_inv.
Require Import abs_op.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import inv_prop. 
Require Import init_spec.

Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import Aarray_new_common. 
Require Import gjb_sem_common. 
Require Import gjb_common.
Require Import abs_infer_abt.
Require Import abs_infer_step.

Require Import os_sem_cap.
Require Import ifun_spec.
Require Import evheap_pure.
Require Import sem_getvalue_pure.
Require Import MapLib.
Require Import os_code_defs.
Require Import ev_aux_code.
Require Import pos_list_common.
Require Import OSTimeTickPure.
Require Import OSMutexPend_pure_ext.
Require Import OSQPendPure_ext.
Require Import OSQPostPure_ext.
Require Import Mbox_common.
Require Import sem_common.
Require Import seplog_trm_tacs.
Require Import protect.
Require Import sempend_pure_ext.
Require Import evauxvar_lemmas.
Require Import evaux_pure.

Require Import part_pos_rgn_spec.
Require Import part_pos_rgn_proof.
Require Import partinv_lemmas.

Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.

Lemma sem_getvalue_absimp_ok: 
  forall s1 s2 sch P, 
         can_change_aop P ->
         absinfer sch
           (<|| s1 ?? s2 ||> ** P)
           (<|| s1 ||>  ** P). 
Proof.
  intros.
  eapply absinfer_choice1.
  pure_auto. pure_auto.
  auto.
Qed.

Lemma sem_getvalue_absimp_ok2: 
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

Lemma sem_getvalue_absimp_sval_null_abt:
  forall sval s P sch,
   sval = Vnull ->
   can_change_aop P ->
   absinfer sch
      (<||  sem_getvalue_sval_null_abt (|sval :: nil|) ?? s ||> ** P)
      (<|| ABORT ||>  ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:= P).
  pure_auto. pure_auto.
  eapply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
Qed.


Lemma sem_getvalue_absimp_gethp_none_abt:
  forall mtp evhp s t l P sch,
   (Get_heap evhp mtp = None \/
   (Get_heap evhp mtp = Some (mtp, t, l) /\ t <> Tint32))->
   can_change_aop P ->
   absinfer sch
      (<|| sem_getvalue_gethpnone_abt (| Vptr mtp :: nil|) ?? s ||> ** 
              HEvAtomHeap evhp ** P)
      (<|| ABORT ||> ** 
          HEvAtomHeap evhp ** P). 
Proof.
  intros.
  assert (can_change_aop (HEvAtomHeap evhp ** P)).
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:= HEvAtomHeap evhp ** P).
  pure_auto. pure_auto.
  eapply absinfer_abt. pure_auto. pure_auto.
  absimp_abt_solver.
Qed.

Lemma sem_getvalue_absimp_set_sval:
  forall sval  evhp evhp'  P sch s,
   evhp' = Set_sval evhp sval (Vint32 Int.zero)->
   can_change_aop P ->
   absinfer sch
      (<|| sem_getvalue_set_sval (|(Vptr sval) ::nil|);;s ||> ** 
               HEvAtomHeap evhp ** P)
      (<|| s ||> ** 
           HEvAtomHeap evhp' ** P). 
Proof.
  intros.
  substs.
  infer_solver 0%nat. 
Qed.

Lemma sem_getvalue_absimp_semok_abt_null:
  forall sch posv P s,
    can_change_aop P ->
    posv <> Vint32 Int.mone -> 
    absinfer sch
      (<|| (sem_getvalue_semerr (|Vnull:: posv :: nil|)??
            sem_getvalue_sem_pos (| Vnull ::posv:: nil|));; s ||> ** P)  
      (<|| ABORT ||> ** P).
Proof.
  introv Hcop Hv.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  instantiate (1:=ABORT).
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  pure_auto.
  apply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver; eauto.
  eapply absinfer_seq_abt.
  pure_auto.
  pure_auto.
  pure_auto.
Qed.

Lemma sem_getvalue_absimp_semerr_abt:
  forall sch v posv P s,
    (cmpaddr Cle v userAddrStart = true \/ cmpaddr Clt userAddrEnd v = true) ->  
    posv <> Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| (sem_getvalue_semerr (|Vptr v:: posv :: nil|)??
            sem_getvalue_sem_pos (| Vptr v ::posv:: nil|));; s ||> ** P) 
      (<|| ABORT ||> ** P).
Proof.
  introv Hsemrgn Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  instantiate (1:=ABORT).
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  pure_auto.
  eapply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  eapply absinfer_seq_abt.
  pure_auto.
  pure_auto.
  pure_auto.
Qed.

Lemma sem_getvalue_absimp_semerr_cont: 
  forall sch vsem posv P s,
    (vsem = Vnull \/
     exists v'4, vsem = Vptr v'4 /\ 
                 (cmpaddr Cle v'4 userAddrStart = true \/
                  cmpaddr Clt userAddrEnd v'4 = true)) ->   
    posv = Vint32 Int.mone -> 
    can_change_aop P -> 
    absinfer sch 
      (<||(sem_getvalue_semerr (|vsem:: posv :: nil|)??
            sem_getvalue_sem_pos (| vsem ::posv:: nil|));; s ||>  ** P)
      (<|| s ||> ** P).
Proof.
  introv Hsemrgn Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  eapply absinfer_choice1.
  pure_auto. pure_auto. pure_auto.
  infer_solver 0%nat.
Qed.

Lemma sem_getvalue_absimp_sem_get_outtype_err_abt:
  forall sch v posv P s,
    cmpaddr Clt userAddrStart v = true ->
    cmpaddr Cle v userAddrEnd = true -> 
    ~(exists i, posv = Vint32 i) -> 
    can_change_aop P ->
    absinfer sch
     (<|| (sem_getvalue_semerr (|Vptr v:: posv :: nil|)??
            sem_getvalue_sem_pos (| Vptr v ::posv:: nil|));; s ||>  ** P)
     (<|| ABORT ||>  ** P). 
Proof.
  introv Hrgn1 Hrgn2 Htp Hcop. 
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P). pure_auto. 
  eapply absinfer_choice2; try pure_auto. 
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:=P). pure_auto. 
  eapply absinfer_abt; try pure_auto. 
  absimp_abt_solver.
  eapply absinfer_seq_abt; try pure_auto. 
  Unshelve.
  exact None. 
Qed. 

Lemma sem_getvalue_absimp_sem_get_none:
  forall sch posv v pbls P s, 
    cmpaddr Clt userAddrStart v = true ->
    cmpaddr Cle v userAddrEnd = true -> 
    get pbls v = None -> 
    can_change_aop P ->
    absinfer sch
     (<|| (sem_getvalue_semerr (|Vptr v:: posv :: nil|)??
            sem_getvalue_sem_pos (| Vptr v ::posv:: nil|));; s ||>  
      ** Hpbls pbls ** P) 
     (<|| ABORT ||>  ** Hpbls pbls ** P).
Proof.
  introv Hrgn1 Hrgn2 Hnone Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= Hpbls pbls ** P). pure_auto. 
  eapply absinfer_choice2.
  pure_auto. pure_auto.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq. 
  pure_auto.
  instantiate (1:= Hpbls pbls ** P). pure_auto.
  eapply absinfer_abt.
  pure_auto. pure_auto.
  absimp_abt_solver.
  right. 
  eexists; eauto. splits; eauto. 
  destruct H. simpljoin1. 
  simpl in H3. destruct H3.
  simpl in H2. subst x2.
  eapply join_sig_get; eauto. 
  pure_auto. 
  eapply absinfer_seq_abt; try pure_auto. 
Qed.

Lemma sem_getvalue_absimp_sem_get_pos_abt: 
  forall sch vsem pbls posv v P s, 
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true -> 
    get pbls vsem = Some posv ->
    v <> Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| (sem_getvalue_semerr (|Vptr vsem:: v :: nil|)??
            sem_getvalue_sem_pos (| Vptr vsem ::v:: nil|));; s ||> ** Hpbls pbls ** P)
     (<|| ABORT ||> ** Hpbls pbls ** P).
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver. 
  instantiate (1:= Hpbls pbls ** P). pure_auto.
  eapply absinfer_choice2.
  pure_auto.
  pure_auto.
  pure_auto.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto.
  instantiate (1:= Hpbls pbls ** P). pure_auto.
  eapply absinfer_abt.
  pure_auto.
  pure_auto.
  absimp_abt_solver.
  right. eexists; splits; eauto.
  pure_auto.
  destruct H. simpljoin1. 
  simpl in s1. destruct s1.
  simpl in j0. subst x2.
  eapply join_sig_get; eauto.
  left. eexists; splits; eauto.
  pure_auto. 
  eapply absinfer_seq_abt; pure_auto.
Qed.  

Lemma sem_getvalue_absimp_sem_get_pos_ok: 
  forall sch vsem pbls posv v P s, 
    cmpaddr Clt userAddrStart vsem = true ->
    cmpaddr Cle vsem userAddrEnd = true -> 
    get pbls vsem = Some posv ->
    v = Vint32 posv -> 
    can_change_aop P ->
   absinfer sch  
     (<|| (sem_getvalue_semerr (|Vptr vsem:: v :: nil|)??
            sem_getvalue_sem_pos (| Vptr vsem ::v:: nil|));; s ||> 
       ** Hpbls pbls ** P) 
     (<|| s ||> ** Hpbls pbls ** P). 
Proof.
  introv Hlt Hle Hposv Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_seq.
  pure_auto. 
  instantiate (1:= Hpbls pbls ** P). pure_auto.
  eapply absinfer_choice2; try pure_auto. 
  infer_solver 0%nat.  
  repeat eexists; eauto.
  right. exists pbls. 
  splits; eauto. 
  destruct H. simpljoin1. simpl in H3. simpl in H2.
  destruct H3. 
  subst x2.
  eapply join_sig_get; eauto.
  left. 
  eexists; splits; eauto.
Qed. 

Lemma sem_getvalue_absimp_poserr:
  forall posv P sch s,
    (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = Int.repr (OS_USER_MAX_EVENTS / 3)) ->
    can_change_aop P -> 
    absinfer sch 
      (<|| sem_getvalue_poserr (|Vint32 posv :: nil|) ?? s ||> ** P) 
      (<|| END (Some (Vint32 (Int.mone))) ||> ** P). 
Proof. 
  infer_solver 0%nat.
Qed.

Lemma sem_getvalue_absimp_posok_choice:
  forall posv P sch s,
    (Int.ltu posv Int.zero = false /\
       Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)) -> 
    can_change_aop P -> 
    absinfer sch 
      (<|| sem_getvalue_poserr (|Vint32 posv ::nil|) ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  introv Hrgn Hcaop.
  apply absinfer_choice2; can_change_aop_solver.
  pure_auto.
Qed. 

Lemma sem_getvalue_absimp_sval_cont: 
  forall sch vsem posv v0 P s,
    (vsem = Vnull \/
     exists v'4, vsem = Vptr v'4 /\ 
                 (cmpaddr Cle v'4 userAddrStart = true \/
                  cmpaddr Clt userAddrEnd v'4 = true)) ->   
    can_change_aop P -> 
    absinfer sch 
      (<|| sem_getvalue_svalerr (| vsem :: nil |)??
                 sem_getvalue_get_ecb_ptr (|posv :: v0 :: nil|) ;; s ||>  ** P)
      (<|| END (Some (Vint32 (Int.mone)))  ||> ** P).
Proof.
  introv Hsemrgn  Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P).
  pure_auto.
  pure_auto. 
  infer_solver 0%nat.
Qed.

Lemma sem_getvalue_absimp_before_abt_hold: 
  forall posv tp sc sembls sch v0 s P, 
    (Int.ltu posv Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) posv = false /\posv <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
    get sembls posv = Some (infohold, tp, sc) -> 
    can_change_aop P -> 
    absinfer sch 
      (<||
         sem_getvalue_get_ecb_ptr (|Vint32 posv :: v0 :: nil|) ;; s ||>  ** HSEMInfo sembls ** P) 
      (<|| ABORT ||>  ** HSEMInfo sembls ** P). 
Proof. 
  introv Hrgn Hsi Hcop.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  right. split; auto. left. split. intro. destruct H0. inv H0. intro Hf. inv Hf.
  Unshelve.
  exact None.
Qed.

Lemma sem_getvalue_absimp_before_abt_out: 
  forall i eo tp sc sembls v sch s P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get sembls i = Some (eo, tp, sc) -> 
         ((exists eid, eo = infotid eid /\ v <> Vptr eid) \/ eo = infonull /\ v <> Vnull) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
              sem_getvalue_get_ecb_ptr (|Vint32 i :: v :: nil|);; s ||>  ** HSEMInfo sembls ** P)
           (<|| ABORT ||>  ** HSEMInfo sembls ** P). 
Proof.
  intros.
  assert (Hc: can_change_aop (HSEMInfo sembls ** P)) by can_change_aop_solver.
  eapply absinfer_trans;
    try eapply absinfer_seq;
    try (eapply absinfer_seq_abt; try eauto);
    try eauto.
  eapply absinfer_abt; try eauto.
  absimp_abt_solver.
  Unshelve.
  exact None.
Qed.  

Lemma sem_getvalue_absimp_before_ok: 
  forall i eo tp sc sembls sch vv s P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         get sembls i = Some (eo, tp, sc) -> 
         (exists eid,  eo = infotid eid /\ vv = Vptr eid) \/ eo = infonull /\ vv = Vnull ->
         can_change_aop P -> 
         absinfer sch 
           (<|| sem_getvalue_get_ecb_ptr (|Vint32 i :: vv :: nil|);; s  ||>  ** HSEMInfo sembls ** P)
           (<|| s ||>  ** HSEMInfo sembls ** P). 
Proof.
  introv Hrgn Hsi Heo Hcop.   
  infer_solver 0%nat.  
  Unshelve. 
  exact None.
Qed. 

Lemma sem_getvalue_absimp_if_null_yes_end: 
  forall i v sch s P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         v = Vnull -> 
         can_change_aop P -> 
         absinfer sch 
           (<||
               sem_getvalue_if_null_yes (|v :: nil|) ??
                 (sem_getvalue_if_null_no (|v :: nil|);; 
                  s) ||>  **  P)
           (<||  END (Some (Vint32 Int.mone))  ||>  ** P). 
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1.
  pure_auto.
  instantiate (1:=P). pure_auto.
  pure_auto.
  infer_solver 0%nat.
Qed.  

Lemma sem_getvalue_absimp_if_null_no: 
  forall i v sch s P, 
         (Int.ltu i Int.zero = false /\ Int.ltu (Int.repr (OS_USER_MAX_EVENTS / 3)) i = false /\ i <> Int.repr (OS_USER_MAX_EVENTS / 3))  ->
         (exists eid, v =Vptr eid) -> 
         can_change_aop P -> 
         absinfer sch 
           (<||sem_getvalue_if_null_yes (|v :: nil|) ??
                 (sem_getvalue_if_null_no (|v :: nil|);; 
                  s) ||>  **  P)
           (<||s ||>  ** P). 
Proof.
  introv Hrgn Hv Hcop.
  eapply absinfer_trans.
  eapply absinfer_choice2.
  pure_auto.
  instantiate (1:=P). pure_auto. 
  pure_auto.
  infer_solver 0%nat.  
  destruct Hv. exists x.
  splits; eauto. 
  subst v. auto.
Qed. 

Lemma sem_getvalue_absimp_have_source_end:
  forall sval  evhp evhp'  P sch s1 s2 n els eid,
   evhp' = Set_sval evhp sval (Vint32 n)->
   can_change_aop P ->
   (exists wls, get els eid = Some (abssem n, wls)) -> 
   n <> Int.zero ->
   absinfer sch
      (<|| sem_getvalue_have_source(|Vptr  eid :: Vptr sval ::nil|) ?? s1 ?? s2 ||> ** HECBList els **
               HEvAtomHeap evhp ** P)
      (<|| END (Some (Vint32 (Int.zero))) ||> ** HECBList els **
           HEvAtomHeap evhp' ** P). 
Proof.
  intros.
  substs.
  infer_solver 0%nat.
Qed.

Lemma sem_getvalue_absimp_no_source_end:
  forall  P sch s1 s2 els eid wls tcbls,
   can_change_aop P ->
   get els eid = Some (abssem Int.zero, wls) -> 
   get_tls_blocked_num (TcbMod.lst tcbls) eid = 0%nat ->
   absinfer sch
      (<|| s1 ?? sem_getvalue_no_source(|Vptr  eid :: nil|) ?? s2 ||> **
               HECBList els ** HTCBList tcbls ** P)
      (<|| END (Some (Vint32 (Int.zero))) ||> ** HECBList els ** HTCBList tcbls ** P). 
Proof.
  infer_solver 1%nat.
Qed.

Lemma sem_getvalue_absimp_blocked_end:
  forall sval  evhp evhp'  P sch s1 s2 vsval els wls eid tcbls l vh,
    l = Vint32 vh ->
    evhp' = Set_sval evhp sval (Vint32 (Int_sub_n vsval vh Int.one))->
   can_change_aop P ->
    get els eid = Some (abssem Int.zero, wls) -> 
    Get_heap evhp sval = Some (sval, Tint32, l) ->
    vsval = get_tls_blocked_num (TcbMod.lst tcbls) eid ->
    Nat.lt 0%nat vsval ->
   absinfer sch
      (<|| s1 ?? s2 ?? sem_getvalue_blocked(|Vptr  eid :: Vptr sval ::nil|) ||> **
               HECBList els ** HTCBList tcbls **
               HEvAtomHeap evhp ** P)
      (<|| END (Some (Vint32 (Int.zero))) ||> ** HECBList els ** HTCBList tcbls **
           HEvAtomHeap evhp' ** P). 
Proof.
  intros.
  substs.
  infer_solver 2%nat.
Qed.

Lemma sem_getvalue_absimp_ok_choice:
  forall s1 P sch s,
    can_change_aop P -> 
    absinfer sch 
      (<|| s1 ?? s ||> ** P) 
      (<|| s ||> ** P). 
Proof.
  intros.
  apply absinfer_choice2; can_change_aop_solver.
  pure_auto.
Qed.


Open Scope code_scope.
Hint Resolve CltEnvMod.beq_refl: brel .

(* copy form OSMutex_common.v *)
Goal forall x y, Int.eq x y = true  -> x=y.
intros.
int auto.
apply unsigned_inj.
auto.
Save inteqeq.
(* end of copy *)

Lemma Sem_getvalueProof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api sem_getvalue
              (semgetvalue, (Tint32,  Tptr sem_t  :: Tptr Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api sem_getvalue
              (semgetvalue, (Tint32,  Tptr sem_t  :: Tptr Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sem_getvalue = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 8 (destruct v'; try apply absabort_rule).
  rename v into posv.
  rename v0 into rv_ptr.
  rename v1 into rv_ptr'.

  destruct H1 as [ Habt | (sval & Hok)]; subst x.
  (* x = Vnull *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_sval_null_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule.
  (* x = Vptr sval *)
  hoare forward prim.
  unfold EvtInv.
  hoare unfold.
  rename v'22 into vpthattr.
  rename v'23 into vcspace.
  rename v'24 into v22. 
  rename v'25 into v23. 
  rename v'26 into v24. 

  rename v'27 into v'22. 
  rename v'28 into v'23. 
  rename v'29 into v'24. 
  rename v'30 into v'25.
  rename v'31 into v'26.
  rename v'32 into v'27. 
  rename v'33 into v'28. 
  rename v'34 into v'29. 
  rename v'35 into v'30. 
  rename v'36 into v'31. 
  rename v'37 into v'32. 
  rename v'38 into v'33. 
  rename v'39 into v'34. 
  rename v'40 into v'35. 
  rename v'41 into v'36. 
  rename v'42 into v'37. 
  rename v'43 into v'38. 
  rename v'44 into v'39. 
  rename v'45 into v'40. 
  
  hoare_lifts_trms_pre (Aop, evatomheapid).
  rename v'28 into evatom.

  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_ok2; eauto.
  pure_auto.
  eapply absinfer_eq.
  destruct (Get_heap evatom sval) eqn: eq1.
  (* Get_heap evatom sval = None *)
  2: {
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. 
   }
   destruct p as ((p & t) & l).
   lets Heq: Get_heap_some_eq eq1.
   subst p.

  assert (Ht: t = Tint32 \/ t <> Tint32) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. }
  subst t.
  (*  Get_heap evatom sval = Some (sval, Tint32, l) *)
  eapply backward_rule1.
  intros.
  eapply AEvAtomHeap_unfold with (ident:= os_code_defs.sval); eauto. sep pauto.
  hoare unfold.
  hoare forward.
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Aop, evatomheapid).
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_set_sval; eauto.
  pure_auto.
  eapply absinfer_eq.

  change (V$ 0) with (Vint32 Int.zero).
  eapply backward_rule1. 
  intros.
  eapply AEvAtomHeap_fold with (ident:= os_code_defs.sval); eauto.
  exists (Vint32 Int.zero) v'18 v'28.
  sep pauto.

  lets Hset: Set_sval_eq eq1 H10.
  rewrite Hset.
   (*EXIT_CRITICAL*)
  hoare forward prim.
  unfold EvtInv.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep pauto.
  trycancel.
  sep cancel ASemEIBs.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  eauto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.

  clear -H2. rename H2 into Hptr_sem.
 (* x ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 sem ′·);ₛ *)
  hoare forward.
  pure_auto.
  pure_auto.
  simpl. destruct Hptr_sem as [ Hnull | (sem & Hok)]; subst; eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  sep destruct H. sep split in H. subst. intro Hf. inv Hf.
  sep destruct H. sep split in H. subst. intro Hf. inv Hf.
  pure_auto.
  
  intros.
  destruct H.
  destruct H; try (sep pauto; sep cancel p_local; sep pauto).

  intros.
  sep pauto. sep cancel p_local. sep pauto.

  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H.
  eauto.
  eapply disj_rule.

  hoare unfold.
  inverts H1.
  hoare_lifts_trms_pre Aop.
  assert (Hposv: posv = Vint32 (Int.mone) \/ posv <> Vint32 (Int.mone)) by tauto.
  destruct Hposv.  
  2: {
    destruct Hptr_sem as [ Hnull | (sem & Hptr)]; subst.
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply sem_getvalue_absimp_semok_abt_null;eauto.
    pure_auto.
    eapply absinfer_eq.
    apply absabort_rule.
    eapply abscsq_rule.
    eapply noabs_oslinv.
    eapply sem_getvalue_absimp_semerr_abt;eauto.
    inversion H; tryfalse.
    simpljoin. inverts H1. auto.
    pure_auto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  hoare abscsq.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_semerr_cont; eauto.
  inversion H.
  left. inverts H1; subst; auto.
  right.
  simpljoin. inverts H1; eauto.
  pure_auto.
  subst posv.

  hoare forward.
  hoare forward.

  change (Int.eq ($ 0) ($ 0)) with true.
  simpl val_inj.
  hoare_unfold. destruct H0; tryfalse.
  eapply hoare_disj_afalseP_r_pre.
  hoare unfold.
  clear -H.
  change (V$ -1) with (Vint32 Int.mone).

  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  Optimize Proof.
  Optimize Heap.
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

  hoare forward;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  rewrite Hdiveq.
  hoare unfold.
  remember (Int.mone) as posv.
  assert (Hposv_cond: Int.ltu posv Int.zero = true \/ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = $ (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    simpl in *; auto.
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    simpl in *; try (apply inteqeq in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in *).
    tryfalse.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_poserr; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  rewrite Hdiveq.
  change (Int.ltu Int.mone ($ 0)) with false.
  assert (Hmt: Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) Int.mone = true).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Hmt.
  assert (Hmf: Int.eq Int.mone ($ (OS_USER_MAX_EVENTS / 3)) = false).
  { clear -Hrgn3 Hrgn4. int auto. }
  rewrite Hmf.
  simpl val_inj.
  change (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero) with true.
  simpl.
  change ( Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true.
  simpl.
  hoare unfold.
  destruct H0; tryfalse.
  (* IF (x ′ ==ₑ ′ 0) false *)
  hoare unfold.
  inverts H1.
  (* second branch: encrit; pos = *sem; excrit *)
  assert (Hposv: ~(exists i, posv = Vint32 i) \/ exists i, posv = Vint32 i) by tauto.
  destruct Hposv as [Hex | Hex].
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  eapply noabs_oslinv. 
  eapply sem_getvalue_absimp_sem_get_outtype_err_abt; eauto. 
  pure_auto.
  eapply absinfer_eq. 
  apply absabort_rule.
  destruct Hex as (posv' & Hpv).
  subst. rename posv' into posv.
  hoare forward; try change (Int.eq ($ 1) ($ 0)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  hoare unfold.
  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold EvtInv.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  rename v'23 into vpthattr.
  rename v'24 into vcspace.
  rename v'25 into v22. 
  rename v'26 into v23. 
  rename v'27 into v24. 

  rename v'28 into v'23. 
  rename v'29 into v'24. 
  rename v'30 into v'25. 
  rename v'31 into v'26.
  rename v'32 into v'27.
  rename v'33 into v'28. 
  rename v'34 into v'29. 
  rename v'35 into v'30. 
  rename v'36 into v'31. 
  rename v'37 into v'32. 
  rename v'38 into v'33. 
  rename v'39 into v'34. 
  rename v'40 into v'35. 
  rename v'41 into v'36. 
  rename v'42 into v'37. 
  rename v'43 into v'38. 
  rename v'44 into v'39. 
  rename v'45 into v'40. 
  rename v'46 into v'41. 
  
  rename v'38 into pbls.
  hoare_lifts_trms_pre (Aop, pblsid).
  assert (Hor: get pbls x = None \/ (exists posv, get pbls x = Some posv)).
  {
    destruct (get pbls x).
    right. eexists. eauto. 
    left. auto.
  }
  destruct Hor as [Hnone | Hsome].
  (* get pbls smadr = None *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_sem_get_none; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
  (* exists posv, get pbls x = Some posv *)
  destruct Hsome as (pv & Hget).
  eapply backward_rule1.
  intros. 
  eapply pos_list_split_frm. 
  sep cancel APosblkList.
  eauto.
  eauto.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.pos).
  hoare forward.
  eapply assign_rule_lvar with (v2:=Vint32 pv). 
  split.
  intros.
  sep cancel (Alvarmapsto os_code_defs.pos).
  eauto.
  intro.
  auto.
  2: { instantiate (1:=long). eapply eq_int. auto. }
  2: { sep pauto. instantiate (1:=init_lg). sep cancel p_local. sep pauto. }
  unfold node.
  introv Hsat.
  sep normal in Hsat.
  destruct Hsat as (sem_blk & Hsat).
  ssplit_apure_in Hsat.
  destruct H0 as (Heq & Hmat).
  inverts Heq.
  unfold V_posblk_pos in *.
  apply nth_val_nth_val'_some_eq in H4.
  rewrite <- H4.
  eapply sem_rv; eauto.
  sep_get_rv.

  assert (Hposv: Vint32 posv <> Vint32 pv \/ Vint32 posv = Vint32 pv) by tauto.
  hoare_lifts_trms_pre (Aop, pblsid).
  destruct Hposv.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_sem_get_pos_abt; eauto. 
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.

  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_sem_get_pos_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  rewrite <- H0.
  hoare unfold.
  eapply backward_rule1. 
  introv Hsat.
  eapply pos_sllseg_merge
    with (vll1:=v'42) (hd:=v'38) (vsem:= x) (pbls1:=v'46) (vl:=v'44)
         (hd':=v'45) (vll2:=v'43) (pbls2:=v'48) (posv:=pv) (pbls':=v'47) (pbls:=pbls).
  sep pauto. 
  eauto.
  (* EXIT_CRITICAL *) 
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
  unfold APosblkList.
  sep pauto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  pure_auto.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.

  (* If (′ 0 >ₑ pos ′ ||ₑ pos ′ ≥ ebinop odiv ′ OS_USER_MAX_EVENTS ′ 3) *)
  lets Hrgn: usr_max_evts_rgn.
  destruct Hrgn as (Hrgn3 & Hrgn4).
  assert (Heqf: Int.eq ($ OS_USER_MAX_EVENTS) ($ Int.min_signed) = false).
  eapply int_min_neq_maxevents.
  lets Hrgn': usr_max_evts_rgn'.
  destruct Hrgn' as (Hrgn5 & Hrgn6).
  assert (Hsieq : (Int.signed ($ OS_USER_MAX_EVENTS) / Int.signed ($ 3)) = (OS_USER_MAX_EVENTS / 3)).
  clear -Hrgn5 Hrgn6.
  int auto.
  Optimize Proof.
  Optimize Heap.
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

  hoare forward;
  try (rewrite Hchg);
  simpl;
  pure_auto.
  rewrite Hdiveq.
  hoare unfold.
  assert (Hposv_cond: Int.ltu posv Int.zero = true \/ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = true \/ posv = $ (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    simpl in *; auto.
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    simpl in *; auto.
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    simpl in *; try (apply OSMutex_common.inteqeq in eq3; subst; auto).
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; simpl in *).
    tryfalse.
  }
  hoare abscsq.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_poserr; eauto.
  can_change_aop_solver.
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  assert (Hposv_range: Int.ltu posv Int.zero = false /\ Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv = false /\ posv <> Int.repr (OS_USER_MAX_EVENTS / 3)).
  {
    change ($ 0) with Int.zero in *.
    rewrite Hdiveq in *.
    destruct (Int.ltu posv Int.zero) eqn:eq1;
    destruct (Int.ltu ($ (OS_USER_MAX_EVENTS / 3)) posv) eqn: eq2;
    destruct (Int.eq posv ($ (OS_USER_MAX_EVENTS / 3))) eqn: eq3;
    try (apply inteqeq in eq3; subst);
    simpl in *; auto;
    repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
    try destruct H0;
    tryfalse.
    splits; try apply sem_lab.semacc_int_eq_false; auto.
  }
  clear H H0.

  eapply abscsq_rule. 
  eapply noabs_oslinv. 
  eapply sem_getvalue_absimp_posok_choice; eauto.
  can_change_aop_solver.
  apply absinfer_eq.
  (* y ′ =ᶠ UserAddrCheck (·〈 (long) ∗ 〉 os_code_defs.sval ′·);ₛ *)
  hoare forward.
  simpl. eauto. 
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat.
  sep destruct H. sep split in H. subst. intro Hf. inv Hf.
  sep destruct H. sep split in H. subst. intro Hf. inv Hf.

  intros.
  destruct H.
  destruct H; try (sep pauto; instantiate (1:=init_lg); sep pauto).

  intros.
  sep pauto. instantiate (1:=init_lg). sep pauto.
  
  hoare unfold.
  eapply backward_rule1.
  intros.
  apply disj_split in H4.
  eauto.
  eapply disj_rule.
  hoare unfold.
  inverts H6.
  hoare forward. 
  hoare_split_pure_all.
  (* encrit *)
  hoare forward prim. 
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  eapply noabs_oslinv. 
  eapply sem_getvalue_absimp_sval_cont.
  right. destruct H4. inverts H4. simpljoin.
  inverts H4. eauto.
  pure_auto.
  apply absinfer_eq. 
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  change (Int.eq ($ 0) ($ 0)) with true; simpl val_inj.
  hoare unfold.
  destruct H5; tryfalse.
  (* y = 1 *)
  hoare unfold.
  inverts H6.
  rename x into vsem.
  rename x0 into sval.
  hoare forward;
  try change (Int.eq ($ 1) ($ 0)) with false; simpl val_inj.
  hoare unfold. tryfalse.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule. 
  eapply noabs_oslinv. 
  eapply sem_getvalue_absimp_ok_choice.
  pure_auto.
  apply absinfer_eq. 
  rename H into Hpos_rgn1; rename H0 into Hpos_rgn2; rename H1 into Hpos_rgn3.
  lets Hpos_neq: Int.eq_false Hpos_rgn3.
  clear -Hpos_rgn1 Hpos_rgn2 Hpos_rgn3 Hpos_neq Hdiveq Hrgn3 Hrgn4.

  (* encrit *)
  hoare forward prim.
  hoare unfold.
  unfold EvtInv. 
  rename v'19 into vpthattr.  
  rename v'20 into vcspace. 
  rename v'21 into v19. 
  rename v'22 into v20. 
  rename v'23 into v21. 
  unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'38.

  (* new add *)
  hoare_assert_pure (length v'28 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto.  }
  unfold EvtInv.
  unfold ASemEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, ASeminfo).
  rename H1 into Hlen_info.
  eapply backward_rule1.
  introv Hsat.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel ASeminfo.
  eauto.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  rename H3 into HH3.
  rename H4 into HH4.
  rename H5 into H3.
  rename H6 into H4.
  rename H8 into H6.
  rename H10 into H8.
  rename H12 into H10.
  rename H7 into H5.
  rename H9 into H7.
  rename H11 into H9.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  rename H16 into H14.
  hoare normal pre.
  hoare_lifts_trms_pre (Aop).
  hoare forward.

  eapply assign_rule_lvar with (v2:=nth_val' 7%nat v'39).
  split; introv Hsat.
  sep_lift_context_in Hsat (Alvarmapsto p).
  eauto.
  sep_lift_context (Alvarmapsto p).
  auto.
  Optimize Proof.
  Optimize Heap.
  introv Hsat.
  sep_get_rv_array_struct.
  rewrite Hdiveq; eauto.
  rewrite Hdiveq; eauto.
  eapply new_array_type_vallist_match_split in H1; eauto.
  mytac.
  { apply eq_vptr. do 2 eexists; splits; auto. }
  { sep pauto. instantiate (1:=init_lg). sep cancel p_local. simpl; auto. }

  assert (Hlemu: Int.unsigned posv <= Int.max_unsigned).
  { clear -H Hrgn3 Hrgn4. int auto. }
  lets Hsls: semb_corr H2 H13 Hpos_rgn1 Hlemu.
  destruct Hsls as (eo & tp & sc & Hget & Hsls).
  rename v'39 into semvl.
  assert (Hcases: ((exists eid, eo = infotid eid /\ V_OSSINFOPevent semvl  = Some (Vptr eid) /\ eid <> vhold_addr) \/ eo = infonull /\ V_OSSINFOPevent semvl  = Some Vnull) \/ eo = infohold /\ V_OSSINFOPevent semvl  = Some (Vptr vhold_addr)).
  { clear -Hsls. intuition. }
  clear Hsls.

  hoare_lifts_trms_pre (Aop, seminfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    subst eo.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sem_getvalue_absimp_before_abt_hold; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  assert (Hveid: ((exists eid,  eo = infotid eid /\ rv_ptr = Vptr eid) \/ eo = infonull /\ rv_ptr = Vnull) \/ ((exists eid, eo = infotid eid /\ rv_ptr <> Vptr eid) \/ eo = infonull /\ rv_ptr <> Vnull)).
  {
    destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
    assert (Hv: rv_ptr = Vptr eid \/ rv_ptr <> Vptr eid) by tauto.
    destruct Hv; [left | right]; left; eauto.
    assert (Hv: rv_ptr = Vnull \/ rv_ptr <> Vnull) by tauto.
    destruct Hv; [left | right]; right; eauto.
   }
  destruct Hveid as [Hveid | Habt].
  2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply sem_getvalue_absimp_before_abt_out; eauto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* excrit *) 
  eapply backward_rule1. 
  intros.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'15 (Z.to_nat (Int.unsigned posv)) v'38.
  sep pauto.

  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel ASemCap.
  eauto.
  pure_auto.
  pure_auto.
  (* split the semvl as semvl = _ :: _ :: ... :: nil *)
  lets Hsem_vll: H1.
  rename H1 into Hsem_vl.
  eapply new_array_type_vallist_match_split in Hsem_vl; eauto.
  destruct Hsem_vl as (_ & _ & Hsem_vl).
  lets Hsem_vl_eq: struct_type_vallist_match_sem_info_t_vl Hsem_vl.
  lets Hvp_ptr: struct_type_vallist_match_sem_info_t_ptr Hsem_vl.
  destruct Hsem_vl_eq as (vtp & vname & vmax & vcur & vcnt & vlink & vblk & vp & vsc & Hsem_vl_eq).
  subst semvl.
  simpl nth_val' in *.
  unfold V_OSSINFOPevent in Hok.
  simpl nth_val in Hok.
  destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
  subst eo; inverts Hvp.
  (* p = NULL *)
  2: { destruct Hveid as [(ed & Hf & _) | (_ & Hveid)].
       clear -Hf; inverts Hf.
       subst rv_ptr.
       (* If (p ′ ==ₑ NULL){RETURN ′ -1};ₛ *)
       hoare forward.
       hoare unfold.
       hoare abscsq.
       apply noabs_oslinv.
       eapply sem_getvalue_absimp_if_null_yes_end; eauto.
       can_change_aop_solver.
       hoare forward.
       eapply hoare_disj_afalseP_l_pre.
       hoare unfold.
       destruct H1; tryfalse.
    }
  (* p == Vptr eid *)
  destruct Hveid as [(vp & Hed & Hveid) | (Hf & _)].
  2: { clear -Hf; inverts Hf. }
  inverts Hed; subst rv_ptr.
  destruct vp as (vp_b & vp_i).
  (*p = Vptr (vp_b, vp_i) *)
  hoare forward.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  eapply abscsq_rule.
  eapply noabs_oslinv. 
  eapply sem_getvalue_absimp_if_null_no; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* new code about part_pos_rgn *)
   hoare_lifts_trms_pre (Aop, os_code_defs.pos, temp_dom, temp_num, Aisr, Aie, Ais, Acs, Aier, p_local, A_dom_lenv).
  (*  fold init_lg. *)
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
   (* clear v'6 v'7; rename v'8 into v'6. *)
   (* end of new code *)

  clear -Hpos_rgn1 Hpos_rgn2 Hpos_rgn3 Hpos_neq Hlemu Hdiveq Hrgn3 Hrgn4.
  (* second get p: ENTER_CRITICAL;ₛ p ′ =ₑ efield (Sem_info ′ [pos ′]) pevent;ₛ EXIT_CRITICAL;ₛ*)
  hoare forward prim.
  hoare unfold.
  rename v'16 into vpthattr.
  rename v'17 into vcspace.
  rename v'18 into v18. 
  rename v'19 into v19. 
  rename v'20 into v20. 
  unfold EvtInv. unfold ASemEIBs.
  hoare normal pre.
  hoare_ex_intro.
  destruct v'35.
  rename b into v'36.
  rename i into v'37.
  hoare_assert_pure (length v'25 = (∘ (OS_USER_MAX_EVENTS / 3))).
  { get_hsat Hsat. sep_lifts_trms_in Hsat ASeminfo.  eapply aseminfo_len_frm; eauto. }
  unfold EvtInv.
  unfold ASemEIBs.
  hoare normal pre; hoare_ex_intro.
  hoare_lifts_trms_pre ( R_Q_Data_P ).
  eapply pure_split_rule'; introv Hrqdata.
  hoare unfold. 
  hoare_lifts_trms_pre (Aop, ASeminfo).
  rename H1 into Hlen_info.
  eapply backward_rule1.
  introv Hsat.
  eapply ASeminfo_unfold_any_idx_frm with (idx:=Z.to_nat (Int.unsigned posv)).
  sep cancel ASeminfo.
  eauto.
  rewrite Hlen_info.
  eapply ge_ne_lt_rgn; eauto.
  rewrite Hdiveq.
  apply Intlt_false_is_Zge; auto.
  rewrite Hdiveq; eauto.

  hoare unfold.
  rename H3 into HH3.
  rename H4 into HH4.
  rename H5 into H3.
  rename H6 into H4.
  rename H8 into H6.
  rename H10 into H8.
  rename H12 into H10.
  rename H7 into H5.
  rename H9 into H7.
  rename H11 into H9.
  rename H13 into H11.
  rename H15 into H13.
  rename H17 into H15.
  rename H16 into H14.
  hoare normal pre.
  hoare_lifts_trms_pre (Aop).
  rename v'38 into semvl.
  lets Hsls: semb_corr H2 H13 Hpos_rgn1 Hlemu.
  destruct Hsls as (eo & tp & sc & Hget & Hsls).
  assert (Hcases: ((exists eid, eo = infotid eid /\ V_OSSINFOPevent semvl  = Some (Vptr eid) /\ eid <> vhold_addr) \/ eo = infonull /\ V_OSSINFOPevent semvl  = Some Vnull) \/ eo = infohold /\ V_OSSINFOPevent semvl  = Some (Vptr vhold_addr)).
  { clear -Hsls. intuition. }
  clear Hsls.

  hoare_lifts_trms_pre (Aop, seminfoid).
  destruct Hcases as [ Hok | Habt ].
  2: {
    destruct Habt as (Habt1 & Habt2).
    subst eo.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sem_getvalue_absimp_before_abt_hold; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  rename rv_ptr' into rv_ptr.
  assert (Hveid: ((exists eid,  eo = infotid eid /\ rv_ptr = Vptr eid) \/ eo = infonull /\ rv_ptr = Vnull) \/ ((exists eid, eo = infotid eid /\ rv_ptr <> Vptr eid) \/ eo = infonull /\ rv_ptr <> Vnull)).
  {
   destruct Hok as [( eid & Heo & _) | (Heo & _)]; subst eo.
   assert (Hv: rv_ptr = Vptr eid \/ rv_ptr <> Vptr eid) by tauto.
   destruct Hv; [left | right]; left; eauto.
   assert (Hv: rv_ptr = Vnull \/ rv_ptr <> Vnull) by tauto.
   destruct Hv; [left | right]; right; eauto.
  }
  destruct Hveid as [Hveid | Habt].
  2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply sem_getvalue_absimp_before_abt_out; eauto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_before_ok; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare_lifts_trms_pre (Sem_info,Astruct, A_dom_lenv, Alvarmapsto os_code_defs.pos).
  hoare remember (1:: 2 :: 3 :: 4 :: nil)%nat pre.

  assert (Hget_rv: forall P, (GV Sem_info @ sem_info_t ∗ |-> Vptr (v'36, v'37) **
  Astruct
    (v'36,
    v'37 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
    sem_info_t semvl **
  A_dom_lenv
    ((os_code_defs.sval, (long) ∗)
     :: (sem, (long) ∗)
        :: (os_code_defs.pos, long)
           :: (x, char_t)
              :: (y, char_t) :: (p, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
  LV os_code_defs.pos @ long |-> Vint32 posv **
  P) ==> Rv efield (Sem_info ′ [os_code_defs.pos ′]) pevent @ (OS_EVENT∗) == (nth_val' 7%nat semvl)).
  { introv Hsat.
    sep_get_rv_array_struct.
    rewrite Hdiveq; eauto.
    rewrite Hdiveq; eauto.
    eapply new_array_type_vallist_match_split in H1; eauto.
    mytac.
  }

   (* split the semvl as semvl = _ :: _ :: ... :: nil *)
  lets Hsem_vll: H1.
  rename H1 into Hsem_vl.
  eapply new_array_type_vallist_match_split in Hsem_vl; eauto.
  destruct Hsem_vl as (_ & _ & Hsem_vl).
  lets Hsem_vl_eq: struct_type_vallist_match_sem_info_t_vl Hsem_vl.
  lets Hvp_ptr: struct_type_vallist_match_sem_info_t_ptr Hsem_vl.
  destruct Hsem_vl_eq as (vtp & vname & vmax & vcur & vcnt & vlink & vblk & vp & vsc & Hsem_vl_eq).
  subst semvl.
  simpl nth_val' in *.
  assert (Heq_rv: vp = rv_ptr).
  { clear -Hok Hveid.
     unfold V_OSSINFOPevent in Hok.
     simpl nth_val in Hok.
     destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
     subst eo; inverts Hvp;
     destruct Hveid as [(ed & Heq & Hrv) | (Heq & Hrv)];
     subst rv_ptr; inverts Heq;
     auto.
  Optimize Proof.
  Optimize Heap.
  }
  subst vp.

  hoare_lifts_trms_pre Aop. 
  hoare forward.
  eapply ift_rule''; eauto.
  introv Hsat.
  eapply bop_rv; eauto.
  sep get rv. 
  clear -Hvp_ptr. simpl. destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst; pure_auto.
  go.
  simpl bop_eval.
  hoare unfold.
  destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst;
  simpl in H1; tryfalse.

  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_if_null_yes_end; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.

  (* exit critical *)
  eapply backward_rule1. 
  intros.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'12 (Z.to_nat (Int.unsigned posv)) v'35.
  sep pauto.
  
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  unfold EvtInv.
  unfold ASemEIBs.
  sep pauto; eauto.
  trycancel.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel ASemCap.
  eauto.
  pure_auto.
  pure_auto.
  (* return -1 *)
  hoare forward.
  eapply hoare_disj_afalseP_l_pre.
  hoare unfold.
  destruct Hvp_ptr as [Heq | ((pb & pi) & Heq) ]; subst;
  simpl in H1; destruct H1; tryfalse.

  (*(efield (Sem_info ′ [pos ′]) pevent) = Vptr (pb, pi) *)
  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_if_null_no; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  destruct Hok as [(eid & Heo & Hvp & Heid_neq) | (Heo & Hvp)];
  subst eo; inverts Hvp.
  lets Hrsem: H3.
  unfold RH_ECBlk_EIBlk_Mux_P in H3.
  rename H3 into Heic.
  lets Hgete: Hget.
  eapply Heic in Hgete; eauto.
  destruct Hgete as (n & wls & Hgete).
  unfold AECBList.
  hoare unfold.
  lets Fget_ectr: ECBList_P_get_ectr_some Hgete H3.
  destruct Fget_ectr as (et & etbl & petbl & Fget_ectr).
  hoare_lifts_trms_pre evsllseg.
  eapply backward_rule1.
  introv Hsat.
  eapply get_ectr_decompose in Hsat; eauto.
  hoare unfold.
  hoare_assert_pure (length v'39 = length v'41).
  {  sep_lifts_trms_in H1 (evsllseg v'25). 
      eapply evsllseg_list_len_eq in H1; auto.
  }
  hoare_split_pure_all. rename H1 into Hlen.
  lets Hels: H3.
  eapply ecblist_p_decompose_new in Hels; eauto.
  destruct Hels as (els1 & els2 & Hels1 & Hels2 & Hej & Hlast_ptr).
  lets Hcp: Hels2.
  simpl in Hcp.
  destruct Hcp as (eid & Hed_eq & Hretbl & Hrpetbl & (ed & els' & eptr & Heptr_eq & Hejs & Hred & Hels2')).
  inverts Hed_eq.
  unfold V_OSEventListPtr in Heptr_eq; simpl in Heptr_eq. inverts Heptr_eq.
  lets Hgete': EcbMod.join_sig_get Hejs.
  eapply EcbMod.join_get_r in  Hgete'; eauto.
  unfold get in Hgete; unfold EcbMap in Hgete.
  rewrite Hgete in Hgete'. inverts Hgete'.
  destruct v'43; lets Hred': Hred; simpl in Hred'; tryfalse.
  destruct Hred' as (Hmatch & Hrecb).
  hoare_assert_pure (i1 = (Int.repr OS_EVENT_TYPE_SEM) /\ i3 = i2).
  {
    unfold AEventData in H1.
    sep split in H1. inverts H16. inverts H19. auto.
  }
  apply pure_split_rule'; introv Hed_eq.
  destruct Hed_eq as (Heq1 & Heq2); subst i1; subst i3.
  subst i2.

  (* If ((efield (Sem_info ′ [pos ′]) pevent) → OSEventCnt >ₑ ′ 0) *)
  hoare forward.
  hoare_lifts_trms_pre (Sem_info,vname, A_dom_lenv, Alvarmapsto os_code_defs.pos).
  eapply ift_rule''; eauto.
  introv Hsat.
  eapply bop_rv; eauto.
  sep get rv.
  eapply struct_member_e_rv'' with (n:= 2%nat ) ; eauto.
  sep cancel (Astruct (v'48, Int.zero)).
  eauto.
  unfold OS_EVENT; eauto.
  simpl; eauto.
  unfold ftype; simpl; eauto.
  simpl; eauto.
  simpl; eauto.
  unfold id_nth; simpl; eauto.
  simpl; eauto.
  simpl; eauto. pure_auto.
  simpl.
  pure_auto.
  simpl; eauto.
  change ($ 0) with Int.zero.
  simpl bop_eval.
  hoare unfold.
  destruct (Int.ltu Int.zero n) eqn: eq1;
  simpl val_inj in H1; tryfalse.
  hoare_lifts_trms_pre (Aop, evatomheapid).
  rename v'22 into evatom.
  destruct (Get_heap evatom sval) eqn: eq2.
  (* Get_heap evatom sval = None *)
  2: {
      eapply abscsq_rule. 
      apply noabs_oslinv.
      eapply sem_getvalue_absimp_gethp_none_abt; eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  destruct p as ((p & t) & l).
  lets Heq: Get_heap_some_eq eq2.
  subst p.

  assert (Ht: t = Tint32 \/ t <> Tint32) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. }
  subst t.
  instantiate (1:= Afalse).
  (*  Get_heap evatom sval = Some (sval, Tint32, l) *)
  eapply backward_rule1.
  intros.
  eapply AEvAtomHeap_unfold with (ident:= os_code_defs.sval); eauto. sep pauto.
  hoare unfold.
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_deref_ptr; eauto.
  intros. sep get rv.
  split; introv Hsat.
  sep pauto.
  sep pauto.
  introv Hsat.
  sep_lifts_trms_in Hsat (Sem_info,vname, A_dom_lenv, Alvarmapsto os_code_defs.pos).
  eapply struct_member_e_rv''  with (n:= 2%nat ) ; eauto.
  sep cancel (Astruct (v'48, Int.zero)).
  eauto.
  unfold OS_EVENT; eauto.
  simpl; eauto.
  unfold ftype; simpl; eauto.
  simpl; eauto.
  simpl; eauto.
  simpl; eauto.
  unfold id_nth; simpl; eauto.
  simpl; eauto.
  pure_auto.
  eapply eq_int.
  split; eauto.
  intros.
  eexists. sep cancel p_local. simpl; auto.

  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.

  lets Hlt: ltu_eq_false eq1.
  eapply semacc_int_eq_false in Hlt.
  hoare_lifts_trms_pre (Aop, absecblsid, evatomheapid).
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_have_source_end; eauto.
  pure_auto.
  eapply absinfer_eq.

  eapply backward_rule1. 
  intros.
  eapply AEvAtomHeap_fold with (ident:= os_code_defs.sval); eauto.
  exists (Vint32 n) v'18 v'21.
  sep pauto.

  lets Hset: Set_sval_eq eq2 H37.
  rewrite Hset.
  (*EXIT_CRITICAL*)
  eapply backward_rule1. 
  intros.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'12 (Z.to_nat (Int.unsigned posv)) v'35.
  sep pauto.

  hoare forward prim.
  unfold EvtInv.
  unfold ASemEIBs.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep pauto; eauto.
  trycancel.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel Aier.
  unfold AECBList.
  sep normal.
  sep eexists.
  sep split; eauto.
  sep cancel OSEventList.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel (evsllseg v'25).
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  eauto.
  split; auto. go.
  unfolds; simpl; eauto.
  pure_auto.
  pure_auto.
  (* return *)
  hoare forward.
  (* n = 0 *)
  eapply hoare_disj_afalseP_l_pre.
  change ($ 0) with Int.zero.
  simpl bop_eval.
  hoare unfold.
  destruct (Int.ltu Int.zero n) eqn: eq1;
  simpl in H1; destruct H1; tryfalse.
  eapply ltu_zero_false_imp_eq_zero in eq1; subst n.

  hoare_lifts_trms_pre (Aop, evatomheapid).
  rename v'22 into evatom.
  destruct (Get_heap evatom sval) eqn: eq2.
  (* Get_heap evatom sval = None *)
  2: {
      eapply abscsq_rule. 
      apply noabs_oslinv.
      eapply sem_getvalue_absimp_gethp_none_abt; eauto.
      pure_auto.
      eapply absinfer_eq.
      apply absabort_rule.
  }
  destruct p as ((p & t) & l).
  lets Heq: Get_heap_some_eq eq2.
  subst p.

  assert (Ht: t = Tint32 \/ t <> Tint32) by tauto.
  destruct Ht as [Hteq | Htneq].
  2:{
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_gethp_none_abt; eauto.
  pure_auto.
  eapply absinfer_eq.
  apply absabort_rule. }
  subst t.

  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sem_getvalue_absimp_ok2.
  pure_auto.
  eapply absinfer_eq.

  (*  eq2: Get_heap evatom sval = Some (sval, Tint32, l) *)
  hoare_assert_pure (rule_type_val_match long l = true).
  { rename H38 into Hsat.
    sep_lifts_trms_in Hsat (AEvAtomHeap, Alvarmapsto os_code_defs.sval).
    eapply AEvAtomHeap_unfold with (ident:= os_code_defs.sval) in Hsat; eauto.
    sep destruct Hsat.
    sep pauto.
  }
  eapply pure_split_rule'; introv Hsval_mat. (* new add *)
  simpl in Hsval_mat. destruct l; tryfalse.
  rename i1 into l.

  (*  eq2: Get_heap evatom sval = Some (sval, Tint32, Vint32 Int.zero) *)
  (* fold AECBList *)
  eapply backward_rule1.
  introv Hsat.
  eapply AECBList_fold with (p:= v'25); eauto.
  eapply lzh_evsllseg_compose; eauto.
  sep cancel (evsllseg v'25).
  sep cancel evsllseg.
  unfold AEventNode.
  unfold AOSEvent.
  unfold node.
  unfold AOSEventTbl.
  sep pauto; eauto.
  2: { split; auto. struct_type_match_solver. }
  sep cancel (Astruct (v'48, Int.zero)).
  sep cancel Aarray.
  sep cancel AOSPostEventTbl.
  eauto.
  unfolds; simpl ; auto.
  (* compose tcbdllseg *)
  eapply backward_rule1.
  introv Hsat.
  eapply tcbdllseg_compose' with (h:= v'0).
  sep cancel (tcbdllseg v'0).
  sep cancel tcbdllseg.
  eauto.
  (* compose TCBList_P *)
   hoare_split_pure_all. rename H38 into Htls_last_case.
  rename H36 into Htls_left; rename H37 into Htls_right.
  rename H19 into Htj; rename H16 into Hhead_neq.
  assert (Htls_whole: TCBList_P v'0 (v'2 ++ v'3 :: v'5) v'6 v'9 ).
 { destruct Htls_last_case as [ (Hnil & Heq) | (vl & Hnnil & Hlast & Heq)];
    subst.  simpl in Htls_left. subst.
    eapply join_emp_eq in Htj; subst.
    rewrite nil_simp. auto.
    eapply TCBList_P_combine; eauto.
  }
  hoare_assert_pure ( isptr v'0).
  {  unfold tcbdllseg in *.
     eapply dllseg_head_isptr with (s:= s0); eauto.
  }
  eapply pure_split_rule'; introv Hptr_ptcb.
    (* ptcb ′ =ₑ OSTCBList ′;ₛ *)
  hoare forward.
  pure_auto.

  destruct Hptr_ptcb as [Hf | (tls_head & Htls_head)]; subst v'0; tryfalse.
  hoare_assert_pure (array_type_vallist_match Int8u v'6 /\ 
                                           length v'6 = ∘ OS_RDY_TBL_SIZE).
   { rename H16 into Hsat.
      unfold AOSRdyTblGrp in Hsat.
      unfold AOSRdyTbl in Hsat.
      sep normal in Hsat.
      sep split in Hsat.
      mytac.
   }
    eapply pure_split_rule'; introv Hrtbl.
    destruct Hrtbl as (Hrtbl_mat & Hrtbl_len).
  (*WHILE (ptcb ′) *)

  (*1: remember irrelevant sep-conjunctions*)
  hoare_lifts_trms_pre (Sem_info, vname, A_dom_lenv, Alvarmapsto os_code_defs.pos, Aop, p_local, tcbdllseg, OSTCBList, OSTCBCur, Alvarmapsto ptcb, Alvarmapsto os_code_defs.sval, evatomheapid, AEvAtomHeap).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: 11 :: 12 :: 13 :: nil)%nat pre.
  protect HeqH16.
  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated *)
  eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX evatom' vsval vptcb vl1 vl2 tls1 tls2 ptcb_addr,
      GV Sem_info @ sem_info_t ∗ |-> Vptr (v'36, v'37) **
      Astruct
        (v'36,
            v'37 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
        sem_info_t
      (vtp
     :: vname
        :: vmax
           :: vcur :: vcnt :: vlink :: vblk :: Vptr (v'48, Int.zero) :: vsc :: nil) **
    A_dom_lenv
    ((os_code_defs.sval, (long) ∗)
     :: (sem, (long) ∗)
        :: (os_code_defs.pos, long)
           :: (x, char_t)
              :: (y, char_t) :: (p, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (temp_dom, char_t) :: (temp_num, char_t):: nil) **
     LV os_code_defs.pos @ long |-> Vint32 posv **
      <||
       sem_getvalue_have_source (|Vptr (v'48, Int.zero) :: Vptr sval :: nil|)
     ?? sem_getvalue_no_source (|Vptr (v'48, Int.zero) :: nil|)
        ?? sem_getvalue_blocked
           (|Vptr (v'48, Int.zero) :: Vptr sval :: nil|) ||>  **
      p_local OSLInv tid
    (logic_val (V$ 1)
     :: logic_val (V$ __EvLoc_normal)
        :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
     tcbdllseg (Vptr tls_head) Vnull v'21 Vnull (v'2 ++ v'3 :: v'5) **
      [| (vptcb = Vptr ptcb_addr /\    (* in the loop *)
          join tls1 tls2 v'9 /\
         TCBList_P (Vptr tls_head) vl1 v'6 tls1 /\
         TCBList_P vptcb vl2 v'6 tls2 /\ vl2 <> nil /\
          (vl1 = nil /\ Vptr ptcb_addr = Vptr tls_head \/
                 (exists vl,
                  vl1 <> nil /\
                  last vl1 nil = vl /\ nth_val 0 vl = Some (Vptr ptcb_addr))))
         \/ ( vptcb = Vnull /\                     (* out of loop *)
                  vl1 = (v'2 ++ v'3 :: v'5) /\ vl2 = nil /\
                  tls1 = v'9 /\ tls2 = TcbMod.emp /\
                  TCBList_P (Vptr tls_head) (v'2 ++ v'3 :: v'5) v'6 v'9) |] **
      [| vl1 ++ vl2 = (v'2 ++ v'3 :: v'5) |] **
      GV OSTCBList @ OS_TCB ∗ |-> (Vptr tls_head) **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
      LV ptcb @ OS_TCB ∗ |-> vptcb **
      LV os_code_defs.sval @ (long) ∗ |-> Vptr sval **
      [|  vsval = get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero) |] **
      [| ( (0 < vsval)%nat /\ evatom' = Set_sval evatom sval (Vint32 (Int_sub_n vsval  l Int.one))) \/
          ( (vsval = 0)%nat /\ evatom' = evatom ) |] **
     HEvAtomHeap evatom **
     AEvAtomHeap evatom' ** H16)).
  introv Hsat.
  exists evatom (0%nat) (Vptr tls_head) (nil: list vallist) ( v'2 ++ v'3 :: v'5).
  exists (TcbMod.emp) v'9 tls_head.
  sep pauto.
  left.
  splits; auto.
  apply old.Unnamed_thm.
  simpl; auto.
  clear. introv Hf. rewrite <- length_zero_iff_nil in Hf.
  rewrite app_length in Hf. simpl in Hf.
   auto with zarith.

  (*3: apply the 'seq_rule' to get the while statement off the remaining statements, then apply the 'while_rule' *)
  eapply seq_rule.

  (*4: prove the condition expression of while is legal *)
  eapply while_rule with (tp := OS_TCB ∗).
  introv Hsat. sep destruct Hsat. eexists. sep get rv.
  sep split in Hsat.
  destruct H19 as [ (Heq_ptcb & _) | (Heq_ptcb & _)];
  subst; simpl; auto.
  (* Aistrue ptcb ′ *)
  (*5: the cond-expr of while hold implies the part of the loop-inv*)
  hoare normal pre.
  apply ex_intro_rule; intro evatom'.
  apply ex_intro_rule; intro vsval.
  apply ex_intro_rule; intro vptcb.
  apply ex_intro_rule; intro vl1.
  apply ex_intro_rule; intro vl2.
  apply ex_intro_rule; intro tls1.
  apply ex_intro_rule; intro tls2.
  apply ex_intro_rule; intro ptcb_addr.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar; eauto.
  introv Hsat. sep get rv.
  sep split in Hsat.
  destruct H19 as [ (Heq_ptcb & _) | (Heq_ptcb & _)];
  subst; simpl; auto.
  hoare_split_pure_all.
  destruct H41 as (_ & Histrue & _).
  destruct H19 as [ (Heq_ptcb & Htj' & Htls_left' & Htls_right' & Hvl2_nnil & Htls_last_case') | (Heq_ptcb & Hvl1_eq & Hvl2_eq & Htls1_eq & Htls2_eq & Htls_whole')];
  subst vptcb; tryfalse.
  (* ptcb = Vptr ptcb_addr *)
  rename H36 into Htls_eq_alt; rename H38 into Hblk_cases.
  (* split tcbdllseg *)
  assert (Hvl2_alt: exists vl vl2', vl2 = vl :: vl2').
  { clear - Hvl2_nnil. destruct vl2; eauto. tryfalse. }
  destruct Hvl2_alt as (vl & vl2' & Hvl2_eq); subst vl2; rename vl2' into vl2.
  rewrite <- Htls_eq_alt.
  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat (tcbdllseg).
  eapply tcbdllseg_split in Hsat; eauto.
  hoare unfold.
  rename H19 into Htls_last_case''.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  hoare unfold.
  assert (Hptcb_eq: (v'45, Int.zero) = ptcb_addr).
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
  assert (Hget_sval: exists vsval', Get_heap evatom' sval = Some (sval, long, vsval') /\ (((get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero) = 0)%nat /\ vsval' = Vint32 l)
 \/ ((0 < get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero))%nat /\ vsval' = (Vint32 (Int_sub_n (get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero)) l Int.one))))).
  { clear -eq2 Hblk_cases.
    destruct Hblk_cases as [ (Hblk_lt & Hevatom) | (Hblk_eq & Hevatom)];
    subst evatom'; eauto.
    eexists.
    splits. eapply Get_Set_sval_eq; eauto.
    auto.
  }
  destruct Hget_sval as ( vsval' & Hget_sval' & Hsval'_eq).
  eapply backward_rule1.
  intros.
  eapply AEvAtomHeap_unfold with (evhpe := evatom') (ident:= os_code_defs.sval); eauto.
  sep cancel AEvAtomHeap.
  sep cancel (Alvarmapsto os_code_defs.sval).
  eauto.
  hoare normal pre.
  apply ex_intro_rule; intro v'1.
  apply ex_intro_rule; intro v'49.
  hoare_split_pure_all.
  subst evatom'.
  simpl in H36. destruct vsval'; tryfalse. rename i8 into vsval. clear H36.
  rename H19 into Hget_sval_none.
  (* If (ptcb ′ → OSTCBEventPtr ==ₑ efield (Sem_info ′ [pos ′]) pevent) *)
  hoare forward.
  hoare_lifts_trms_pre (Sem_info,vname, A_dom_lenv, Alvarmapsto os_code_defs.pos).
  eapply ift_rule''; eauto.
  introv Hsat.
  eapply bop_rv; eauto.
  sep get rv.
  go.
  simpl. clear -H43. destruct H43 as [Heq | ((pb & pi) & Heq) ]; subst; simpl; pure_auto.
  simpl; eauto.
  simpl bop_eval.
  hoare unfold.
  destruct H43 as [Heq | ((pb & pi) & Heq) ]; subst; simpl in H1; tryfalse.
  destruct (Int.eq pi Int.zero) eqn: ifeq2;
  destruct (peq pb v'48) eqn: ifeq1; simpl in H1; tryfalse.
  eapply semacc_int_eq_true in ifeq2; subst pi; subst pb.
  (* −− ∗os_code_defs.sval ′ *)
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_deref_ptr; eauto.
  intros. sep get rv.
  split; introv Hsat.
  sep pauto.
  sep pauto.
  intros.
  sep get rv.
  eapply eq_int.
  split; eauto.
  intros.
  eexists. sep cancel p_local. simpl; auto.
  (* rename i8 into vsval. *)
  (* ptcb ′ =ₑ ptcb ′ → OSTCBNext *)
  simpl bop_eval.
  eapply backward_rule1 with (p:= (
       <||
       sem_getvalue_have_source (|Vptr (v'48, Int.zero) :: Vptr sval :: nil|)
      ?? sem_getvalue_no_source (|Vptr (v'48, Int.zero) :: nil|)
         ?? sem_getvalue_blocked (|Vptr (v'48, Int.zero) :: Vptr sval :: nil|) ||>  **
   PV sval @ long |-> (if val_eq' x10 (Vptr (v'48, Int.zero))
                                                then Vint32 (vsval -ᵢ $ 1) else Vint32 vsval) **
   GV Sem_info @ sem_info_t ∗ |-> Vptr (v'36, v'37) **
   Astruct
     (v'36,
     v'37 +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned posv) * typelen sem_info_t))
     sem_info_t
     (vtp :: vname :: vmax :: vcur :: vcnt :: vlink :: vblk :: Vptr (v'48, Int.zero) :: vsc :: nil) **
   A_dom_lenv
     ((os_code_defs.sval, (long) ∗)
      :: (sem, (long) ∗)
         :: (os_code_defs.pos, long)
            :: (x, char_t)
               :: (y, char_t) :: (p, OS_EVENT ∗) :: (ptcb, OS_TCB ∗) :: (temp_dom, char_t) :: (temp_num, char_t) :: nil) **
   LV os_code_defs.pos @ long |-> Vint32 posv **
   LV os_code_defs.sval @ (long) ∗ |-> Vptr sval **
   AEvAtomHeap v'1 **
   AEvAtomHeap v'49 **
   Astruct ptcb_addr OS_TCB_flag
     (v'22
      :: v'0
         :: x10
            :: x9
               :: Vint32 i7
                  :: Vint32 i6
                     :: Vint32 i5
                        :: Vint32 i4
                           :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil) **
   dllseg v'22 (Vptr ptcb_addr) v'21 Vnull vl2 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   dllseg (Vptr tls_head) Vnull v'0 (Vptr ptcb_addr) vl1 OS_TCB_flag
     (fun vl : vallist => nth_val 1 vl) (fun vl : vallist => nth_val 0 vl) **
   p_local OSLInv tid
     (logic_val (V$ 1)
      :: logic_val (V$ inferules.__EvLoc_normal)
         :: logic_val Vnull :: logic_val Vnull :: logic_val Vnull :: nil) **
   GV OSTCBList @ OS_TCB ∗ |-> Vptr tls_head **
   GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr tid **
   LV ptcb @ OS_TCB ∗ |-> Vptr ptcb_addr **
   HEvAtomHeap evatom ** H16)).
  introv Hsat.
  destruct Hsat as [Hsat | Hsat].
  (* x10 = Vptr (v'47, Int.zero) *)
  clear -Hsat H43.
  sep split in Hsat. destruct H as (H & _).
  destruct H43 as [Heq | ((pb & pi) & Heq) ]; subst; simpl in H; tryfalse.
  simpl val_eq'.
  destruct (Int.eq pi Int.zero) eqn: ifeq2;
  destruct (peq pb v'48) eqn: ifeq1; simpl in H; tryfalse.
  eapply semacc_int_eq_true in ifeq2; subst pi; subst pb.
  change (left eq_refl && true) with true.
  sep auto.
  (* x10 <> Vptr (v'47, Int.zero) *)
  clear -Hsat H43.
  sep split in Hsat.
  destruct H43 as [Heq | ((pb & pi) & Heq) ]; subst; simpl in H;
  destruct H; tryfalse;
  simpl val_eq';  try (destruct (Int.eq pi Int.zero) eqn: ifeq2;
  destruct (peq pb v'48) eqn: ifeq1; simpl in H; tryfalse);
  try rewrite andb_false_r; try  change (right n && true) with false;
  sep auto.
  (* compose AEvAtomHeap*)
  eapply backward_rule1.
  introv Hsat.
  eapply AEvAtomHeap_fold with (ident:= os_code_defs.sval); eauto.
  eexists. exists v'1 v'49.
  sep pauto.
  destruct (val_eq' x10 (Vptr (v'48, Int.zero))); simpl; auto.
  (* actrual assign ptcb *)
  eapply conseq_rule.
  eauto.
  2: { hoare forward. go. }
  introv Hsat.
  subst ptcb_addr.
  lets Hcp: Htls_right'.
  simpl in Hcp.
  simpljoin.
  inverts H1.
  inverts H19.
  rename H36 into Htj_sig; rename H52 into Hptcb_node; rename H53 into Hptcb_right.
  (* process abstcb state relation *)
  assert (Hget_ptcb: exists st sus', TcbMod.get tls2 (v'45, Int.zero) = Some (i5, st, x9, sus')).
  { eapply TCBListP_head_in_tcb'; eauto. }
  destruct Hget_ptcb as (st & sus' & Hget_ptcb).
  lets Hget_ptcb': Hget_ptcb.
  eapply TcbMod.join_get_r in Hget_ptcb'; eauto.
  lets Hcp: Htj_sig. unfold join,sig in Hcp; unfold TcbMap in Hcp.
  eapply TcbMod.join_sig_get in Hcp.
  destruct x5 as (((prio & tcb_st) & msg) & sus).
  rewrite Hget_ptcb in Hcp; inverts Hcp.

  assert (Hst_case: (val_eq' x10 (Vptr (v'48, Int.zero)) = true -> (exists wt, tcb_st = wait (os_stat_sem (v'48, Int.zero)) wt)) /\ (val_eq' x10 (Vptr (v'48, Int.zero)) = 
    false -> ~(exists wt, tcb_st = wait (os_stat_sem (v'48, Int.zero)) wt))).
  { clear -H Hgete Htls_right' Htj_sig Hptcb_node Hget_ptcb' Hget_ptcb.
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
        introv Hf; destruct Hf as (wt & Hf); tryfalse.
        (*  tcb_st = wait os_stat_time i1 *)
        destruct t.
        Focus 4.
        eapply get_tcb_stat_rdy_sus in Hget_ptcb; eauto.
        destruct Hget_ptcb as (Hst & Heptr); invert Heptr.
        simpl val_eq'.
        split; introv Hcond; tryfalse.
        introv Hf; destruct Hf as (wt & Hf); inverts Hf.
        (*  tcb_st = wait (os_stat_sem e) i1 *)
        lets Hcp: Hget_ptcb.
        destruct o; subst.
        (* case : o = None *)
        2:{ eapply get_tcb_stat_sem_none_sus in Hget_ptcb; eauto.
            destruct Hget_ptcb as (Hst & Heptr  & Hdly & Hnintbl ); inverts Heptr; inverts Hdly;
            destruct e as (pb & pi).
            simpl val_eq'.
            destruct (peq pb v'48) eqn: eq_b;
            destruct (Int.eq pi Int.zero) eqn: eq_i;
            try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
            try rewrite andb_true_r; try rewrite andb_false_r;
            split; introv Hcond; tryfalse; eauto;
            introv Hf; destruct Hf as (wt & Hf); inverts Hf;
            try rewrite Int.eq_true in eq_i; tryfalse.
        }
        (* case : o = Some ts *)
        rename i into ts.
        assert (Hts: ts = Int.zero \/ ts <> Int.zero ) by tauto.
        destruct Hts as [Hzero | Hnz].
        (* ts = Int.zero *)
        destruct sus; subst.
        (* sus = true *)
        eapply get_tcb_stat_sem_zero_sus in Hget_ptcb; eauto.
        destruct Hget_ptcb as (Hst & Heptr  & Hdly & Hnintbl ); inverts Heptr; inverts Hdly;
        destruct e as (pb & pi).
        simpl val_eq'.
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; tryfalse; eauto;
        introv Hf; destruct Hf as (wt & Hf); inverts Hf;
        try rewrite Int.eq_true in eq_i; tryfalse.
        (* sus = false *)
        eapply get_tcb_stat_sem_zero in Hget_ptcb; eauto.
        destruct Hget_ptcb as (Hst & Heptr  & Hdly & Hnintbl ); inverts Heptr; inverts Hdly;
        destruct e as (pb & pi).
        simpl val_eq'.
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; tryfalse; eauto;
        introv Hf; destruct Hf as (wt & Hf); inverts Hf;
        try rewrite Int.eq_true in eq_i; tryfalse.
        (* ts <> Int.zero  *)
        eapply get_tcb_stat_sem_sus in Hget_ptcb; eauto.
        destruct Hget_ptcb as (Hst & Heptr  & Hdly & Hnintbl ); inverts Heptr; (* inverts Hdly; *)
        destruct e as (pb & pi).
        simpl val_eq'.
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
        try rewrite andb_true_r; try rewrite andb_false_r;
        split; introv Hcond; tryfalse; eauto;
        introv Hf; destruct Hf as (wt & Hf); inverts Hf;
        try rewrite Int.eq_true in eq_i; tryfalse.
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
         try solve [
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); tryfalse; auto;
         try solve [
         eapply Hrhq in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mx & my & pqwl &qwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgete in Hget_ptcb'; inverts Hget_ptcb']].
       (*  tcb_st = wait (os_stat_postq e) i1 *)
        lets Hcp: Hget_ptcb.
        destruct sus ; subst;
         [ specialize (Hhl_pqsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_pqsuspend;
            destruct Hhl_pqsuspend as (Hhl_pq' & Hdlyzero & Heptr & Hst)
           | specialize (Hhl_pq _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_pq;
            destruct Hhl_pq as (Hhl_pq' & Hdlyzero & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        try solve [
       destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); tryfalse; auto;
         try solve [
         eapply Hrhq in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mx & my & pqwl &qwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgete in Hget_ptcb'; inverts Hget_ptcb']].
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
        try solve [
        destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); tryfalse; auto;
         try solve [
         eapply Hrhmb in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mn & mwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgete in Hget_ptcb'; inverts Hget_ptcb']].
       (*  tcb_st = wait (os_stat_mutexsem e) i1 *)
       lets Hcp: Hget_ptcb.
        destruct sus ; subst;
         [ specialize (Hhl_mssuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_mssuspend;
            destruct Hhl_mssuspend as (Hhl_ms' & Heptr & Hst)
           | specialize (Hhl_ms _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_ms;
            destruct Hhl_ms as (Hhl_ms' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        try solve [
       destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); tryfalse; auto;
         try solve [
         destruct Hrhmx as (_ & Hrhmx & _);
         eapply Hrhmx in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mn1 & mn2 & mwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgete in Hget_ptcb'; inverts Hget_ptcb']].
       (*  tcb_st = wait (os_stat_port e) i1  new add *)
       lets Hcp: Hget_ptcb.
        destruct sus ; subst;
         [ specialize (Hhl_portsuspend _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_portsuspend;
            destruct Hhl_portsuspend as (Hhl_port' & Heptr & Hst)
           | specialize (Hhl_port _ _ _ _ (eq_refl _)) ;
            unfold WaitTCBblk in Hhl_port;
            destruct Hhl_port as (Hhl_port' & Heptr & Hst) ];
        inverts Heptr; inverts Hst;
        try solve [
       destruct e as (pb & pi);
        simpl val_eq';
        destruct (peq pb v'48) eqn: eq_b;
        destruct (Int.eq pi Int.zero) eqn: eq_i;
        try subst pb; try (eapply semacc_int_eq_true in eq_i; subst pi);
         try rewrite andb_true_r; try rewrite andb_false_r;
         split; introv Hcond; try (introv Hf; destruct Hf as (wt & Hf)); tryfalse; auto;
         try solve [
         eapply Hrhport in Hget_ptcb'; eauto;
         destruct Hget_ptcb' as (mwl & Hget_ptcb' & Hin);
         unfold get in Hget_ptcb'; unfold EcbMap in Hget_ptcb';
         rewrite Hgete in Hget_ptcb'; inverts Hget_ptcb']].
  }
  destruct Hst_case as (Hst_same & Hst_diff).
  (* exit while loop  *)
  assert (Hnone: TcbMod.get tls1 (v'45, Int.zero) = None).
  { eapply tjoin_get_none_l. 
    instantiate (2:= tls2).
    eauto.
    eauto.
  }
  assert (Hblked_eq:  get_tls_blocked_num (TcbMod.lst (TcbMod.merge tls1 (TcbMod.sig (v'45, Int.zero) (prio, tcb_st, msg, sus)))) (v'48, Int.zero) = (get_tls_blocked_num (((v'45, Int.zero),(prio, tcb_st, msg, sus))::nil) (v'48, Int.zero) + get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero))%nat ).
  {  assert (Hmerge: TcbMod.join (TcbMod.sig (v'45, Int.zero) (prio, tcb_st, msg, sus)) tls1 (TcbMod.merge (TcbMod.sig (v'45, Int.zero) (prio, tcb_st, msg, sus)) tls1)).
     { clear -Htj' Htj_sig.
       eapply TcbMod.join_whole2part;
       eapply TcbMod.join_comm; eauto.
     }
     eapply TcbMod.join_comm in Hmerge.
     eapply TcbMod.join_meq_eql in Hmerge.
     rewrite <- Hmerge.
     eapply get_tls_blocked_succ_eq; eauto.
   }
   exists (v'1 ++
             (sval, long,
             if val_eq' x10 (Vptr (v'48, Int.zero))
             then Vint32 (vsval -ᵢ $ 1)
             else Vint32 vsval) :: v'49).
   exists (get_tls_blocked_num (TcbMod.lst (TcbMod.merge tls1 (TcbMod.sig (v'45, Int.zero) (prio, tcb_st, msg, sus)))) (v'48, Int.zero)).
   exists x2. 
   exists (vl1 ++
              (x2
               :: v'0
                  :: x10
                     :: msg
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 prio
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: nil) :: nil). 
   exists vl2 (TcbMod.merge tls1 (sig (v'45, Int.zero) (prio, tcb_st, msg, sus))) x3.
   (* discuss where ptcb is null *)
   destruct H41 as [Hptcb_null | (pnext & Hptcb_ptr)];
   subst x2.
   (* new ptcb = Vnull, get out of the loop *)
   assert (Heq_right: vl2 = nil /\ x3 = TcbMod.emp).
   { clear -Hptcb_right.
     destruct vl2; auto. simpl in *. simpljoin. tryfalse. }
   destruct Heq_right; subst vl2; subst x3.
   assert (Hmerge_eq: (TcbMod.merge tls1 (TcbMod.sig (v'45, Int.zero) (prio, tcb_st, msg, sus))) = v'9).
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
   eapply OSMutexPendPure1.dllseg_compose.
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
      lets Hblk_num_pos: get_tls_blocked_pos (TcbMod.lst tls1) (v'48, Int.zero).
      remember (get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero)) as blk_num.
      destruct (val_eq' x10 (Vptr (v'48, Int.zero))) eqn: blk_cond.
      (* found new bocked tcb *)
       specialize (Hst_same (eq_refl _)). destruct Hst_same as (wt & Hst_same). subst tcb_st.
       unfold get_tls_blocked_num. rewrite tid_beq_true.
       rewrite Nat.add_0_r.
       left.
       clear -Hblk_cases Hsval'_eq Hblk_num_pos Hget_sval_none Hget_sval' eq2.
       split. eapply Nat.add_pos_nonneg; auto with zarith.
       lets Hset_sval'_eq: Set_sval_eq Hget_sval' Hget_sval_none.
       rewrite <- Hset_sval'_eq. clear Hset_sval'_eq.
       simpl Int_sub_n.
       destruct Hsval'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
       subst blk_num. inverts Heq.
       simpl Int_sub_n in *.
       destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
       apply Nat.lt_irrefl in Hlt.
       tryfalse.
       rewrite <- Heq.
       change ($ 1) with Int.one. auto.
       change ($ 1) with Int.one.
       destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
        2: {  subst blk_num.  apply Nat.lt_irrefl in Hblk_lt. (* new add *) tryfalse. } 
        rewrite Heq'. inverts Heq.
        rewrite Set_set_sval_eq; auto.
      (* not found the new blocked tcb *)
       specialize (Hst_diff (eq_refl _)).
      assert (Heq: (get_tls_blocked_num ((v'45, Int.zero, (prio, tcb_st, msg, sus)) :: nil)
   (v'48, Int.zero) = 0)%nat).
     { clear -Hst_diff. simpl.
        destruct tcb_st; auto.
        destruct t; auto.
        destruct ( tidspec.beq e (v'48, Int.zero) ) eqn: eq1; auto.
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
  eapply OSMutexPendPure1.dllseg_compose.
  sep cancel (dllseg (Vptr tls_head)).
  simpl dllseg at 1.
  unfold node.
  sep cancel Aop.
  sep cancel A_dom_lenv.
  sep pauto.
  split; auto. go.
  2: { clear. rewrite <- app_assoc. rewrite list_prop1. auto. }
  2: { left. splits; auto.
       eapply TcbMod.join_comm.
       eapply OSTimeTickPure.join_join_merge'; eapply TcbMod.join_comm; eauto.
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
    lets Hblk_num_pos: get_tls_blocked_pos (TcbMod.lst tls1) (v'48, Int.zero).
    remember (get_tls_blocked_num (TcbMod.lst tls1) (v'48, Int.zero)) as blk_num.
    destruct (val_eq' x10 (Vptr (v'48, Int.zero))) eqn: blk_cond.
    (* found new bocked tcb *)
    specialize (Hst_same (eq_refl _)); destruct Hst_same as (wt & Hst_same); subst tcb_st.
    unfold get_tls_blocked_num. rewrite tid_beq_true.
    rewrite Nat.add_0_r.
    left.
    clear -Hblk_cases Hsval'_eq Hblk_num_pos Hget_sval_none Hget_sval' eq2.
    split. eapply Nat.add_pos_nonneg; auto with zarith.
    lets Hset_sval'_eq: Set_sval_eq Hget_sval' Hget_sval_none.
    rewrite <- Hset_sval'_eq. clear Hset_sval'_eq.
    simpl Int_sub_n.
    destruct Hsval'_eq as [(Hblk_eq & Heq) | (Hblk_lt & Heq)].
    subst blk_num. inverts Heq.
    simpl Int_sub_n in *.
    destruct Hblk_cases as [ (Hlt & Heq) | (Hsame & Heq)].
    apply Nat.lt_irrefl in Hlt. (* new add *)
    tryfalse.
    rewrite <- Heq.
    change ($ 1) with Int.one. auto.
    change ($ 1) with Int.one.
    destruct Hblk_cases as [ (Hlt & Heq') | (Hsame & Heq')].
    2: { subst blk_num.  apply Nat.lt_irrefl in Hblk_lt. (* new add *) tryfalse. } 
    rewrite Heq'. inverts Heq.
    rewrite Set_set_sval_eq; auto.
    (* not found the new blocked tcb *)
    specialize (Hst_diff (eq_refl _)).
    assert (Heq: (get_tls_blocked_num ((v'45, Int.zero, (prio, tcb_st, msg, sus)) :: nil)
   (v'48, Int.zero) = 0)%nat).
    { clear -Hst_diff. simpl.
      destruct tcb_st; auto.
      destruct t; auto.
      destruct ( tidspec.beq e (v'48, Int.zero) ) eqn: eq1; auto.
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
  clear -H1. destruct H1 as [ (Heq & _) | (Heq & _)]; subst; simpl; auto.
  unprotect HeqH16.
  hoare unfold.
  destruct H1 as [ (Heq & _) | (Heq & Heq2)]; subst v'22; simpl in H38; destruct H38; tryfalse.
  simpljoin.
  substs.
  eapply backward_rule1. 
  intros.
  eapply ASeminfo_select_sn_ex_strong.
  exists v'12 (Z.to_nat (Int.unsigned posv)) v'35.
  sep pauto.
  eapply backward_rule1. 
  introv Hsat.
  sep_lifts_trms_in Hsat tcbdllseg.
  eapply tcbdllseg_split in Hsat; eauto.
  hoare unfold.
  assert (Hct_eq: v'22 = tid).
  { clear -H1 Htls_last_case.
     destruct Htls_last_case as [ (Hnil & Heq) | (vl & Hnnil & Hlast & Heq)];
    subst; inverts Heq;
    destruct H1 as [ ( Hnnil' & Hlast) | (Hnil & Heq)];
    subst; try inverts Heq;
    auto; tryfalse.
    rewrite Hlast in H0. inverts H0.
   auto.
  }
  subst v'22.

  hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid, evatomheapid).
  destruct H37 as [(Hblk_lt & Hevatom') | (Hblk_0 & Hevatom')];
  subst v'0.
  (* the blocked tasks exists *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_blocked_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  (*EXIT_CRITICAL*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep_lifts_trms AOSTCBList.
  unfold AOSTCBList.
  unfold EvtInv.
  sep pauto; eauto.
  unfold ASemEIBs.
  sep normal. eexists.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel (tcbdllseg (Vptr tls_head)).
  sep cancel tcbdllseg.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel ASemCap.
  trycancel.
  sep split; eauto.
  pure_auto.
  pure_auto.
  (* return *)
  hoare forward.

   (* the blocked tasks related the sem event in tcblist *)
  eapply abscsq_rule. 
  apply noabs_oslinv.
  eapply sem_getvalue_absimp_no_source_end; eauto.
  pure_auto.
  eapply absinfer_eq.
  (*EXIT_CRITICAL*)
  hoare forward prim.
  sep cancel tcbdllflag.
  sep cancel p_local.
  sep_lifts_trms AOSTCBList.
  unfold AOSTCBList.
  unfold EvtInv.
  sep pauto; eauto.
  unfold ASemEIBs.
  sep normal. eexists.
  sep cancel ASeminfo.
  sep cancel AMuxEIBs.
  sep cancel AMqEIBs.
  sep cancel (tcbdllseg (Vptr tls_head)).
  sep cancel tcbdllseg.
  sep cancel Aier.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv. 
  sep cancel ASemCap.
  trycancel.
  sep split; eauto.
  pure_auto.
  pure_auto.
  (* return *)
  hoare forward.
  Unshelve.
  exact Tnull.
  exact Vnull.
  exact 0%nat.
  exact 0%nat.
  exact Tnull.
  exact Vnull.
  exact Tnull.
  exact Vnull.
  exact vhold_addr.
Qed.
