Require Import include_frm1.
Require Import NPeano.
Require Import Lia.

Require Import os_code_defs1.
Require Import code_notations1.
Require Import os_ucos_h1.
Require Import abs_op1.

Require Import ifun_taskcreate.
Require Import thread_create1. 

Require Import threadcreat.
Require Import ifun_taskdel_spec. 
Require Import ifun_taskdelete.
Require Import thread_cancel1.
Set Keyed Unification.

(* Definition pthread_exit_impl :=
Void ·pthread_cancel·(⌞⌟)··{
  ⌞ 
    thread @ Int8u; 
    ret @ Int8u
    ⌟;
  
  ENTER_CRITICAL;ₛ   
  thread′ =ₑ OSTCBCur′→OSTCBPrio;ₛ 
  EXIT_CRITICAL;ₛ 
  ret′ =ᶠ OSTaskDel(·thread′·);ₛ
  RETURN
}·.  *)

Definition prework (vl: vallist)(O1 : osabst) (rst : option val * option osabst) :=
  match rst with 
  |(v, O2)  =>
  exists t tls st m p rv_prio,
  vl = rv_prio :: nil /\
  get O1 curtid = Some (oscurt t) /\ 
  get O1 abstcblsid = Some (abstcblist tls) /\ 
  get tls t = Some (p, st, m) /\
  v = None /\
  (rv_prio =  Vint32 p /\ O2 = Some O1 \/
   rv_prio <>  Vint32 p /\ O2 = None)
  end.
  

Definition threadexit(vl: vallist):=
  match vl with
  (rv_prio ::rv:: nil) =>
(   
  prework(|rv_prio :: nil|) ;;
  spec_code_cons (taskdelcode (rv_prio:: rv::nil))
  (END None))
| _ => spec_abort
end.


Local Open Scope code_scope.

Require Import abs_op1.
Require Import init_spec1.
Require Import inv_prop1.
Require Import hoare_tactics1.
Require Import pure_auto1.
Require Import ucos_pauto1.
Require Import seplog_tactics1.
Require Import seplog_lemmas1.
Require Import sep_cancel_ext1.
Require Import derived_rules1.
Require Import hoare_conseq1.
Require Import ucos_forward1.
Require Import sem_common1.
Require Import seplog_trm_tacs.

Local Open Scope code_scope.

Lemma threadexit_absimp_prework_abt:
  forall sch tls ct p ready msg s P rv_prio,
    can_change_aop P ->
    get tls ct = Some(p, ready, msg)->
    rv_prio <> Vint32 p ->
    absinfer sch
      (<|| prework(|rv_prio :: nil|) ;; s ||> ** HTCBList tls  ** HCurTCB ct** P)
      (<|| ABORT ||> ** HTCBList tls  ** HCurTCB ct** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := HTCBList tls ** HCurTCB ct ** P).
  can_change_aop_solver.
  eapply absinfer_abt.
  can_change_aop_solver.
  can_change_aop_solver.
  absimp_abt_solver.
  sep lift 2%nat in H2.
  eauto.
  can_change_aop_solver.
  apply absinfer_seq_abt; can_change_aop_solver; eauto.
Qed.

Lemma prework_succ:
forall sch tls ct p ready msg s P rv_prio,
  get tls ct = Some(p, ready, msg)->
  rv_prio = Vint32 p ->
  can_change_aop P ->
  absinfer sch (<||prework (|rv_prio :: nil|) ;; s||>  ** HTCBList tls  ** HCurTCB ct** P)
       (<||s||>  ** HTCBList tls ** HCurTCB ct ** P).
Proof.
infer_solver 0%nat.
Qed.

(* Definition pthread_exit : ident := 1715%Z.  *)

Definition pthreadexitapi :=
  (threadexit, (Tvoid, Tint32 :: Tint32 :: nil)).

Definition new_api_spec_list :=
  ((pthread_exit, pthreadexitapi) :: nil) ++ api_spec_list.

Definition new_api_spec :=
  convert_api_spec new_api_spec_list.

Definition new_os_spec :=
  (new_api_spec, GetHPrio).


Require Import ifun_spec1.
Local Open Scope list_scope.


Definition os_spec_list_ext :=
  (((OSTaskDel, OSTaskDelete_spec) :: nil)
   ++ new_osq_spec_list).

Definition os_spec_ext :=
  convert_spec os_spec_list_ext.

Require Import abs_infer_step1.
Require Import ucos_frmaop1.


Definition api_fun_list_new := (pthread_exit_impl :: nil)%list.
Definition os_api_new := convert_cfuns api_fun_list_new.

Local Ltac sifs := 
  match goal with
    | |- context[if ?e then _ else _] => destruct e; sifs
    | |- _ <> _ => try solve [simpl; intro; tryfalse]
    | _ => idtac
  end.

Open Scope code_scope.

Lemma PthreadexitProof:
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api_new pthread_exit
              (threadexit, (Tvoid, Tint32 :: Tint32 :: nil)) vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api_new pthread_exit
              (threadexit, (Tvoid, Tint32 :: Tint32 :: nil)) vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api_new pthread_exit = Some (t, d1, d2, s) /\
      {|os_spec_ext, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lift_pre Aop.

  hoare forward prim.
  pure_auto.
  hoare_split_pure_all.

  try unfold OSInv; try unfold AOSTCBList;unfold_dll.
  pure intro.

  hoare forward.
  go.

  assert(Hpriolt64:Int.unsigned i3 < 64).
  unfold TCBList_P in H8.
  simpljoin.
  unfold TCBNode_P in H10.
  destruct x2, p.
  simpljoin. 
  unfold RL_TCBblk_P in H23.
  simpljoin.
  unfold V_OSTCBPrio in H23. simpl in H23. inverts H23. lia.
  assert(Htrue: Int.unsigned i3 <=? Byte.max_unsigned = true).
  change Byte.max_unsigned with 255.
  clear -Hpriolt64. int auto.
  lets bak_H0: H0.
  unfold RH_CurTCB in H0.
  do 3 destruct H0.

  assert(x = i3).
  {
    clear -H0 H6 H8.
    unfolds in H8. simpljoin.
    unfolds in H3. 
    destruct x5, p. 
    simpljoin.
    unfolds in H5. simpl in H5.
    inverts H5.
    inverts H. 
    clear -H0 H6 H2.
    assert(get v'16 (v'29, Int.zero) =
    Some (p, t, m)).
    eapply join_joinsig_get; eauto.
    rewrite H in H0.
    inverts H0. auto.
  }
  subst x.
  

    do 3 (destruct v'; try apply absabort_rule).
  unfold threadexit.
  hoare lifts (1::20::22::nil)%nat pre.
    (* hoare_lifts_trms_pre (Aop, abstcblsid, curtid). *)
  assert (Hrv_prio: v = Vint32 i3 \/ v <> Vint32 i3) by tauto.
  destruct Hrv_prio as [Hrv_prio | Hrv_prio].
  2:{

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply threadexit_absimp_prework_abt.
    go.
    eauto. eauto.
    eapply absinfer_eq.
    apply absabort_rule.
  }
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply prework_succ.
  eauto.
  eauto.
  go.
  eapply absinfer_eq.
  
  hoare forward prim.
  sep cancel APthreadAttr. 
  sep cancel tcbdllflag.
  unfold AOSTCBList.
  sep pauto.
  unfold tcbdllseg.
  sep cancel 4%nat 1%nat. 
  unfold1 dllseg. 
  sep pauto. 
  unfold1 node. 
  sep pauto. 
  sep cancel 2%nat 1%nat. 
  sep cancel 2%nat 1%nat.
  eauto.
  split; auto.
  go.
  go.
  eauto.
  eauto.
  auto.
  go.

  hoare forward.
  math simpls.
  {
    sep cancel Aie.
    sep cancel Ais.
    sep cancel Acs.
    sep cancel Aisr.
    sep cancel Aop.
    sep pauto.
  }  
  go.
  go.
  {
    unfold retpost. introv Hsat.
    inverts Hsat; sep auto.
    sep destruct H2. sep split in H2.
    destruct H10. rewrite H10. auto.
  }
  {
    clear - Hrv_prio Htrue.
    inverts Hrv_prio. pure_auto.
  }
  {
    intros.
    sep destruct H2.
    eexists init_lg.
    sep pauto.
  }
  {
    intros.
    sep destruct H2.
    eexists init_lg.
    sep pauto.
  }
  hoare unfold.
  hoare forward.
  inverts H2.
  eauto.
Qed.
  
  



