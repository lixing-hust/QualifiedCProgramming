Require Import ucos_include.
Require Import ios_int.
Require Import int_lock.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma dint_rule':
    forall Spec sd  I r ri isr ier is cs pa t P level v Hier,
    GoodFrm P ->  
    P ==> CurLINV pa t ->
    InfRules Spec sd pa I r ri 
          ( <|| int_lock_aop(|nil|)||> ** Aisr isr ** Aier ier ** Aie false ** Ais is ** Acs cs **  
            LV level @ Tint32 |-> v  ** Aabsdata ierid (hier Hier)** P
          )
          (sprim (dint level))
          (<||(END (Some (Vint32(getLevel ier intStart Int.zero intStartInt))))||> ** Aisr isr ** Aier (empupd ier) ** Aie false ** Ais is ** Acs cs **  
            LV level @ Tint32 |-> (Vint32 (getLevel ier intStart Int.zero intStartInt))  ** 
            Aabsdata ierid (hier (empupd Hier)) ** P) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
    <|| int_lock_aop (|nil|)||> **
    OS [isr, ier, false, is, cs] ** LV level @ Tint32 |-> v ** Hhier Hier ** P
  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply dint_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

Lemma IntLockPicProof: 
    forall  vl p r tid, 
    Some p =
    BuildPreA' os_api int_lock lockapi vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api int_lock lockapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
    os_api int_lock = Some (t, d1, d2, s) /\
    {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare forward prim; pure_auto.
  unfold IntInv.
  hoare unfold.
  unfold lockcode.

  eapply backward_rule1.
  intro.
  intros.

(*
  instantiate (1 :=
    (<||int_lock_aop (|nil|) ||>  **
        Aisr empisr **
        Aier v'0 **
        Aie false **
        Ais nil **
        Acs (true :: nil) **
        LV level @ Tint32 |-> v' **
        Hhier v'20 **
        (
        HECBList v'14 **
        HTCBList v'15 **
        HTime v'16 **
        HCurTCB tid **
        Hhinthandler v'21 **
        HhinthandlerParam v'22 **
        Hhexchandler v'23 **
        AOSEventFreeList v'1 **
        AOSQFreeList v'2 **
        AOSQFreeBlk v'3 **
        AECBList v'5 v'4 v'14 v'15 **
        AOSMapTbl **
        AOSUnMapTbl **
        AOSTCBPrioTbl v'6 v'12 v'15 v'17 **
        AOSTCBList v'7 v'8 v'9 (v'10 :: v'11) v'12 tid v'15 **
        AOSTCBFreeList v'18 v'19 **
        AOSRdyTblGrp v'12 v'13 **
        AOSTime (Vint32 v'16) **
        AGVars **
        AOSInthandler v'21 **
        AOSInthandlerParam v'22 **
        AOSExchandler (Vint32 v'23) **
        tcbdllflag v'7 (v'9 ++ v'10 :: v'11) **
        p_local OSLInv tid init_lg **
        A_dom_lenv ((level, Tint32) :: nil)
        )
    )).

  sep lifts (2::5:: nil)%nat.
  eapply elim_a_isr_is_prop.
  eapply elim_aemp_isr_is_prop.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aier.
  sep cancel A_isr_is_prop.
  sep cancel aemp_isr_is.
  sep pauto.
*)

  sep lifts(29::31::21::34::28::30::32::33::35::1::nil)%nat in H1.
  eapply elim_a_isr_is_prop in H1.
  eapply elim_aemp_isr_is_prop in H1.
  exact H1.
  eapply seq_rule.
  hoare lifts(3::1::6::4::2::5::7::nil)%nat pre.
  eapply dint_rule'; eauto.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intro.
  intros.
  unfold CurLINV.
  unfold p_local in H1.
  sep pauto.
  sep cancel LINV.
  simpl; auto.

  eapply backward_rule1.
  intro; intros.
  sep lifts (2::5::nil)%nat in H1.
  eapply add_a_isr_is_prop in H1.
  sep lifts (1::2::5::nil)%nat in H1.
  eapply add_aemp_isr_is_prop in H1.
  eauto.
  hoare lift 6%nat pre.

  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel EvtInv.
  sep cancel p_local.
  unfold IntInv.
  sep cancel Aier.
  sep pauto.
  auto.
  go.
  hoare forward.
Qed.
