Require Import ucos_include.
Require Import ios_int.
Require Import int_lock.
Local Open Scope code_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma rintp_rule':
  forall Spec sd  I r ri isr ier is cs aop pa t P irqLine Hier Hier' v,
      GoodFrm P ->
      P ==> CurLINV pa t ->
      Hier' = ierupd Hier (Z.to_nat (Int.unsigned v)) true ->
      InfRules Spec sd pa I r ri 
          ( <|| int_enable_pic_aop(|nil|) ;; aop||> 
            ** Aisr isr ** Aier ier ** Aie false ** Ais is ** Acs cs
            ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier) ** P 
          )
          (sprim (rintp irqLine))
          (<||aop||> ** Aisr isr ** Aier (ierupd ier (Z.to_nat (Int.unsigned v)) true) ** Aie false ** Ais is ** Acs cs
            ** LV irqLine @ Tint32 |-> (Vint32 v) ** Aabsdata ierid (hier Hier') ** P) t.
Proof.
  intros.
  eapply backward_rule1.
  instantiate (1:= (
    <|| int_enable_pic_aop (|nil|);; aop ||> **
    OS [isr, ier, false, is, cs] ** LV irqLine @ Int32u |-> Vint32 v ** Hhier Hier ** P
  )).
  intro.
  intros.
  sep pauto.
  eapply forward_rule2.
  eapply rintp_rule; eauto.
  intro.
  intro.
  sep pauto.
Qed.

Lemma IntenablePicProof: 
    forall  vl p r tid, 
    Some p =
    BuildPreA' os_api int_enable_pic enablepicapi vl OSLInv tid init_lg ->
    Some r =
    BuildRetA' os_api int_enable_pic enablepicapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
    os_api int_enable_pic = Some (t, d1, d2, s) /\
    {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-tid {{p}}s {{Afalse}}.
Proof.
  init_spec.
  hoare forward prim; pure_auto.
  unfold IntInv.
  hoare unfold.
  unfold enablepiccode.

  eapply backward_rule1.
  intro.
  intros.

(*
  instantiate (1 :=
    (<|| int_enable_pic_aop (|nil|);; END None ||>  **
        Aisr empisr **
        Aier v' **
        Aie false **
        Ais nil **
        Acs (true :: nil) **
        Hhier v'19 **
        (
        HECBList v'13 **
        HTCBList v'14 **
        HTime v'15 **
        HCurTCB tid **
        Hhinthandler v'20 **
        HhinthandlerParam v'21 **
        Hhexchandler v'22 **
        AOSEventFreeList v'0 **
        AOSQFreeList v'1 **
        AOSQFreeBlk v'2 **
        AECBList v'4 v'3 v'13 v'14 **
        AOSMapTbl **
        AOSUnMapTbl **
        AOSTCBPrioTbl v'5 v'11 v'14 v'16 **
        AOSTCBList v'6 v'7 v'8 (v'9 :: v'10) v'11 tid v'14 **
        AOSTCBFreeList v'17 v'18 **
        AOSRdyTblGrp v'11 v'12 **
        AOSTime (Vint32 v'15) **
        AGVars **
        AOSInthandler v'20 **
        AOSInthandlerParam v'21 **
        AOSExchandler (Vint32 v'22) **
        tcbdllflag v'6 (v'8 ++ v'9 :: v'10) **
        p_local OSLInv tid init_lg **
        LV irqLine @ Int32u |-> Vint32 i ** A_dom_lenv ((irqLine ↝ {Int32u}) :: nil)
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
  eapply rintp_rule'; eauto.
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
