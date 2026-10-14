(*
Definition OSTickISR_impl :=
(* Void ·OSTickISR·(⌞ ⌟)··{ *)
  OSTickISR ↝ {
    (* ⌞y @ Int32  ⌟; *)
    
    (*DSP_C6x_Save(­);ₛ*)
    OSIntEnter(­);ₛ
    If(OSIntNesting′==ₑ′1){
       (*y′ =ᶠ DSP_C6x_GetCurrentSP(·);ₛ
       OSTCBCur′→ OSTCBStkPtr =ₑ〈OS_STK ∗〉y′*)
       (*OSTCBCur′→ OSTCBStkPtr =ᶠ DSP_C6x_GetCurrentSP(·)*)
       OSIntNesting′=ₑ′1
    };ₛ 
    OSTimeTick(­);ₛ
    OSIntExit(­);ₛ
    (*DSP_C6x_Resume(­);ₛ*)
    RETURN
(*}·.*)
  }.
*)
Require Import ucos_include2.
Require Import ios_int2.
Require Import oscore_common2.
Require Import os_spec2.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import Lia.
Require Import OSTimeTickPure2.
Require Import ios_int_tac2.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.

Lemma isrupd_true_false:
  forall ir i,
    isrupd (isrupd ir i true) i false = isrupd ir i false.
Proof.
  intros.
  unfold isrupd.
  apply functional_extensionality_dep.
  intros.
  destruct (beq_nat i x);auto.
Qed.

Lemma absimp_tickisr:
forall P tls qls tm s sch qls' tls' tm',
  can_change_aop P ->
  tm'=(Int.add tm Int.one) ->
  tickstep tls qls tls' qls' ->
  absinfer sch
            ( <||tickisr_spec (|nil|) ;; s||> ** HECBList qls **  HTCBList tls ** HTime tm ** P)
            ( <||END None;;s ||> ** HECBList qls' ** HTCBList tls' **  HTime tm' ** P).
Proof.
  intros.
  apply absinfer_seq.
  can_change_aop_solver.
  can_change_aop_solver.
  eapply absinfer_prim.
  can_change_aop_solver.
  can_change_aop_solver.
  (* ** ac: Print absimp. *)
  unfold absimp.
  intros.
  eexists; exgamma.
  (* infer_part1 0%nat. *)
  (* eexists; exgamma. *)
  splits.
  hmstep_solver.
  assert (eqdomO  
        (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls'))
                  (set
        (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl;auto.
  }
  
  assert (eqdomO  (set O absecblsid (absecblist qls')) (set (set O absecblsid (absecblist qls'))
                                                                                abtcblsid (abstcblist tls'))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl.
  
    eapply tickstep_eqdomtls;eauto.
    apply TcbMod.sub_refl.
  }
  
  assert (eqdomO O (set O absecblsid (absecblist qls'))).
  {
    eapply abst_get_set_eqdom.
    absdata_solver.
    simpl;auto.
  }

  (* ** ac: Check tickstep_eqdomtls. *)
  eapply tickstep_eqdomtls;eauto.
  apply TcbMod.sub_refl.
  
  (* eapply eqdomO_trans;eauto. *)
  assert (tidsame (set (set O absecblsid (absecblist qls'))
                                 abtcblsid (abstcblist tls'))
                  (set
                     (set (set O absecblsid (absecblist qls'))
                                    abtcblsid (abstcblist tls')) ostmid (ostm (tm+ᵢInt.one)))).
  {
    tidsame_solver.
  }
  assert (tidsame O
                  (set (set O absecblsid (absecblist qls'))
                       abtcblsid (abstcblist tls'))).
  {
    tidsame_solver.
  }
  rewrite H0.
  eapply tidsame_trans; eauto.
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma OSTickISR_proof:
forall ir er si p r ct lg,
  Some p = BuildintPre 4 int_spec ir er si I OSLInv ct lg->
  Some r = BuildintRet 4 int_spec ir er si I OSLInv ct lg->
  exists s,
    os_interrupt OSTickISR = Some s /\ {| OS_spec , GetHPrio, OSLInv, I, retfalse, r |} |-ct
    {{p}} s {{Afalse}}.
Proof.
  intros.
  unfold BuildintPre in H.
  simpl in H.
  unfold ipreasrt' in H.
  inverts H.
  unfold  BuildintRet in H0.
  simpl in H0.
  unfold iretasrt' in H0.
  inverts H0.
  unfold os_interrupt.
  simpl.
  eexists.
  split.
  auto.

  unfold invlth_noisr.
  unfold starinv_noisr.
  simpl.

  unfold p_local.
  unfold LINV.
  unfold OSLInv.
  hoare unfold.
  (*unfold IntInv.*)

  (*OSEnter*)
  hoare forward.
  (*sep lift 19%nat.
  apply disj_split.
  right.*)
  instantiate (1:=A_dom_lenv nil).
  Focus 4.
  apply H0.
  Focus 3.
  isr_is_prop_help (4%nat) (si) (ir).
  clear H9.
  sep lifts (1::2::41::nil)%nat in H10.
  apply a_isr_is_prop_split in H10.
  sep split in H10.
  apply H16.

  assert(ct = v'15).
  unfold CurTid, AOSTCBList' in H.
  sep lift 10%nat in H.
  apply disj_split in H.
  destruct H.
  sep normal in H. sep destruct H.
  sep lift 6%nat in H. sep split in H.
  destruct H3.
  rewrite H14 in H.

  (*将第四个调整至最前面*)
  sep lift 4%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  sep normal in H. sep destruct H.
  sep lift 7%nat in H. sep split in H.
  destruct H3. rewrite H11 in H.
  sep lifts (1::3::nil)%nat in H.
  eapply read_only_merge_vptr in H.
  destruct H. auto.
  rewrite <- H3 in H.
  clear H3.

  sep lifts (22::23::19::nil)%nat in H.
  apply a_isr_is_prop_split in H.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel AOSTCBPrioTbl.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel AOSRdyTblGrp.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aop.
  sep cancel Aier.
  unfold p_local.
  unfold LINV. unfold OSLInv.
  sep auto.
  auto.
  good_frm_sovler.

  intros.
  sep auto.
  intros.
  sep auto.

  (*If (OSIntNesting ′ ==ₑ ′ 1)*)
  hoare unfold.
  unfold AGVars.
  pure intro.
  rename H6 into HPrio.
  rename H7 into HPrioC.
  hoare forward.
  destruct (Int.eq v'56($ 1)); auto.
  pure intro.
  hoare forward.
  eapply disj_rule.
  pure intro.
  clear H6 H7 H8.
  inversion H3.

  (*EOI*)
  eapply backward_rule1.
  intros.
  sep lift 33%nat in H6.
  eapply disj_split in H6.
  destruct H6.
  sep split in H6.
  tryfalse.
  sep normal in H6.
  exact H6.
  eapply seq_rule.  
  hoare lifts (3::34::2::35::36::37::nil)%nat pre.
  eapply eoi_ieoff_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  instantiate (1:=4%nat).
  rewrite Int.unsigned_repr.
  simpl.
  auto.
  rewrite max_unsigned_val.
  lia.
  intros.
  
  exact H6.
  apply GoodI_I.  (*Good I*)
  (*unfold AOSRunning.
  unfold AIntNumCurrent.*)
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  go.

  (*OSTimeTick()*)
  unfold isflag in H5.
  destruct H5; subst v'25.
  eapply backward_rule1.
  intros.
  sep lifts (28::29::38::nil)%nat in H5.
  eapply inv_change_aux in H5.
  exact H5.
  unfold AOSTime.
  unfold AOSTCBList.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'33).
  sep lift 2%nat in H3.

  eapply dllseg_head_isptr';eauto.
  pure intro.
  unfold isptr in H3.
  destruct H3;tryfalse.
  destruct H3.
  hoare forward.
  sep cancel Aisr.
  sep cancel p_local.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Ais.
  sep cancel Aier.
  sep cancel 1%nat 1%nat.
  sep cancel AOSRdyTblGrp.
  sep cancel AECBList.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  exact H7.
  auto.
  eauto.
  eauto.
  eauto.
  auto.
  unfold IntInv.
  (*unfold AOSRunning.
  unfold AIntNumCurrent.*)
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  go.
  intros.
  sep auto.
  intros.
  sep auto.
  hoare unfold.

  inverts H7.

  lets Hx:tickstep_exists' H.
  Import DeprecatedTactic.
  mytac.
  unfold tickisr.
  hoare lifts(6::37::38::39::nil)%nat pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absimp_tickisr;eauto.
  Require Import ios_int_tac2.
  can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.
  rewrite isrupd_true_false.
  lets Hx:tcbls_rtbl_timetci_update_decompose H21;mytac.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H7.
  lets Hx:tcbls_rtbl_timetci_update_tls_split H16 H10 H7.
  exact Hx.
  lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H21.
  mytac.
  lets Hx: timetick_update_prop H8 H9 H11 H12 H21;eauto.
  mytac.
  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate(1:=v'73).
  instantiate (2:=(Vptr v'61)).
  simpl app.
  apply TcbMod.join_emp_eq in H6;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  mytac.
  lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H21.

  eapply backward_rule1 with(
    [| R_Prio_No_Dup v'73 |] ** EX x8 : val,
    tcbdllseg (Vptr v'61) Vnull x8 (Vptr v'83) x1 **
    tcbdllseg (Vptr v'83) x8 v'69 Vnull (x2 :: x3) **
     <|| END None;; (isched;; END None ?? END None) ||>  **
    HECBList x0 **
    HTCBList x **
    HTime (v'67 +ᵢ  Int.one) **
    Aisr (isrupd v'21 4%nat false) **
    Aier (ierupd v'34 4%nat true) **
    Aie false **
    Ais (4%nat :: v'26) **
    Acs nil **
    GV OSTCBList @ OS_TCB ∗ |-> Vptr v'61 **
    GV OSEventList @ OS_EVENT ∗ |-> v'77 **
    evsllseg v'77 Vnull v'80 v'79 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr v'83 **
    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'70 **
    GV OSRdyGrp @ Int8u |-> Vint32 x7 **
    GV OSTime @ Int32u |-> Vint32 (v'67 +ᵢ  Int.one) **
    p_local OSLInv v'83 (logic_val (V$ 1) :: nil) **
    AOSTCBFreeList v'43 v'44 **
    tcbdllflag (Vptr v'61) (x1 ++ x2 :: x3) **  (*不为(v'62 ++ v'63 :: v'64)*)
    A_dom_lenv nil **
    GV OSIntNesting @ Int32u |-> (V$ 1) **
    GV OSLockNesting @ Int32u |-> Vint32 v'57 **
    GV INT_MUX_H @ Int32u |-> Vint32 v'55 **
    GV INT_MUX_L @ Int32u |-> Vint32 v'54 **
    GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'53 **
    GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'52 **
    GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'51 **
    GV OSIntExitY @ Int8u |-> Vint32 v'50 **
    GV OSPrioCur @ Int8u |-> Vint32 v'49 **
    GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'48 **
    GV OSCtxSwCtr @ Int32u |-> Vint32 v'47 **
    GV OSPrioHighRdy @ Int8u |-> Vint32 v'46 **
    AOSEventFreeList v'27 **
    AOSQFreeList v'28 **
    AOSQFreeBlk v'29 **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl v'32 v'65 v'73 v'45 **
    HCurTCB v'83 **
    GV OSRunning @ Int8u |-> (V$ 1) **
    IntInv
  ).
  intros.
  sep destruct H29.
  
  unfold AOSTCBPrioTbl in H29.
  unfold R_PrioTbl_P in H29.
  unfold_sep_cancel_helper.
  sep auto.
  sep lift 3%nat.
  sep lift 3%nat in H29.
  eapply tcbdllflag_hold.
  eauto.
  eauto.
  destructs H32;auto.
  hoare_split_pure_all.
  rename H29 into Hnodup.
  lets Hx:timetick_tcblist_p H21 H18 H19 H3 Hnodup.
  eapply tcbls_rtbl_timetci_update_len_eq;eauto.
  clear -H16.
  destruct H16;mytac;subst.
  inverts H0;simpl;auto.
  unfolds.
  destruct v'62;tryfalse.
  unfolds in H1;auto.
  auto.
  mytac.
  (*unfold IntInv.*)
  hoare lifts (3::nil)%nat pre.
  (*unfold AOSIntNesting.*)

  (*hoare abscsq.*)
  eapply abscsq_rule'.
  eapply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  unfold IntInv. can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.

  hoare forward.
  instantiate(1:=A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.

  sep normal.
  sep eexists.
  sep lifts (8::9::20::nil)%nat.
  apply inv_change_aux.
  unfold AGVars.
  unfold AOSTCBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  (*unfold AOSIntNesting.*)
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  (*unfold AOSIntNesting.*)
  sep pauto.
  sep cancel tcbdllflag.
  sep auto.

  eapply tickstep_rh_tcblist_ecblist_p;eauto.
  pauto.
  eapply tickstep_r_priotbl_p;eauto.
  eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'62 ++ v'63 :: v'64));eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'61).
  simpl app.
  apply join_emp_eq in H6; rewrite H6 in H19.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.

  eapply imp_rl_priotbl_p;eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'61).
  simpl app.
  apply join_emp_eq in H6;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  eauto.
  eauto.
  auto.
  eapply tickstep_ecblist_p with (htls:=v'73) (ltls1:=v'62);eauto.
  unfolds.
  destruct v'62;eauto.
  destruct H16;mytac.
  inverts H40;auto.
  tryfalse.
  destruct H16;mytac;tryfalse.
  unfold V_OSTCBNext;auto.
  auto.
  sep split in H32. auto.
  sep split in H32. auto.
  sep split in H32. apply H34.
  auto. unfolds; auto.

  clear -H4.
  unfold isr_is_prop in *.
  intros.
  apply H4 in H.
  unfold isrupd in *.
  destruct ( beq_nat 4 x);auto.
  go.

  intros.
  sep normal in H32.
  sep destruct H32.
  sep split in H32.
  inverts H33.
  apply disj_split in H32.
  destruct H32.
  sep split in H32; tryfalse.
  sep split in H32.
  clear H33.
  sep auto.
  intros.
  sep destruct H32.
  sep split in H32.
  
  inverts H33.
  apply disj_split in H32.
  destruct H32.
  sep split in H32; tryfalse.
  sep split in H32.
  clear H33.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  intros.
  inverts H32.
  sep lift 2%nat in H35.
  apply disj_split in H35.
  destruct H35.
  sep split in H32. tryfalse.
  sep normal in H32.
  apply astar_l_apure_elim in H32.
  destruct H32.
  clear H32.
  exact H35.
  hoare unfold.
  inverts H30.
  inverts H32.
  eapply iret_rule'.
  intros.
  apply disj_split. right.
  sep lift 7%nat in H30.
  apply disj_split in H30.
  destruct H30.
  unfold p_local in *.
  unfold OSLInv in *.
  unfold LINV in *.
  sep normal in H30.
  sep destruct H30.

  sep normal. exists x30.
  sep lift 9%nat.
  apply disj_split. right.
  unfold AGVars in *.
  (*unfold AOSIntNesting , AOSRunning in *.*)
  sep normal in H30.
  sep destruct H30.
  sep normal.
  sep eexists.
  unfold A_isr_is_prop.
  sep auto.
  rewrite H48, H50. auto.
  sep split in H30. tryfalse.
  
  pure intro.
  clear H5.
  rewrite isrupd_true_false.
  (*current task dead*)
  hoare unfold.
  unfold AOSTCBList'.
  hoare lift 27%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H3.
  destruct H3.
  unfold p_local in H3.
  unfold CurTid in H3.
  sep normal in H3.
  sep destruct H3.
  unfold tcbdllseg in H3.
  unfold tcbdllflag in H3.
  sep lifts (4::1::nil)%nat in H3.
  sep split in H3.
  destruct H5;subst.
  eapply read_only_merge_vptr in H3.
  destruct H3.
  clear H17.
  sep lifts (3::4::5::34::nil)%nat in H3.
  apply task_del_noexists in H3.
  unfolds in H3;false.
  exact H3.

  unfold AOSTime.
  unfold tcblist.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'33).
  sep lift 3%nat in H6.
  eapply dllseg_head_isptr;eauto.
  pure intro.
  unfold isptr in H6.
  destruct H6;tryfalse.
  destruct H6.
  eapply backward_rule1.
  intros.
  sep lift 3%nat  in H7.
  unfold tcbdllseg in H7.
  unfold V_OSTCBPrev in H7.
  unfold V_OSTCBNext in H7.
  eapply tcbdllseg_split.
  unfold tcbdllseg.
  subst v'33.
  eauto.
  hoare unfold.
  lets Hx: OSQPostPure2.TCBList_P_Split H3.
  mytac.
  assert (x0= Vptr v'25).
  unfolds in H6.
  destruct v'35.
  inverts H6;auto.
  destruct H7;mytac;tryfalse;auto.
  destruct H7;mytac;tryfalse;auto.
  unfolds in H6.
  rewrite H6 in H11;inverts H11;auto.
  subst x0.
  clear H3.
  hoare forward.
  sep cancel p_local.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Ais.
  sep cancel Aier.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel AECBList.
  sep cancel AOSRdyTblGrp.
  exact H3.
  unfolds; auto.
  eauto.
  eauto.
  eauto.
  auto.
  unfold IntInv.
  good_frm_sovler'.
  intros.
  sep auto.
  sep auto.
  hoare unfold.
  inverts H3.

  lets Hx:tickstep_exists' H.
  
  mytac.
  unfold tickisr.

  hoare lifts(6::38::39::40::nil)%nat pre.
  eapply abscsq_rule'.
  (*hoare abscsq.*)
  apply noabs_oslinv.
  apply absimp_tickisr; eauto.
  pauto.
  unfold IntInv.
  can_change_aop_solver'.

  lets Hx:tcbls_rtbl_timetci_update_decompose H21;mytac.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H13.
  lets Hx:tcbls_rtbl_timetci_update_tls_split H16 H25 H13.
  exact Hx.
  lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H21.
  mytac.
  lets Hx: timetick_update_prop H11 H12 H14 H15 H21;eauto.
  mytac.
  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (3:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H8. rewrite H8 in H19.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  mytac.
  lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H21.

    eapply backward_rule1 with(
      [| R_Prio_No_Dup v'70 |] ** EX x8 : val,
      tcbdllseg (Vptr v'58) Vnull x8 (Vptr v'80) x1 **
      tcbdllseg (Vptr v'80) x8 v'66 Vnull (x2 :: x3) **
       <|| END None;; (isched;; END None ?? END None) ||>  **
      HECBList x0 **
      HTCBList x **
      HTime (v'64 +ᵢ  Int.one) **
      Aisr (isrupd v'33 4%nat false) **
      Aier (ierupd v'43 4%nat true) **
      Aie false **
      Ais (4%nat :: v'34) **
      Acs nil **
      GV OSTCBList @ OS_TCB ∗ |-> Vptr v'58 **
      GV OSEventList @ OS_EVENT ∗ |-> v'74 **
      evsllseg v'74 Vnull v'77 v'76 **
      GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
      GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'67 **
      GV OSRdyGrp @ Int8u |-> Vint32 x7 **
      GV OSTime @ Int32u |-> Vint32 (v'64 +ᵢ  Int.one) **
      p_local OSLInv ct (logic_val (V$ 0) :: nil) **
      TCB_Not_In (Vptr ct) (Vptr v'58) (v'59 ++ v'60 :: v'61) **
      tcbdllflag (Vptr v'58) (x1 ++ x2 :: x3) **
      A_dom_lenv nil **
      GV OSIntNesting @ Int32u |-> (V$ 1) **
      GV OSLockNesting @ Int32u |-> Vint32 v'57 **
      GV INT_MUX_H @ Int32u |-> Vint32 v'55 **
      GV INT_MUX_L @ Int32u |-> Vint32 v'54 **
      GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'53 **
      GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'52 **
      GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'51 **
      GV OSIntExitY @ Int8u |-> Vint32 v'50 **
      GV OSPrioCur @ Int8u |-> Vint32 v'49 **
      GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'48 **
      GV OSCtxSwCtr @ Int32u |-> Vint32 v'47 **
      GV OSPrioHighRdy @ Int8u |-> Vint32 v'46 **
      AOSEventFreeList v'27 **
      AOSQFreeList v'28 **
      AOSQFreeBlk v'29 **
      AOSMapTbl **
      AOSUnMapTbl **
      AOSTCBPrioTbl v'32 v'62 v'70 v'45 ** 
      AOSTCBFreeList' (Vptr ct) v'44 ct v'70 ** 
      HCurTCB ct ** 
      GV OSRunning @ Int8u |-> (V$ 1) ** 
      IntInv 
  ).
  intros.
  sep destruct H30.
  (*sep lifts (45::46::47::48::49::50::nil)%nat in H30.*)
  
  unfold AOSTCBPrioTbl in H30.
  unfold R_PrioTbl_P in H30.
  unfold_sep_cancel_helper.
  sep auto.
  sep lift 3%nat.
  sep lift 3%nat in H30.
  eapply tcbdllflag_hold.
  eauto.
  eauto.
  destructs H33;auto.
  hoare_split_pure_all.
  rename H30 into Hnodup.
  lets Hx:timetick_tcblist_p H21 H18 H19 H3 Hnodup.
  eapply tcbls_rtbl_timetci_update_len_eq;eauto.
  auto.
  auto.
  mytac.
  hoare lifts (3::nil)%nat pre.

  eapply abscsq_rule'.
  eapply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  unfold IntInv. can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.

  hoare forward.
  instantiate(1:=A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.
  instantiate (1:=(V$ 0)).
  unfold AOSTCBList'.
  sep normal.
  sep eexists.
  sep lift 8%nat.
  apply disj_split.
  right.
  unfold AOSTCBFreeList'.
  sep normal.
  sep eexists.
  sep lift 16%nat.
  apply disj_split.
  right.

  unfold AOSTCBFreeList' in H33.
  sep normal in H33.
  sep lift 38%nat in H33.
  apply disj_split in H33.
  destruct H33.
  unfold TCBFree_Not_Eq in H33.
  sep normal in H33.
  sep split in H33.
  tryfalse.
  unfold tcblist.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  unfold AOSIntNesting.
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  unfold TCB_Not_In in *.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel 1%nat 1%nat.
  sep cancel 6%nat 1%nat.

  eapply tcbfree_eq_tick_hold;eauto.
  sep cancel 1%nat 1%nat.
  eapply inv_prop2.tcbdllseg_compose; sep auto.
  eapply tickstep_rh_tcblist_ecblist_p;eauto.
  pauto.
  eapply tickstep_r_priotbl_p;eauto.
  eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'59 ++ v'60 :: v'61));eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H17. rewrite H17 in H19.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.

  eapply imp_rl_priotbl_p;eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H8;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  split;try eexists;eauto.
  eapply not_in_tcblist_tick_hold;eauto.

  eapply OSQPostPure2.TCBList_P_Combine;eauto.
  eapply OSQPostPure2.get_lasr_tcb_ptr_tick_hold;eauto.

  eapply tickstep_ecblist_p with (htls:=v'70) (ltls1:=v'59);eauto.
  sep split in H33. auto.
  sep split in H33. auto.
  sep split in H33. apply H35.
  auto. unfolds; eauto.

  clear -H4.
  unfold isr_is_prop in *.
  intros.
  apply H4 in H.
  unfold isrupd in *.
  destruct ( beq_nat 4 x);auto.
  go.

  intros.
  sep normal in H33.
  sep destruct H33.
  sep split in H33.
  inverts H34.
  apply disj_split in H33.
  destruct H33.
  sep split in H33; tryfalse.
  sep split in H33.
  clear H34.
  sep auto.
  intros.
  sep destruct H33.
  sep split in H33.
  
  inverts H34.
  apply disj_split in H33.
  destruct H33.
  sep split in H33; tryfalse.
  sep split in H33.
  clear H34.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  intros.
  inverts H33.
  sep lift 2%nat in H36.
  apply disj_split in H36.
  destruct H36.
  sep split in H33. tryfalse.
  sep normal in H33.
  apply astar_l_apure_elim in H33.
  destruct H33.
  clear H33.
  exact H36.
  hoare unfold.
  inverts H31.
  inverts H33.
  eapply iret_rule'.
  intros.
  apply disj_split. right.
  sep lift 7%nat in H31.
  apply disj_split in H31.
  destruct H31.
  unfold p_local in *.
  unfold OSLInv in *.
  unfold LINV in *.
  sep normal in H31.
  sep destruct H31.

  sep normal. exists x30.
  sep lift 9%nat.
  apply disj_split. right.
  unfold AGVars in *.
  sep normal in H31.
  sep destruct H31.
  sep normal.
  sep eexists.
  unfold A_isr_is_prop.
  sep auto.
  rewrite H49, H51. auto.
  sep split in H31. tryfalse.


  (*OSIntNesting != 1*)
  pure intro.
  clear H6.
  inversion H3.

  eapply backward_rule1.
  intros.
  sep lift 31%nat in H6.
  eapply disj_split in H6.
  destruct H6.
  sep split in H6.
  tryfalse.
  sep normal in H6.
  exact H6.
  pure intro.
  clear H6.
  eapply seq_rule.  
  hoare lifts (35::31::1::32::33::34::nil)%nat pre.
  eapply eoi_ieoff_rule'.
  simpl.
  rewrite Int.unsigned_repr.
  lia.
  rewrite max_unsigned_val.
  lia.
  instantiate (1:=4%nat).
  rewrite Int.unsigned_repr.
  simpl.
  auto.
  rewrite max_unsigned_val.
  lia.
  intros.
  
  exact H3.
  apply GoodI_I.  (*Good I*)
  (*unfold AOSRunning.
  unfold AIntNumCurrent.*)
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  go.

  (*OSTimeTick()*)
  unfold isflag in H5.
  destruct H5; subst v'25.
  eapply backward_rule1.
  intros.
  sep lifts (26::27::36::nil)%nat in H3.
  eapply inv_change_aux in H3.
  exact H3.
  unfold AOSTime.
  unfold AOSTCBList.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'33).
  sep lift 2%nat in H8.

  eapply dllseg_head_isptr';eauto.
  pure intro.
  unfold isptr in H8.
  destruct H8;tryfalse.
  destruct H8.
  hoare forward.
  sep cancel Aisr.
  sep cancel p_local.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Ais.
  sep cancel Aier.
  sep cancel 1%nat 1%nat.
  sep cancel AOSRdyTblGrp.
  sep cancel AECBList.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  exact H9.
  auto.
  eauto.
  eauto.
  eauto.
  auto.
  (*unfold AOSRunning.*)
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  go.
  intros.
  sep auto.
  intros.
  sep auto.
  hoare unfold.

  inverts H9.

  lets Hx:tickstep_exists' H.
  Import DeprecatedTactic.
  mytac.
  unfold tickisr.
  hoare lifts(6::36::37::38::nil)%nat pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absimp_tickisr;eauto.
  Require Import ios_int_tac2.
  can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.
  rewrite isrupd_true_false.
  lets Hx:tcbls_rtbl_timetci_update_decompose H20;mytac.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H9.
  lets Hx:tcbls_rtbl_timetci_update_tls_split H15 H12 H9.
  exact Hx.
  lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H20.
  mytac.
  lets Hx: timetick_update_prop H10 H11 H13 H14 H20;eauto.
  mytac.
  destruct H15.
  destruct a;subst.
  inverts e0.
  simpl in H17.
  subst.
  instantiate(1:=v'73).
  instantiate (2:=(Vptr v'61)).
  simpl app.
  apply TcbMod.join_emp_eq in H5;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  mytac.
  lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H20.

  eapply backward_rule1 with(
    [| R_Prio_No_Dup v'73 |] ** EX x8 : val,
    tcbdllseg (Vptr v'61) Vnull x8 (Vptr v'83) x1 **
    tcbdllseg (Vptr v'83) x8 v'69 Vnull (x2 :: x3) **
     <|| END None;; (isched;; END None ?? END None) ||>  **
    HECBList x0 **
    HTCBList x **
    HTime (v'67 +ᵢ  Int.one) **
    Aisr (isrupd v'21 4%nat false) **
    Aier (ierupd v'60 4%nat true) **
    Aie false **
    Ais (4%nat :: v'59) **
    Acs nil **
    GV OSTCBList @ OS_TCB ∗ |-> Vptr v'61 **
    GV OSEventList @ OS_EVENT ∗ |-> v'77 **
    evsllseg v'77 Vnull v'80 v'79 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr v'83 **
    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'70 **
    GV OSRdyGrp @ Int8u |-> Vint32 x7 **
    GV OSTime @ Int32u |-> Vint32 (v'67 +ᵢ  Int.one) **
    p_local OSLInv v'83 (logic_val (V$ 1) :: nil) **
    AOSTCBFreeList v'43 v'44 **
    tcbdllflag (Vptr v'61) (x1 ++x2 :: x3) **
    GV OSLockNesting @ Int32u |-> Vint32 v'57 **
    GV OSIntNesting @ Int32u |-> Vint32 v'56 **
    GV INT_MUX_H @ Int32u |-> Vint32 v'55 **
    GV INT_MUX_L @ Int32u |-> Vint32 v'54 **
    GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'53 **
    GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'52 **
    GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'51 **
    GV OSIntExitY @ Int8u |-> Vint32 v'50 **
    GV OSPrioCur @ Int8u |-> Vint32 v'49 **
    GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'48 **
    GV OSCtxSwCtr @ Int32u |-> Vint32 v'47 **
    GV OSPrioHighRdy @ Int8u |-> Vint32 v'46 **
    AOSEventFreeList v'27 **
    AOSQFreeList v'28 **
    AOSQFreeBlk v'29 ** 
    AOSMapTbl ** 
    AOSUnMapTbl ** 
    AOSTCBPrioTbl v'32 v'65 v'73 v'45 ** 
    HCurTCB v'83 ** 
    GV OSRunning @ Int8u |-> (V$ 1) ** 
    IntInv ** 
    A_dom_lenv nil
  ).
  intros.
  sep destruct H28.
  (*sep lifts (45::46::47::48::49::nil)%nat in H28.*)
  
  unfold AOSTCBPrioTbl in H28.
  unfold R_PrioTbl_P in H28.
  unfold_sep_cancel_helper.
  sep auto.
  sep lift 3%nat.
  sep lift 3%nat in H28.
  eapply tcbdllflag_hold.
  eauto.
  eauto.
  destructs H31;auto.
  hoare_split_pure_all.
  rename H28 into Hnodup.
  lets Hx:timetick_tcblist_p H20 H17 H18 H8 Hnodup.
  eapply tcbls_rtbl_timetci_update_len_eq;eauto.
  clear -H15.
  destruct H15;mytac;subst.
  inverts H0;simpl;auto.
  unfolds.
  destruct v'62;tryfalse.
  unfolds in H1;auto.
  auto.
  mytac.
  hoare lifts (3::nil)%nat pre.

  eapply abscsq_rule'.
  eapply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  unfold IntInv. can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.

  hoare forward.
  unfold AGVars.
  instantiate(1:=A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.

  sep normal.
  sep eexists.
  sep lifts (22::23::34::nil)%nat.
  apply inv_change_aux.
  unfold AOSTCBList.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  sep pauto.
  sep cancel tcbdllflag.
  sep auto.

  eapply tickstep_rh_tcblist_ecblist_p;eauto.
  pauto.
  eapply tickstep_r_priotbl_p;eauto.
  eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'62 ++ v'63 :: v'64));eauto.

  destruct H15.
  destruct a;subst.
  inverts e0.
  simpl in H17.
  subst.
  instantiate (2:=Vptr v'61).
  simpl app.
  apply join_emp_eq in H5; rewrite H5 in H18.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.

  eapply imp_rl_priotbl_p;eauto.

  destruct H15.
  destruct a;subst.
  inverts e0.
  simpl in H17.
  subst.
  instantiate (2:=Vptr v'61).
  simpl app.
  apply join_emp_eq in H5;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  eauto.
  eauto.
  auto.
  eapply tickstep_ecblist_p with (htls:=v'73) (ltls1:=v'62);eauto.
  unfolds.
  destruct v'62;eauto.
  destruct H15;mytac.
  inverts H39;auto.
  tryfalse.
  destruct H15;mytac;tryfalse.
  unfold V_OSTCBNext;auto.
  auto.
  sep split in H31. auto.
  sep split in H31. auto.
  sep split in H31. apply H33.
  auto. unfolds; auto.

  clear -H4.
  unfold isr_is_prop in *.
  intros.
  apply H4 in H.
  unfold isrupd in *.
  destruct ( beq_nat 4 x);auto.
  go.

  intros.
  sep normal in H31.
  sep destruct H31.
  sep split in H31.
  inverts H32.
  apply disj_split in H31.
  destruct H31.
  sep split in H31; tryfalse.
  sep split in H31.
  clear H32.
  sep auto.
  intros.
  sep destruct H31.
  sep split in H31.
  
  inverts H32.
  apply disj_split in H31.
  destruct H31.
  sep split in H31; tryfalse.
  sep split in H31.
  clear H32.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  intros.
  inverts H31.
  sep lift 2%nat in H34.
  apply disj_split in H34.
  destruct H34.
  sep split in H31. tryfalse.
  sep normal in H31.
  apply astar_l_apure_elim in H31.
  destruct H31.
  clear H31.
  exact H34.
  hoare unfold.
  inverts H29.
  inverts H31.
  eapply iret_rule'.
  intros.
  apply disj_split. right.
  sep lift 7%nat in H29.
  apply disj_split in H29.
  destruct H29.
  unfold p_local in *.
  unfold OSLInv in *.
  unfold LINV in *.
  sep normal in H29.
  sep destruct H29.

  sep normal. exists x30.
  sep lift 9%nat.
  apply disj_split. right.
  unfold AGVars in *.
  sep normal in H29.
  sep destruct H29.
  sep normal.
  sep eexists.
  unfold A_isr_is_prop.
  sep auto.
  rewrite H47, H49. auto.
  sep split in H29. tryfalse.
  
  pure intro.
  rewrite isrupd_true_false.
  (*current task dead*)
  hoare unfold.
  unfold AOSTCBList'.
  hoare lift 26%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H3.
  destruct H3.
  unfold p_local in H3.
  unfold CurTid in H3.
  sep normal in H3.
  sep destruct H3.
  unfold tcbdllseg in H3.
  unfold tcbdllflag in H3.
  sep lifts (4::1::nil)%nat in H3.
  sep split in H3.
  destruct H5;subst.
  eapply read_only_merge_vptr in H3.
  destruct H3.
  clear H17.
  sep lifts (3::4::5::34::nil)%nat in H3.
  apply task_del_noexists in H3.
  unfolds in H3;false.
  exact H3.

  unfold AOSTime.
  unfold tcblist.
  hoare unfold.
  unfold tcbdllseg at 1.
  hoare_assert_pure (isptr v'33).
  sep lift 3%nat in H6.
  eapply dllseg_head_isptr;eauto.
  pure intro.
  unfold isptr in H6.
  destruct H6;tryfalse.
  destruct H6.
  eapply backward_rule1.
  intros.
  sep lift 3%nat  in H7.
  unfold tcbdllseg in H7.
  unfold V_OSTCBPrev in H7.
  unfold V_OSTCBNext in H7.
  eapply tcbdllseg_split.
  unfold tcbdllseg.
  subst v'33.
  eauto.
  hoare unfold.
  lets Hx: OSQPostPure2.TCBList_P_Split H3.
  mytac.
  assert (x0= Vptr v'25).
  unfolds in H6.
  destruct v'35.
  inverts H6;auto.
  destruct H7;mytac;tryfalse;auto.
  destruct H7;mytac;tryfalse;auto.
  unfolds in H6.
  rewrite H6 in H11;inverts H11;auto.
  subst x0.
  clear H3.
  hoare forward.
  sep cancel p_local.
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Acs.
  sep cancel Ais.
  sep cancel Aier.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel 1%nat 1%nat.
  sep cancel AECBList.
  sep cancel AOSRdyTblGrp.
  exact H3.
  unfolds; auto.
  eauto.
  eauto.
  eauto.
  auto.
  unfold IntInv.
  good_frm_sovler'.
  intros.
  sep auto.
  sep auto.
  hoare unfold.
  inverts H3.

  lets Hx:tickstep_exists' H.
  
  mytac.
  unfold tickisr.

  hoare lifts(6::37::38::39::nil)%nat pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absimp_tickisr; eauto.
  pauto.
  unfold IntInv.
  can_change_aop_solver'.

  lets Hx:tcbls_rtbl_timetci_update_decompose H21;mytac.
  eapply backward_rule1.
  intros.
  sep lift 13%nat in H13.
  lets Hx:tcbls_rtbl_timetci_update_tls_split H16 H25 H13.
  exact Hx.
  lets Hx: tcbls_rtbl_timetci_update_rgrp_vint H21.
  mytac.
  lets Hx: timetick_update_prop H11 H12 H14 H15 H21;eauto.
  mytac.
  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (3:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H8. rewrite H8 in H19.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  mytac.
  lets Hy:tcbld_rtbl_timetci_update_tcbdllflag H21.

  eapply backward_rule1 with(
    [| R_Prio_No_Dup v'70 |] ** EX x8 : val,
    tcbdllseg (Vptr v'58) Vnull x8 (Vptr v'80) x1 **
    tcbdllseg (Vptr v'80) x8 v'66 Vnull (x2 :: x3) **
     <|| END None;; (isched;; END None ?? END None) ||>  **
    HECBList x0 **
    HTCBList x **
    HTime (v'64 +ᵢ  Int.one) **
    Aisr (isrupd v'33 4%nat false) **
    Aier (ierupd v'43 4%nat true) **
    Aie false **
    Ais (4%nat :: v'34) **
    Acs nil **
    GV OSTCBList @ OS_TCB ∗ |-> Vptr v'58 **
    GV OSEventList @ OS_EVENT ∗ |-> v'74 **
    evsllseg v'74 Vnull v'77 v'76 **
    GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
    GAarray OSRdyTbl (Tarray Int8u ∘ OS_RDY_TBL_SIZE) v'67 **
    GV OSRdyGrp @ Int8u |-> Vint32 x7 **
    GV OSTime @ Int32u |-> Vint32 (v'64 +ᵢ  Int.one) **
    p_local OSLInv ct (logic_val (V$ 0) :: nil) **
    TCB_Not_In (Vptr ct) (Vptr v'58) (v'59 ++ v'60 :: v'61) **
    tcbdllflag (Vptr v'58) (x1 ++x2 :: x3) **
    GV OSLockNesting @ Int32u |-> Vint32 v'57 **
    GV OSIntNesting @ Int32u |-> Vint32 v'56 **
    GV INT_MUX_H @ Int32u |-> Vint32 v'55 **
    GV INT_MUX_L @ Int32u |-> Vint32 v'54 **
    GV CGEM_regs_INTMUX3 @ Int32u |-> Vint32 v'53 **
    GV CGEM_regs_INTMUX2 @ Int32u |-> Vint32 v'52 **
    GV CGEM_regs_INTMUX1 @ Int32u |-> Vint32 v'51 **
    GV OSIntExitY @ Int8u |-> Vint32 v'50 **
    GV OSPrioCur @ Int8u |-> Vint32 v'49 **
    GV OSTCBHighRdy @ OS_TCB ∗ |-> Vptr v'48 **
    GV OSCtxSwCtr @ Int32u |-> Vint32 v'47 **
    GV OSPrioHighRdy @ Int8u |-> Vint32 v'46 **
    AOSEventFreeList v'27 **
    AOSQFreeList v'28 **
    AOSQFreeBlk v'29 **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl v'32 v'62 v'70 v'45 ** 
    AOSTCBFreeList' (Vptr ct) v'44 ct v'70 ** 
    HCurTCB ct ** 
    GV OSRunning @ Int8u |-> (V$ 1) ** 
    IntInv ** 
    A_dom_lenv nil
  ).
  intros.
  sep destruct H30.
  
  unfold AOSTCBPrioTbl in H30.
  unfold R_PrioTbl_P in H30.
  unfold_sep_cancel_helper.
  sep auto.
  sep lift 3%nat.
  sep lift 3%nat in H30.
  eapply tcbdllflag_hold.
  eauto.
  eauto.
  destructs H33;auto.
  hoare_split_pure_all.
  rename H30 into Hnodup.
  lets Hx:timetick_tcblist_p H21 H18 H19 H3 Hnodup.
  eapply tcbls_rtbl_timetci_update_len_eq;eauto.
  auto.
  auto.
  mytac.
  hoare lifts (3::nil)%nat pre.

  eapply abscsq_rule'.
  eapply noabs_oslinv.
  eapply absinfer_seq_end;eauto.
  unfold IntInv. can_change_aop_solver'.
  unfold IntInv. can_change_aop_solver'.

  hoare forward.
  unfold AGVars.
  instantiate(1:=A_dom_lenv nil).
  sep cancel Aisr.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.
  instantiate (1:=(V$ 0)).
  unfold AOSTCBList'.
  sep normal.
  sep eexists.
  sep lift 22%nat.
  apply disj_split.
  right.
  unfold AOSTCBFreeList'.
  sep normal.
  sep eexists.
  sep lift 30%nat.
  apply disj_split.
  right.

  unfold AOSTCBFreeList' in H33.
  sep normal in H33.
  sep lift 37%nat in H33.
  apply disj_split in H33.
  destruct H33.
  unfold TCBFree_Not_Eq in H33.
  sep normal in H33.
  sep split in H33.
  tryfalse.
  unfold tcblist.
  unfold AOSRdyTblGrp.
  unfold AOSRdyTbl.
  unfold AOSRdyGrp.
  unfold AOSTime.
  unfold AECBList in *.
  unfold AOSTCBPrioTbl in *.
  unfold TCB_Not_In in *.
  sep pauto.
  sep cancel tcbdllflag.
  sep cancel 1%nat 1%nat.
  sep cancel 6%nat 1%nat.

  eapply tcbfree_eq_tick_hold;eauto.
  sep cancel 1%nat 1%nat.
  eapply inv_prop2.tcbdllseg_compose; sep auto.
  eapply tickstep_rh_tcblist_ecblist_p;eauto.
  pauto.
  eapply tickstep_r_priotbl_p;eauto.  
  eapply tcbls_rtbl_timetci_update_rl_rtbl_priotbl_p with (a:=(v'59 ++ v'60 :: v'61));eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H17. rewrite H17 in H19.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.

  eapply imp_rl_priotbl_p;eauto.

  destruct H16.
  destruct a;subst.
  inverts e0.
  simpl in H18.
  subst.
  instantiate (2:=Vptr v'58).
  simpl app.
  apply TcbMod.join_emp_eq in H8;subst.
  eauto.
  eapply TCBList_merge_prop;eauto.
  mytac;subst.
  unfolds;auto.
  split;try eexists;eauto.
  eapply not_in_tcblist_tick_hold;eauto.

  eapply OSQPostPure2.TCBList_P_Combine;eauto.
  eapply OSQPostPure2.get_lasr_tcb_ptr_tick_hold;eauto.

  eapply tickstep_ecblist_p with (htls:=v'70) (ltls1:=v'59);eauto.
  sep split in H33. auto.
  sep split in H33. auto.
  sep split in H33. apply H35.
  auto. unfolds; eauto.

  clear -H4.
  unfold isr_is_prop in *.
  intros.
  apply H4 in H.
  unfold isrupd in *.
  destruct ( beq_nat 4 x);auto.
  go.

  intros.
  sep normal in H33.
  sep destruct H33.
  sep split in H33.
  inverts H34.
  apply disj_split in H33.
  destruct H33.
  sep split in H33; tryfalse.
  sep split in H33.
  clear H34.
  sep auto.
  intros.
  sep destruct H33.
  sep split in H33.
  
  inverts H34.
  apply disj_split in H33.
  destruct H33.
  sep split in H33; tryfalse.
  sep split in H33.
  clear H34.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  intros.
  inverts H33.
  sep lift 2%nat in H36.
  apply disj_split in H36.
  destruct H36.
  sep split in H33. tryfalse.
  sep normal in H33.
  apply astar_l_apure_elim in H33.
  destruct H33.
  clear H33.
  exact H36.
  hoare unfold.
  inverts H31.
  inverts H33.
  eapply iret_rule'.
  intros.
  apply disj_split. right.
  sep lift 7%nat in H31.
  apply disj_split in H31.
  destruct H31.
  unfold p_local in *.
  unfold OSLInv in *.
  unfold LINV in *.
  sep normal in H31.
  sep destruct H31.

  sep normal. exists x30.
  sep lift 9%nat.
  apply disj_split. right.
  unfold AGVars in *.
  sep normal in H31.
  sep destruct H31.
  sep normal.
  sep eexists.
  unfold A_isr_is_prop.
  sep auto.
  rewrite H49, H51. auto.
  sep split in H31. tryfalse.
Qed.