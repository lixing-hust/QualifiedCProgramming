Require Import ucos_include.
Require Import ios_int.
Require Import oscore_common.
Require Import ios_int_ipc.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import ios_int_tac.
Require Import Lia.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Lemma absimp_ipcisr:
forall P tls qls curtid tm s sch,
can_change_aop P ->
absinfer sch
          ( <||ipcisr_spec (|nil|) ;; s||> ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
          ( <||END None;;s ||> ** HECBList qls** HTCBList tls **  HTime tm ** HCurTCB curtid **P).
Proof.
intros.
apply absinfer_seq.
can_change_aop_solver.
can_change_aop_solver.
infer_solver 0%nat.
Qed.
Lemma ipc_isr_proof:
forall ir er si p r ct lg,
  Some p = BuildintPre 6 int_spec ir er si I OSLInv ct lg->
  Some r = BuildintRet 6 int_spec ir er si I OSLInv ct lg->
  exists s,
    os_interrupt OSIpcISR = Some s /\ {| OS_spec , GetHPrio, OSLInv, I, retfalse, r |} |-ct
    {{p}} s {{Afalse}}.
Proof.
    intros.
    (*Print OSLInv.*)
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
    eapply backward_rule1.
    intros.
    apply disj_split in H.
    destruct H.
    sep split in H.
    tryfalse.
    exact H.
    pure intro.
    clear H.

    unfold invlth_noisr.
    unfold starinv_noisr.
    simpl.
    unfold p_local.
    unfold LINV.
    unfold OSLInv.
    hoare unfold.

    rename v'15 into v15.
    rename v'16 into v16.
    rename v'17 into v17.
    rename v'18 into v18.
    rename v'19 into v19.
    rename v'20 into v'15.
    rename v'21 into v'16.
    rename v'22 into v'17.
    rename v'23 into v'18.
    rename v'24 into v'19.

    hoare forward.
    sep lift 11%nat.
    apply disj_split.
    right.
    instantiate (1:=A_dom_lenv nil).
    Focus 4.
    
    isr_is_prop_help (6%nat) (si) (ir).
    clear H12.
    sep lifts (1::2::44::nil)%nat in H15.
    apply a_isr_is_prop_split in H15.
    sep split in H15.
    apply H22.
    assert(ct = v'10).
    unfold CurTid, AOSTCBList' in H.
    sep lift 8%nat in H.
    apply disj_split in H.
    destruct H.
    sep normal in H. sep destruct H.
    sep lift 6%nat in H. sep split in H.
    destruct H7. rewrite H19 in H.
    
    sep lift 4%nat in H.
    eapply read_only_merge_vptr in H.
    destruct H. auto.
    sep normal in H. sep destruct H.
    sep lift 7%nat in H. sep split in H.
    destruct H7. rewrite H16 in H.
    sep lifts (1::3::nil)%nat in H.
    eapply read_only_merge_vptr in H.
    destruct H. auto.
    rewrite <- H7 in H. clear H7.
    sep lifts (18::19::13::nil)%nat in H.
    apply a_isr_is_prop_split in H.
    unfold p_local. unfold OSLInv.
    sep_cancel_unfold_solver.
    sep auto. apply H8.
    split;eauto.
  
    assert(ct = v'10).
    unfold CurTid, AOSTCBList' in H.
    sep lift 9%nat in H.
    apply disj_split in H.
    destruct H.
    sep normal in H. sep destruct H.
    sep lift 6%nat in H. sep split in H.
    destruct H7. rewrite H19 in H.
    sep lift 4%nat in H.
    eapply read_only_merge_vptr in H.
    destruct H. auto.
  
    sep normal in H. sep destruct H.
    sep lift 7%nat in H. sep split in H.
    destruct H7. rewrite H16 in H.
    sep lift 3%nat in H.
    eapply read_only_merge_vptr in H.
    destruct H. auto.
    rewrite H7. auto.
    auto. auto. good_frm_better_sovler.
    intros.
    sep auto.
    intros.
    sep auto.
    hoare unfold.

    rename v'45 into v45.
    rename v'46 into v46.
    rename v'47 into v47.
    rename v'48 into v'45.
    rename v'49 into v49.
    rename v'50 into v50.
    
    unfold AGVars.
    hoare forward.
    destruct (Int.eq v'56 (Int.repr 1)); auto.
    hoare forward.
    eapply disj_rule.
    pure intro.
    rename H10 into Hx. rename H11 into Hy.
    clear  H12 H13 H14 H15 H16 H17.
    inverts H7.
    
    (* Ltac tmp1 := 
      do 5 try (apply rvl_elim;[ symbolic_execution | ]);
                           first [apply rvl_nil | simpl;auto].
    eapply seq_rule.
    eapply call_rule'.
    instantiate(4:=OSIpc1Pre).
    eauto.
    intuition eauto.
    intros.
    tmp1.
    intros. unfold_spec. sep pauto. *)

    hoare forward.
    sep lift 34%nat in H7.
    apply disj_split in H7. destruct H7.
    sep split in H7. tryfalse.
    sep lift 20%nat.
    apply disj_split. right.
    instantiate(9:=6%nat).
    instantiate(1:=A_dom_lenv nil).
    unfold_sep_cancel_helper.

    sep semiauto; eauto.
    auto.
    auto. auto. good_frm_better_sovler.
    intros. sep auto.
    intros. sep auto.
    unfold OSIpc1Post.
    unfold OSIpc1Post'.
    unfold getasrt.
    pure intro.
    
    rename v'76 into v76.
    rename v'77 into v77.
    rename v'78 into v78.
    rename v'79 into v'76.
    rename v'80 into v80.
    rename v'81 into v81.

    eapply backward_rule1.
    intros.
    sep normal in H13.
    sep lift 20%nat in H13.
    apply disj_split in H13. destruct H13.
    sep split in H13.
    inverts H14. tryfalse.
    exact H13.
    unfold IntInv.
    unfold EvtInv.
    pure intro.
    clear H21.

    inverts H10.
    hoare_abscsq.
    apply noabs_oslinv.
    unfold ipcisr.
    apply absimp_ipcisr.
    can_change_aop_solver'.
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply absinfer_seq_end;eauto.
    can_change_aop_solver'.
    can_change_aop_solver'.
    eapply seq_rule.
    eapply eoi_ieoff_rule'.
    unfold INUM.
    simpl.
    rewrite Int.unsigned_repr.
    lia.
    rewrite max_unsigned_val.
    lia.
    auto.
    intros.
    sep lifts (49::35::50::51::52::nil)%nat in H10.
    assert(Z.to_nat (Int.unsigned ($ 6)) = 6%nat) by auto.
    rewrite H14.
    clear H14.
    exact H10.
    apply GoodI_I.
    good_frm_sovler'.
    hoare forward.
    sep lift 2%nat. apply disj_split. right.
    sep lift 8%nat. apply disj_split. left.
    sep normal in H10. sep destruct H10.
    unfold IntInv.
    unfold EvtInv.
    sep normal. sep eexists.
    unfold_sep_cancel_helper.
    instantiate(1:= A_dom_lenv nil).
    sep semiauto; eauto.
    auto.
    rewrite  isrupd_true_false.
    assert((Z.to_nat (Int.unsigned ($ 6)) = (6%nat))) by auto.
    rewrite H27.
    clear -H11.
    unfold isr_is_prop in *.
    intros.
    apply H11 in H.
    unfold isrupd in *.
    destruct ( beq_nat 6 x);auto.
    good_frm_sovler'.
    intros. sep auto.
    intros. sep auto.
    unfold OSIntExitIntPost.
    unfold OSIntExitPost_int .
    unfold getasrt.
    pure intro.
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H22.
    apply disj_split in H22.
    destruct H22.
    sep lift 4%nat in H22.
    apply disj_split in H22.
    destruct H22.
    inverts H10.
    sep split in H22. tryfalse.
    exact H22.
    sep normal in H22. sep split in H22.
    apply astar_l_afalse_elim in H22.
    simpl in H22.
    tryfalse.

    eapply iret_rule'.
    intros.
    inverts H10.
    sep normal. sep eexists.
    sep lift 7%nat.
    apply disj_split. right.
    sep lift 13%nat.
    apply disj_split. right.
    unfold A_isr_is_prop.
    unfold p_local in H22.
    unfold OSLInv in H22.
    unfold LINV in H22.
    unfold AGVars in H22.
    unfold IntInv in H22.
    unfold EvtInv in H22.
    sep normal in H22. sep destruct H22. 
    
    rename x13 into xx13.
    rename x14 into xx14.
    rename x15 into xx15.
    rename x16 into x13.
    rename x17 into xx17.
    rename x18 into xx18.
    rename x19 into x14.
    rename x20 into x15.
    rename x21 into x16.
    rename x22 into x17.
    rename x23 into x18.
    rename x24 into x19.
    rename x25 into x20.
    rename x26 into x21.
    rename x27 into x22.
    rename x28 into x23.
    rename x29 into x24.
    rename x30 into x25.
    rename x31 into x26.
    rename x32 into x27.
    rename x33 into x28.
    rename x34 into x29.
    rename x35 into x30.

    rename x36 into x31.
    rename x37 into x32.
    rename x38 into x33.
    rename x39 into x34.
    rename x40 into x35.
    rename x41 into x36.
    rename x42 into x37.
    rename x43 into x38.
    rename x44 into x39.
    rename x45 into x40.

    rename x46 into x41.
    rename x47 into x42.
    rename x48 into x43.
    rename x49 into x44.
    rename x50 into x45.
    rename x51 into x46.
    rename x52 into x47.
    rename x53 into x48.
    rename x54 into x49.
    rename x55 into x50.
    rename x56 into x51.
    rename x57 into x52.
    rename x58 into x53.

    sep split in H22.
    unfold IntInv.
    sep normal. sep eexists. sep split.
    sep_cancel_unfold_solver.
    destruct H10. inversion e.
    rewrite <- H45 in H22.
    rewrite <- H45.
    clear H45 H46 H47 H48 H49.
    sep auto.
    auto. 
    auto. 
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto. substs. auto.
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto.
    rewrite H44 in H38. rewrite isrupd_true_false in H38. auto.
    auto. 
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto. substs. auto.
    auto. auto. auto.
    sep auto.
    auto. auto. auto.
    auto. auto. split; auto.
    auto. auto. auto. auto. auto. auto. auto. auto.
    auto. auto. auto. auto. auto. rewrite H38, H40. auto.

    pure intro.
    rename H10 into Hx. rename H11 into Hy.
    clear  H12.
    inverts H7.
    hoare forward.
    sep lift 33%nat in H7.
    apply disj_split in H7. destruct H7.
    sep split in H7. tryfalse.
    sep lift 20%nat.
    apply disj_split. right.
    instantiate(9:=6%nat).
    instantiate(1:=A_dom_lenv nil).
    unfold_sep_cancel_helper.
    sep semiauto; eauto.
    auto.
    auto. auto. good_frm_better_sovler.
    intros. sep auto.
    intros. sep auto.
    unfold OSIpc1Post.
    unfold OSIpc1Post'.
    unfold getasrt.
    pure intro.

    rename v'76 into v76.
    rename v'77 into v77.
    rename v'78 into v78.
    rename v'79 into v'76.
    rename v'80 into v80.
    rename v'81 into v81.

    eapply backward_rule1.
    intros.
    sep normal in H13.
    sep lift 20%nat in H13.
    apply disj_split in H13. destruct H13.
    sep split in H13.
    inverts H14. tryfalse.
    exact H13.
    unfold IntInv.
    unfold EvtInv.
    pure intro.
    clear H21.
    inverts H10.
    hoare_abscsq.
    apply noabs_oslinv.
    unfold ipcisr.
    apply absimp_ipcisr.
    can_change_aop_solver'.
    eapply abscsq_rule'.
    apply noabs_oslinv.
    eapply absinfer_seq_end;eauto.
    can_change_aop_solver'.
    can_change_aop_solver'.
    eapply seq_rule.
    eapply eoi_ieoff_rule'.
    unfold INUM.
    simpl.
    rewrite Int.unsigned_repr.
    lia.
    rewrite max_unsigned_val.
    lia.
    auto.
    intros.
    sep lifts (49::35::50::51::52::nil)%nat in H10.
    assert(Z.to_nat (Int.unsigned ($ 6)) = 6%nat) by auto.
    rewrite H14.
    clear H14.
    exact H10.
    apply GoodI_I.
    good_frm_sovler'.
    hoare forward.
    sep lift 2%nat. apply disj_split. right.
    sep lift 8%nat. apply disj_split. left.
    sep normal in H10. sep destruct H10.
    unfold IntInv.
    unfold EvtInv.
    sep normal. sep eexists.
    unfold_sep_cancel_helper.
    instantiate(1:= A_dom_lenv nil).
    sep semiauto; eauto.
    auto.
    rewrite  isrupd_true_false.
    assert((Z.to_nat (Int.unsigned ($ 6)) = (6%nat))) by auto.
    rewrite H27.
    clear -H11.
    unfold isr_is_prop in *.
    intros.
    apply H11 in H.
    unfold isrupd in *.
    destruct ( beq_nat 6 x);auto.
    good_frm_sovler'.
    intros. sep auto.
    intros. sep auto.
    unfold OSIntExitIntPost.
    unfold OSIntExitPost_int .
    unfold getasrt.
    pure intro.
    eapply backward_rule1.
    intros.
    sep lift 7%nat in H22.
    apply disj_split in H22.
    destruct H22.
    sep lift 4%nat in H22.
    apply disj_split in H22.
    destruct H22.
    inverts H10.
    sep split in H22. tryfalse.
    exact H22.
    sep normal in H22. sep split in H22.
    apply astar_l_afalse_elim in H22.
    simpl in H22.
    tryfalse.

    eapply iret_rule'.
    intros.
    inverts H10.
    sep normal. sep eexists.
    sep lift 7%nat.
    apply disj_split. right.
    sep lift 13%nat.
    apply disj_split. right.
    unfold A_isr_is_prop.
    unfold p_local in H22.
    unfold OSLInv in H22.
    unfold LINV in H22.
    unfold AGVars in H22.
    unfold IntInv in H22.
    unfold EvtInv in H22.
    sep normal in H22. sep destruct H22. 

    rename x13 into xx13.
    rename x14 into xx14.
    rename x15 into xx15.
    rename x16 into x13.
    rename x17 into xx17.
    rename x18 into xx18.
    rename x19 into x14.
    rename x20 into x15.
    rename x21 into x16.
    rename x22 into x17.
    rename x23 into x18.
    rename x24 into x19.
    rename x25 into x20.
    rename x26 into x21.
    rename x27 into x22.
    rename x28 into x23.
    rename x29 into x24.
    rename x30 into x25.
    rename x31 into x26.
    rename x32 into x27.
    rename x33 into x28.
    rename x34 into x29.
    rename x35 into x30.

    rename x36 into x31.
    rename x37 into x32.
    rename x38 into x33.
    rename x39 into x34.
    rename x40 into x35.
    rename x41 into x36.
    rename x42 into x37.
    rename x43 into x38.
    rename x44 into x39.
    rename x45 into x40.

    rename x46 into x41.
    rename x47 into x42.
    rename x48 into x43.
    rename x49 into x44.
    rename x50 into x45.
    rename x51 into x46.
    rename x52 into x47.
    rename x53 into x48.
    rename x54 into x49.
    rename x55 into x50.
    rename x56 into x51.
    rename x57 into x52.
    rename x58 into x53.
    
    sep split in H22.
    unfold IntInv.
    sep normal. sep eexists. sep split.
    sep_cancel_unfold_solver.
    destruct H10. inversion e.
    rewrite <- H45 in H22.
    rewrite <- H45.
    clear H45 H46 H47 H48 H49.
    sep auto.
    auto. 
    auto. 
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto. substs. auto.
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto.
    rewrite H44 in H38. rewrite isrupd_true_false in H38. auto.
    auto. 
    assert(Z.to_nat (Int.unsigned ($ 6)) = (6%nat)) by auto. substs. auto.
    auto. auto. auto.
    sep auto.
    auto. auto. auto.
    auto. auto. split; auto.
    auto. auto. auto. auto. auto. auto. auto. auto.
    auto. auto. auto. auto. auto. rewrite H38, H40. auto.
    Unshelve.
    all :exact spec_abort.
Qed.