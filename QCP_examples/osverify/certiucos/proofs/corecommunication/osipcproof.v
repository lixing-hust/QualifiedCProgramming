Require Import ucos_include.
Require Import Lia.

Require Import sem_lab.
Require Import ternary_assignment.

Require Import aux_pureLib.
Require Import corecommu_rules.
Require Import corecommu_tactics.
Require Import corecommu_sep_added.
Require Import corecommu_SemPtr_assign_rules.
Require Import sem_corecommu.

Require Import osipc_abs_rules.
Require Import osipcproofRules.

Open Scope code_scope.

Open Scope int_scope.

Lemma OSIpc_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSIpc vl logicl OS_IpcPre ct->
      Some r =
      BuildRetI os_internal OSIpc vl logicl OS_IpcPost ct->
      exists t d1 d2 s,
        os_internal OSIpc = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'27 into v27.
  rename v'28 into v28.
  rename v'29 into v29.

  rename v'30 into v'27. 
  rename v'31 into v'28. 
  rename v'32 into v'29. 
  rename v'33 into v'30. 
  rename v'34 into v'31. 

  inverts H9.
  rename v'2 into isr.
  rename v'3 into ier.
  rename v'4 into is.
  rename v'5 into i.
  rename v'6 into s.
  rename v'17 into ipcgr_val.
  rename v'9 into corenum_val.
  rename v'10 into eid.
  rename v'11 into v_ret.
  rename v'18 into cfglp.
  clear H10 H11.
  unfold OSIPC_aspec.
  cbn [spec_code_cons].
  pure intro.
  (* read_ipcgr ′ =ₑ ∗ iIPCGRInfo ′;ₛ *)
  unfold AOSIPCGRinfo.
  hoare forward.
  (* CLEARIPC (〈 Int8u 〉 ′ DNUM, read_ipcgr ′);ₛ *)
  hoare name lift p_local pre. hoare name lift read_ipcgr pre. 
  hoare name lift ipcgrid pre. hoare name lift (PV ipcgr_addr @ long |-> Vint32 ipcgr_val) pre.
  hoare name lift iIPCGRInfo pre. hoare name lift Aop pre.  
  eapply seq_rule.
  eapply OSIpc_proofPart0.
  { can_change_aop_solver. unfold can_change_aop. auto. }
  (* corenum ′ =ᶠ OS_getCoreIPC (·read_ipcgr ′·);ₛ *)
  rename H4 into RLHrecvh. 
  destruct H5 as [? H5].
  hoare name lift (LV read_ipcgr @ Int32u |-> Vint32 ipcgr_val) pre.
  hoare name lift (LV corenum @ long |-> v'1) pre.
  hoare lifts (3::8::9::10::11::12::7::nil)%nat pre.
  eapply seq_rule.
  eapply OSIpc_proofPart1;eauto.
  go.
  (*If (corenum ′ ==ₑ ′ (-1)){RETURN};ₛ*)
  hoare forward.
  pauto.
  - (* branch yes *)
    pure intro.
    assert (Int.eq corenum_val ($ -1) = true ) by pauto.
    hoare remember (1::nil)%nat pre.
    hoare abscsq.
    apply noabs_oslinv.
    { assert (can_change_aop H13). { subst H13;can_change_aop_solver. simpl. auto. }
    instantiate (1:= <|| s ||>  ** H13).
    eapply absinfer_trans with (q:= <|| END None;;s ||>  ** H13).
    eapply absinfer_trans.
    apply absinfer_choice1;eauto.
    eapply absinfer_seq;auto.
    apply absinfer_assume;auto.
    apply absinfer_seq_end;auto. }
    hoare forward.
    sep auto.
    all : auto.
    eexists. eauto.
  - (*end If*)
    hoare forward.
    pure intro.
    assert (Int.eq corenum_val ($ -1) = false).
    { destruct (Int.eq corenum_val ($ -1));auto.
      destruct H9;tryfalse. } 
    assert ( corenum_val = $ 0 \/  corenum_val = $ 1
      \/ corenum_val = $ 2 \/ corenum_val = $ 3
      \/ corenum_val = $ 4 \/ corenum_val = $ 5
      \/ corenum_val = $ 6 \/ corenum_val = $ 7).
      {clear - H4 H10.
      repeat (match goal with 
      | H : _ \/ _  |- _ => destruct H 
      | H : _ /\ _  |- _ => destruct H
      | H : corenum_val = _ |- _ => subst corenum_val;try tauto
      end). tryfalse. }
    assert (Int.eq corenum_val ($ DNUM) = false) as H4_.
    { clear - H4 H10. pose proof dnum_range.
    repeat (match goal with 
    | H : _ \/ _  |- _ => destruct H 
    | H : _ /\ _  |- _ => destruct H
    | H : corenum_val = _ |- _ => subst corenum_val;apply Inteq_false_is_Zneq;
                                  do 2 rewrite Int.unsigned_repr by mauto;auto
    end).  }
    (* IF ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_RDY) ==ₑ ′ IPC_MESSAGE_RDY) *)
    hoare forward.
    pauto.
    + (* branch yes (rdy) *)
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_RDY) ($ IPC_MESSAGE_RDY) = true) by pauto.
      apply Int_eq_dec in H15.
      instantiate (1:= Afalse).
      hoare remember (1::nil)%nat pre.
      hoare abscsq.
      apply noabs_oslinv.
      { assert (can_change_aop H16). { subst H16;can_change_aop_solver. simpl;auto. }
      instantiate (1:= <|| spec_code_cons (sem_post_ipc (Vptr eid :: v_ret :: nil)) s ||>  ** H16).
      eapply absinfer_trans with (q:= <|| END None ;; spec_code_cons (sem_post_ipc (Vptr eid :: v_ret :: nil)) s  ||>  ** H16).
      eapply absinfer_trans.
      apply absinfer_choice2;eauto.
      eapply absinfer_trans.
      apply absinfer_choice1;eauto.
      eapply absinfer_seq;auto.
      apply absinfer_assume;auto.
      apply absinfer_seq_end;auto. }
      subst H16.
      (* OSIPCSemPost (­ IPCSem ′ [corenum ′]­);ₛ *)
      hoare name lift AOSIPCSem pre.
      unfold AOSIPCSem.
      pure intro.
      assert (Z.to_nat (Int.unsigned corenum_val) <= 7)%nat. { clear - H11. mauto. }
      assert (exists p, nth_val' (Z.to_nat (Int.unsigned corenum_val)) IPCSem_ptrl = Vptr p /\ In (Vptr p) IPCSem_ptrl).
      { eapply isptr_list_nth_ptr_ex;eauto. lia. }
      destruct H19 as [? [? ?]].
      destruct H5 as [ [_ ?] | [? _] ].
      2: { contradiction. }
      assert (x0 = eid). 
      { apply nth_val'_imp_nth_val_vptr in H19.
        apply nth_val_nth_error in H19.
        unfold IPCSem_ptrl in H19. 
        apply map_nth_error with (f:= (fun x : addrval => Vptr x))  in H5.
        rewrite H5 in H19. inversion H19. subst. auto. }
      subst x0.
      eapply seq_rule.
      eapply call_rule';
      [ intuition eauto|  |
        intros;unfold_spec |
       idtac | sep_unfold_funpost  | 
       sep_unfold_funpre |
       simpl;eauto ] .
      { intros;(apply rvl_elim;[ symbolic_execution | ]);
       first [apply rvl_nil | simpl;auto].
       rewrite H19. auto. }
      { unfold A_isr_is_prop;sep normal;sep eexists.
        sep lift 4%nat in H21. 
        eapply astar_mono in H21. 3: {intros s' hs'; exact hs'. }
        2: { instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
             intros. 
             destruct H22. 
             sep split in H22. subst i. cbn [Nat.eqb]. auto. 
             sep split in H22. destruct ((i =? 1)%nat) eqn:?;[ | auto ]. apply beq_nat_true in Heqb. lia. }
        sep_pauto'.
        2: { rewrite H19. simpl (((Vptr eid :: nil) ++_ :: nil)). eauto. }
        2: auto.
        2: { cbn. eauto. }
        2: { unfold isr_is_prop in *. auto. }  
        eapply disj_split.
        apply adisj_intro. right.
        sep normal. sep eexists. sep pauto.
        sep cancel EvtInv. sep cancel AOSRdyTblGrp.
        sep cancel AOSTCBPrioTbl. sep cancel AOSTCBList.  exact H21.  
        auto.
        eexists. eauto.
        auto. }
      go. 
      { intros. 
        exists init_lg. sep auto. }
      { intros. 
        exists init_lg. sep auto. }
      { rewrite H19. auto. }
      unfold OSIPCSemPostPost, getasrt, OSIPCSemPostPost'.
      hoare normal pre. pure intro.
      eapply backward_rule1.
      { intros.
        sep lift 11%nat in H21.
        eapply disj_split in H21.
        destruct H21.
        { exfalso. sep split in H21.
          rewrite H19 in H22. inversion H22. }
        sep normal in H21.
        exact H21. }
      pure intro.
      inversion H27. subst. clear H27.  
      unfold A_isr_is_prop.
      (* RETURN *)
      eapply ret_rule. intros.
      sep normal. sep eexists.
      sep lift 3%nat.  eapply astar_mono.
      { instantiate (1:= i). instantiate (1:= ier).
        instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
        intros. 
        destruct ((i =? 1)%nat) eqn:?. 
        left. sep autocancel. sep auto. apply beq_nat_true in Heqb. auto.  
        right.  sep autocancel. sep auto. unfold not. intros. subst i. rewrite Nat.eqb_refl in Heqb. discriminate. }
      2:{ sep cancel Aier. exact H27. }
      intros. 
      sep autocancel.
      sep auto.
      unfold DynamicRefactorINV in *. 
      sep destruct H28. sep eexists.
      sep autocancel. sep auto.
      { destruct H29 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
        subst. auto.
        subst. auto.
        { subst. unfold is_que in *. 
          erewrite EcbMod.set_sem. 
          destruct (tidspec.beq v'2 dynrefcmsgQ_addr) eqn:?;auto.
          { exfalso. apply tidspec.beq_true_eq in Heqb.
            destruct H32 as [? [? [? [? ?]]]]. 
            subst. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x6 x7 x8, x9))by auto.
            rewrite H29 in H34.
            inverts H34. } }
        destruct H29 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
        subst. unfold is_que in *.
        erewrite EcbMod.set_sem. 
        destruct (tidspec.beq v'2 dynrefcmsgQ_addr) eqn:?;auto.
        { exfalso. apply tidspec.beq_true_eq in Heqb.
          destruct H32 as [? [? [? [? ?]]]]. 
          subst. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x12 x13 x14, x15))by auto.
          rewrite H29 in H36.
          inverts H36. } }
      eexists. eauto.
      { destruct H29 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
        subst. auto.
        subst. auto.
        subst. apply CORESEM_INECB_P_set_issem. auto.
        destruct H29 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
        subst. apply CORESEM_INECB_P_set_issem. auto. }
    + (* enter else branch (IF ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_RDY) !=ₑ ′ IPC_MESSAGE_RDY)) *)
      pure intro.
      instantiate (1:= Afalse).
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_RDY) ($ IPC_MESSAGE_RDY) = false).
      {  clear - H12. destruct (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_RDY) ($ IPC_MESSAGE_RDY));auto. simpl in H12. 
      destruct H12;tryfalse. }
      destruct H5 as [ [? ?] | [? H5] ].
      rewrite H5 in H13. rewrite Int.eq_true in H13. tryfalse.
      (* IF ((read_ipcgr ′ &ₑ ′ REFACTOR_RDY) ==ₑ ′ REFACTOR_RDY) *)
      eapply forward_rule2; [ hoare_forward_first
                          |  ].
      pauto.
      ++ (* branch yes (IF ((read_ipcgr ′ &ₑ ′ REFACTOR_RDY) ==ₑ ′ REFACTOR_RDY))*)
      pure intro. instantiate (1:= Afalse).
      assert (Int.eq (ipcgr_val&ᵢ$ REFACTOR_RDY) ($ REFACTOR_RDY) = true ) by pauto.
      apply Int_eq_dec in H18.
      destruct H5 as [ [_ H5] | [? _] ].
      2: contradiction.
      (* choose abs step *)
      hoare remember (1::nil)%nat pre.
      hoare abscsq.
      apply noabs_oslinv.
      { assert (can_change_aop H19). { subst H19;can_change_aop_solver. simpl;auto. }
      instantiate (1:= <||  spec_code_cons (doRefactorISR_aspec ((Vint32 corenum_val :: nil) ++ cfglp :: v_ret :: nil)) s||>  ** H19).
      eapply absinfer_trans with (q:= <|| spec_code_cons (doRefactorISR_aspec ((Vint32 corenum_val :: nil) ++ cfglp :: v_ret :: nil)) s  ||>  ** H19).
      eapply absinfer_trans.
      apply absinfer_choice2;eauto.
      eapply absinfer_trans.
      apply absinfer_choice2;eauto.
      apply absinfer_choice1;eauto.
      apply absinfer_eq. }
      subst H19.
      (* doRefactorISR (­ corenum ′­);ₛ *)
      eapply seq_rule.
      eapply call_rule';
      [ intuition eauto|  |
        intros;unfold_spec |
       idtac | sep_unfold_funpost  | 
       sep_unfold_funpre |
       simpl;eauto ] .
      { intros. apply rvl_elim. symbolic_execution. apply rvl_nil. }
      { unfold A_isr_is_prop. sep normal. sep eexists. 
        sep lift 3%nat in H19. 
        eapply astar_mono in H19. 3: {intros s' hs'; exact hs'. }
        2: { instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
            intros. 
            destruct H20. 
            sep split in H20. subst i. cbn [Nat.eqb]. auto. 
            sep split in H20. destruct ((i =? 1)%nat) eqn:?;[ | auto ]. apply beq_nat_true in Heqb. lia. }
        sep_pauto''. sep autocancel. sep split. exact H19.
        3: reflexivity.
        all: auto. }
      go.
      { intros. exists init_lg. sep auto. }
      { intros. exists init_lg. sep auto. }
      simpl;auto.
      unfold doRefactorISRPost, getasrt, doRefactorISRPost'.
      hoare normal pre.
      pure intro.
      rename v'43 into v43.
      rename v'44 into v44.
      rename v'45 into v45.

      rename v'46 into v'43. 
      rename v'47 into v'44. 
      rename v'48 into v'45. 
      rename v'49 into v'46. 
      rename v'50 into v'47. 
      rename v'51 into v'48. 

      rename v'53 into v'50. 
      rename v'54 into v'51. 
      rename v'55 into v'52. 
      rename v'56 into v'53. 
      rename v'57 into v'54. 
      rename v'58 into v'55. 
      rename v'59 into v'56. 
    

      inversion H23. subst. clear H23. inversion H24. clear H24. subst v'4.
      (* RETURN *)
      eapply ret_rule. intros.
      sep normal. sep eexists.
      sep lift 3%nat.  eapply astar_mono.
      { instantiate (1:= i). instantiate (1:= ier).
        instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
        intros. 
        destruct ((i =? 1)%nat) eqn:?. 
        left. sep autocancel. sep auto. apply beq_nat_true in Heqb. auto.  
        right.  sep autocancel. sep auto. unfold not. intros. subst i. rewrite Nat.eqb_refl in Heqb. discriminate. }
      2:{ sep cancel Aier. exact H5. }
      intros. sep normal in H21. sep destruct H21.
      sep_pauto''. sep autocancel.
      sep split;auto.
      { unfold A_isr_is_prop in H21.
        sep destruct H21.
        sep split in H21. auto. }
      eexists. eauto.
      { destruct H22 as [[? [? [? [? [? [? _ ]] ]]]] |  [[? [? [? [? [? [? _ ]] ]]]] | ]]. 
        subst. auto.
        { subst. apply CORESEM_INECB_P_set_notsem; auto.
        unfold not;intros. destruct H30 as [? [? ?]].
        assert (EcbMod.get v'32 dynrefcmsgQ_addr = Some (abssem x3, x4)) by auto.
        rewrite H33 in H22. inversion H22. }
        destruct H22 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  & ? & ? & ?  &  _).
        subst. apply CORESEM_INECB_P_set_notsem; auto.
        unfold not;intros. destruct H30 as [? [? ?]].
        assert (EcbMod.get v'32 dynrefcmsgQ_addr = Some (abssem x10, x11)) by auto.
        rewrite H35 in H22. inversion H22. }
      ++(*enter else branch (IF ((read_ipcgr ′ &ₑ ′ REFACTOR_RDY) !=ₑ ′ REFACTOR_RDY)) *)
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ REFACTOR_RDY) ($ REFACTOR_RDY) = false).
      { clear -H15. destruct (Int.eq (ipcgr_val&ᵢ$ REFACTOR_RDY)
      ($ REFACTOR_RDY));auto. destruct H15;tryfalse. }
      clear H15.
      destruct H5 as [ [? _] | [? H5]].
      apply semacc_int_eq_false in H16. false.
      (* IF ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_ACK) ==ₑ ′ IPC_MESSAGE_ACK)*)
      (* enter ack broad *) 
      hoare forward. pauto.
      +++ (* branch yes (IF ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_ACK) ==ₑ ′ IPC_MESSAGE_ACK))*)
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_ACK) ($ IPC_MESSAGE_ACK) = true ) by pauto.
      apply Int_eq_dec in H20.
      destruct H5 as [ [_ ?] | [? _] ].
      2: contradiction.
      instantiate (1:= Afalse).
      hoare name lift AOSIPCSendSem pre.
      unfold AOSIPCSendSem.
      pure intro.
      assert (exists p, nth_val' (Z.to_nat (Int.unsigned corenum_val)) IPCSendSem_ptrl = Vptr p /\ In (Vptr p) IPCSendSem_ptrl).
      { eapply isptr_list_nth_ptr_ex;eauto.
        clear - H11. mauto.  }
      destruct H23 as [? [? ?]].
      (* absop : choose ASSUME .. ;; OSIPCSemPost_spec eid*)
      hoare remember (2::nil)%nat pre.
      hoare abscsq.
      apply noabs_oslinv.
      { assert (can_change_aop H25). { subst H25;can_change_aop_solver. cbn. auto. }
      instantiate (1:= <|| spec_code_cons (sem_post_ipc (Vptr eid :: v_ret :: nil)) s ||>  ** H25).
      eapply absinfer_trans with (q:= <|| END None ;;spec_code_cons (sem_post_ipc (Vptr eid :: v_ret :: nil)) s ||>  ** H25).
      eapply absinfer_trans.
      apply absinfer_choice2;eauto.
      eapply absinfer_trans.
      apply absinfer_choice1;eauto.
      eapply absinfer_seq;auto.
      apply absinfer_assume;auto.
      apply absinfer_seq_end;auto. } 
      subst H25.
      (* OSIPCSemPost (­ IPCSendSem ′ [corenum ′]­);ₛ *)
      assert (Z.to_nat (Int.unsigned corenum_val) <= 7)%nat. { clear - H11. mauto. }
      assert (x0 = eid). 
      { apply nth_val'_imp_nth_val_vptr in H23.
        apply nth_val_nth_error in H23.
        unfold IPCSendSem_ptrl in H23. 
        apply map_nth_error with (f:= (fun x : addrval => Vptr x))  in H5.
        rewrite H5 in H23. inversion H23. subst. auto. }
      subst x0.
      eapply seq_rule.
      eapply call_rule';
      [ intuition eauto|  |
        intros;unfold_spec |
       idtac | sep_unfold_funpost  | 
       sep_unfold_funpre |
       simpl;eauto ] .
      { intros; (apply rvl_elim;[ symbolic_execution | ]);
       first [apply rvl_nil | simpl;auto].
       rewrite H23. auto. }
      { unfold A_isr_is_prop;sep normal;sep eexists.
        sep lift 4%nat in H26. 
        eapply astar_mono in H26. 3: {intros s' hs'; exact hs'. }
        2: { instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
             intros. 
             destruct H27. 
             sep split in H27. subst i. cbn [Nat.eqb]. auto. 
             sep split in H27. destruct ((i =? 1)%nat) eqn:?;[ | auto ]. apply beq_nat_true in Heqb. lia. }
        sep_pauto'.
        2: { rewrite H23. simpl (((Vptr eid :: nil) ++_ :: nil)). eauto. }
        2: auto.
        2: { cbn. eauto. }
        2: { unfold isr_is_prop in *. auto. }  
        eapply disj_split.
        apply adisj_intro. right.
        sep normal. sep eexists. sep pauto. sep autocancel.  exact H26.  
        auto.
        eexists. eauto.
        auto. }
      go. 
      { intros. exists init_lg. sep auto. }
      { intros. exists init_lg. sep auto. }
      { rewrite H23. auto. }
      unfold OSIPCSemPostPost, getasrt, OSIPCSemPostPost'.
      hoare normal pre. pure intro.
      eapply backward_rule1.
      { intros.
        sep lift 11%nat in H26.
        eapply disj_split in H26.
        destruct H26.
        { exfalso. sep split in H26.
          rewrite H23 in H27. inversion H27. }
        sep normal in H26.
        exact H26. }
      pure intro.
      inversion H32. subst. clear H32.  
      unfold A_isr_is_prop.
      (* RETURN *)
      eapply ret_rule. intros.
      sep normal. sep eexists.
      sep lift 3%nat.  eapply astar_mono.
      { instantiate (1:= i). instantiate (1:= ier).
        instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
        intros. 
        destruct ((i =? 1)%nat) eqn:?. 
        left. sep autocancel. sep auto. apply beq_nat_true in Heqb. auto.  
        right.  sep autocancel. sep auto. unfold not. intros. subst i. rewrite Nat.eqb_refl in Heqb. discriminate. }
      2:{ sep cancel Aier. exact H32. }
      intros. sep autocancel.
      sep auto.
      unfold DynamicRefactorINV in *. 
      sep destruct H33. sep eexists.
      sep autocancel. sep auto.
      { destruct H34 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
      subst. auto.
      subst. auto.
      { subst. unfold is_que in *. 
        erewrite EcbMod.set_sem. 
        destruct (tidspec.beq v'2 dynrefcmsgQ_addr) eqn:?;auto.
        { exfalso. apply tidspec.beq_true_eq in Heqb.
          destruct H37 as [? [? [? [? ?]]]]. 
          subst. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x6 x7 x8, x9))by auto.
          rewrite H39 in H34.
          inverts H34. } }
      destruct H34 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
      subst. unfold is_que in *.
      erewrite EcbMod.set_sem. 
      destruct (tidspec.beq v'2 dynrefcmsgQ_addr) eqn:?;auto.
      { exfalso. apply tidspec.beq_true_eq in Heqb.
        destruct H37 as [? [? [? [? ?]]]]. 
        subst. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x12 x13 x14, x15))by auto.
        rewrite H41 in H34.
        inverts H34. } }
      eexists. eauto.
      { destruct H34 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
      subst. auto.
      subst. auto.
      subst. apply CORESEM_INECB_P_set_issem. auto.
      destruct H34 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
      subst. apply CORESEM_INECB_P_set_issem. auto. }
      +++ (*enter else branch (IF ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_ACK) !=ₑ ′ IPC_MESSAGE_ACK)) *)
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_ACK) ($ IPC_MESSAGE_ACK) = false).
      { clear -H17. destruct (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_ACK)
      ($ IPC_MESSAGE_ACK));auto. destruct H17;tryfalse. }
      clear H17.
      destruct H5 as [ [? _] | [? H5 ]].
      apply semacc_int_eq_false in H18. false.
      (* If ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_ACK) ==ₑ ′ IPC_MESSAGE_BROAD) *)
      (* enter branch broad *) 
      hoare forward. pauto.
      ++++ (* enter if branch (If ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_BROAD) ==ₑ ′ IPC_MESSAGE_BROAD) )*)
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD) ($ IPC_MESSAGE_BROAD) = true) by pauto.
      destruct H5 as [[? ?] | ?].
      2: { apply semacc_int_eq_true in H22. false. }
      instantiate (1:= Afalse).
      (* absop : choose broad *)
      hoare remember (1::nil)%nat pre.
      hoare abscsq.
      apply noabs_oslinv.
      { assert (can_change_aop H24). { subst H24;can_change_aop_solver. cbn. auto. } 
      eapply absinfer_trans.
      eapply absinfer_choice2 with (q:= H24);auto.
      eapply absinfer_trans.
      eapply absinfer_choice2 with (q:= H24);auto. 
      eapply absinfer_trans.
      eapply absinfer_choice2 with (q:= H24);auto.
      eapply absinfer_trans. 
      eapply absinfer_choice1 with (q:= H24);auto.
      eapply absinfer_eq. }
      subst H24.
      hoare name lift AOSIPCBroadList pre.
      unfold AOSIPCBroadList.
      pure intro.
      rename v'2 into broad_ptr.
      rename v'14 into broad_vl.
      rename v'13 into bstack.
      (* abs step : assert *)
      hoare name lift osipcbroad pre.
      assert ((NoDup bstack) \/ ~ NoDup bstack) as [? | ? ] by tauto. 
      hoare abscsq;[ apply noabs_oslinv | | ].
      eapply OSIpc_high_level_step_bstacknodup_cont;[auto | can_change_aop_solver;cbn;auto  ].
      2: { hoare abscsq.
      apply noabs_oslinv.
      eapply OSIpc_high_level_step_bstacknodup_abt;eauto.
      can_change_aop_solver. cbn. auto.
      apply absabort_rule. }
      apply Zle_lt_or_eq in H29 as [? | ?].
      2: {  assert (length bstack = Z.to_nat CORENUM)%nat.
          { subst broad_ptr. 
            clear -H26 H27. unfold RLH_BROAD_P in H26.
            unfold CORENUM in *.
            do 9 (destruct broad_vl;try discriminate).
            simpl in H26.
            destruct H26 as [? [? ?]].
            subst x.
            simpl in H0.
            subst bstack.
            simpl. lia. }
          exfalso. unfold CORENUM, coreid in *. subst broad_ptr.
          do 9 (destruct broad_vl;try discriminate).
          destruct H26 as [? [? ?]].
          assert (length x0 = 8)%nat.
          { pose proof map_length unsigned2nat x0.  rewrite <- H29 in H31. lia. }
          assert (length bstack <= length (remove Nat.eq_dec (Z.to_nat DNUM) (0::1::2::3::4::5::6::7::nil)))%nat.
          { apply NoDup_incl_length. auto.
            do 9 (destruct x0;try discriminate).
            apply list_reverse_prop2 in H26.  simpl in H26.
            inversion H26;subst. clear H26.
            unfold legal_broadlist in H28. simpl in H28. rename H28 into Hl'.
            clear - Hl'.
            do 8 ( let Hv := fresh "Hv" in inversion Hl' as [ |v l Hv Hl];
                  subst v l;clear Hl'; rename Hl into Hl').
            clear Hl'. 
            repeat match goal with 
            | Hv: legal_broad_element ?v |- _ => 
              unfold legal_broad_element in Hv; destruct v;try contradiction;
              destruct Hv as [Hv [? ?]]; simpl_intltbool end.
            unfold incl. intros.
            rewrite Int.signed_eq_unsigned in * by (apply Int.signed_positive;lia).
            unfold unsigned2nat in H15. simpl in H15.
            repeat match goal with 
            | H : Int.eq ?i ($ ?x) = false |- _ => 
            apply Int_eq_false_intrepr_r in H;[ |  clear; pose proof dnum_range; mauto]
            end.  
            destruct H15 as [ | [ | [ | [ | [ | [ | [ | [ |  ]] ] ] ] ] ]];try contradiction.
            all: match goal with 
            | H: Int.unsigned ?i < 8, H0 : -1 < Int.unsigned ?i, H2: Int.unsigned ?i <> DNUM,
              H1:  Z.to_nat (Int.unsigned ?i) = ?a |- In ?a _ => clear - H H0 H1 H2;
              let h := fresh "H" in assert (Int.unsigned i = 0 \/
              Int.unsigned i = 1 \/ Int.unsigned i = 2 \/  Int.unsigned i = 3 \/ Int.unsigned i = 4 \/
              Int.unsigned i = 5 \/ Int.unsigned i = 6 \/ Int.unsigned i = 7) by mauto;
              pose proof DNUM_destruct as Hdnum;
              destruct h as [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ]];
              destruct Hdnum as [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ]];try congruence
            end;
            match goal with 
            | H: Int.unsigned ?i = ?x, H0 : DNUM = ?y |- _ => subst a;rewrite H, H0;simpl (remove _ _ _);cbn [In]; lia end. }
          assert ( (length (remove Nat.eq_dec (Z.to_nat DNUM) (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil)) < length (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil))%nat).
          { eapply remove_length_lt. clear.  pose proof DNUM_destruct as Hdnum.
            destruct Hdnum as [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ]];cbn [In];lia. }
          cbn [length] in H33. lia. }
      (* IPCBroad_Core_Current ′ [IPCBroad_pointer ′] =ₑ ′ CORENUM;ₛ *)
      hoare forward.
      { clear - H24 H29.
        unfold CORENUM in *.
        mauto.
        cbn. assert (broad_ptr <=? 255 = true) by lia. rewrite H. auto. }
      { clear - H24 H29.
      unfold CORENUM in *.
      mauto. }
      { clear - H24 H29 H27.
      unfold CORENUM in *.
      mauto. }
      (* ++ IPCBroad_pointer ′; *)
      hoare forward.
      { clear - H24 H29.
        unfold CORENUM in *.
        mauto.
        cbn. assert (broad_ptr <=? 255 = true) by lia. rewrite H. auto. }
      (* abs step : OSIPC_broad*)
      hoare name lift osipcbroad pre.
      hoare abscsq;[ apply noabs_oslinv | | ].
      apply OSIpc_high_level_step_broad;auto.
      { clear - H11. mauto. }
      { clear - H11. mauto. }
      can_change_aop_solver. cbn. auto. 
      (* tmpsem ′ =ₑ IPCSemShared ′;ₛ *)
      hoare name lift AOSIPCSemShared pre.
      unfold AOSIPCSemShared.
      (* OSIPCSemPost (­ IPCSemShared ′­) *)
      eapply seq_rule.
      eapply call_rule';
      [ intuition eauto|  |
        intros;unfold_spec |
       idtac | sep_unfold_funpost  | 
       sep_unfold_funpre |
       simpl;eauto ] .
      { intros; (apply rvl_elim;[ symbolic_execution | ]);
       first [apply rvl_nil | simpl;auto].  }
      { unfold A_isr_is_prop;sep normal;sep eexists.
        sep lift 8%nat in H30. 
        eapply astar_mono in H30. 3: { intros s' hs'; exact hs'. }
        2: { instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
             intros. 
             destruct H31. 
             sep split in H31. subst i. cbn [Nat.eqb]. auto. 
             sep split in H31. destruct ((i =? 1)%nat) eqn:?;[ | auto ]. apply beq_nat_true in Heqb. lia. }
        sep_pauto'.
        2: { simpl (((Vptr OSSemShared_val :: nil) ++_ :: nil)). eauto. }
        2: auto.
        2: { cbn. eauto. }
        2: { unfold isr_is_prop in *. auto. }  
        eapply disj_split.
        apply adisj_intro. right.
        sep normal. sep eexists. sep pauto. sep autocancel.  exact H30.  
        auto.
        eexists. eauto. }
      go. 
      { intros. 
        exists init_lg. sep auto. }
      { intros. 
        exists init_lg. sep auto. }
      { simpl. auto. }
      unfold OSIPCSemPostPost, getasrt, OSIPCSemPostPost'.
      hoare normal pre. pure intro.
      eapply backward_rule1.
      { intros.
        sep lift 11%nat in H30.
        eapply disj_split in H30.
        destruct H30.
        { exfalso. sep split in H30. inversion H31. }
        sep normal in H30.
        exact H30. }
      pure intro.
      inversion H36. subst. clear H36.  
      unfold A_isr_is_prop.
      (* RETURN *)
      eapply ret_rule. intros.
      sep normal. sep eexists.
      sep lift 8%nat.  eapply astar_mono.
      { instantiate (1:= i). instantiate (1:= ier).
        instantiate (1:= Aier (if Nat.eqb i 1%nat then (ierupd ier i false) else (ierupd ier i true))).
        intros. 
        destruct ((i =? 1)%nat) eqn:?. 
        left. sep autocancel. sep auto. apply beq_nat_true in Heqb. auto.  
        right.  sep autocancel. sep auto. unfold not. intros. subst i. rewrite Nat.eqb_refl in Heqb. discriminate. }
      2:{ sep cancel Aier. exact H30. }
      intros. sep autocancel.
      sep auto.
      unfold DynamicRefactorINV in *. 
      sep destruct H36. sep eexists.
      sep autocancel. sep auto.
      { destruct H38 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
      subst. auto.
      subst. auto.
      { subst. unfold is_que in *. 
        erewrite EcbMod.set_sem. 
        destruct (tidspec.beq OSSemShared_val dynrefcmsgQ_addr) eqn:?;auto.
        { exfalso. apply tidspec.beq_true_eq in Heqb.
          destruct H40 as [? [? [? [? ?]]]]. 
          rewrite Heqb in *. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x6 x7 x8, x9))by auto.
          rewrite H42 in H38.
          inverts H38. } }
      destruct H38 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
      subst. unfold is_que in *.
      erewrite EcbMod.set_sem. 
      destruct (tidspec.beq OSSemShared_val dynrefcmsgQ_addr) eqn:?;auto.
      { exfalso. apply tidspec.beq_true_eq in Heqb.
        destruct H40 as [? [? [? [? ?]]]]. 
        rewrite Heqb in *. assert (EcbMod.get v'4 dynrefcmsgQ_addr = Some (absmsgq x12 x13 x14, x15))by auto.
        rewrite H44 in H38.
        inverts H38. } }
      eexists. eauto.
      { destruct H38 as [[_ [? _]] | [[? [? [? [? _ ]]]] | [[? [? [? [? _ ]]]] | ] ] ]. 
      subst. auto.
      subst. auto.
      subst. apply CORESEM_INECB_P_set_issem. auto.
      destruct H38 as (? & ? & ? & ? & ? & ? & ?  & ? & ? & ? & ? & ? & ?  &  _).
      subst. apply CORESEM_INECB_P_set_issem. auto. }
      { clear -H10 H4_ H26 H24 H29 H25 H28 H27. 
        unfold RLH_BROAD_P in *.
        destruct H26 as [? [? ?]].
        exists (Vint32 corenum_val :: x).
        simpl.
        split;[ | subst bstack;auto].
        unfold CORENUM in *.
        do 2 rewrite Int.unsigned_repr by mauto.
        assert (exists v, nth_error broad_vl (Z.to_nat broad_ptr) = Some v) as [? ?].
        { eexists. apply nth_error_nth' with (d := Vnull). lia. }
        apply nth_error_split in H1 as [? [? [? ?]]].
        subst broad_vl.
        rewrite <- H2.
        rewrite update_nth_val_midlle.
        rewrite list_cons_assoc.
        rewrite firstn_app in *.
        rewrite H2 in H. 
        assert (length (x1 ++ Vint32 corenum_val :: nil) =(Z.to_nat (broad_ptr + 1))).
        { rewrite app_length. simpl. lia. }
        rewrite H1.
        rewrite Nat.sub_diag in *. simpl in *.
        rewrite rev_app_distr in *; simpl in *.
        rewrite <- H2 in H. rewrite <- H1.
        rewrite firstn_all in *.
        rewrite rev_app_distr.
        simpl.
        rewrite H.
        reflexivity. }
      { splits.
        apply array_type_vallist_match_hold;auto. 
        clear - H24 H29 H27. unfold CORENUM in *. rewrite Int.unsigned_repr by mauto. lia.
        rewrite update_nth_val_len_eq;auto.
        { clear - H11 H4_ H24 H29 H27 H28. unfold CORENUM in *.
          unfold legal_broadlist in *.  
          do 2 rewrite Int.unsigned_repr by mauto.
          assert (exists v, nth_error broad_vl (Z.to_nat broad_ptr) = Some v) as [? ?].
          { eexists. apply nth_error_nth' with (d := Vnull). lia. }
          apply nth_error_split in H as [? [? [? ?]]].
          subst broad_vl.
          rewrite <- H0.
          rewrite update_nth_val_midlle.
          rewrite list_cons_assoc.
          rewrite firstn_app in *.
          rewrite H0 in H28. 
          assert (length (x0 ++ Vint32 corenum_val :: nil) =(Z.to_nat (broad_ptr + 1))).
          { rewrite app_length. simpl. lia. }
          rewrite H.
          rewrite Nat.sub_diag in *. simpl in *.
          rewrite <- H0 in H28. rewrite <- H.
          rewrite firstn_all in *.
          rewrite app_nil_r in *.
          apply Forall_app.
          split;auto.
          apply Forall_cons;[ | apply Forall_nil].
          unfold legal_broad_element.
          clear -H11 H4_. splits;auto.
          clear -H11. mauto. mauto. }}
      { clear - H24 H29. unfold CORENUM in *. mauto. }
      ++++ (* end if branch (If ((read_ipcgr ′ &ₑ ′ IPC_MESSAGE_BROAD) ==ₑ ′ IPC_MESSAGE_BROAD) )*)
      instantiate (1:= Afalse).
      pure intro.
      assert (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD) ($ IPC_MESSAGE_BROAD) = false).
      { destruct (Int.eq (ipcgr_val&ᵢ$ IPC_MESSAGE_BROAD) ($ IPC_MESSAGE_BROAD));auto.
        destruct H19; tryfalse. }
      apply semacc_int_eq_false in H20.
      (* abs step *)
      hoare abscsq;[apply noabs_oslinv | | ].
      apply OSIpc_high_level_step_assume3;auto.
      can_change_aop_solver. cbn. auto. 
      (* RETURN  *)
      eapply ret_rule. 
      intros.
      sep normal. sep eexists. sep autocancel. 
      sep pauto.
      eexists. eauto.
      ++ (*branch end*)
      intros.
      destruct H15.
      { sep auto. }

      sep split in H15.
      destruct H15.
      { sep auto. }

      sep split in H15.
      destruct H15.
      sep auto.
      sep auto.
    + destruct H12;
      sep auto.
Qed.
