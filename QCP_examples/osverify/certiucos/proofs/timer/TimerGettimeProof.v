Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.
Require Import TimerGettimeRules.


Open Scope code_scope.
(* timer gettime  Proof *)
Open Scope int_scope.


Lemma OStimer_gettimeProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api OStimer_gettime tmrgetapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api OStimer_gettime tmrgetapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api OStimer_gettime = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec. 
  (*err′ =ₑ ′0;ₛ*)
  hoare forward.
  (*ret′ =ₑ ′0;ₛ*)
  hoare forward.
  
  (*  If ( timerid′ >ₑ ′7 &&ₑ timerid′ <ₑ ′16) true *)
  hoare forward;pauto.
  - (* enter branch : yes*)
    instantiate (1:= <|| END (Some (Vint32 ($ -1))) ||>  ** 
    LV ret @ Int32u |-> (V$ 0) **
    LV err @ Int32u |-> (V$ 0) **
    LV TimerRegs_CNTHI @ (Int32u) ∗ |-> v'3 **
    LV TimerRegs_CNTLO @ (Int32u) ∗ |-> v'2 **
    p_local OSLInv tid init_lg **
    LV cnthigh @ (Int32u) ∗ |-> x **
    LV cntlow @ (Int32u) ∗ |-> x0 **
    LV os_code_defs.timerid @ Int32u |-> Vint32 i **
    Aie true **
    Ais nil **
    Acs nil **
    Aisr empisr **
    Aier v'4 **
    A_dom_lenv
      ((cnthigh, (Int32u) ∗)
        :: (cntlow, (Int32u) ∗)
          :: (os_code_defs.timerid, Int32u)
              :: (err, Int32u)
                :: (ret, Int32u) :: (TimerRegs_CNTLO, (Int32u) ∗) :: (TimerRegs_CNTHI, (Int32u) ∗) :: nil)).
    pure intro.
    assert (Int.ltu ($ 7) i  = true) by pauto. 
    assert (Int.ltu i ($ 16)  = true) by pauto.
    (* choose second abs branch *)
    hoare abscsq.
    apply noabs_oslinv.
    apply absinfer_choice2.
    can_change_aop_solver.
    2:{  intros s Hs; exact Hs. }
    can_change_aop_solver.
    (* abs op : ASSERT tmr_valvptr x0 *)
    destruct H2 as [H2 | [? H2]].
    { subst x0.
    hoare_abscsq.
    apply noabs_oslinv.
    eapply tmr_absinfer_valvptr_abt;eauto.
    can_change_aop_solver.
    apply absabort_rule. }
    subst x0.
    hoare_abscsq.
    apply noabs_oslinv.
    eapply tmr_absinfer_valvptr_cont;eauto.
    can_change_aop_solver.
    (* abs op : ASSERT tmr_valvptr x *)
    destruct H1 as [H1 | [? H1]].
    { subst x.
    hoare_abscsq.
    apply noabs_oslinv.
    eapply tmr_absinfer_valvptr_abt;eauto.
    can_change_aop_solver.
    apply absabort_rule. }
    subst x.
    hoare_abscsq.
    apply noabs_oslinv.
    eapply tmr_absinfer_valvptr_cont;eauto.
    can_change_aop_solver.
    rename x1 into low_addr.
    rename x0 into high_addr.
    (* ENTER_CRITICAL;ₛ *)
    hoare forward prim.
    unfold TmrInv.

    unfold  TmrInv', HeapInv', AOSTMRList_TMRused, AOSTMRIDUsed.
    pure intro.
    rename v'20 into vpthattr.
    rename v'21 into vcspace.
    rename v'22 into v22. 
    rename v'23 into v23. 
    rename v'24 into v24. 
    rename v'25 into v'20. 
    rename v'26 into v'21. 
    rename v'27 into v'22. 
    rename v'28 into v'23. 
    rename v'29 into v'24. 
    rename v'30 into v'25. 
    rename v'31 into v'26. 
    rename v'32 into v'27. 
  

    hoare lift 8%nat pre.
    (* abs op : ASSERT TMRnotERROR;; *)
    destruct H9 as [[tmrls [H9_ H9]] | H9].
    2:{ rewrite H9.
        hoare_abscsq_tmr2.
        apply noabs_oslinv.
        eapply tmr_absinfer_TMRnotERROR_abort.
        can_change_aop_solver.
        apply absabort_rule. }
    subst v'24.
    hoare_abscsq_tmr2.
    apply noabs_oslinv.
    eapply tmr_absinfer_TMRnotERROR_cont.
    can_change_aop_solver.
    my_destruct H9.
    assert ((Int.unsigned (i -ᵢ $ 8) = Int.unsigned i -  8)%Z).
    { simpl_intltbool. rewrite Int_unsigned_minus. 
      rewrite Int.unsigned_repr by (cbn;lia).
      auto.
      rewrite Int.unsigned_repr by (cbn;lia).
      lia.  }
    assert ((Int.unsigned (i -ᵢ $ 8) < 8)%Z).
    { simpl_intltbool.
      rewrite H17.
      lia. }
    assert (rule_type_val_match Int8u (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'23) = true).
    { apply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match;eauto. 
      rewrite H17. lia. }
    remember (nth_val' (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'23) as used_i.
    destruct used_i;tryfalse.
    (* If (OS_timerid_used ′ [os_code_defs.timerid ′ − ′ 8] ==ₑ ′ 1) *)
    hoare forward;pauto.
    { rewrite <- Heqused_i. auto. }
    { rewrite <- Heqused_i.
      unfold val_eq. 
      destruct (Int.eq i0 ($ 1)); pauto. } 
    + instantiate (1:= Afalse). 
      (* enter branch : tmrused condition true *) 
      pure intro.
      assert (Int.eq i0 ($1) = true).
      { rewrite <- Heqused_i in *.
        unfold val_eq in *. 
        destruct (Int.eq i0 ($ 1)); auto. }
      clear H20 H21 H22.
      apply Int_eq_dec in H23.
      subst i0.
      rename v'23 into tmrusedl.
      rename v'22 into utmrl.
      (*choose the second abs op*)
      hoare abscsq.
      apply noabs_oslinv.
      eapply absinfer_choice2;eauto.
      can_change_aop_solver.
      can_change_aop_solver.
      (* TimerRegs_CNTLO ′ =ₑ NULL;ₛ *)
      hoare forward.
      (* TimerRegs_CNTHI ′ =ₑ NULL;ₛ *)
      hoare forward.
      (* TimerRegs_CNTLO ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 4 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
      hoare lifts (1::3::14::44::33::45::nil)%nat pre.
      eapply seq_rule.
      eapply timer_assign_timerregs_mul with (n:= 4%nat);eauto. lia.
      unfold tmrregsLists; cbn [nth].
      (* TimerRegs_CNTHI ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 5 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
      hoare lifts (1::7::3::4::5::6::nil)%nat pre.
      eapply seq_rule.
      eapply timer_assign_timerregs_mul with (n:= 5%nat);eauto. lia.
      unfold tmrregsLists; cbn [nth].
      (* lift AOSTMRList' and get tmri properties *)
      hoare lifts (13::nil)%nat pre.
      eapply backward_rule1.
      eapply AOSTMRList_separate;eauto. 
      pure intro.
      rename v'22 into tmri.
      rewrite nth_error_app2 in H20 by (simpl_intltbool;lia).
      rewrite H8 in H20.
      assert (exists abstmr, IsGPtmr tmri abstmr = true /\ get x0 (Z.of_nat (Z.to_nat (Int.unsigned (i -ᵢ $ 8)))  + 8) = Some abstmr /\ TMRNode_P tmri abstmr ).
      { eapply RLH_TMRused_is1;eauto.
        { rewrite H17.
        assert ((Z.to_nat (Int.unsigned i - 8)) = (Z.to_nat (Int.unsigned i) - 8))%nat by (simpl_intltbool;lia).
        rewrite H22.
        eauto. }
        { unfold TMR_used.
          apply nth_val_nth_error.
          eapply nth_val'_imply_nth_val;eauto.
          lia. } }
      my_destruct H22.
      apply andb_true_iff in H22 as [? ?].
      destruct_tmr x1;tryfalse.
      (* get low value and high value*)
      assert ((Z.of_nat (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) + 8) = Int.unsigned i).
      { rewrite H17. simpl_intltbool. lia. }
      rewrite H26 in H23;clear H26.
      assert (V_OSCNTLO' tmri = V$ tk /\ V_OSCNTHI' tmri = V$ tk / Int.modulus) as [? ?].
      { eapply RLH_TMRList_P_user_gettklowhigh;eauto. }
      (* get length tmri*)
      eapply backward_rule1.
      eapply AOSTMRNode_imply_length_frm.
      pure intro.
      (* case analysis for abs update low : abt or end*)
      rename v'26 into cHeape.
      assert ((~ In_heape_addrval cHeape low_addr Tint32 ) \/ 
      In_heape_addrval cHeape low_addr Tint32 ) by tauto.
      destruct H29.
      (* case 1: ~ In_heape_addrval cHeape x2 Tint32 
      abs step abort *)
      hoare_abscsq_tmr2.
      apply noabs_oslinv.
      eapply tmrgettime_absinfer_updatelow_abt;eauto.
      eapply join_get_r;eauto.
      can_change_aop_solver.
      apply absabort_rule.
      (* ∗ cntlow′ =ₑ ∗ TimerRegs_CNTLO′ ;ₛ *)
      (* get cntlow : PV *)
      hoare lift 16%nat pre.
      eapply backward_rule1.
      eapply In_heape_addrval_split with (l:= low_addr);eauto.
      pure intro.
      eapply backward_rule1.
      eapply coreheape_separate_frm.  
      (* ∗ cntlow ′ =ₑ ∗ TimerRegs_CNTLO ′;ₛ *)
      hoare lifts (6::48::12::2::4::10::11::nil)%nat pre.
      hoare forward.
      eapply tmrgettimeproof_part0;eauto.
      rewrite H26.
      (* absop : tmrgettime_absinfer_succ_updatelow  *)
      hoare_abscsq_tmr2.
      apply noabs_oslinv.
      eapply tmrgettime_absinfer_succ_updatelow;eauto.
      eapply join_get_r;eauto.
      can_change_aop_solver.
      (* merge coreheap *)
      hoare lifts (13::9::14::nil)%nat pre.
      eapply backward_rule1.
      eapply coreheape_merge_frm.
      (* case analysis for abs update high : abt or end*)
      remember (v'22 ++ (low_addr, Int32u, V$ tk) :: v'23) as cHeape.
      assert ((~ In_heape_addrval cHeape high_addr Tint32 ) \/ 
      In_heape_addrval cHeape high_addr Tint32 ) by tauto.
      destruct H30.
      (* case 1: ~ In_heape_addrval cHeape high_addr Tint32
      abs step abort *)
      hoare_abscsq_tmr2.
      apply noabs_oslinv.
      eapply tmrgettime_absinfer_updatehigh_abt;eauto.
      eapply join_get_r;eauto.
      can_change_aop_solver.
      apply absabort_rule.
      (* case 2: In_heape_addrval cHeape x2 Int32u  *)
      (* get cnthigh : PV *)
      eapply backward_rule1.
      eapply In_heape_addrval_split with (l:= high_addr);eauto.
      hoare_ex_intro.
      hoare_split_pure_all.
      rewrite H31.
      eapply backward_rule1.
      eapply coreheape_separate_frm.  
      (* ∗ cnthigh ′ =ₑ ∗ TimerRegs_CNTHI ′;ₛ *)
      hoare lifts (4::48::16::2::12::13::14::nil)%nat pre.
      hoare forward.
      eapply tmrgettimeproof_part1;eauto.
      rewrite H27.
      (* absop : tmrgettime_absinfer_succ_updatelow  *)
      hoare_abscsq_tmr2.
      apply noabs_oslinv.
      eapply tmrgettime_absinfer_succ_updatehigh;eauto.
      eapply join_get_r;eauto.
      rewrite <-  H31. auto.
      can_change_aop_solver.
      (* merge coreheap *)
      hoare lifts (13::9::14::nil)%nat pre.
      eapply backward_rule1.
      eapply coreheape_merge_frm.
      (* merge AOSTMRList' *)
      hoare lifts (10::15::nil)%nat pre.
      eapply backward_rule1.
      eapply AOSTMRList_merge;eauto.
      assert (update_nth_vallist (Z.to_nat (Int.unsigned i)) (v'21 ++ utmrl)  tmri = (v'21 ++ utmrl) ). 
      { erewrite update_nth_vallist_app2;[ | simpl_intltbool; lia]. 
        erewrite update_nth_vallist_nth_error;eauto.
        rewrite H8. auto. }
      rewrite H32;clear H32.
      (* EXIT_CRITICAL;ₛ *)
      hoare forward prim.
      2: eauto.
      { unfold TmrInv, TmrInv', HeapInv', AOSTMRList_TMRused, AOSTMRIDUsed.
        trycancel.
        sep normal.
        sep eexists.
        sep split.
        trycancel. 
        sep pauto.
        left. eexists. split;eauto.
        splits;auto.
        splits;auto.
        all : auto. 
      { clear -H2 H31.
        assert (map fst (map fst (v'22 ++ (low_addr, Int32u, V$ tk) :: v'23)) = 
        map fst (map fst (v'26 ++ (high_addr, Int32u, v'29) :: v'28))) by (rewrite H31;auto).
        clear H31.
        repeat rewrite map_app in *.
        cbn in *.
        rewrite <- H;auto. } }
      go.
      (* RETURN ′ 0 *)
      hoare forward.
    + hoare forward. 
      (* out branch : tmrused condition false *) 
      pure intro.
      rewrite <- Heqused_i in H20.
      unfold val_eq in H20.
      assert (Int.eq i0 ($ 1) = false).
      { destruct (Int.eq i0 ($ 1));auto.
        simpl in H20. destruct H20;tryfalse. }
      clear H20.
      assert (nth_val (Z.to_nat (Int.unsigned (i -ᵢ $ 8))) v'23 = Some (Vint32 i0)).
      { eapply nth_val'_imply_nth_val;eauto.
        lia.  }
      clear Heqused_i.
      assert (Vint32 i0 = V$ 0 \/ Vint32 i0 = V$ 1).
      { eapply Forall_forall with (x:= Vint32 i0) in H14. auto.
        eapply nth_val_In;eauto. }
      destruct H22;inversion H22;subst i0;tryfalse.
      rewrite H17 in H20.
      assert (~ indom x0 (Int.unsigned i)).
      { assert (Int.unsigned i = Z.of_nat (Z.to_nat (Int.unsigned i - 8)) + 8) by (simpl_intltbool; lia).
        rewrite H23.
        eapply RLH_TMRused_is0;eauto.
        lia.
        eapply nth_val_nth_error;eauto. }
      assert (~ indom x (Int.unsigned i)).
      { unfold indom,not;intro.
        destruct H24.
        assert (Int.unsigned i = Z.of_nat (Z.to_nat (Int.unsigned i))) by (simpl_intltbool;lia).
        rewrite H25 in H24.
        lets Hx : RLH_TMRList_P_sys_idrange H15 H24.
        simpl_intltbool. lia. }
      assert (get tmrls (Int.unsigned i) = None).
      { apply nindom_get in H23,H24.
        erewrite map_join_get_none''';eauto. }
      (* change abs op*)
      hoare_abscsq_tmr2.
      apply noabs_oslinv.
      eapply ostimer_absimp_tmrget_tmrnone;eauto.
      can_change_aop_solver.
      (* EXIT_CRITICAL *)
      hoare forward prim.
      { unfold TmrInv, TmrInv', HeapInv', AOSTMRList_TMRused, AOSTMRIDUsed.
        trycancel.
        sep normal.
        sep eexists.
        trycancel.
        sep split.
        sep pauto.
        { left. eexists. split;eauto. }
        1,2: splits;auto.
        all: auto. }
      auto.
      go.
      sep auto.
  - 
    hoare forward.
    + hoare forward.
      hoare forward.
    + 
      pure intro.
    assert (Int.ltu ($ 7) i = false \/ Int.ltu i ($ 16) = false).
    { destruct (Int.ltu ($ 7) i);destruct (Int.ltu i ($ 16));auto.
      simpl in H. 
      assert (Int.ltu Int.zero Int.one = true ) by pauto.
      rewrite H0 in H.
      simpl in H.
      destruct H;tryfalse. }
    hoare forward.
    hoare abscsq.
    apply noabs_oslinv.
    eapply tmrgettime_absinfer_iderror;eauto.
    can_change_aop_solver.
    (* RETURN ′ (-1) *)
    hoare forward.
Qed.