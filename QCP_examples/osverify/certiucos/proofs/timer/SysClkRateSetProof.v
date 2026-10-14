Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.
(* SYS_CLK_RATE_SET Proof *)
Open Scope int_scope.

Lemma sys_clk_rate_set_absinfer_nop :
 forall P sch i aop, 
    can_change_aop P ->
    Int.ltu i ($ 1) = true ->
    absinfer sch ( <|| osclk_rate_set_nop (|Vint32 i :: nil|) ?? 
                       aop  ||> ** P) 
    (<|| END (Some (Vint32 (Int.repr (Zneg xH)))) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.


Lemma sys_clk_rate_set_absinfer_rateset :
 forall P sch i t ct tmrls clkrate aop, 
    can_change_aop P ->
    Int.ltu i ($ 1) = false ->
    absinfer sch ( <|| osclk_rate_set (|Vint32 i :: nil|) ;; aop  ||> ** 
                    HTime t ** HCurTCB ct ** 
                    HTMRList tmrls ** HClkRate clkrate **  P) 
    (<|| aop ||> ** 
        HTime t ** HCurTCB ct ** 
        HTMRList tmrls ** HClkRate i **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sys_clk_rate_set_absinfer_update_systmr :
 forall P sch i t ct tmrls clkrate, 
    can_change_aop P ->
    Int.ltu i ($ 1) = false ->
    absinfer sch ( <|| osclk_rate_set_update_systmr (|Vint32 i :: nil|)  ||> ** 
                    HTime t ** HCurTCB ct ** 
                    HTMRList (Some tmrls) ** HClkRate clkrate **  P) 
    (<|| END (Some (Vint32 Int.zero)) ||> ** 
        HTime t ** HCurTCB ct ** 
        HTMRList (Some ((set tmrls DNUM (gp_t (1000000000 / (Int.unsigned i * 6)) continuously, tm_start, 0, om_clock)))) ** HClkRate clkrate **  P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma TMRNode_P_init: forall p v0 v1 v2 v9,
0 <= p < Int.modulus ->
TMRNode_P
  (Vint32 v0
   :: Vint32 (tmrinit_emumgt_clkpsd v1)
      :: v2
         :: Vint32 Int.zero
            :: Vint32 Int.zero
               :: V$ p :: V$ 0 :: V$ 136 :: V$ 3 :: Vint32 v9 :: nil)
  (gp_t p continuously, tm_start, 0, om_clock).
Proof.
  intros.
  unfold TMRNode_P in *.
  splits.
  - unfold TMRNode_Pmode, V_OSTGCR, V_OSTCRreg;simpl.
    do 2 eexists; splits;eauto.
  - unfold TMRNode_Pcnt, V_OSCNTLO, V_OSCNTHI;simpl.
    do 2 eexists; splits;eauto.
  - unfold TMRNode_Pprd, V_OSPRDLO, V_OSPRDHI;simpl.
    do 2 eexists; splits;eauto.
    rewrite Z.div_small by auto.
    auto.
  - unfold TMRNode_Pstatus, V_OSTGCR;simpl.
    eexists; splits;eauto.
  - unfold TMRNode_Poutmode, V_OSTCRreg;simpl.
    eexists; splits;eauto.
Qed.

Lemma TMRList_P_sys_init: forall systmrl tmrls n m p v0 v1 v2 v3 v4 v5 v6 v7 v8 v9, 
nth_error systmrl n =
      Some
        (Vint32 v0
         :: Vint32 v1
            :: v2
               :: Vint32 v3
                  :: Vint32 v4
                     :: Vint32 v5
                        :: Vint32 v6
                           :: Vint32 v7
                              :: Vint32 v8 :: Vint32 v9 :: nil) ->
TMRList_P_sys m systmrl tmrls ->
0 <= p < Int.modulus ->
TMRList_P_sys m
  (update_nth_vallist n systmrl
     (Vint32 v0
      :: Vint32 (tmrinit_emumgt_clkpsd v1)
         :: v2
            :: Vint32 Int.zero
               :: Vint32 Int.zero
                  :: V$ p
                     :: V$ 0 :: V$ 136 :: V$ 3 :: Vint32 v9 :: nil))
  (set tmrls (Z.of_nat (m + n))
     (gp_t p continuously, tm_start, 0,
     om_clock)).
Proof.
  induction systmrl;intros.
  - destruct n;simpl in H;tryfalse. 
  - destruct n.
    + simpl in H. inversion H;subst a; clear H.
      simpl in H0;simpl.
      my_destruct H0.
      exists (gp_t p continuously, tm_start, 0, om_clock) x0.
      splits;eauto.
      apply TMRNode_P_init;auto.
      rewrite Nat.add_0_r.
      eapply join_sig_set;eauto.
    + simpl in H.
      simpl in H0;simpl.
      my_destruct H0.
      exists x ((set x0 (Z.of_nat (m + S n)) (gp_t p continuously, tm_start, 0, om_clock))).
      splits;auto.
      { apply map_join_comm.
      eapply map_join_set_none;eauto.
      apply map_join_comm;eauto.
      eapply get_sig_none. lia. }
      assert (m + S n = S m + n)%nat by lia.
      rewrite H4.
      eapply IHsystmrl;eauto.
Qed.

      


Lemma OSsys_clk_rate_setProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api sys_clk_rate_set clkratesetapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api sys_clk_rate_set clkratesetapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sys_clk_rate_set = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init spec.
  (* If (′ 1 >ₑ tickspersecond ′) *)
  hoare forward.
  pauto.
  - (* Branch : enter branch*)
    (* err ′ =ₑ ′ EINVAL;ₛ *)
    hoare forward.
    pure intro.
    assert (Int.ltu i ($ 1) = true) by pauto. 
    hoare abscsq.
    apply noabs_oslinv.
    eapply sys_clk_rate_set_absinfer_nop; eauto.
    can_change_aop_solver.
    (* RETURN ′ (-1) *)
    hoare forward.
  - hoare forward.
    pure intro.
    assert (Int.ltu i ($ 1) = false).
    { destruct (Int.ltu i ($ 1));auto.
      simpl in H.
      destruct H;tryfalse. }
    (* abs op: choose the second branch *)
    hoare abscsq.
    apply noabs_oslinv.
    eapply absinfer_choice2.
    3: {  intros s Hs; exact Hs. }
    1,2: can_change_aop_solver.
    (* ENTER_CRITICAL;ₛ *)
    hoare forward prim.
    unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed.
    pure intro.
    rename v'18 into vpthattr.
    rename v'19 into vcspace.
    rename v'20 into v20. 
    rename v'21 into v21. 
    rename v'22 into v22. 
    
    rename v'23 into v'18. 
    rename v'24 into v'19. 
    rename v'25 into v'20. 
    rename v'26 into v'21. 
    rename v'27 into v'22. 

    rename v'19 into systmrl.
    (* abs op : ASSERT TMRnotERROR;; *)
    destruct H3 as [[tmrls [H3_ H3]] | H3].
    2:{ rewrite H3.
        hoare_abscsq_tmr1.
        apply noabs_oslinv.
        eapply tmr_absinfer_TMRnotERROR_abort.
        can_change_aop_solver.
        apply absabort_rule. }
    subst v'22.
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply tmr_absinfer_TMRnotERROR_cont.
    can_change_aop_solver.
    my_destruct H3.
    (* OS_TICKS_PER_SEC_SYS ′ =ₑ tickspersecond ′;ₛ *)
    unfold AOSClkRate; hoare forward.
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply sys_clk_rate_set_absinfer_rateset;eauto.
    can_change_aop_solver.
    (* prdlo ′ =ᶠ compute_period (·OS_TICKS_PER_SEC_SYS ′, ′ CPU_CLK_KHZ·);ₛ *)
    hoare lifts (1::30::31::32::33::34::22::7::29::nil)%nat pre.
    hoare_calle_lvar_aempiser.
    { intros. sep destruct H11.
    exists init_lg.
    sep auto. }
    { intros. sep destruct H11.
    exists init_lg.
    sep auto. }
    pure intro.
    remember (match Int.unsigned v'23 with
          | 0 => 0
          | Z.pos y' => Z.pos (y' + (y' + (y' + (y' + (y' + y'~0)~0)~0)~0)~0~0)~0~0~0
          | Z.neg y' => Z.neg (y' + (y' + (y' + (y' + (y' + y'~0)~0)~0)~0)~0~0)~0~0~0
          end / (Int.unsigned v'22 * 6))%Z as prdloz eqn:?.
    inversion H12. inversion H13.
    subst v'22 v'23 v'26 v'25.
    clear H12 H13.
    unfold CPU_CLK_KHZ in Heqprdloz.
    rewrite Int.unsigned_repr in Heqprdloz by mauto.
    simpl in Heqprdloz.
    (* get AOSTMRNode ($ DNUM) v'23 *)
    pose proof dnum_range as [Hdnum0 Hdnum7].
    hoare lift 18%nat pre. 
    eapply backward_rule1.
    eapply AOSTMRList_separate with (i := ($ DNUM));eauto.
    { clear - Hdnum0 Hdnum7. 
      apply Intlt_true_is_Zlt.
      rewrite Int.unsigned_repr by mauto. 
      rewrite Int.unsigned_repr by mauto.
      lia.  }
    pure intro.
    rewrite Int.unsigned_repr in H11 by mauto.
    (* destruct v'19*)
    unfold AOSTMRNode.
    pure intro.
    hoare remember (1::2::3::4::5::6::7::8::9::nil)%nat pre.
    eapply backward_rule1 with (p:= 
    AOSTMRNode ($ DNUM) (Vint32 v'22
    :: Vint32 v'23
       :: v'24
          :: Vint32 v'25
             :: Vint32 v'26
                :: Vint32 v'27
                   :: Vint32 v'28
                      :: Vint32 v'29 :: Vint32 v'30 :: Vint32 v'31 :: nil) ** H13).
    { intros.
      unfold AOSTMRNode.
      sep cancel H13.
      sep auto. }
    subst H13.
    
    hoare lifts (7::3::8::4::9::6::10::1::19::11::nil)%nat pre.
    hoare_call_aempiser.
    { clear - Hdnum0 Hdnum7.
      apply Intlt_true_is_Zlt.
      do 2 rewrite Int.unsigned_repr by mauto. lia.  }
    { unfold V_OSEMUMGT; cbn; eauto. }
    { cbn [nth_val]. eauto. }
    { cbn [nth_val]. eauto. }
    { intros. sep destruct H13.
      exists init_lg.
      sep auto. }
    { intros. sep destruct H13.
      exists init_lg.
      sep auto. }
    inversion H17. inversion H18.
    subst v'35 v'37 v'38.
    clear H17 H18.
    cbn [update_nth_val].
    (* abs step*)
    hoare_abscsq_tmr1.
    apply noabs_oslinv.
    eapply sys_clk_rate_set_absinfer_update_systmr;eauto.
    can_change_aop_solver.
    (* EXIT_CRITICAL;ₛ *)
    hoare forward prim.
    { unfold TmrInv, TmrInv', AOSTMRList_TMRused, AOSTMRIDUsed, AOSClkRate.
      sep normal.
      sep eexists.
      trycancel.
      sep normal.
      sep split.
      { sep lifts (7::4::3::5::2::nil)%nat in H13.
      sep cancel Agvarmapsto.
      sep cancel Agvarmapsto.
      eapply AOSTMRList_merge in H13;eauto.
      2: { clear - Hdnum0 Hdnum7.
      apply Intlt_true_is_Zlt.
      do 2 rewrite Int.unsigned_repr by mauto. lia.  }
      rewrite Int.unsigned_repr in H13 by mauto.
      rewrite update_nth_vallist_app1 in H13 by lia.
      sep cancel AOSTMRList'.
      sep cancel GAarray.
      exact H13. }
    { left. eexists. split;eauto.
      exists (set x DNUM
     (gp_t (1000000000 / (Int.unsigned i * 6)) continuously, tm_start, 0, om_clock)) x0.
     splits;auto.
     { eapply join_set_l;eauto.
       rewrite <-Z2Nat.id by auto.
      eapply RLH_TMRList_P_sys_indom;eauto.
      lia. } 
     { unfold RLH_TMRList_P_sys in *.
       rewrite <- (Z2Nat.id  DNUM) at 2 by auto.
       eapply TMRList_P_sys_init;eauto.
       erewrite nth_error_app1 in H11 by lia.
       eauto.
       clear -H0.
       simpl_intltbool.
       pose proof Int.unsigned_range i as [_ ?].
       split.
       { apply Z.div_pos; lia. }
       { eapply Z.lt_trans with (1000000000).
         apply Z.div_lt; lia.
         rewrite modulus_val.
         lia. }
     } }
    rewrite length_update_nth_vallist;auto.
    splits;auto.  }
    auto.
    go.
    (* RETURN ′ 0 *)
    hoare forward.
Qed.