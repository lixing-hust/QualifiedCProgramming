Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.
(* timer init Proof *)
Open Scope int_scope.

Lemma OS_timerInit_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OStimer_Init
                  vl logicl OS_timerInitPre ct->
      Some r =
      BuildRetI os_internal OStimer_Init vl logicl OS_timerInitPost ct->
      exists t d1 d2 s,
        os_internal OStimer_Init = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p }} s {{Afalse}}. 
Proof.
  init_spec.

  simpl in H4, H0, H.
  inversion H4;subst v'8. 
  inversion H0;subst v'7.
  inversion H;subst v'6.
  rename v'11 into aop.
  rename v'12 into er.
  rename v'10 into tmri.
  rename v'9 into emumgt_clkpsd.
  rename i1 into prdhi.
  rename i0 into prdlo.  


  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  (* TimerRegs_CNTLO ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 4 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::8::16::20::17::21::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=4%nat);eauto.
  lia.
  (*TimerRegs_CNTHI ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 5 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=5%nat);eauto.
  lia.
  (* TimerRegs_PRDLO ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 6 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=6%nat);eauto.
  lia.
  (* TimerRegs_PRDHI ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 7 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=7%nat);eauto.
  lia.
  (* TimerRegs_EMUMGT_CLKSPD ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 1 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=1%nat);eauto.
  (* TimerRegs_TGCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 9 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=9%nat);eauto.
  lia.
  (* TimerRegs_TCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 8 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::12::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:=8%nat);eauto.
  lia.
  (* OSreset_timer (­ os_code_defs.timerid ′­);ₛ *)
  hoare lifts (1::13::14::15::16::17::18::4::5::nil)%nat pre.
  hoare_call.
  instantiate (1:= (logic_lv tmri ::logic_ier er :: logic_code aop :: nil));reflexivity.
  { intros. sep destruct H1.
    exists init_lg.
    sep auto. }
  { intros. sep destruct H1.
    exists init_lg.
    sep auto. }
  inversion H2. subst v'8 v'9 v'10.
  rename v'7 into tmrid.
  (* meger two cases in reset post into one *)
  hoare lifts (8::nil)%nat pre.
  hoare remember (1::nil)%nat pre.
  eapply backward_rule1.
  instantiate (1:= EX tmri', AOSTMRNode tmrid tmri' ** 
  [|tmri' = (update_nth_val 7 (update_nth_val 8 tmri (V$ 0)) (V$ 0)) \/ 
    tmri' = tmri |] ** H).
  intros s Hs.
  apply disj_split_star in Hs.
  destruct Hs.
  { exists (update_nth_val 7 (update_nth_val 8 tmri (V$ 0)) (V$ 0)).
    sep cancel H.
    sep auto. }
  { exists (tmri).
    sep cancel H.
    sep auto.  }
  subst H.
  pure intro.
  rename v'6 into new_tmri.
  unfold tmrregsLists;cbn [nth].
  (* ∗ TimerRegs_CNTLO ′ =ₑ ′ 0;ₛ *)
  unfold AOSTMRNode at 2. 
  pure intro.
  hoare forward.
  (* ∗ TimerRegs_CNTHI ′ =ₑ ′ 0;ₛ *)
  hoare forward.
  (* ∗ TimerRegs_PRDLO ′ =ₑ os_code_defs.prdlo ′;ₛ *)
  hoare forward.
  (* ∗ TimerRegs_PRDHI ′ =ₑ os_code_defs.prdhi ′;ₛ *)
  hoare forward.
  (* ∗ TimerRegs_TGCR ′ =ₑ
  ′ CSL_TMR_TIMMODE_GPT ≪ ′ CSL_TMR_TGCR_TIMMODE_SHIFT |ₑ
  ′ CSL_TMR_TGCR_TIMLORS_RESET_OFF ≪ ′ CSL_TMR_TGCR_TIMLORS_SHIFT |ₑ
  ′ CSL_TMR_TGCR_TIMHIRS_RESET_OFF ≪ ′ CSL_TMR_TGCR_TIMHIRS_SHIFT;ₛ *)
  hoare forward.
  assert (Int.ltu ($ CSL_TMR_TGCR_TIMMODE_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TGCR_TIMLORS_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TGCR_TIMHIRS_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  cbn [val_inj or].
  assert ((Int.or
           (Int.or ($ CSL_TMR_TIMMODE_GPT<<ᵢ$ CSL_TMR_TGCR_TIMMODE_SHIFT)
              ($ CSL_TMR_TGCR_TIMLORS_RESET_OFF<<ᵢ$ CSL_TMR_TGCR_TIMLORS_SHIFT))
           ($ CSL_TMR_TGCR_TIMHIRS_RESET_OFF<<ᵢ$ CSL_TMR_TGCR_TIMHIRS_SHIFT)) = ($ 3)).
  { unfold CSL_TMR_TIMMODE_GPT, CSL_TMR_TGCR_TIMMODE_SHIFT, 
    CSL_TMR_TGCR_TIMLORS_RESET_OFF, CSL_TMR_TGCR_TIMLORS_SHIFT, 
    CSL_TMR_TGCR_TIMHIRS_RESET_OFF, CSL_TMR_TGCR_TIMHIRS_SHIFT.
    mauto. }
  rewrite H0;clear H0.
  (* ∗ TimerRegs_EMUMGT_CLKSPD ′ &= ′ CSL_TMR_EMUMGT_CLKSPD_MASK;ₛ *)
  hoare forward.
  (* ∗ TimerRegs_TCR ′ =ₑ
′ CSL_TMR_CLOCK_INP_NOGATE ≪ ′ CSL_TMR_TCR_TIEN_LO_SHIFT |ₑ
′ CSL_TMR_CLKSRC_INTERNAL ≪ ′ CSL_TMR_TCR_CLKSRC_LO_SHIFT |ₑ
′ CSL_TMR_ENAMODE_CONT ≪ ′ CSL_TMR_TCR_ENAMODE_LO_SHIFT |ₑ ′ 0 ≪ ′ CSL_TMR_TCR_PWID_LO_SHIFT |ₑ
′ CSL_TMR_CP_CLOCK ≪ ′ CSL_TMR_TCR_CP_LO_SHIFT |ₑ ′ CSL_TMR_INVINP_UNINVERTED ≪ ′ CSL_TMR_TCR_INVINP_LO_SHIFT |ₑ
′ CSL_TMR_INVOUTP_UNINVERTED ≪ ′ CSL_TMR_TCR_INVOUTP_LO_SHIFT |ₑ ′ 0 ≪ ′ CSL_TMR_TCR_TSTAT_LO_SHIFT;ₛ *)
  hoare forward.
  assert (Int.ltu ($ CSL_TMR_TCR_TIEN_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_CLKSRC_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_ENAMODE_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_PWID_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_CP_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_INVINP_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_INVOUTP_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  assert (Int.ltu ($ CSL_TMR_TCR_TSTAT_LO_SHIFT) Int.iwordsize = true) by pauto.
  rewrite H0;clear H0.
  cbn [val_inj or].
  assert ((Int.or
           (Int.or
              (Int.or
                 (Int.or
                    (Int.or
                       (Int.or
                          (Int.or ($ CSL_TMR_CLOCK_INP_NOGATE<<ᵢ$ CSL_TMR_TCR_TIEN_LO_SHIFT)
                             ($ CSL_TMR_CLKSRC_INTERNAL<<ᵢ$ CSL_TMR_TCR_CLKSRC_LO_SHIFT))
                          ($ CSL_TMR_ENAMODE_CONT<<ᵢ$ CSL_TMR_TCR_ENAMODE_LO_SHIFT))
                       ($ 0<<ᵢ$ CSL_TMR_TCR_PWID_LO_SHIFT)) ($ CSL_TMR_CP_CLOCK<<ᵢ$ CSL_TMR_TCR_CP_LO_SHIFT))
                 ($ CSL_TMR_INVINP_UNINVERTED<<ᵢ$ CSL_TMR_TCR_INVINP_LO_SHIFT))
              ($ CSL_TMR_INVOUTP_UNINVERTED<<ᵢ$ CSL_TMR_TCR_INVOUTP_LO_SHIFT))
           ($ 0<<ᵢ$ CSL_TMR_TCR_TSTAT_LO_SHIFT)) = ($ 136)).
  { clear.
    unfold CSL_TMR_CLOCK_INP_NOGATE, CSL_TMR_TCR_TIEN_LO_SHIFT,
    CSL_TMR_CLKSRC_INTERNAL,CSL_TMR_TCR_CLKSRC_LO_SHIFT,CSL_TMR_ENAMODE_CONT,
    CSL_TMR_TCR_ENAMODE_LO_SHIFT, CSL_TMR_TCR_PWID_LO_SHIFT,CSL_TMR_CP_CLOCK,
    CSL_TMR_TCR_CP_LO_SHIFT,CSL_TMR_INVINP_UNINVERTED,CSL_TMR_TCR_INVINP_LO_SHIFT,
    CSL_TMR_INVOUTP_UNINVERTED,CSL_TMR_TCR_INVOUTP_LO_SHIFT,CSL_TMR_TCR_TSTAT_LO_SHIFT.
    assert (($ 0<<ᵢ$ 9) = Int.zero) by mauto.
    rewrite H;clear H.
    assert (($ 0<<ᵢ$ 8) = Int.zero) by mauto.
    rewrite H;clear H.
    assert (($ 0<<ᵢ$ 4) = Int.zero) by mauto.
    rewrite H;clear H.
    assert (($ 0<<ᵢ$ 2) = Int.zero) by mauto.
    rewrite H;clear H.
    assert (($ 0<<ᵢ$ 1) = Int.zero) by mauto.
    rewrite H;clear H.
    assert (($ 0<<ᵢ$ 0) = Int.zero) by mauto.
    rewrite H;clear H.
    repeat rewrite Int.or_zero.
    rewrite (Int.or_commut Int.zero).
    rewrite Int.or_zero.
    mauto.  }
  rewrite H0;clear H0.
  (* RETURN *)
  hoare forward.
  destruct H.
  - do 11 (destruct tmri;tryfalse).
    simpl in H.
    inversion H;subst.
    cbn [update_nth_val].
    unfold AOSTMRNode.
    sep auto.
    instantiate (1:= v1).
    unfold tmrinit_emumgt_clkpsd.
    unfold V_OSEMUMGT in H5.
    simpl in H5.
    inverts H5.
    auto.
  - subst tmri.
    cbn [update_nth_val].
    unfold AOSTMRNode.
    sep auto.
    instantiate (1:= v'8).
    unfold tmrinit_emumgt_clkpsd.
    unfold V_OSEMUMGT in H5.
    simpl in H5.
    inverts H5.
    auto.
  Qed.
