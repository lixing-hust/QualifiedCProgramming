Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.
Require Import TimerOutConfigRules.

Open Scope code_scope.
(* timer outconfig Proof *)
Open Scope int_scope.

Lemma OS_timerOutConfig_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OStimer_outConfig
                  vl logicl OS_timerOutConfigPre ct->
      Some r =
      BuildRetI os_internal OStimer_outConfig vl logicl OS_timerOutConfigPost ct->
      exists t d1 d2 s,
        os_internal OStimer_outConfig = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p }} s {{Afalse}}. 
Proof.
  init_spec.

  pure intro.
  rename v'4 into aop.
  rename v'5 into er.
  rename v'0 into i.
  rename v'2 into tmri.
  rename v'1 into outputmode_v.

  (* TimerRegs_TCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 8 +ₑ (os_code_defs.timerid ′ ≪ ′ 14));ₛ *)
  hoare lifts (1::11::9::13::10::14::nil)%nat pre.
  eapply seq_rule.
  eapply timer_assign_timerregs_shl with (n:= 8%nat);eauto.
  lia.
  unfold tmrregsLists.
  cbn [nth].
  (* IF (outputmode ′) *)
  eapply seq_rule.
  eapply ss_if_else_rule; [ symbolic execution
  | idtac 
  | idtac ].
  - (* if branch *)
    pure intro.
    hoare lifts (1::13::2::14::5::6::nil)%nat pre.
    eapply OS_timerOutConfigProof_outmodeneq0;eauto.
    apply Int.eq_false.
    unfold not;intro.
    rewrite H5 in H.
    tryfalse.
  - (* else branch *)
    pure intro.
    hoare lifts (1::13::2::14::5::6::nil)%nat pre.
    eapply OS_timerOutConfigProof_outmodeeq0;eauto.
    apply Int_eq_dec.
    destruct H;[ | tryfalse].
    inversion H;auto.
  - (* end if else *) 
    (* RETURN *)
    hoare forward.
Qed.