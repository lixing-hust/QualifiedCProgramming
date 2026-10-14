Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.
Require Import TimerConfigRules.

Open Scope code_scope.
(* timer config Proof *)
Open Scope int_scope.


Lemma OS_timerConfig_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OStimer_Config
                  vl logicl OS_timerConfigPre ct->
      Some r =
      BuildRetI os_internal OStimer_Config vl logicl OS_timerConfigPost ct->
      exists t d1 d2 s,
        os_internal OStimer_Config = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p }} s {{Afalse}}.   
Proof.
  init_spec.

  pure intro.
  rename v'6 into aop.
  rename v'7 into Aier.
  rename v'0 into tmrid_i.
  rename v'5 into tmri.
  (* timerx ′ =ₑ 〈 OSTimerRegs ∗ 〉 (__timerregs ′ +ₑ (os_code_defs.timerid ′ ≪ ′ 14));ₛ *)
  hoare lifts (1::11::9::16::10::17::nil)%nat pre.
  eapply seq_rule.
  eapply OS_timerConfigProofPart0;eauto.
  (* timerx ′ → OSPRDLO =ₑ prdlo ′;ₛ *)
  hoare lifts (1::13::2::17::5::6::nil)%nat pre.
  hoare forward.
  eapply OS_timerConfigProofPart1;eauto.
  (* timerx ′ → OSPRDHI =ₑ prdhi ′;ₛ *)
  hoare lifts (1::2::3::17::5::6::nil)%nat pre.
  hoare forward.
  eapply OS_timerConfigProofPart2;eauto.
  (* timerx ′ → OSCNTLO =ₑ ′ 0;ₛ *)
  hoare lifts (1::2::3::5::6::nil)%nat pre.
  hoare forward.
  eapply OS_timerConfigProofPart3;eauto.
  (* timerx ′ → OSCNTHI =ₑ ′ 0;ₛ *)
  hoare forward.
  eapply OS_timerConfigProofPart4;eauto.
  (* IF (mode ′) *)
  eapply seq_rule.
  eapply ss_if_else_rule;[ symbolic execution | idtac ..].
  - (* enter if branch *)
    pure intro.
    assert (Int.eq Int.zero v'3 = false).
    { apply Int.eq_false. unfold not;intro.
      apply H.
      rewrite H4;auto. }
    (* timerx ′ → OSTCRreg =ₑ ′ 128 *)
    hoare lifts (1::2::3::17::4::5::nil)%nat pre.
    hoare forward.
    eapply OS_timerConfigProofPart5_modeneq0;eauto.
  - (* enter else branch *)
    pure intro.
    assert (Int.eq Int.zero v'3 = true).
    { apply Int_eq_dec. 
      destruct H;[ | inversion H].
      inversion H.
      auto. }
    (* timerx ′ → OSTCRreg =ₑ ′ 64 *)
    hoare lifts (1::2::3::17::4::5::nil)%nat pre.
    hoare forward.
    eapply OS_timerConfigProofPart5_modeeq0;eauto.
  - (* end if else*)
  eapply seq_rule.
  eapply ss_if_else_rule;[ symbolic execution | idtac ..].
  + (* enter if branch *)
    pure intro. 
    assert (Int.eq Int.zero v'4 = false).
    { apply Int.eq_false. unfold not;intro.
      apply H.
      rewrite H4;auto. }
    (* timerx ′ → OSTGCR *)
    hoare lifts (1::2::3::17::5::6::nil)%nat pre.
    hoare forward.
    eapply OS_timerConfigProofPart5_64bitneq0;eauto.
  + (* enter else branch *)
    pure intro.
    assert (Int.eq Int.zero v'4 = true).
    { apply Int_eq_dec. 
      destruct H;[ | inversion H].
      inversion H.
      auto. }
    (* timerx ′ → OSTGCR =ₑ ′ 4 *)
    hoare lifts (1::2::3::17::5::6::nil)%nat pre.
    hoare forward.
    eapply OS_timerConfigProofPart5_65biteq0;eauto.
  + (* end if else*)
    (* RETURN *)
    hoare forward.
Qed.

