Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.
(* reset timer Proof *)
Open Scope int_scope.


Lemma OSreset_timer_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSreset_timer
                  vl logicl OS_resettimerPre ct->
      Some r =
      BuildRetI os_internal OSreset_timer vl logicl OS_resettimerPost ct->
      exists t d1 d2 s,
        os_internal OSreset_timer = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p }} s {{Afalse}}. 
Proof.
  init_spec.
  cbn in H. inversion_clear H. subst.
  rename v'1 into id_v.
  rename v'2 into tmri.
  rename v'3 into aop.
  rename v'4 into er.

  (* TimerRegs_TGCR ′ =ₑ NULL;ₛ *)
  hoare forward.
  (* TimerRegs_TCR ′ =ₑ NULL;ₛ *)
  hoare forward.
  (* TimerRegs_TGCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 9 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::3::11::13::12::14::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:= 9%nat);eauto; [ lia |  auto ..].
  unfold tmrregsLists;cbn [nth].
  (* TimerRegs_TCR ′ =ₑ 〈 (Int32u) ∗ 〉 (__timerregs ′ +ₑ ′ 8 +ₑ os_code_defs.timerid ′ × ′ 16384);ₛ *)
  eapply seq_rule.
  hoare lifts (1::7::3::4::5::6::nil)%nat pre.
  eapply timer_assign_timerregs_mul with (n:= 8%nat);[ lia | lia | auto ..].
  unfold tmrregsLists;cbn [nth].
  (* get pv (timer_TGCR id_v)*)
  hoare lifts (13::nil)%nat pre.
  unfold AOSTMRNode at 3.
  pure intro.
  (* If (∗ TimerRegs_TGCR ′) *)
  hoare forward.
  - (* Branch : yes*)
    pure intro.
    (* ∗ TimerRegs_TGCR ′ =ₑ ′ 0;ₛ *)
    hoare forward.
    (* ∗ TimerRegs_TCR ′ =ₑ ′ 0 *)
    hoare forward.
  - (* Branch : no*)
    (* RETURN *)
    hoare forward.
    + hoare forward.
      left.
      unfold V_OSTGCR, AOSTMRNode.
      sep auto.
      { simpl. unfold not;intros H'.
        inversion H'. subst v'9.
        apply H2. auto. }
      { simpl. auto. }
    + hoare forward.
      right.
      unfold V_OSTGCR, AOSTMRNode.
      sep auto.
      { simpl. 
        inversion H2;[ | tryfalse].
        rewrite H9. auto. }
Qed.