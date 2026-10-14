Require Import Lia.

Require Import join_lib_aux.
Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.

Open Scope int_scope.

Lemma OS_timerOutConfigProof_outmodeneq0: forall 
r ri P
(ct: tid)
(v': val)
(i outputmode_v tcg: int32) tmri
(aop: absop),
Int.ltu ($ 0) i = true ->
Int.ltu i ($ 16) = true ->
V_OSTCRreg tmri = Some (Vint32 tcg) ->
Int.eq Int.zero outputmode_v = false ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode i tmri **
  LV TimerRegs_TCR @ (Int32u) ∗ |-> Vptr (timer_TCR i) **
  LV outputmode @ Int32u |-> Vint32 outputmode_v **
  p_local OSLInv ct init_lg **
  A_dom_lenv
     ((outputmode, Int32u)
      :: (os_code_defs.timerid, Int32u)
         :: (TimerRegs_TCR, (Int32u) ∗) :: nil)** P }}
∗ TimerRegs_TCR ′ =ₑ ∗ TimerRegs_TCR ′ |ₑ ′ 8
{{ <|| aop ||>  **
  AOSTMRNode i (update_nth_val 7 tmri (Vint32 (tmroutmode_config tcg outputmode_v))) **
  LV TimerRegs_TCR @ (Int32u) ∗ |-> Vptr (timer_TCR i) **
  LV outputmode @ Int32u |-> Vint32 outputmode_v **
  p_local OSLInv ct init_lg **
  A_dom_lenv
     ((outputmode, Int32u)
      :: (os_code_defs.timerid, Int32u)
         :: (TimerRegs_TCR, (Int32u) ∗) :: nil)** P }}.
Proof.
  intros.
  unfold AOSTMRNode.
  pure intro.
  unfold V_OSTCRreg in H1.
  simpl in H1.
  inversion H1;subst v'7.
  unfold tmroutmode_config.
  rewrite H2.
  hoare forward.
  simpl.
  eauto.
Qed.

Lemma OS_timerOutConfigProof_outmodeeq0: forall 
r ri P
(ct: tid)
(v': val)
(i outputmode_v tcg: int32) tmri
(aop: absop),
Int.ltu ($ 0) i = true ->
Int.ltu i ($ 16) = true ->
V_OSTCRreg tmri = Some (Vint32 tcg) ->
Int.eq Int.zero outputmode_v = true ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-ct 
{{ <|| aop ||>  **
  AOSTMRNode i tmri **
  LV TimerRegs_TCR @ (Int32u) ∗ |-> Vptr (timer_TCR i) **
  LV outputmode @ Int32u |-> Vint32 outputmode_v **
  p_local OSLInv ct init_lg **
  A_dom_lenv
     ((outputmode, Int32u)
      :: (os_code_defs.timerid, Int32u)
         :: (TimerRegs_TCR, (Int32u) ∗) :: nil)** P }}
∗ TimerRegs_TCR ′ &= ′ 4294967287
{{ <|| aop ||>  **
  AOSTMRNode i (update_nth_val 7 tmri (Vint32 (tmroutmode_config tcg outputmode_v))) **
  LV TimerRegs_TCR @ (Int32u) ∗ |-> Vptr (timer_TCR i) **
  LV outputmode @ Int32u |-> Vint32 outputmode_v **
  p_local OSLInv ct init_lg **
  A_dom_lenv
     ((outputmode, Int32u)
      :: (os_code_defs.timerid, Int32u)
         :: (TimerRegs_TCR, (Int32u) ∗) :: nil)** P }}.
Proof.
  intros.
  unfold AOSTMRNode.
  pure intro.
  unfold V_OSTCRreg in H1.
  simpl in H1.
  inversion H1;subst v'7.
  unfold tmroutmode_config.
  rewrite H2.
  hoare forward.
  simpl.
  eauto.
Qed.