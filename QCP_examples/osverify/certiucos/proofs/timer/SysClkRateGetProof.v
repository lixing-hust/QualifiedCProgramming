Require Import ucos_include.
Require Import Lia.
Require Import tmr_tactics.


Open Scope code_scope.
(* SYS_CLK_RATE_GET Proof *)
Open Scope int_scope.



Lemma sys_clk_rate_get_high_level_step :
  forall P t ct sch tmrls clkrate,
    can_change_aop P ->
     sch    ⊢   (<|| clkrategetcode nil ||> ** 
                       HTime t ** HCurTCB ct ** 
                       HTMRList tmrls **
                       HClkRate clkrate **  P) ⇒
             (<|| END (Some (Vint32 clkrate)) ||> ** 
                  HTime t ** HCurTCB ct  **   HTMRList tmrls ** HClkRate clkrate **  P)  .
Proof.
  infer_solver 0%nat. Qed.

Lemma OSsys_clk_rate_getProof :
  forall vl p r tid ,
    Some p = BuildPreA' os_api sys_clk_rate_get clkrategetapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api sys_clk_rate_get clkrategetapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api sys_clk_rate_get = Some (t, d1, d2, s) /\
      {| OS_spec, GetHPrio, OSLInv, I, r, Afalse |} |-tid {{ p }} s {{ Afalse }}.
Proof.
  init_spec.
  hoare forward prim.
  unfold TmrInv, TmrInv'.
  hoare normal pre.
  pure intro.
  unfold AOSClkRate; hoare forward.
  hoare normal pre.
  hoare_abscsq_tmr1.
  + apply noabs_oslinv.
  + eapply sys_clk_rate_get_high_level_step.
    can_change_aop_solver.
  + hoare forward prim.
    - unfold TmrInv, TmrInv', AOSClkRate in *.
      sep pauto.
      trycancel.
      exact H1.
    - go.
    - go.
    - hoare forward.
Qed.
