(*
Definition exception_handler_set_impl :=
Int32 ·exception_handler_set·(⌞ handler@Int32 ⌟)··{
  ⌞ old_handler@Int32 ⌟;
  ENTER_CRITICAL;ₛ
  old_handler′ =ₑ exception_handler′;ₛ
  exception_handler′ =ₑ handler′;ₛ
  EXIT_CRITICAL;ₛ
  RETURN old_handler′
}·.
*)
Require Import ucos_include.
(*Require Import oscore_common.*)
Require Import ios_int_tick.
Require Import ios_int.
Require Import ios_int_tac.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.

Lemma Exception_handler_set_step :
  forall P sch exchandler i vl',
    can_change_aop P ->
     absinfer sch (<|| exchandler_setcode (Vint32 i :: vl')||> ** Hhexchandler exchandler ** P)
             (<|| END (Some (Vint32 exchandler))||> ** Hhexchandler i ** P)  .
Proof.
  intros.
  simpljoin.
  infer_solver 0%nat.
Qed.

Definition Old_BuildPreA':= 
  fun (p : progunit) (f : fid) (abs : osapi) (vl : vallist)  (pa : LocalInv) t lg=>
    match p f with
      | Some (_, d1, d2, _) =>
        match dl_vl_match d1 (rev vl) with
          | true =>
            match buildp (dladd d1 d2) vl with
              | Some p2 =>
                Some   
                  ( ((<|| (fst abs) (rev vl) ||> ** p_local pa t lg ** p2 **Aie true ** Ais nil ** Acs nil ** Aisr empisr) ** A_dom_lenv (getlenvdom (revlcons d1 d2))))
                  
              | None => None
            end
          |false => None
        end
      | None => None
    end.

Definition Old_BuildRetA':= 
  fun (p : progunit) (f : fid) (_ : osapi) (_ : vallist) (pa : LocalInv) t lg=>
    match p f with
      | Some (_, d1, d2, _) =>
        match buildq (dladd d1 d2) with
          | Some p2 =>
            Some
              (fun v : option val =>
                 ((  <|| spec_done v ||>  ** p_local pa t lg **p2 **  Aie true ** Ais nil ** Acs nil ** Aisr empisr) **  A_dom_lenv (getlenvdom (revlcons d1 d2))) )
              
          | None => None
        end
      | None => None
    end.

Lemma Exception_handler_setProof: 
  forall tid vl p r, 
    Some p = BuildPreA' os_api exception_handler_set exchandler_setapi vl OSLInv tid init_lg ->
    Some r = BuildRetA' os_api exception_handler_set exchandler_setapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api exception_handler_set = Some (t, d1, d2, s) /\
      {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}}s {{Afalse}}.
Proof.
  (*intros. init_retspec. init_prespec. 
  unfold_internal_pre.
  hoare normal pre.
  hoare_split_pure_all.
  type_val_match_elim. *)
  init spec. (*Initialize Specification*)
  (*L1:  OS_ENTER_CRITICAL();*)
  hoare forward prim; pauto.

  (*L2: old_handler ′ =ₑ exception_handler ′ *)
  hoare unfold.
  unfold IntInv.
  unfold AOSExchandler.
  hoare forward; pauto.
  
  (*L3: exception_handler ′ =ₑ handler ′*)
  hoare forward.
  hoare lifts(10 :: nil)%nat pre.
  hoare normal pre.
  new_hoare_abscsq.
  (*hoare abscsq.*)
  apply noabs_oslinv.
  eapply Exception_handler_set_step.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold aemp_isr_is.
  (*can_change_aop_solver.*)
  pauto.

  (*exists v'0.*)

  (*L4: EXIT_CRITICAL;*)
  hoare forward prim.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel p_local.
  unfold IntInv.
  unfold AOSExchandler.
  sep cancel EvtInv.
  sep cancel Aier.
  sep_unfold. sep pauto.

  (*L5: RETURN old_handler′*)
  auto.
  pure_auto.
  hoare forward. 
Qed.
