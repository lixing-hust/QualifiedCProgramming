
Require Import PIF_sys.
Require Import PIF_spec.
Require Import PIF_language.
Require Import PIF_Modules.
Require Import List.
Require Import PIF_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import PIF_memory.
Require Import PIF_assertion.
Require Import init_and_inv_PIF.
Require Import inv_hold_init.

Open Scope nat_scope.
Require Import Integers.
Open Scope int_scope.
Require Import int_auto. 

Require Import PIF_LibTactics.
Require Import PIF_os_ucos_h.

Require Import aux_lemmas.
Require Import mux_succ_gen. 
Require Import pif_lemmas. 
Require Import pif_tacs. 

Require Import seplog_lemmas. 
Require Import protect. 
Require Import join_lib.

Require Import mutexinit_dtinv_preserve.
Require Import mutexdestroy_dtinv_preserve.
Require Import mutexlock_dtinv_preserve.
Require Import mutextrylock_dtinv_preserve.
Require Import mutextimedlock_dtinv_preserve. 
Require Import mutexunlock_dtinv_preserve.
Require Import mutexattrinit_dtinv_preserve.
Require Import mutexattrdestroy_dtinv_preserve.
Require Import mutexattrsettype_dtinv_preserve.
Require Import mutexattrgettype_dtinv_preserve.
Require Import mutexattrsetprioceiling_dtinv_preserve.
Require Import mutexattrgetprioceiling_dtinv_preserve.

Lemma good_dt_set_curtid:
  forall O t, 
    GOOD_DT O -> 
    GOOD_DT (set O curtid (oscurt t)). 
Proof.
  introv Hgdt.
  unfold GOOD_DT in *.
  introv Hge' Hgt' Hgm' Hgp'.
  eapply Hgdt; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hge'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgt'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgm'; eauto.
  rewrite OSAbstMod.set_a_get_a' in Hgp'; eauto.
Qed. 

Lemma good_dt_hpstepok_preserve:
  forall client_code T cst O T' cst' O' ,
    goodtasks_h T ->
    hpstepok (client_code, os_spec') T cst O T' cst' O' ->
    no_nest_client client_code O T cst ->
    (* good_client_code client_code -> *)
    (* no_abort T -> *)
    GOOD_DT O ->
    GOOD_DT O'.
Proof.
  introv Hgtsks Hsp Hnn Hgdt.
  inverts Hsp.
  match goal with
    H: context [hpstep] |- _ => assert (Hsp_:=H); inverts H
  end.
  - (* htstep *)
    match goal with
      H: context [htstep] |- _ => inverts H
    end.
    + (* cstep *) 
      auto.
    + (* hapistep *)
      match goal with
        H: context [hapistep] |- _ => inverts H
      end.
      * (* api enter *)
        auto.
      * (*  *)
        assert (Hnn1: NO_NEST_PENDING_O O).
        {
          unfolds in Hnn. eapply Hnn; eauto.
          constructors.
        }
        assert (Hnn2: NO_NEST_PENDING_O O').
        {
          unfolds in Hnn. eapply Hnn; eauto.
          repeat (constructors; eauto).
        }
        match goal with H: (_, _) = _ |- _ => inverts H end.
        specializes Hgtsks; eauto.
        simpl in Hgtsks.
        destruct Hgtsks as (Hgevl & Hgcont).

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexunlock_dtinv_preserve with (O:=O) (O':=O'); eauto. 

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexlock_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutextimedlock_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutextrylock_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexinit_dtinv_preserve with (O:=O) (O':=O'); eauto.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexdestroy_dtinv_preserve with (O:=O) (O':=O'); eauto.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrinit_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrdestroy_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrsettype_dtinv_preserve with (O:=O) (O':=O'); eauto.
        
        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrgettype_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrsetprioceiling_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Hhs | Hgevl].
        destruct Hhs as (vl & Hhs).
        eapply mutexattrgetprioceiling_dtinv_preserve with (O:=O) (O':=O'); eauto.

        destruct Hgevl as [Habt | Hend].
        subst cd.
        match goal with H: context[hmstep] |- _ => inverts H end.
        simpljoin.
        match goal with H: context[hmstep] |- _ => inverts H end.

      * (* *)
        auto.
      * (* *)
        auto.

  - (* htistep *)
    match goal with H: context[htistep] |- _ => inverts H end. 
    auto.

  - (* sched *)
    eapply good_dt_set_curtid; eauto. 
Qed. 
        
        
