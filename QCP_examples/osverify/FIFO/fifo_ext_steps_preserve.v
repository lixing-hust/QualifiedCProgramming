
Require Import log_code_defs.
Require Import log_code_notations.

Require Import FIFO_inv_and_init.
Require Import FIFO_spec. 
(* Require Import FIFO_succ.  *)
Require Import FIFO_sys.
Require Import FIFO_pure.

Require Import mqinit_dtinv_preserve.
Require Import mqdelete_dtinv_preserve.
Require Import mqsend_dtinv_preserve.
Require Import mqrecv_dtinv_preserve.
Require Import mqtimedrecv_dtinv_preserve.
Require Import mqgetinfo_dtinv_preserve.

Require Import mq_succ_gen. 
          
Require Import seplog_tactics.
Import DeprecatedTactic.

Open Scope type_scope.
Open Scope list_scope.

Lemma fifo_ext_hpstep_preserve: 
  forall client_code T cst O T' O' cst',
    goodtasks_h T ->
    FIFO_ext O ->
    hpstep (client_code, os_spec') T cst O T' cst' O'->
    FIFO_ext O'.
Proof.
  introv Hgt Hfe Hsp.
  inverts Hsp.
  - (* htstep *)
    match goal with H: context[htstep] |- _ => inverts H end; 
    match goal with H: (_, _) = _ |- _ => inverts H end.
    + (* cstep *)
      auto.
    + (* hapistep *)
      match goal with H: context[hapistep] |- _ => inverts H end.
      * (* api enter *)
        auto.
      * (* id api *)
        specializes Hgt; eauto.
        unfolds in Hgt.
        destruct Hgt as (Hgcd & Hgk).
        do 3 unfolds in Hgcd.
        
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqcreate_dtinv_preserve; eauto.
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqdelete_dtinv_preserve; eauto.
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqsend_dtinv_preserve; eauto.
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqrecv_dtinv_preserve; eauto.
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqtimedrecv_dtinv_preserve; eauto.
        destruct Hgcd as [(vl & Hs) | Hgcd].
        eapply mqgetinfo_dtinv_preserve; eauto.
        destruct Hgcd. subst.
        match goal with H: context[spec_step] |- _ => inverts H end.
        simpljoin. 
        match goal with H: context[spec_step] |- _ => inverts H end.
      * (* api exit *)
        auto.
      * (* int exit *)
        auto.
        
  - (* htistep *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with H: context[htistep] |- _ => inverts H end.
    unfolds in H. unfold int_spec_list in H.
    simpl in H. tryfalse.
    
  - (* sched *)
    unfolds.
    intros.
    rewrite map_get_set' in H3; auto.
    rewrite map_get_set' in H7; auto.
    rewrite map_get_set' in H9; eauto.
Qed. 

    
        
        
        
        
        
      
