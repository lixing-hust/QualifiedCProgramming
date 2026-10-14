(* Require Import lemmasfortoptheo.  *)
(* Require Import oscorrectness.  *)
Require Import PIF_sys.
(* Require Import PIF_succs. *)
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
Require Import PIF_LibTactics.
Require Import Integers.

Require Import PIF_os_code_defs.
Open Scope nat_scope.

Require Import mux_succ_gen.

Require Import pif_tacs. 

Lemma callcont_goodks:
  forall ks f s le ks',
    callcont ks = Some (kcall f s le ks') ->
    goodks_h ks ->
    goodks_h ks'.
Proof.
  induction ks; intros;simpl in *;auto; tryfalse;mytac.
  inverts H; auto.
Qed.


Ltac des_inv Hgc rights :=
  match goal with
    H: (if ?t then _ else _) = Some _ |- _ =>
      destruct t;
      [match goal with H: Some _ = Some _ |- _ => inverts H end; 
       simpl; simpl in Hgc; simpljoin;
       split; eauto;
       unfolds; rights; left; eexists; eauto;
                   unfolds; left; eauto |
                  idtac
      ]
  end.

Lemma n_spec_lp_muxunlock: 
  forall vl, has_spec_lp (mutexunlock vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed.

Local Hint Resolve n_spec_lp_muxunlock: spec_lp_contra_lemmas. 

Lemma n_spec_lp_muxlock: 
  forall vl, has_spec_lp (mutexlock vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_muxlock: spec_lp_contra_lemmas. 

Lemma n_spec_lp_timedlock: 
  forall vl, has_spec_lp (mutextimedlock vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_timedlock: spec_lp_contra_lemmas. 

Lemma n_spec_lp_trylock: 
  forall vl, has_spec_lp (mutextrylock vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_trylock: spec_lp_contra_lemmas. 

Lemma n_spec_lp_init: 
  forall vl, has_spec_lp (mutex_init vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_init: spec_lp_contra_lemmas. 

Lemma n_spec_lp_destroy: 
  forall vl, has_spec_lp (mutex_destroy vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_destroy: spec_lp_contra_lemmas. 

Lemma n_spec_lp_attrinit: 
  forall vl, has_spec_lp (mutexattrinit vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_attrinit: spec_lp_contra_lemmas. 

Lemma n_spec_lp_attrdestroy: 
  forall vl, has_spec_lp (mutexattrdestroy vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_attrdestroy: spec_lp_contra_lemmas. 

Lemma n_spec_lp_attrsettype: 
  forall vl, has_spec_lp (mutexattrsettype vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_attrsettype: spec_lp_contra_lemmas. 

Lemma n_spec_lp_attrgettype: 
  forall vl, has_spec_lp (mutexattrgettype vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_attrgettype: spec_lp_contra_lemmas. 

Lemma n_spec_lp_setprioceiling: 
  forall vl, has_spec_lp (mutexattrsetprioceiling vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_setprioceiling: spec_lp_contra_lemmas. 

Lemma n_spec_lp_getprioceiling: 
  forall vl, has_spec_lp (mutexattrgetprioceiling vl) -> False. 
Proof. 
  introv Hf.
  repeat
    (destruct vl; 
     [ solve [simpl in Hf; inverts Hf ] | idtac]).
  simpl in Hf.
  destruct vl;
    repeat (match goal with H: context[has_spec_lp] |- _ => inverts H end).
Qed. 

Local Hint Resolve n_spec_lp_getprioceiling: spec_lp_contra_lemmas. 


Ltac succ_tac Hor rights :=
  let h_ := fresh "H_" in 
  destruct Hor; 
  [
    simpljoin; 
    lets h_: succ_step_preserve; eauto; 
    specializes h_; eauto; 
    eauto with spec_lp_contra_lemmas; 
    destruct h_; [rights; left; eexists; eauto | auto 20] |
    idtac
  ]. 

Lemma hapistep_goodcode:
  forall C O c O',
    goodcode_h C->
    hapistep os_spec' C O c O' ->
    goodcode_h c.
Proof.
  introv Hgc Hsp.
  inverts Hsp.
  - (* api enter *)
    unfolds in H.
    inverts H.
    match goal with H: api_spec' _ = _ |- _ => unfolds in H; inverts H end.
    des_inv Hgc (idtac).
    des_inv Hgc ltac:(do 1 right).
    des_inv Hgc ltac:(do 2 right).
    des_inv Hgc ltac:(do 3 right).
    des_inv Hgc ltac:(do 4 right).
    des_inv Hgc ltac:(do 5 right).
    des_inv Hgc ltac:(do 6 right).
    des_inv Hgc ltac:(do 7 right).
    des_inv Hgc ltac:(do 8 right).
    des_inv Hgc ltac:(do 9 right).
    des_inv Hgc ltac:(do 10 right).
    des_inv Hgc ltac:(do 11 right).
    tryfalse. 
  - (* id api *)
    simpl in Hgc.
    simpl.
    simpljoin; split; auto.
    unfold good_api_stmt in *.
    succ_tac H0 (idtac).
    succ_tac H0 ltac:(do 1 right).
    succ_tac H0 ltac:(do 2 right).
    succ_tac H0 ltac:(do 3 right).
    succ_tac H0 ltac:(do 4 right).
    succ_tac H0 ltac:(do 5 right).
    succ_tac H0 ltac:(do 6 right).
    succ_tac H0 ltac:(do 7 right).
    succ_tac H0 ltac:(do 8 right).
    succ_tac H0 ltac:(do 9 right).    
    succ_tac H0 ltac:(do 10 right).    
    succ_tac H0 ltac:(do 11 right).        
    destruct H0. subst. inverts H.
    simpljoin. inverts H.
  - (* api exit *)
    simpl. simpl in Hgc.
    simpljoin; auto.
  - (* int exit *) 
    simpl. simpl in Hgc.
    simpljoin; auto.
Qed. 

Lemma htstep_goodcode_h:
  forall pc t C cst O c cst' O',
    good_client_code pc ->
    htstep (pc, os_spec') t C cst O c cst' O' ->
    goodcode_h C ->
    goodcode_h c.
Proof.
  intros.
  inverts H0.
  inverts H2.
  inverts H3.
  inverts H2;simpl in H1;simpl;mytac;auto;tryfalse.
  inverts H2;simpl in H1;simpl;mytac;auto;tryfalse.
  splits; auto.
  apply H in H4.
  clear -H4.
  induction s;simpl in H4;simpl;auto; tryfalse.
  splits; auto.
  mytac. mytac.
  mytac.
  splits; auto.
  splits; auto.
  eapply callcont_goodks;eauto.
  inverts H2.
  eapply hapistep_goodcode; eauto. 
Qed. 
  
(* Lemma hpstepok_goodcode_h: *)
(*   forall pc T cst O T' cst' O', *)
(*     goodtasks_h T -> *)
(*     good_client_code pc -> *)
(*     hpstepok (pc,os_spec') T cst O T' cst' O' -> *)
(*     goodtasks_h T'. *)
(* Proof. *)
(*   introv Hgt Hgcc Hsp. *)
(*   inverts Hsp. *)
(*   inverts H. *)
(*   -  (* htstep *) *)
(*     unfold goodtasks_h in *. *)
(*     introv Hget. *)
(*     casetac t t0 Ht Hf. *)
(*     + subst. rewrite TasksMod.set_a_get_a in Hget.  *)
(*       inverts Hget. *)
(*       specializes Hgt; eauto. *)
(*       match goal with H: context[htstep] |- _ => inverts H end. *)
(*       inverts H. *)
(*       eapply htstep_goodcode_h;eauto. *)
(*       apply tidspec.eq_beq_true; auto.  *)
(*     + rewrite TasksMod.set_a_get_a' in Hget; eauto. *)
(*       apply tidspec.neq_beq_false; eauto.  *)
(*   - (* htistep *)  *)
(*     match goal with H: (_, _) = _ |- _ => inverts H end. *)
(*     match goal with *)
(*       H: context[htistep] |- _ =>  unfold int_spec', int_spec_list' in H; simpl in H; inverts H *)
(*     end. *)
(*     tryfalse.  *)

Lemma succ0_sub2:
  forall cd1 cd2 cd, 
    has_succ0 cd (spec_seq cd1 cd2) ->
    has_succ0 cd cd2.
Proof. 
  introv Hhs.
  remember cd1 as CD1.
  remember cd2 as CD2.
  remember cd as CD.
  gen cd1 cd2 cd.
  inductions Hhs; introv Heq1 Heq2 Heq3; subst;
    try (constructors; fail).
  - 
    eapply hs_seq3; eauto.
    constructors. 
  -
    inverts Hhs.
    + 
      constructors. constructors.
    +
      constructors. constructors. constructors.
    +
      specializes IHHhs; eauto. constructors. auto.
    +
      constructors. constructors. constructors.
    +
      specializes IHHhs; eauto. constructors. auto.
    +
      constructors. eapply hs_choice2; eauto. constructors.
    +
      specializes IHHhs; eauto. constructors. auto.
    +
      constructors. constructors.
    +
      constructors. constructors. 
  -
    constructors. constructors. 
  -
    specializes IHHhs; eauto.
    constructors. auto.
  -
    eapply hs_choice2; eauto.
    constructors.
  -
    specializes IHHhs; eauto.
    eapply hs_choice2; eauto.
Qed.     

Lemma succ_sub2:
  forall cd1 cd2 cd, 
    has_succ cd (spec_seq cd1 cd2) ->
    has_succ cd cd2.
Proof.
  introv Hhs.
  unfold has_succ in *.
  destruct Hhs; subst.
  - right. constructors.
  - right. eapply succ0_sub2; eauto. 
Qed.     
  
Lemma hpstepok_goodcode_h:
  forall pc T cst O T' cst' O',
    goodtasks_h T ->
    good_client_code pc ->
    hpstepok (pc,os_spec') T cst O T' cst' O' ->
    goodtasks_h T'.
Proof.
  introv Hgt Hgcc Hsp.
  inverts Hsp.
  inverts H.
  -  (* htstep *)
    unfold goodtasks_h in *.
    introv Hget.
    casetac t t0 Ht Hf.
    + subst. rewrite TasksMod.set_a_get_a in Hget. 
      inverts Hget.
      specializes Hgt; eauto.
      eapply htstep_goodcode_h;eauto.
      apply tidspec.eq_beq_true; auto. 
    + rewrite TasksMod.set_a_get_a' in Hget; eauto.
      apply tidspec.neq_beq_false; eauto. 
  - (* htistep *) 
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with
      H: context[htistep] |- _ =>  unfold int_spec', int_spec_list' in H; simpl in H; inverts H
    end.
    tryfalse. 
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    unfold goodtasks_h in *.
    introv Hget.
    casetac t t0 Ht Hf.
    + subst. rewrite TasksMod.set_a_get_a in Hget.
      2: { apply tidspec.eq_beq_true; eauto. } 
      inverts Hget.
      specializes Hgt; eauto.
      simpl in Hgt.
      simpl.
      simpljoin; split; eauto.
      unfold good_api_stmt in H.
      destruct H; simpljoin.
      unfolds. left. eexists. eapply succ_sub2; eauto. 
      destruct H; simpljoin.
      unfolds. right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 2 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 3 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 4 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 5 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 6 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin.
      unfolds. do 7 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin. 
      unfolds. do 8 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin. 
      unfolds. do 9 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin. 
      unfolds. do 10 right; left. eexists. eapply succ_sub2; eauto.
      destruct H; simpljoin. 
      unfolds. do 11 right; left. eexists. eapply succ_sub2; eauto.
      inverts H. false. simpljoin. false. 
    +
      rewrite TasksMod.set_a_get_a' in Hget.
      2: { apply tidspec.neq_beq_false; eauto. }
      eapply Hgt; eauto. 
Qed.       
      
Lemma hpstepstarok_goodcode_h:
  forall pc T cst O T' cst' O',
    hpstepstarok (pc,os_spec') T cst O T' cst' O' ->
    goodtasks_h T ->
    good_client_code pc ->
    goodtasks_h T'.
Proof.
  intros.
  inductions H;auto.
  eapply IHhpstepstarok;eauto.
  eapply hpstepok_goodcode_h;eauto.
Qed.

(*  *)
