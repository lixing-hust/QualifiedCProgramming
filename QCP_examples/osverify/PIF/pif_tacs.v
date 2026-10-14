
Require Import base_tac.
Require Import PIF_memory.
Require Import PIF_language.
Require Import PIF_opsem.
Require Import seplog_lemmas.

Require Import mux_succ_gen.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Ltac l_rew21 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H2 in H1; inverts H1
  end.

Ltac l_rew12 trm :=
  match goal with
    H1: trm = _, H2: trm = _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.

Ltac rewsimp :=
  match goal with
    H: _ |- context [get (set _ ?k1 _) ?k2] =>
      unify k1 k2; rewrite set_a_get_a
  | H: _ |- context [get (set _ ?k1 _) ?k2] =>
      rewrite set_a_get_a'; [idtac | let Hff:=fresh in introv Hff; inverts Hff]
  | _ => idtac
  end.

Ltac kvext_h hyp k mp :=
  match type of hyp with
    context [set _ k ?v] => assert (get mp k = Some v)
  end; 
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_h_name hyp k mp hyp' :=
  match type of hyp with
    context [set _ k ?v] => assert (hyp': get mp k = Some v)
  end; 
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_h0 hyp k mp :=
  match type of hyp with
    context [set _ k ?v] => assert (get mp k = Some v)
  end; 
  [ eapply join_get_get_l; eauto | idtac ].

Ltac kvext mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (get mp k = v)
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_name mp0 k mp hyp' :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (hyp': get mp k = v)
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].  

Ltac kvext0 mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (get mp k = v)
  end; 
  [ eapply join_get_get_l; eauto | idtac ].


Require Import pif_lemmas.

Ltac desvl0 vl :=
  match goal with
    Hhs: context[has_succ], Hsp: context[spec_step] |- _ => 
      destruct vl;
      [ simpl in Hhs; 
        lets Heq: abt_no_succ Hhs; eauto; subst; 
        inverts Hsp | idtac ]
  end. 

Ltac des_vl :=
  match goal with
    vl: vallist |- _ => desvl0 vl
  | vl: list val |- _ => desvl0 vl
  end. 

Ltac dt_preserve_eq := 
  eapply good_dt_preserve00; eauto; 
  eapply join_get_same_l; eauto; 
  repeat rewsimp; eauto.

Ltac dt_presesrve_eq_impl O0 O :=
  eapply good_dt_preserve0; eauto; 
  try (eapply join_get_same_l; eauto; repeat rewsimp; eauto); 
  try (unfolds; intros;  
       kvext O0 absmutinfoid O; 
       eexists; eauto; fail);
  try (unfolds; intros;  
       kvext O0 absptlsid O; 
       eexists; eauto; fail);
  try (eapply ptls_eq_impl; eauto; 
       eapply join_get_same_l; eauto; 
       repeat rewsimp; eauto; fail);
  try (eapply mutinfo_eq_impl; eauto;
       eapply join_get_same_l; eauto; 
       repeat rewsimp; eauto; fail).

Ltac pif_preserve_eq := 
  eapply pif_preserve00; eauto; 
  eapply join_get_same_l; eauto; 
  repeat rewsimp; eauto.

Ltac pif_preserve_eq_impl O0 O :=
  eapply pif_preserve0; eauto; 
  try (eapply join_get_same_l; eauto; repeat rewsimp; eauto); 
  try (unfolds; intros;  
       kvext O0 absmutinfoid O; 
       eexists; eauto; fail);
  try (unfolds; intros;  
       kvext O0 absptlsid O; 
       eexists; eauto; fail);
  try (eapply ptls_eq_impl; eauto; 
       eapply join_get_same_l; eauto; 
       repeat rewsimp; eauto; fail);
  try (eapply mutinfo_eq_impl; eauto;
       eapply join_get_same_l; eauto; 
       repeat rewsimp; eauto; fail).


