
Require Import base_tac. 
Require Import memory.

Require Import if_assms.

Require Import if_common_lemmas. 


Ltac apply2 trm1 trm2 lem :=
  let hyp := fresh in 
  match goal with
    H1: context [trm1], H2: context [trm2] |- _ =>
      lets hyp: lem H1 H2; subst 
  end.

Ltac apply2_rev trm1 trm2 lem :=
  let hyp := fresh in 
  match goal with
    H1: context [trm1], H2: context [trm2] |- _ =>
      lets hyp: lem H2 H1; subst 
  end.

Ltac apply2_clr2 trm1 trm2 lem :=
  let hyp := fresh in 
  match goal with
    H1: context [trm1], H2: context [trm2] |- _ =>
      lets hyp: lem H1 H2; subst; clear H2 
  end.

Ltac apply2_rev_clr2 trm1 trm2 lem :=
  let hyp := fresh in 
  match goal with
    H1: context [trm1], H2: context [trm2] |- _ =>
      lets hyp: prio_unique H2 H1; subst; clear H2
  end.

Ltac apply11 trm1 trm2 lem hh1 hh2 :=
  match goal with
    H1: context [ trm1 ], H2: context [ trm2 ] |- _ =>
      lets hh1: lem H1; eauto;
      lets hh2: lem H2; eauto
  end. 



Ltac rewsimp :=
  match goal with
    H: _ |- context [get (set _ ?k1 _) ?k2] =>
      unify k1 k2; rewrite set_a_get_a
  | H: _ |- context [get (set _ ?k1 _) ?k2] =>
      rewrite set_a_get_a'; [idtac | let Hff:=fresh in introv Hff; inverts Hff]
  | _ => idtac
  end.

Ltac rewsimp_in hyp :=
  match goal with
  | hyp: context [ get (set _ ?k1 _) ?k2 ] |- _ => unify k1 k2; rewrite set_a_get_a in hyp
  | H: context [ get (set _ ?k1 _) ?k2 ] |- _ =>
      rewrite set_a_get_a' in hyp;
      [  | let Hff := fresh in introv Hff; inverts Hff ] 
  | _ => idtac
  end. 

Ltac kvext_h_ hyp k constr mp :=
  match type of hyp with
    context [constr ?x] => assert (get mp k = Some (constr x))
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Ltac kvext_h hyp k mp :=
  match type of hyp with
    context [set _ k ?v] => assert (get mp k = Some v)
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

Ltac kvext0 mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (get mp k = v)
  end; 
  [ eapply join_get_get_l; eauto | idtac ].



Ltac inv_some :=
  match goal with H: Some _ = Some _ |- _ => inverts H end.

Ltac inv_lst :=
  match goal with
    H: _ :: _ = _ :: _ |- _ => inverts H
  end.

Ltac rem_dis :=
  match goal with
    H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse
  end.
