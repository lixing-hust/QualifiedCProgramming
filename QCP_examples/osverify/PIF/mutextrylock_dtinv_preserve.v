
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

Require Import PIF_os_ucos_h.
Require Import aux_lemmas.

Require Import mux_succ_gen. 
Require Import pif_lemmas. 
Require Import pif_tacs. 

Open Scope int_scope.

Require Import seplog_lemmas. 
Require Import int_auto.

Require Import protect. 
Require Import join_lib.

Ltac some_none_tac Hs :=
  match Hs with
    (pnil, ?hyp) => 
      match type of hyp with
        ?P /\ ?Q => let h1 := fresh "h" in let h2 := fresh "h" in destruct hyp as (h1 & h2); some_none_tac pnil
      | ?P \/ ?Q =>
          let h1 := fresh "h" in
          let h2 := fresh "h" in
          destruct hyp as [h1 | h2];
          [some_none_tac (pnil, h1) | some_none_tac (pnil, h2)]
      | Some _ = None => solve [false]
      | exists _, _ => let x := fresh "x" in let h1 := fresh "h" in destruct hyp as (x & h1); some_none_tac (pnil, h1)
      | _ => idtac
      end
  | pnil =>
      match goal with
        h: context [Some ?t1 = None] |- _ => some_none_tac (pnil, h)
      | h: context [Some ?t1 = Some ?t2] |- _ => some_none_tac (pnil, h) 
      | h: _ |- _ => idtac
      end
  end.
  
Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); tac h1; tac h2
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.
       
Ltac symexe0 := 
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; tryfalse; some_none_tac pnil; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | H: Some _ = Some _ |- _ => inverts H; symexe0 
  | H: GOOD_DT ?O |- GOOD_DT ?O => solve[auto]
  | Hjo1: join ?O ?Of ?OO, Hjo2: join ?O ?Of ?OO' |- _ =>
      assert (OO = OO') by join auto; subst; symexe0 
  | H: _ |- _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.


Set Nested Proofs Allowed.

Lemma good_dt_mutexacc_preserved:
  forall 
    (O' O : OSAbstMod.map)
    (O0 Of : OSAbstMod.map)
    (x : addrval)
    (x2 : EcbMod.map)
    (x4 : int32)
    (x5 : waitset)
    (x6 : int32)
    (x9 : addrval)
    (H10 : join (set O0 absecblsid (absecblist (set x2 x (absmutexsem x4 (Some (x9, x6)), x5)))) Of O')
    (H9 : join O0 Of O)
    (H1 : GOOD_DT O)
    (H0 : NO_NEST_PENDING_O O)
    (Hnest : NO_NEST_PENDING_O O')
    (x0 : val)
    (x3 : TcbMod.map)
    (x7 : taskstatus)
    (x8 : msg)
    (sus : susstatus)
    (H2 : get O0 curtid = Some (oscurt x9))
    (H4 : get O0 absecblsid = Some (absecblist x2))
    (H5 : get O0 abtcblsid = Some (abstcblist x3))
    (H6 : get x3 x9 = Some (x6, x7, x8, sus))
    (H7 : Int.ltu x4 x6 = true)
    (H8 : get x2 x = Some (absmutexsem x4 None, x5))
    (He : x0 = Vint32 Int.one), 
    GOOD_DT O'. 
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x9)) as Hct.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x2)) as Hels.
  eapply join_get_get_l;eauto.
  assert (get O abstcblsid = Some (abstcblist x3)) as Htls.
  eapply join_get_get_l;eauto.
  assert (O'= set O  absecblsid
                (absecblist (set x2 x (absmutexsem x4 (Some (x9, x6)), x5)))).
  eapply join_get_set_eq;eauto.
  clear H2 H5 H4.
  remember O as Ox.
  clear HeqOx.
  subst O'.
  
  unfolds. intros.
  unfolds in Hnest.
  lets Hnest':Hnest H H2.
  clear Hnest.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H2, H3, H4;auto.
  unfold get in *;simpl in *.
  rewrite H2 in Htls;inverts Htls.
  unfolds in H1.
  lets Hgooddt: H1 Hels H2 H3 H4.

  (*rdy_notin_wl*)
  assert (rdy_notin_wl x3 (set x2 x (absmutexsem x4 (Some (x9, x6)), x5))) as Hrdynotintwl.
  destruct Hgooddt as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6). unfolds.
  unfolds in Hg1. simpljoin. 
  splits.
  intros.
  apply H in H12.
  intro.
  destruct H12.
  unfold ST_WAIT_T in *.
  mytac.
  assert (Hr: x = x0 \/ x <> x0) by tauto.
  destruct Hr as [He | Hn]; subst.
  rewrite EcbMod.set_a_get_a in H12.
  2: apply tidspec.eq_beq_true;auto.
  inverts H12.
  do 4 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a' in H12;[ | apply tidspec.neq_beq_false;auto].
  do 4 eexists;splits;eauto.
  
  (*---------------*)
  intros.
  apply H5 in H12.
  unfold IS_WAITING_E in *.
  mytac.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr as [He | Hn]; subst.
  rewrite EcbMod.set_a_get_a;[ | apply tidspec.eq_beq_true;auto].
  rewrite H12 in H8; inverts H8.
  do 3 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.

  (*----------------*)
  intros.
  assert (IS_WAITING_E t eid x2).
  unfold IS_WAITING_E in *.
  mytac.
  assert (Hr: x = eid \/ x <> eid) by tauto.
  destruct Hr as [He | Hn]; subst.
  rewrite EcbMod.set_a_get_a in H12; [ | apply tidspec.eq_beq_true;auto].
  inverts H12.
  do 3 eexists;splits;eauto.
  rewrite EcbMod.set_a_get_a' in H12; [ | apply tidspec.neq_beq_false;auto].
  do 3 eexists;splits;eauto.
  eapply H11 in H13; eauto.

  destruct Hgooddt as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6); eauto. 
  splits; eauto.
  (*owner_prio_prop*)
  {
    unfold owner_prio_prop in *.
    intros.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He' | Hn]; subst.
    rewrite EcbMod.set_a_get_a in H5;[ | apply tidspec.eq_beq_true;auto].
    inverts H5.
    rewrite H in H6;inverts H6.
    split;auto.
    rewrite EcbMod.set_a_get_a' in H5; [ | apply tidspec.neq_beq_false;auto].
    eapply Hg2; eauto. 
  }

  (*wait_prop*)
  {
    unfold wait_prop in *.
    intros.
    assert (TcbMod.get x3 t = Some (p, wait (os_stat_mutexsem eid) tm, m, sus0)) as Ht;auto.
    apply Hg4 in H.
    mytac.
    do 4 eexists;splits;eauto.
    unfold IS_OWNER in *.
    assert (Hr: x = eid \/ x <> eid) by tauto.
    destruct Hr as [He | Hn]; subst.
    mytac.
    rewrite H8 in H; inverts H.
    mytac.
    rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto].
    do 3 eexists;eauto.
    assert (Hr: t = x9 \/ t <> x9 ) by tauto.
    destruct Hr as [He | Hn]; subst.
    intros.
    rewrite Ht in H6;inverts H6.
    unfolds in Hnest'.
    eapply no_nest_pending_set_prio_eq;eauto.

    intros.
    eapply H12.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite Ht in H14; tryfalse.
  }

  (*op_p_prop*)
  { 
    unfold op_p_prop in *.
    intros.
    eapply Hg5; eauto.
    assert (Hr: t = x9 \/ t <> x9) by tauto.
    destruct Hr as [He' | Hn]; subst.
    2: {
      eapply set_neq_getop_eq;eauto.
      intro.
      rewrite H11 in H; tryfalse.
    }

    rewrite H6 in H; inverts H.
    lets Hnoowner: no_nest_pending_set_none H6 H8 Hnest'.
    lets Heq: no_nest_pending_set_prio_eq Hnest' H5 H6.
    subst p.
    unfolds. intro.
    right. split;auto.
    do 2 eexists;eauto.
  }

  (*nowner_prio_prop*)
  {
    unfold nowner_prio_prop in *.
    intros.
    assert (Hr: t = x9 \/ t <> x9) by tauto.
    destruct Hr as [He' | Hn]; subst.
    rewrite H6 in H; inverts H.
    eapply no_nest_pending_set_prio_eq;eauto.
    eapply Hg6; eauto.

    intro.
    destruct H5.
    mytac;eexists;eapply is_owner_set_other;eauto.
    eapply set_neq_getop_eq;eauto.
    intro.
    rewrite H in H12; tryfalse.
  }

Qed.
    
Lemma mutextrylock_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mutextrylock vl) cd ->
    NO_NEST_PENDING_O O ->
    GOOD_DT O ->
    spec_step sc cd O cd' O' -> 
    NO_NEST_PENDING_O O' ->
    GOOD_DT O'.
Proof.
  introv Hhs Hnn Hgd Hsp Hnn'.
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto).

  repeat symexe.
  repeat symexe.
  repeat symexe.
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_mutexacc_preserved; eauto. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_mutexacc_preserved; eauto. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
Qed.   
