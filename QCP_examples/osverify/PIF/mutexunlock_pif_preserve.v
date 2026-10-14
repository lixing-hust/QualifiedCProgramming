
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

Require Import protect. 
Require Import join_lib.

Require Import mutexunlock_dtinv_preserve.
Require Import int_auto. 

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
  | H: PIF ?O |- PIF ?O => solve[auto]
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

Lemma pif_post_nowt_noret_succ:
  forall
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x2 : PtbMod.map)
    (x4 : EcbMod.map)
    (x5 : TcbMod.map)
    (x7 x8 x9 : int32)
    (x10 : taskstatus)
    (x11 : msg)
    (x12 : susstatus)
    (x13 : addrval)
    (H7 : join
            (set
               (set O0 absecblsid
                  (absecblist (set x4 x (absmutexsem x7 None, nil)))) absptlsid
               (absptls (set x2 x7 Holder))) Of O')
    (H6 : join O0 Of O)
    (H0 : get O0 curtid = Some (oscurt x13))
    (H1 : get O0 absecblsid = Some (absecblist x4))
    (H2 : get O0 abtcblsid = Some (abstcblist x5))
    (H3 : get O0 absptlsid = Some (absptls x2))
    (H8 : get x4 x = Some (absmutexsem x7 (Some (x13, x8)), nil))
    (H9 : get x5 x13 = Some (x9, x10, x11, x12))
    (H10 : Int.eq x9 x7 = false)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT O'), 
    PIF O'. 
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x13)) as Hct by (eapply join_get_l;eauto).
  assert (get O absecblsid = Some (absecblist x4)) as Hels by (eapply join_get_l;eauto).
  assert (get O abtcblsid = Some (abstcblist x5)) as Htls by (eapply join_get_l;eauto).
  assert (get O absptlsid = Some (absptls x2)) as Hpls by (eapply join_get_l;eauto).
  assert (O' =(set (set O absecblsid(absecblist(set x4 x (absmutexsem x7 None, nil))))
                 absptlsid (absptls (set x2 x7 Holder)))).
  eapply join_get_set_eq_2;eauto.
  subst O'.
  remember O as Ox. clear HeqOx.
  unfold get in *;simpl in *.
  unfold PIF in *; intros.
  rewrite abst_set_get_neq in H, H4, H5, H11;auto.
  rewrite abst_set_get_neq in H4, H5, H11;auto.
  rewrite OSAbstMod.map_get_set in H; inverts H.
  rewrite OSAbstMod.map_get_set in H12; inverts H12.
  rewrite H5 in Hct;inverts Hct.

  unfolds in H14. mytac.
  unfolds in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.

  assert (He: Some (absecblist (EcbMod.set x4 x (absmutexsem x7 None, nil))) =
                Some (absecblist (EcbMod.set x4 x (absmutexsem x7 None, nil))))by auto.
  assert(He1:Some (absptls (set x2 x7 Holder)) = Some (absptls (set x2 x7 Holder))) by auto.
  lets Hgoodstx:Hgooddt' He Htls H11 He1.
  clear Hgooddt' He He1.
  destruct Hgoodstx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get x5 t = Some (p, st, m, sus)).
  remember (TcbMod.get x5 t) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto. mytac.
  lets Htaskstp':Htkp H14.
  rewrite Htls in H4; inverts H4.

  rewrite H9 in H; inverts H.
  assert (Hee:x0 = x8).
  clear -Hgooddt H10 H9 H8 Htls Hels H11 Hpls.
  unfolds in Hgooddt.
  lets Hx:Hgooddt Hels Htls H11 Hpls. mytac.
  unfolds in H0.
  lets Hx: H0 H9 H8.
  destruct Hx.
  destruct H5;auto.
  subst x0. false.
  clear -H10. int auto. 
  subst x8.
  lets Hpct:post_nolift_get_op_ct Hnonesto Hels Htls H8 H13;auto. eauto.
  subst x0.

  destruct Htaskstp'. subst x14.
  lets Hx:H12 H16 H14.
  unfolds in Hopp.
  lets Hy:Hopp H14 H18.
  clear -Hx Hy.
  destruct Hy;int auto.
  mytac;subst.
  unfolds in Hwtp.
  lets Hx:Hwtp H14. mytac.

  lets Hx:post_no_lift_ct_nowner Hnonesto Hels Htls H8 H;auto.
  eauto.
  lets Hz: H12 Hx H4.
  lets Hy:H21 H18.
  clear -H20 Hz Hy.
  subst x6. int auto. 
  
Qed.

Lemma pif_post_exwt_ret_succ:
  forall
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x7 : PtbMod.map)
    (x9 x10 x11 : int32)
    (x12 : taskstatus)
    (x13 : msg)
    (x14 : list tid)
    (x15 : tid)
    (x16 : taskstatus)
    (x17 : msg)
    (x18 : addrval)
    (x19 x20 : susstatus)
    (H7 : join
            (set
               (set
                  (set O0 abtcblsid
                     (abstcblist
                        (set (set x3 x18 (x11, x12, x13, x19)) x15
                           (x10, rdy, Vnull, x20)))) absecblsid
                  (absecblist
                     (set x2 x
                        (absmutexsem x9 (Some (x15, x10)), remove_tid x15 x14))))
               absptlsid (absptls (set (set x7 x11 (Valid_Addr x18)) x9 Holder)))
            Of O')
    (H6 : join O0 Of O)
    (H0 : get O0 curtid = Some (oscurt x18))
    (H1 : get O0 absecblsid = Some (absecblist x2))
    (H2 : get O0 abtcblsid = Some (abstcblist x3))
    (H3 : get O0 absptlsid = Some (absptls x7))
    (H4 : get x2 x = Some (absmutexsem x9 (Some (x18, x11)), x14))
    (H5 : x14 <> nil)
    (H8 : GetHWait x3 x14 x15)
    (H9 : get x3 x18 = Some (x9, x12, x13, x19))
    (H10 : get x3 x15 = Some (x10, x16, x17, x20))
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT O'),
    PIF O'.
Proof.
  intros.
  assert (get O curtid = Some (oscurt x18)) as Hct by (eapply join_get_l;eauto).
  assert (get O absecblsid = Some (absecblist x2)) as Hels by (eapply join_get_l;eauto).
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls by (eapply join_get_l;eauto).
  assert (get O absptlsid = Some (absptls x7)) as Hpls by (eapply join_get_l;eauto).
  assert (O' =(set (set (set O abtcblsid
                           (abstcblist(set (set x3 x18 (x11, x12, x13, x19)) x15
                                         (x10, rdy, Vnull, x20)))) absecblsid(absecblist(set x2 x
                                                                                           (absmutexsem x9 (Some (x15, x10)), remove_tid x15 x14)))) absptlsid
                 (absptls(set (set x7 x11 (Valid_Addr x18)) x9 Holder)))).
  eapply join_get_set_eq_3;eauto.
  subst O'.
  remember O as Ox. clear HeqOx.
  unfold get in *;simpl in *.
  lets Hneq: post_ex_wait_ct_neq Hnonesto Hels Htls H4 H8.
  unfold PIF in *; intros.
  rewrite abst_set_get_neq in H, H11, H12, H13;auto.
  rewrite OSAbstMod.map_get_set in H14; inverts H14.
  rewrite abst_set_get_neq in H11, H12, H13;auto.
  rewrite OSAbstMod.map_get_set in H; inverts H.
  rewrite OSAbstMod.map_get_set in H11; inverts H11.
  rewrite abst_set_get_neq in H12, H13;auto.
  rewrite H12 in Hct;inverts Hct.

  unfolds in H16. mytac.
  unfolds in Hgooddt'.
  rewrite TcbMod.set_a_get_a' in H.
  rewrite TcbMod.set_a_get_a in H. inverts H.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.

  assert (He: Some (absecblist (set x2 x
                                  (absmutexsem x9 (Some (x15, x10)), remove_tid x15 x14))) =
                Some (absecblist (set x2 x (absmutexsem x9 (Some (x15, x10)),
                                      remove_tid x15 x14))))by auto.
  assert (He1: Some (abstcblist (set (set x3 x18 (x0, rdy, x1, x4)) x15
                                   (x10, rdy, Vnull, x20))) =
                 Some (abstcblist (set (set x3 x18 (x0, rdy, x1, x4)) x15
                                     (x10, rdy, Vnull, x20))))by auto.
  assert(He2:Some (absptls (set (set x7 x0 (Valid_Addr x18)) x9
                              Holder)) = Some (absptls (set (set x7 x0 (Valid_Addr x18)) x9 Holder))) by auto.
  lets Hgoodstx:Hgooddt' He He1 H13 He2.
  clear Hgooddt' He He1 He2.
  destruct Hgoodstx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get (set (set x3 x18 (x0, rdy, x1, x4)) x15
                                           (x10, rdy, Vnull, x20)) t = Some (p, st, m, sus)).
  remember (TcbMod.get
              (set (set x3 x18 (x0, rdy, x1, x4)) x15
                 (x10, rdy, Vnull, x20)) t) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto. mytac.
  destruct H19; auto. mytac.
  assert(Hr: t = x15 \/ t <> x15) by tauto.
  destruct Hr as [He | Hn].
  subst x15.
  2:{
    assert (Hg: TcbMod.get x3 t = Some (x5, x6, x8, x11)).
    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
    lets Htaskstp':Htkp H.

    lets Hpct:post_lift_exwt_get_op_ct Hneq Hnonesto Hels Htls H4; auto.
    assert (Hrdy':TcbMod.get x3 x18 = Some (x9, rdy, x1, x4)) by auto.
    eapply Hpct in H9; eauto.
    subst x0.
    destruct Htaskstp'.
    subst x6.
    lets Hx:H11 H18 H.
    unfolds in Hopp.
    lets Hy:Hopp H H20.
    clear -Hx Hy.
    destruct Hy;int auto.
    mytac;subst.
    unfolds in Hwtp.
    lets Hx:Hwtp H. mytac.

    lets Hx:post_lift_exwt_ct_nowner Hnonesto Hels Htls H9 Hneq;auto.
    eauto. eauto.
    lets Hz: H11 Hx H14.
    lets Hy:H22 H20.
    clear -H16 Hz Hy.
    subst x5. int auto.
  }

  lets Hpct:post_lift_exwt_get_op_ct Hneq Hnonesto Hels Htls H4; auto.
  assert (Hrdy':TcbMod.get x3 x18 = Some (x9, rdy, x1, x4)) by auto.
  eapply Hpct in H9; eauto.
  subst x0.
  assert (Hx5: x6 = rdy).
  rewrite TcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H. auto.
  subst x6.
  lets Hx:H11 H18 H.
  unfolds in Hopp.
  lets Hy:Hopp H H20.
  clear -Hx Hy.
  destruct Hy;int auto.
  mytac;subst.
  apply tidspec.eq_beq_true;auto.
  apply tidspec.neq_beq_false;auto.
Qed.

Lemma pif_post_exwt_noret_succ:
  forall 
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x6 : addrval)
    (x7 : PtbMod.map)
    (x9 x10 x11 x12 : int32)
    (x13 : taskstatus)
    (x14 : msg)
    (x15 : list tid)
    (x16 : tid)
    (x17 : taskstatus)
    (x18 : msg)
    (x19 x20 : susstatus)
    (H7 : join
            (set
               (set
                  (set O0 abtcblsid
                     (abstcblist (set x3 x16 (x10, rdy, Vnull, x20)))) absecblsid
                  (absecblist
                     (set x2 x
                        (absmutexsem x9 (Some (x16, x10)), remove_tid x16 x15))))
               absptlsid (absptls (set x7 x9 Holder))) Of O')
    (H0 : get O0 curtid = Some (oscurt x6))
    (H1 : get O0 absecblsid = Some (absecblist x2))
    (H2 : get O0 abtcblsid = Some (abstcblist x3))
    (H3 : get O0 absptlsid = Some (absptls x7))
    (H4 : get x2 x = Some (absmutexsem x9 (Some (x6, x12)), x15))
    (H5 : x15 <> nil)
    (H8 : GetHWait x3 x15 x16)
    (H9 : Int.eq x11 x9 = false)
    (H10 : get x3 x6 = Some (x11, x13, x14, x19))
    (H11 : get x3 x16 = Some (x10, x17, x18, x20))
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT O'),
    PIF O'. 
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x6)) as Hct by (eapply join_get_l;eauto).
  assert (get O absecblsid = Some (absecblist x2)) as Hels by (eapply join_get_l;eauto).
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls by (eapply join_get_l;eauto).
  assert (get O absptlsid = Some (absptls x7)) as Hpls by (eapply join_get_l;eauto).
  assert (O' =(set (set (set O abtcblsid (abstcblist (set x3 x16 (x10, rdy, Vnull, x20))))
                      absecblsid (absecblist (set x2 x (absmutexsem x9 (Some (x16, x10)),
                                                  remove_tid x16 x15)))) absptlsid (absptls (set x7 x9 Holder)))).
  eapply join_get_set_eq_3;eauto.
  subst O'.
  remember O as Ox. clear HeqOx.
  unfold get in *;simpl in *.
  lets Hneq: post_ex_wait_ct_neq Hnonesto Hels Htls H4 H8.
  unfold PIF in *; intros.
  rewrite abst_set_get_neq in H, H12, H13, H14; auto.
  rewrite OSAbstMod.map_get_set in H15; inverts H15.
  rewrite abst_set_get_neq in H12, H13, H14;auto.
  rewrite OSAbstMod.map_get_set in H; inverts H.
  rewrite OSAbstMod.map_get_set in H12; inverts H12.
  rewrite abst_set_get_neq in H13, H14;auto.
  rewrite H13 in Hct;inverts Hct.

  unfolds in H17. mytac.
  unfolds in Hgooddt'.
  (*   rewrite TcbMod.set_a_get_a' in H.
  rewrite TcbMod.set_a_get_a in H. inverts H. *)
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.

  assert (He: Some (absecblist (set x2 x (absmutexsem x9 (Some (x16, x10)),
                                    remove_tid x16 x15))) =
                Some (absecblist (set x2 x (absmutexsem x9 (Some (x16, x10)),
                                      remove_tid x16 x15))))by auto.
  assert (He1: Some (abstcblist (set x3 x16 (x10, rdy, Vnull, x20))) =
                 Some (abstcblist (set x3 x16 (x10, rdy, Vnull, x20))))by auto.
  assert(He2:Some (absptls (set x7 x9 Holder)) = Some (absptls (set x7 x9 Holder))) by auto.
  lets Hgoodstx:Hgooddt' He He1 H14 He2.
  clear Hgooddt' He He1 He2.
  destruct Hgoodstx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get (set x3 x16 (x10, rdy, Vnull, x20)) t =
                               Some (p, st, m, sus)).
  remember (TcbMod.get (set x3 x16 (x10, rdy, Vnull, x20)) t) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto. mytac.
  assert (Hr: t = x16 \/ t <> x16) by tauto.
  destruct Hr.
  2:{
    lets Htaskstp':Htkp H15.
    rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
    unfold get in *;unfold set in *;simpl in *.
    rewrite H in H10;inverts H10.

    assert (He: x11 = x12).
    clear -Hgooddt H9 H H4 Htls Hels Hpls H14.
    unfolds in Hgooddt.
    lets Hx:Hgooddt Hels Htls H14 Hpls. mytac.
    unfolds in H1.
    lets Hx: H1 H H4.
    destruct Hx.
    destruct H7;auto.
    subst x9. rewrite Int.eq_true in H9; tryfalse.
    subst x12.

    lets Hpct:post_nolift_exwt_get_op_ct Hnonesto Hels Htls H4 H16;auto.
    eauto. subst x11.
    
    destruct Htaskstp'.
    subst x8.
    lets Hx:H12 H19 H15.
    unfolds in Hopp.
    lets Hy:Hopp H15 H21.
    clear -Hx Hy.
    destruct Hy;int auto.
    mytac;subst.
    unfolds in Hwtp.
    lets Hx:Hwtp H15. mytac.
    
    lets Hx:post_nolift_exwt_ct_nowner Hnonesto Hels Htls H10 Hneq;auto.
    eauto.
    eauto.
    lets Hz: H12 Hx H23.
    lets Hy:H25 H21.
    clear -H24 Hz Hy.
    subst x5. int auto.
  }

  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
  inverts H.
  lets Hpct:post_nolift_exwt_get_op_ct Hnonesto Hels Htls H4 H16;auto.
  eauto.
  subst x0.
  assert (Hx: x8 = rdy).
  rewrite TcbMod.set_a_get_a in H15;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H15. auto.
  subst x8.
  lets Hx':H12 H19 H15.
  unfolds in Hopp.
  lets Hy:Hopp H15 H21.
  clear -Hx' Hy.
  destruct Hy;int auto. 
Qed.

Lemma pif_post_nowt_ret_succ:
  forall
    (O O' : OSAbstMod.map)
    (O0 Of : osabst)
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x6 x7 : int32)
    (x8 : taskstatus)
    (x9 : msg)
    (x10 : addrval)
    (x11 : PtbMod.map)
    (x13 : susstatus)
    (H7 : join
            (set
               (set (set O0 abtcblsid (abstcblist (set x3 x10 (x7, x8, x9, x13))))
                  absecblsid (absecblist (set x2 x (absmutexsem x6 None, nil))))
               absptlsid (absptls (set (set x11 x7 (Valid_Addr x10)) x6 Holder)))
            Of O')
    (H0 : get O0 curtid = Some (oscurt x10))
    (H1 : get O0 absecblsid = Some (absecblist x2))
    (H2 : get O0 abtcblsid = Some (abstcblist x3))
    (H3 : get O0 absptlsid = Some (absptls x11))
    (H8 : get x2 x = Some (absmutexsem x6 (Some (x10, x7)), nil))
    (H9 : get x3 x10 = Some (x6, x8, x9, x13))
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (Hgooddt' : GOOD_DT O'), 
    PIF O'. 
Proof.
  intros. 
  assert (get O curtid = Some (oscurt x10)) as Hct by (eapply join_get_l;eauto).
  assert (get O absecblsid = Some (absecblist x2)) as Hels by (eapply join_get_l;eauto).
  assert (get O abtcblsid = Some (abstcblist x3)) as Htls by (eapply join_get_l;eauto).
  assert (O' =(set
                 (set (set O abtcblsid (abstcblist (set x3 x10 (x7, x8, x9, x13))))
                    absecblsid (absecblist (set x2 x (absmutexsem x6 None, nil))))
                 absptlsid (absptls(set (set x11 x7 (Valid_Addr x10)) x6 Holder)))).
  eapply join_get_set_eq_3;eauto.
  subst O'.
  remember O as Ox. clear HeqOx.
  unfold get in *;simpl in *.
  unfold PIF in *; intros.
  rewrite abst_set_get_neq in H, H4, H5, H10;auto.
  rewrite OSAbstMod.map_get_set in H11; inverts H11.
  rewrite abst_set_get_neq in H4, H5, H10;auto.
  rewrite OSAbstMod.map_get_set in H; inverts H.
  rewrite abst_set_get_neq in H5, H10;auto.
  rewrite OSAbstMod.map_get_set in H4;inverts H4.
  rewrite H5 in Hct;inverts Hct.

  assert (HighestRdy (TcbMod.set x3 x10 (x7, x8, x9, x13)) x10) as Hhighest by auto.
  unfolds in H13. mytac.
  rewrite TcbMod.set_a_get_a in H. inverts H.
  unfolds in Hgooddt'.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite OSAbstMod.map_get_set in Hgooddt'.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.
  rewrite abst_set_get_neq in Hgooddt';auto.

  assert (He: Some (absecblist (EcbMod.set x2 x (absmutexsem x6 None, nil))) =
                Some (absecblist (EcbMod.set x2 x (absmutexsem x6 None, nil))))by auto.
  assert(He1:Some (abstcblist (set x3 x10 (x0, rdy, x1, x4))) = Some (abstcblist (set x3 x10 (x0, rdy, x1, x4)))) by auto.
  assert(He2: Some(absptls(set (set x11 x0 (Valid_Addr x10)) x6
                             Holder)) = Some(absptls(set (set x11 x0 (Valid_Addr x10)) x6
                                                       Holder)) ) by auto.
  lets Hgoodstx:Hgooddt' He He1 H10 He2.

  clear Hgooddt' He He1 He2.
  destruct Hgoodstx as (Hrdy&Howp&Htkp&Hwtp&Hopp&Hnoowp).
  unfolds in Htkp.
  assert (exists p st m sus, TcbMod.get (set x3 x10 (x0, rdy, x1, x4)) t= Some (p,st,m,sus)).
  remember (TcbMod.get (set x3 x10 (x0, rdy, x1, x4)) t) as X;destruct X;tryfalse.
  destruct b. destruct p. destruct p.
  do 3 eexists;eauto.
  destruct H16;auto. mytac.
  assert (TcbMod.get x3 t = Some (x5, x7, x8, x9)).
  rewrite TcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
  lets Htaskstp':Htkp H.

  lets Hpct:post_lift_get_op_ct Hnonesto Hels Htls H9 H12;auto.
  subst p_ct.
  destruct Htaskstp'. subst x7.
  lets Hx:H4 H15 H.
  unfolds in Hopp.
  lets Hy:Hopp H H17.
  clear -Hx Hy.
  destruct Hy;int auto.
  mytac;subst.
  unfolds in Hwtp.
  lets Hx:Hwtp H. mytac.

  lets Hx:post_lift_ct_nowner Hnonesto Hels Htls H8 H13;auto. eauto.
  lets Hz: H4 Hx H19.
  lets Hy:H21 H17.
  clear -H20 Hz Hy.
  subst x5. int auto.
  apply tidspec.eq_beq_true;auto. 
Qed.
  
Lemma mutexunlock_pif_preserve: 
  forall sc vl cd O cd' O', 
    spec_step sc cd O cd' O' -> 
    NO_NEST_PENDING_O O ->
    GOOD_DT O ->
    PIF O -> 
    has_succ (mutexunlock vl) cd ->
    NO_NEST_PENDING_O O' ->
    PIF O'. 
Proof.
  introv Hsp Hnn Hgd Hpif Hhs Hnn'.
  assert (Hgooddt': GOOD_DT O').
  {
    lets H__: mutexunlock_dtinv_preserve Hhs Hnn; eauto.
  }
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto).

  repeat symexe.
  repeat symexe.
  repeat symexe.
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
  eapply pif_post_nowt_ret_succ; eauto. 
  eapply pif_post_nowt_noret_succ; eauto. 
  eapply pif_post_exwt_ret_succ; eauto. 
  eapply pif_post_exwt_noret_succ; eauto. 
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
  eapply pif_post_nowt_ret_succ; eauto. 
  eapply pif_post_nowt_noret_succ; eauto.   
  eapply pif_post_exwt_ret_succ; eauto. 
  eapply pif_post_exwt_noret_succ; eauto.   
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
  pif_preserve_eq_impl O0 O.
Qed.   
