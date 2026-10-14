

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

Require Import mutexdestroy_dtinv_preserve.

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

Lemma pif_mutexdestroy_succ: 
  forall 
    (O O' : OSAbstMod.map)
    (* (Hgooddt' : GOOD_DT O') *)
    (O0 Of : osabst)
    (x3 : int32)
    (x4 : MibMod.map)
    (x5 : owner)
    (x6 : muxtype)
    (x7 : rec_cnt)
    (x8 : prot)
    (x9 : prioc)
    (x10 : wq)
    (x11 : cnsa)
    (x14 : int32)
    (x16 : EcbMod.map)
    (x18 : PtbMod.map)
    (H7 : join
            (set
               (set (set O0 absecblsid (absecblist x16)) absmutinfoid
                  (absmutinfo (set x4 x3 (Null, x5, x6, x7, x8, x9, x10, x11))))
               absptlsid (absptls (set x18 x14 Null))) Of O')
    (H6 : join O0 Of O)
    (Hnonesto : NO_NEST_PENDING_O O)
    (Hnonesto' : NO_NEST_PENDING_O O')
    (Hgooddt : GOOD_DT O)
    (Hpif : PIF O)
    (x : addrval)
    (H1 : cmpaddr Clt userAddrStart x = true)
    (H2 : cmpaddr Cle x userAddrEnd = true)
    (x0 : PbMod.map)
    (x1 : tid)
    (H3 : get O0 pblsid = Some (pblist x0))
    (H4 : get x0 x1 = Some x3)
    (H5 : x3 = Int.zero \/ Int.ltu Int.zero x3 = true)
    (H9 : Int.ltu x3 ($ 6) = true)
    (x12 : tid)
    (x13 : EcbMod.map)
    (x15 : owner)
    (H8 : get O0 absmutinfoid = Some (absmutinfo x4))
    (H10 : get x4 x3 = Some (Valid_Addr x12, x5, x6, x7, x8, x9, x10, x11))
    (H11 : get O0 absecblsid = Some (absecblist x13))
    (H12 : get x13 x12 = Some (absmutexsem x14 x15, nil))
    (H13 : get O0 absptlsid = Some (absptls x18))
    (H14 : get x18 x14 = Some Holder)
    (H16 : join x16 (sig x12 (absmutexsem x14 x15, nil)) x13), 
    PIF O'.
Proof. 
  intros.
  assert (get O absmutinfoid = Some (absmutinfo x4)) as Hinfo.
  eapply join_get_get_l;eauto.
  assert (get O absecblsid = Some (absecblist x13)) as Hecb.
  eapply join_get_get_l;eauto.
  assert (get O absptlsid = Some (absptls x18)) as Hpls.
  eapply join_get_get_l;eauto.

  assert (O'= set (set (set O absecblsid (absecblist x16))
                     absmutinfoid (absmutinfo (set x4 x3
                                                 (Null, x5, x6, x7, x8, x9, x10, x11))))
                absptlsid (absptls (set x18 x14 Null))).
  eapply join_get_set_eq_3;eauto.
  clear H8 H11 H13.
  remember O as Ox.
  clear HeqOx.
  subst O'.

  unfolds; intros.
  (*   lets Hgood: Hgooddt' H H0 H10 H12. *)
  lets Hnest: Hnonesto' H H0.
  rewrite OSAbstMod.map_get_set in H13.
  inverts H13.
  rewrite abst_set_get_neq in H, H0, H8, H11; auto.
  rewrite OSAbstMod.map_get_set in H11.
  inverts H11.
  rewrite abst_set_get_neq in H, H0, H8; auto.
  rewrite OSAbstMod.map_get_set in H.
  inverts H.
  rewrite abst_set_get_neq in H0, H8; auto.
  unfold get in *;simpl in *.
  lets Hgood: Hgooddt Hecb H0 Hinfo Hpls.

  destruct Hgood as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6).
  unfolds in H21.
  lets Hs: H20.
  eapply H21 in H20; eauto.
  destruct H20 as [His | Hn].
  mytac.
  unfolds in Hnest.
  unfolds in H.
  unfold IS_OWNER in Hnest.
  mytac.
  lets Hss: Hs.
  eapply Hnest with (qid:= x2) in Hs ; eauto.
  mytac.
  eapply H11 in H22; tryfalse.
  destruct Hn as (Hn & Hget).
  destruct Hget as (st & msg & sus & Hget).
  lets Hget': Hget.
  eapply Hg3 in Hget'.
  destruct Hget'; subst.
  unfolds in H17; mytac.
  unfold GET_ORP in H15.
  rewrite H in H15; destruct H15; auto.
  mytac.
  unfolds in H13.
  unfolds in H18.
  false.
  eapply H18.
  exists x19.
  mytac.
  unfolds.
  do 3 eexists; eauto.
  mytac.
  inverts H15.
  lets Hget': Hget.
  eapply Hg1 in Hget; eauto.
  mytac.
  assert(Hr: ((exists p', x15 = Some (ct, p')) /\ x12 = x2) \/
               ~ ((exists p', x15 = Some (ct, p')) /\ x12 = x2) ) by tauto.
  destruct Hr as [He | Hne].
  mytac.
  lets Hg': Hget.
  eapply Hg4 in Hget.
  mytac.
  unfolds in H.
  rewrite H12 in H.
  mytac; inverts H.
  unfolds in H15.
  rewrite H11 in H15; destruct H15; auto.
  unfolds in H18.
  unfold IS_OWNER_P in *.
  unfold IS_OWNER in *.
  mytac.
  false; eapply H18; eauto.
  mytac.
  inverts H15. eauto.

  eapply Classical_Prop.not_and_or in Hne.
  destruct Hne.
  eapply Hpif; eauto.
  unfolds. intros.
  unfolds in H18.
  unfolds in H17; mytac.
  unfolds in H15.
  rewrite H13 in H15; destruct H15; auto.
  mytac.
  unfold IS_OWNER_P in H15.
  mytac.
  false. eapply H18.
  exists x21.
  unfolds; eauto.
  mytac. inverts H20.
  right. splits; eauto.

  intro. eapply H15.
  unfold IS_OWNER in *.
  mytac.
  assert(Hr: x17 = x12 \/ x17 <> x12) by tauto.
  destruct Hr as [He1 | Hne1]; subst.
  rewrite H12 in H20; inverts H20.
  false; eapply H; eauto.
  exists x17 x19 x20 x21.
  eapply joinsig_neq_get; eauto.
  unfold EcbMod.joinsig.
  eapply EcbMod.join_comm; eauto.

  (*IS_NOT_OWNER*)
  unfold IS_NOT_OWNER in *. intro.
  eapply H18.
  unfold IS_OWNER in *.
  mytac.
  assert(Hr: x17 = x12 \/ x17 <> x12) by tauto.
  destruct Hr as [He1 | Hne1]; subst.
  rewrite H11 in H12; inverts H12.
  false; eapply H; eauto.
  exists x17 x19 x20 x21.
  eapply joinsig_neq_get; eauto.
  unfold EcbMod.joinsig.
  eapply EcbMod.join_comm; eauto.

  2: eapply st_wait_t_del_hold; eauto.
  (*GET_ORP*)
  unfolds; intros.
  eapply H21 in H11; eauto.
  destruct H11.
  false. eapply Hn.
  mytac.  
  unfolds in H11.
  mytac.
  eexists.
  unfolds; eauto.
  mytac.
  right; splits; eauto.
  intro. eapply Hn.
  mytac.
  lets Hnest': Hnonesto Hecb H0.
  unfolds in Hnest'.
  specialize (Hnest' t x21).
  assert(Hx: TcbMod.get tls t <> None ).
  { intro. rewrite H13 in H23; inverts H23. }
  lets Hy: Hnest' Hx H20.
  eapply st_wait_t_del_hold in H22; eauto.
  mytac.
  eapply H23 in H22; tryfalse.

  (*x12 <> x2*)
  lets Hg: Hget.
  eapply Hg4 in Hg; eauto.
  mytac.
  assert(Hr: x17 = ct \/ x17 <> ct) by tauto.
  destruct Hr; subst.
  unfolds in H15; rewrite H13 in H15; destruct H15; eauto.
  mytac.
  false; eapply H18.
  unfolds in H15.
  mytac.
  exists x17.
  unfolds; eauto.
  mytac.
  inverts H24; eauto.
  unfolds in H17.
  mytac.
  eapply H25 in H24; eauto.
  unfolds in H15.
  rewrite H17 in H15; destruct H15; auto.
  false; eapply H18.
  mytac. unfolds in H15.
  mytac.
  exists x25.
  unfolds; eauto.
  mytac. inverts H26.
  clear -H20 H24.
  int auto. 
Qed.
  
Lemma mutexdestroy_pif_preserve: 
  forall sc vl cd O cd' O', 
    spec_step sc cd O cd' O' -> 
    NO_NEST_PENDING_O O ->
    GOOD_DT O ->
    PIF O -> 
    has_succ (mutex_destroy vl) cd ->
    NO_NEST_PENDING_O O' ->
    PIF O'. 
Proof.
  introv Hsp Hnn Hgd Hpif Hhs Hnn'.
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto).

  repeat symexe.
  eapply pif_mutexdestroy_succ; eauto. 
Qed. 
