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
      (* | Some _ = Some _ => inverts hyp *)
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


Lemma rdy_notin_wl_new_mux: 
  forall tls ecbs eid pr, 
    rdy_notin_wl tls ecbs ->
    get ecbs eid = None -> 
    rdy_notin_wl tls (set ecbs eid (absmutexsem pr None, nil)). 
Proof.
  introv Hrn Hget.
  unfold rdy_notin_wl in *.
  destruct Hrn as (Hnwt & Hwt1 & Hwt2).
  splits.
  - introv Hg Hwt.
    specializes Hnwt; eauto.
    unfold ST_WAIT_T in Hwt, Hnwt.
    destruct Hwt as (qid & p_q & on & wl & Hgq & Hin).
    casetac eid qid Ht Hf.
    + subst. unfold set, EcbMap in Hgq.
      rewrite EcbMod.map_get_set in Hgq. inverts Hgq.
      inverts Hin.
    + unfold set, EcbMap in Hgq.
      rewrite EcbMod.map_get_set' in Hgq; eauto.
      eapply Hnwt. do 4 eexists; split; eauto.
  - introv Hg.
    specializes Hwt1; eauto.
    unfold IS_WAITING_E in *.
    destruct Hwt1 as (p_q & owner & wl & Hge & Hin).
    unfold set, EcbMap.
    casetac eid eid0 Ht Hf.
    + subst. unfold get, EcbMap in Hget.
      rewrite Hget in Hge; inverts Hge.
    + rewrite EcbMod.map_get_set'; eauto. 
  - introv Hwt.
    unfold IS_WAITING_E in Hwt2, Hwt.
    casetac eid eid0 Ht Hf.
    + subst. 
      rewrite EcbMod.set_a_get_a in Hwt.
      destruct Hwt as (p_q & owner & wl & Heq & Hin).
      inverts Heq.
      inverts Hin.
      apply TcbMod.beq_refl.
    + rewrite EcbMod.set_a_get_a' in Hwt; eauto.
      eapply tidspec.neq_beq_false; eauto. 
Qed. 

Lemma nowner_pp_new_mux: 
  forall tls ecbs pr eid, 
    owner_prio_prop tls ecbs ->
    get ecbs eid = None -> 
    owner_prio_prop tls (set ecbs eid (absmutexsem pr None, nil)). 
Proof.
  introv Hopp Hgn.
  unfold owner_prio_prop in *.
  introv Hgt Hge.
  casetac eid eid0 Ht Hf.
  - subst.
    unfold set, EcbMap in Hge.
    rewrite EcbMod.set_a_get_a in Hge. inverts Hge.
    apply TcbMod.beq_refl. 
  - unfold set, EcbMap in Hge.
    rewrite EcbMod.set_a_get_a' in Hge; eauto.
    eapply tidspec.neq_beq_false; eauto. 
Qed.

Lemma wait_prop_new_mux: 
  forall tls ecbs eid pr, 
    wait_prop tls ecbs ->
    get ecbs eid = None -> 
    wait_prop tls (set ecbs eid (absmutexsem pr None, nil)). 
Proof.
  introv Hwp Hge.
  unfold wait_prop in *.
  introv Hgt.
  specializes Hwp; eauto.
  destruct Hwp as (t' & po & m_ & sus_ & Hio & Hgt_ & Hor & Hip).
  unfold IS_OWNER in *.
  destruct Hio as (p_q & p_w & wl & Hg).
  unfold set, EcbMap. 
  casetac eid eid0 Ht Hf.
  - subst. unfold get, EcbMap in Hge.
    rewrite Hge in Hg. false.
  - rewrite EcbMod.set_a_get_a'; eauto. 
    2: { eapply tidspec.neq_beq_false; eauto. }
    do 4 eexists; splits; eauto.
    unfold GET_ORP in *.
    unfold IS_OWNER_P in *.
    unfold IS_OWNER in *.
    introv H_. 
    specializes Hip; eauto.  
    introv Hnn.
    specializes H_; eauto.
    destruct H_ as [Ha | Hb].
    + destruct Ha as (qid & p_q_ & wl_ & Hg_).
      casetac eid qid Ht_ Hf_.
      * subst.
        rewrite EcbMod.set_a_get_a in Hg_. inverts Hg_.
        apply TcbMod.beq_refl.
      * rewrite EcbMod.set_a_get_a' in Hg_; eauto. 
        apply tidspec.neq_beq_false; eauto. 
    + right.
      simpljoin.
      split; eauto.  
      introv Hcontra.
      apply H.
      destruct Hcontra as (qid & p_q_ & p_o & wl_ & Hget).
      casetac eid qid Htt Hff.
      * subst. unfold get, EcbMap in Hge.
        rewrite Hge in Hget. false.
      * exists qid.
        rewrite EcbMod.set_a_get_a'; eauto.
        apply tidspec.neq_beq_false; eauto. 
Qed. 

Lemma op_p_prop_new_mux:
  forall tls ecbs eid pr, 
    op_p_prop tls ecbs ->
    get ecbs eid = None -> 
    op_p_prop tls (set ecbs eid (absmutexsem pr None, nil)).
Proof.
  introv Hopp Hge.
  unfold op_p_prop in *.
  introv Hgt Hgo.
  unfold GET_ORP in *.
  unfold IS_OWNER_P, IS_OWNER in *.
  specializes Hopp; eauto.
  introv Hnn.
  specializes Hgo; eauto.
  destruct Hgo as [Ha | Hb].
  - destruct Ha as (qid & p_q & wl & Hg).
    casetac eid qid Ht Hf.
    + subst.
      rewrite EcbMod.set_a_get_a in Hg.
      inverts Hg.
      apply TcbMod.beq_refl.
    + rewrite EcbMod.set_a_get_a' in Hg; eauto.
      apply tidspec.neq_beq_false; eauto. 
  - right.
    simpljoin.
    split; eauto.
    introv Hcontra.
    apply H.
    destruct Hcontra as (qid & p_q & p_o & wl & Hg).
    casetac eid qid Htt Hff.
    + subst. unfold get, EcbMap in Hge. rewrite Hge in Hg.
      false.
    + exists qid. rewrite EcbMod.set_a_get_a'; eauto.
      apply tidspec.neq_beq_false; eauto. 
Qed. 

Lemma nowner_prio_prop_new_mux: 
  forall tls ecbs eid pr, 
    nowner_prio_prop tls ecbs ->
    get ecbs eid = None -> 
    nowner_prio_prop tls (set ecbs eid (absmutexsem pr None, nil)). 
Proof.
  introv Hnpp Hge.
  unfold nowner_prio_prop in *.
  unfold IS_NOT_OWNER in *.
  unfold IS_OWNER, GET_ORP in *.
  unfold IS_OWNER, IS_OWNER_P in *.
  introv Hgt Hne Hor.
  specializes Hnpp; eauto.
  - introv Hcontra.
    apply Hne.
    destruct Hcontra as (eid_ & p_q & p_o & wl & Hge_).
    casetac eid eid_ Ht Hf.
    + subst.
      unfold get, EcbMap in Hge.
      rewrite Hge in Hge_.
      false.
    + exists eid_. 
      rewrite EcbMod.set_a_get_a'; eauto.
      apply tidspec.neq_beq_false; eauto.
  - introv Hn.
    specializes Hor; eauto.
    destruct Hor as [Ha | Hb].
    + destruct Ha as (qid_ & p_q & wl & H').
      left.
      casetac eid qid_ Ht Hf.
      * subst. rewrite EcbMod.set_a_get_a in H'.
        inverts H'.
        apply TcbMod.beq_refl.
      * rewrite EcbMod.set_a_get_a' in H'; eauto.
        apply tidspec.neq_beq_false; eauto.
    + right.
      simpljoin. 
      split; eauto.
      introv Hcontra.
      destruct Hcontra as (qid & p_q & p_o & wl & Hg_).
      apply H.
      casetac eid qid Htt Hff.
      * subst.
        unfold get, EcbMap in Hge.
        rewrite Hge in Hg_.
        false.
      * exists qid. rewrite EcbMod.set_a_get_a'; eauto.
        apply tidspec.neq_beq_false; eauto.
Qed. 

Lemma good_dt_upd_muxnone_preserved:
  forall O0 Of O O' ecbs eid pr x3 x2, 
    get O0 absecblsid = Some (absecblist ecbs) ->
    get ecbs eid = None -> 
    join O0 Of O ->
    join
      (set (set O0 absecblsid (absecblist (set ecbs eid (absmutexsem pr None, nil))))
         evlocid (evloc (set x3 x2 (V$ __EvLoc_ecbcre2)))) Of O' ->
    GOOD_DT O ->
    GOOD_DT O'. 
Proof.
  introv Hges Hnone Hjo Hjo' Hgdt.
  unfold GOOD_DT in *.
  introv Hge Hgt Hgm Hgp.
  assert (Hgteq: OSAbstMod.get O abtcblsid = OSAbstMod.get O' abstcblsid).
  {
    eapply join_get_same_l; eauto.
    repeat rewsimp; auto. 
  }
  assert (Hgmeq: OSAbstMod.get O absmutinfoid = OSAbstMod.get O' absmutinfoid).
  {
    eapply join_get_same_l; eauto.
    repeat rewsimp; eauto. 
  }
  assert (Hgpeq: OSAbstMod.get O absptlsid = OSAbstMod.get O' absptlsid).
  {
    eapply join_get_same_l; eauto.
    repeat rewsimp; eauto. 
  }
  kvext O0 absecblsid O.
  specializes Hgdt; eauto. 
  rewrite Hgteq; eauto.
  rewrite Hgmeq; eauto.
  rewrite Hgpeq; eauto.
  kvext_h_name Hjo' absecblsid O' Hge'.
  unfold get, AMap in Hge'.
  rewrite Hge in Hge'; inverts Hge'.
  simpljoin.
  splits; eauto.
  - eapply rdy_notin_wl_new_mux; eauto.
  - eapply nowner_pp_new_mux; eauto. 
  - eapply wait_prop_new_mux; eauto. 
  - eapply op_p_prop_new_mux; eauto.
  - eapply nowner_prio_prop_new_mux; eauto. 
Qed.


Lemma mutexinit_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mutex_init vl) cd ->
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
  inverts Hsp; (auto; fail).

  repeat symexe. 
  { dt_preserve_eq. } 
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. } 
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. } 
  { dt_preserve_eq. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_upd_muxnone_preserved; eauto. } 
  { dt_preserve_eq. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_preserve_eq. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. }
  { dt_preserve_eq. } 
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_upd_muxnone_preserved; eauto. }
  { dt_preserve_eq. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. } 
  { dt_presesrve_eq_impl O0 O. } 
  { dt_presesrve_eq_impl O0 O. } 
  { dt_presesrve_eq_impl O0 O. } 
  { dt_preserve_eq. } 

Qed.   

  

    
