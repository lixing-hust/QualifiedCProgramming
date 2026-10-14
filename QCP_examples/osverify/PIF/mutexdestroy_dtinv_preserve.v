
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


Lemma rdy_notin_wl_mux_destroy: 
  forall tls els els' pr onr eid, 
    join els' (sig eid (absmutexsem pr onr, nil)) els -> 
    get els eid = Some (absmutexsem pr onr, nil) -> 
    rdy_notin_wl tls els ->
    rdy_notin_wl tls els'.
Proof.
  introv Hjo Hge Hrnw.
  unfold rdy_notin_wl in *.
  destruct Hrnw as (Hnw & Hwt1 & Hwt2).
  splits.
  - introv Hgt Hwt'. 
    specializes Hnw; eauto.
    apply Hnw.
    eapply st_wait_t_del_hold; eauto.
  - introv Hgt.
    specializes Hwt1; eauto.
    unfold IS_WAITING_E in *.
    destruct Hwt1 as (p_q & on & wl & Hget & Hin).
    match type of Hget with
      context[Some ?t] => 
        assert (Hor: get els' eid0 = Some t \/
                       get (sig eid (absmutexsem pr onr, nil)) eid0 = Some t)
    end.
    { eapply join_get_or; eauto. }
    destruct Hor as [Ha | Hb].
    + do 3 eexists; split; eauto.
    + assert (Hb' := Hb).
      eapply map_get_sig'_l in Hb; eauto. 
      eapply map_get_sig'_r in Hb'; eauto. 
      subst.
      inverts Hb'.
      false.               
  - introv Hiw.
    specializes Hwt2; eauto.
    unfold IS_WAITING_E in *.
    destruct Hiw as (p_q & onr_ & wl & Hge' & Hin').
    do 3 eexists.
    split.
    eapply EcbMod.join_get_l; eauto.
    eauto. 
Qed. 

Lemma owner_prio_prop_mux_destroy:
  forall els els' eid pr onr tls, 
    join els' (sig eid (absmutexsem pr onr, nil)) els -> 
    get els eid = Some (absmutexsem pr onr, nil) ->           
    owner_prio_prop tls els ->
    owner_prio_prop tls els'. 
Proof.
  introv Hjo Hge Hopp.
  unfold owner_prio_prop in *.
  introv Hgt Hge'.
  eapply Hopp; eauto.
  eapply ecb_joinsig_get_eq; eauto.
  unfolds.
  eapply EcbMod.join_comm in Hjo;eauto.
Qed. 
        
Lemma  ecbmod_get_join_get:
  forall eid y m x z t,
    eid <> y ->
    EcbMod.get m eid = Some t ->
    EcbMod.join x (EcbMod.sig y z) m ->
    EcbMod.get x eid = Some t.
Proof.
  intros.

  set (EcbMod.join_get_or H1 H0).
  elim o; intros.
  auto.
  rewrite EcbMod.get_a_sig_a' in H2.
  inversion H2.
  EcbMod.beq_simpl_tac.
Qed.

Lemma wait_prop_mux_destroy:
  forall els els' eid pr onr tls,
    join els' (sig eid (absmutexsem pr onr, nil)) els ->
    get els eid = Some (absmutexsem pr onr, nil) ->
    wait_prop tls els ->
    rdy_notin_wl tls els ->
    wait_prop tls els'.
Proof.
  introv Hjo Hge Hwp Hrnw.
  unfold wait_prop in *.
  introv Hg.
  specializes Hwp; eauto.
  destruct Hwp as (t' & po & m_ & sus_ & Hio & Hgt' & Hor & Himpl).
  casetac eid eid0 Ht Hf.
  - (* eid = eid0 *) 
    subst. 
    eapply Hrnw in Hg; eauto.
    unfolds in Hg.
    destruct Hg as (pq & or & wl_ & Hgg & Hin).
    unfold get, EcbMap in Hge.
    rewrite Hge in Hgg.
    inverts Hgg.
    false.
  - (* eid <> eid0 *)
    do 4 eexists; splits; eauto.
    + unfold IS_OWNER in *.
      simpljoin. 
      do 3 eexists.
      eapply ecbmod_get_join_get; eauto.
    + introv Hgo.
      unfold GET_ORP in *.
      rewrite Hg in Hgo.
      specializes Hgo; eauto.
      destruct Hgo as [Ha | Hb].
      * eapply Himpl; eauto.
        left. 
        unfold IS_OWNER_P in *.
        simpljoin. do 3 eexists.
        eapply EcbMod.join_get_l; eauto.
      * simpljoin.
        inverts H0. 
        auto.
Qed. 

Lemma op_p_prop_mux_destroy:
  forall tls els els' onr pr eid,
    join els' (sig eid (absmutexsem pr onr, nil)) els ->
    get els eid = Some (absmutexsem pr onr, nil) ->
    op_p_prop tls els ->
    op_p_prop tls els'. 
Proof.
  introv Hjo Hge Hopp.
  unfold op_p_prop in *.
  introv Hgt Hgo.
  unfold GET_ORP in *.
  rewrite Hgt in Hgo.
  specializes Hgo; eauto. 
  destruct Hgo as [Hex | (Hnex & Hgtt)].
  - eapply Hopp; eauto.
    introv Hn.
    left. 
    unfold IS_OWNER_P in *.
    simpljoin. 
    do 3 eexists.
    eapply EcbMod.join_get_l; eauto. 
  - right.
    simpljoin. 
    inverts H. 
    int auto. 
Qed. 

Lemma nowner_prio_prop_mux_destroy: 
  forall tls els els' eid onr pr, 
    join els' (sig eid (absmutexsem pr onr, nil)) els ->
    get els eid = Some (absmutexsem pr onr, nil) ->
    nowner_prio_prop tls els ->
    nowner_prio_prop tls els'. 
Proof.
  introv Hjo' Hg' Hnpp.
  unfold nowner_prio_prop in *. 
  introv Hgt Hno Hgo.
  unfolds in Hgo.
  rewrite Hgt in Hgo.
  specializes Hgo; auto.
  destruct Hgo as [Ha | Hb].
  - unfold IS_OWNER_P in *. 
    unfolds in Hno.  
    false. apply Hno.
    unfold IS_OWNER.
    simpljoin. do 4 eexists; eauto.
  - simpljoin.
    inverts H0. auto.
Qed. 

Lemma good_dt_mux_destroy_preserved: 
  forall O0 Of O O' pr onr eid els els' x2 x3 x4 x5 x6 x7 x8 x9 x10 x17, 
    get O0 absecblsid = Some (absecblist els) -> 
    get O0 absmutinfoid = Some (absmutinfo x3) ->
    get O0 absptlsid = Some (absptls x17) -> 
    get els eid = Some (absmutexsem pr onr, nil) -> 
    join O0 Of O ->
    join
      (set
         (set (set O0 absecblsid (absecblist els')) absmutinfoid
            (absmutinfo (set x3 x2 (Null, x4, x5, x6, x7, x8, x9, x10)))) absptlsid
         (absptls (set x17 pr Null))) Of O' ->          
    join els' (sig eid (absmutexsem pr onr, nil)) els -> 
    GOOD_DT O ->
    GOOD_DT O'. 
Proof.
  introv Hge Hgm Hgp Hgee Hjo Hjo' Hje Hgdt. 
  unfold GOOD_DT in *.
  introv Hge' Hgt' Hgm' Hgp'.
  kvext_h_name Hjo' absmutinfoid O' Ham.
  kvext_h_name Hjo' absptlsid O' Hpt.
  kvext_h_name Hjo' absecblsid O' Hel.
  assert (Htc: get O abstcblsid = get O' abstcblsid).
  {
    eapply join_get_same_l; eauto.
    repeat rewsimp; eauto.
  }
  unfold get, AMap in Ham.
  unfold get, AMap in Hpt.
  unfold get, AMap in Hel.
  unfold get, AMap in Htc.
  l_rew12 (OSAbstMod.get O' absecblsid).
  l_rew12 (OSAbstMod.get O' absmutinfoid).
  l_rew12 (OSAbstMod.get O' absptlsid).
  rewrite Hgt' in Htc.

  kvext_name O0 absecblsid O Hels.
  kvext_name O0 absmutinfoid O Hmif.
  kvext_name O0 absptlsid O Hptls.
  unfold get, AMap in Hels.
  unfold get, AMap in Hmif.
  unfold get, AMap in Hptls.
  specializes Hgdt; eauto. 

  simpljoin.
  splits; eauto.
  -            
    eapply rdy_notin_wl_mux_destroy; eauto. 
  -
    eapply owner_prio_prop_mux_destroy; eauto.
  -
    eapply wait_prop_mux_destroy; eauto.
  -
    eapply op_p_prop_mux_destroy; eauto.
  -
    eapply nowner_prio_prop_mux_destroy; eauto.
Qed. 

Lemma mutexdestroy_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mutex_destroy vl) cd ->
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
  { eapply good_dt_mux_destroy_preserved; eauto. }

Qed. 
    

