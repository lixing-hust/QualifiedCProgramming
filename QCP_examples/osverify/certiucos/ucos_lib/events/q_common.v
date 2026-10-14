Require Import include_frm.
Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import cancel_abs.
Require Import os_inv.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Require Import evtinv_lemmas.
Require Import join_lib.
Require Export sem_lab.
Require Import Lia.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by tauto;
  destruct h as [Ht | Hf].
Ltac mytac :=
  heat; jeauto2.
  
Lemma qcre_ecblist_star_not_inh :
    forall v'28 v'24  eid  v'27 v'37 v'38 s vl P,
      ECBList_P v'24 Vnull v'28 v'27 v'37 v'38 ->
      s |= Astruct eid OS_EVENT vl  **
        evsllseg v'24 Vnull v'28 v'27  ** P ->
      get v'37 eid = None.
Proof.
  inductions v'28;intros.
  simpl in H; mytac.
  unfold ECBList_P in H.
  fold ECBList_P in H.
  mytac.
  destruct v'27.
  tryfalse.
  destruct a.   destruct p. 
  mytac.
  unfold evsllseg in H0.
  fold evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H6.
  inverts H6.
  sep lower 2%nat in H0. 
  sep lower 3%nat in H0.
  sep lower 1%nat in H0.
  lets Hrs : IHv'28 H5 H0.
  unfold AEventNode in H0.
  unfold AOSEvent in H0.
  unfold node in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  mytac.
  inverts H6.
  sep lift 4%nat in H0.
  lets Hs : astruct_neq_ptr H0.
  intro Hf.
  unfolds in Hf.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf.
  mytac.
  tryfalse.
  tryfalse.
  intro Hf.
  unfolds in Hf.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf as [Hx | Hf].
  mytac.
  tryfalse.
  destruct Hf.
  mytac.
  tryfalse.
  tryfalse.
  unfold TcbJoin in H3.
  eapply map_join_get_none'; jeauto2.
Qed.  


Lemma RH_SEM_EINFO_ECB_P_Q_set' :
  forall qls sid mls n pwl wls embls mls' n' pwl' wls',
    EcbMod.get qls sid = Some (absmsgq mls n pwl, wls) ->
    RH_SEM_EINFO_ECB_P qls embls ->
    RH_SEM_EINFO_ECB_P (set qls sid (absmsgq mls' n' pwl', wls')) embls.
Proof.
  unfold RH_SEM_EINFO_ECB_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  rewrite H2 in H1. 
  do 2 destruct H1.
  unfold get in  H1.
  unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.

  eapply H0 in H1.
(*   2 :{ eauto. } *)
  do 2 destruct H1.
  exists x. exists x0.
  assert (get (set qls sid (absmsgq mls' n' pwl', wls')) eid = get qls eid).
  {
    eapply neq_set_get.
    auto.
  }
  rewrite H3.
  eapply H1.
Qed.

Lemma RH_MUX_AMuxEIBs_ECB_P_Q_set' :
  forall qls sid mls n pwl wls embls mls' n' pwl' wls',
    EcbMod.get qls sid = Some (absmsgq mls n pwl, wls) ->
    RH_ECBlk_EIBlk_Mux_P embls qls  ->
    RH_ECBlk_EIBlk_Mux_P embls (set qls sid (absmsgq mls' n' pwl', wls')) .
Proof.
  unfold RH_ECBlk_EIBlk_Mux_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  rewrite H3 in H1. 
  do 3 destruct H1.
  unfold get in  H1.
  unfold EcbMap in H1.
  rewrite H1 in H.
  tryfalse.
  auto.
  eapply H0 in H1.
(*   2 :{ eauto. } *)
  do 3 destruct H1.
  exists x. exists x0. exists x1.
  assert (get (set qls sid (absmsgq mls' n' pwl', wls')) eid = get qls eid).
  {
    eapply neq_set_get.
    auto.
  }
  rewrite H4.
  eapply H1.
  auto.
Qed.

Lemma RH_Mux_EIB_ECB_Q_P_set':
  forall els mls n pwl wls muxeibs tid eid wl, 
    EcbMod.get els eid = Some (absmsgq mls n pwl, wls) -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs els -> 
    RH_ECBlk_EIBlk_Mux_P muxeibs (EcbMod.set els eid (absmsgq nil n pwl, remove_tid tid wl)). 
Proof.
  unfold RH_ECBlk_EIBlk_Mux_P. 
  intros.
  subst.
  assert (Hcs: eid = eid0 \/ eid <> eid0) by tauto.
  destruct Hcs.
  - eapply H0 in H1; eauto. 
    simpl_map1.
    unfold get, EcbMap in H1.
    rewrite H in H1. tryfalse.
  - rewrite set_a_get_a'; eauto.
Qed.

Lemma RH_EIBlk_ECBlk_Q_P_set' :
forall qls sid  mls n pwl wls qattrb mls' n' pwl' wls',
EcbMod.get qls sid = Some (absmsgq mls n pwl, wls)  ->
RH_EIBlk_ECBlk_Q_P qls qattrb ->
RH_EIBlk_ECBlk_Q_P (set qls sid (absmsgq mls' n' pwl', wls')) qattrb.
Proof.
  unfold RH_EIBlk_ECBlk_Q_P.
  intros.
  assert (Hi: eid = sid \/ eid <> sid) by tauto.
  destruct Hi.
  subst.
  exists mls' n' pwl' wls'.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set qls sid (absmsgq mls' n' pwl', wls')) eid = get qls eid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma ASemEIBs_q_rm_tid_preserve: 
  forall infol scapl embls ecbls vhold tid eid mls n pwl wl s, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= ASemEIBs infol scapl embls ecbls vhold -> 
    s |= ASemEIBs infol scapl embls (EcbMod.set ecbls eid (absmsgq mls n pwl, remove_tid tid wl)) vhold.  
Proof. 
  introv Hget Hsat.
  unfold ASemEIBs in *.
  sep pauto.
  clear Hsat.
  unfold RH_SEM_EINFO_ECB_P in *.
  eapply RH_SEM_EINFO_ECB_P_Q_set'; eauto. 
Qed.

Lemma ASemEIBs_q_set_ecbls_preserve: 
  forall infol scapl embls ecbls vhold  eid mls mls' n pwl wl s P, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= ASemEIBs infol scapl embls ecbls vhold ** P-> 
    s |= ASemEIBs infol scapl embls (EcbMod.set ecbls eid (absmsgq mls' n pwl, wl)) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold ASemEIBs in *.
  sep pauto.
  clear Hsat.
  unfold RH_SEM_EINFO_ECB_P in *.
  eapply RH_SEM_EINFO_ECB_P_Q_set'; eauto. 
Qed.

Lemma ASemEIBs_q_set_ecbls_all_preserve: 
  forall infol scapl embls ecbls vhold  eid mls mls' n n' pwl pwl' wl wl' s P, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= ASemEIBs infol scapl embls ecbls vhold ** P-> 
    s |= ASemEIBs infol scapl embls (EcbMod.set ecbls eid (absmsgq mls' n' pwl', wl')) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold ASemEIBs in *.
  sep pauto.
  clear Hsat.
  unfold RH_SEM_EINFO_ECB_P in *.
  eapply RH_SEM_EINFO_ECB_P_Q_set'; eauto. 
Qed.

Lemma AMuxEIBs_q_set_ecbls_preserve: 
  forall minfol mcapl minfob ecbls vhold  eid mls mls' n pwl wl s P, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMuxEIBs minfol mcapl minfob ecbls vhold ** P -> 
    s |= AMuxEIBs minfol mcapl minfob (EcbMod.set ecbls eid (absmsgq mls' n pwl, wl)) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold AMuxEIBs in *.
  sep pauto.
  clear Hsat.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  eapply RH_MUX_AMuxEIBs_ECB_P_Q_set'; eauto. 
Qed.

Lemma AMuxEIBs_q_set_ecbls_all_preserve: 
  forall minfol mcapl minfob ecbls vhold  eid mls mls' n n' pwl pwl' wl wl' s P, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMuxEIBs minfol mcapl minfob ecbls vhold ** P -> 
    s |= AMuxEIBs minfol mcapl minfob (EcbMod.set ecbls eid (absmsgq mls' n' pwl', wl')) vhold **P.  
Proof. 
  introv Hget Hsat.
  unfold AMuxEIBs in *.
  sep pauto.
  clear Hsat.
  unfold RH_ECBlk_EIBlk_Mux_P in *.
  eapply RH_MUX_AMuxEIBs_ECB_P_Q_set'; eauto. 
Qed.

Lemma AMqEIBs_q_rm_tid_preserve: 
  forall qattrl qcapl qattr ecbls vhold tid eid mls n pwl wl s, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMqEIBs qattrl qcapl qattr ecbls vhold -> 
    s |= AMqEIBs qattrl qcapl qattr (EcbMod.set ecbls eid (absmsgq mls n pwl, remove_tid tid wl)) vhold.  
Proof. 
  introv Hget Hsat.
  unfold AMqEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_EIBlk_ECBlk_Q_P_set'; eauto. 
Qed.

Lemma AMqEIBs_q_set_ecbls_preserve: 
  forall qattrl qcapl qattr ecbls vhold mls' eid mls n pwl wl s P, 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMqEIBs qattrl qcapl qattr ecbls vhold ** P-> 
    s |= AMqEIBs qattrl qcapl qattr (EcbMod.set ecbls eid (absmsgq mls' n pwl,  wl)) vhold ** P.  
Proof. 
  introv Hget Hsat.
  unfold AMqEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_EIBlk_ECBlk_Q_P_set'; eauto. 
Qed.

Lemma AMqEIBs_q_set_ecbls_all_preserve: 
  forall qattrl qcapl qattr ecbls vhold mls' eid mls n n' pwl  pwl' wl wl' s , 
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMqEIBs qattrl qcapl qattr ecbls vhold -> 
    s |= AMqEIBs qattrl qcapl qattr (EcbMod.set ecbls eid (absmsgq mls' n' pwl', wl')) vhold.  
Proof. 
  introv Hget Hsat.
  unfold AMqEIBs in *.
  sep pauto.
  clear Hsat.
  eapply RH_EIBlk_ECBlk_Q_P_set'; eauto. 
Qed.

Lemma ASemEIBs_q_nil_rm_tid_preserve_frm:
  forall infol scapl embls ecbls vhold tid eid mls n pwl wl s P,
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= ASemEIBs infol scapl embls ecbls vhold ** P -> 
    s |= ASemEIBs infol scapl embls (EcbMod.set ecbls eid (absmsgq nil n pwl, remove_tid tid wl)) vhold ** P. 
Proof.
  intros.
  sep cancel P.
  unfold ASemEIBs in *.
  sep pauto.
  eapply RH_SEM_EINFO_ECB_P_Q_set'; eauto. 
Qed.

Lemma AMuxEIBs_q_nil_rm_tid_preserve_frm: 
  forall s minfol mcapl muxeibs els vhold_addr pwl n mls wl eid tid P,  
    get els eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMuxEIBs minfol mcapl muxeibs els vhold_addr ** P -> 
    s |= AMuxEIBs minfol mcapl muxeibs (EcbMod.set els eid (absmsgq nil n pwl, remove_tid tid wl)) vhold_addr ** P.
Proof.
  intros.
  sep cancel P.
  unfold AMuxEIBs in *.
  sep pauto.
  eapply RH_Mux_EIB_ECB_Q_P_set'; eauto. 
Qed.

Lemma AMqEIBs_q_nil_rm_tid_preserve_frm:
  forall ecbls qcapl vhold tid eid mls n pwl wl s qattrl qattr P,
    get ecbls eid = Some (absmsgq mls n pwl, wl) ->
    s |= AMqEIBs qattrl qcapl qattr ecbls vhold ** P -> 
    s |= AMqEIBs qattrl qcapl qattr (EcbMod.set ecbls eid (absmsgq nil n pwl, remove_tid tid wl)) vhold ** P.  
Proof.
  intros.
  sep cancel P.
  unfold AMqEIBs in *.
  sep pauto.
  eapply RH_EIBlk_ECBlk_Q_P_set'; eauto. 
Qed.

Lemma sem_ecb_p_que_mls'_wls'_preserve:
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n pwl wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    SEM_ECB_P locmp ptrmp (set els eid (absmsgq mls' n pwl, wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hsep.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  destruct H00 as [Hecb1 | [Hecb2 | Hdel]].
  -
    simpljoin1.
    left.
    splits; eauto. 
    casetac eid eptr Heq Hne.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2. tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; left.
    splits; eauto.
    unfold is_sem in *.
    simpljoin1.
    casetac eid eptr Heq Hne. 
    subst. 
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H1.
    rewrite Hget in H1.
    inverts H1.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; right.
    splits; eauto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    casetac eid eptr Heq Hne.
    subst.
    rewrite set_a_get_a.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    simpljoin1.
    right; right.
    rewrite Hget in H0. inverts H0.
    do 4 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
Qed.   

Lemma sem_ecb_p_que_all_preserve:
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n n' pwl pwl' wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    SEM_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    SEM_ECB_P locmp ptrmp (set els eid (absmsgq mls' n' pwl', wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hsep.
  unfold SEM_ECB_P in *.
  introv Hgetp.
  lets H00: Hsep Hgetp.
  destruct H00 as [Hecb1 | [Hecb2 | Hdel]].
  -
    simpljoin1.
    left.
    splits; eauto. 
    casetac eid eptr Heq Hne.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2. tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; left.
    splits; eauto.
    unfold is_sem in *.
    simpljoin1.
    casetac eid eptr Heq Hne. 
    subst. 
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H1.
    rewrite Hget in H1.
    inverts H1.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; right.
    splits; eauto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    casetac eid eptr Heq Hne.
    subst.
    rewrite set_a_get_a.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    simpljoin1.
    right; right.
    rewrite Hget in H0. inverts H0.
    do 4 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
Qed. 

Lemma mux_ecb_p_que_mls'_wls'_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n pwl wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    MUX_ECB_P locmp ptrmp (set els eid (absmsgq mls' n pwl, wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hmep.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  destruct H00 as [Hecb1 | [Hecb2 | Hdel]].
  -
    simpljoin1.
    left.
    splits; eauto. 
    casetac eid eptr Heq Hne.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2. tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; left.
    splits; eauto.
    unfold is_mux in *.
    simpljoin1.
    casetac eid eptr Heq Hne. 
    subst. 
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H1.
    rewrite Hget in H1.
    inverts H1.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; right.
    splits; eauto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    casetac eid eptr Heq Hne.
    subst.
    rewrite set_a_get_a.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    simpljoin1.
    right; right.
    rewrite Hget in H0. inverts H0.
    do 4 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
Qed.

Lemma mux_ecb_p_que_all_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n n' pwl pwl' wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    MUX_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    MUX_ECB_P locmp ptrmp (set els eid (absmsgq mls' n' pwl', wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hmep.
  unfold MUX_ECB_P in *.
  introv Hgetp.
  lets H00: Hmep Hgetp.
  destruct H00 as [Hecb1 | [Hecb2 | Hdel]].
  -
    simpljoin1.
    left.
    splits; eauto. 
    casetac eid eptr Heq Hne.
    subst.
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H2.
    rewrite Hget in H2. tryfalse.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; left.
    splits; eauto.
    unfold is_mux in *.
    simpljoin1.
    casetac eid eptr Heq Hne. 
    subst. 
    unfold get, EcbMap in Hget.
    unfold get, EcbMap in H1.
    rewrite Hget in H1.
    inverts H1.
    rewrite set_a_get_a'; eauto.
  -
    simpljoin1.
    right; right.
    splits; eauto.
    destruct H0.
    2: { right. auto. }
    left.
    unfold is_evt in *.
    unfold is_sem, is_mux, is_que in *.
    casetac eid eptr Heq Hne.
    subst.
    rewrite set_a_get_a.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    destruct H0.
    simpljoin1.
    rewrite Hget in H0. inverts H0.
    simpljoin1.
    right; right.
    rewrite Hget in H0. inverts H0.
    do 4 eexists; eauto.
    rewrite set_a_get_a'; eauto. 
Qed.

Lemma q_ecb_p_que_mls'_wls'_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n pwl wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    Q_ECB_P locmp ptrmp (set els eid (absmsgq mls' n pwl, wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hqep.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  destruct H00 as (Hor & Hdel).
  split.
  -(* part1*)
    destruct Hor.
    +
      left.
      simpljoin1.
      splits; eauto. 
      casetac eid eptr Heq Hne.
      subst.
      unfold get, EcbMap in Hget.
      unfold get, EcbMap in H2.
      rewrite Hget in H2. tryfalse.
      rewrite set_a_get_a'; eauto.
    +
      destruct H.
      *
        right;left.
        simpljoin1.
        splits; eauto.
        unfold is_que in *.
        simpljoin1.
        casetac eid eptr Heq Hne. 
        subst. 
        unfold get, EcbMap in Hget.
        unfold get, EcbMap in H1.
        rewrite Hget in H1.
        rewrite set_a_get_a.
        do 4 eexists. eauto.
        rewrite set_a_get_a'; eauto. 
      *
        right;right.
        simpljoin1.
        splits; eauto.
        destruct H0.
        2: { right. auto. }
        left.
        unfold is_evt in *.
        unfold is_sem, is_mux, is_que in *.
        casetac eid eptr Heq Hne.
        subst.
        rewrite set_a_get_a.
        destruct H0.
        simpljoin1.
        rewrite Hget in H0. inverts H0.
        destruct H0.
        simpljoin1.
        rewrite Hget in H0. inverts H0.
        simpljoin1.
        right; right.
        rewrite Hget in H0. inverts H0.
        do 4 eexists; eauto.
        rewrite set_a_get_a'; eauto. 
  -(*part2*)
    introv Hgetl.
    lets H00:  Hdel Hgetl.
    simpljoin1.
    splits;auto.
        unfold is_que in *.
        simpljoin1.
        casetac eid eptr Heq Hne. 
        subst. 
        unfold get, EcbMap in Hget.
        unfold get, EcbMap in H.
        rewrite Hget in H.
        rewrite set_a_get_a.
        do 4 eexists. eauto.
        rewrite set_a_get_a'; eauto. 
Qed.

Lemma q_ecb_p_que_all_preserve: 
  forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n n' pwl pwl' wl wl', 
    get els eid = Some (absmsgq mls n pwl, wl) -> 
    Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs -> 
    Q_ECB_P locmp ptrmp (set els eid (absmsgq mls' n' pwl', wl')) fecbh fecbvl semeibs muxeibs qeibs. 
Proof.
  introv Hget Hqep.
  unfold Q_ECB_P in *.
  introv Hgetp.
  lets H00: Hqep Hgetp.
  destruct H00 as (Hor & Hdel).
  split.
  -(* part1*)
    destruct Hor.
    +
      left.
      simpljoin1.
      splits; eauto. 
      casetac eid eptr Heq Hne.
      subst.
      unfold get, EcbMap in Hget.
      unfold get, EcbMap in H2.
      rewrite Hget in H2. tryfalse.
      rewrite set_a_get_a'; eauto.
    +
      destruct H.
      *
        right;left.
        simpljoin1.
        splits; eauto.
        unfold is_que in *.
        simpljoin1.
        casetac eid eptr Heq Hne. 
        subst. 
        unfold get, EcbMap in Hget.
        unfold get, EcbMap in H1.
        rewrite Hget in H1.
        rewrite set_a_get_a.
        do 4 eexists. eauto.
        rewrite set_a_get_a'; eauto. 
      *
        right;right.
        simpljoin1.
        splits; eauto.
        destruct H0.
        2: { right. auto. }
        left.
        unfold is_evt in *.
        unfold is_sem, is_mux, is_que in *.
        casetac eid eptr Heq Hne.
        subst.
        rewrite set_a_get_a.
        destruct H0.
        simpljoin1.
        rewrite Hget in H0. inverts H0.
        destruct H0.
        simpljoin1.
        rewrite Hget in H0. inverts H0.
        simpljoin1.
        right; right.
        rewrite Hget in H0. inverts H0.
        do 4 eexists; eauto.
        rewrite set_a_get_a'; eauto. 
  -(*part2*)
    introv Hgetl.
    lets H00:  Hdel Hgetl.
    simpljoin1.
    splits;auto.
        unfold is_que in *.
        simpljoin1.
        casetac eid eptr Heq Hne. 
        subst. 
        unfold get, EcbMap in Hget.
        unfold get, EcbMap in H.
        rewrite Hget in H.
        rewrite set_a_get_a.
        do 4 eexists. eauto.
        rewrite set_a_get_a'; eauto. 
Qed.

(* The statement of the lemma might need to be adjusted in performing the verification. *)
(* Lemma mq_ecb_p_que_mls'_wls'_preserve:  *)
(*   forall locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs eid mls mls' n pwl wl wl',  *)
(*     get els eid = Some (absmsgq mls n pwl, wl) ->  *)
(*     Q_ECB_P locmp ptrmp els fecbh fecbvl semeibs muxeibs qeibs ->  *)
(*     Q_ECB_P locmp ptrmp (set els eid (absmsgq mls' n pwl, wl')) fecbh fecbvl semeibs muxeibs qeibs.  *)
(* Proof. *)

Lemma EvtInv_part2_Q_rm_tid_preserve: 
  forall els tcblh tcbvl vhold scapl mcapl qcapl P tid eid mls n pwl wl s,
    get els eid = Some (absmsgq mls n pwl, wl) ->
    s |= EvtInv_part2 els tcblh tcbvl vhold scapl mcapl qcapl ** P ->
    s |= EvtInv_part2 ((set els eid (absmsgq nil n pwl, remove_tid tid wl))) tcblh tcbvl vhold scapl mcapl qcapl ** P. 
Proof.
  introv Hget Hsat.
  unfold EvtInv_part2 in *.
  sep normal in Hsat.
  sep normal.
  sep pauto.
  sep cancel AOSEventFreeList.
  eapply ASemEIBs_q_nil_rm_tid_preserve_frm; eauto.
  sep cancel ASemEIBs.
  eapply AMuxEIBs_q_nil_rm_tid_preserve_frm; eauto.
  sep cancel AMuxEIBs.
  apply astar_r_aemp_elim.
  eapply AMqEIBs_q_nil_rm_tid_preserve_frm; eauto.
  sep cancel AMqEIBs. auto.
  3: { eapply sem_ecb_p_que_mls'_wls'_preserve; eauto. }
  2: { eapply mux_ecb_p_que_mls'_wls'_preserve; eauto. }
  eapply q_ecb_p_que_mls'_wls'_preserve;eauto.
Qed.

Lemma beq_tid_true_eq :
  forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
Proof.
  intros.
  unfolds in H.
  destruct t1, t2.
  apply andb_true_iff in H.
  destruct H.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  pose proof Int.eq_spec i i0.
  rewrite H0 in H1.
  substs; auto.
Qed.

Lemma msgqnode_p_nomsg:
  forall qptr qst qend qin qout size qens qblk mblk ml A l ,
    Int.ltu ($ 0) qens = false ->
    RLH_ECBData_P
      ( 
        DMsgQ l (qptr
                   :: qst
                   :: qend
                   :: qin
                   :: qout
                   :: Vint32 size :: Vint32 qens :: Vptr qblk :: nil)
              mblk ml) A ->
    exists qmax pwl wl, A = (absmsgq nil qmax pwl,wl).
Proof.
  intros.
  unfolds in H0.
  destruct A.
  destruct e; tryfalse.
  simp join.
  funfold H0.
  funfold H1.
  funfold H2.
  lets Heq : int_ltu_false_eq0 H.
  rewrite Heq in H1.
  apply eq_sym in H1.
  apply zof_nat_eq_zero_zero in H1.
  apply length_zero_nil in H1.
  subst l0.
  eauto.
Qed.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma h_has_same_msg: 
  forall b qptr qst qend qin outi qsize qens qblk sti l  qblkm vl hml,
    Int.ltu ($ 0) qens = true ->
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) ->
    length vl = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: qsize :: Vint32 qens :: Vptr qblk:: nil) ->
    RLH_ECBData_P (DMsgQ l
                         (qptr
                            :: qst
                            :: qend
                            :: qin
                            :: Vptr (b, outi)
                            :: qsize :: Vint32 qens :: Vptr qblk:: nil) 
                         qblkm vl) hml -> 
    exists vl' max pwl wl, hml = (absmsgq ((nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) vl) :: vl')  max pwl , wl).
Proof.
  introv Hint Hid  Hlen Hwl Hrl .
  funfold Hwl. rename H12 into Hentryltsize. rename x6 into qens. rename H13 into H11.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in Hid.
   inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  destruct hml.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in *.
  rewrite Int.repr_unsigned in *.
  lets Hes : int_nat_ltu_lt H7 Hint.
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l0.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
       Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
          Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
        Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) ) by lia.
  destruct H5 as [Ha1 | [Ha2 | Ha3] ].
  apply H19 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'  H10 H2 H11; eauto.
  rewrite <- Heq.
  subst xx.
  do 3 eexists; eauto.
  apply H21 in Ha2.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H5.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  rewrite app_comm_cons in Ha2.
  apply app_inv_tail in Ha2.
  lets Has : vallist_seg_prop_eq Ha2.
  subst xx.
  do 3 eexists; eauto.
  apply H22 in Ha3.
  destruct Ha3.
  simp join; tryfalse.
  destruct H5.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H16.
  lets Hsp : list_append_split Hdas H9.
  simp join.
  rewrite app_comm_cons in H9.
  apply app_inv_tail in H9.
  lets Has : vallist_seg_prop_eq H9.
  subst xx.
  do 3 eexists; eauto.
Qed.

(* Lemma h_has_same_msg: 
  forall b qptr qst qend qin outi qsize qens qblk sti l  qblkm vl hml,
    Int.ltu ($ 0) qens = true ->
    id_addrval qblk msgqueuetbl os_ucos_h.OS_Q_FREEBLK = Some (b, sti) ->
    length vl = ∘OS_MAX_Q_SIZE ->
    WellformedOSQ
      (qptr
         :: qst
         :: qend
         :: qin
         :: Vptr (b, outi)
         :: qsize :: Vint32 qens :: Vptr qblk:: nil) ->
    RLH_ECBData_P (DMsgQ l
                         (qptr
                            :: qst
                            :: qend
                            :: qin
                            :: Vptr (b, outi)
                            :: qsize :: Vint32 qens :: Vptr qblk:: nil) 
                         qblkm vl) hml -> 
    exists vl' max wml wl , hml = (absmsgq ((nth_val' (Z.to_nat ((Int.unsigned outi - Int.unsigned sti) / 4)) vl) :: vl')  max wml , wl).
Proof.
  introv Hint Hid  Hlen Hwl Hrl .
  funfold Hwl.
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  simpl in *.
  destruct x5.
  apply eq_sym in Hid.
   inverts Hid.
  remember ( i2+ᵢ($ 4+ᵢInt.zero)) as k.
  inverts H5.
  destruct hml.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in *.
  rewrite Int.repr_unsigned in *.
  lets Hes : int_nat_ltu_lt H7 Hint.
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l0.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
       Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
          Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) \/
          Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
        Int.unsigned (Int.divu (outi-ᵢ$ 4) ($ 4)) ) by lia.
  destruct H5 as [Ha1 | [Ha2 | Ha3] ].
  apply H19 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'  H10 H2 H11; eauto.
  rewrite <- Heq.
  subst xx.
  do 3 eexists; eauto.
  apply H21 in Ha2.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H5.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  rewrite app_comm_cons in Ha2.
  apply app_inv_tail in Ha2.
  lets Has : vallist_seg_prop_eq Ha2.
  subst xx.
  do 3 eexists; eauto.
  apply H22 in Ha3.
  destruct Ha3.
  simp join; tryfalse.
  destruct H5.
  lets Heq :  math_out_start_eq' H10 H2  H11; eauto.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) vl) as ls.
  assert ( (∘(Int.unsigned m) <= length vl)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop  H2 H16.
  lets Hsp : list_append_split Hdas H9.
  simp join.
  rewrite app_comm_cons in H9.
  apply app_inv_tail in H9.
  lets Has : vallist_seg_prop_eq H9.
  subst xx.
  do 3 eexists; eauto.
Qed. *)

Fixpoint get_ectr (eid:val) (head:val) (ectrl:list EventCtr) :=
  match eid,head,ectrl with
    | (Vptr e),(Vptr e'),(osevent, etbl,petbl)::vll =>
      match beq_addrval e e' with
        | true => Some (osevent,etbl, petbl)
        | false => match V_OSEventListPtr osevent with
                     | Some vn => get_ectr eid vn vll
                     | _ => None
                   end
      end
    | _,_,_ => None
  end.


Lemma joinsig_beq_addrval_false_get : forall a a1 x x1 m1 m2,
  joinsig a x m1 m2 -> EcbMod.get m2 a1 = Some x1 -> a <> a1 -> EcbMod.get m1 a1 = Some x1. 
Proof.
  intros.
  unfold joinsig in H.
  pose proof H a1.
  rewrite EcbMod.get_sig_none in H2; auto.
  rewrite H0 in H2.
  destruct (EcbMod.get m1 a1); tryfalse.
  substs; auto.
Qed.

Lemma beq_pos_true : forall p, beq_pos p p = true.
Proof.
  inductions p.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  unfolds.
  fold beq_pos.
  rewrite IHp; auto.
  simpl; auto.
Qed.

Lemma beq_addrval_false_neq : forall a1 a2, beq_addrval a1 a2 = false -> a1 <> a2.
Proof.
  intros.
  unfolds in H.
  destruct a1, a2.
  intro.
  inverts H0.
  rewrite beq_pos_true in H.
  rewrite Int.eq_true in H.
  simpl in H; tryfalse.
Qed.
(* 
Lemma ECBList_P_get_ectr_some : forall (l:list EventCtr) tl ecbls mqls tcbls a x v,
  EcbMod.get mqls a = Some x -> ECBList_P v tl l ecbls mqls tcbls ->
  exists et etbl, get_ectr (Vptr a) v l = Some (et, etbl).
Proof.
  inductions l; intros.
  simpl in H0; mytac.
  unfolds in H; simpl in H; tryfalse.
  simpl in H0.
  destruct ecbls; mytac; tryfalse.
  destruct a; destruct p; mytac.
  simpl.
  destruct (beq_addrval a0 x0) eqn : eq1.
  eauto.
  rewrite H0.
  assert (EcbMod.get x2 a0 = Some x).
  apply beq_addrval_false_neq in eq1.
  eapply joinsig_beq_addrval_false_get; eauto.
  clear H.
  eapply IHl; eauto.
Qed.
 *)

Lemma beq_addrval_eq: forall a b, beq_addrval a b = true -> a = b.
Proof.
  introv HeqX.
  unfold beq_addrval in HeqX.
  destruct b, a.
  rewrite andb_true_iff in HeqX.
  destruct HeqX.
  rewrite beq_pos_Pos_eqb_eq in H.
  apply Peqb_true_eq in H.
  lets Hx: Int.eq_spec i0 i.
  rewrite H0 in Hx.
  subst.
  auto.
Qed.

Lemma eq_beq_addrval: forall a, beq_addrval a a = true.
Proof.
  unfold beq_addrval.
  destruct a.
  rewrite andb_true_iff.
  split.
  rewrite beq_pos_Pos_eqb_eq.
  apply Pos.eqb_refl.
  apply Int.eq_true.
Qed.

Ltac xunfold' H:=
  let M:= fresh in  
  match type of H with
    | match ?X with
        | _ => _
      end = Some _ => remember X as M;destruct M;tryfalse;auto
    | _ => idtac
  end.

Lemma get_ectr_decompose:
  forall qptrl s P msgqls l x y p eid,
    s |= evsllseg p Vnull qptrl msgqls ** P ->
    get_ectr (Vptr eid) p qptrl = Some ((l,x),y) ->
    s |= EX vn qptrl1 qptrl2 msgqls1 msgqls2 msgq, 
  [| V_OSEventListPtr l = Some vn /\
     qptrl = qptrl1 ++ (((l, x), y) :: nil) ++ qptrl2 /\
     msgqls = msgqls1 ++ (msgq :: nil) ++ msgqls2 /\ get_ectr (Vptr eid) p qptrl1 = None /\
   (get_ectr  (Vptr eid) p (qptrl1++ (((l, x) ,y) :: nil)) = Some ((l,x),y)) /\ p <> Vnull /\ forall l,In l qptrl1 -> exists x,V_OSEventListPtr (fst (fst l)) = Some (Vptr x)|] **
                                                     AEventNode (Vptr eid) l x y msgq **
                                                     evsllseg p (Vptr eid) qptrl1 msgqls1 ** evsllseg vn Vnull qptrl2 msgqls2 ** P.
Proof.
  induction qptrl.
  intros.
  simpl evsllseg in *.
  sep split in H.
  destruct H1;subst.
  simpl in H0.
  tryfalse.
  intros.
  simpl evsllseg in *.
  destruct msgqls.
  simpl in H;mytac;tryfalse.
  destruct a as (osevent,petbl).
  destruct osevent as (osevent, etbl).
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpl in H0.
  destruct p;tryfalse.
  remember (beq_addrval eid a) as X.
  destruct X.
  inverts H0.
  sep lift 2%nat in H.
  exists x0 (nil:list EventCtr) qptrl.
  exists (nil:list EventData) msgqls e.
  simpl evsllseg.
  symmetry in HeqX.
  apply beq_addrval_eq in HeqX.
  subst.
  sep auto.
  simpl;splits;auto.
  rewrite eq_beq_addrval.
  auto.
  intro;tryfalse.
  intros.
  tryfalse.
  xunfold' H0.
  inverts H1.
  sep lift 2%nat in H.
  lets Hx: IHqptrl H H0.
  sep normal in Hx.
  clear H.
  sep destruct Hx.
  sep split in Hx.
  mytac.
  clear IHqptrl.
  sep auto.
  Focus 2.
  splits;simpl.
  eauto.
  instantiate (1:=x3).
  instantiate (1:= (osevent, etbl, petbl) :: x2).
  simpl.
  auto.
  instantiate (1:= x5).
  instantiate (1:= x6).
  instantiate (1:= e :: x4).
  simpl;auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  simpl.
  rewrite <- HeqX.
  rewrite <- HeqH2.
  auto.
  intro;tryfalse.
  intros.
  simpl in H1.
  destruct H1;auto.
  subst.
  simpl.
  rewrite <- HeqH2.
  destruct eid;tryfalse.
  destruct x2;destruct x0;simpl in H4;tryfalse;eexists;auto.
  simpl evsllseg at 1.
  sep auto.
Qed.

Lemma evsllseg_aux:
  forall l1 s a b l2 P,
    s |= evsllseg a b l1 l2 ** P ->
    (a = b /\ l1 = nil \/ get_last_ptr l1 = Some b) /\ length l1 = length l2.
Proof.
  inductions l1.
  intros.
  simpl in H.
Import DeprecatedTactic.
  mytac.
  left.
  auto.
  auto.
  intros.
  unfold evsllseg in H.
  fold evsllseg in H.
  destruct l2.
  simpl in H.
  mytac; tryfalse.
  destruct a.
  destruct p.
  sep normal in H.
  sep destruct H.
  sep lift 3%nat in H.
  lets Hxax: IHl1 H.
  mytac.
  2: simpl; auto.
  destruct H0.
  mytac.
  right.
  unfolds.
  simpl.
  sep split in H.
  auto.
  right.
  unfolds.
  simpl.
  destruct l1.
  unfolds in H0.
  simpl in H0.
  unfolds in H0.
  unfold nth_val in H0.
  tryfalse.
  simpl.
  auto.
Qed.

Lemma ecblistp_evsllseg_tlsame:
  forall ls1 hd tl tl' ls2 hls tcbls P s,
       ECBList_P hd tl ls1 ls2 hls tcbls ->
       s |= evsllseg hd tl' ls1 ls2 ** P ->
       tl  = tl'.
Proof.
  induction ls1.
  intros.
  simpl in H.
  simpljoin.
  unfold evsllseg in H0.
  sep split in H0.
  tauto.
  intros.
  unfold1 ECBList_P in H.
  simpljoin.
  destruct ls2; tryfalse.
  destruct a;destruct p; simpljoin.
  unfold1 evsllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0.
  rewrite H in H6.
  inverts H6.
  eapply IHls1.
  eauto.
  sep lift 2%nat in H0.
  eauto.
Qed.

Lemma wellq_props:
  forall x12 x11 x5 x6 v'49 x i2 i1  v'47 x13 x14 v2 v'46,
    length v2 = ∘OS_MAX_Q_SIZE ->
    Int.ltu ($ 0) i1 = true ->
    RLH_ECBData_P
      (DMsgQ (Vptr (v'47, Int.zero))
             (x12
                :: x11
                :: x5
                :: x6
                :: Vptr (v'49, x)
                :: Vint32 i2
                :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil)
             (x13 :: x14 :: nil) v2) v'46 ->
    WellformedOSQ
      (x12
         :: x11
         :: x5
         :: x6
         :: Vptr (v'49, x)
         :: Vint32 i2
         :: Vint32 i1 :: Vptr (v'49, Int.zero) :: nil) ->
    Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x /\
    4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
    Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
    (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < Z.of_nat (length v2) /\
    rule_type_val_match (Void) ∗
                        (nth_val'
                           (Z.to_nat
                              ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                           v2) = true.
Proof.
  introv Hlen Hint Hrl  Hwf.
  Definition auxand P Q :=  P /\ Q.
  assert (auxand (Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) <= Int.unsigned x)
                 (4 * ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4) =
                  Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero)) /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 < 20 /\
                  (Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4 <
                  Z.of_nat (length v2) /\
                  rule_type_val_match (Void) ∗
                                      (nth_val'
                                         (Z.to_nat
                                            ((Int.unsigned x - Int.unsigned (Int.zero+ᵢ($ 4+ᵢInt.zero))) / 4))
                                         v2) = true
                 )).
  funfold Hwf. rename x9 into qens; rename H12 into Hensltsize; rename H13 into H11. (*add by yss*)
  unfold arrayelem_addr_right in *.
  unfold qend_right, ptr_offset_right,ptr_minus,  distance in *.
  simp join.
  fsimpl.
  inverts H5.
  unfolds in Hrl.
  destruct v'46.
  destruct e; tryfalse.
  destruct Hrl as (Hm1 & Hm2 & Hm3).
  destruct Hm3 as (Hm3 & _).
  funfold Hm1.
  funfold Hm2.
  funfold Hm3.
  unfold distance in *.
  simpl in H7, H10, H18, H20, H21.
  rewrite Int.repr_unsigned in *.
  assert ((Int.zero+ᵢ($ 4+ᵢInt.zero)) = $4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  assert (Int.unsigned ($ 4) =4).
  clear -x.
  mauto.
  rewrite H1 in *.
  clear H1.
  splits.
  clear -H.
  int auto.
  apply eq_sym.
  eapply Z_div_exact_2; try lia.
  eapply math_prop_int_modu; eauto.
  eapply math_prop_ltu_20; eauto.
  rewrite Hlen.
  unfold OS_MAX_Q_SIZE.
  simpl.
  eapply math_prop_ltu_20; eauto.
  assert (Int.unsigned ($4) = 4). 
  clear -x.
  mauto.
  assert ( Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) >
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))  \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) <
         Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4)) \/
         Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4)) =
           Int.unsigned (Int.divu (x-ᵢ$ 4) ($ 4))) by lia.
  lets Hes : int_nat_ltu_lt H5 Hint. 
  lets Hls : list_length_lt Hes.
  destruct Hls as (xx & ll & lt).
  subst l.
  destruct H9 as [Ha1 | [ Ha2 | Ha3]].
  apply H18 in Ha1.
  lets Has : vallist_seg_prop_eq Ha1.
  lets Heq :  math_out_start_eq'   H11; try eapply H; eauto.
  rewrite H1 in *.
    rewrite <- Heq.
  rewrite <- Has.
  simpl in H19.
  destruct H19.
  simpl.
  clear - H9.
  pauto.
  apply H20 in Ha2.
  lets Heq :  math_out_start_eq'   H11; try eapply H; eauto.
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha2.
  simp join.
  simpl in H19.
  destruct H19.
  apply vallist_seg_prop_eq in H16.
  rewrite <- H16.
  simpl.
  clear -H7.
  pauto.
  apply H21 in Ha3.
  lets Heq :  math_out_start_eq'   H11; try eapply H; eauto.
  destruct Ha3 as [Haa | Ha3].
  simp join; tryfalse.
  destruct Ha3 as (Heqa & Ha3).
  rewrite H1 in *.
  rewrite <- Heq.
  remember (vallist_seg 0 ∘(Int.unsigned (Int.divu (i0-ᵢ$ 4) ($ 4))) v2) as ls.
  assert ( (∘( ( Int.unsigned m)) <= length v2)%nat).
  eapply list_maxsize_le; eauto.
  lets Hdas: vallist_seg_prop H2 H9; eauto.
  lets Hsp : list_append_split Hdas Ha3.
  simp join.
  simpl in H19.
  destruct H19.
  apply vallist_seg_prop_eq in H16.
  rewrite <- H16.
  simpl.
  clear -H7.
  pauto.
  auto.
Qed.

Lemma osq_same_blk_st_out'
: forall (qptr qst qend qin qout qsz qen : val) 
         (b : block) (i : int32),
    WellformedOSQ
      (qptr
         :: qst :: qend :: qin :: qout :: qsz :: qen :: Vptr (b,i) :: nil) ->
    exists i', qout = Vptr (b, i').
Proof.
  introv Hwf.
  funfold Hwf.
  simpl in H5.
  funfold H9.
  funfold H10.
  unfold ptr_offset_right in *.
  unfold ptr_minus in *.
  inverts H5.
  unfolds in H8.
  simpl in *.
  simp join.
  rewrite H5 in *.
  destruct x1.
  destruct x2.
  remember ((b0 =? b)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  apply eq_sym in HeqHbool.
  inverts HeqHbool.
  remember ((b1 =? b0)%positive ) as Hbool.
  destruct Hbool; tryfalse.
  simp join.
  rewrite Pos2Z.inj_eqb in HeqHbool.
  apply eq_sym in HeqHbool.
  apply Z.eqb_eq in HeqHbool.
  inverts HeqHbool.
  eauto.
Qed.

Ltac lzh_find_ret_stmt stmts :=
  match stmts with
    | sseq ?s ?rs =>
      match s with
        | srete _ => constr:(some 1%nat)
        | _ => lzh_find_ret_stmt rs
      end
    | srete _ => constr:(some 1%nat)
    | _ => constr:(none 1%nat)
  end.

Ltac lzh_destruct_event :=
  match goal with
    | |- context [match ?d with
                    | DMsgQ _ _ _ _ => _
                    | DSem _ => _
                    | DMbox _ => _
                    | DMutex _ _ => _
                  end] => destruct d
    | _ => fail
  end.

Ltac lzh_unfold_event := 
  try unfold AEventNode;
    try unfold AEventData; 
      try lzh_destruct_event;
      try unfold AMsgData; 
      try unfold AOSQCtr; try unfold AOSQBlk;
    try unfold AOSEvent;
      try unfold AOSEventTbl;
  try unfold node. 

Ltac lzh_unfold_var x := 
   match x with
    | OSQFreeBlk =>  try unfold OSInv; try unfold AOSQFreeBlk;  unfold_qblkfsll 
    | OSQFreeList =>  try unfold OSInv; try unfold AOSQFreeList;  unfold_sll
  (*  | OSEventPtrFreeList => try unfold OSInv; try unfold AOSEventPtrFreeList;  unfold_sll
*)   
    | OSEventFreeList => try unfold OSInv; try unfold AOSEventFreeList; unfold_ecbfsll
    | OSEventList => try unfold OSInv; try unfold AECBList; unfold_msgslleg
    | OSTCBCur => try unfold OSInv; try unfold AOSTCBList;unfold_dll
    | OSTCBList => try unfold OSInv; try unfold AOSTCBList
    | OSRdyTbl => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyTbl
    | OSRdyGrp => try unfold OSInv; try unfold AOSRdyTblGrp; try unfold AOSRdyGrp
    | OSTCBPrioTbl => try unfold OSInv; try unfold AOSTCBPrioTbl
    | OSTime => try unfold OSInv; try unfold AOSTime
    | 999%Z =>  lzh_unfold_event
    | OSIntNesting => try unfold OSInv; try unfold AOSIntNesting
    | OSRunning => try unfold OSInv; try unfold AGVars
    | _ => idtac
   end.  

Ltac lzh_unfold_exprlist ls :=  
  match ls with 
    | ((eunop _ ?e) :: ?l)%list => unfold_exprlist ((e::l)%list)
    | ((ebinop _ ?e1 ?e2) :: ?l)%list =>  unfold_exprlist ((e1::e2::l)%list)
    | ((ederef ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((eaddrof ?e) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((efield ?e ?id) :: ?l)%list =>  unfold_exprlist ((e::(evar 999%Z) :: l)%list)
    | ((ecast ?e _) :: ?l)%list =>  unfold_exprlist ((e::l)%list)
    | ((earrayelem ?e1 ?e2) :: ?l)%list => unfold_exprlist ((e1::e2::l)%list)
    | ((evar ?x) ::?l)%list => lzh_unfold_var x; unfold_exprlist l
    | (enull:: ?l)%list => unfold_exprlist l
    | ((econst32 _) :: ?l) => unfold_exprlist l
    | (@nil expr)%list => idtac
  end. 

Ltac lzh_hoare_unfold :=
  try unfold OSInv; try unfold_funpost;
  match goal with
    | |- {| _, _, _, _, _, _ |} |- ?ct {{ _ }} _ {{ _ }} =>
      hoare_split_pure_all;
        let x := find_first_exprs in
          lzh_unfold_exprlist x; pure_intro
    | _ => idtac
  end.

Ltac lzh_val_inj_solver :=
  intros be H;
  destruct be;
  match goal with
    | |- ?X = ?X => reflexivity
    | |- ?X = ?Y => 
        simpl in H;
        (* ** ac: idtac "X"; *)
        try (unfold Int.notbool in H);
        first [rewrite Int.eq_true in H |
               rewrite Int.eq_false in H | idtac];
        destruct H; tryfalse; auto
  end.

Lemma val_inj_false:
  forall (be : bool),
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vint32 Int.zero \/
     val_inj
       (if be
        then Some (Vint32 Int.one)
        else Some (Vint32 Int.zero)) = Vnull ->
     be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_true:
  forall (be : bool),
    val_inj
      (notint
         (val_inj
            (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vint32 Int.zero /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vnull /\
       val_inj
         (notint
            (val_inj
               (if be
                then Some (Vint32 Int.one)
                else Some (Vint32 Int.zero)))) <> Vundef ->
    be = false.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_not_false:
  forall (be : bool),
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vint32 Int.zero \/
     val_inj
       (notint
          (val_inj
             (if be
              then Some (Vint32 Int.one)
              else Some (Vint32 Int.zero)))) = Vnull ->
     be = true.
  lzh_val_inj_solver.
Qed.

Lemma val_inj_impl_neq:
  forall x y,
    val_inj (val_eq x y) = Vint32 Int.zero \/
    val_inj (val_eq x y) = Vnull ->
    x <> y.
  (* 对x y做destruct，需要编写通用的tactic来解决这类问题 *)
  intros.
  assert (x = y \/ x <> y) by tauto.
  destruct H0.
  subst.
  unfold val_eq in H.
  destruct y.
  unfold val_inj in H.
  destruct H; tryfalse.
  unfold val_inj in H; destruct H; tryfalse.
  rewrite Int.eq_true in H.
  unfold val_inj in H; destruct H; tryfalse.
  destruct a.
  destruct (peq b b).
  rewrite Int.eq_true in H; unfold val_inj in H; destruct H; tryfalse.
  tryfalse.
  auto.
Qed.

Lemma val_inj_true:
  forall (be : bool),
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vnull /\
    val_inj
      (if be
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)) <> Vundef ->
    be = true.
  lzh_val_inj_solver.
Qed.

Ltac lzh_val_inj_simpl :=
  match goal with
    | H : val_inj ?e <> Vint32 Int.zero /\
          val_inj ?e <> Vnull /\
          val_inj ?e <> Vundef |- _ =>
      match e with
        | notint _ => apply val_inj_not_true in H
        | val_eq ?x Vnull => apply val_inj_impl_Vnull in H
        | val_eq ?x ?y => apply val_inj_impl_eq in H
        | _ => try apply val_inj_true in H
      end
   
    | H : val_inj ?e = Vint32 Int.zero \/
          val_inj ?e = Vnull |- _ =>
      match e with
        | notint _ => apply val_inj_not_false in H
        | val_eq ?x Vnull => 
          apply val_inj_impl_Vptr in H; destruct H; subst x
        | val_eq ?x ?y =>
          apply val_inj_impl_neq
        | _ => try apply val_inj_false in H
      end

    | _ => idtac
  end.
  
Ltac lzh_hoare_if2 :=
  lzh_hoare_unfold;
  hoare forward; 
  match goal with
    | |- {|_, _, _, _, _, _|} |- ?ct {{?p ** [|?v <> Vint32 Int.zero /\
                                       ?v <> Vnull /\
                                       ?v <> Vundef|]}} ?stmts {{_}} =>
      (* ** ac: idtac "if block proof"; *)
      let x := lzh_find_ret_stmt stmts in
        match x with
          | some _ => instantiate (1:=Afalse)
          | none _ => idtac
        end;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse

    | |- {|_, _, _, _, _, _|} |- ?ct {{_}} _ {{_}} => 
      (* ** ac: idtac "if all"; *)
      hoare forward;
      hoare_split_pure_all;
      lzh_val_inj_simpl; tryfalse
      (* first proof if-true condition, then proof if-false condition *)
    | _ => pauto
  end.

Ltac exact_s :=
  match goal with
    | H : ?s |= _ |- ?s |= _ =>
      exact H
  end.

Ltac transform_pre lemma cancel_tac :=
  eapply backward_rule1;
  [ intros; 
    eapply lemma; 
    match goal with
      | |- ?s |= _ => 
        cancel_tac;
        try exact_s;
        sep pauto
      | _ => solve [eauto;auto | pauto]
    end  
   | idtac ].

Lemma qacc_eventtype_neq_q:
   forall s P a msgq mq t,
    s |= AEventData a msgq ** P ->
    RLH_ECBData_P msgq mq ->
    V_OSEventType a = Some (Vint32 t) ->
    Int.eq t ($ OS_EVENT_TYPE_Q) = false ->
    s |= AEventData a msgq **
         [| (~ exists m n pwl wl, mq = (absmsgq m n pwl,wl)) |] ** P.
  intros.

  unfold AEventData in *.
  destruct msgq eqn:Hmsgq.
  sep split in H.
  sep auto.
  sep split in H.
  rewrite H4 in H1.
  inverts H1.
  rewrite Int.eq_true in H2.
  tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

  sep split in H.
  sep auto.
  unfold RLH_ECBData_P in H0.
  destruct mq; destruct e eqn:Hmq; tryfalse.
  unfold not; intros; mytac; tryfalse.

Qed.


(* Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac sep_lift_context trm :=
  match goal with
    | |- _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat
      end
  end.
*)

(* Ltac mytac_lift_ACNU :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_match_context P ACNU with
            | none _ => idtac 1 "no ACNU in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.
  
Ltac mytac_lift_absop :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_aop P with
            | none _ => idtac 1 "no absop in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.
  
Ltac mytac_lift_absecbls :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P absecblsid with
            | none _ => idtac 1 "no absebls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.
  
Ltac mytac_lift_abstcbls :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P abstcblsid with
            | none _ => idtac 1 "no absebls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac mytac_lift_abscurtid :=
  match goal with
    | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
          match find_absdata P curtid with
            | none _ => idtac 1 "no absebls in the pre-condition"; fail 1
            | some ?a => hoare lifts (a::nil) pre
          end
  end.

Ltac hoare_lift_context_pre cx :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; sep_lift_context_in H cx; exact H | idtac ]
    | |-  {| _, _, _, _, _, _ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; sep_lift_context_in H cx; exact H | idtac ]
  end. *)

Lemma option2val:
  forall T (x y: T),
    Some x = Some y -> x = y.
Proof.
  intros T x y.
  intros F1.
  inversion F1.
  trivial.
Qed.  

Ltac test2:=
match goal with
                | |- ?P' <==> PV ?l @ _ |-> _ ** _ =>
                  match find_ptrmapsto P' l with
                    | none _ => fail 2
                    | some ?b => 
                      intros until s; split; intros H;
                      [ sep lift b in H; exact H
                      | sep lift b;  exact H ]
                  end
              end.
              
Lemma beq_tid_true :
  forall tid, beq_tid tid tid = true.
Proof.
  intros.
  unfolds.
  destruct tid.
  rewrite beq_pos_true.
  rewrite Int.eq_true.
  auto.
Qed.




