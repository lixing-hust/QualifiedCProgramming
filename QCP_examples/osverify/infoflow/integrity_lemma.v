Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import buffer_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import if_assms.
Require Import if_succ_gen.
Require Import if_good_code.

Require Import hasrt_sat_preserve.
Require Import FunctionalExtensionality.
Require Import spec_aux_defs.


Set Keyed Unification.

Require Import confidentiality_tactics.
Require Import if_common_lemmas.

Ltac kvextH H1 mp0 k mp :=
  match goal with
    H: context [get mp0 k = ?v] |- _ => assert (H1: get mp k = v)
  end;
  [ eapply join_get_get_l; eauto; repeat rewsimp; auto | idtac ].

Lemma bufidx_diff_dom:
forall d1 d2 i,
  d1 <> d2 ->
  buf_in_dom i d1 = true ->
  buf_in_dom i d2 = true ->
  False. 
Proof.
intros.
eapply bufadr_diff_dom in H0,H1.
destruct i. 
eapply dom_disj_addrs;eauto.
Qed.

  Lemma dom_for_prio_neq:
forall pr pr1,
dom_for_prio pr1 <> dom_for_prio pr ->
pr1 <> pr.
Proof.
intros.
intro; subst; tryfalse.
Qed.

Lemma task_prio_id_set_ntls_eq:
forall O O' pr aid abs,
(exists t, task_prio_id O pr t )->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
(exists t, task_prio_id O' pr t).
Proof.
introv Ht Heq Hneq.
simpljoin.
exists x.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a'; eauto.
rewrite H.
do 5 eexists; eauto.
Qed.

Lemma task_prio_id_set_ntls_eq':
forall O O' pr aid abs,
(exists t, task_prio_id O' pr t )->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
(exists t, task_prio_id O pr t).
Proof.
introv Ht Heq Hneq.
simpljoin.
exists x.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a' in H; eauto.
rewrite H.
do 5 eexists; eauto.
Qed.


Definition mq_ref_preserved' (O O': osabst) :=
  mq_ref_preserved O O' /\
  mq_ref_preserved O' O.


Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

(* same lemma as in confidentiality_proof.v *)
Lemma prio_unique:
  forall O pr t pr', task_prio_id O pr t -> task_prio_id O pr' t -> pr = pr'.
Proof.
  introv Htpi Htpi'.
  unfold task_prio_id in *.
  simpljoin.
  rewrite H0 in H.
  inverts H.
  rewrite H2 in H1.
  inverts H1.
  auto.
Qed.   

Lemma estep_dom_intact:
  forall d d' c m c' m' ge le M ge' le' M' ke ke', 
    estep d c ke m c' ke' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'. 
Proof.
  introv Hestep Hm Hm' Hdd'.
  subst.
  inverts Hestep; try auto.
Qed.  

(* same lemma as in confidentiality_proof.v *) 
Lemma storebytes_get_old_blk': 
  forall (vl: list memval) m m' b b' (i i': Z),  
    storebytes m (b, i) vl = Some m' ->
    b <> b' -> 
    get m' (b', i') = get m (b', i'). 
Proof.  
  induction vl; introv Hsb Hneq.
  - simpl in Hsb.
    inverts Hsb.
    auto.
  - simpl in Hsb.
    destruct (get m (b, i)) eqn: E.
    + rewrite E in Hsb.
      destruct p as (tf, mv).
      destruct tf; tryfalse.
      destruct (storebytes m (b, i + 1) vl) eqn: E'; tryfalse.
      inverts Hsb.
      rewrite set_a_get_a'; eauto.
      introv Hf.
      inverts Hf. 
      apply Hneq; auto.
    + rewrite E in Hsb.
      tryfalse.
Qed.


Lemma store_intact0: 
  forall t M a0 a v M' d, 
    store t M a0 v = Some M' -> 
    addr_in_dom a0 d = true ->
    addr_in_dom a d = false ->
    get M a = get M' a. 
Proof.
  introv Hstore Hin Hnotin.
  unfolds in Hstore.
  destruct a0 as (b0, o0).
  destruct a as (b, o).
  assert (b <> b0).
  {
    casetac b b0 Ht Hf.
    subst.
    erewrite n_block_cross_part in Hin. rewrite Hnotin in Hin. tryfalse.
    auto.
  }
  symmetry.
  eapply storebytes_get_old_blk'; eauto.
Qed.   

(* same lemma as in confidentiality_proof.v *) 
Lemma get_dom_mem_allocb_eq: 
  forall n b i d d0 m m', 
    addr_in_dom (b, i) d = true ->
    allocb m b i n = m' ->
    d <> d0 -> 
    get_dom_mem m d0 = get_dom_mem m' d0.
Proof.
  induction n; 
    introv Haid Halc Hneq.
  -
    simpl in Halc.
    subst. auto.
  -
    simpl in Halc.
    remember (allocb m b (i + 1) n) as m''.
    symmetry in Heqm''.
    assert (Haid': addr_in_dom (b, i+1) d = true).
    { erewrite n_block_cross_part in Haid. eauto. }
    lets H_: IHn Haid' Heqm'' Hneq.
    assert (get_dom_mem m'' d0 = get_dom_mem m' d0).
    {
      unfolds.
      eapply functional_extensionality.
      intro a.
      destruct (addr_in_dom a d0) eqn: E.
      - rewrite <- Halc.
        casetac (b, i) a He Hne.
        + subst.
          lets Hf: dom_disj_addrs Hneq Haid E.
          tryfalse.
        + rewrite set_a_get_a'; eauto.
      - auto.          
    }
    congruence.
Qed.

(* same lemma as in confidentiality_proof.v *) 
Lemma get_dom_mem_alloc_eq: 
  forall x tp le M le' M' d d0,    
    alloc_pt x tp le M le' M' d ->
    d <> d0 -> 
    get_dom_mem M d0 = get_dom_mem M' d0.  
Proof.
  introv Halcp Hneq.
  unfolds in Halcp.
  simpljoin.
  remember (allocb M x0 0 (typelen tp)) as m'.
  eapply get_dom_mem_allocb_eq; eauto.
Qed. 

(* same lemma as in confidentiality_proof.v *) 
Lemma get_dom_mem_freeb_eq:
  forall n m b i m' d d0, 
    freeb m b i n = Some m' ->
    addr_in_dom (b, i) d = true ->
    d <> d0 ->
    get_dom_mem m d0 = get_dom_mem m' d0.
Proof.
  induction n; 
    introv Hfrb Haid Hneq.
  -
    simpl in Hfrb. inverts Hfrb.
    auto.
  -
    simpl in Hfrb.
    destruct (get m (b, i)) eqn: E; tryfalse.
    destruct p.
    destruct b0; tryfalse.
    destruct (freeb m b (i + 1) n) eqn: E'; tryfalse.
    inverts Hfrb.
    assert (Haid': addr_in_dom (b, i+1) d = true).
    { erewrite n_block_cross_part in Haid. eauto. }
    lets H_: IHn E' Haid' Hneq.
    rewrite H_.
    unfolds.
    apply functional_extensionality. intro a.
    destruct (addr_in_dom a d0) eqn: E''.
    + 
      erewrite mem_del_get_neq'; eauto.
      introv Heq. subst.
      lets Hf: dom_disj_addrs Hneq Haid E''.
      auto.
    + 
      auto.
Qed.

Lemma sstep_dom_intact: 
  forall d d' pu c m c' m' ge le M ge' le' M' ks ks', 
    sstep pu d c ks m c' ks' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'.
Proof.
  introv Hsstep Hm Hm' Hindom.
  subst.
  inverts Hsstep; auto; 
    (repeat match goal with H: (_, _, _) = (_, _, _) |- _ => inverts H end);
    auto. 
  - unfolds.
    apply functional_extensionality.
    intro a'.
    destruct (addr_in_dom a' d') eqn: E.
    + 
      destruct (addr_in_dom a' d) eqn: E'.
      lets Hf: dom_disj_addrs E' E. auto. tryfalse.    
      eapply store_intact0; eauto.
      unfolds in H1.
      destruct a. simpl.
      destruct i. simpl in H1. simpl. auto.
    +
      auto. 
  -
    lets H_: get_dom_mem_alloc_eq H1 Hindom.
    rewrite H_.
    unfold alloc_pt in H1.
    simpljoin.
    rewrite set_a_get_a in H2.
    inverts H2.
    remember (allocb M0 b 0 (typelen t)) as M_.
    unfolds. 
    apply functional_extensionality.
    intro a'.
    destruct (addr_in_dom a' d') eqn: E.
    + 
      destruct (addr_in_dom a' d) eqn: E'.
      lets Hf: dom_disj_addrs E' E. auto. tryfalse.    
      eapply store_intact0; eauto.
    +
      auto. 
  -
    lets H_: get_dom_mem_alloc_eq H1 Hindom.
    auto.
  -
    eapply get_dom_mem_freeb_eq; eauto.
Qed. 

Lemma cstep_dom_intact:
  forall d d' p C m C' m' ge le M ge' le' M', 
    cstep p d C m C' m' ->
    m = (ge, le, M) ->
    m' = (ge', le', M') ->
    d <> d' -> 
    get_dom_mem M d' = get_dom_mem M' d'.
Proof.
  introv Hcstep Hm Hm' Hnin.
  subst.
  inverts Hcstep.
  - eapply estep_dom_intact; eauto.
  - eapply sstep_dom_intact; eauto.
Qed.     

Lemma reachable_get_bufsid:
  forall hp T cst O, 
    reachable hp T cst O ->
    exists x y,
      get O ibufsid = Some (ibufs x) /\ get O obufsid = Some (obufs y). 
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_buf_st in H6.
  simpljoin.
  unfold eqdomO0 in H_.
  assert (H__ := H_).
  destruct H_ as (H12 & _).
  specialize (H12 ibufsid).
  rewrite H6 in H12. 
  destruct H__ as (H12' & _).
  specialize (H12' obufsid).
  rewrite H8 in H12'.
  simpljoin.
  do 2 eexists.
  splits; eauto.
Qed. 

Lemma reachable_get_knldataid:
  forall hp T cst O,
    reachable hp T cst O ->
    exists x1 x2 x3 x4 x5 x6, 
      get O abstcblsid = Some (abstcblist x1) /\ 
        get O absmqattrid = Some (absmqattr x2) /\
        get O absecblsid = Some (absecblist x3) /\
        get O osdomainportid = Some (osdomainport x4) /\
        get O oskportid = Some (oskport x5) /\ 
        get O cspaceid = Some (capcspace x6).  
Proof.
  introv Hrc.
  unfolds in Hrc.
  simpljoin.
  lets H_: hpstepokstar_eqdomO0 H1.
  unfold init in H0.
  destruct H0 as (Hinittsk & Hinitst).
  unfolds in Hinitst.
  simpljoin.
  unfold init_tsk_st, init_evt_st, init_prt_st, init_cap_st in *.
  simpljoin.
  
  unfold eqdomO0 in H_.
  destruct H_ as (H1_2 & _).
  assert (H1_2' := H1_2).
  assert (H1_2'' := H1_2).
  assert (H1_2''' := H1_2).
  assert (H1_2'''' := H1_2).
  assert (H1_2''''' := H1_2). 
  specialize (H1_2 abstcblsid).
  unfold get in H1_2. unfold AMap in H1_2. 
  rewrite H3 in H1_2.
  specialize (H1_2' absmqattrid).
  unfold get in H1_2'. unfold AMap in H1_2'.
  rewrite H4 in H1_2'. 
  specialize (H1_2'' absecblsid). 
  unfold get in H1_2''. unfold AMap in H1_2''.
  rewrite H11 in H1_2''.
  specialize (H1_2''' osdomainportid). 
  unfold get in H1_2'''. unfold AMap in H1_2'''.
  rewrite H10 in H1_2'''.
  specialize (H1_2'''' oskportid). 
  unfold get in H1_2''''. unfold AMap in H1_2''''.
  rewrite H5 in H1_2''''.
  specialize (H1_2''''' cspaceid).
  rewrite H7 in H1_2'''''.

  simpljoin.
  do 6 eexists. 
  splits; eauto.
Qed. 

Lemma client_data_equiv_local_upd_preserve:           
  forall O pr t d d0 ges cenvs le' M M', 
    task_prio_id O pr t -> 
    dom_for_prio pr = d -> 
    ~flowsTo (TaskDom d) (TaskDom d0) -> 
    get_dom_mem M d0 = get_dom_mem M' d0 ->           
    client_data_equiv d0 (ges, cenvs, M) (ges, set cenvs t le', M') O O. 
Proof.
  introv Htpi Hd Hfl Hgd.
  unfold client_data_equiv.
  do 6 eexists. 
  splits; eauto.
  unfold local_envs_equiv.
  introv Hd' Htpi1 Htpi2.
  assert (t1 = t2).
  { eapply tid_unique; eauto. }
  subst.
  casetac t t2 He Hne.
  - subst.
    assert (pr = pr0).
    { eapply prio_unique; eauto. }
    subst.
    false. apply Hfl. apply flows_to_refl.
  - rewrite set_a_get_a'; eauto. 
Qed.     
  
Lemma knl_hapicode:
  forall c, ~ not_knl_stmt c -> (exists ss, c = curs (hapi_code ss)).
Proof.
  introv Hknl.
  destruct c.
  -
    false. apply Hknl.
    unfolds. left. eexists; eauto.
  -
    destruct s; 
      try (false; apply Hknl; unfolds; right; eexists; splits; eauto; introv Hf; simpljoin; tryfalse; fail).
    eexists; eauto. 
Qed.     
  
Lemma code_equiv_tskd_local_upd_preserve:
  forall O pr t d d0 T C', 
    task_prio_id O pr t ->
    dom_for_prio pr = d ->
    ~flowsTo (TaskDom d) (TaskDom d0) ->
    code_equiv_tskd' d0 T (set T t C') O O. 
Proof.
  introv Htpi Hd Hnfl.
  unfolds.
  introv Hd0 Htpi1 Htpi2.
  assert (t1 = t2).
  { eapply tid_unique; eauto. }
  subst.
  casetac t t2 He Hne.
  -
    subst.
    assert (pr = pr0).
    { eapply prio_unique; eauto. }
    subst.
    false. apply Hnfl. apply flows_to_refl.
  -
    rewrite set_a_get_a'; eauto.
    split; auto.
    introv Hget.
    assert (Hor: not_knl_stmt c \/ ~not_knl_stmt c) by tauto.
    split.
    +
      destruct Hor as [Hnknl | Hknl].
      *
        left; auto.
      *
        right.
        lets H_: knl_hapicode Hknl.
        destruct H_ as (ss & Hc).
        exists ss. split; auto.
        split; intros; auto.
    +
      intros.
      split; auto. 
Qed.

Lemma  local_envs_equiv_same_preserve:
forall i ces O, local_envs_equiv i ces ces O O.
Proof.
unfold local_envs_equiv.
intros.
lets Heq: tid_unique H0 H1.
subst.
auto.
Qed.

Lemma  client_data_equiv_same_preserve:
forall i cst O, client_data_equiv i cst cst O O.
Proof.
unfold client_data_equiv.
intros.
destruct cst as ((ges & ces) & m).
repeat eexists; eauto.
eapply local_envs_equiv_same_preserve.
Qed.

Lemma data_equiv_tskd_same_preserve:
forall i cst O t hp T,
reachable hp T cst O ->
get O curtid = Some (oscurt t) ->
data_equiv_tskd i cst cst O O.
Proof.
unfold data_equiv_tskd.
introv Hrch Hget.
split. eapply ctid_equiv_refl; eauto.
split. apply reachable_get_bufsid in Hrch.
destruct Hrch as (x & y & Hgetx & Hgety).
eapply bufs_equiv_refl; eauto.
split. apply reachable_get_knldataid in Hrch.
simpljoin. eapply kernel_data_equiv_refl; eauto.
eapply client_data_equiv_same_preserve.
Qed.

Require Import spec_aux_defs.

Ltac solve_prim_same :=
match goal with H: _ _ _ _ (_, _) |- _ => unfolds in H; simpljoin end;
try (match goal with H: _ \/ _ |- _ => destruct H; simpljoin end);
try (match goal with H: Some _ = Some _ |- _ => inverts H end);
try (match goal with
         Hj1: join _ ?Of _ , Hj2: join _ ?Of ?O' |- _ =>
                   try eapply map_join_deter with (c' := O') in Hj1; eauto
        end);
subst; tryfalse.

Ltac my_succs_solver_same_absdata :=
match goal with
Hnth: nth_error _ _ = Some _ |- _
=> simpl in Hnth;
    inverts Hnth;
    repeat try re_step_contra;
    try solve [solve_prim_same];
    try solve [tryfalse]
end.


Ltac solve_prim_set_part :=
match goal with H: _ _ _ _ (_, _) |- _ => unfolds in H; simpljoin end;
try (match goal with H: _ \/ _ |- _ => destruct H; simpljoin end);
try (match goal with H: Some _ = Some _ |- _ => inverts H end);
try (let Hj:= fresh in
         match goal with
          | Hj1: join _ ?Of _ , Hj2 : join (set _ _ _) ?Of _ |- _ =>
              lets Hj: OSAbstMod.join_set_l_rev Hj2; destruct Hj as (O_new & Hj & HO_new);
              try eapply map_join_deter with (c' := O_new) in Hj1; eauto;
              subst
        end).

Lemma tid_unique_set_ntls:
forall O O' pr t t' aid abs,
task_prio_id O pr t ->
task_prio_id O' pr t' ->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
t = t'.
Proof.
introv Ht1 Ht2 Heq Hneq.
simpljoin.
lets Ht: tid_unique t Ht2.
unfold task_prio_id in *.
simpljoin.
rewrite set_a_get_a'; eauto.
repeat eexists; eauto.
auto.
Qed.

Lemma prio_unique_set_tls1:
forall O O' pr t' t tls p st m sus op ot,
get O abtcblsid = Some (abstcblist tls) ->
task_prio_id O pr t ->
task_prio_id O' pr t' ->
O' = set O abstcblsid (abstcblist (set tls ot (p,st,m,sus, op))) ->
(ot <> t' ) ->
t = t'.
Proof.
  introv  H0 H2 Hnew'   HO Hp_neq1.
  unfolds in H2.
  unfolds in Hnew'.
  simpljoin.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H2; eauto.
  rewrite H0 in H1; inverts H1.
  eapply tid_unique; eauto.
  unfolds.
  do 5 eexists. eauto.
  unfolds.
  do 5 eexists. eauto. 
Qed.



Lemma prio_unique_set_ntls:
forall O O' pr pr' t aid abs,
task_prio_id O pr t ->
task_prio_id O' pr' t ->
O' = (set O aid abs) ->
(aid <> abstcblsid) ->
pr = pr'.
Proof.
introv Ht1 Ht2 Heq Hneq.
simpljoin.
unfold task_prio_id in Ht1, Ht2.
simpljoin.
rewrite set_a_get_a' in H; eauto.
rewrite H0 in H.
inverts H.
rewrite H1 in H2; inverts H2.
auto.
Qed.

Lemma prio_unique_set_tls:
forall O O' pr pr' t tls p st m sus op ot,
get O abtcblsid = Some (abstcblist tls) ->
task_prio_id O pr t ->
task_prio_id O' pr' t ->
O' = set O abstcblsid (abstcblist (set tls ot (p,st,m,sus, op))) ->
(ot <> t \/ op <> pr') ->
pr = pr'.
Proof.
introv Htls Ht1 Ht2 Heq Hneq.
simpljoin.
unfold task_prio_id in Ht1, Ht2.
simpljoin.
rewrite set_a_get_a in H.
inverts H.
rewrite Htls in H0; inverts H0.
casetac ot t Heq Ht.
subst.
destruct Hneq. tryfalse.
rewrite set_a_get_a in H1; inverts H1.
tryfalse.
rewrite set_a_get_a' in H1; auto.
congruence.
Qed.

(* ____________________________________________yyy *)
Lemma join_get_set_eq:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    join (set O1 a b') O2 O' ->
    O' = set O a b'.
Proof.
  intros.
  assert (join (set O1 a b') O2 (set O a b')).
  {
    clear H2.
    geat.
  }
  eapply map_join_deter; eauto.
Qed.

Lemma join_get_set_eq_2:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b' a' c c',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c -> 
    join (set (set O1 a b') a' c') O2 O' ->
    O' = set (set O a b') a' c'.
Proof.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma join_get_set_eq_3
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' d d',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    join (set ((set (set O1 a b') a' c')) a'' d') O2 O' -> O' = set (set (set O a b') a' c') a'' d'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed. 

Lemma join_get_set_eq_4
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' a''' d d' e e',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    get O1 a''' = Some e ->
    join (set (set ((set (set O1 a b') a' c')) a'' d') a''' e') O2 O' -> O' = set (set (set (set O a b') a' c') a'' d') a''' e'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed. 

Lemma join_get_set_eq_8
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' a''' a4 a5 a6 a7 d d' e e' f f' g g' h h' i i',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    get O1 a''' = Some e ->
    get O1 a4 = Some f ->
    get O1 a5 = Some g ->
    get O1 a6 = Some h ->
    get O1 a7 = Some i ->
    join (set (set (set (set (set (set (set (set O1 a b') a' c') a'' d') a''' e') a4 f') a5 g') a6 h') a7 i') O2 O' ->
   O' = set (set (set (set (set (set (set (set O a b') a' c') a'' d') a''' e') a4 f') a5 g') a6 h') a7 i'.
Proof.
  intros.
  repeat progress(eapply join_set_l_rev in H9; eauto; simpljoin).
  eapply map_join_deter in H0; eauto.
  subst; auto.
Qed.

Lemma task_prio_id_tidneq:
forall O pr1 pr2 t1 t2,
task_prio_id O pr1 t1 ->
task_prio_id O pr2 t2 ->
pr1 <> pr2 ->
t1<> t2.
Proof.
  intros.
  unfolds in H; simpljoin.
  unfolds in H0; simpljoin.
  rewrite H in H0; inverts H0.
  intro.
  subst.
  rewrite H2 in H3; inverts H3; tryfalse.
Qed.


Lemma mq_ref_preserved_self:
forall O,
mq_ref_preserved O O.
Proof.
  intros.
  unfolds.
  intros; simpljoin; repeat eexists; eauto.
  rewrite H in H0; inverts H0.
  eauto.
Qed.

Lemma qprt_preserved_self:
forall O ,
qprt_preserved O O.
Proof.
  intros.
  unfolds.
  intros; simpljoin; repeat eexists; eauto.
  rewrite H in H0; inverts H0.
  eauto.
Qed.

Lemma dom_impl_self:
forall O,
dom_impl O O.
Proof.
  intros.
  unfolds. intros.
  destruct (get O x).
  destruct a; eauto.
  auto.
Qed.

Definition good_api_stmt' s:=
 (exists fid acode ft vl, api_spec fid = Some (acode, ft)
                                           /\  (In s (get_all_succs (acode vl))))
\/ (exists v, s = END v) \/ (s = ABORT).

Ltac destruct_inverts1 H:=
  let Hx:= fresh in
  match type of H with
    | ?H1 \/ ?H2 => destruct H as [Hx | H]; [inverts Hx | destruct_inverts1 H]
    | exists _, _ = _ => let x:= fresh in (destruct H as (x&H);inverts H)
    | _ => idtac
  end.


Lemma qtimedpost_ovf_blk_hold:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_ovf_block_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H10.

assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
                     (abstcblist (set x9 x6
                    (x2, wait (os_stat_postq x) None, x0, x1, x15))))
                    absecblsid (absecblist (set x7 x (absmsgq x11 x12 (x6 :: x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H0.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x8) eqn: eq1; try destruct a;
try solve[ assert(Hr: x8 = absecblsid \/ x8 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x8 = abtcblsid \/ x8 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x8 = absecblsid \/ x8 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x8 = abtcblsid \/ x8 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
  
Qed.


Lemma qtimedpost_timeout_err_hold:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_timeout_err_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x2)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid
              (abstcblist (set x3 x2 (x4, rdy, Vnull, false, x13))))
           absecblsid
           (absecblist
              (set x7 x (absmsgq x11 x10 (remove_tid x2 x9), x12)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H4.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x1) eqn: eq1; try destruct a;
try solve[ assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x1 = abtcblsid \/ x1 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x1 = abtcblsid \/ x1 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

Lemma qpost_exwt_succ_hold:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_exwt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set
(set O abtcblsid
   (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15))))
absecblsid
(absecblist (set x2 x (absmsgq nil x13 x14, remove_tid x6 x4)))).
eapply join_get_set_eq_2;eauto.
clear H2 H3.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x1) eqn: eq1; try destruct a;
try solve[ assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x1 = abtcblsid \/ x1 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x1 = abtcblsid \/ x1 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].


    unfolds; intros.
    rewrite map_get_set' in H1; auto. 
    rewrite map_get_set' in H1; auto. 
    rewrite H0 in H1; inverts H1.
    simpljoin; do 6 eexists; eauto.
    intro; tryfalse.
    intro; tryfalse.
Qed.


Lemma qpost_nowt_succ_hold:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_nowt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
rename H4 into Hltx4.
rename H5 into H4.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set O absecblsid
           (absecblist (set x2 x (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)))).
eapply join_get_set_eq;eauto.
clear H2.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x1) eqn: eq1; try destruct a;
try solve[ assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]].

assert(Hr: x1 = absecblsid \/ x1 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
    rewrite map_get_set' in H1; auto. 
    rewrite H0 in H1; inverts H1.
    simpljoin; do 6 eexists; eauto.
    intro; tryfalse.
Qed.


Lemma asrt_and_ret_hold:
forall i3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (Vint32 i3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.

Lemma ret_val_hold:
forall i3 v2 O'0 O0 Of O O' act,
ret_val (Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.
(*  spec_step_ref_dom_mqsend_hold  *) 

(* qportpost_qref_asrt_preserve *)
Lemma store_msg_ref_dom_hold:
forall v v1 O'0 O0 Of O O' act,
store_msg (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H7.

assert (get O ibufsid = Some (ibufs x9)) as Hib.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hdom.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O osdomainportid
              (osdomainport
                 (set x0 x
                    (x1, x2, x3, SourceP, x4, x5, x6,
                    QueuePort x7 (x8 ++ x11 :: nil))))) ibufsid
           (ibufs (upd_bufmp x9 x10 x8))).
eapply join_get_set_eq_2;eauto.
clear H2 H0.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x12) eqn: eq1; try destruct a;
try solve [assert(Hr: x12 = ibufsid \/ x12 <> ibufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hib in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x12 = osdomainportid \/ x12 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr:x12 = ibufsid \/ x12 <> ibufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hib in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x12 = osdomainportid \/ x12 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

unfolds; intros.

rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite map_get_set in H2.
rewrite Hdom in H0; inverts H0.
inverts H2.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite H1 in H0; inverts H0.

do 7 eexists; 
rewrite map_get_set;eauto.
rewrite map_get_set';eauto.
do 7 eexists; eauto.
Qed.

Lemma q_send_to_domain_hold:
forall v v1 O'0 O0 Of O O' act,
q_send_to_domain (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H16.

assert (get O ibufsid = Some (ibufs x19)) as Hib.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x25)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x23)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O oskportid = Some (oskport x8)) as Hosk.
eapply join_get_get_l;eauto.
assert (get O oschannelid = Some (oschannel x14)) as Hchal.
eapply join_get_get_l;eauto.

assert (O'=set
(set
   (set (set O osdomainportid (osdomainport x27)) abtcblsid
      (abstcblist x26)) absecblsid (absecblist x24)) ibufsid
(ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_4;eauto.
clear H4 H2 H0 H6 H7 H8.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 4 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x28) eqn: eq1; try destruct a;
try solve [assert(Hr: x28 = ibufsid \/ x28 <> ibufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hib in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x28 = absecblsid \/ x28 <> absecblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x28 = abstcblsid \/ x28 <> abstcblsid) by tauto; 
destruct Hr as [He | Hne1]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x28 = osdomainportid \/ x28 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x28 = ibufsid \/ x28 <> ibufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hib in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x28 = absecblsid \/ x28 <> absecblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x28 = abstcblsid \/ x28 <> abstcblsid) by tauto; 
destruct Hr as [He | Hne1]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x28 = osdomainportid \/ x28 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

unfolds; intros.
do 3 rewrite map_get_set' in H2; try intro; tryfalse; auto.


rewrite map_get_set in H2.
rewrite Hosd in H0; inverts H0.
inverts H2.

unfold dpl_upd in H11.
specialize (H11 a).
destruct H11.
simpljoin.
rewrite H4 in H2;inverts H2.
do 7 eexists; eauto.
simpljoin.
rewrite H4.
do 7 eexists; eauto.
Qed.



Lemma  qportpend_block_get_ref_dom_hold:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_get_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H11.

assert (get O curtid = Some (oscurt x16)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x12)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O obufsid = Some (obufs x20)) as Hob.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
           (set (set O abtcblsid (abstcblist (set x12 x16 (x14, rdy, Vnull, x17, x18)))) osdomainportid
              (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11)))) obufsid
           (obufs (upd_bufmp x20 (dom_for_prio x18) (x20 (dom_for_prio x18) ++ x10 :: nil)))).
eapply join_get_set_eq_3;eauto.
clear H3 H2 H0 H5.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 3 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
rename x13 into x22.
destruct (get O x22) eqn: eq1; try destruct a;
try solve[ assert(Hr: x22 = obufsid \/ x22 <> obufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hob in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x22 = osdomainportid \/ x22 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x22 = abstcblsid \/ x22 <> abstcblsid) by tauto; 
destruct Hr as [He | Hne1]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x22 = obufsid \/ x22 <> obufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hob in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x22 = osdomainportid \/ x22 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x22 = abstcblsid \/ x22 <> abstcblsid) by tauto; 
destruct Hr as [He | Hne1]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

unfolds; intros.
rewrite map_get_set' in H2; try intro; tryfalse; auto.
rewrite map_get_set in H2; try intro; tryfalse; auto.
inverts H2.
rewrite Hosd in H0;inverts H0.
simpljoin.

casetac x a Hy Hn.
subst.
rewrite H1 in H0.
inverts H0.
do 7 eexists; rewrite map_get_set ;eauto.

do 7 eexists; rewrite map_get_set' ;eauto.
Qed.


Lemma qportpend_block_ref_dom_hold:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H12.

assert (get O curtid = Some (oscurt x14)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x10)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
              (abstcblist
                 (set x10 x14 (x12, wait (os_stat_port x) x17, x15, x16, x18))))
           absecblsid (absecblist (set x19 x (absport, x14 :: x20)))).
eapply join_get_set_eq_2;eauto.

clear H4 H3 H2 H0.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x11) eqn: eq1; try destruct a;
try solve [assert(Hr: x11 = absecblsid \/ x11 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x11 = abtcblsid \/ x11 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[ rewrite get_set_eq; eauto | 
 rewrite map_get_set'; eauto]];
try solve [assert(Hr: x11 = absecblsid \/ x11 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x11 = abtcblsid \/ x11 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1| rewrite map_get_set'; eauto]];
try solve [assert(Hr: x11 = absecblsid \/ x11 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1| 
rewrite map_get_set'; eauto];
assert(Hr: x11 = abtcblsid \/ x11 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1| rewrite map_get_set'; eauto]].

unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.
Qed. 


Lemma qportpend_block_timeout_ref_dom_hold:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_timeout (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
rename H13 into H12.
inverts H12.

assert (get O curtid = Some (oscurt x15)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x11)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid (abstcblist (set x11 x15 (x13, rdy, Vnull, x17, x18)))) absecblsid
           (absecblist (set x19 x (absport, remove_tid x15 x20)))).
eapply join_get_set_eq_2;eauto.
clear H7 H3 H2 H0.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x12) eqn: eq1; try destruct a;
try solve [ assert(Hr: x12 = absecblsid \/ x12 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x12 = abtcblsid \/ x12 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]].

assert(Hr: x12 = absecblsid \/ x12 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x12 = abtcblsid \/ x12 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

assert(Hr: x12 = absecblsid \/ x12 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x12 = abtcblsid \/ x12 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.
Qed. 

Lemma qportpend_notnil_body_ref_dom_hold:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_notnil_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

kvextH Hosd O0 osdomainportid O.
kvextH Hob O0 obufsid O.

assert (O'=set (set O osdomainportid (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11)))) obufsid
           (obufs (upd_bufmp x13 x15 (x13 x15 ++ x10 :: nil)))).
eapply join_get_set_eq_2;eauto.

clear  H2 H0.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 2 rewrite map_get_set' in H2; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
rename x12 into x21.
destruct (get O x21) eqn: eq1; try destruct a;
try solve [ assert(Hr: x21 = obufsid \/ x21 <> obufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hob in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x21 = osdomainportid \/ x21 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hosd in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]].

assert(Hr: x21 = obufsid \/ x21 <> obufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hob in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x21 = osdomainportid \/ x21 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

assert(Hr: x21 = obufsid \/ x21 <> obufsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hob in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x21 = osdomainportid \/ x21 <> osdomainportid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hosd in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

unfolds; intros.
rewrite map_get_set' in H2; try intro; tryfalse; auto.
rewrite map_get_set in H2.
rewrite Hosd in H0; inverts H0.
inverts H2.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite H1 in H0; inverts H0.

do 7 eexists; 
rewrite map_get_set;eauto.
rewrite map_get_set';eauto.
do 7 eexists; eauto.
Qed. 
(* qportpost_qref_asrt_preserve *)


(* lllllllllllllllllllllllllllllllllll *)

(* spec_step_ref_dom_mqrecv_hold *)

Lemma spec_skip_step_nil_sm_preserve:
forall O0 v2 O'0 Of O O' act,
spec_skip_step nil O0 act (v2, Some O'0) ->
join O0 Of O -> 
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
intros.
inverts H; simpljoin. inverts H.
eapply map_join_deter in H0; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.

Lemma asrt_and_ret_hold1:
forall i3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (Vint32 i3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst.
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.

Lemma asrt_and_ret_hold3:
forall v3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (v3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst.
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.


(* qpend_get_no_pwl_succ_body *)
Lemma qpend_get_no_pwl_succ_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_no_pwl_succ_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
           (absecblist (set x2 x (absmsgq x5 x6 nil, x7)))).
eapply join_get_set_eq;eauto.
(* clear H2. *)
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H5; auto. 
rewrite H4 in H5; inverts H5.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.

 (*dom_impl*)
unfolds. intros.
destruct (get O x0) eqn: eq1; try destruct a;
try solve [assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]]. 
assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
    rewrite map_get_set' in H5; auto. 
    rewrite H4 in H5; inverts H5.
    simpljoin; do 6 eexists; eauto.
     intro; tryfalse.
Qed.

(* qpend_block_get_body *)
Lemma qpend_block_get_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_get_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H6 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (O'=set O abtcblsid
           (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H4; auto. 
rewrite H3 in H4; inverts H4.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x0) eqn: eq1;try destruct a;
try solve [assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Htcb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]]. 
assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
    unfolds; intros.
    rewrite map_get_set' in H4; auto. 
    rewrite H3 in H4; inverts H4.
    simpljoin; do 6 eexists; eauto.
     intro; tryfalse.

Qed.

(* qpend_get_ex_pwl_before_sched_body *)
Lemma qpend_get_ex_pwl_before_sched_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_ex_pwl_before_sched_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x2)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.
assert (O'=set
(set O abtcblsid
   (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15))))
absecblsid
(absecblist
   (set x1 x
      (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
 intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x0) eqn: eq1; try destruct a;
try solve[ assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
 intro; tryfalse.
Qed.

(* qpend_block_body *)
Lemma qpend_block_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

assert (get O curtid = Some (oscurt x11)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x5)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
(abstcblist
   (set x3 x11 (x8, wait (os_stat_q x) x12, x1, x2, x14))))
absecblsid
(absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H4.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x4) eqn: eq1; try destruct a;
try solve[ assert(Hr: x4 = absecblsid \/ x4 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = abtcblsid \/ x4 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x4 = absecblsid \/ x4 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x4 = abtcblsid \/ x4 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

(* qpend_to_body *)
Lemma qpend_to_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_to_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H8 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x3)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist (set x1 x3 (x2, rdy, Vnull, false, x11))))
absecblsid
(absecblist (set x4 x (absmsgq x6 x7 x8, remove_tid x3 x9)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H3.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x0) eqn: eq1; try destruct a;
try solve[ assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].
assert(Hr: x0 = abtcblsid \/ x0 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne']; subst;
 [ rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite map_get_set' in H1; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

(* qpend_assm_stat *)
Lemma qpend_assm_hold:
forall v1 v3 O'0 O0 Of O O' act,
qpend_assm_stat (v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto.
inverts Hj1.
splits; try eapply mq_ref_preserved_self; 
try eapply dom_impl_self
; try eapply qprt_preserved_self; auto.
Qed.
(* qacc_succ_body *)
Lemma qacc_succ_hold:
forall v1 v2 v3 O'0 O0 Of O O' act,
qacc_succ_body  (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid (absecblist (set x1 x (absmsgq x3 x4 x5, x6)))).
eapply join_get_set_eq;eauto.

clear H2.
subst.
splits; eauto.
(*mq_ref_preserved*)
unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.

(*dom_impl*)
unfolds. intros.
destruct (get O x0) eqn: eq1; try destruct a;
try solve [assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]]. 
assert(Hr: x0 = absecblsid \/ x0 <> absecblsid) by tauto; 
destruct Hr as [He | Hne]; subst;
 [ rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto |
    rewrite map_get_set'; eauto ].

    unfolds; intros.
rewrite map_get_set' in H1; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
Qed.

Lemma pro_preserved_self:
forall O ,
prio_preserved O O.
Proof.
  intros.
  unfolds.
  intros. unfolds. intros. 
  split;intros;eauto.
Qed.

Ltac preserved_eq :=
  try solve[splits; try eapply mq_ref_preserved_self ; try eapply dom_impl_self; try eapply qprt_preserved_self;try eapply pro_preserved_self].

Ltac inv_preserved_eq:=
  match goal with
  | H:spec_step _ _ _ _ _ _  |- _=>
inverts H;try solve[split; try eapply mq_ref_preserved_self ;  try eapply dom_impl_self ; try eapply qprt_preserved_self;try eapply pro_preserved_self]
  end.

Ltac preserved_qprt :=
try solve[try eapply qprt_preserved_self].


Lemma spec_step_ref_dom_mqrecv_hold:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
preserved_eq.
preserved_eq.

inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve; eauto.
inverts H6.
preserved_eq.
inverts H2.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2.
inverts H3. simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9. 
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(*n=7*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq;
preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

(*n=8*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.

inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(*n=8*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.

inv_preserved_eq.
preserved_eq.

inv_preserved_eq.
preserved_eq.
preserved_eq.

(*n=9*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
 
  inverts H3; simpljoin.
  destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
  inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
  inverts H3; simpljoin.
  destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
  inverts Ho.
eapply map_join_deter in H14; eauto; subst;
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.

eapply qpend_get_no_pwl_succ_hold;eauto.

inverts H15.
inverts H16.
inverts H16.
inverts H17.
inverts H17.
tryfalse.
inv_preserved_eq.
tryfalse.
preserved_eq.
inverts H2.
inverts H11.
inverts H12.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.

inverts H12.
inverts H13.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

eapply qpend_get_no_pwl_succ_hold;eauto.
preserved_eq.
inverts H16. 
inverts H17.
inverts H6.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
inverts H6.
preserved_eq.
inverts H2.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
preserved_eq.
inverts H17.
inverts H18.
inverts H6.
eapply qpend_block_hold;eauto.
preserved_eq.
inverts H2.
eapply qpend_block_hold;eauto.
preserved_eq.

inverts H18.
tryfalse.
inv_preserved_eq.
tryfalse.

(*n=10*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2. inverts H8.
preserved_eq.

inverts H8.
inverts H3.
preserved_eq.

(*n=11*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H3;simpljoin.
inverts H2.
eapply map_join_deter in H11; eauto; subst;
preserved_eq.
preserved_eq.
inverts H2.
inverts H3;simpljoin.
inverts H2.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.
 
(*n=12*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

(*n=12*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

eapply qpend_assm_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold;eauto.
preserved_eq.

(*n=14*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

(*n=15*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.

(*n=16*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

(*n=17*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

inverts H3.
simpljoin.
inverts H2.
eapply map_join_deter in H12; eauto;subst.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H2.
eapply map_join_deter in H13; eauto;subst.
preserved_eq.
preserved_eq.

(*n=17*)
destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
eapply ret_val_hold;eauto.
preserved_eq.
destruct n; simpl in H0; inverts H0.

Qed.

(* spec_step_ref_dom_mqsend_hold *)
Lemma spec_step_ref_dom_mqsend_hold:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqsend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

simpl in Hnth.
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9.
inverts H11.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H11.
inverts H6. 
eapply spec_skip_step_nil_sm_preserve; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2. 
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H3; simpljoin.
destruct H3 as [(_ & He)|(_ & Hn)]; tryfalse.
inverts He;eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.


destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9.
inverts H6.
eapply spec_skip_step_nil_sm_preserve; eauto.
inverts H6.
preserved_eq.
inverts H2.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9.
inverts H6. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.

preserved_eq.
inverts H2. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve; eauto.
inverts H6.
preserved_eq.
inverts H2.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2.
inverts H3. simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inverts H2.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(*n=7*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inverts H2.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(*n=8*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2; simpljoin;
preserved_eq.

(*n=9*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H10.
eapply asrt_and_ret_hold; eauto.

inverts H10. inverts H11.
eapply asrt_and_ret_hold; eauto.

inverts H11. inverts H12.
eapply asrt_and_ret_hold; eauto.

inverts H12. inverts H13. inverts H13.
inverts H14; tryfalse.
inverts H14. inverts H15. inverts H15.
inverts H16. 

eapply qpost_nowt_succ_hold; eauto.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_exwt_succ_hold; eauto.
preserved_eq.
inv_preserved_eq.
eapply qpost_exwt_succ_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

(*qtimedpost_ovf_block_body*)
eapply qtimedpost_ovf_blk_hold; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2.
eapply qtimedpost_ovf_blk_hold; eauto.
preserved_eq.

inverts H16. inverts H17.
eapply qpost_nowt_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

(*n=10*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2. inverts H8.
preserved_eq.
inverts H8.
inverts H3.
preserved_eq.

(*n=11*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

inverts H2.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

(*n=12*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2. 
inv_preserved_eq.
preserved_eq.
preserved_eq.
inverts H3.
preserved_eq.

(*n=13*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2.
inverts H8. 

(*qtimedpost_after_sched*)
inverts H3; simpljoin.
destruct H6 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

inverts H3; simpljoin.
inverts H2; simpljoin.
destruct H11 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H10.

(*qtimedpost_timeout_err_body*)
eapply qtimedpost_timeout_err_hold; eauto.

inverts H10.
inverts H11.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.

inverts H11; tryfalse.
preserved_eq.
inverts H2.
inverts H11.
eapply qtimedpost_timeout_err_hold; eauto.
preserved_eq.

inverts H11. inverts H12.
inverts H2; simpljoin.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H14; eauto; subst;
preserved_eq.
preserved_eq.

inverts H12; tryfalse.

(*n=15*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H10.
eapply asrt_and_ret_hold; eauto.

inverts H10. inverts H11.
eapply asrt_and_ret_hold; eauto.
inverts H11. inverts H12.
eapply asrt_and_ret_hold; eauto.
inverts H12. inverts H13.
eapply asrt_and_ret_hold; eauto.
inverts H13. inverts H14.

(*qpost_nowt_succ_body*)
eapply qpost_nowt_succ_hold; eauto.

inverts H14. inverts H15.
inverts H15; tryfalse.
preserved_eq.
inverts H2. inverts H11.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

inverts H11. inverts H12.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

inverts H12. inverts H13.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

inverts H13. inverts H14.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

inverts H14. inverts H15.
eapply qpost_nowt_succ_hold; eauto.
preserved_eq.

inverts H15. inverts H16.
inverts H6.
eapply qpost_exwt_succ_hold; eauto.
preserved_eq.

inverts H2.
eapply qpost_exwt_succ_hold; eauto.
preserved_eq.

inverts H16; tryfalse.

(*n=16*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inverts H2. inverts H8.
preserved_eq.
inverts H8. inverts H3.
preserved_eq.

(*n=17*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold; eauto.
preserved_eq.
inverts H2.
eapply asrt_and_ret_hold; eauto.
preserved_eq.

(*n=18*)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9.
inverts H11.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H11.
eapply ret_val_hold; eauto.
preserved_eq.

(*n=19*)
repeat progress (destruct n; simpl in Hnth; inverts Hnth).
Qed.
(* spec_step_ref_dom_mqsend_hold *)

(* qportpost_qref_asrt_preserve *)
Lemma qportpost_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9.
 inv_preserved_eq.
 preserved_eq.
 preserved_eq.
 inv_preserved_eq.
 preserved_eq.
 preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9. inverts H11.
inverts H2. simpljoin. inverts H2.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

inverts H11. inverts H12. eapply ret_val_hold; eauto.
preserved_eq.
inverts H12. inverts H13.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H13. inverts H6. inverts H3.
simpljoin. inverts H.
eapply map_join_deter in H15; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H3. simpljoin.
inverts H.
eapply map_join_deter in H16; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9. inverts H6.
inverts H11. inverts H11. inverts H3. simpljoin. inverts H.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
inverts H6. inverts H11. inverts H3. inverts H11.
inverts H4; simpljoin; tryfalse.
inverts H2. inverts H12.
inverts H6;
preserved_eq.
preserved_eq.
inverts H2; preserved_eq.

inverts H12. inverts H2; simpljoin; tryfalse.
inverts H.
eapply map_join_deter in H14; eauto; subst;
preserved_eq.
inverts H9; simpljoin; tryfalse.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inverts H10.
eapply ret_val_hold; eauto.
inverts H10. inverts H3. simpljoin.
inverts H. 
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H11. eapply ret_val_hold; eauto.
preserved_eq.
inverts H11. inverts H2; simpljoin; tryfalse.
inverts H. 
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.

inverts H6.
eapply q_send_to_domain_hold; eauto.
preserved_eq.
inverts H2.
eapply q_send_to_domain_hold; eauto.
preserved_eq.

inverts H9. inverts H11.
inverts H6.
eapply store_msg_ref_dom_hold; eauto.
preserved_eq.

inverts H2.
eapply store_msg_ref_dom_hold; eauto.
preserved_eq.

inverts H11.
inverts H6.
inverts H12.
preserved_eq.
inverts H12. inverts H3; simpljoin. inverts H.
eapply map_join_deter in H14; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H13.
preserved_eq.
inverts H13. inverts H2; simpljoin.
inverts H.
eapply map_join_deter in H15; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.

inverts H10.
preserved_eq.
inverts H10. inverts H3; simpljoin.
inverts H.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

 inverts H2. inverts H11.
preserved_eq.
inverts H11. inverts H2. simpljoin. inverts H.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

inverts H2.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H6. inverts H10.
preserved_eq.
inverts H10. inverts H3; simpljoin. inverts H.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H11.
preserved_eq.
inverts H11. inverts H2; simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
preserved_eq.
preserved_eq.

rewrite nth_error_nil in H1; tryfalse.
Qed.
(* qportpost_qref_asrt_preserve *)

(* qportpend_qref_asrt_preserve *)
Lemma qportpend_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9.
 inv_preserved_eq.
 preserved_eq.
 preserved_eq.
 inv_preserved_eq.
 preserved_eq.
 preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
preserved_eq.
inverts H9. inverts H11.
inverts H2. simpljoin. inverts H2.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

inverts H11. inverts H12. eapply ret_val_hold; eauto.
preserved_eq.
inverts H12. inverts H13.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H13. inverts H6. inverts H3.
simpljoin. inverts H.
eapply map_join_deter in H15; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2. inverts H3. simpljoin.
inverts H.
eapply map_join_deter in H16; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inverts H9. 
inverts H6.

inverts H11.
inverts H11.
inverts H3.
simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.
inverts H2.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

inverts H2.
preserved_eq.

inverts H12.
inverts H2.
simpljoin.
inverts H.
eapply map_join_deter in H14; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
  inverts H6.
  inv_preserved_eq.
  eapply ret_val_hold; eauto.
inverts H10.
inverts H3.
destruct H0.
inverts H.
eapply map_join_deter in H12; eauto; subst;
preserved_eq.
preserved_eq.

inverts H2.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

inverts H11.
inverts H2.
simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H9.
inverts H6.
eapply qportpend_notnil_body_ref_dom_hold; eauto.
inverts H6.
preserved_eq.
inverts H2.
eapply qportpend_notnil_body_ref_dom_hold; eauto.
preserved_eq.

inverts H9. inverts H6. inverts H11.
preserved_eq.
inverts H11.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inverts H2.
inverts H12.
preserved_eq.
inverts H12.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inverts H6.
inv_preserved_eq.
preserved_eq.
inverts H10.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inverts H2.
inv_preserved_eq.
preserved_eq.
inverts H11.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
eapply qportpend_block_ref_dom_hold; eauto.
preserved_eq.
inverts H2.
eapply qportpend_block_ref_dom_hold; eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H6 ; simpljoin.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inverts H9; simpljoin.
eapply qportpend_block_get_ref_dom_hold; eauto.
preserved_eq.

inverts H9.
eapply qportpend_block_timeout_ref_dom_hold;eauto.
preserved_eq.
rewrite nth_error_nil in H0; tryfalse.
Qed.
(* qportpend_qref_asrt_preserve *)

(* tickisr_spec_ref_dom_hold *)
Lemma tickisr_spec_ref_dom_hold:
forall v1 O'0 O0 Of O O' act,
tickisr_spec nil O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9; simpljoin.
inverts H19.

assert (get O abtcblsid = Some (abstcblist x)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x0)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O ostmid = Some (ostm x1)) as Htm.
eapply join_get_get_l;eauto.
assert (get O ksdomtimeid = Some (ksdomtime x5)) as Hdom.
eapply join_get_get_l;eauto.
assert (get O ksdschedidxid = Some (ksdschedidx x4)) as Hdx.
eapply join_get_get_l;eauto.
assert (get O ksdschedlenid = Some (ksdschedlen x6)) as Hdl.
eapply join_get_get_l;eauto.
assert (get O kscurdomid = Some (kscurdom x7)) as Hcur.
eapply join_get_get_l;eauto.
assert (get O ksdschedid = Some (ksdsched x9)) as Hsd.
eapply join_get_get_l;eauto.
assert(get O kslastdomid = Some (kslastdom x8)) as Hksl.
eapply join_get_get_l;eauto.

assert (O'=set (set (set (set (set (set
                          (set (set O absecblsid (absecblist x3)) abtcblsid
                             (abstcblist x2)) ostmid 
                          (ostm (x1 +ᵢ  Int.one))) ksdomtimeid
                       (ksdomtime (x5 -ᵢ Int.one))) ksdschedidxid
                    (ksdschedidx
                       (if Int.ltu (x4 +ᵢ  Int.one) x6
                        then x4 +ᵢ  Int.one
                        else Int.zero))) kslastdomid 
                 (kslastdom x7)) kscurdomid (kscurdom x12)) ksdomtimeid
           (ksdomtime x13)).
eapply join_get_set_eq_8;eauto.

clear H2 H1 H0 H3 H5 H6 H7 H8 H9.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 8 rewrite map_get_set' in H1; try intro; tryfalse; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x10) eqn: eq1; try destruct a;
try solve [ assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]].

assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].


assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kscurdomid \/ x10 <> kscurdomid) by tauto; 
destruct Hr as [He | Hne']; subst;
[rewrite Hcur in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = kslastdomid \/ x10 <> kslastdomid) by tauto; 
destruct Hr as [He | Hne2]; subst;
[rewrite Hksl in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdschedidxid \/ x10 <> ksdschedidxid) by tauto; 
destruct Hr as [He | Hne3]; subst;
[rewrite Hdx in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].
assert(Hr: x10 = ksdomtimeid \/ x10 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne4]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = ostmid \/ x10 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = abtcblsid \/ x10 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x10 = absecblsid \/ x10 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto].

unfolds; intros.
do 8 rewrite map_get_set' in H1; try intro; tryfalse; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.

inverts H3.

assert (get O abtcblsid = Some (abstcblist x)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x0)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O ostmid = Some (ostm x1)) as Htm.
eapply join_get_get_l;eauto.
assert (get O ksdomtimeid = Some (ksdomtime x5)) as Hdom.
eapply join_get_get_l;eauto.

assert (O'=set (set
              (set (set O absecblsid (absecblist x3)) abtcblsid
                 (abstcblist x2)) ostmid (ostm (x1 +ᵢ  Int.one))) ksdomtimeid
           (ksdomtime (x5 -ᵢ Int.one))).
eapply join_get_set_eq_4;eauto.

clear H2 H1 H0 H5.
subst.
splits; eauto.

(*mq_ref_preserved*)
unfolds; intros.
do 4 rewrite map_get_set' in H1; try intro; tryfalse; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.

(*dom_impl*)
unfolds. intros.
destruct (get O x4) eqn: eq1; try destruct a;
try solve [assert(Hr: x4 = ksdomtimeid \/ x4 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = ostmid \/ x4 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = abtcblsid \/ x4 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = absecblsid \/ x4 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto]];

try solve [assert(Hr: x4 = ksdomtimeid \/ x4 <> ksdomtimeid) by tauto; 
destruct Hr as [He | Hne]; subst;
[rewrite Hdom in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = ostmid \/ x4 <> ostmid) by tauto; 
destruct Hr as [He | Hne5]; subst;
[rewrite Htm in eq1; inverts eq1; rewrite get_set_eq; eauto | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = abtcblsid \/ x4 <> abtcblsid) by tauto; 
destruct Hr as [He | Hne6]; subst;
[rewrite Htcb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto];
assert(Hr: x4 = absecblsid \/ x4 <> absecblsid) by tauto; 
destruct Hr as [He | Hne7]; subst;
[rewrite Hecb in eq1; inverts eq1 | 
rewrite map_get_set'; eauto]].

unfolds; intros.
do 4 rewrite map_get_set' in H1; try intro; tryfalse; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
Qed. 

Lemma mqrecv_get_msgsize_hold:
forall i i2 v3 O'0 O0 Of O O' act,
mqrecv_get_msgsize (Vint32 i :: Vint32 i2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma mqrecv_get_ecb_ptr_hold:
forall i v1 v3 O'0 O0 Of O O' act,
mqrecv_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma mqrecv_get_mqflags_hold:
forall i v1 v3 O'0 O0 Of O O' act,
mqrecv_get_mqflags (Vint32 i :: Vint32 v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma ret_val_hold2':
forall v3 v2 O'0 O0 Of O O' act,
ret_val (v3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.

Lemma memcpy_empty_hold2:
forall v i0 v3 v2 O'0 O0 Of O O' act,
memcpy_empty (v :: v2 :: Vint32 i0 :: nil) O0 act  (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.

Lemma spec_step_ref_dom_mqtmrecv_hold:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1;destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(* 2 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_msgsize_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_msgsize_hold;eauto.
preserved_eq.
(* 3 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(* 4 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_ecb_ptr_hold; eauto.
preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_ecb_ptr_hold; eauto.
preserved_eq.

(* 5 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(* 6 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_mqflags_hold; eauto.
preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_mqflags_hold; eauto.
preserved_eq.

(* 7 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve; eauto.
preserved_eq.

(* 8 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.

(* 9 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold;eauto.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
tryfalse.

(* 10 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

(* 11 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold2';eauto.
preserved_eq.
inv_preserved_eq.
eapply ret_val_hold2';eauto.
preserved_eq.

(* 12 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

(* 13 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold;eauto.
preserved_eq.

(* 14 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

(* 15 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.

(* 16 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

(* 17 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply memcpy_empty_hold2;eauto.
preserved_eq.
inv_preserved_eq.
eapply memcpy_empty_hold2;eauto.
preserved_eq.

(* 18 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
eapply ret_val_hold;eauto.
preserved_eq.

(*n=19*)
repeat progress (destruct n; simpl in Hnth; inverts Hnth).
Qed. 


Lemma buffer_post_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_nowt_succ_hold;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_nowt_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_exwt_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpost_exwt_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold1;eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma buffer_accept_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold2'; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma buffer_pend_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

  destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold2'; eauto.
preserved_eq.
inv_preserved_eq.
eapply ret_val_hold2'; eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
preserved_eq.
inv_preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold;eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
inv_preserved_eq.
tryfalse.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold;eauto.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold;eauto.
preserved_eq.
inv_preserved_eq.
tryfalse.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold3;eauto.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
eapply ret_val_hold2'; eauto.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma sample_portpost_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

  destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

  destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].


(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst O.
preserved_eq.
preserved_eq.
inverts H9.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H9.
inverts H11.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H11.
inverts H12.
inverts H2.
simpljoin.
inverts H4.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H12.
inverts H13.
inverts H2.
simpljoin.
inverts H4.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H13.
inverts H6.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.


destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H9.
inverts H6.
inverts H11.
inverts H11.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H12.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
inverts H12.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
inverts H10.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H11.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H11.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H16.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm2.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
unfolds.
intros.
eapply join_get_get_l in H0;eauto.
eapply join_get_get_l in H7;eauto.
destruct (get O x24) eqn: eq1. 

match goal with H: get O osdomainportid = _ |-_=> rename H into Hosdomainportid end. 
lets Hosdomainportid_: Hosdomainportid.

match goal with H: get O ibufsid = _ |-_=> rename H into Hibufsid end. 
lets Hibufsid_: Hibufsid.

destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x24;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hibufsid_ in eq1;tryfalse. 

destruct x24;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hosdomainportid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.

try repeat (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

unfolds.
introv Hos1 Hos2 Hdpl.
unfolds in H13.
specialize(H13 a).
destruct H13.
simpljoin.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite H13 in H16. inverts H16.
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
inverts H15.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
rewrite H16.
do 7 eexists. eauto.
introv Hfa;tryfalse.

preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H17.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm2.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
unfolds.
intros.
eapply join_get_get_l in H0;eauto.
eapply join_get_get_l in H9;eauto.
destruct (get O x24) eqn: eq1. 

match goal with H: get O osdomainportid = _ |-_=> rename H into Hosdomainportid end. 
lets Hosdomainportid_: Hosdomainportid.

match goal with H: get O ibufsid = _ |-_=> rename H into Hibufsid end. 
lets Hibufsid_: Hibufsid.

destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x24;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hibufsid_ in eq1;tryfalse. 

destruct x24;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hosdomainportid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.

try repeat (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

unfolds.
introv Hos1 Hos2 Hdpl.
unfolds in H14.
specialize(H14 a).
destruct H14.
simpljoin.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite H14 in H17. inverts H17.
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
inverts H16.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
rewrite H17.
do 7 eexists. eauto.
introv Hfa;tryfalse.

preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma port_accept_qref_asrt_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (portaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
introv Hnth Hstep.

destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

  destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

  destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst O.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H9.
inverts H11.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H11.
inverts H12.
inverts H2.
simpljoin.
inverts H4.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H12.
inverts H6.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H9.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H9.
inverts H6.
inverts H11.
inverts H11.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H12.
inverts H6.
preserved_eq.
preserved_eq.
inverts H2.
preserved_eq.
inverts H12.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
inverts H10.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H2.
inverts H11.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inverts H11.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H9.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm2.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
unfolds.
intros.
eapply join_get_get_l in H0;eauto.
eapply join_get_get_l in H1;eauto.
destruct (get O x12) eqn: eq1. 

match goal with H: get O osdomainportid = _ |-_=> rename H into Hosdomainportid end. 
lets Hosdomainportid_: Hosdomainportid.

match goal with H: get O obufsid = _ |-_=> rename H into Hobufsid end. 
lets Hobufsid_: Hobufsid.

destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x12;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hobufsid_ in eq1;tryfalse. 

destruct x12;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hosdomainportid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.

try repeat (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

unfolds.
introv Hos1 Hos2 Hdpl.
destruct H3.
simpljoin.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
casetac x a Hte Htne.
subst a. rewrite set_a_get_a.
rewrite H7 in H2. inverts H2.
do 7 eexists. eauto.
rewrite set_a_get_a';[idtac|introv Hfa;tryfalse].
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
do 7 eexists. eauto.
introv Hfa;tryfalse.

preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H10.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm2.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
unfolds.
intros.
eapply join_get_get_l in H0;eauto.
eapply join_get_get_l in H1;eauto.
destruct (get O x12) eqn: eq1. 

match goal with H: get O osdomainportid = _ |-_=> rename H into Hosdomainportid end. 
lets Hosdomainportid_: Hosdomainportid.

match goal with H: get O obufsid = _ |-_=> rename H into Hobufsid end. 
lets Hobufsid_: Hobufsid.

destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x12;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hobufsid_ in eq1;tryfalse. 

destruct x12;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hosdomainportid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.

try repeat (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

unfolds.
introv Hos1 Hos2 Hdpl.
destruct H3.
simpljoin.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
casetac x a Hte Htne.
subst a. rewrite set_a_get_a.
rewrite H9 in H2. inverts H2.
do 7 eexists. eauto.
rewrite set_a_get_a';[idtac|introv Hfa;tryfalse].
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
eapply join_get_get_l in H0;eauto.
rewrite Hos1 in H0. inverts H0.
rewrite set_a_get_a' in Hos2.
rewrite set_a_get_a in Hos2.
inverts Hos2.
do 7 eexists. eauto.
introv Hfa;tryfalse.

preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O=O').
eapply join_unique;eauto.
subst.
preserved_eq.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma spec_step_ref_dom_hold:
forall cd cd' O O' sd act ,
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O O' /\ dom_impl O O' /\ qprt_preserved O O'.
Proof.
intros.
unfolds in H.
destruct H as [Hapis | [ Hend | Habt]]; simpljoin; subst; simpl; auto.
(*apispec*)
unfolds in H; simpl in H.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqsend_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqrecv_hold; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqtmrecv_hold;eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpost_qref_asrt_preserve; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpend_qref_asrt_preserve; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X.
inverts H. 
eapply In_nth_error in H1; simpljoin.
eapply sample_portpost_qref_asrt_preserve; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply port_accept_qref_asrt_preserve; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply buffer_post_qref_asrt_preserve; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply buffer_accept_qref_asrt_preserve; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply buffer_pend_qref_asrt_preserve; eauto.
tryfalse.

inverts H0.
inverts H0.

Qed.


(* Lemma spec_step_ref_dom_hold2:
forall cd cd' O O' sd act ,
good_api_stmt cd ->
spec_step sd cd O cd' O' act ->
qprt_preserved O O' /\ dom_impl O O'.
Proof.
intros.
unfolds in H.
destruct H as [Hapis | [ Hints | [ Hend | Habt]]]; simpljoin; subst; simpl; auto.
(*apispec*)
unfolds in H; simpl in H.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqsend_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqrecv_hold; eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpost_qref_asrt_preserve; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpend_qref_asrt_preserve; eauto.

tryfalse.

(*int_spec*)
unfolds in H.
unfolds in H; simpl in H.
repeat progress (destruct x; tryfalse).
inverts H.
simpl in H1.
destruct_inverts1 H1. 
inverts H0. inverts H8.
eapply tickisr_spec_ref_dom_hold; eauto.
preserved_eq.
invert H4; intros.
eapply tickisr_spec_ref_dom_hold; eauto.
preserved_eq.
inverts H0.
inverts H8;
preserved_eq.
preserved_eq.
inverts H4; preserved_eq.

inverts H0.
inverts H4; simpljoin.
inverts H;  eapply map_join_deter in H12; eauto; subst; auto.
preserved_eq.
preserved_eq.
tryfalse.
inverts H0.
inverts H0.
Qed. *)




Lemma dom_impl_comm:
forall O' O,
dom_impl O O' <-> dom_impl O' O.
Proof. 
unfold dom_impl.
intros.
split.
intros.
specialize( H x).
destruct (get O x) eqn : eq1;tryfalse.
destruct a; simpljoin;rewrite H ;eauto.
rewrite H;eauto.

intros.
specialize( H x).
destruct (get O' x) eqn : eq1;tryfalse.
destruct a; simpljoin;rewrite H ;eauto.
rewrite H;eauto.
Qed.

Lemma ret_val_hold1:
forall i3 v2 O'0 O0 Of O O' act,
ret_val (Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
Qed.

Lemma spec_skip_step_nil_sm_preserve1:
forall O0 v2 O'0 Of O O' act,
spec_skip_step nil O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
intros.
inverts H; simpljoin. inverts H.
eapply map_join_deter in H2; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
Qed.

(* qpend_get_no_pwl_succ_body *)
Lemma qpend_get_no_pwl_succ_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_no_pwl_succ_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
           (absecblist (set x2 x (absmsgq x5 x6 nil, x7)))).
eapply join_get_set_eq;eauto.
(* clear H2. *)
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H4; auto. 
rewrite H4 in H5; inverts H5.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.

 rewrite map_get_set' in H4; auto. 
rewrite H4 in H5; inverts H5.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
Qed.

(* qpend_block_get_body *)
Lemma qpend_block_get_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_get_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H6 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (O'=set O abtcblsid
           (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto.
subst.
(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H3; auto. 
rewrite H3 in H4; inverts H4.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
 rewrite map_get_set' in H3; auto. 
rewrite H3 in H4; inverts H4.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
Qed.

(* qpend_get_ex_pwl_before_sched_body *)
Lemma qpend_get_ex_pwl_before_sched_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_ex_pwl_before_sched_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x2)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.
assert (O'=set
(set O abtcblsid
   (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15))))
absecblsid
(absecblist
   (set x1 x
      (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1.
subst.
(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
 intro; tryfalse.
 rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
 intro; tryfalse.
 intro; tryfalse.
Qed.

(* qpend_block_body *)
Lemma qpend_block_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

assert (get O curtid = Some (oscurt x11)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x5)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
(abstcblist
   (set x3 x11 (x8, wait (os_stat_q x) x12, x1, x2, x14))))
absecblsid
(absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H4.
subst.
(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.

Qed.

(* qpend_to_body *)
Lemma qpend_to_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_to_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H8 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x3)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist (set x1 x3 (x2, rdy, Vnull, false, x11))))
absecblsid
(absecblist (set x4 x (absmsgq x6 x7 x8, remove_tid x3 x9)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H3.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

(* qpend_assm_stat *)
Lemma qpend_assm_hold1:
forall v1 v3 O'0 O0 Of O O' act,
qpend_assm_stat (v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto.
inverts Hj1.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
Qed.

(* qacc_succ_body *)
Lemma qacc_succ_hold1:
forall v1 v2 v3 O'0 O0 Of O O' act,
qacc_succ_body  (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid (absecblist (set x1 x (absmsgq x3 x4 x5, x6)))).
eapply join_get_set_eq;eauto.

clear H2.
subst.
(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
Qed.


Lemma qtimedpost_ovf_blk_hold1:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_ovf_block_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H10.

assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
                     (abstcblist (set x9 x6
                    (x2, wait (os_stat_postq x) None, x0, x1, x15))))
                    absecblsid (absecblist (set x7 x (absmsgq x11 x12 (x6 :: x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H0.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

Lemma qtimedpost_timeout_err_hold1:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_timeout_err_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x2)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid
              (abstcblist (set x3 x2 (x4, rdy, Vnull, false, x13))))
           absecblsid
           (absecblist
              (set x7 x (absmsgq x11 x10 (remove_tid x2 x9), x12)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H4.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto.
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.


Lemma qpost_nowt_succ_hold1:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_nowt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set O absecblsid
           (absecblist (set x2 x (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)))).
eapply join_get_set_eq;eauto.
clear H2.
subst.
(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
Qed.

Lemma qpost_exwt_succ_hold1:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_exwt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set
(set O abtcblsid
   (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15))))
absecblsid
(absecblist
   (set x2 x (absmsgq nil x13 x14, remove_tid x6 x4)))).
eapply join_get_set_eq_2;eauto.
clear H2 H3.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
rewrite map_get_set' in H0; auto. 
rewrite map_get_set' in H0; auto. 
rewrite H0 in H1; inverts H1.
simpljoin; do 6 eexists; eauto.
intro; tryfalse.
intro; tryfalse.
Qed.

Lemma asrt_and_ret_hold4:
forall v3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (v3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;
try solve[split; try eapply qprt_preserved_self; try eapply mq_ref_preserved_self;auto].
Qed.

Lemma spec_step_ref_dom_mqrecv_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
simpl in Hnth.
destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H11.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11.
inverts H6. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H3; simpljoin.
destruct H3 as [(_ & He)|(_ & Hn)]; tryfalse.
inverts He;eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H9; simpljoin.
destruct H3 as [(_ & He)|(_ & Hn)]; tryfalse.

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H6. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
inverts H3. simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. 
inverts H11.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11.
inverts H6. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=7*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H2; simpljoin;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=8*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H11;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  
inverts H3; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H12;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H14; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H12;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H13;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H13;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H14;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H14.
inverts H15. 
eapply qpend_get_no_pwl_succ_hold1;eauto.
inverts H15.
inverts H16.
inverts H16.
inverts H17.
inverts H17.
tryfalse.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold1;eauto.
inv_preserved_eq.
eapply qpend_block_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.

(*n=9*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H8.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8.
inverts H3.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=10*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H3;simpljoin.
  inverts H2.
  eapply map_join_deter in H11; eauto; subst;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H2.
  inverts H3;simpljoin.
  inverts H2.
  eapply map_join_deter in H12; eauto; subst;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
 
(*n=11*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=12*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inv_preserved_eq.
inv_preserved_eq.

eapply qpend_assm_hold1;eauto.
inv_preserved_eq.
eapply qpend_assm_hold1;eauto.

(*n=13*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold1;eauto.
inv_preserved_eq.
eapply qpend_to_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold1;eauto.
inv_preserved_eq.

(*n=14*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.

(* 15 *)
destruct n.
simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold1;eauto.
inv_preserved_eq.

(*n=15*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
 
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. 
inverts H6. 

inverts H3;simpljoin. 
inverts H2.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
inverts H3;simpljoin. 
inverts H2.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
(*n=16*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

(*n=17*)
destruct n; simpl in Hnth; inverts Hnth.
Qed.

Lemma asrt_and_ret_hold2:
forall i3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (Vint32 i3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O .
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;
try solve[split; try eapply qprt_preserved_self; try eapply mq_ref_preserved_self;auto].
Qed.

Lemma spec_step_ref_dom_mqsend_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqsend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.

(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

simpl in Hnth.
destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H11.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11.
inverts H6. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2. 
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H3; simpljoin.
destruct H3 as [(_ & He)|(_ & Hn)]; tryfalse.
inverts He;eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H9; simpljoin.
destruct H3 as [(_ & He)|(_ & Hn)]; tryfalse.

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9.
inverts H6. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
inverts H6.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H11; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
inverts H3. simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
(*n=7*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.

inverts H9. inverts H6.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply spec_skip_step_nil_sm_preserve1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
(*n=8*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2; simpljoin;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=9*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10.
eapply asrt_and_ret_hold2; eauto.

inverts H10. inverts H11.
eapply asrt_and_ret_hold2; eauto.

inverts H11. inverts H12.
eapply asrt_and_ret_hold2; eauto.

inverts H12. inverts H13. inverts H13.
inverts H14; tryfalse.
inverts H14. inverts H15. inverts H15.
inverts H16. 
eapply qpost_nowt_succ_hold1; eauto.

inverts H16; tryfalse.
inverts H2. inverts H11.
eapply asrt_and_ret_hold2; eauto.
inverts H8; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.

inverts H11. inverts H12.
eapply asrt_and_ret_hold2; eauto.
inverts H8; simpljoin.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H12. inverts H13.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H13.
inverts H14.
inverts H6.

eapply qpost_exwt_succ_hold1; eauto.
inverts H6. 
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
eapply qpost_exwt_succ_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H14. inverts H15; tryfalse.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H15. inverts H16.
inverts H6.

(*qtimedpost_ovf_block_body*)
eapply qtimedpost_ovf_blk_hold1; eauto.
inverts H6. inverts H4; simpljoin; tryfalse.
inverts H2.
eapply qtimedpost_ovf_blk_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H16. inverts H17.

(*qtimedpost_nowt_succ_body*)
eapply qpost_nowt_succ_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H17; tryfalse.

(*n=10*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H8.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8.
inverts H3.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
(*n=11*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply asrt_and_ret_hold2; eauto.

inverts H2.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=12*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H8; 
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H3.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=13*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
inverts H8. 

(*qtimedpost_after_sched*)
inverts H3; simpljoin.
destruct H6 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H3; simpljoin.
inverts H2; simpljoin.
destruct H11 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10.

(*qtimedpost_timeout_err_body*)
eapply qtimedpost_timeout_err_hold1; eauto.

inverts H10.
inverts H11.
inverts H3; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11; tryfalse.
inverts H2.
inverts H11.
eapply qtimedpost_timeout_err_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11. inverts H12.
inverts H2; simpljoin.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H14; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H12; tryfalse.

(*n=15*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10.
eapply asrt_and_ret_hold2; eauto.

inverts H10. inverts H11.
eapply asrt_and_ret_hold2; eauto.
inverts H11. inverts H12.
eapply asrt_and_ret_hold2; eauto.
inverts H12. inverts H13.
eapply asrt_and_ret_hold2; eauto.
inverts H13. inverts H14.

(*qpost_nowt_succ_body*)
eapply qpost_nowt_succ_hold1; eauto.
inverts H14. inverts H15.
inverts H15; tryfalse.
inverts H2. inverts H11.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11. inverts H12.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H12. inverts H13.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H13. inverts H14.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H14. inverts H15.
eapply qpost_nowt_succ_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H15. inverts H16.
inverts H6.
eapply qpost_exwt_succ_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
eapply qpost_exwt_succ_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H16; tryfalse.

(*n=16*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2. inverts H8.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8. inverts H3.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=17*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply asrt_and_ret_hold2; eauto.
inverts H2.
eapply asrt_and_ret_hold2; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=18*)
destruct n.
simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.
inverts H9.
inverts H11.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

(*n=19*)
repeat progress (destruct n; simpl in Hnth; inverts Hnth).
Qed.

Lemma q_send_to_domain_hold1:
forall v v1 O'0 O0 Of O O' act,
q_send_to_domain (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H16.

assert (get O ibufsid = Some (ibufs x19)) as Hib.
eapply join_get_get_l;eauto.

assert (get O abtcblsid = Some (abstcblist x25)) as Htcb.
eapply join_get_get_l;eauto.

assert (get O absecblsid = Some (absecblist x23)) as Hecb.
eapply join_get_get_l;eauto.

assert (get O osdomainportid = Some (osdomainport x0)) as Hosd.
eapply join_get_get_l;eauto.

assert (get O oskportid = Some (oskport x8)) as Hosk.
eapply join_get_get_l;eauto.

assert (get O oschannelid = Some (oschannel x14)) as Hchal.
eapply join_get_get_l;eauto.


assert (O'=set
(set
   (set (set O osdomainportid (osdomainport x27)) abtcblsid
      (abstcblist x26)) absecblsid (absecblist x24)) ibufsid
(ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_4;eauto.
clear H4 H2 H0 H6 H7 H8.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 4 rewrite map_get_set' in H0; try intro; tryfalse; auto.
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

do 3 rewrite map_get_set' in H0; try intro; tryfalse; auto.
rewrite map_get_set in H0; inverts H0.
rewrite Hosd in H2; inverts H2.
simpljoin.

unfold dpl_upd in H11.
specialize (H11 a).
destruct H11.
simpljoin.
rewrite H6 in H0;inverts H0.
do 7 eexists; eauto.
simpljoin.
rewrite H4 in H0.
do 7 eexists; eauto.
Qed.

Lemma store_msg_ref_dom_hold1:
forall v v1 O'0 O0 Of O O' act,
store_msg (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H7.

assert (get O ibufsid = Some (ibufs x9)) as Hib.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hdom.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O osdomainportid
              (osdomainport
                 (set x0 x
                    (x1, x2, x3, SourceP, x4, x5, x6,
                    QueuePort x7 (x8 ++ x11 :: nil))))) ibufsid
           (ibufs (upd_bufmp x9 x10 x8))).
eapply join_get_set_eq_2;eauto.
clear H2 H0.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite map_get_set in H0.
rewrite Hdom in H2; inverts H2.
inverts H0.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite map_get_set in H0.
inverts H0.
do 7 eexists; eauto.
rewrite map_get_set' in H0;eauto.
do 7 eexists; eauto.
Qed.


Lemma qportpost_qref_asrt_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
inverts H6; try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2; 
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.
inverts H9. inverts H11.
inverts H2. simpljoin. inverts H2.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11. inverts H12. 
eapply ret_val_hold1 ; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H12. inverts H13.
eapply ret_val_hold1 ; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H13. inverts H6. inverts H3.
simpljoin. inverts H.
eapply map_join_deter in H15; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H3. simpljoin.
inverts H.
eapply map_join_deter in H16; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
eapply ret_val_hold1; eauto.
inverts H9. inverts H6.
inverts H11. inverts H11. inverts H3. simpljoin. inverts H.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6. inverts H11. inverts H3. inverts H11.
inverts H4; simpljoin; tryfalse.
inverts H2. inverts H12.
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2; try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H12. inverts H2; simpljoin; tryfalse.
inverts H.
eapply map_join_deter in H14; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9; simpljoin; tryfalse.

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10.
eapply ret_val_hold1; eauto.
inverts H10. inverts H3. simpljoin.
inverts H. 
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H11. 
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H11. inverts H2; simpljoin; tryfalse.
inverts H. 
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H6.
eapply q_send_to_domain_hold1; eauto.
inverts H2.
eapply q_send_to_domain_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H9. inverts H11.
inverts H6.
eapply store_msg_ref_dom_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
eapply store_msg_ref_dom_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11.
inverts H6.
inverts H12.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H12. inverts H3; simpljoin. inverts H.
eapply map_join_deter in H14; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H13.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H13. inverts H2; simpljoin.
inverts H.
eapply map_join_deter in H15; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H10.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10. inverts H3; simpljoin.
inverts H.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H11.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H11. inverts H2. simpljoin. inverts H.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6. inverts H10.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H10. inverts H3; simpljoin. inverts H.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H11.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H11. inverts H2; simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H8; simpljoin; tryfalse.

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2; simpljoin. inverts H2.
eapply map_join_deter in H10; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

rewrite nth_error_nil in H1; tryfalse.
Qed.



Lemma qportpend_notnil_body_ref_dom_hold1:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_notnil_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

assert (get O obufsid = Some (obufs x13)) as Hob.
eapply join_get_get_l;eauto.

assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set O osdomainportid
   (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid (obufs (upd_bufmp x13 x15 (x13 x15 ++ x10 :: nil)))).
eapply join_get_set_eq_2;eauto.

clear H2 H0.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite map_get_set in H0.
rewrite Hosd in H2; inverts H2.
inverts H0.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite map_get_set in H0.
inverts H0.
do 7 eexists; eauto.
rewrite map_get_set' in H0;eauto.
do 7 eexists; eauto.
Qed.

Lemma  qportpend_block_get_ref_dom_hold1:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_get_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H11.

assert (get O curtid = Some (oscurt x16)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x12)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O obufsid = Some (obufs x20)) as Hob.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set (set O abtcblsid (abstcblist (set x12 x16 (x14, rdy, Vnull, x17, x18))))
   osdomainportid
   (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid
(obufs (upd_bufmp x20 (dom_for_prio x18) (x20 (dom_for_prio x18) ++ x10 :: nil)))).
eapply join_get_set_eq_3;eauto.
clear H3 H2 H0 H5.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 3 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite map_get_set in H0.

rewrite Hosd in H2; inverts H2.
inverts H0.
simpljoin.
casetac x a Hy Hn.
subst.
rewrite map_get_set in H0.
inverts H0.
do 7 eexists; eauto.
rewrite map_get_set' in H0;eauto.
do 7 eexists; eauto.
Qed.

Lemma qportpend_block_timeout_ref_dom_hold1:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_timeout (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
rename H13 into H12.
inverts H12.

assert (get O curtid = Some (oscurt x15)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x11)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid (abstcblist (set x11 x15 (x13, rdy, Vnull, x17, x18))))
absecblsid (absecblist (set x19 x (absport, remove_tid x15 x20)))).
eapply join_get_set_eq_2;eauto.
clear H7 H3 H2 H0.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.
Qed.

Lemma qportpend_block_ref_dom_hold1:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H12.

assert (get O curtid = Some (oscurt x14)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x10)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist
      (set x10 x14 (x12, wait (os_stat_port x) x17, x15, x16, x18))))
absecblsid (absecblist (set x19 x (absport, x14 :: x20)))).
eapply join_get_set_eq_2;eauto.

clear H4 H3 H2 H0.
subst.

(*mq_ref_preserved*)
split;unfolds; intros.
do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.

do 2 rewrite map_get_set' in H0; try intro; tryfalse; auto. 
rewrite H0 in H2; inverts H2.
simpljoin; do 6 eexists; eauto.
Qed.


Lemma qportpend_qref_asrt_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2; 
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self];
eapply ret_val_hold1; eauto.
inverts H9. inverts H11.
inverts H2. simpljoin. inverts H2.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H11. inverts H12. eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H12. inverts H13.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H13. inverts H6. inverts H3.
simpljoin. inverts H.
eapply map_join_deter in H15; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2. inverts H3. simpljoin.
inverts H.
eapply map_join_deter in H16; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self];
eapply ret_val_hold1; eauto.
inverts H9.

inverts H6.

inverts H11.
inverts H11.
inverts H3.
simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self] .

split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self.
inverts H2.
inverts H12;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H6;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H12.
inverts H2.
simpljoin.
inverts H.
eapply map_join_deter in H14; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H6.
  inverts H10;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self];
  eapply ret_val_hold1; eauto.
inverts H10.
inverts H3.
destruct H0.
inverts H.
eapply map_join_deter in H12; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H2.
inverts H11;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self];
eapply ret_val_hold1; eauto.

inverts H11.
inverts H2.
simpljoin.
inverts H.
eapply map_join_deter in H13; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H9.
  inverts H6.
  eapply qportpend_notnil_body_ref_dom_hold1; eauto.
  inverts H6.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H2.
  eapply qportpend_notnil_body_ref_dom_hold1; eauto.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  
  inverts H9. inverts H6.
  inverts H11.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H11.
  eapply spec_skip_step_nil_sm_preserve1; eauto.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H2.
  inverts H12.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H12.
  eapply spec_skip_step_nil_sm_preserve1; eauto.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
 
  destruct n; simpl in H1; inverts H1.
  inverts Hstep;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H6.

  inverts H10;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H10.
  eapply spec_skip_step_nil_sm_preserve1; eauto.
  inverts H2.
  inverts H11;
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
  inverts H11.
  eapply spec_skip_step_nil_sm_preserve1; eauto.
  try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self];
eapply ret_val_hold1; eauto.

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6.

eapply qportpend_block_ref_dom_hold1; eauto.
inverts H2.
eapply qportpend_block_ref_dom_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].


destruct n; simpl in H0; inverts H0.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H6.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H2.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

destruct n; simpl in H1; inverts H1.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
eapply qportpend_block_get_ref_dom_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].

inverts H9.
eapply qportpend_block_timeout_ref_dom_hold1;eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
rewrite nth_error_nil in H0; tryfalse.
Qed.

Lemma mqrecv_get_msgsize_hold1:
forall i i2 v3 O'0 O0 Of O O' act,
mqrecv_get_msgsize (Vint32 i :: Vint32 i2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma mqrecv_get_ecb_ptr_hold1:
forall i v1 v3 O'0 O0 Of O O' act,
mqrecv_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma mqrecv_get_mqflags_hold1:
forall i v1 v3 O'0 O0 Of O O' act,
mqrecv_get_mqflags (Vint32 i :: Vint32 v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H3 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

eapply map_join_deter in Hj1; eauto; subst;
preserved_eq.
Qed.

Lemma ret_val_hold1':
forall v3 v2 O'0 O0 Of O O' act,
ret_val (v3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
Qed.

Lemma memcpy_empty_hold:
forall v i0 v3 v2 O'0 O0 Of O O' act,
memcpy_empty (v :: v2 :: Vint32 i0 :: nil) O0 act  (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[splits; try eapply mq_ref_preserved_self;
 try eapply dom_impl_self
 ; try eapply qprt_preserved_self;auto].
Qed.


Lemma spec_step_ref_dom_mqtmrecv_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
(* 1 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1; eauto.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1; eauto.

(* 2 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_msgsize_hold1;eauto.
inv_preserved_eq.
eapply mqrecv_get_msgsize_hold1;eauto.

(* 3 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.

(* 4 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_ecb_ptr_hold1;eauto.
inv_preserved_eq.
eapply mqrecv_get_ecb_ptr_hold1;eauto.

(* 5 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.

(* 6 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply mqrecv_get_mqflags_hold1;eauto.
inv_preserved_eq.
eapply mqrecv_get_mqflags_hold1;eauto.

(* 7 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.
inv_preserved_eq.
eapply spec_skip_step_nil_sm_preserve1;eauto.

(* 8*)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

(* 9 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_no_pwl_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
inv_preserved_eq.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_hold1;eauto.
inv_preserved_eq.
eapply qpend_block_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.

(* 10 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

(* 11 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1';eauto.
inv_preserved_eq.
eapply ret_val_hold1';eauto.

(* 12 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.

(* 12 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_assm_hold1;eauto.
inv_preserved_eq.
eapply qpend_assm_hold1;eauto.

(* 13 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_to_hold1;eauto.
inv_preserved_eq.
eapply qpend_to_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qpend_block_get_hold1;eauto.
inv_preserved_eq.

(* 14 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.

(* 15 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold4;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qacc_succ_hold1;eauto.
inv_preserved_eq.

(* 16 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply memcpy_empty_hold;eauto.
inv_preserved_eq.
eapply memcpy_empty_hold;eauto.

(* 17 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
eapply ret_val_hold1;eauto.

(* 18 *)
repeat progress (destruct n; simpl in Hnth; inverts Hnth).
Qed.

Ltac rp_preved :=
  try  inv_preserved_eq;
  try tryfalse;
  try preserved_eq.

Lemma spec_step_ref_dom_bufferpost_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
(* 1 *)
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
eapply ret_val_hold1';eauto.
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_nowt_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply asrt_and_ret_hold2;eauto.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_nowt_succ_hold1;eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply qpost_exwt_succ_hold1;eauto.
inv_preserved_eq.
eapply qpost_exwt_succ_hold1;eauto.
inv_preserved_eq.

destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply asrt_and_ret_hold2;eauto.
eapply asrt_and_ret_hold2;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
Qed.

Lemma spec_step_ref_dom_bufferaccept_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
(* 1 *)
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply qacc_succ_hold1;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply qacc_succ_hold1;eauto.

destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1';eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
Qed.

Lemma spec_step_ref_dom_bufferpend_hold1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)
  
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
(* 1 *)
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply qpend_get_no_pwl_succ_hold1;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
eapply qpend_get_no_pwl_succ_hold1;eauto.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
eapply qpend_get_ex_pwl_before_sched_hold1;eauto.
eapply qpend_block_hold1;eauto.
eapply qpend_block_hold1;eauto.

destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1';eauto.
eapply ret_val_hold1';eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply qpend_assm_hold1;eauto.
eapply qpend_assm_hold1;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply qpend_block_get_hold1;eauto.
eapply qpend_to_hold1;eauto.
eapply qpend_to_hold1;eauto.
eapply qpend_block_get_hold1;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply asrt_and_ret_hold4;eauto.
eapply asrt_and_ret_hold4;eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
eapply ret_val_hold1';eauto.
destruct n. simpl in Hnth; inverts Hnth.
repeat rp_preved.
Qed.

Lemma sampleportpost_qref_asrt_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
inverts H6.
preserved_eq.
preserved_eq.
inv_preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H4.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H4.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H16.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm1.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.

unfolds.
introv Hos1 Hos2 Hdpl.
unfolds in H13.
specialize(H13 a).
destruct H13.
simpljoin.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite H13 in H17. inverts H17.
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
inverts H15.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
rewrite <- H16.
do 7 eexists. eauto.
introv Hfa;tryfalse.

inv_preserved_eq.
inverts H3.
simpljoin.
inverts H17.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm1.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.

unfolds.
introv Hos1 Hos2 Hdpl.
unfolds in H14.
specialize(H14 a).
destruct H14.
simpljoin.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite H14 in H19. inverts H19.
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
inverts H16.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
rewrite <- H17.
do 7 eexists. eauto.
introv Hfa;tryfalse.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma portaccpet_qref_asrt_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (portaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n. simpl in Hnth; inverts Hnth.
inverts Hstep;
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
eapply ret_val_hold1; eauto.
try solve[split; try eapply mq_ref_preserved_self ; try eapply qprt_preserved_self].
inverts H9.
inverts H6.
preserved_eq.
preserved_eq.
inv_preserved_eq.

destruct n; simpl in Hnth; inverts Hnth.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H4.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H9.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm1.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.

unfolds.
introv Hos1 Hos2 Hdpl.
destruct H3.
simpljoin.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
casetac x a Hte Htne.
subst a. rewrite set_a_get_a in H7.
inverts H7.
do 7 eexists. eauto.
rewrite set_a_get_a' in H7;[idtac|introv Hfa;tryfalse].
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
do 7 eexists. eauto.
introv Hfa;tryfalse.

inv_preserved_eq.
inverts H3.
simpljoin.
inverts H10.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
splits.
unfolds.
introv Hm1 Hm2. do 2 rewrite set_a_get_a' in Hm1.
rewrite Hm1 in Hm2. inverts Hm2.
introv Hq.
eauto.
introv Hfal;tryfalse.
introv Hfal;tryfalse.
introv Hfal;tryfalse.

unfolds.
introv Hos1 Hos2 Hdpl.
destruct H3.
simpljoin.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
casetac x a Hte Htne.
subst a. rewrite set_a_get_a in H9.
inverts H9.
do 7 eexists. eauto.
rewrite set_a_get_a' in H9;[idtac|introv Hfa;tryfalse].
do 7 eexists. eauto.
introv Hfa;tryfalse.
simpljoin.
eapply join_get_get_l in H0;eauto.
rewrite Hos2 in H0. inverts H0.
rewrite set_a_get_a' in Hos1.
rewrite set_a_get_a in Hos1.
inverts Hos1.
do 7 eexists. eauto.
introv Hfa;tryfalse.

destruct n; simpl in H1; inverts H1.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H3.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H0; inverts H0.
inv_preserved_eq.
inverts H2.
simpljoin.
inverts H2.
assert(O'= O).
eapply join_unique;eauto.
subst.
preserved_eq.

destruct n; simpl in H1; inverts H1.
Qed.

Lemma spec_step_ref_dom_hold1:
forall cd cd' O O' sd act ,
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
mq_ref_preserved O' O /\ qprt_preserved O' O.
Proof.
intros.
unfolds in H.
destruct H as [Hapis | [ Hend | Habt]]; simpljoin; subst; simpl; auto.
(*apispec*)
unfolds in H; simpl in H.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqsend_hold1; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqrecv_hold1; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqtmrecv_hold1;eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpost_qref_asrt_preserve1; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpend_qref_asrt_preserve1; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply sampleportpost_qref_asrt_preserve1; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply portaccpet_qref_asrt_preserve1; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferpost_hold1; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferaccept_hold1; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferpend_hold1; eauto.

tryfalse.
inverts H0.
inverts H0.
Qed.


(* pro       ------- *)
Ltac preserved_eq_pro :=
  try solve[try eapply pro_preserved_self;eauto].

  Ltac inv_preserved_pro_eq:=
    match goal with
    | H:spec_step _ _ _ _ _ _  |- _=>
  inverts H; try solve[try eapply pro_preserved_self;eauto]
    end.

Lemma ret_val_pro_hold:
forall i3 v2 O'0 O0 Of O O' act,
ret_val (Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[try eapply pro_preserved_self; auto].
Qed.

Lemma spec_skip_step_nil_sm_preserve_pro:
forall O0 v2 O'0 Of O O' act,
spec_skip_step nil O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin. inverts H.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma mqsend_get_msgsize_preserve_pro:
forall O0 v2 O'0 Of O O' act i i1,
mqsend_get_msgsize (Vint32 i :: Vint32 i1 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma mqsend_get_ecb_ptr_preserve_pro:
forall O0 v2 O'0 Of O O' act i v1,
mqsend_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma mqsend_get_mqflags_preserve_pro:
forall O0 v2 O'0 Of O O' act i i2,
mqsend_get_mqflags (Vint32 i :: Vint32 i2 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma asrt_and_ret_pro:
forall i3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (Vint32 i3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O .
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;try eapply pro_preserved_self; auto.
Qed.


Lemma qtimedpost_ovf_block_body_pro:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_ovf_block_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H10.

assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
                     (abstcblist (set x9 x6
                    (x2, wait (os_stat_postq x) None, x0, x1, x15))))
                    absecblsid (absecblist (set x7 x (absmsgq x11 x12 (x6 :: x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H0.
subst.

(*prio_preserved *)
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.
rewrite map_get_set' in H1;try intro;tryfalse. 
rewrite map_get_set in H1.
inverts H1. 
casetac x6 t Hy Hn.
subst.
rewrite map_get_set in H2.
inverts H2.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H2;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x6 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H6 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qtimedpost_after_sched_pro:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_after_sched (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;try eapply pro_preserved_self; auto.
Qed.

Lemma qtimedpost_timeout_err_body_pro:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qtimedpost_timeout_err_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x2)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
           (set O abtcblsid
              (abstcblist (set x3 x2 (x4, rdy, Vnull, false, x13))))
           absecblsid
           (absecblist
              (set x7 x (absmsgq x11 x10 (remove_tid x2 x9), x12)))).
eapply join_get_set_eq_2;eauto.
clear H1 H2 H4.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.
rewrite map_get_set' in H1;try intro;tryfalse. 
rewrite map_get_set in H1.
inverts H1. 
casetac x2 t Hy Hn.
subst.
rewrite map_get_set in H2.
inverts H2.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H2;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x2 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H3 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qpost_nowt_succ_body_pro:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_nowt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set O absecblsid
           (absecblist (set x2 x (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)))).
eapply join_get_set_eq;eauto.
clear H2.
subst.
(*prio_preserved*)
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro;tryfalse. 
unfolds.
do 5 eexists.
split;eauto.

unfolds in H1.
simpljoin.

unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse.
split;eauto. 
Qed.

Lemma qpost_exwt_succ_body_pro:
forall v1 v i3 v2 O'0 O0 Of O O' act,
qpost_exwt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set
(set O abtcblsid
   (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15))))
absecblsid
(absecblist
   (set x2 x (absmsgq nil x13 x14, remove_tid x6 x4)))).
eapply join_get_set_eq_2;eauto.
clear H2 H3.
subst.

(*qprt_preserved O' O*)
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro;tryfalse. 
rewrite map_get_set in H1.
inverts H1.
casetac x6 t Hy Hn.
subst.
rewrite map_get_set in H2.
inverts H2.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H2;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x6 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H6 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma spec_step_ref_dom_mqsend_pro_hold:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqsend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.

(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct n. simpl in Hnth; inverts Hnth.
inv_preserved_pro_eq.
inv_preserved_pro_eq.
inv_preserved_pro_eq.
destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply mqsend_get_msgsize_preserve_pro;eauto.
eapply mqsend_get_msgsize_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply mqsend_get_ecb_ptr_preserve_pro;eauto.
eapply mqsend_get_ecb_ptr_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply mqsend_get_mqflags_preserve_pro;eauto.
eapply mqsend_get_mqflags_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.
eapply qtimedpost_ovf_block_body_pro;eauto.
eapply qtimedpost_ovf_block_body_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply qtimedpost_after_sched_pro;eauto.
eapply qtimedpost_after_sched_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply qtimedpost_timeout_err_body_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qtimedpost_timeout_err_body_pro;eauto.
eapply asrt_and_ret_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
destruct n; simpl in H0; inverts H0.
Qed.

Lemma mqrecv_get_msgsize_preserve_pro:
forall O0 v2 O'0 Of O O' act i i1,
mqrecv_get_msgsize (Vint32 i :: Vint32 i1 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma mqrecv_get_ecb_ptr_preserve_pro:
forall O0 v2 O'0 Of O O' act i v1,
mqrecv_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma mqrecv_get_mqflags_preserve_pro:
forall O0 v2 O'0 Of O O' act i i2,
mqrecv_get_mqflags (Vint32 i :: Vint32 i2 :: nil) O0 act (v2, Some O'0) ->
eqdomO O0 O'0 ->
tidsame O0 O'0 ->
join O0 Of O -> 
join O'0 Of O' ->
prio_preserved O' O.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in H2; eauto; subst;
try eapply pro_preserved_self; auto.
Qed.

Lemma asrt_and_ret_pro1:
forall v3 v2 O'0 O0 Of O O' act x,
asrt_and_ret (v3 :: x :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O .
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H2 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;try eapply pro_preserved_self; auto.
Qed.

Lemma qpend_get_no_pwl_succ_body_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_no_pwl_succ_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H7 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x1)) as Hcid.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
           (absecblist (set x2 x (absmsgq x5 x6 nil, x7)))).
eapply join_get_set_eq;eauto.
clear H0 H1 H2.
subst.

(*prio_preserved*)
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro;tryfalse. 
unfolds.
do 5 eexists.
split;eauto.

unfolds in H1.
simpljoin.

unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse.
split;eauto.
Qed. 

Lemma qpend_block_get_body_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_get_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H6 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (O'=set O abtcblsid
           (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto.
subst.
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H4.
simpljoin.

rewrite map_get_set in H4.
inverts H4.
casetac x6 t Hy Hn.
subst.
rewrite map_get_set in H5.
inverts H5.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H5;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x6 t Hy Hn.
subst.
unfolds in H4.
simpljoin.
rewrite Htcb in H3;inverts H3.
rewrite H2 in H4;inverts H4.
unfolds.
do 5 eexists.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H4.
simpljoin.
rewrite Htcb in H4;inverts H4.
unfolds.
do 5 eexists.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qpend_get_ex_pwl_before_sched_body_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_get_ex_pwl_before_sched_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H9 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O abtcblsid = Some (abstcblist x2)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.
assert (O'=set
(set O abtcblsid
   (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15))))
absecblsid
(absecblist
   (set x1 x
      (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)))).
eapply join_get_set_eq_2;eauto.
clear H0 H1.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro ;tryfalse.
rewrite map_get_set in H1.
inverts H1.
casetac x12 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x12 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H5 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qpend_block_body_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_block_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

assert (get O curtid = Some (oscurt x11)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x5)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid
(abstcblist
   (set x3 x11 (x8, wait (os_stat_q x) x12, x1, x2, x14))))
absecblsid
(absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H4.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro ;tryfalse.
rewrite map_get_set in H1.
inverts H1.
casetac x11 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x11 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H5 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qpend_to_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qpend_to_body (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H8 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O curtid = Some (oscurt x3)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist (set x1 x3 (x2, rdy, Vnull, false, x11))))
absecblsid
(absecblist (set x4 x (absmsgq x6 x7 x8, remove_tid x3 x9)))).
eapply join_get_set_eq_2;eauto.

clear H0 H1 H3.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro ;tryfalse.
rewrite map_get_set in H1.
inverts H1.
casetac x3 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x3 t Hy Hn.
subst.
unfolds in H1.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H2 in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H1.
simpljoin.
rewrite Htcb in H1;inverts H1.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma ret_val_pro_hold1:
forall v3 v2 O'0 O0 Of O O' act,
ret_val (v3 :: nil) O0 act  (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[try eapply pro_preserved_self; auto].
Qed.

Lemma qpend_assm_pro:
forall v1 v3 O'0 O0 Of O O' act,
qpend_assm_stat (v1 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H5 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.
eapply map_join_deter in Hj1; eauto; subst;
try solve[try eapply pro_preserved_self; auto].
Qed.

Lemma qacc_succ_pro:
forall v1 v2 v3 O'0 O0 Of O O' act,
qacc_succ_body  (v1 :: v2 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
destruct H4 as [(Heq & Ho)|(Hne & Hn)]; tryfalse.
inverts Ho.

assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid (absecblist (set x1 x (absmsgq x3 x4 x5, x6)))).
eapply join_get_set_eq;eauto.

clear H2.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H1.
simpljoin.

rewrite map_get_set' in H1;try intro;tryfalse. 
unfolds.
do 5 eexists.
split;eauto.

unfolds in H1.
simpljoin.

unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse.
split;eauto.
Qed.

Lemma memcpy_empty_pro:
forall v v2 v3 i0 O'0 O0 Of O O' act,
memcpy_empty (v :: v2 :: Vint32 i0 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H2.
eapply map_join_deter in Hj1; eauto; subst;
try solve[try eapply pro_preserved_self; auto].
Qed.

Lemma spec_step_ref_dom_mqrecv_pro:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply mqrecv_get_msgsize_preserve_pro;eauto.
eapply mqrecv_get_msgsize_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply mqrecv_get_ecb_ptr_preserve_pro;eauto.
eapply mqrecv_get_ecb_ptr_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply mqrecv_get_mqflags_preserve_pro;eauto.
eapply mqrecv_get_mqflags_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 

eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_block_body_pro;eauto.
eapply qpend_block_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply qpend_assm_pro;eauto.
eapply qpend_assm_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply qpend_block_get_body_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_block_get_body_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply memcpy_empty_pro;eauto.
eapply memcpy_empty_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
destruct n; simpl in H0; inverts H0.
Qed.

Lemma q_send_to_domain_pro:
forall v v1 O'0 O0 Of O O' act,
q_send_to_domain (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H16.

assert (get O ibufsid = Some (ibufs x19)) as Hib.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x25)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x23)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O oskportid = Some (oskport x8)) as Hosk.
eapply join_get_get_l;eauto.
assert (get O oschannelid = Some (oschannel x14)) as Hchal.
eapply join_get_get_l;eauto.

assert (O'=set
(set
   (set (set O osdomainportid (osdomainport x27)) abtcblsid
      (abstcblist x26)) absecblsid (absecblist x24)) ibufsid
(ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_4;eauto.
clear H4 H2 H0 H6 H7 H8.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H2.
simpljoin.

do 2 rewrite map_get_set' in H2;try intro;tryfalse. 
rewrite map_get_set in H2.
inverts H2.
unfolds in H13.
specialize (H13 t).
destruct H13.
simpljoin.
rewrite H6 in H4;inverts H4.

unfolds.
do 5 eexists.
split;eauto.

simpljoin.
rewrite H2 in H4.
unfolds.
do 5 eexists.
split;eauto.
unfolds in H2.
simpljoin.
rewrite Htcb in H2;inverts H2.

unfolds in H13.
specialize (H13 t).
destruct H13.
simpljoin.
rewrite H2 in H4;inverts H4.

unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse.
split.
rewrite map_get_set';try intro;tryfalse.
rewrite map_get_set;eauto.
eauto.

simpljoin.
rewrite <-H2 in H4.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse.
split.
rewrite map_get_set';try intro;tryfalse.
rewrite map_get_set;eauto.
eauto.
Qed.

Lemma store_msg_ref_dom_pro:
forall v v1 O'0 O0 Of O O' act,
store_msg (v :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H7.

assert (get O ibufsid = Some (ibufs x9)) as Hib.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hdom.
eapply join_get_get_l;eauto.

assert (O'=set
(set O osdomainportid
   (osdomainport
      (set x0 x
         (x1, x2, x3, SourceP, x4, x5, x6,
         QueuePort x7 (x8 ++ x11 :: nil))))) ibufsid
(ibufs (upd_bufmp x9 x10 x8))).
eapply join_get_set_eq_2;eauto.
clear H2 H0.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H2.
simpljoin.
do 2 rewrite map_get_set' in H2;try intro;tryfalse. 
unfolds.
do 5 eexists.
split;eauto.

unfolds in H2.
simpljoin.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
split.
rewrite map_get_set';try intro;tryfalse.
eauto.
eauto.
Qed.

Lemma qportpost_qref_asrt_pro_preserve:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply q_send_to_domain_pro;eauto.
eapply q_send_to_domain_pro;eauto.
eapply store_msg_ref_dom_pro;eauto.
eapply store_msg_ref_dom_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
destruct n; simpl in H0; inverts H0.
Qed.


Lemma qportpend_notnil_body_ref_dom_pro:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_notnil_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H8.

assert (get O obufsid = Some (obufs x13)) as Hob.
eapply join_get_get_l;eauto.

assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set O osdomainportid
   (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid (obufs (upd_bufmp x13 x15 (x13 x15 ++ x10 :: nil)))).
eapply join_get_set_eq_2;eauto.
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H6.
simpljoin.
do 2 rewrite map_get_set' in H6;try intro;tryfalse. 
unfolds.
do 5 eexists.
split;eauto.

unfolds in H6.
simpljoin.
unfolds.
do 5 eexists.
rewrite map_get_set';try intro;tryfalse. 
split.
rewrite map_get_set';try intro;tryfalse.
eauto.
eauto.
Qed.

Lemma qportpend_block_ref_dom_pro:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H12.

assert (get O curtid = Some (oscurt x14)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x10)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist
      (set x10 x14 (x12, wait (os_stat_port x) x17, x15, x16, x18))))
absecblsid (absecblist (set x19 x (absport, x14 :: x20)))).
eapply join_get_set_eq_2;eauto.

clear H4 H3 H2 H0.
subst.
unfolds; intros.
unfolds;intros;split;intros.
unfolds in H2.
simpljoin.
rewrite map_get_set' in H2;try intro;tryfalse. 
rewrite map_get_set in H2.
inverts H2.
casetac x14 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x14 t Hy Hn.
subst.
unfolds in H2.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H7 in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H2.
simpljoin.
rewrite Htcb in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma  qportpend_block_get_ref_dom_pro:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_get_body (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
inverts H11.

assert (get O curtid = Some (oscurt x16)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x12)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O obufsid = Some (obufs x20)) as Hob.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
(set (set O abtcblsid (abstcblist (set x12 x16 (x14, rdy, Vnull, x17, x18))))
   osdomainportid
   (osdomainport (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
obufsid
(obufs (upd_bufmp x20 (dom_for_prio x18) (x20 (dom_for_prio x18) ++ x10 :: nil)))).
eapply join_get_set_eq_3;eauto.
clear H3 H2 H0 H5.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H2.
simpljoin.
do 2 rewrite map_get_set' in H2;try intro;tryfalse. 
rewrite map_get_set in H2.
inverts H2.
casetac x16 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x16 t Hy Hn.
subst.
unfolds in H2.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H4 in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H2.
simpljoin.
rewrite Htcb in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qportpend_block_timeout_ref_dom_pro:
forall v v1 v2 O'0 O0 Of O O' act,
qportpend_block_timeout (v :: v2 :: nil) O0 act (v1, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
prio_preserved O' O.
Proof.
introv Hstem Hj1 Hj2.
inverts Hstem; simpljoin.
rename H13 into H12.
inverts H12.

assert (get O curtid = Some (oscurt x15)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x11)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set (set O abtcblsid (abstcblist (set x11 x15 (x13, rdy, Vnull, x17, x18))))
absecblsid (absecblist (set x19 x (absport, remove_tid x15 x20)))).
eapply join_get_set_eq_2;eauto.
clear H7 H3 H2 H0.
subst.

unfolds; intros.
unfolds;intros;split;intros.
unfolds in H2.
simpljoin.
rewrite map_get_set' in H2;try intro;tryfalse. 
rewrite map_get_set in H2.
inverts H2.
casetac x15 t Hy Hn.
subst.
rewrite map_get_set in H3.
inverts H3.
unfolds.
do 5 eexists.
split;eauto.
rewrite map_get_set' in H3;eauto.
unfolds.
do 5 eexists.
split;eauto.

casetac x15 t Hy Hn.
subst.
unfolds in H2.
simpljoin.
rewrite Htcb in H0;inverts H0.
rewrite H4 in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set;eauto.

unfolds in H2.
simpljoin.
rewrite Htcb in H2;inverts H2.
unfolds.
do 5 eexists.
rewrite map_get_set' ;try intro ;tryfalse.
rewrite map_get_set.
split.
eauto.
rewrite map_get_set';eauto.
Qed.

Lemma qportpend_qref_asrt_pro_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (qportpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto. 
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply qportpend_notnil_body_ref_dom_pro;eauto.
eapply qportpend_notnil_body_ref_dom_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply qportpend_block_ref_dom_pro;eauto.
eapply qportpend_block_ref_dom_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply qportpend_block_get_ref_dom_pro;eauto.
eapply qportpend_block_timeout_ref_dom_pro;eauto.
destruct n; simpl in H1; inverts H1.
Qed.

Lemma tickchange_els :
  forall t st st' els els',
    tickchange t st els st' els' ->
    (els = els' \/
     (exists eid m wl, EcbMod.get els eid = Some (m, wl) /\
        els' = EcbMod.set els eid (m, remove_tid t wl))
    ).
Proof.
  intros.
  inverts H;
    try solve [left; auto].
Qed.

Lemma spec_step_ref_dom_mqtmrecv_pro:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct v; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v2; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply mqrecv_get_msgsize_preserve_pro;eauto.
eapply mqrecv_get_msgsize_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply mqrecv_get_ecb_ptr_preserve_pro;eauto.
eapply mqrecv_get_ecb_ptr_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply mqrecv_get_mqflags_preserve_pro;eauto.
eapply mqrecv_get_mqflags_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
eapply ret_val_pro_hold;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 

eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_block_body_pro;eauto.
eapply qpend_block_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply qpend_assm_pro;eauto.
eapply qpend_assm_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply qpend_block_get_body_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_block_get_body_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply memcpy_empty_pro;eauto.
eapply memcpy_empty_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
destruct n; simpl in H0; inverts H0.
Qed.

Lemma spec_step_ref_dom_bufferpost_pro:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v1; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.
eapply qpost_nowt_succ_body_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.
eapply qpost_exwt_succ_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro;eauto.
eapply asrt_and_ret_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.
destruct n; simpl in H0; inverts H0.
Qed.

Lemma spec_step_ref_dom_bufferaccept_pro:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qacc_succ_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
Qed.




Lemma spec_step_ref_dom_bufferpend_pro:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
(* destruct v0; destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]]. *)

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.
eapply qpend_get_no_pwl_succ_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_get_ex_pwl_before_sched_body_pro;eauto.
eapply qpend_block_body_pro;eauto.
eapply qpend_block_body_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply qpend_assm_pro;eauto.
eapply qpend_assm_pro;eauto.
destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply qpend_block_get_body_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_to_pro;eauto.
eapply qpend_block_get_body_pro;eauto.
destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq. 
eapply asrt_and_ret_pro1;eauto.
eapply asrt_and_ret_pro1;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
Qed.

Lemma sampleportpost_qref_asrt_pro_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto. 
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
inverts H3.
simpljoin.
inverts H16.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
unfolds.
intros.
unfolds.
introv Hdom.
split.
introv Htpi1.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a' in H12;[idtac|introv Hfa;tryfalse]).
do 5 eexists. split. eauto. eauto.

introv Htpi.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
do 5 eexists. split;eauto.

inverts H3.
simpljoin.
inverts H17.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
unfolds.
intros.
unfolds.
introv Hdom.
split.
introv Htpi1.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a' in H13;[idtac|introv Hfa;tryfalse]).
do 5 eexists. split. eauto. eauto.

introv Htpi.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
do 5 eexists. split;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
Qed.

Lemma portaccept_qref_asrt_pro_preserve1:
forall cd cd' O O' vl n sd act ,
nth_error (get_all_succs (portaccept vl)) n = Some cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
introv Hnth Hstep.
destruct vl; simpl in Hnth.
unfold get_all_succs in Hnth .
unfold get_all_succs_aux in Hnth.
(* simpl in Hnth. *)
destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse].

destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct v0;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].
destruct vl;
try solve [destruct n; simpl in Hnth; 
[ inverts Hnth; inverts Hstep | 
  simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse]].

destruct n; simpl in Hnth; inverts Hnth.
try repeat inv_preserved_pro_eq. 
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply ret_val_pro_hold1;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
inverts H3.
simpljoin.
inverts H9.
eapply join_get_set_eq_2 in H12;eauto.
inverts H12.
unfolds.
intros.
unfolds.
introv Hdom.
split.
introv Htpi1.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a' in H7;[idtac|introv Hfa;tryfalse]).
do 5 eexists. split. eauto. eauto.

introv Htpi.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
do 5 eexists. split;eauto.

inverts H3.
simpljoin.
inverts H10.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
unfolds.
intros.
unfolds.
introv Hdom.
split.
introv Htpi1.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a' in H9;[idtac|introv Hfa;tryfalse]).
do 5 eexists. split. eauto. eauto.

introv Htpi.
unfold task_prio_id in *.
simpljoin.
try repeat( rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
do 5 eexists. split;eauto.

destruct n; simpl in H0; inverts H0.
try repeat inv_preserved_pro_eq.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.
eapply spec_skip_step_nil_sm_preserve_pro;eauto.

destruct n; simpl in H1; inverts H1.
try repeat inv_preserved_pro_eq.
eapply ret_val_pro_hold1;eauto.

destruct n; simpl in H0; inverts H0.
Qed.

Lemma spec_step_qprt_pro_hold1:
forall cd cd' O O' sd act ,
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
prio_preserved O' O.
Proof.
intros.
unfolds in H.
destruct H as [Hapis | [ Hend | Habt]]; simpljoin; subst; simpl; auto.
(*apispec*)
unfolds in H; simpl in H.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
inverts H.
inverts H2.
eapply spec_step_ref_dom_mqsend_pro_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqrecv_pro; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_mqtmrecv_pro;eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpost_qref_asrt_pro_preserve; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply qportpend_qref_asrt_pro_preserve1; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply sampleportpost_qref_asrt_pro_preserve1; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply portaccept_qref_asrt_pro_preserve1; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferpost_pro; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferaccept_pro; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H.
eapply In_nth_error in H1; simpljoin.
eapply spec_step_ref_dom_bufferpend_pro; eauto.
tryfalse.

inv_preserved_pro_eq;tryfalse.
inv_preserved_pro_eq;tryfalse.
Qed.

(* pro       ------- end ------*)

(*api_cspaceid_hold*)
(*mqsend*)
Lemma ret_val_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i,
ret_val (i :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H4.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.

Lemma spec_skip_step_cspaceid_absteq:
forall O0 act O'0 Of O O' v2,
spec_skip_step nil O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma mqsend_get_msgsize_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
mqsend_get_msgsize (Vint32 i :: Vint32 i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma mqsend_get_mqflags_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i2,
mqsend_get_mqflags (Vint32 i :: Vint32 i2 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.

Lemma mqsend_get_ecb_ptr_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
mqsend_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma asrt_and_ret_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i3 v3,
asrt_and_ret (i3 :: v3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H4 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma qpost_nowt_succ_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 v1 v i3,
qpost_nowt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set O absecblsid
          (absecblist (set x2 x (absmsgq (x4 ++ x0 :: nil) x3 x5, nil)))).
eapply join_get_set_eq;eauto.
clear H4.
subst.
rewrite set_a_get_a'; try intro; tryfalse; eauto.
Qed.


Lemma qpost_exwt_succ_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 v1 v i3,
qpost_exwt_succ_body (v1 :: v :: Vint32 i3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H11 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x7)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'=set
(set O abtcblsid
   (abstcblist (set x7 x6 (x11, rdy, x0, x10, x15))))
absecblsid
(absecblist (set x2 x (absmsgq nil x13 x14, remove_tid x6 x4)))).
eapply join_get_set_eq_2;eauto.
clear H4 H5.
subst.
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.
Qed.


Lemma qtimedpost_ovf_block_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 v1 v i3,
qtimedpost_ovf_block_body (v1 :: v :: Vint32 i3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H12.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x9)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.

assert (O'=set
          (set O abtcblsid
             (abstcblist
                (set x9 x6 (x2, wait (os_stat_postq x) None, x0, x1, x15))))
          absecblsid
          (absecblist (set x7 x (absmsgq x11 x12 (x6 :: x13), x14)))).
eapply join_get_set_eq_2;eauto.
clear H4 H3 H2.
subst.
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.
Qed.


Lemma qtimedpost_after_sched_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 v1 v i3,
qtimedpost_after_sched (v1 :: v :: Vint32 i3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma qtimedpost_timeout_err_body_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 v1 v i3,
qtimedpost_timeout_err_body (v1 :: v :: Vint32 i3 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H11 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O absecblsid = Some (absecblist x7)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O curtid = Some (oscurt x2)) as Hct.
eapply join_get_get_l;eauto.

assert (O'= set
          (set O abtcblsid
             (abstcblist (set x3 x2 (x4, rdy, Vnull, false, x13)))) absecblsid
          (absecblist (set x7 x (absmsgq x11 x10 (remove_tid x2 x9), x12)))).
eapply join_get_set_eq_2;eauto.
clear H4 H3 H6.
subst.
do 2 try rewrite set_a_get_a'; try intro; tryfalse; eauto.
Qed.

Lemma mqsend_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (mqsend x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct v; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.

destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v0; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v1; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v2; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct v2; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.

destruct H; subst.
inverts H0.
inverts H7; auto.
auto.
inverts H3; auto.
simpl in H.
destruct_inverts1 H.
inverts H0.
inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.
inverts H11. inverts H12.
eapply ret_val_cspaceid_absteq; eauto.
auto.

inverts H12. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto.
inverts H7; auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H8.
eapply mqsend_get_msgsize_cspaceid_absteq; eauto.
inverts H8; auto.
inverts H4.
eapply mqsend_get_msgsize_cspaceid_absteq; eauto.
auto.
inverts H0.

inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.

inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.
inverts H11.
inverts H7.
eapply mqsend_get_ecb_ptr_cspaceid_absteq; eauto.
auto.

inverts H3.
eapply mqsend_get_ecb_ptr_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.

inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.

inverts H0.
inverts H8.
eapply mqsend_get_mqflags_cspaceid_absteq; eauto.
auto.

inverts H4.
eapply mqsend_get_mqflags_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.

inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.

inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

inverts H0; try inverts H8; auto.
inverts H4; auto.
inverts H0. inverts H8.
inverts H11.
eapply asrt_and_ret_cspaceid_absteq; eauto.

inverts H11. inverts H12.
eapply asrt_and_ret_cspaceid_absteq; eauto.
inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto.

inverts H13. inverts H14. inverts H14.
inverts H15; tryfalse.
inverts H15. inverts H16. inverts H16.
inverts H17.
eapply qpost_nowt_succ_cspaceid_absteq; eauto.
inverts H17; auto. auto.

inverts H4. inverts H12.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H13. inverts H14.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H14. inverts H15. inverts H7.
eapply qpost_exwt_succ_cspaceid_absteq; eauto. auto.

inverts H3.
eapply qpost_exwt_succ_cspaceid_absteq; eauto. auto.
inverts H15. inverts H16; tryfalse. auto.

inverts H16. inverts H17. inverts H7.
eapply qtimedpost_ovf_block_cspaceid_absteq; eauto.
inverts H7; auto.
inverts H3.
eapply qtimedpost_ovf_block_cspaceid_absteq; eauto. auto.

inverts H17. inverts H18.
eapply qpost_nowt_succ_cspaceid_absteq; eauto. auto.
inverts H18; auto.

inverts H0. inverts H8; auto. auto.
inverts H4. inverts H8; auto. auto.
inverts H3; auto.
inverts H0. inverts H8.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H4.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.

inverts H0. inverts H8; auto. auto.
inverts H4. inverts H8; auto. auto.
inverts H3; auto.
inverts H0. inverts H8. auto.
inverts H4. inverts H8. 
eapply qtimedpost_after_sched_cspaceid_absteq; eauto. auto.

inverts H3.
eapply qtimedpost_after_sched_cspaceid_absteq; eauto. auto.
inverts H0. inverts H8. inverts H11.
eapply qtimedpost_timeout_err_body_cspaceid_absteq; eauto.

inverts H11. inverts H12.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H12; tryfalse. auto.
inverts H4. inverts H12.
eapply qtimedpost_timeout_err_body_cspaceid_absteq; eauto. auto.

inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H13; tryfalse.
inverts H0. inverts H8. inverts H11.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H11. inverts H12.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.

inverts H13. inverts H14.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H14. inverts H15.
eapply qpost_nowt_succ_cspaceid_absteq; eauto. auto.
inverts H15. inverts H16.
inverts H16; tryfalse. auto.
inverts H4. inverts H12. 
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H13. inverts H14. 
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H14. inverts H15.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H15. inverts H16.
eapply qpost_nowt_succ_cspaceid_absteq; eauto. auto.
inverts H16. inverts H17. inverts H7.
eapply qpost_exwt_succ_cspaceid_absteq; eauto. auto.
inverts H3. 
eapply qpost_exwt_succ_cspaceid_absteq; eauto. auto.
inverts H17; tryfalse. 
inverts H0. inverts H8; auto. auto.
inverts H4. inverts H8; auto. auto.
inverts H3; auto.
inverts H0. inverts H8.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H4.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.
inverts H11. inverts H12.
eapply ret_val_cspaceid_absteq; eauto. auto.
inverts H12.
eapply ret_val_cspaceid_absteq; eauto. auto. tryfalse.
destruct H; subst; inverts H0;
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
destruct H; subst. inverts H0.
simpl in H; tryfalse.
Qed.

(*mqreceive*)

Lemma mqrecv_get_msgsize_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
mqrecv_get_msgsize (Vint32 i :: Vint32 i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma mqrecv_get_ecb_ptr_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
mqrecv_get_ecb_ptr (Vint32 i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.
eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.


Lemma qpend_get_no_pwl_succ_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_get_no_pwl_succ_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H9 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O absecblsid = Some (absecblist x2)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O curtid = Some (oscurt x1)) as Hct.
eapply join_get_get_l;eauto.

assert (O'= set O absecblsid (absecblist (set x2 x (absmsgq x5 x6 nil, x7)))).
eapply join_get_set_eq;eauto.
clear H3 H2 H4.
subst.

rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_block_get_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_block_get_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H8 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.

assert (O'= set O abtcblsid (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto.
clear H3 H2.
subst.

rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_get_ex_pwl_before_sched_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_get_ex_pwl_before_sched_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H11 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O abtcblsid = Some (abstcblist x2)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set
          (set O abtcblsid (abstcblist (set x2 x12 (x8, rdy, x11, x13, x15))))
          absecblsid
          (absecblist
             (set x1 x (absmsgq (x4 ++ x11 :: nil) x5 (remove_tid x12 x6), x7)))).
eapply join_get_set_eq_2;eauto.
clear H3 H2.
subst.

do 2 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_block_body_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_block_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
match goal with 
H: Some _ = Some _ |- _ => inverts H end.

assert (get O curtid = Some (oscurt x11)) as Hct.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x5)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x3)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'= set
          (set O abtcblsid
             (abstcblist
                (set x3 x11 (x8, wait (os_stat_q x) x12, x1, x2, x14))))
          absecblsid (absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))).
eapply join_get_set_eq_2;eauto.
clear H3 H2 H4.
subst.

do 2 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_to_body_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_to_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H10 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O curtid = Some (oscurt x3)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x4)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set
          (set O abtcblsid
             (abstcblist (set x1 x3 (x2, rdy, Vnull, false, x11)))) absecblsid
          (absecblist (set x4 x (absmsgq x6 x7 x8, remove_tid x3 x9)))).
eapply join_get_set_eq_2;eauto.
clear H3 H2 H4.
subst.

do 2 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_block_get_body_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qpend_block_get_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H8 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O curtid = Some (oscurt x6)) as Hct.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x1)) as Htcb.
eapply join_get_get_l;eauto.

assert (O'= set O abtcblsid (abstcblist (set x1 x6 (x2, rdy, Vnull, false, x8)))).
eapply join_get_set_eq;eauto.
clear H3 H2.
subst.

do 2 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qacc_succ_body_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i v1,
qacc_succ_body ( i :: v1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H6 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

assert (get O absecblsid = Some (absecblist x1)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'= set O absecblsid (absecblist (set x1 x (absmsgq x3 x4 x5, x6)))).
eapply join_get_set_eq;eauto.
clear H4.
subst.

do 2 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qpend_assm_stat_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i,
qpend_assm_stat ( i  :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H7 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

eapply map_join_deter in H0; eauto. 
subst; auto.

Qed.


Lemma memcpy_empty_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1 i2,
memcpy_empty ( i :: i1 :: i2  :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H4.

eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.

Lemma mq_recv_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (mqreceive x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct v; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.

destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v0; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v1; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v2; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.

destruct H; subst.
inverts H0.
inverts H7; auto.
auto.
inverts H3; auto.
simpl in H.
destruct_inverts1 H.
inverts H0.
inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.
inverts H11. inverts H12.
eapply ret_val_cspaceid_absteq; eauto.
auto.

inverts H12. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto.
inverts H7; auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H8.
eapply mqrecv_get_msgsize_cspaceid_absteq; eauto.
inverts H8; auto.
inverts H4.
eapply mqrecv_get_msgsize_cspaceid_absteq; eauto.
auto.
inverts H0.

inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.
inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.
inverts H11.
inverts H7.
eapply mqsend_get_ecb_ptr_cspaceid_absteq; eauto.
auto.

inverts H3.
eapply mqsend_get_ecb_ptr_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto.
auto.

inverts H11. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto.
auto.

inverts H0.
inverts H8.
eapply mqsend_get_mqflags_cspaceid_absteq; eauto.
auto.

inverts H4.
eapply mqsend_get_mqflags_cspaceid_absteq; eauto.
auto.

inverts H0. inverts H11.
eapply ret_val_cspaceid_absteq; eauto. auto.

inverts H11. inverts H12.
eapply ret_val_cspaceid_absteq; eauto. auto.

inverts H12. inverts H7.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inverts H3.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

inverts H0. inverts H8; auto. auto.
inverts H4; auto.
inverts H0. inverts H8. inverts H11.
inverts H12.
eapply asrt_and_ret_cspaceid_absteq; eauto.

inverts H12. inverts H13.
eapply asrt_and_ret_cspaceid_absteq; eauto.
inverts H13. inverts H14; tryfalse.
inverts H14. inverts H15; tryfalse.
inverts H15. invert H16.
intros.
eapply qpend_get_no_pwl_succ_cspaceid_absteq; eauto.

do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end. tryfalse.

destruct H1'; subst.
inverts H11; tryfalse.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply asrt_and_ret_cspaceid_absteq; eauto. 
eapply asrt_and_ret_cspaceid_absteq; eauto. 
eapply qpend_get_no_pwl_succ_cspaceid_absteq; eauto. 

do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 

eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq; eauto. 
eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq; eauto. 
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply qpend_block_body_cspaceid_absteq; eauto.
eapply qpend_block_body_cspaceid_absteq; eauto.

destruct H1'; subst.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
destruct H1'; subst.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply ret_val_cspaceid_absteq; eauto. auto.

eapply ret_val_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end. eauto.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply qpend_assm_stat_cspaceid_absteq; eauto. auto.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply qpend_assm_stat_cspaceid_absteq; eauto. 
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 
eapply qpend_block_get_body_cspaceid_absteq;eauto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_block_get_body_cspaceid_absteq;eauto.
destruct H1'; subst.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto. 

eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply qacc_succ_body_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; tryfalse.
auto. auto. auto.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply asrt_and_ret_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply qacc_succ_body_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; tryfalse.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; tryfalse.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; tryfalse.
eapply memcpy_empty_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply memcpy_empty_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
tryfalse.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
Qed.

Lemma qsend_to_domain_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i,
q_send_to_domain ( i  :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H18.

assert (get O ibufsid = Some (ibufs x19)) as Hib.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x25)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x23)) as Hecb.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O oskportid = Some (oskport x8)) as Hosk.
eapply join_get_get_l;eauto.
assert (get O oschannelid = Some (oschannel x14)) as Hchal.
eapply join_get_get_l;eauto.

assert (O'=set
(set
   (set (set O osdomainportid (osdomainport x27)) abtcblsid
      (abstcblist x26)) absecblsid (absecblist x24)) ibufsid
(ibufs (upd_bufmp x19 x20 x22))).
eapply join_get_set_eq_4;eauto.
clear H4 H2 H0 H6 H7 H8.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.

Lemma store_msg_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i,
store_msg ( i  :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H9.

assert (get O ibufsid = Some (ibufs x9)) as Hib.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x0)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
          (set O osdomainportid
             (osdomainport
                (set x0 x
                   (x1, x2, x3, SourceP, x4, x5, x6,
                   QueuePort x7 (x8 ++ x11 :: nil))))) ibufsid
          (ibufs (upd_bufmp x9 x10 x8))).
eapply join_get_set_eq_2;eauto.
clear H4 H2.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qportpost_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (qportpost x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].

destruct v0; destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].

destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
simpl in H.
destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.

do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply qsend_to_domain_cspaceid_absteq; eauto.
eapply qsend_to_domain_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply store_msg_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply store_msg_cspaceid_absteq; eauto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply spec_skip_step_cspaceid_absteq; eauto. 
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply spec_skip_step_cspaceid_absteq; eauto. 
eapply spec_skip_step_cspaceid_absteq; eauto. 
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end. auto.
eapply spec_skip_step_cspaceid_absteq; eauto.  auto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
tryfalse.
Qed.

Lemma qportpend_notnil_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
qportpend_notnil_body ( i :: i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H10.

assert (get O obufsid = Some (obufs x13)) as Hob.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.

assert (O'=set
          (set O osdomainportid
             (osdomainport
                (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
          obufsid (obufs (upd_bufmp x13 x15 (x13 x15 ++ x10 :: nil)))).
eapply join_get_set_eq_2;eauto.
clear H4 H2.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qportpend_block_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
qportpend_block ( i :: i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H14.

assert (get O curtid = Some (oscurt x14)) as Hct.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x10)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
          (set O abtcblsid
             (abstcblist
                (set x10 x14 (x12, wait (os_stat_port x) x17, x15, x16, x18))))
          absecblsid (absecblist (set x19 x (absport, x14 :: x20)))).
eapply join_get_set_eq_2;eauto.
clear H4 H2 H5 H6.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qportpend_block_get_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
qportpend_block_get_body ( i :: i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H13.

assert (get O curtid = Some (oscurt x16)) as Hct.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x12)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O obufsid = Some (obufs x20)) as Hobd.
eapply join_get_get_l;eauto.

assert (O'=set
          (set
             (set O abtcblsid
                (abstcblist (set x12 x16 (x14, rdy, Vnull, x17, x18))))
             osdomainportid
             (osdomainport
                (set x1 x (x2, x3, x4, x5, x6, x7, x8, QueuePort x9 x11))))
          obufsid
          (obufs
             (upd_bufmp x20 (dom_for_prio x18)
                (x20 (dom_for_prio x18) ++ x10 :: nil)))).
eapply join_get_set_eq_3;eauto.
clear H4 H2 H5 H7.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.


Lemma qportpend_block_timeout_cspaceid_absteq:
forall O0 act O'0 Of O O' v2 i i1,
qportpend_block_timeout ( i :: i1 :: nil) O0 act (v2, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
inverts H15.

assert (get O curtid = Some (oscurt x15)) as Hct.
eapply join_get_get_l;eauto.
assert (get O osdomainportid = Some (osdomainport x1)) as Hosd.
eapply join_get_get_l;eauto.
assert (get O abtcblsid = Some (abstcblist x11)) as Htcb.
eapply join_get_get_l;eauto.
assert (get O absecblsid = Some (absecblist x19)) as Hecb.
eapply join_get_get_l;eauto.

assert (O'=set
          (set O abtcblsid
             (abstcblist (set x11 x15 (x13, rdy, Vnull, x17, x18))))
          absecblsid (absecblist (set x19 x (absport, remove_tid x15 x20)))).
eapply join_get_set_eq_2;eauto.
clear H4 H2 H5 H9.
subst.

do 4 try rewrite set_a_get_a'; try intro; tryfalse; auto.
Qed.

Lemma qportpend_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (qportpend x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].

destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v1; destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].

destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
simpl in H.
destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply qportpend_notnil_cspaceid_absteq; eauto.
eapply qportpend_notnil_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply spec_skip_step_cspaceid_absteq; eauto.
do 2 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
 eapply spec_skip_step_cspaceid_absteq; eauto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply spec_skip_step_cspaceid_absteq; eauto.
eapply spec_skip_step_cspaceid_absteq; eauto.

match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qportpend_block_cspaceid_absteq; eauto.
eapply qportpend_block_cspaceid_absteq; eauto.
do 3 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qportpend_block_get_cspaceid_absteq; eauto.
eapply qportpend_block_timeout_cspaceid_absteq;eauto.
tryfalse.
Qed.

Lemma mqrecv_get_mqflags_cspaceid_absteq:
forall O0 act O'0 Of O O' v3 i i3,
mqrecv_get_mqflags (Vint32 i :: Vint32 i3 :: nil) O0 act (v3, Some O'0) ->
join O0 Of O ->
join O'0 Of O' ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
inverts H; simpljoin.
destruct H5 as [(He & Hsome) | (Hn & Hnone)]; tryfalse.
inverts Hsome.

eapply map_join_deter in H0; eauto. 
subst; auto.
Qed.

Lemma mq_recvtm_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (mqtimedreceive x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct v; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.

destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v0; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v1; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct v1; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct v2; destruct x2.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct x2.

destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
simpl in H.
destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply mqrecv_get_msgsize_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply mqrecv_get_msgsize_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply mqrecv_get_ecb_ptr_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply mqrecv_get_ecb_ptr_cspaceid_absteq; eauto.
auto.

do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply mqrecv_get_mqflags_cspaceid_absteq;eauto.
auto.
eapply mqrecv_get_mqflags_cspaceid_absteq;eauto.
auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto. 
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply spec_skip_step_cspaceid_absteq; eauto. 
eapply spec_skip_step_cspaceid_absteq; eauto.

match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_get_no_pwl_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_get_no_pwl_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_block_body_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_block_body_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_assm_stat_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_assm_stat_cspaceid_absteq; eauto. 
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_block_get_body_cspaceid_absteq;eauto.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_block_get_body_cspaceid_absteq;eauto.
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto. 
eapply asrt_and_ret_cspaceid_absteq; eauto. 
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.  
eapply qacc_succ_body_cspaceid_absteq; eauto. 
eapply asrt_and_ret_cspaceid_absteq; eauto.  
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.   
eapply qacc_succ_body_cspaceid_absteq; eauto.  
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto. 
eapply memcpy_empty_cspaceid_absteq; eauto. 
eapply memcpy_empty_cspaceid_absteq; eauto. 
do 7 try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
eapply ret_val_cspaceid_absteq; eauto. 
tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
destruct H; subst; inverts H0; tryfalse.
Qed.
 
Lemma bufferpost_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (bufferpost x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].

destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v1; destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].

destruct_inverts1 H.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
simpl in H.
destruct_inverts1 H.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
inverts H0.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply qpost_nowt_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply qpost_nowt_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply qpost_exwt_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply qpost_exwt_succ_cspaceid_absteq;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end;eauto.
eapply ret_val_cspaceid_absteq;eauto.
tryfalse.
Qed.

Ltac rp_prevedpro :=
  repeat try match goal with 
  H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
 

Lemma bufferaccept_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (bufferaccept x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
(* destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]. *)
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
(* destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]]. *)

destruct_inverts1 H.
rp_prevedpro.

simpl in H.
destruct_inverts1 H.
rp_prevedpro.
inverts H0.
eapply ret_val_cspaceid_absteq; eauto.
auto.
rp_prevedpro.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply qacc_succ_body_cspaceid_absteq; eauto. 
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply qacc_succ_body_cspaceid_absteq; eauto.

inverts H0.
eapply ret_val_cspaceid_absteq; eauto.
auto.
tryfalse.
Qed.

Lemma bufferpend_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (bufferpend x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].
destruct v0;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
(* destruct v0;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]]. *)
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].

destruct_inverts1 H.
rp_prevedpro.

simpl in H.
destruct_inverts1 H.
rp_prevedpro.
inverts H0.
eapply ret_val_cspaceid_absteq; eauto.
auto.
rp_prevedpro.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply qpend_get_no_pwl_succ_cspaceid_absteq;eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply qpend_get_no_pwl_succ_cspaceid_absteq; eauto. 
eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq; eauto.
eapply qpend_get_ex_pwl_before_sched_cspaceid_absteq; eauto.
eapply qpend_block_body_cspaceid_absteq;eauto.
eapply qpend_block_body_cspaceid_absteq;eauto.

rp_prevedpro.
rp_prevedpro.
eapply ret_val_cspaceid_absteq; eauto.
eapply ret_val_cspaceid_absteq; eauto.
rp_prevedpro.
rp_prevedpro.
eapply qpend_assm_stat_cspaceid_absteq;eauto.
eapply qpend_assm_stat_cspaceid_absteq;eauto.
rp_prevedpro.
eapply qpend_block_get_body_cspaceid_absteq;eauto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_to_body_cspaceid_absteq;eauto.
eapply qpend_block_get_body_cspaceid_absteq;eauto.
rp_prevedpro.
eapply asrt_and_ret_cspaceid_absteq; eauto.
eapply asrt_and_ret_cspaceid_absteq; eauto.
rp_prevedpro.
eapply ret_val_cspaceid_absteq; eauto.
tryfalse.
Qed.

Lemma sampleportpost_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (sampleportpost x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].

destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v0; 
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v0;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].


destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
simpl in H.
destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 3 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto. 
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
eapply ret_val_cspaceid_absteq; eauto. auto.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
inverts H4.
simpljoin.
inverts H17.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
try repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).

inverts H3.
simpljoin.
inverts H18.
eapply join_get_set_eq_2 in H14;eauto.
inverts H14.
try repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto.
inv_preserved_eq.
eapply ret_val_cspaceid_absteq; eauto. auto.
tryfalse.
Qed.

Lemma portaccept_spec_step_cspaceid_hold:
forall cd sd O O' act cd' x2,
In cd (get_all_succs (portaccept x2)) ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
lets H1': H.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
destruct x2; simpl in H.
destruct H; subst; inverts H0; tryfalse.
destruct x2.
destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse].

destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v0; 
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct v0;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].
destruct x2;
try solve [ destruct H; subst;
[ match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end |
simpl in H; tryfalse]].


destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
simpl in H.
destruct_inverts1 H.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
do 2 match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.
eapply ret_val_cspaceid_absteq; eauto. auto.
match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end.

eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.
eapply ret_val_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto. auto.
inv_preserved_eq.
inv_preserved_eq.

inverts H4.
simpljoin.
inverts H10.
eapply join_get_set_eq_2 in H13;eauto.
inverts H13.
try repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).

inv_preserved_eq.
inverts H3.
simpljoin.
inverts H11.
eapply join_get_set_eq_2 in H14;eauto.
inverts H14.
try repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).

inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto.
inv_preserved_eq.
inv_preserved_eq.
inv_preserved_eq.
eapply spec_skip_step_cspaceid_absteq; eauto.
inv_preserved_eq.
eapply ret_val_cspaceid_absteq; eauto. auto.
tryfalse.
Qed.

Lemma spec_step_cspaceid_hold:
forall cd sd O O' act cd',
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
get O' cspaceid = get O cspaceid.
Proof.
intros.
unfolds in H.
destruct H as [Hapis | [ Hend | Habt]]; simpljoin; subst; simpl; auto.
unfolds in H; simpl in H.

remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
eapply mqsend_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
eapply mq_recv_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H.
eapply mq_recvtm_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
eapply qportpost_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
eapply qportpend_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X.
inverts H.
eapply sampleportpost_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X.
inverts H.
eapply portaccept_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H.
eapply bufferpost_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H.
eapply bufferaccept_spec_step_cspaceid_hold; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H.
eapply bufferpend_spec_step_cspaceid_hold; eauto.

tryfalse.
try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
try match goal with 
H: spec_step _ _ _ _ _ _ |- _ => inverts H end; auto.
Qed.


Ltac des_vl_absprog hstep := 
  match goal with
    vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
      destruct vl; inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst; simpl; auto
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst; simpl; auto)   
  end.

(* O' -> O *)
Lemma head_asrt_sat_step_O'_to_O_hold':
forall s pr O O' cd' sd act cd,
good_api_stmt s ->
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
head_asrt_sat pr s O'->
head_asrt_sat pr s O.
Proof.
introv Hgds Hgdcd Hspec Hsat.
destruct Hgds as [Hapis | [ Hints | [ Hend | Habt]]]; simpljoin; subst; simpl; auto.
(*api_spec*)
unfolds in H; simpl in H.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
 remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
Require Import protect.
protect Heqsend_vl.
rename H0 into H1.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply mqsend_qref_asrt_preserve; eauto.
exists (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                          :: nil)  (Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil) n.
change  ((Vint32 i :: v :: Vint32 i0 :: v0 :: nil) ++
         Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil) with (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                         :: Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold1; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].

eapply mqrecv_qref_asrt_preserve; eauto.
exists (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                          :: nil)  (Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil) n.
change  ((Vint32 i :: v :: Vint32 i0 :: v0 :: nil) ++
         Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil) with (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                         :: Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold1; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].

eapply mqtimedrecv_qref_asrt_preserve; eauto.
exists (Vint32 i :: v :: Vint32 i0  :: v0 :: Vint32 i1 :: nil)  
 (Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil) n.
change  ((Vint32 i :: v :: Vint32 i0  :: v0 :: Vint32 i1 :: nil) ++
Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil) with (Vint32 i
:: v
   :: Vint32 i0
      :: v0
         :: Vint32 i1
            :: Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold1; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply qprtpost_asrt_preserve; eauto.
exists (v :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v :: nil) ++ Vint32 i :: v0 :: nil) with (v :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_qprt_pro_hold1;eauto.
eapply spec_step_ref_dom_hold1; eauto.
eapply spec_step_cspaceid_hold; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply qprtpend_asrt_preserve; eauto.
exists (v :: v0 :: nil)  (Vint32 i :: v1 :: nil) n.
change  ((v :: v0 :: nil) ++ Vint32 i :: v1 :: nil) with (v :: v0 :: Vint32 i :: v1 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold1; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X. 
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply sprtpost_asrt_preserve; eauto.
exists (v  :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v  :: nil) ++ Vint32 i :: v0 :: nil) with (v  :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_qprt_pro_hold1;eauto.
eapply spec_step_ref_dom_hold1; eauto.
eapply spec_step_cspaceid_hold; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X. 
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply prtaccept_asrt_preserve; eauto.
exists (v  :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v  :: nil) ++ Vint32 i :: v0 :: nil) with (v  :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold1; eauto.
rewrite <-dom_impl_comm. 
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferpost_asrt_preserve; eauto.
exists (v :: v0 :: nil)  (Vint32 i :: nil) n.
change  ((v :: v0 :: nil) ++ Vint32 i :: nil) with (v :: v0 :: Vint32 i :: nil).
rewrite H1'. simpl; splits; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
(* destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]]. *)
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferaccept_asrt_preserve; eauto.
exists (v :: nil)  (v0 :: nil) n.
change  ((v :: nil) ++ v0 :: nil) with (v :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H.
lets H1': H0.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H0, H1'.
protect Heqsend_vl.
rename H0 into H1.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
(* destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]]. *)
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferpend_asrt_preserve; eauto.
exists (v :: Vint32 i :: nil)  (v0 :: nil) n.
change  ((v :: Vint32 i :: nil) ++ v0 :: nil) with (v :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.

tryfalse.
unfolds in H; simpl in H.
repeat progress(destruct x; tryfalse).
inverts H.
eapply intr_asrt_preserve; eauto.
eapply In_nth_error in H0; simpljoin; eauto.
Qed.

Lemma pro_preserved_comm:
forall O' O,
prio_preserved O O' <-> prio_preserved O' O.
Proof. 
unfold prio_preserved.
intros.
split.
intros.
specialize( H td).
unfolds in H.
unfolds.
intros.
rewrite H;eauto.
split;intros;eauto.

intros.
specialize( H td).
unfolds in H.
unfolds.
intros.
rewrite H;eauto.
split;intros;eauto.
Qed.

Lemma head_asrt_sat_step_hold':
forall s pr O O' cd' sd act cd,
good_api_stmt s ->
good_api_stmt' cd ->
spec_step sd cd O cd' O' act ->
(head_asrt_sat pr s O <-> head_asrt_sat pr s O').
Proof.
introv Hgds Hgdcd Hspec.
splits; intros.
destruct Hgds as [Hapis | [ Hend | Habt]]; simpljoin; subst; simpl; auto.
(*api_spec*)
unfolds in H0; simpl in H0.
remember (Zeq_bool mq_send x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
Require Import protect.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply mqsend_qref_asrt_preserve; eauto.
exists (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                          :: nil)  (Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil) n.
change  ((Vint32 i :: v :: Vint32 i0 :: v0 :: nil) ++
         Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil) with (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                         :: Vint32 i1 :: v1 :: Vint32 i2 :: Vint32 i3 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool mq_recv x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply mqrecv_qref_asrt_preserve; eauto.
exists (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                          :: nil)  (Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil) n.
change  ((Vint32 i :: v :: Vint32 i0 :: v0 :: nil) ++
         Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil) with (Vint32 i
                :: v
                   :: Vint32 i0
                      :: v0
                         :: Vint32 i1 :: v1 :: Vint32 i2 :: v2 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool mq_timedrecv x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct v; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v2; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply mqtimedrecv_qref_asrt_preserve; eauto.
exists (Vint32 i
:: v
   :: Vint32 i0
      :: v0
         :: Vint32 i1
                          :: nil)  (Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil) n.
change  ((Vint32 i
:: v
   :: Vint32 i0
      :: v0
         :: Vint32 i1 :: nil) ++
Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil) with (Vint32 i
:: v
   :: Vint32 i0
      :: v0
         :: Vint32 i1
            :: Vint32 i2 :: v1 :: Vint32 i3 :: v2 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool q_port_post x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply qprtpost_asrt_preserve; eauto.
exists (v :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v :: nil) ++ Vint32 i :: v0 :: nil) with (v :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
rewrite pro_preserved_comm.
eapply spec_step_qprt_pro_hold1;eauto.

eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_cspaceid_hold in Hspec; eauto.

remember (Zeq_bool q_port_pend x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply qprtpend_asrt_preserve; eauto.
exists (v :: v0 :: nil)  (Vint32 i :: v1 :: nil) n.
change  ((v :: v0 :: nil) ++ Vint32 i :: v1 :: nil) with (v :: v0 :: Vint32 i :: v1 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool sample_port_post x) as X.
destruct X. 
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply sprtpost_asrt_preserve; eauto.
exists (v  :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v  :: nil) ++ Vint32 i :: v0 :: nil) with (v  :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
eapply spec_step_ref_dom_hold; eauto.
rewrite pro_preserved_comm.
eapply spec_step_qprt_pro_hold1;eauto.
lets Ht:spec_step_ref_dom_hold.
specializes Ht.
eapply Hgdcd. eapply Hspec.
simpljoin. eauto.
eapply spec_step_cspaceid_hold in Hspec; eauto.

remember (Zeq_bool port_accept x) as X.
destruct X. 
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply prtaccept_asrt_preserve; eauto.
exists (v  :: nil)  (Vint32 i :: v0 :: nil) n.
change  ((v  :: nil) ++ Vint32 i :: v0 :: nil) with (v  :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.
lets Ht:spec_step_ref_dom_hold.
specializes Ht.
eapply Hgdcd. eapply Hspec.
simpljoin. eauto.
eapply spec_step_ref_dom_hold; eauto.

remember (Zeq_bool buffer_post x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v1; destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferpost_asrt_preserve; eauto.
exists (v :: v0 :: nil)  (Vint32 i :: nil) n.
change  ((v :: v0 :: nil) ++ Vint32 i :: nil) with (v :: v0 :: Vint32 i :: nil).
rewrite H1'. simpl; splits; eauto.

remember (Zeq_bool buffer_accept x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.
destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
(* destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]]. *)
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferaccept_asrt_preserve; eauto.
exists (v :: nil)  (v0 :: nil) n.
change  ((v :: nil) ++ v0 :: nil) with (v :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.

remember (Zeq_bool buffer_pend x) as X.
destruct X.
inverts H0.
lets H1': H1.
eapply In_nth_error in H1'.
destruct H1' as (n & H1').
  remember x2 as send_vl.
rewrite Heqsend_vl in H1, H1'.
protect Heqsend_vl.

destruct x2; simpl in H1; subst.
destruct H1; simpl; subst; auto; tryfalse.
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
(* destruct v0; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]]. *)
destruct x2; simpl; auto;
try solve [destruct H1; [ subst; simpl; auto | simpl in H; tryfalse]].
eapply bufferpend_asrt_preserve; eauto.
exists (v :: Vint32 i :: nil)  (v0 :: nil) n.
change  ((v :: Vint32 i :: nil) ++ v0 :: nil) with (v :: Vint32 i :: v0 :: nil).
rewrite H1'. simpl; splits; eauto.

tryfalse.
unfolds in H0; simpl in H0.
repeat progress(destruct x; tryfalse).
inverts H0.
eapply intr_asrt_preserve; eauto.
eapply In_nth_error in H1; simpljoin; eauto.

destruct Habt; simpljoin. 
simpl; auto.
simpl; auto.

eapply head_asrt_sat_step_O'_to_O_hold';eauto.
Qed.
