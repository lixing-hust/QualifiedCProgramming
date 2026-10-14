(* Require Import lemmasfortoptheo.  *)
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
Open Scope nat_scope.
Require Import PIF_LibTactics.
Require Import Integers.
Require Import Map.
Require Import PIF_join_lib.
Require Import inv_hold_init.
(* Require Import join_prop.
Require Import rulesoundlib.
Require Import step_prop.
Require Import joinmemLib.
Require Import lmachLib. *)
Lemma tid_eq_dec: forall (t t':tid), {t=t'}+{t<>t'}.
Proof.
intros.
destruct t,t'.
assert ({b=b0} + {b<>b0}).
apply Pos.eq_dec.
destruct H.
subst.
assert ({i=i0} + {i<>i0}).
apply Int.eq_dec.
destruct H.
subst.
left.
auto.
right.
intro H.
apply n.
inversion H.
auto.
right.
intro H.
apply n.
inversion H;auto.
Qed.

Lemma beq_taskid: forall (x y : tid), {x = y} + {x <> y}.
Proof.
  apply tid_eq_dec.
Qed.

Module mmapspec.
  Definition domain:= tid.
  Definition image:= mem.
  Definition beq_Domain := beq_taskid.
End mmapspec.


Module TMSpecMod := Map.MapFun mmapspec.

Definition TMMap:= TMSpecMod.Map.

Module omapspec.
  Definition domain:= tid.
  Definition image:= osabst.
  Definition beq_Domain := beq_taskid.
End omapspec.


Module TOSpecMod := Map.MapFun omapspec.

Definition TOMap:= TOSpecMod.Map.

Ltac unfoldbug:= try (unfold code in *;unfold tid in *;unfold cont in *).

Ltac unfolddef:=
  try
    (unfold code in *;unfold cont in *;unfold tid in *;unfold TMSpecMod.B in *;
     unfold mmapspec.image in *;
     unfold TOSpecMod.B in *;
     unfold omapspec.image in *;unfold Maps.sub in *;unfold disjoint in *;unfold osabst in *).
(****************************************)
Lemma join_get_set_eq:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    join (set O1 a b') O2 O' ->
    O' = set O a b'.
  intros.
  assert (join (set O1 a b') O2 (set O a b')).
  {
    clear H2.
    geat.
  }
  eapply map_join_deter; eauto.
Qed.

Ltac infer_v ls t :=
  (** verbose infer, logical correct by slow **)
  let ic := calc_ins_for_context in
  let ig := plist_minus ls ic in
  let ic' := plist_minus ls ig in
  infer' ic' t; try (solve [ crush ]); infer' ig t.

Ltac infer_q ls t :=
  (** quick infer, may be quick but can not solve **)
  let ic := calc_ins_for_context in
  let ig := plist_minus ls ic in
  let ic' := plist_minus ls ig in
  infer' ic' t; crush; infer' ig t.

Ltac infer ::= infer_q.

Lemma join_get_set_eq_2:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b' a' c c',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c -> 
    join (set (set O1 a b') a' c') O2 O' ->
    O' = set (set O a b') a' c'.
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

Lemma abst_set_get_neq: forall id1 id2 y O, id1<>id2 ->  OSAbstMod.get (OSAbstMod.set O id2 y) id1 = OSAbstMod.get O id1.
  Proof.
    intros.
    apply OSAbstMod.set_a_get_a'.
    apply absdataidspec.neq_beq_false.
    auto.
  Qed.

Lemma post_nowt_return_getop_t:
  forall tls els x x5 t ct x6 x7 x8 x9 p_t,
    t <> ct -> 
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x6)), nil) ->
    TcbMod.get tls ct = Some (x5, x7, x8, x9) ->
    GET_ORP t (TcbMod.set tls ct (x6, x7, x8, x9))
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_t ->
    GET_ORP t tls els p_t.
Proof.
  intros.
  unfolds; intros.  
  assert (TcbMod.get (TcbMod.set tls ct (x6, x7, x8, x9)) t <> None).
  rewrite TcbMod.set_a_get_a'; auto.
  apply tidspec.neq_beq_false; auto.
  apply H2 in H4.
  destruct H4; mytac.
  left.
  exists x0.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto; inverts H4.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds; eauto.

  right.
  split.
  intro; apply H4; mytac.
  exists x3.
  unfolds in H6; mytac.
  unfolds.
  destruct (tidspec.beq x x3) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H6 in H0; inverts H0; tryfalse.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.
  rewrite TcbMod.set_a_get_a' in H5.
  eauto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma pend_timeout_get_opt:
forall t ct x7 x x9 x10 x11 x3 p st m x4 x6 op sus s s',
  t <> ct ->
  EcbMod.get x7 x = Some (absmutexsem x9 x10, x11) ->
  In ct x11 ->
  TcbMod.get x3 t = Some (p, st, m, sus) ->
  TcbMod.get x3 ct = Some (x4, wait (os_stat_mutexsem x) (Some Int.zero), x6, s) ->
  GET_ORP t (set x3 ct (x4, rdy, x6, s')) 
                       (set x7 x (absmutexsem x9 x10, remove_tid ct x11)) op ->
  GET_ORP t x3 x7 op.
Proof.
  intros.
  unfolds; intros.  
  assert (TcbMod.get (TcbMod.set x3 ct (x4, rdy, x6, s')) t <> None).
  rewrite TcbMod.set_a_get_a'; auto.
  apply tidspec.neq_beq_false; auto.
  apply H4 in H6.
  destruct H6; mytac.
  left.
  exists x0.
  unfolds in H6; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H6; auto; inverts H6.
(*   rewrite EcbMod.set_a_get_a' in H6; auto. *)
  unfolds; eauto.
  rewrite EcbMod.set_a_get_a' in H6; auto.
  unfolds; eauto.

  right.
  split.
  intro; apply H6; mytac.
  exists x5.
  unfolds in H8; mytac.
  unfolds.
  destruct (tidspec.beq x x5) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H8 in H0; inverts H0; tryfalse.
  rewrite EcbMod.set_a_get_a; auto.
  eauto.
  rewrite EcbMod.set_a_get_a'; auto. eauto.
  rewrite TcbMod.set_a_get_a' in H7.
  eauto.
  apply tidspec.neq_beq_false; auto.
Qed.

    Lemma beq_tid_true_eq: forall t1 t2, beq_tid t1 t2 = true -> t1 = t2.
    Proof.
      intros.
      unfolds in H; destruct t1; destruct t2.
      apply andb_true_iff in H; destruct H.
      rewrite beq_pos_Pos_eqb_eq in H.
      apply Pos.eqb_eq in H.
      pose proof Int.eq_spec i i0.
      rewrite H0 in H1.
      substs; auto.
    Qed.

  Lemma In_remove_tid' : forall wl t t', t <> t' -> In t wl -> In t (remove_tid t' wl).
  Proof.
    intro; inductions wl; intros.
    simpl in *; tryfalse.
    simpl in H0; destruct H0; substs.
    simpl.
    destruct(beq_tid t' t) eqn : eq1.
    false; apply H.
    apply beq_tid_true_eq in eq1; auto.
    simpl; auto.
    simpl.
    destruct(beq_tid t' a) eqn : eq1.
    eapply IHwl; eauto.
    simpl.
    right.
    eapply IHwl; eauto.
Qed.

  Lemma In_remove_tid : forall wl t ct, In ct (remove_tid t wl) -> In ct wl.
  Proof.
    inductions wl; intros.
    simpl in H; tryfalse.
    simpl in H.
    destruct (beq_tid t a) eqn : eq1.
    simpl.
    right; eapply IHwl; eauto.
    simpl in H; destruct H; substs.
    simpl; left; auto.
    simpl; right; eapply IHwl; eauto.
  Qed.

Lemma post_iswait:
  forall t x11 x12 x x6 els owner owner',
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 owner, x11) ->
    (ST_WAIT_T t
               (EcbMod.set els x
                           (absmutexsem x6 owner', remove_tid x12 x11)) <->
    ST_WAIT_T t els).
Proof.
  intros.
  split; intros.
  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  inverts H1.
  do 4 eexists.
  split; eauto.
  eapply In_remove_tid; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  do 4 eexists; split; eauto.

  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H1 in H0; inverts H0.
  exists x0.
  rewrite EcbMod.set_a_get_a; auto.
  do 3 eexists; split; eauto.
  eapply In_remove_tid'; eauto.
  exists x0.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.

Lemma post_iswait':
  forall t x11 x12 x x6 eid els owner owner',
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 owner, x11) ->
    (IS_WAITING_E t eid
                 (EcbMod.set els x
                             (absmutexsem x6 owner', remove_tid x12 x11)) <->
    IS_WAITING_E t eid els).
Proof.
  intros.
  split; intros.
  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto; inverts H1.
  do 3 eexists; split; eauto.
  eapply In_remove_tid; eauto.
  rewrite EcbMod.set_a_get_a' in H1; auto.
  do 3 eexists; split; eauto.

  unfolds in H1; mytac.
  unfolds.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H1 in H0; inverts H0.
  rewrite EcbMod.set_a_get_a; auto.
  do 3 eexists; split; eauto.
  eapply In_remove_tid'; eauto.
  rewrite EcbMod.set_a_get_a'; auto.
  do 3 eexists; split; eauto.
Qed.

  Lemma beq_tid_true : forall t, beq_tid t t = true.
  Proof.
    intros.
    unfolds; destruct t.
    rewrite beq_pos_Pos_eqb_eq.
    rewrite Pos.eqb_refl.
    rewrite Int.eq_true.
    simpl; auto.
  Qed.

Lemma In_remove_tid_false : forall wl t, In t (remove_tid t wl) -> False.
Proof.
  intro; inductions wl; intros.
  simpl in H; auto.
  simpl in H.
  destruct (beq_tid t a) eqn : eq1.
  eapply IHwl; eauto.
  simpl in H.
  destruct H.
  substs.
  rewrite beq_tid_true in eq1; tryfalse.
  eapply IHwl; eauto.
Qed.

Lemma nnp_remove_nwait:
  forall tls els x11 t x x6 ct x8 p x13 x14 sus,
    NO_NEST_PENDING tls els ->
    rdy_notin_wl tls els ->
    GetHWait tls x11 t ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    TcbMod.get tls t = Some (p, x13, x14, sus) ->
    ~
      ST_WAIT_T t
      (EcbMod.set els x (absmutexsem x6 (Some (t, p)), remove_tid t x11)).
Proof.
  intros.
  intro.
  unfolds in H4; mytac.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4.
  eapply In_remove_tid_false; eauto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds in H1; mytac.
  unfolds in H0; mytac.
  assert(IS_WAITING_E t x els).
  unfolds; do 3 eexists; split; eauto.
  assert(IS_WAITING_E t x0 els).
  unfolds; do 3 eexists; split; eauto.
  lets Hx1 : H9 H10.
  lets Hx2 : H9 H11.
  mytac.
  rewrite H13 in H12; inverts H12.
  assert(tidspec.beq x0 x0 = true).
  apply tidspec.eq_beq_true; auto.
  rewrite eq1 in H12; tryfalse.
Qed.



Lemma remove_is_wait_neq:
  forall x12 t x x6 x7 x11 els ct x8,
    t <> x12 ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    ST_WAIT_T t
               (EcbMod.set els x
                           (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11)) ->
    ST_WAIT_T t els.
Proof.
  intros.
  unfolds in H1; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto; inverts H1.
  unfolds. exists x0 x1 (Some (ct, x8)) x11.
  split; auto.
  eapply In_remove_tid; eauto.

  rewrite EcbMod.set_a_get_a' in H1; auto.
  unfolds.
  exists x0 x1 x2 x3; split; eauto.
Qed.

Lemma set_neq_getop_eq:
  forall t ct tls x4 x3 x6 x7 x8 p_t,
    t <> ct ->
    TcbMod.get tls t <> None ->
    EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
    GET_ORP t tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) p_t ->
    GET_ORP t tls x4 p_t.
Proof.
  intros.
  lets Hx: H2 H0.
  unfolds; intros.
  destruct Hx; mytac.
  left.
  unfolds in H4; mytac.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; inverts H4; tryfalse.
  auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  exists x; unfolds; eauto.

  right.
  split.
  intro; apply H4; mytac.
  destruct (tidspec.beq x3 x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H6; mytac.
  rewrite H1 in H6; tryfalse.
  exists x2.
  unfolds; rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.

Lemma no_nest_pending_set_none:
  forall tls p_ct st msg sus els eid ct p_e wl x6 x7,
    TcbMod.get tls ct = Some (p_ct, st, msg, sus) ->
    EcbMod.get els eid = Some (absmutexsem x6 None, x7) ->
    NO_NEST_PENDING tls (EcbMod.set els eid (absmutexsem p_e (Some (ct, p_ct)), wl)) ->
    ~ (exists qid, IS_OWNER ct qid els).
Proof.
  intros.
  unfolds in H1.
  assert (TcbMod.get tls ct <> None).
  intro; rewrite H in H2; tryfalse.
  assert (IS_OWNER ct eid
         (EcbMod.set els eid (absmutexsem p_e (Some (ct, p_ct)), wl))).
  unfolds.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
  lets Hx: H1 H2 H3; clear H1 H2 H3; mytac.
  intro; apply H2; mytac.
  destruct (tidspec.beq eid x) eqn : eq1.
  apply tidspec.beq_true_eq in eq1; substs.
  unfolds in H3; mytac.
  rewrite H0 in H3; tryfalse.
  exists x.
  splits; auto.
  apply tidspec.beq_false_neq; auto.
  unfolds.
  rewrite EcbMod.set_a_get_a'; auto.
Qed.

Lemma no_nest_pending_set_prio_eq:
  forall tls x4 x3 x6 ct x8 x7 x9 x10 sus p_ct,
    NO_NEST_PENDING tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) ->
    GET_ORP ct tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) p_ct ->
    TcbMod.get tls ct = Some (x8, x9, x10, sus) ->
    p_ct = x8.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  assert(TcbMod.get tls ct <> None).
  intro; rewrite H1 in H2; tryfalse.
  assert(IS_OWNER ct x3 (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7))).
  unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
  lets Hx1: H H2 H3.
  lets Hx2: H0 H2.
  clear H H0 H2 H3.
  destruct Hx2; mytac.
  unfolds in H; mytac.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H; inverts H; auto.
  false; apply H2.
  exists x; unfold IS_OWNER.
  rewrite EcbMod.set_a_get_a'; auto.
  rewrite EcbMod.set_a_get_a' in H; auto.
  apply tidspec.beq_false_neq in eq1.
  eauto.

  false; apply H.
  unfold IS_OWNER.
  do 4 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  apply tidspec.eq_beq_true; auto.
Qed.


Lemma no_nest_pending_set_hold:
  forall tls x4 x3 x6 ct x8 x7,
    NO_NEST_PENDING tls
                    (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7)) ->
    EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
    NO_NEST_PENDING tls x4.
Proof.
  intros.
  unfolds; intros.
  destruct(tidspec.beq x3 qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds in H2; do 3 destruct H2.
  rewrite H0 in H2; tryfalse.

  assert(IS_OWNER t qid (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, x8)), x7))).
  unfolds; rewrite EcbMod.set_a_get_a'; auto.
  lets Hx: H H1 H3. simpljoin. splits; auto.
  intro; apply H4.
  unfolds in H6; mytac.
  destruct (tidspec.beq x3 x) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfolds; do 4 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  rewrite H0 in H6; inverts H6; eauto.
  unfolds; do 4 eexists.
  rewrite EcbMod.set_a_get_a'; eauto.

  intro; apply H5; mytac.
  exists x;splits; auto.
  unfolds in H7. 
  destruct (tidspec.beq x3 x) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  unfolds. do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  simpljoin.
  rewrite e in H0; inverts H0.
  simpljoin.
  unfolds.
  exists x0.
  exists x1.
  exists x2.
  rewrite EcbMod.set_a_get_a'; auto.
  Unshelve.
  exact Int.zero.
  exact Int.zero.
  exact nil.
Qed.

(*add*)
Lemma remove_wait:
forall tls els x x9 x10 x11 ct x4 x6 sus,
  rdy_notin_wl tls els ->
  EcbMod.get els x = Some (absmutexsem x9 x10, x11) ->
  In ct x11 ->
  TcbMod.get tls ct = Some (x4, wait (os_stat_mutexsem x) (Some Int.zero), x6, sus)->
  ~ ST_WAIT_T ct (set els x (absmutexsem x9 x10, remove_tid ct x11)).
Proof.
  intros.
  intro.
  unfolds in H3; mytac.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H3; auto.
  inverts H3.
  eapply In_remove_tid_false; eauto.
  
  rewrite EcbMod.set_a_get_a' in H3; auto.
  unfolds in H; mytac.
  assert(IS_WAITING_E ct x els).
  unfolds; do 3 eexists; split; eauto.
  assert(IS_WAITING_E ct x0 els).
  unfolds; do 3 eexists; split; eauto.
  lets Hx1 : H6 H7.
  lets Hx2 : H6 H8.
  mytac.
  rewrite H9 in H10; inverts H10.
  assert(tidspec.beq x x = true).
  apply tidspec.eq_beq_true; auto.
  rewrite eq1 in H10; tryfalse.
Qed.

Lemma remove_is_wait_neq':
forall t ct els x9 x10 x11 x ,
    t <> ct -> 
    EcbMod.get els x = Some (absmutexsem x9 x10, x11) -> 
    In ct x11 -> 
    ~ ST_WAIT_T t els ->
    ~ ST_WAIT_T t (set els x (absmutexsem x9 x10, remove_tid ct x11)).
Proof.
  intros.
  intro.
  eapply H2.
  unfolds in H3; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H3; auto; inverts H3.
  unfolds. exists x0 x1 x2 x11.
  split; auto.
  eapply In_remove_tid; eauto.

  rewrite EcbMod.set_a_get_a' in H3; auto.
  unfolds.
  exists x0 x1 x2 x3; split; eauto.
Qed.

Lemma is_owner_set_other:
  forall t eid els x x3 x4 x5 ct,
    t <> ct ->
    IS_OWNER t eid els ->
    EcbMod.get els x = Some (absmutexsem x3 None, x4) ->
    IS_OWNER t eid
             (EcbMod.set els x (absmutexsem x3 (Some (ct, x5)), x4)).
Proof.
  intros.
  unfolds; unfolds in H0; mytac.
  destruct(tidspec.beq x eid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a; auto.
  rewrite H0 in H1; inverts H1.
  rewrite EcbMod.set_a_get_a'; auto.
  eauto.
Qed.

Lemma pend_no_lift_iswating:
  forall t ct els x x8 x9 x10 x7,
    t <> ct ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) ->
    ST_WAIT_T t (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) ->
    ST_WAIT_T t els.
Proof.
  intros.
  unfolds in H1; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H1; auto.
  inverts H1.
  unfolds; do 4 eexists.
  split; eauto.
  simpl in H2; destruct H2; tryfalse; auto.

  rewrite EcbMod.set_a_get_a' in H1; auto.
  unfolds; do 4 eexists.
  split; eauto.
Qed.

Lemma pend_no_lift_getop:
  forall tls ct x12 x2 els x x8 x9 x10 x7 x0 t p_t m sus,
    TcbMod.get tls ct = Some (x12, rdy, x2, sus) ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) -> 
    GET_ORP t (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, m, sus))
           (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) p_t ->
    GET_ORP t tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, m, sus)) t <> None).
  destruct (tidspec.beq ct t) eqn : eq1.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  apply H1 in H3.
  destruct H3; mytac.
  left.
  unfolds in H3; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  rewrite EcbMod.set_a_get_a in H3; auto; inverts H3.
  exists x; unfolds; do 2 eexists; eauto.

  rewrite EcbMod.set_a_get_a' in H3; auto.
  exists x1; unfolds; do 2 eexists; eauto.

  right.
  split.
  intro; apply H3; mytac.
  unfolds in H5; mytac.
  destruct (tidspec.beq x x5) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  rewrite H0 in H5; inverts H5.
  eexists; unfolds; do 3 eexists.
  rewrite EcbMod.set_a_get_a; eauto.
  eexists; unfolds.
  do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  destruct (tidspec.beq ct t) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite TcbMod.set_a_get_a in H4; auto.
  inverts H4; eauto.

  rewrite TcbMod.set_a_get_a' in H4; eauto.
Qed.


Lemma pend_no_lift_nnp:
  forall tls ct x12 x2 els x x8 x9 x10 x7 x0 m sus,
    TcbMod.get tls ct = Some (x12, rdy, x2, sus) ->
    EcbMod.get els x = Some (absmutexsem x8 (Some (x9, x10)), x7) -> 
    NO_NEST_PENDING (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, m, sus))
                    (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7)) ->
    NO_NEST_PENDING tls els.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set tls ct (x12, wait (os_stat_mutexsem x) x0, m, sus)) t <> None).
  destruct (tidspec.beq ct t) eqn : eq1.
  rewrite TcbMod.set_a_get_a; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  assert(IS_OWNER t qid (EcbMod.set els x (absmutexsem x8 (Some (x9, x10)), ct :: x7))).
  unfolds in H3; mytac.
  destruct (tidspec.beq x qid) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H0 in H3; inverts H3.
  unfolds.
  rewrite EcbMod.set_a_get_a; auto.
  eauto.
  unfolds.
  rewrite EcbMod.set_a_get_a'; eauto.

  lets Hx: H1 H4 H5. simpljoin. splits; auto.
  intro; apply H6; mytac.
  unfolds in H8; mytac.
  unfolds.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  do 4 eexists; rewrite EcbMod.set_a_get_a.
  rewrite H0 in H8; inverts H8.
  split; eauto.
  destruct (tidspec.beq t ct) eqn : eq2.
  pose proof tidspec.beq_true_eq _ _ eq2; substs.
  simpl; auto.
  simpl; right; auto.
  eauto.
  do 4 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  intro; apply H7; simpljoin. 
  exists x1.
  split; auto.
  unfolds in H9; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a; auto.
  rewrite H9 in H0; inverts H0; eauto.

  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.
Qed.

Lemma pend_lift_getop_t:
  forall tls ct x10 x13 x2 x12 x14 x15 x11 x x8 x9 t p_t els x0 st sus sus',
    t<> ct ->
    t<> x10 ->
    TcbMod.get tls ct = Some (x13, st, x2, sus) ->
    TcbMod.get tls x10 = Some (x12, x14, x15, sus') ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) ->
    GET_ORP t
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2, sus)) x10
              (x9, x14, x15, sus'))
           (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) p_t ->
    GET_ORP t tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2, sus))
            x10 (x9, x14, x15, sus'))
         t <> None).
  rewrite TcbMod.set_a_get_a'; auto.
  rewrite TcbMod.set_a_get_a'; auto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
  
  lets Hx: H4 H6; destruct Hx; mytac.
  left.
  unfolds in H7; mytac.
  destruct (tidspec.beq x x1) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H7; auto.
  inverts H7; exists x1; unfolds; do 2 eexists; eauto.
  rewrite EcbMod.set_a_get_a' in H7; auto.
  exists x1; unfolds; do 2 eexists; eauto.

  right.
  split.
  intro; apply H7; mytac.
  exists x5.
  unfolds in H9; mytac.
  destruct (tidspec.beq x x5) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H9 in H3; inverts H3.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a; auto.
  unfolds; do 3 eexists; rewrite EcbMod.set_a_get_a'; eauto.

  rewrite TcbMod.set_a_get_a' in H8.
  rewrite TcbMod.set_a_get_a' in H8.
  eauto.
  apply tidspec.neq_beq_false; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma pend_lift_getop_ct:
  forall (tls : TcbMod.map) (ct x10 : tidspec.A) 
         (x13 : priority) (x2 : msg) (x12 : priority) 
         (x14 : taskstatus) (x15 : msg) (x11 : int32) 
         (x : tidspec.A) (x8 : waitset) (x9 : int32) 
         (p_t : int32) (els : EcbMod.map) 
         x0 (st : taskstatus) sus sus',
    x10 <> ct ->
    TcbMod.get tls ct = Some (x13, st, x2, sus) ->
    TcbMod.get tls x10 = Some (x12, x14, x15, sus') ->
    EcbMod.get els x = Some (absmutexsem x9 (Some (x10, x11)), x8) ->
    GET_ORP ct
           (TcbMod.set
              (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2, sus)) x10
              (x9, x14, x15, sus'))
           (EcbMod.set els x (absmutexsem x9 (Some (x10, x11)), ct :: x8)) p_t ->
    GET_ORP ct tls els p_t.
Proof.
  intros.
  unfolds; intros.
  assert(TcbMod.get (TcbMod.set
            (TcbMod.set tls ct (x13, wait (os_stat_mutexsem x) x0, x2, sus)) x10
            (x9, x14, x15, sus')) ct <> None).
  rewrite TcbMod.set_a_get_a'.
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
  apply H3 in H5; clear H3; destruct H5; mytac.
  left.
  unfolds in H3; mytac.
  destruct (tidspec.beq x x1) eqn: eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H3; auto; inverts H3; tryfalse.
  rewrite EcbMod.set_a_get_a' in H3; auto.
  exists x1; unfolds; eauto.

  right.
  split.
  intro; apply H3.
  destruct H6; unfolds in H6; mytac.
  destruct(tidspec.beq x x5) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite H6 in H2; inverts H2; tryfalse.
  exists x5; unfolds; rewrite EcbMod.set_a_get_a'; eauto.
  rewrite TcbMod.set_a_get_a' in H5.
  rewrite TcbMod.set_a_get_a in H5.
  inverts H5; eauto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_lift_get_op_ct:
  forall Ox els tls x x5 ct x0 x1 p_ct sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x0)), nil) ->
    TcbMod.get tls ct = Some (x5, rdy, x1, sus) ->
    GET_ORP ct (TcbMod.set tls ct (x0, rdy, x1, sus))
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_ct ->
    p_ct = x0.
Proof.
  intros.
  unfolds in H4.
  assert(TcbMod.get (TcbMod.set tls ct (x0, rdy, x1, sus)) ct <> None).
  rewrite TcbMod.set_a_get_a; auto; apply tidspec.eq_beq_true; auto.
  apply H4 in H5; clear H4.
  destruct H5; mytac.
  unfolds in H.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inversion H4.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  false; apply H8.
  exists x2. splits; auto. 
  apply tidspec.beq_false_neq; auto.
  unfolds.
  eauto.

  rewrite TcbMod.set_a_get_a in H5; inverts H5; auto.
  apply tidspec.eq_beq_true; auto.
Qed.

Lemma post_lift_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3 sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), nil) ->
    TcbMod.get tls ct = Some (x5, rdy, x1, sus) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 None, nil)) ->
    x3 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  intro; substs; apply H8.
  exists x0. splits; auto.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.


Lemma post_nolift_get_op_ct:
  forall Ox els tls x x5 x0 ct x1 p_ct sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, x0)), nil) ->
    TcbMod.get tls ct = Some (x0, rdy, x1, sus) ->
    GET_ORP ct tls
           (EcbMod.set els x (absmutexsem x5 None, nil)) p_ct ->
    p_ct = x0.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H4.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  unfolds in Hx.
  assert (IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6.
  apply H4 in H5; clear H4.
  unfolds in H6; mytac.
  destruct H5; mytac.
  unfolds in H5; mytac.
  destruct (tidspec.beq x x6) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H5; auto; inversion H5.
  false; apply H7.
  exists x6. simpljoin. splits; auto.  
  apply tidspec.beq_false_neq; auto.
  unfolds.
  rewrite EcbMod.set_a_get_a' in H5; eauto.

  rewrite H3 in H8; inverts H8.
  auto.
Qed.


Lemma post_no_lift_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3 sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), nil) ->
    TcbMod.get tls ct = Some (p_ct, rdy, x1, sus) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 None, nil)) ->
    x3 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H4.
  unfolds in Hx.
  assert (TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert (IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H6; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto; inversion H4.
  intro; substs.
  apply H8.
  exists x0. simpljoin. splits; auto.
  apply tidspec.beq_false_neq; auto.
  rewrite EcbMod.set_a_get_a' in H4; auto.
  unfolds; eauto.
Qed.

Lemma post_lift_exwt_get_op_ct:
  forall (Ox : OSAbstMod.map) (els : EcbMod.map) 
         (tls : TcbMod.map) (x : tidspec.A) (x6 : int32) 
         (ct : tid) (x0 : int32) (x1 : msg) (p_ct : int32) x12 x7 x11 x5 sus sus',
    x12 <> ct ->
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x0)), x11) ->
    TcbMod.get tls ct = Some (x5, rdy, x1, sus) ->
    GET_ORP ct
           (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1, sus)) x12 (x7, rdy, Vnull, sus'))
           (EcbMod.set els x
                       (absmutexsem x6 (Some (x12, x7)), remove_tid x12 x11)) p_ct -> 
    p_ct = x0.
Proof.
  intros.
  lets Hx:H0 H1 H2.
  unfolds in H5.
  unfolds in Hx.
  assert (TcbMod.get
         (TcbMod.set (TcbMod.set tls ct (x0, rdy, x1, sus)) x12 (x7, rdy, Vnull, sus'))
         ct <> None ).
  rewrite TcbMod.set_a_get_a'.
  rewrite TcbMod.set_a_get_a; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
  apply H5 in H6; clear H5.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H7.
  destruct H6; mytac.
  unfolds in H6; mytac.
  destruct (tidspec.beq x x2) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H6; auto.
  inverts H6; tryfalse.

  rewrite EcbMod.set_a_get_a' in H6; auto.
  false; apply H9; exists x2. simpljoin. splits; auto.  
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.

  rewrite TcbMod.set_a_get_a' in H10.
  rewrite TcbMod.set_a_get_a in H10.
  inverts H10; auto.
  apply tidspec.eq_beq_true; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_lift_exwt_ct_nowner:
  forall Ox els tls x x5 ct x0 x1 p_ct x3 x12 x7 x11 sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x5 (Some (ct, p_ct)), x11) ->
    TcbMod.get tls ct = Some (x5, rdy, x1, sus) ->
    IS_OWNER x3 x0 (EcbMod.set els x (absmutexsem x5 (Some (x12, x7)), remove_tid x12 x11)) -> x12 <> ct ->
    x3 <> ct.
Proof.
  intros.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7; mytac.
  intro; substs.
  apply H9.
  exists x0. simpljoin. splits; auto. 
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.

Lemma post_nolift_exwt_get_op_ct:
  forall Ox els tls x ct p_ct x11 x12 x13 x6 x7 x8 x9 sus sus',
    x13 <> ct ->
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x9)), x12) ->
    TcbMod.get tls ct =  Some (x8, rdy, x11, sus) ->
    GET_ORP ct (TcbMod.set tls x13 (x7, rdy, Vnull, sus'))
           (EcbMod.set els x
                       (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12)) p_ct ->
    p_ct = x8.
Proof.
  intros.
  lets Hx: H0 H1 H2.
  unfolds in H5.
  assert(TcbMod.get (TcbMod.set tls x13 (x7, rdy, Vnull, sus')) ct <> None).
  rewrite TcbMod.set_a_get_a'.
  rewrite H4; auto.
  apply tidspec.neq_beq_false; auto.
  apply H5 in H6; clear H5.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H4; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H5 H7.
  destruct H6; mytac.
  unfolds in H6; mytac.
  destruct(tidspec.beq x x0) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H6; auto.
  inverts H6; tryfalse.

  rewrite EcbMod.set_a_get_a' in H6; auto.
  false; apply H9; exists x0. simpljoin. splits; auto. 
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.

  rewrite TcbMod.set_a_get_a' in H10.
  rewrite H4 in H10; inverts H10; auto.
  apply tidspec.neq_beq_false; auto.
Qed.

Lemma post_nolift_exwt_ct_nowner:
  forall Ox els tls x x3 ct x0 p_ct x13 x6 x7 x12 x11 sus,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, p_ct)), x12) ->
    TcbMod.get tls ct = Some (p_ct, rdy, x11, sus) ->
    IS_OWNER x3 x0  (EcbMod.set els x
                                (absmutexsem x6 (Some (x13, x7)), remove_tid x13 x12))->  x13 <> ct ->
    x3 <> ct.
Proof.
  intros.
  unfolds in H4; mytac.
  destruct (tidspec.beq x x0) eqn :eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.set_a_get_a in H4; auto.
  inverts H4; auto.

  rewrite EcbMod.set_a_get_a' in H4; auto.
  lets Hx: H H0 H1.
  unfolds in Hx.
  assert(TcbMod.get tls ct <> None).
  rewrite H3; auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7; mytac.
  intro; substs.
  apply H9.
  exists x0; simpljoin. splits; auto.
  apply tidspec.beq_false_neq; auto.
  unfolds; eauto.
Qed.

Lemma post_ex_wait_ct_neq:
  forall Ox els tls x x6 ct x8 x11 x12,
    NO_NEST_PENDING_O Ox ->
    OSAbstMod.get Ox absecblsid = Some (absecblist els) ->
    OSAbstMod.get Ox abtcblsid = Some (abstcblist tls) ->
    EcbMod.get els x = Some (absmutexsem x6 (Some (ct, x8)), x11) ->
    GetHWait tls x11 x12 ->
    x12 <> ct.
Proof.
  intros.
  lets Hx: H H0 H1.
  unfolds in H3.
  unfolds in Hx.
  mytac; intro; substs.
  assert(get tls ct <> None).
  unfolddef.
  unfold get.
  simpl.
  unfold get in H4.
  simpl in H4.
  rewrite H4;auto.
  assert(IS_OWNER ct x els).
  unfolds; eauto.
  lets Hx1: Hx H6 H7.
  mytac.
  apply H8.
  unfolds.
  do 4 eexists.
  mytac; eauto.
Qed.

Lemma set_getop_eq:
          forall ct tls x4 x3 x6 x7 p_ct x0 x1 sus,
            TcbMod.get tls ct = Some (p_ct, x0, x1, sus) ->
            EcbMod.get x4 x3 = Some (absmutexsem x6 None, x7) ->
            GET_ORP ct tls (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, p_ct)), x7)) p_ct ->
            NO_NEST_PENDING tls
                            (EcbMod.set x4 x3 (absmutexsem x6 (Some (ct, p_ct)), x7)) ->
            GET_ORP ct tls x4 p_ct.
Proof.
  intros.
  rename H2 into Hnonest.
  unfolds in H1.
  unfolds;intros.
  apply H1 in H2.
  clear H1.
  destruct H2.
  right.
  split;eauto.
  eapply no_nest_pending_set_none;eauto.
  right;split;eauto.
  eapply no_nest_pending_set_none;eauto.
Qed.

Lemma get_orp_cre_act:
forall t tls x2 x0 x p,
 EcbMod.get x2 x0 = None ->
 GET_ORP t tls (set x2 x0 (absmutexsem x None, nil)) p ->
 GET_ORP t tls x2 p.
Proof.
  intros.
  unfold GET_ORP in *.
  intros.
  eapply H0 in H1; eauto.
  destruct H1.
  mytac.
  unfolds in H1.
  mytac.
  assert(Hr: x0 = x1 \/ x0 <> x1) by tauto.
  destruct Hr; subst.
  rewrite EcbMod.set_a_get_a in H1;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H1.
  rewrite EcbMod.set_a_get_a' in H1;[ | apply tidspec.neq_beq_false;auto];auto.
  left; eexists; unfolds; eauto.
  
(*not_ow*)
  mytac.
  right; splits; eauto.
  intro.
  eapply H1.
  mytac.
  exists x5.
  unfold IS_OWNER in *.
  mytac.
  assert(Hr: x0 = x5 \/ x0 <> x5) by tauto.
  destruct Hr; subst.
  rewrite H in H3; inverts H3.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto.
  eauto.
Qed.

Lemma is_not_owner_cre_act:
forall x2 x0 ct x,
 EcbMod.get x2 x0 = None ->
 IS_NOT_OWNER ct (set x2 x0 (absmutexsem x None, nil)) ->
 IS_NOT_OWNER ct x2.
Proof.
  intros.
  unfold IS_NOT_OWNER in *.
  intro.
  eapply H0.
  unfold IS_OWNER in *.
  mytac.
  exists x1.
  assert(Hr: x0 = x1 \/ x0 <> x1) by tauto. 
  destruct Hr; subst.
  rewrite H in H1; tryfalse.
  rewrite EcbMod.set_a_get_a';[ | apply tidspec.neq_beq_false;auto];auto.
  eauto.
Qed.

Lemma st_wait_t_cre_act:
forall t x2 x0 x,
 ST_WAIT_T t (set x2 x0 (absmutexsem x None, nil)) ->
 ST_WAIT_T t x2.
Proof.
  intros.
  unfold ST_WAIT_T in *.
  mytac.
  assert(Hr: x0 = x1 \/ x0 <> x1) by tauto.
  destruct Hr; subst.
  rewrite EcbMod.set_a_get_a in H;[ | apply tidspec.eq_beq_true;auto];auto.
  inverts H; tryfalse.
  rewrite EcbMod.set_a_get_a' in H;[ | apply tidspec.neq_beq_false;auto];auto.
  do 4 eexists; eauto.
Qed.

Lemma st_wait_t_del_hold:
  forall t x4 x3 x6 x7 els,
    EcbMod.join els (EcbMod.sig x3 (absmutexsem x6 x7, nil)) x4 ->
    ST_WAIT_T t els ->
    ST_WAIT_T t x4.
Proof.
  intros.
  unfolds in H0; mytac.
  pose proof H x.
  rewrite H0 in H2.
  destruct (tidspec.beq x3 x) eqn : eq1.
  pose proof tidspec.beq_true_eq _ _ eq1; substs.
  rewrite EcbMod.get_sig_some in H2; tryfalse.
  rewrite EcbMod.get_sig_none in H2.
  destruct (EcbMod.get x4 x) eqn: eq2; tryfalse.
  inverts H2.
  unfolds; do 4 eexists; eauto.
  apply tidspec.beq_false_neq; auto.
Qed.

Lemma joinsig_neq_get:
  forall x y els els0 s eid,
    eid <> x ->
    EcbMod.get els0 eid = s ->
    EcbMod.joinsig x y els els0 ->
    EcbMod.get els eid = s.
Proof.
  intros.
  pose proof H1 eid.
  rewrite EcbMod.get_sig_none in H2; auto.
  destruct (EcbMod.get els eid);
  destruct (EcbMod.get els0 eid); tryfalse; substs; auto.
Qed.

Lemma ecb_joinsig_get_eq:
  forall x6 x3 x4 els x8 a0 x9 x x5,
    EcbMod.joinsig x6 (absmutexsem x3 x5, nil) x4 els ->
    EcbMod.get x4 x = Some (absmutexsem x9 a0, x8) ->
    EcbMod.get els x = Some (absmutexsem x9 a0, x8).
Proof.
  intros.
  unfolds in H; pose proof H x.
  rewrite H0 in H1.
  destruct(EcbMod.get (EcbMod.sig x6 (absmutexsem x3 x5, nil)) x); tryfalse.
  destruct(EcbMod.get els x); tryfalse.
  rewrite H1; auto.
Qed.
