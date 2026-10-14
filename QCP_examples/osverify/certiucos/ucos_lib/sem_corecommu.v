(* add by SJTU *)
Require Import sem_common.
Require Import ifun_spec.

Open Scope code_scope.

  
Local Ltac find_name' n x Hp :=
  match Hp with
    | ?A ** ?B =>
          match A with
          | context[x] => constr:(n)
          | _ => find_name' (S n) x B
          end
   | context[x] =>constr:(n)
   | _ => constr : (1%nat)
   end.

Ltac find_name x Hp :=
 let y := find_name' 1%nat x Hp in
 eval compute in y.

Tactic Notation "sep" "name" "lift" constr(x) "in" hyp (H):=
  match type of H with
  | sat _ ?P => let n:= find_name x P in
                          sep lift n in H
  | _ =>idtac
  end.
  
Lemma CORESEM_INECB_P_set_issem : forall els x i wl,
  CORESEM_INECB_P els ->
  CORESEM_INECB_P (EcbMod.set els x (abssem i, wl)).
Proof.
  unfold CORESEM_INECB_P;intros * [? [ ? ?]].
  splits;intros;unfold is_sem.
  - specialize (H _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid);[eexists; eauto | auto].
  - specialize (H0 _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid);[eexists; eauto | auto].
  - erewrite EcbMod.set_sem.
    destruct (tidspec.beq x OSSemShared_val);[eexists; eauto | auto].
Qed.


Lemma CoreCommuInv_set_issem_frm : forall els x i wl P ,
  is_sem els x ->
  CoreCommuInv els ** P ==> CoreCommuInv (set els x (abssem i, wl)) ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  apply CORESEM_INECB_P_set_issem;auto.
  unfold is_que, is_sem in *.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x dynrefcmsgQ_addr) eqn:?.
  { apply tidspec.beq_true_eq in Heqb.
    subst.
    destruct H2 as [? [? [? [? ?]]]].
    destruct H as [? [? ?]].
    rewrite H in H2.
    inverts H2. }
  eauto.
Qed.


Lemma CORESEM_INECB_P_set_notsem : forall els x ecb,
  ~ is_sem els x ->
  CORESEM_INECB_P els ->
  CORESEM_INECB_P (EcbMod.set els x ecb).
Proof.
  unfold CORESEM_INECB_P;intros * Hnot [? [ ? ?]].
  splits;intros;unfold is_sem.
  - specialize (H _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    contradiction.
  - specialize (H0 _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    contradiction.
  - erewrite EcbMod.set_sem.
    destruct (tidspec.beq x OSSemShared_val) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    contradiction.
Qed.

Lemma CoreCommuInv_set_notsemq_frm : forall els x ecb P ,
  ~ is_sem els x -> ~ is_que els x ->
  CoreCommuInv els ** P ==> CoreCommuInv (set els x ecb) ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  apply CORESEM_INECB_P_set_notsem;auto.
  unfold is_que in *.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x dynrefcmsgQ_addr) eqn:?.
  { apply tidspec.beq_true_eq in Heqb.
    subst.
    exfalso.
    apply H0.
    auto. }
  eauto.
Qed.

Lemma CORESEM_INECB_P_set_none : forall els x ecb,
  get els x = None ->
  CORESEM_INECB_P els ->
  CORESEM_INECB_P (EcbMod.set els x ecb).
Proof.
  unfold CORESEM_INECB_P;intros * Hnone [? [ ? ?]].
  splits;intros;unfold is_sem.
  - specialize (H _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    destruct H as [? [? ?]].
    apply nindom_get_rev in Hnone.
    unfold indom in Hnone.
    exfalso.
    apply Hnone.
    eexists;eauto.
  - specialize (H0 _ H2).
    erewrite EcbMod.set_sem.
    destruct (tidspec.beq x eid) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    destruct H0 as [? [? ?]].
    apply nindom_get_rev in Hnone.
    unfold indom in Hnone.
    exfalso.
    apply Hnone.
    eexists;eauto.
  - erewrite EcbMod.set_sem.
    destruct (tidspec.beq x OSSemShared_val) eqn:?;[ | auto].
    apply tidspec.beq_true_eq in Heqb.
    subst.
    destruct H1 as [? [? ?]].
    apply nindom_get_rev in Hnone.
    unfold indom in Hnone.
    exfalso.
    apply Hnone.
    eexists;eauto.
Qed.

Lemma CoreCommuInv_set_none_frm : forall els x ecb P ,
  get els x = None ->
  CoreCommuInv els ** P ==> CoreCommuInv (set els x ecb) ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  apply CORESEM_INECB_P_set_none;eauto.
  unfold is_que, is_sem in *.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x dynrefcmsgQ_addr) eqn:?.
  { apply tidspec.beq_true_eq in Heqb.
    subst.
    destruct H2 as [? [? [? [? ?]]]].
    rewrite H in H2.
    inverts H2. }
  eauto.
Qed.

Lemma CoreCommuInv_set_mutex_frm : forall els x i o w P ,
  is_mux els x ->
  CoreCommuInv els ** P ==> CoreCommuInv (set els x (absmutexsem i o, w)) ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  apply CORESEM_INECB_P_set_notsem;auto.
  { unfold is_mux, is_sem, not in *;intros.
    do 3 destruct H.
    do 2 destruct H8.
    rewrite H in H8.
    inverts H8.
  }
  unfold is_que, is_mux in *.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x dynrefcmsgQ_addr) eqn:?.
  { apply tidspec.beq_true_eq in Heqb.
    subst.
    do 3 destruct H.
    do 4 destruct H2.
    rewrite H in H2.
    inverts H2. }
  eauto.
Qed.

Lemma CoreCommuInv_set_queue_frm : forall els x y z p w P ,
  is_que els x ->
  CoreCommuInv els ** P ==> CoreCommuInv (set els x (absmsgq y z p, w)) ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  apply CORESEM_INECB_P_set_notsem;auto.
  { unfold is_que, is_sem, not in *;intros.
    do 4 destruct H.
    do 2 destruct H8.
    rewrite H in H8.
    inverts H8.
  }
  unfold is_que in *.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x dynrefcmsgQ_addr) eqn:?.
  eauto.
  eauto.
Qed.


Lemma CORESEM_INECB_P_merge : forall els els0 x ecb,
  notIncoreSemQ x ->
  join els0 (sig x ecb) els ->
  CORESEM_INECB_P els ->
  CORESEM_INECB_P els0.
Proof.
  unfold CORESEM_INECB_P;intros * Hnotin Hj [? [ ? ?]].
  splits;intros;unfold is_sem.
  - specialize (H _ H2) as [? [? ?]]. 
    exists x0 x1.
    eapply ecbmod_get_join_get;eauto.
    unfold not;intros; subst.
    unfold notIncoreSemQ in Hnotin.
    destruct Hnotin.
    contradiction.
  - specialize (H0 _ H2) as [? [? ?]]. 
    exists x0 x1.
    eapply ecbmod_get_join_get;eauto.
    unfold not;intros; subst.
    unfold notIncoreSemQ in Hnotin.
    destruct Hnotin as [? [? ?]].
    contradiction.
  - destruct H1 as [? [? ?]].
    exists x0 x1.
    eapply ecbmod_get_join_get;eauto.
    unfold not;intros; subst.
    unfold notIncoreSemQ in Hnotin.
    destruct Hnotin as [? [? [? ?]]].
    contradiction.
Qed.

Lemma CoreCommuInv_merge_frm : forall els els0 x ecb P,
  notIncoreSemQ x ->
  join els0 (sig x ecb) els ->
  CoreCommuInv els ** P ==> CoreCommuInv els0 ** P.
Proof.
  intros.
  unfold CoreCommuInv, DynamicRefactorINV in *.
  sep normal;
  sep semiauto.
  eapply CORESEM_INECB_P_merge;eauto.
  destruct H as [? [? [? ?]]].
  unfold is_que in *.
  destruct H3 as [? [? [? [? ?]]]].
  exists x11 x12 x13 x14.
  eapply ecbmod_get_join_get;eauto.
Qed.

Ltac cancel_corecommuinv  :=
      match goal with 
      | H: ?s |= _  |- ?s |= _ =>  sep name lift CoreCommuInv in H
      end;
      match goal with 
      | H: ?s |= CoreCommuInv ?els ** ?P |- context [CoreCommuInv (?f ?els ?x (abssem ?i, ?wl))] =>
          (eapply (CoreCommuInv_set_none_frm els x ((abssem i, wl))) in H;[sep cancel CoreCommuInv | solve [auto]]) ||
          (eapply (CoreCommuInv_set_issem_frm els x i wl) in H;[sep cancel CoreCommuInv | solve [unfold is_sem;do 2 eexists;eauto]])
      | H: ?s |= CoreCommuInv ?els ** ?P |- context [CoreCommuInv (?f ?els ?x  (absmutexsem ?i ?o, ?w))] =>
          (eapply (CoreCommuInv_set_none_frm els x (absmutexsem i o, w)) in H;[sep cancel CoreCommuInv | solve [auto]]) ||
          (eapply (CoreCommuInv_set_mutex_frm els x i o w) in H;[sep cancel CoreCommuInv | solve [unfold is_mux ;do 3 eexists;eauto]]) 
      | H: ?s |= CoreCommuInv ?els ** ?P |- context [CoreCommuInv (?f ?els ?x (absmsgq ?y ?z ?p, ?w))] =>
          (eapply (CoreCommuInv_set_none_frm els x (absmsgq y z p, w)) in H;[sep cancel CoreCommuInv | solve [auto]]) || 
          (eapply (CoreCommuInv_set_queue_frm els x y z p w) in H;[sep cancel CoreCommuInv | try solve [unfold is_que ;do 4 eexists;eauto]] )
      | H: ?s |= CoreCommuInv ?els ** ?P, H0 : ?fjoin ?els0 (?fsig ?x ?ecb) ?els
         |- context [CoreCommuInv ?els0] =>
          eapply (CoreCommuInv_merge_frm els els0 x ecb) in H;[sep cancel CoreCommuInv | auto | auto]
      | H: ?s |= CoreCommuInv ?els ** ?P
         |- context [CoreCommuInv ?els] => sep cancel CoreCommuInv
      end.

(* end add by SJTU *)