(* add by CNU *)
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

Lemma RLH_PortPtrINecb_sem_issem: 
forall dplptr dpl dpptrl els x i wl,
  is_sem els x ->
  RLH_PortPtrINecb dplptr dpl dpptrl els ->
  RLH_PortPtrINecb dplptr dpl dpptrl (set els x (abssem i, wl)).
Proof.
  unfold RLH_PortPtrINecb. 
  unfold is_sem.
  intros.
  destruct  H0; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H1 _ H2).
  simpljoin1.
  exists x1.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x x0) eqn:?;[ | auto].
  apply tidspec.beq_true_eq in Heqb.
  subst.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H1.
  rewrite H in H1.
  inverts H1.
Qed.

Lemma PartitionInv_set_issem_frm : forall els x i w P,
  is_sem els x ->
  PartitionInv els ** P ==> PartitionInv (set els x (abssem i, w)) ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  apply RLH_PortPtrINecb_sem_issem; eauto.
  eauto. eauto.
Qed.

Lemma RLH_PortPtrINecb_set_none : 
  forall dplptr dpl dpptrl els x ecb,
  get els x = None ->
  RLH_PortPtrINecb dplptr dpl dpptrl els ->
  RLH_PortPtrINecb dplptr dpl dpptrl ((* EcbMod. *)set els x ecb).
Proof.
  unfold RLH_PortPtrINecb. 
  intros.
  destruct H0; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H1 _ H2).
  simpljoin1.
  exists x1.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x x0) eqn:?;[ | auto].
  apply tidspec.beq_true_eq in Heqb.
  subst.
  apply nindom_get_rev in H.
  unfold indom in H.
  exfalso.
  apply H.
  eexists;eauto.
Qed.

Lemma PartitionInv_set_none_frm : forall els x ecb P ,
  get els x = None ->
  PartitionInv els ** P ==> PartitionInv (set els x ecb) ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  apply RLH_PortPtrINecb_set_none; eauto.
  eauto. eauto.
Qed.

Lemma RLH_PortPtrINecb_set_notsem_mutex : 
forall dplptr dpl dpptrl els x i o w,
  is_mux els x ->
  RLH_PortPtrINecb dplptr dpl dpptrl els ->
  RLH_PortPtrINecb dplptr dpl dpptrl (set els x  (absmutexsem i o, w)).
Proof.
  unfold RLH_PortPtrINecb. 
  unfold is_sem, is_mux.
  intros.
  destruct H0; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H1 _ H2).
  simpljoin1.
  exists x1.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x x0) eqn:?;[ | auto].
  apply tidspec.beq_true_eq in Heqb.
  subst.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H1.
  rewrite H in H1.
  tryfalse.
Qed.

Lemma PartitionInv_set_mutex_frm : 
  forall els x i o w P ,
  is_mux els x ->
  PartitionInv els ** P ==> PartitionInv (set els x (absmutexsem i o, w)) ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  apply RLH_PortPtrINecb_set_notsem_mutex; eauto.
  eauto. eauto.
Qed.


Lemma RLH_PortPtrINecb_set_notsem_queue : 
forall dplptr dpl dpptrl els x y z p w,
  is_que els x ->
  RLH_PortPtrINecb dplptr dpl dpptrl els ->
  RLH_PortPtrINecb dplptr dpl dpptrl (set els x  (absmsgq y z p, w)).
Proof.
  unfold RLH_PortPtrINecb. 
  unfold is_sem.
  intros.
  destruct H0; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H1 _ H2).
  simpljoin1.
  exists x1.
  erewrite EcbMod.set_sem.
  destruct (tidspec.beq x x0) eqn:?;[ | auto].
  apply tidspec.beq_true_eq in Heqb.
  subst.
  unfold is_que in H.
  do 4 destruct H.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H1.
  rewrite H in H1.
  tryfalse.
Qed.

Lemma PartitionInv_set_queue_frm :
  forall els x y z p w P ,
   is_que els x ->
  PartitionInv els ** P ==> PartitionInv (set els x (absmsgq y z p, w)) ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  apply RLH_PortPtrINecb_set_notsem_queue; eauto.
  eauto. eauto.
Qed.

Lemma RLH_PortPtrINecb_sem_merge : forall dplptr dpl dpptrl els els0 x i w (* ecb *),
  get els x = Some (abssem i, w) ->
  join els0 (sig x (abssem i, w)) els ->
  RLH_PortPtrINecb dplptr dpl dpptrl els ->
  RLH_PortPtrINecb dplptr dpl dpptrl els0.
Proof.
  unfold RLH_PortPtrINecb. 
  intros.
  destruct H1; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H2 _ H3).
  simpljoin1.
  exists x1.
  eapply ecbmod_get_join_get;eauto.
  unfold not;intros; subst.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H2.
  rewrite H in H2.
  tryfalse.
Qed.

Lemma PartitionInv_sem_merge_frm : forall els els0 x i w (* ecb *) P,
  get els x = Some (abssem i, w) ->
  join els0 (sig x (abssem i, w)) els ->
  PartitionInv els ** P ==> PartitionInv els0 ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  eapply RLH_PortPtrINecb_sem_merge; eauto.
  eauto. eauto.
Qed.

Lemma RLH_PortPtrINecb_mutex_merge : forall dplptr dpl dpptrl els els0 x i o w,
  get els x = Some  (absmutexsem i o, w) ->
  join els0 (sig x (absmutexsem i o, w)) els ->
  RLH_PortPtrINecb  dplptr dpl dpptrl els ->
  RLH_PortPtrINecb  dplptr dpl dpptrl els0.
Proof.
  unfold RLH_PortPtrINecb. 
  intros.
  destruct H1; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H2 _ H3).
  simpljoin1.
  exists x1.
  eapply ecbmod_get_join_get;eauto.
  unfold not;intros; subst.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H2.
  rewrite H in H2.
  tryfalse.
Qed.

Lemma PartitionInv_mutex_merge_frm : forall els els0 x i o w (* ecb *) P,
  get els x = Some (absmutexsem i o, w) ->
  join els0 (sig x (absmutexsem i o, w)) els ->
  PartitionInv els ** P ==> PartitionInv els0 ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  eapply RLH_PortPtrINecb_mutex_merge; eauto.
  eauto. eauto.
Qed.

Lemma RLH_PortPtrINecb_queue_merge : forall dplptr dpl dpptrl els els0 x y z p w,
  get els x = Some  (absmsgq y z p, w) ->
  join els0 (sig x (absmsgq y z p, w)) els ->
  RLH_PortPtrINecb  dplptr dpl dpptrl els ->
  RLH_PortPtrINecb  dplptr dpl dpptrl els0.
Proof.
  unfold RLH_PortPtrINecb. 
  intros.
  destruct H1; splits; eauto.
  rewrite Forall_forall in *.
  intros.
  specialize (H2 _ H3).
  simpljoin1.
  exists x1.
  eapply ecbmod_get_join_get;eauto.
  unfold not;intros; subst.
  unfold get, EcbMap in H.
  unfold get, EcbMap in H2.
  rewrite H in H2.
  tryfalse.
Qed.

Lemma PartitionInv_queue_merge_frm : forall els els0 x y z p w P,
  get els x = Some (absmsgq y z p, w) ->
  join els0 (sig x (absmsgq y z p, w)) els ->
  PartitionInv els ** P ==> PartitionInv els0 ** P.
Proof.
  intros.
  unfold PartitionInv in *.
  sep normal;
  sep semiauto.
  eauto. eauto. eauto. eauto.
  eapply RLH_PortPtrINecb_queue_merge; eauto.
  eauto. eauto.
Qed.


Ltac cancel_partitioninv  :=
      match goal with 
      | H: ?s |= _  |- ?s |= _ =>  sep name lift PartitionInv in H
      end;
      match goal with 
      | H: ?s |= PartitionInv ?els ** ?P |- context [PartitionInv (?f ?els ?x (abssem ?i, ?wl))] =>
          (eapply (PartitionInv_set_none_frm els x ((abssem i, wl))) in H;[sep cancel PartitionInv | solve [auto]]) ||
          (eapply (PartitionInv_set_issem_frm els x i wl) in H;[sep cancel PartitionInv | solve [unfold is_sem;do 2 eexists;eauto]])
      | H: ?s |= PartitionInv ?els ** ?P |- context [PartitionInv (?f ?els ?x  (absmutexsem ?i ?o, ?w))] =>
          (eapply (PartitionInv_set_none_frm els x (absmutexsem i o, w)) in H;[sep cancel PartitionInv | solve [auto]]) ||
          (eapply (PartitionInv_set_mutex_frm els x i o w) in H;[sep cancel PartitionInv | solve [unfold is_mux ;do 3 eexists;eauto]]) 
      | H: ?s |= PartitionInv ?els ** ?P |- context [PartitionInv (?f ?els ?x (absmsgq ?y ?z ?p, ?w))] =>
          (eapply (PartitionInv_set_none_frm els x (absmsgq y z p, w)) in H;[sep cancel PartitionInv | solve [auto]]) || 
          (eapply (PartitionInv_set_queue_frm els x y z p w) in H;[sep cancel PartitionInv | try solve [unfold is_que ;do 4 eexists;eauto]] )
      | H: ?s |= PartitionInv ?els ** ?P, H0 : ?fjoin ?els0 (?fsig ?x (?abssem ?i, ?w)) ?els
         |- context [PartitionInv ?els0] =>
          (eapply (PartitionInv_sem_merge_frm els els0 x i w) in H;[sep cancel PartitionInv | auto | auto])
      | H: ?s |= PartitionInv ?els ** ?P, H0 : ?fjoin ?els0 (?fsig ?x (?absmutexsem ?i ?o, ?w)) ?els
         |- context [PartitionInv ?els0] =>
          (eapply (PartitionInv_mutex_merge_frm els els0 x i o w) in H;[sep cancel PartitionInv | auto | auto])
      | H: ?s |= PartitionInv ?els ** ?P, H0 : ?fjoin ?els0 (?fsig ?x (?absmsgq ?y ?z ?p, ?w)) ?els
         |- context [PartitionInv ?els0] =>
          (eapply (PartitionInv_queue_merge_frm els els0 x y z p w) in H;[sep cancel PartitionInv | auto | auto])
      | H: ?s |= PartitionInv ?els ** ?P
         |- context [PartitionInv ?els] => sep cancel PartitionInv
      end.


(* end add by CNU *)