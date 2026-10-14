

Require Import base_tac. 
Require Import FunctionalExtensionality.

Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import osspecs. 
Require Import properties.
Require Import if_assms.
Require Import sem_prop.


Require Import equiv_prop.
Require Import if_succ_gen.
(* Require Import abs_op. *)
(* Require Import if_good_code. *)
(* Require Import equiv_sem_prop. *)

Require Import if_common_lemmas.
(* Require Import mqsend_cproof1. *)
(* Require Import mqrecv_cproof1. *)
Require Import spec_aux_defs.
Require Import FunctionalExtensionality.
Require Import hasrt_sat_preserve.
Set Keyed Unification.

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


Lemma join_get_set_eq_4
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' a''' d d' e e',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    get O1 a''' = Some e ->
    join (set (set (set (set O1 a b') a' c') a'' d') a''' e') O2 O' ->
   O' = set (set (set (set O a b') a' c') a'' d') a''' e'.
Proof.
  intros.
  repeat progress(eapply join_set_l_rev in H5; eauto; simpljoin).
  eapply map_join_deter in H0; eauto.
  subst; auto.
Qed.


Definition prio_preserved_d td O O' :=
  forall pr t,
    dom_for_prio pr = td ->
    (task_prio_id O pr t <-> task_prio_id O' pr t). 

Definition prio_preserved O O' :=
  forall td, prio_preserved_d td O O'. 

Lemma tlsused_tls_none:
  forall tls els tls_ els_ tlsused t,
  get tlsused t = None ->
  intspecs.tickstep' tls els tls_ els_ tlsused ->
  get tls t =get tls_ t.
Proof.
introv Hget Hstep.
induction Hstep.
eauto.
casetac t t0 Hte Htne.
subst t0.
assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
eapply get_join_sig_set_rev;eauto.
rewrite H2 in Hget.
rewrite set_a_get_a in Hget.
tryfalse.

assert(tls_used = set tls_used' t0 (p, st, msg0, sus0, pr)).
eapply get_join_sig_set_rev;eauto.
rewrite H2 in Hget.
rewrite set_a_get_a' in Hget;eauto.
lets H': IHHstep Hget.
rewrite <-H'.
rewrite <-H1.
rewrite set_a_get_a';eauto.
Qed.

Lemma join_disj_tcb : 
	forall    M1 M2 M,
 	 TcbMod.join M1 M2 M -> 
 	disjoint M1 M2.
Proof.
  intros.
  unfold disjoint.
  geat.
Qed.

Lemma sig_set_emp_tcb :
  forall  x y ,
    TcbMod.sig x y  = set emp x y.
Proof.
  intros.
  apply eq_sym.
  apply TcbMod.map_set_emp.
Qed.


Lemma tlsused_joinsig:
  forall t p st msg sus pr tls_used tls_used' ,
  TcbMod.joinsig t (p, st, msg, sus, pr) tls_used' tls_used->
  get tls_used' t = None.
Proof.
introv Hjoin.
unfolds in Hjoin.
(* Search join. *)
eapply join_disj_tcb in Hjoin. 
eapply disjoint_sem' in Hjoin; eauto.
destruct Hjoin as [Hjoin|Hjoin].
(* Search sig. *)
rewrite sig_set_emp_tcb in Hjoin.
rewrite set_a_get_a in Hjoin.
tryfalse.
eauto.
Qed.


Lemma tlsused_tls'_prio_preserved:
  forall tls els tls_ els_ t tlsused,
  intspecs.tickstep' tls els tls_ els_ tlsused ->
  (
   (get tlsused t <> None /\ 
   (forall p0,
     (exists p st msg sus, get tls_ t = Some (p, st, msg, sus, p0))
      <-> (exists p st msg sus, get tlsused t = Some (p, st, msg, sus, p0))))
    \/
    (get tlsused t = None /\ 
    (forall p0, 
      (exists p st msg sus, get tls t = Some (p, st, msg, sus, p0))
      <-> (exists p st msg sus, get tls_ t = Some (p, st, msg, sus, p0)))
     )
  ). 
Proof.
introv Hstep.
induction Hstep.
+
  right.
  split. rewrite emp_sem. eauto.
  split.
  -
    introv Hget. eauto.
  -
    introv Hget. eauto.
+ 
  destruct IHHstep as [IHHstep|IHHstep].
  casetac t t0 Hte Htne.
  -
    left. split. introv Hf. subst t0.
    assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto. 
    rewrite H2 in Hf. rewrite set_a_get_a in Hf.
    tryfalse.
    subst t0. split. introv Hget. destruct IHHstep as (Hused' & Hd).
    specialize(Hd p0).
    destruct Hd as (Hd1 & Hd2).
    lets H':Hd1 Hget.
    assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto.
    eapply tlsused_joinsig in H. rewrite H in Hused'.
    tryfalse.

    introv Hget. destruct IHHstep as (Hused & Hd).
    specialize (Hd p0). destruct Hd as (Hd1 & Hd2).
    eapply tlsused_joinsig in H. rewrite H in Hused.
    tryfalse.
  -
    destruct IHHstep as (Hused & Hd).
    left. split. 
    assert(tls_used = set tls_used' t0 (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto.
    introv Hfa. rewrite H2 in Hfa. rewrite set_a_get_a' in Hfa;eauto.
    split.
    introv Hget. specialize (Hd p0). destruct Hd as (Hd1 & Hd2).
    lets H':Hd1 Hget.
    assert(tls_used = set tls_used' t0 (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto.
    rewrite H2. rewrite set_a_get_a';eauto.
    
    introv Hget. specialize(Hd p0).
    destruct Hd as(Hd1 & Hd2).
    assert(tls_used = set tls_used' t0 (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto.
    rewrite H2 in Hget.
    rewrite set_a_get_a' in Hget.
    lets H':Hd2 Hget. eauto. eauto.
  -
    destruct IHHstep as (Hused & Hd).
    casetac t t0 Hte Htne.
    left.
    split. subst t0.
    assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto. rewrite H2.
    rewrite set_a_get_a. introv Hfa;tryfalse.
    split.
    introv Hget. specialize(Hd p0).
    destruct Hd as (Hd1 & Hd2).
    lets H':Hd2 Hget. subst t0.
    assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto. rewrite H2.
    rewrite set_a_get_a. rewrite <-H1 in H'.
    rewrite set_a_get_a in H'.
    simpljoin. inverts H3. do 4 eexists. eauto.

    introv Hget. specialize (Hd p0).
    destruct Hd as(Hd1 & Hd2).
    subst t0. 
    assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto. 
    eapply tlsused_tls_none in Hused;eauto.
    inverts Hused. rewrite H2 in Hget.
    rewrite set_a_get_a in Hget.
    simpljoin.
    rewrite set_a_get_a. inverts H3.
    do 4 eexists. eauto.

    right.
    split. assert(tls_used = set tls_used' t0 (p, st, msg0, sus0, pr)).
    eapply get_join_sig_set_rev;eauto.
    rewrite H2. rewrite set_a_get_a';eauto.

    split. introv Hget. specialize(Hd p0).
    destruct Hd as (Hd1 & Hd2).
    eapply tlsused_tls_none in Hused;eauto.
    rewrite <-Hused. rewrite <-H1.
    rewrite set_a_get_a';eauto.
    
    introv Hget. specialize(Hd p0).
    destruct Hd as(Hd1 & Hd2).
    lets H': Hd2 Hget.
    rewrite <-H1 in H'.
    rewrite set_a_get_a' in H';eauto.
Qed.
    

Lemma tickisr_spec_prio_preserved:
  forall O1 O1'  cd' ,
spec_step (snd (api_spec, int_spec, get_hprio_d)) intspecs.tickisr O1 cd' O1' TauAct->
prio_preserved O1 O1'.
Proof.
lets H': tlsused_tls'_prio_preserved.
intros.
inverts H.
- 
  inverts H7.
  unfolds in H3.
  simpljoin.
  destruct H13.
  +
    simpljoin.
    inverts H23.
    eapply join_get_set_eq_8 in H12;eauto.
    inverts H12. clear H14.
    unfolds in H4.
    unfolds.
    intros.
    unfolds.
    introv Hdom.
    split.
    introv Htpi1.
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    lets H_: H' H4. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    eapply join_get_get_l in H0;eauto.
    rewrite H0 in Hgetabstcblsid.
    inverts Hgetabstcblsid.
    destruct H2_.
    do 4 eexists. eapply Htcbs.
    simpljoin.
    unfolds. do 5 eexists. split. do 6 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a. eauto. eauto.

    destruct H_ as (Hget & H_).
    eapply join_get_get_l in H0;eauto.
    rewrite H0 in Hgetabstcblsid.
    inverts Hgetabstcblsid. rewrite Htcbs in Hget. tryfalse.

    introv Htpi1'.
    unfolds in Htpi1'.
    destruct Htpi1' as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    do 6 (rewrite set_a_get_a' in Hgetabstcblsid;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H4. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H1_.
    do 4 eexists. eapply Htcbs.
    simpljoin.
    eapply join_get_get_l in H0;eauto.
    unfolds. do 5 eexists. split. eauto. eauto.

    destruct H_ as (Hget & H_).
    eapply join_get_get_l in H0;eauto.
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eauto.
    simpljoin. rewrite H12 in Hget. tryfalse.

  +
    simpljoin. inverts H3. eapply join_get_set_eq_4 in H12;eauto.
    inverts H12. clear H3. eapply join_get_get_l in H0;eauto.
    unfolds.
    intros.
    unfolds. introv Hdom. split.
    introv Htpi1. 
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    rewrite H0 in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H4. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eapply Htcbs. simpljoin.
    unfolds. do 5 eexists. split. do 2 (rewrite set_a_get_a' ;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a. eauto. eauto.

    destruct H_ as (Hget & H_). rewrite Htcbs in Hget. tryfalse.

    introv Htpi1. 
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    do 2 (rewrite set_a_get_a' in Hgetabstcblsid ;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H4. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H1_. do 4 eexists. eapply Htcbs. simpljoin.
    unfolds. do 5 eexists. split. eauto. eauto.

    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eauto.
    simpljoin. rewrite H3 in Hget. tryfalse.

-
  inverts H6.
  unfolds in H4. simpljoin.
  destruct H10. simpljoin.
  tryfalse. simpljoin. tryfalse.
-
  inverts H3.
  unfolds in H2.
  simpljoin. destruct H14.
  +
    simpljoin.
    inverts H25.
    eapply join_get_set_eq_8 in H13;eauto.
    inverts H13. clear H15.
    unfolds in H5.
    unfolds.
    intros.
    unfolds.
    introv Hdom.
    split.
    introv Htpi1.
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    lets H_: H' H5. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    eapply join_get_get_l in H0;eauto.
    rewrite H0 in Hgetabstcblsid.
    inverts Hgetabstcblsid.
    destruct H2_.
    do 4 eexists. eapply Htcbs.
    simpljoin.
    unfolds. do 5 eexists. split. do 6 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a. eauto. eauto.

    destruct H_ as (Hget & H_).
    eapply join_get_get_l in H0;eauto.
    rewrite H0 in Hgetabstcblsid.
    inverts Hgetabstcblsid. rewrite Htcbs in Hget. tryfalse.

    introv Htpi1'.
    unfolds in Htpi1'.
    destruct Htpi1' as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    do 6 (rewrite set_a_get_a' in Hgetabstcblsid;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H5. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H1_.
    do 4 eexists. eapply Htcbs.
    simpljoin.
    eapply join_get_get_l in H0;eauto.
    unfolds. do 5 eexists. split. eauto. eauto.

    destruct H_ as (Hget & H_).
    eapply join_get_get_l in H0;eauto.
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eauto.
    simpljoin. rewrite H13 in Hget. tryfalse.

  +
    simpljoin. inverts H3. eapply join_get_set_eq_4 in H13;eauto.
    inverts H13. clear H3. eapply join_get_get_l in H0;eauto.
    unfolds.
    intros.
    unfolds. introv Hdom. split.
    introv Htpi1. 
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    rewrite H0 in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H5. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eapply Htcbs. simpljoin.
    unfolds. do 5 eexists. split. do 2 (rewrite set_a_get_a' ;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a. eauto. eauto.

    destruct H_ as (Hget & H_). rewrite Htcbs in Hget. tryfalse.

    introv Htpi1. 
    unfolds in Htpi1.
    destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabstcblsid & Htcbs).
    do 2 (rewrite set_a_get_a' in Hgetabstcblsid ;[idtac|introv Hfa;tryfalse]).
    rewrite set_a_get_a in Hgetabstcblsid. inverts Hgetabstcblsid.
    lets H_: H' H5. clear H'.
    destruct H_ as [H_|H_].
    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H1_. do 4 eexists. eapply Htcbs. simpljoin.
    unfolds. do 5 eexists. split. eauto. eauto.

    destruct H_ as (Hget & H_).
    specialize (H_ pr).
    destruct H_ as (H1_ & H2_).
    destruct H2_. do 4 eexists. eauto.
    simpljoin. rewrite H3 in Hget. tryfalse.

  +
    unfolds in H7.
    simpljoin.
    destruct H11.
    simpljoin. tryfalse. simpljoin. tryfalse.
Qed.

Lemma tickstep_except_st_preserved:
forall t1 tls1 tls1' els1 els1' tls_used1 pr1 st1 msg1 sus1 pr ,
get tls_used1 t1 = Some (pr1, st1, msg1, sus1, pr)->
intspecs.tickstep' tls1 els1 tls1' els1' tls_used1->
exists st1', get tls1' t1 = Some (pr1, st1', msg1, sus1, pr).
Proof.
introv Hget Hstep.
induction Hstep. rewrite emp_sem in Hget. tryfalse.
 
casetac t t1 Hte Htne.
assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr0)).
eapply get_join_sig_set_rev;eauto.
rewrite H2 in Hget. subst t1. rewrite set_a_get_a in Hget.
inverts Hget. eapply tlsused_joinsig in H.
eapply tlsused_tls_none in H;eauto.
inverts H. rewrite <-H1. rewrite set_a_get_a.
eexists. eauto.

assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr0)).
eapply get_join_sig_set_rev;eauto.
rewrite H2 in Hget. rewrite set_a_get_a' in Hget;eauto.
Qed.


Lemma st_same:
forall t1 st1 els st1' els' t2  els0 st2' els'0,
intspecs.tickchange t1 st1 els st1' els'->
intspecs.tickchange t2 st1 els0 st2' els'0->
st1' = st2'.
Proof.
introv Hc1 Hc2.
inverts Hc1. inverts Hc2.
eauto. repeat(destruct H as [H|H];tryfalse).
repeat(destruct H as [H|H];tryfalse).
destruct H1 as[H1|[H1|[H1|[H1|H1]]]];inverts H1;repeat(destruct H as [H|H];tryfalse).
inverts H. destruct H2. tryfalse.
inverts H. destruct H2. tryfalse.
inverts H. destruct H2. tryfalse.
inverts H. destruct H2. tryfalse.
destruct H0 as[H0|[H0|[H0|H0]]];inverts H0;repeat(destruct H as [H|H];tryfalse).

inverts Hc2.
repeat(destruct H as [H|H];tryfalse).
inverts H. eauto.
inverts H. tryfalse.
destruct H1 as[H1|[H1|[H1|[H1|H1]]]];inverts H1.
inverts H. destruct H2. tryfalse.
inverts H. destruct H2. tryfalse.
inverts H.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H1. inverts H1. inverts H1. inverts H1.

inverts Hc2.
repeat(destruct H as [H|H];tryfalse). 
inverts H. tryfalse. eauto.
destruct H0 as[H0|[H0|[H0|[H0|H0]]]];inverts H0.
inverts H. inverts H. inverts H. inverts H.
inverts H.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H0. inverts H0. inverts H0. inverts H0.

inverts Hc2.
repeat(destruct H as [H|H];tryfalse). 
inverts H. destruct H1. tryfalse.
destruct H0 as[H0|[H0|[H0|[H0|H0]]]];inverts H0.
inverts H. destruct H1. tryfalse.
inverts H. inverts H. inverts H. inverts H.
inverts H. destruct H1. tryfalse.
inverts H. destruct H1. tryfalse.
destruct H0 as[H0|[H0|[H0|[H0|H0]]]];inverts H0.
inverts H. inverts H. inverts H. inverts H.
inverts H. 
destruct H0 as[H0|[H0|[H0|[H0|H0]]]];inverts H0.
inverts H. inverts H. inverts H. inverts H.
inverts H. 
destruct H0 as[H0|[H0|[H0|[H0|H0]]]];inverts H0.
destruct H2 as[H2|[H2|[H2|[H2|H2]]]];inverts H2.
inverts H. eauto. inverts H. inverts H. inverts H.
inverts H. 
destruct H2 as[H2|[H2|[H2|[H2|H2]]]];inverts H2.
inverts H. inverts H. eauto. inverts H. inverts H.
inverts H.
destruct H2 as[H2|[H2|[H2|[H2|H2]]]];inverts H2.
inverts H. inverts H. inverts H. eauto.
inverts H. inverts H.
destruct H2 as[H2|[H2|[H2|[H2|H2]]]];inverts H2.
inverts H. inverts H. inverts H. inverts H. eauto.
inverts H.
destruct H2 as[H2|[H2|[H2|[H2|H2]]]];inverts H2.
inverts H. inverts H. inverts H. inverts H. inverts H.
eauto.

destruct H0 as[H0|[H0|[H0|H0]]];inverts H0.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H2. destruct H1. tryfalse.
inverts H2. inverts H2. inverts H2.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H2. inverts H2. destruct H1. tryfalse.
inverts H2. inverts H2.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H2. inverts H2. inverts H2. destruct H1. tryfalse.
inverts H2.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H2. inverts H2. inverts H2. inverts H2. destruct H1. tryfalse.
destruct H as[H|[H|[H|H]]];inverts H.
inverts H2. inverts H2. inverts H2. inverts H2.

inverts Hc2. 
destruct H as[H|[H|[H|H]]];inverts H.
repeat(destruct H0 as [H0|H0];tryfalse).
repeat(destruct H0 as [H0|H0];tryfalse).
repeat(destruct H0 as [H0|H0];tryfalse).
repeat(destruct H0 as [H0|H0];tryfalse).
inverts H0. tryfalse.
inverts H0. 
destruct H as[H|[H|[H|H]]];inverts H.
destruct H as[H|[H|[H|H]]];inverts H.
destruct H1 as[H1|[H1|[H1|[H1|H1]]]];inverts H1.
inverts H0. destruct H3. tryfalse.
inverts H0. inverts H0. inverts H0. inverts H0.
destruct H1 as[H1|[H1|[H1|[H1|H1]]]];inverts H1.
inverts H0. destruct H3. tryfalse.
inverts H0. tryfalse. inverts H0. inverts H0.
inverts H0.
destruct H1 as[H1|[H1|[H1|H1]]];inverts H1.
inverts H0. inverts H0. inverts H0. destruct H3. tryfalse.
inverts H0. inverts H0. 
destruct H1 as[H1|[H1|[H1|H1]]];inverts H1.
inverts H0. inverts H0. inverts H0. inverts H0. destruct H3. tryfalse.
inverts H0. 
inverts H1.
destruct H as[H|[H|[H|H]]];inverts H.
destruct H0 as[H0|[H0|[H0|H0]]];inverts H0.
eauto. eauto. eauto. eauto.
Qed.



Lemma tickstep_st_same:
forall t1 t2 tls1 els1 tls1' els1' tls2 els2 tls2' els2' pr
        pr1 st1 msg1 sus1 pr2 st2 msg2 sus2 
       st1' st2' pr1' pr2' msg1' msg2' sus1' sus2' tls_used1 tls_used2,
get tls_used1 t1 = Some (pr1, st1, msg1, sus1, pr)->
get tls_used2 t2 = Some (pr2, st2, msg2, sus2, pr)->
pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2->
intspecs.tickstep' tls1 els1 tls1' els1' tls_used1->
intspecs.tickstep' tls2 els2 tls2' els2' tls_used2->
get tls1' t1 = Some (pr1', st1', msg1', sus1', pr)->
get tls2' t2 = Some (pr2', st2', msg2', sus2', pr)->
st1'=st2'.
Proof.
intros.
induction H2.
induction H3.
rewrite emp_sem in H. tryfalse.
rewrite emp_sem in H. tryfalse.

induction H3.
rewrite emp_sem in H0. tryfalse.
casetac t1  t Hte Htne.
subst t. 
assert(tls_used = set tls_used' t1 (p, st, msg0, sus0, pr0)).
eapply get_join_sig_set_rev;eauto.
rewrite H12 in H. rewrite set_a_get_a in H.
inverts H. destruct H1 as (H11' & H12' & H13' & H14').
subst st2.
casetac t2 t0 Hte2 Htne2.
subst t0.
assert(tls_used0 = set tls_used'0 t2 (p0, st0, msg3, sus3, pr3)).
eapply get_join_sig_set_rev;eauto.
rewrite H in H0. rewrite set_a_get_a in H0.
inverts H0. eapply tlsused_joinsig in H3.
eapply tlsused_joinsig in H2.
eapply tlsused_tls_none in H2;eauto.
eapply tlsused_tls_none in H3;eauto.
rewrite <-H2 in H4. rewrite <-H3 in H5.
rewrite <-H7 in H4. rewrite <-H10 in H5.
rewrite set_a_get_a in H4. 
rewrite set_a_get_a in H5.
inverts H4. inverts H5.
lets Hc1:H6. lets Hc2 :H9.
eapply st_same in Hc1;eauto.


assert(tls_used0 = set tls_used'0 t0 (p0, st0, msg3, sus3, pr3)).
eapply get_join_sig_set_rev;eauto.
rewrite H in H0. rewrite set_a_get_a' in H0;eauto.

casetac t2 t0 Hte2 Htne2.
subst t0.
assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr0)).
eapply get_join_sig_set_rev;eauto.
rewrite H12 in H. rewrite set_a_get_a' in H;eauto.

assert(tls_used = set tls_used' t (p, st, msg0, sus0, pr0)).
eapply get_join_sig_set_rev;eauto.
rewrite H12 in H. rewrite set_a_get_a' in H;eauto.
Qed.

Lemma tickisr_tcbs_preserved:
forall t1 t2 tls1 els1 tls1' els1' tls2 els2 tls2' els2' pr
        pr1 st1 msg1 sus1 pr2 st2 msg2 sus2 
       st1' st2' pr1' pr2' msg1' msg2' sus1' sus2' tls_used1 tls_used2,

get tls_used1 t1 = Some (pr1, st1, msg1, sus1, pr)->
get tls_used2 t2 = Some (pr2, st2, msg2, sus2, pr)->
pr1 = pr2 /\ st1 = st2 /\ msg1 = msg2 /\ sus1 = sus2->
intspecs.tickstep' tls1 els1 tls1' els1' tls_used1->
intspecs.tickstep' tls2 els2 tls2' els2' tls_used2->
get tls1' t1 = Some (pr1', st1', msg1', sus1', pr)->
get tls2' t2 = Some (pr2', st2', msg2', sus2', pr)->
pr1'=pr2'/\st1'=st2'/\msg1'=msg2'/\sus1'=sus2'.
Proof.
intros. 
lets H':tickstep_st_same.
lets H_:H' H H0 H1 H2 H3 H4.
lets Ht:H_ H5.
subst st2'.
lets H2':H2. lets H3':H3.
eapply tickstep_except_st_preserved in H2;eauto.
eapply tickstep_except_st_preserved in H3;eauto.
simpljoin. rewrite H2 in H4. rewrite H3 in H5.
inverts H4. inverts H5.
split. eauto. split. eauto. split. eauto. eauto.
Qed.
