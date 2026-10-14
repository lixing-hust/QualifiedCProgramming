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
Require Import equiv_sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas.
Require Import confidentiality_sched_lemma.
Require Import equiv_prop. 
Require Import sem_prop_2.
Require Import if_good_code.
Require Import data_invs.
Require Import equiv_prop.
(* Require Import assms. *)
(* Require Import succ_gen. *)
Require Import math_auto.
Require Import symbolic_lemmas.
Require Import hasrt_sat_preserve.
Require Import intspecs.
Require Import sched_lemma.
Set Keyed Unification.


Definition prio_preserved_d td O O' :=
forall pr t,
dom_for_prio pr = td ->
(task_prio_id O pr t <-> task_prio_id O' pr t). 

Definition prio_preserved O O' :=
forall td, prio_preserved_d td O O'. 

Lemma tickisr_els_same:
forall tls tls' els els',
intspecs.tickstep tls els tls' els'->
els=els'.
Proof.
introv Htickstep.
induction Htickstep.
eauto.
inverts H0;
rewrite IHHtickstep;
eauto.
Qed.

Lemma x_sub_one_zero:
forall x,
x -ᵢ Int.one = Int.zero->
x = Int.one.
Proof.
intros.
eapply sub_zero_eq.
eauto.
Qed.


Lemma prio_tid_corr:              
  forall O1 O2 t1 t2 pr t1' t2' pr', 
    task_prio_id O1 pr t1 -> 
    task_prio_id O2 pr t2 ->
    task_prio_id O1 pr' t1' ->
    task_prio_id O2 pr' t2' ->
    (t1 = t1' /\ t2 = t2' \/ t1 <> t1' /\ t2 <> t2').
Proof.
  introv Htpi1 Htpi2 Htpi1' Htpi2'.
  casetac t1 t1' Ht Hf.
  - subst. 
    assert (t2 = t2').
    {
      casetac t2 t2' Ht Hf.
      - auto.
      - casetac pr pr' He Hne.
        + subst. 
          lets H'_: tid_unique Htpi2 Htpi2'.
          tryfalse.
        + lets Hf_: prio_unique Htpi1 Htpi1'.
          tryfalse.
    }
    subst.
    left; auto.
  -
    casetac pr pr' He Hne.
    + subst.
      lets H_: tid_unique Htpi1 Htpi1'. tryfalse.
    + 
      casetac t2 t2' Ht_ Hf_.
      * subst.
        lets Hf_: prio_unique Htpi2 Htpi2'.
        tryfalse.
      * right. split; auto.
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

Definition apicode_type_c (C:code)  :=
match C with
    (c,(ke ,ks ))=>
     (forall cd,
        absintcont ks <> None ->
        c = curs(hapi_code cd) ->
        exists iid ,int_spec iid = Some tickisr /\
        (In cd (get_all_succs tickisr) \/ (exists vs,cd = END vs)) )
end.

Definition pool_apicode_type_c (T: tasks) :=
  forall t C, get T t = Some C -> apicode_type_c C. 


Lemma apicode_type_sstep_preserve:
  forall  pu td c ks m c' ks' m' ke , 
    sstep pu td c ks m c' ks' m' ->
    tskcode_no_sub_abs (c,(ke,ks)) ->
    apicode_type_c (c,(ke,ks)) ->
    apicode_type_c (c',(ke,ks'))  .
Proof.
  introv Hstep Htnsa  H_.
  unfold tskcode_no_sub_abs in *.
  destruct Htnsa as (Hcnoabs & Hksnoabs).
  unfolds.
  - introv Hrabsi Hcurapi.
    inverts Hstep;tryfalse.
    destruct s;tryfalse.
    destruct Hcnoabs as [Hcnoabs|Hcnoabs].
    simpl in Hksnoabs.
    destruct Hksnoabs.
    tryfalse.
    destruct Hcnoabs as (cd' & Hcnoabs).
    tryfalse.
    destruct Hcnoabs as [Hcnoabs|Hcnoabs].
    simpl in Hcnoabs.
    destruct Hcnoabs.
    destruct s1;tryfalse.
    destruct Hcnoabs.
    tryfalse.
    simpl in Hksnoabs.
    destruct Hksnoabs as (Hksnoabsstnoabs & Hksnoabsksnoabs).
    simpl in Hksnoabsstnoabs.
    destruct s;tryfalse.
    simpl in Hksnoabs.
    destruct Hksnoabs as (Hksnoabsstnoabs & Hksnoabsksnoabs).
    simpl in Hksnoabsstnoabs.
    destruct s;tryfalse.
    simpl in Hksnoabs.
    destruct Hksnoabs as (Hksnoabsstnoabs1 & Hksnoabsstnoabs2 & Hksnoabsksnoabs).
    simpl in Hksnoabsstnoabs1.
    destruct s1;tryfalse.
    simpl in Hksnoabs.
    destruct Hksnoabs as (Hksnoabsstnoabs1 & Hksnoabsstnoabs2 & Hksnoabsksnoabs).
    simpl in Hksnoabsstnoabs1.
    destruct s2;tryfalse.
    simpl in Hksnoabs.
    destruct Hksnoabs as (Hksnoabsstnoabs & Hksnoabsksnoabs).
    simpl in Hksnoabsstnoabs.
    destruct s;tryfalse.
Qed.


Lemma apicode_type_estep_preserve:
  forall  td c ke m c' ke' m' ks, 
    estep td c ke m c' ke' m' ->
    apicode_type_c (c,(ke,ks)) ->
    apicode_type_c (c',(ke',ks))  .
Proof.
  introv Hstep Hatc.
  unfolds.
  - introv Habsintcont Hcurapi .
    inverts Hstep;tryfalse.
Qed.


Lemma apicode_type_cstep_preserve:
  forall  pu td C m C' m', 
    cstep pu td C m C' m' ->
    tskcode_no_sub_abs C ->
    apicode_type_c C ->
    apicode_type_c C' .
Proof.
  introv Hstep Htsknosubabs Hatc .
  inverts Hstep.
  eapply apicode_type_estep_preserve;eauto.
  eapply apicode_type_sstep_preserve;eauto.
Qed.

Lemma apicode_type_specstep_preserve:
forall  cd O cd' O' act ke ks , 
    spec_step get_hprio_d cd O cd' O' act ->
    apicode_type_c (curs(hapi_code cd),(ke,ks)) ->
    apicode_type_c (curs(hapi_code cd'),(ke,ks)) .
Proof.
  introv Hstep Hatc.
  unfolds.
  -
    introv Habsintcont Hcursapi.
    unfolds in Hatc.
    assert (exists cd0, curs (hapi_code cd) = curs (hapi_code cd0));eauto.
    destruct H as (cd1 & Hcursapi_).
    eexists.
    specialize(Hatc cd1  Habsintcont Hcursapi_).
    inverts Hcursapi.
    inverts Hcursapi_.
    lets Hatc_:Hatc.
    destruct Hatc_ as (iid_ & Hintspec_ & Hact_).
    destruct Hatc as (iid & Hintspec & Hatc).
    destruct Hatc as [Hin|Hin].
    unfold int_spec in Hintspec.
    do 6 (destruct iid;simpl in Hintspec;tryfalse).
    inverts Hintspec.
    lets Hin_ : Hin.
    simpl in Hin.
    lets Hnth: In_nth_error cd1 Hin_.
    destruct Hnth as (n & Hnth).
    lets H_ : tickisr_spec_step_succs_preserve Hnth Hstep.
    
    split.
    instantiate(1:= 5%nat).
    unfold int_spec.
    simpl.
    eauto.
    destruct H_ as [H_|[H_|H_]].

    inverts Hstep;tryfalse;simpl;eauto.
    simpl in H_.
    inverts Hstep;simpl;eauto.
    simpl.



    destruct Hin.
    inverts H2.
    destruct H2.
    inverts H2.
    destruct H2.
    inverts H2.
    simpl in H.
    destruct H.
    destruct H2.
    tryfalse.
    tryfalse.

    
    destruct Hin.
    inverts H0.
    eauto.
    destruct H0.
    inverts H0.
    eauto.
    destruct H0.
    inverts H0.
    tryfalse.


    destruct Hin.
    inverts H1.
    inverts H.
    simpl in H6.
    simpljoin.
    destruct H11.
    simpljoin.
    tryfalse.
    simpljoin.
    tryfalse.
    destruct H1.
    inverts H1.
    inverts H.
    destruct H1.
    inverts H1.
    tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct Hin as [Hin|[Hin|[Hin|Hin]]];tryfalse.
    destruct H_ as (vo & H_).



    destruct Hin as [Hin|[Hin|[Hin|Hin]]].
    inverts Hin.
    inverts Hstep;tryfalse.
    inverts Hin.
    inverts Hstep;tryfalse.
    inverts Hin.
    inverts Hstep.
    simpl in H3.
    simpljoin.
    destruct vo.
    tryfalse.
    simpl.
    eauto.
    tryfalse.
    tryfalse.
    
    destruct Hin as (vs & Hin).
    inverts Hstep;
    tryfalse.
Qed.

Lemma apicode_type_hapistep_preserve:
  forall C O C' O' act c ke ks , 
    hapistep os_spec C O C' O' act ->
    C = (c, (ke, ks)) -> 
    kevt_no_nest ks ->
    nknl_nkevt c ks->
    apicode_type_c C ->
    apicode_type_c C' .
Proof.
  introv Hstep Hc  Hkevtnonest Hnknlnkevt1  Hatc.
  inverts Hstep.
  - unfolds in Hatc.  
    unfolds.
    intros.
    eexists.
    split.
    instantiate(1:= 5%nat).
    unfold int_spec.
    eauto.
    unfolds in Hnknlnkevt1.
    inverts H1.
    destruct Hnknlnkevt1.
    unfolds.
    right.
    eexists.
    split.
    eauto.
    introv.
    intros.
    destruct H1.
    tryfalse.
    tryfalse.
  - inverts H0.
    eapply apicode_type_specstep_preserve;eauto.
  - unfolds.
    intros.
    tryfalse.
  - inverts H.
    unfolds.
    intros.
    simpl in Hkevtnonest.
    tryfalse.
Qed.

Lemma apicode_type_htstep_preserve:
  forall p t td C cst O C' cst' O' act ke ks c, 
    htstep (p, os_spec) t td C cst O C' cst' O' act ->
    C = (c, (ke, ks)) -> 
    kevt_no_nest ks ->  
    nknl_nkevt c ks->
    tskcode_no_sub_abs C ->
    apicode_type_c C ->
    apicode_type_c C'.
Proof.
  introv Hstep  Hkevtnonest Hnknlnevt Htsknosub1 (* Htsknosub2 *) Hatc.
  inverts Hstep.
  eapply apicode_type_cstep_preserve;eauto.
  eapply apicode_type_hapistep_preserve;eauto.
  inverts H.
  eauto.
Qed.

Lemma apicode_type_htistep_preserve:
forall   O  C C' O' c ks,
    htistep int_spec C O C' O' ->
    kevt_no_nest ks ->  
    nknl_nkevt c ks->
    tskcode_no_sub_abs C ->
    apicode_type_c C ->
    apicode_type_c C'.
Proof.
  introv Hstep Hkevtnonest Hnknlnkevt1 Hnosubabs1 (* Hnosubabs2 *) Hatc.
  inverts Hstep.
  unfolds.
  introv Habsintcont Hcurs .
  eexists.
  instantiate(1:= 5%nat).
  split.
  unfold int_spec.
  simpl.
  eauto.
  inverts Hcurs.
  lets H_: H.
  unfold int_spec in H.
  do 6 (destruct i;simpl;tryfalse).
  simpl in H.
  inverts H.
  unfolds in Hatc.
  
  
  unfold int_spec in H_.
  simpl in H_.
  left.
  eauto.
Qed.

Lemma pool_apicode_type_c_hpstep_preserve: 
  forall p T cst O T'  cst' O' act, 
    hpstep (p, os_spec) T cst O T' cst' O' act ->
    pool_nknl_nkevt T->
    task_pool_no_sub_abs T->
    pool_kevt_no_nest T ->      
    pool_apicode_type_c T ->
    pool_apicode_type_c T'.
Proof.
  introv  Hstep Hpoolnknlnkevt Hpolnosubabs Hpolkevtnonest Hpolatc.
  unfolds in Hpoolnknlnkevt.
  unfolds in Hpolnosubabs.
  unfolds in Hpolkevtnonest.
  unfolds in Hpolatc.
  unfolds.
  introv Hget.
  inverts Hstep.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H3.
      clear Hpolatc.
      destruct C0 as (c_, (ke_, ks_)).
      eapply apicode_type_htstep_preserve;eauto.
    * rewrite set_a_get_a' in Hget; eauto.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H1.
      clear Hpolatc.
      destruct C0 as (c_, (ke_, ks_)).
      inverts H.
      eapply apicode_type_htistep_preserve;eauto.
    * rewrite set_a_get_a' in Hget; eauto.
  - 
    casetac t t0 Ht Hf.
    * subst t0. rewrite set_a_get_a in Hget. inverts Hget.
      lets Hatc: Hpolatc H2.
      unfolds in Hatc.
      unfolds.
      introv Habsintcont Hcurs.
      eexists.
      split.
      unfold int_spec.
      instantiate(1:= 5%nat).
      simpl;eauto.
      assert (exists cd', curs (hapi_code (sched asrt;; s)) = curs (hapi_code cd'));eauto.
      destruct H3 as (cd' & Hcurs').
      specialize (Hatc cd' ).
      lets H_ : Hatc Habsintcont Hcurs'.
      inverts Hcurs'.
      destruct H_ as (iid & Hintspec & H_).
      unfold int_spec in Hintspec.
      do 6 (destruct iid;simpl in Hintspec;tryfalse).
      inverts Hintspec.
      destruct H_ as [H_|H_].
      simpl in H_.
      destruct H_ as [H_|[H_|[H_|H_]]].
      tryfalse.
      inverts H_.
      inverts Hcurs.
      left.
      simpl.
      eauto.
      tryfalse.
      tryfalse.
      destruct H_ as (vs & H_).
      tryfalse.
    * rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma pool_apicode_type_c_hpstepokstar_preserve: 
  forall p T cst O T' cst' O', 
    pu_noabs p ->    
    hpstepokstar (p , os_spec) T cst O T' cst' O' ->
    pool_nknl_nkevt T->
    task_pool_no_sub_abs T->
    pool_kevt_no_nest T ->      
    pool_apicode_type_c T ->
    pool_apicode_type_c T'.
Proof.
  introv Hp Hstep Hpolnknlnkevt Hpolnosubabs Hpolkevtnonest Hpolatc.
  inductions Hstep; intros.
  auto.
  eapply IHHstep; eauto.
  inverts H.
  eapply nknl_nkevt_hpstep_preserve;eauto.
  inverts H.
  eapply noabs_preserve_hpstep;eauto.
  inverts H.
  eapply pool_kevt_nnest_preserve_hpstep;eauto.
  inverts H.
  eapply pool_apicode_type_c_hpstep_preserve;eauto.
Qed.
  
Lemma reachable_apicode_type_c: 
  forall p  T cst O, 
    pu_noabs p ->
    reachable (p, os_spec) T cst O ->
    pool_apicode_type_c T. 
Proof.
  introv  Hp Hrch.
  unfolds in Hrch.
  destruct Hrch as (pu & spc & Hhp & Hex).
  destruct Hex as (T0 & cst0 & O0 & Hini & Hsstar).
  eapply pool_apicode_type_c_hpstepokstar_preserve;eauto.
  -
    unfold init in Hini.
    destruct Hini as (Hit & His).
    unfolds in Hit.
    destruct Hit as (_ & Ha).
    unfolds. introv Hget. lets H_: Ha Hget. simpljoin.
    unfolds in H. inverts H.
    unfolds; intros.
    simpl. auto. 
  -
    unfold init in Hini.
    destruct Hini as (Hit & His).
    unfolds in Hit.
    destruct Hit as (Heqd & Hall).
    inverts Hhp.
    unfolds.
    introv Hget.
    unfold get in Hget. unfold TasksMap in Hget.
    apply Hall in Hget.
    simpl.
    simpljoin.
    unfolds in Hp.
    unfolds.
    unfold nilcont.
    simpl.
    split; auto.
    left. eapply Hp; eauto.
  -
    unfolds in Hini.
    destruct Hini as (Hit & _).
    unfolds in Hit.
    destruct Hit as (Heqd & Hall).
    unfolds. introv Hget.
    lets H_: Hall Hget.
    simpljoin.
    unfold nilcont in H.  inverts H.
    simpl. auto.
  -
    unfolds in Hini.
    destruct Hini as (Hitt & Hits).
    unfolds in Hitt.
    destruct Hitt as (Heqd & Hall).
    unfolds.
    introv Hget.
    lets H_:Hall Hget.
    simpljoin.
    unfold nilcont.
    simpl.
    introv Hn Hcurs.
    eexists.
    split.
    unfold int_spec. 
    instantiate(1:= 5%nat).
    simpl.
    eauto.
    tryfalse.
Qed.
    

Lemma confidentiality_sched_proof:
forall 
(pu : progunit) (T1 T2 : tasks) (cst1 cst2 : clientst)
(O1 O2 : osabst) (T1' T2' : tasks) (cst1' cst2' : clientst)
(O1' O2' : osabst) (act : action) (i : taskdom)
(Hpu : pu_noabs pu)
(Hncfid : no_common_fid pu (api_spec, int_spec, get_hprio_d))
(Hgood : good_client_code pu)
(Hrch2 : reachable (pu, (api_spec, int_spec, get_hprio_d)) T2 cst2 O2)
(Hrch1 : reachable (pu, (api_spec, int_spec, get_hprio_d)) T1 cst1 O1)
(Hfloweq : flowsTo SchedDom (TaskDom i) ->obsr_equiv get_hprio_d SchedDom T1 T2 cst1 cst2 O1 O2)
(Htdeq : obsr_equiv_tskd get_hprio_d i T1 T2 cst1 cst2 O1 O2)
(Htmeq : obsr_equiv get_hprio_d TransDom T1 T2 cst1 cst2 O1 O2)
(Hsceq : obsr_equiv get_hprio_d SchedDom T1 T2 cst1 cst2 O1 O2)
(Hstep2 : hpstep_pt (pu, (api_spec, int_spec, get_hprio_d)) T2 cst2 O2 T2' cst2' O2' act SchedDom)
(H : hpstep (pu, (api_spec, int_spec, get_hprio_d)) T1 cst1 O1 T1' cst1' O1' act)
(H0 : act = EniAct \/ act = TauAct /\ in_intr T1 O1 \/ act = SchAct)
(H1 : nabt T1'),

obsr_equiv_tskd get_hprio_d i T1' T2' cst1' cst2' O1' O2'.
Proof.
introv Hpu Hncfid Hgood Hrch2 Hrch1.
introv Hfloweq Htdeq Htmeq Hsceq Hstep2 H H0 H1.
rename i into td.
(* sched step (as opposed to task step) by left system *)
match goal with H: hpstep _ T1 _ _ _ _ _ _ |- _ => rename H into Hstep1 end.
unfold obsr_equiv_tskd.
          assert (Hflcs: flowsTo SchedDom (TaskDom td)
                 \/ ~flowsTo SchedDom (TaskDom td)) by tauto.
          destruct Hflcs as [Hstepdm | Hstepdm'].
          lets Hd'eq: Hfloweq Hstepdm.
          assert (Hd'eq_ := Hd'eq).
unfolds in Hd'eq_.
unfold obsr_equiv_schd in Hd'eq_.
destruct Hd'eq_ as (Hceq & Hdeq).
unfold data_equiv_schd in Hdeq.
destruct Hdeq as (Hcdomid & Hschidxid & Hschid & Hdomtiid & Hd).
destruct Hd as (t1 & t2 & Hgs1 & Hgs2 & Htoi & Hd).
unfold obsr_equiv_tskd in Htdeq.
destruct Htdeq as (Htce & Htde).
lets Htde': Htde.
unfold data_equiv_tskd in Htde. 
unfold code_equiv_schd in Hceq.
destruct Hceq as(c1 & c2 & ke1 & ke2 & ks1 & ks2 & Hcct1 & Hcct2 & Habse & Habsc).
destruct Htde as (Hctide & Hbufs3 & Hkernelde & Hclientde).
inverts Hstep1.
+(* htstep for left system *)
  inverts H4.
  ++(* htclt_step for left system *)(*change of sem_prop  *)
    assert (t = t1) by congruence. subst.
    lets Hp1 : reachable_intr_ncli Hrch1.
    lets Hp2 : reachable_intr_ncli Hrch2.
    unfolds in Hp1.
    lets Hp1_ : Hp1 H5.
    unfolds in Hp1_.
    destruct C.
    destruct c0.
    destruct H0.
    tryfalse.
    destruct H0.
    2:tryfalse.
    destruct H0.
    unfolds in H4.
    destruct H4 as (c_ & e_ & s_ & Hcct & Habscont).
    unfold code_cur_task in Hcct.
    rewrite Hgs1 in Hcct.
    rewrite H5 in Hcct.
    inverts Hcct.
    destruct Hp1_.
    tryfalse.
    destruct H4 as (cd & H4).
    inverts H8.
    inverts H10;
    inverts H9;
    tryfalse.
    inverts H10;
    inverts H9;
    tryfalse.
  ++(* hapi_step for left system *)
    inverts H6.
    +++(* hapinter_step for left system *)
          assert (t = t1) by congruence. subst.
          lets Hp1 : reachable_intr_ncli Hrch1.
          lets Hp2 : reachable_intr_ncli Hrch2.
          unfolds in Hp1.
          lets Hp1_ : Hp1 H5.
          unfolds in Hp1_.
          destruct H0.
          tryfalse.
          destruct H0.
          2:tryfalse.
          destruct H0.
          unfolds in H4.
          destruct H4 as (c_ & e_ & s_ & Hcct & Habscont).
          unfold code_cur_task in Hcct.
          rewrite Hgs1 in Hcct.
          rewrite H5 in Hcct.
          inverts Hcct.
          destruct Hp1_.
          tryfalse.
          destruct H4 as (cd & H4).
          tryfalse.
    +++(* hidapi_step for left system *)
          inverts Hstep2.  
          inverts H6.
        ++++(*hp_step for right system*)
          inverts H12.
            +++++(*htclt_step for right system*)
                  assert (t = t1) by congruence. subst.
                  lets Hp2 : reachable_intr_ncli Hrch2.
                  unfolds in Hp2.
                  lets Hp2_ : Hp2 H13.
                  unfolds in Hp2_.
                  destruct H7.
                  tryfalse.
                  destruct H7.
                  2:tryfalse.
                  destruct H7.
                  unfolds in H12.
                  destruct H12 as (c_ & e_ & s_ & Hcct & Habscont).
                  unfold code_cur_task in Hcct.
                  rewrite H9 in Hcct.
                  rewrite H13 in Hcct.
                  inverts Hcct.
                  destruct Hp2_.
                  tryfalse.
                  destruct H12 as (cd_ & H12).
                  inverts H15;
                  inverts H17;
                  tryfalse.
            +++++(*hapi_step for right system*)
                  inverts H11.
                  ++++++(*hapienter_step for right system*)
                      assert (t0 = t2) by congruence. subst.
                      lets Hp2 : reachable_intr_ncli Hrch2.
                      unfolds in Hp2.
                      lets Hp2_ : Hp2 H13.
                      unfolds in Hp2_.
                      destruct H7.
                      tryfalse.
                      destruct H7.
                      2:tryfalse.
                      destruct H7.
                      unfolds in H11.
                      destruct H11 as (c_ & e_ & s_ & Hcct & Habscont).
                      unfold code_cur_task in Hcct.
                      rewrite H9 in Hcct.
                      rewrite H13 in Hcct.
                      inverts Hcct.
                      destruct Hp2_.
                      tryfalse.
                      destruct H11 as (cd_ & H11).
                      tryfalse.
                  ++++++(*hidapi_step for right system  possible O -> O'*)
                      (* unfold code_cur_task in *. *)
                      lets Hgodt1: reachable_good_tasks Hgood Hrch1.
                      lets Hgodt2: reachable_good_tasks Hgood Hrch2.
                      unfolds in Htce.
                      unfolds in Hctide.
                      destruct Hctide as (t1_ & t2_ & Hgcs1_ & Hgcs2_ & Hf).
                      assert (t1_ = t1) by congruence. subst.
                      assert (t2_ = t2) by congruence. subst.
                      assert (t = t1) by congruence. subst.
                      assert (t0 = t2) by congruence. subst.
                      unfold code_cur_task in *.
                      rewrite Hgs1 in Hcct1.
                      rewrite  H5 in Hcct1.
                      rewrite H9 in Hcct2.
                      rewrite H13 in Hcct2.
                      destruct H0.
                      {(*act = Eniact*)
                       
                        subst act.
                        match goal with H: _ \/ _ \/ _ |- _ => rename H into Hact end.
                        destruct Hact as [Hact|[Hact|Hact]].
                        2:simpljoin;tryfalse.
                        2:tryfalse.
                        lets Hfa: speccode_not_eniact Hact Hgood Hrch1 H3 H4 H5.
                        tryfalse.
                      }
                      destruct H0.
                      {(*act = Tauact*)
                          destruct H0 as (Hact & Hinintr).
                          lets Hinintr1_:Hinintr.
                          subst act.
                          unfolds in Hinintr.
                          destruct Hinintr as (c_ & ke_ & ks_ & Hcct & Habsintcont).
                          unfolds in Hcct.
                          rewrite H in Hcct.
                          rewrite H5 in Hcct.
                          inverts Hcct.
                          destruct H7 as [Hact2|[Hact2|Hact2]];tryfalse.
                          lets Hpatc1: reachable_apicode_type_c Hpu Hrch1.
                          lets Hpatc2: reachable_apicode_type_c Hpu Hrch2.
                          unfold pool_apicode_type_c in *.
                          lets Hatc1: Hpatc1 H5.
                          lets Hatc2: Hpatc2 H13.
                          unfold apicode_type_c in *.
                          inverts Hcct1.
                          inverts Hcct2.
                          destruct Hact2 as (Hact & Hinintr2).
                          lets Hinintr2_:Hinintr2.
                          inverts Hact.
                          unfolds in Hinintr2.
                          destruct Hinintr2 as (c_ & ke_ & ks_ & Hcct2 & Habsintcont2).
                          unfolds in Hcct2.
                          rewrite Hgs2 in Hcct2.
                          rewrite H13 in Hcct2.
                          inverts Hcct2.
                          assert (exists cd2,curs (hapi_code cd0)=curs (hapi_code cd2));eauto.
                          destruct H0 as (cd2 & Hcurs2).
                          lets H_:Hatc2 Habsintcont2 Hcurs2.
                          destruct H_ as (iid2 & Hintspec2 & Hin2).
                          inverts Hcurs2.
                          assert (exists cd1,curs (hapi_code cd)=curs (hapi_code cd1));eauto.
                          destruct H0 as (cd1 & Hcurs1).
                          lets H_:Hatc1 Habsintcont Hcurs1.
                          destruct H_ as (iid1 & Hintspec1 & Hin1).
                          inverts Hcurs1.
                          destruct Hin1 as [Hin1|Hin1].
                          simpl in Hin1.
                          simpl in Hin2.

                          destruct Hin1 as [Hin1|[Hin1|[Hin1|Hin1]]];tryfalse.

                          (*1:intspecs.tickisr = cd1*)
                          inverts Hin1.
                          destruct Hin2 as [Hin2|Hin2].
                          destruct Hin2 as [Hin2|[Hin2|[Hin2|Hin2]]];tryfalse.
                          inverts Hin2.

                          match goal with H: spec_step _ _ O2 _ _ _  |- _ => rename H into Hstep2 end.
                          match goal with H: spec_step _ _ O1 _ _ _  |- _ => rename H into Hstep1 end.
                          inverts H3.
                          inverts H6.
                          lets Hpriopreserved1 : tickisr_spec_prio_preserved Hstep1.
                          lets Hpriopreserved2 : tickisr_spec_prio_preserved Hstep2.
                          lets Hpriopre1_:Hpriopreserved1.
                          lets Hpriopre2_:Hpriopreserved2.
                          inverts Hstep1.
                          match goal with H: spec_step _ _ O1 _ _ _  |- _ => rename H into Hstep1 end.
                          inverts Hstep1.
                          match goal with H: intspecs.tickisr_spec _ _ _ _   |- _ => rename H into Hint1 end.

                          inverts Hstep2.
                          match goal with H: spec_step _ _ O2 _ _ _  |- _ => rename H into Hstep2 end.
                          inverts Hstep2.

                          match goal with H: intspecs.tickisr_spec nil O0 TauAct (v0, Some O'0) |- _ => rename H into Hint2 end.

                          match goal with H: task_prio_id O1 _ _ |- _ => rename H into Htpi1 end.
                          match goal with H: task_prio_id O2 _ _ |- _ => rename H into Htpi2 end.

                          inverts Hint1. 
                          simpljoin. 
                          destruct H23. 
                          simpljoin. 
                          inverts H41.
                          eapply join_get_set_eq_8 in H21;eauto.
                          inverts H21.
                          clear H22.
                          
                          match goal with H: intspecs.tickisr_spec _ _ _ _   |- _ => rename H into Hint2 end.
                          inverts Hint2.
                          simpljoin.
                          destruct H42.
                          simpljoin.
                          inverts H52.
                          eapply join_get_set_eq_8 in H25;eauto.
                          inverts H25.
                          clear H43.


                          split.
                          unfolds.
                          introv Hdom Htpi1' Htpi2'.

                          unfolds in Hpriopreserved1.
                          specialize (Hpriopreserved1 td).
                          unfolds in Hpriopreserved1.
                          lets Hpriopreserve : Hpriopreserved1 Hdom.
                          destruct Hpriopreserve as (Hpriop1 & Hpriop2).
                          
                          unfolds in Hpriopreserved2.
                          specialize (Hpriopreserved2 td).
                          unfolds in Hpriopreserved2.
                          lets Hpriopreserve : Hpriopreserved2 Hdom.
                          destruct Hpriopreserve as (Hpriop1_ & Hpriop2_).


                          lets Ht1: Hpriop2 Htpi1'.
                          lets Ht1_: Hpriop2_ Htpi2'.
                          casetac t1 t0 Hte Htne.
                          2:{
                            casetac pr pr1 Hpe Hpne.
                            subst pr.
                            lets Hfalse: tid_unique Htpi1 Ht1.
                            tryfalse.
                            casetac t2 t3 Hte_ Htne_.
                            subst t3.
                            lets H_:prio_unique Htpi2 Ht1_.
                            subst pr0.
                            lets H__: Hd Htpi1 Ht1_.
                            rewrite Hdom in H__.
                            lets H___:Hf Htpi1 Ht1_ H__.
                            tryfalse.
                 
                            rewrite set_a_get_a';eauto.
                            rewrite set_a_get_a';eauto.
                            lets Hfalse :Htce Hdom Ht1 Ht1_.
                            simpljoin.
                            do 5 eexists.
                            split. eauto. split. eauto. split.
                            unfolds.
                            match goal with H: cmd_equiv pr1 _ _ _ _ |-_=>rename H into Hcmd end.
                            destruct Hcmd as [Hcmd|Hcmd].
                            left;eauto.
                            simpljoin.
                            right.
                            do 2 eexists.
                            split. eauto. split. eauto.
                            
                            match goal with H: get T1 t0 = _ |- _ => rename H into Hgett0 end.
                            match goal with H: get T2 t3 = _ |- _ => rename H into Hgett3 end.
                            
                            unfold eqdomO in *.
                            destruct H16 as (Heqdom1 & Heqdom1_).
                            destruct H15 as (Heqdom2 & Heqdom2_).
                            unfold eqdomO0 in *.

                            clear Hpatc1.
                            clear Hpatc2.
                            match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                            lets Htype: Hstmte.
                            unfolds in Htype.
                            destruct Htype as [Htype|Htype].
                            simpljoin.
                            split. simpl. eauto. split. simpl. eauto. eauto. eauto.

                            destruct Htype as (HnotEND & Hapi).
                            destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].
                            (*mqsend_equiv x30 x31*)
                            unfolds in Hmqsend.

                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                            split;eauto.
                            (*mqrecv _qref_asrt *)
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 

                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                            split;eauto.
                            (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                            split;eauto.
                            (*mqtimedrecv_equiv end*)





                            (*qprtpost_equiv *)
                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            } 
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. 
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.

                            (*qprtpend_equiv *)

                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                            split;eauto.

                            (*sprtpost*)
                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            eapply dom_impl_8_proof;eauto.
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            eapply dom_impl_8_proof;eauto.
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.

                            (*prtaccept_equiv *)
                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_8_proof;eauto.

                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_8_proof;eauto.

                            split;eauto.

                            (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*intr_equiv *)
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror2.
                            match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*ABORT*)
                            destruct Habort as (Habort1 & Habort2).
                            inverts Habort1.
                            inverts Habort2.
                            split. simpl. eauto.
                            split. simpl. eauto.
                            split;eauto.


                            (*cont_equiv*)
                            match goal with H: cont_equiv _ _ _ O1 O2 |- _ => rename H into Hcont end.
                            destruct Hcont as [Hcont|Hcont].
                            destruct Hcont as (Hcont1 & Hcont2 & Hcont3).
                            unfolds. left. split. eauto. split. eauto. eauto.

                            destruct Hcont as (c1 & c2 & ke & ks' & Hcont1 & Hcont2 & Hcont3).
                            unfolds. right. do 4 eexists. split. eauto. split. eauto.


                            destruct Hcont3 as [Hcont3|Hcont3].
                            simpljoin. unfolds. left. split. eauto. split. eauto. eauto.
                            
                            simpljoin.
                            
                            
                            match goal with H: get T1 t0 = _ |- _ => rename H into Hgett0 end.
                            match goal with H: get T2 t3 = _ |- _ => rename H into Hgett3 end.
                            
                            unfold eqdomO in *.
                            destruct H15 as (Heqdom1 & Heqdom1_).
                            destruct H16 as (Heqdom2 & Heqdom2_).
                            unfold eqdomO0 in *.

                            clear Hpatc1.
                            clear Hpatc2.
                            match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                            lets Htype: Hstmte.
                            unfolds in Htype.
                            destruct Htype as [Htype|Htype].

                            simpljoin.
                            unfolds. right. do 2 eexists. split. eauto. split. eauto.
                            split. simpl. eauto. split. simpl. eauto. eauto. eauto.

                            destruct Htype as (HnotEND & Hapi).
                            unfolds. right. do 2 eexists. split. eauto. split. eauto.
                            destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].

                            (*mqsend_equiv x30 x31*)
                            unfolds in Hmqsend.

                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H: head_asrt_sat _ _ O1 |- _ => rename H into Hheadasrt1 end. eapply Hheadasrt1.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              }
                            split;eauto.
                            (*mqrecv _qref_asrt *)
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H: head_asrt_sat _ _ O1 |- _ => rename H into Hhearasrt1 end.  eapply Hhearasrt1.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              }
                            split;eauto.


                            (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              }
                            split;eauto.
                            (*mqtimedrecv_equiv end*)
                            (*qprtpost_equiv *)
                            
                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48. 
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              
                              }
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                            split;eauto.

                            (*qprtpend_equiv *)
                            
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              }
                            split;eauto.


                            (*sprtpost*)
                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            eapply dom_impl_8_proof;eauto.
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            eapply dom_impl_8_proof;eauto.
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 8 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.


                            (*prtaccept_equiv *)
                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_8_proof;eauto.

                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_8_proof;eauto.

                            split;eauto.
                             (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            (*intr_equiv *)
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror1. eapply H48.
                            
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror2.
                            match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*ABORT*)
                            destruct Habort as (Habort1 & Habort2).
                            inverts Habort1.
                            inverts Habort2.
                            split. simpl. eauto.
                            split. simpl. eauto.
                            split;eauto.
                             }
                          subst t0.
                          assert (t2=t3).
                          {
                            lets H_:prio_unique Htpi1 Ht1.
                            subst pr.
                            lets H_: Hf Htpi1 Htpi2 Hdom.
                            subst pr0.
                            lets H_: prio_tid_corr Htpi1 Htpi2 Ht1 Ht1_.
                            destruct H_ as [H_|H_]. simpljoin. simpljoin. tryfalse.
                          }
                          subst t3.
                          lets Htce' : Htce Hdom Ht1 Ht1_.
                          destruct Htce' as (c1' & c2' & ke' & ks1' & ks2' & Hgtt1 & Hgtt2 & Hcmde & Hconte ).
                          match goal with H: get T2 t2 = Some (curs (hapi_code intspecs.tickisr), (ke_, ks_)) |-_=> rename H into Hgtt2' end.
                          match goal with H: get T1 t1 = Some (curs (hapi_code intspecs.tickisr), (ke1, ks1)) |-_=> rename H into Hgtt1' end.
                          rewrite Hgtt1 in Hgtt1'.
                          rewrite Hgtt2 in Hgtt2'.
                          inverts Hgtt1'. inverts Hgtt2'.
                          do 5 eexists.
                          split. rewrite set_a_get_a. eauto. split. rewrite set_a_get_a. 
                          eauto. split.
                          (*cmd_equiv*)
                          unfolds in Hcmde. destruct Hcmde as [Hcmde|Hcmde]. unfolds. 
                          destruct Hcmde as ((Hcmde1 & Hcmde2) & Hcmde3). unfolds in Hcmde1. destruct Hcmde1 as [Hcmde1|Hcmde1]. simpljoin;tryfalse. 
                          simpljoin. destruct H13. inverts H5.  eauto. 
                          unfold eqdomO in *.
                          destruct H15 as (Heqdom1 & Heqdom1_).
                          destruct H16 as (Heqdom2 & Heqdom2_).
                          unfold eqdomO0 in *.
                          simpljoin.
                          match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                          lets Htype: Hstmte.
                          unfolds in Htype.
                          destruct Htype as [Htype|Htype].
                          simpljoin.
                          unfolds. right. do 2 eexists. split. eauto. split. eauto. split. simpl. eauto. split. eauto. split;eauto.
                          unfolds. intros. match goal with H:get_hd_vl _ = _ |- _ => rename H into H_ end. unfolds in H_.
                          match goal with H:get_hd_vl _ = _ |- _ => rename H into H__ end. unfolds in H__. inverts H_. inverts H__.
                          simpl in *. tryfalse. 
                          (*stmt_equiv*)
                          unfolds.
                          right. split. introv Hfalse. simpljoin. tryfalse. right. right. right. right. right. right. right. right. right. right. left.
                          unfolds. eexists. split. instantiate(1:=1%nat). simpl. eauto. simpl. eauto.
                          (*cmd_equiv*)
                          unfolds. destruct Htype as (Htypef & Htype). inverts H5. inverts H13.
                          right. do 2 eexists. split. eauto. split. eauto. split. simpl. eauto. split. simpl. eauto.
                          split. unfolds. intros. match goal with H:get_hd_vl (SCHED;; spec_skip_step (|nil|)) = Some vl1 |-_=> rename H into H_ end. 
                          simpl in H_. inverts H_. simpl in *. match goal with H: Some nil = Some vl2 |-_=> inverts H end. induction i. simpl in *. tryfalse. simpl in *. tryfalse.
                          unfolds. right. split. introv Hfalse. destruct Hfalse as (vo1 & vo2 & H1_ & H2_ ). tryfalse. do 9 right. right. left. unfolds. eexists. split. instantiate(1:= 1%nat). simpl. eauto. simpl. eauto.
                          
                          (*cont_equiv*)
                          unfolds in Hconte. destruct Hconte as [Hconte|Hconte]. destruct Hconte as (Hfalse1 & Hfalse2 &Heq). unfolds. left. split. eauto. split. eauto. eauto.
                          destruct Hconte as (c1 & c2 & ke & ks' & Hkev1 & Hkev2 & Hcmde_). unfolds. right. do 4 eexists. split. eauto. split. eauto. 
                          (*cont-cmd equiv*)
                          unfolds.
                          destruct Hcmde_ as [Hcmde_|Hcmde_]. eauto. right. destruct Hcmde_ as (cd1 & cd2 & Hc1 & Hc2 & Hheadasrt1 & Hheadast2 & Hvle & Hstmte).
                          do 2 eexists. split. eauto. split. eauto. unfolds in Hstmte. destruct Hstmte as [Hstmte|Hstmte]. simpljoin. simpl in *. tryfalse. split. eauto. split. eauto. split. eauto. unfolds. left. eauto.
                        
                          destruct Hstmte as (Hfa & Hstmte).

                          unfold eqdomO in *.
                          destruct H15 as (Heqdom1 & Heqdom1_).
                          destruct H16 as (Heqdom2 & Heqdom2_).
                          unfold eqdomO0 in *.

                          lets Hapi: Hstmte.
                          
                          destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].

                          (*mqsend_equiv x30 x31*)
                          unfolds in Hmqsend.


                          split.
                          eapply mqsend_qref_asrt_preserve.
                          destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H:head_asrt_sat pr1 cd1 O1 |-_=>rename H into Hheadasrt1 end. eapply Hheadasrt1.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                          split.
                          eapply mqsend_qref_asrt_preserve.
                          destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                          split;eauto.
                          unfolds. right. eauto.
                          (*mqrecv _qref_asrt *)
                          split.
                          eapply mqrecv_qref_asrt_preserve.
                          destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H:head_asrt_sat pr1 cd1 O1 |-_=>rename H into Hheadasrt1 end. eapply Hheadasrt1.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                            lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                          split.
                          eapply mqrecv_qref_asrt_preserve.
                          destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                          split;eauto.
                          unfolds. right. eauto.

                          (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                             lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                              }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 8 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                              }
                            split;eauto. unfolds. right. split;eauto.
                            (*mqtimedrecv_equiv end*)

                          (*qprtpost_equiv *)
                          split.
                          eapply qprtpost_asrt_preserve.
                          destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H:head_asrt_sat pr1 cd1 O1|-_=> rename H into Hheadasrt1 end. eapply Hheadasrt1.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          { 
                              lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                          eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa_;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 8 (rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse]). eauto.
                          split.
                          eapply qprtpost_asrt_preserve.
                          destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                          eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa_;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 8 (rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse]). eauto.

                          split;eauto.
                          unfolds. right. eauto.
                          (*qprtpend_equiv *)

                          split.
                          eapply qprtpend_asrt_preserve.
                          destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. match goal with H: head_asrt_sat pr1 cd1 O1 |-_=>rename H into Hheadasrt1 end. eapply Hheadasrt1.
                          unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                          inverts Hget'. eauto.
                          
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          { 
                            lets Ht:dom_impl_8_proof H20 H3 H4 H6 H12 H2.
                              lets Ht':Ht H7 H10 H14 H18.
                              eauto.
                            }
                          split.
                          eapply qprtpend_asrt_preserve.
                          destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          unfolds. introv Hgetosdomainortid Hget' Hdpl. do 8 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                          inverts Hget'. eauto.
                          { 
                              lets Ht:dom_impl_8_proof H24 H22 H23 H35 H38 H36.
                              lets Ht':Ht H39 H40 H41 H42 .
                              eauto.
                            }
                          split;eauto.
                          unfolds. right. eauto.


                          (*sprtpost*)
                          split.
                          eapply sprtpost_asrt_preserve.
                          destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          eapply dom_impl_8_proof;eauto.
                          eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 8 (rewrite set_a_get_a';[idtac|introv Hfal;tryfalse]). eauto.

                          split.
                          eapply sprtpost_asrt_preserve.
                          destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          eapply dom_impl_8_proof;eauto.
                          eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 8 (rewrite set_a_get_a';[idtac|introv Hfal;tryfalse]). eauto.

                          split;eauto.
                          unfolds. eauto.


                          (*prtaccept_equiv *)
                          split.
                          eapply prtaccept_asrt_preserve.
                          destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          eapply dom_impl_8_proof;eauto.

                          split.
                          eapply prtaccept_asrt_preserve.
                          destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          unfolds. introv Ha Hb Hc. do 8 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          eapply dom_impl_8_proof;eauto.

                          split;eauto. unfolds. eauto.


	                       (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            unfolds. eauto.
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            unfolds. eauto.
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            unfolds. eauto.

                          (*intr_equiv *)
                          split.
                          eapply intr_asrt_preserve.
                          destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                          eexists.
                          eapply Hntherror1. match goal with H:head_asrt_sat pr1 cd1 O1 |-_ => rename H into Hheadasrt1 end. eapply Hheadasrt1.
                          
                          split.
                          eapply intr_asrt_preserve.
                          destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                          eexists.
                          eapply Hntherror2.
                          match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          
                          split;eauto.
                          unfolds. right. eauto.
                          (*ABORT*)
                          destruct Habort as (Habort1 & Habort2).
                          inverts Habort1.
                          inverts Habort2.
                          split. simpl. eauto.
                          split. simpl. eauto.
                          split;eauto.
                          unfolds. right. eauto.


                          (*data_equiv_tskd*)
                          unfolds. 
                          
                          (*data_equiv -> ctid_equiv*)
                          split. unfolds. do 2 eexists. split. repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).
                          split. repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]). intros. 
                          lets H1_:Hpriopreserved1.
                          lets H2_:Hpriopreserved2.
                          unfolds in H1_. unfolds in H2_. specialize (H1_ td). specialize(H2_ td).
                          unfold prio_preserved_d in *. match goal with H: dom_for_prio pr1 = _ |- _=>rename H into Hdom_ end. specialize (H1_ pr1 t1 Hdom_). specialize(H2_ pr1 t2 Hdom_).
                          destruct H1_ as (H11_ & H12_). destruct H2_ as (H21_ & H22_). lets Htpi1_ : H12_ H25. destruct Htoi as (Htoi1 & Htoi2). destruct Htoi1. eexists. eapply Htpi1_.
                          lets Hpe: prio_unique Htpi1 Htpi1_. subst pr. 
                          lets Hpe_:Hf Htpi1 Htpi2 Hdom_. subst pr0. lets Hm: H21_ Htpi2. lets Hm_: prio_unique H43 Hm. eauto.

                          (*tickisr t1=t0 t2=t3 data_equiv -> bufs_equiv*)(*sched  skip *)
                          lets Htde: Htde'. unfolds in Htde. destruct Htde as (Htctid &  Htbufs & Htkernel & Htclient). unfolds in Htbufs. destruct Htbufs as (Htbufs1 & Htbufs2).
                          unfolds in Htbufs1. unfolds in Htbufs2.
                          split. unfolds. split.  unfolds. repeat(rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                          (*data_equiv->obufs_equiv *)
                          unfolds. repeat(rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                          (*data_equiv->kernel_data_equiv *)
                          split. destruct Htkernel as (Htkerneltask & Htkernelmq & Htkernelport & Htkernelcap).
                          unfolds. 

                          (*data_equiv->kernel_data_equiv->kernel_task_equiv*)
                          split. unfolds in Htkerneltask. destruct Htkerneltask as (tcbs1 & tcbs2 & Habstcblsid1 & Habstcblsid2 & Htkerneltask).
                          unfolds. do 2 eexists. split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. instantiate(1:= x2). eauto.
                          intros. split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. instantiate(1:= x15). eauto.
                          intros.
                          lets Htke: Htkerneltask H25. destruct Htke as (Htk1 & Htk2). 
                          split. split. intros. 
                          destruct H43. unfold prio_preserved in *. 
                          specialize(Hpriopreserved1 td). specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *. specialize(Hpriopreserved1 pr1 x23).
                          specialize (Hpriopreserved1 H25). destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Hm: Hpriopreserved12 H43. destruct Htk1 as (Htk11 & Htk12). destruct Htk11. eauto. 
                          specialize(Hpriopreserved2 pr1 x24). 
                          specialize(Hpriopreserved2 H25).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Ht:Hpriopreserved21 H44.
                          unfolds in Ht. destruct Ht as (pr' & tcbs & st & msg0 & sus & Ht).
                          destruct Ht as (Ht1&Ht2).  repeat(try rewrite set_a_get_a in Ht1;rewrite set_a_get_a' in Ht1;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 5 eexists. split. 2:eauto. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Ht1. rewrite set_a_get_a. eauto.


                          intros.
                          destruct H43. unfold prio_preserved in *. 
                          specialize(Hpriopreserved1 td). specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *. specialize(Hpriopreserved2 pr1 x23).
                          specialize (Hpriopreserved2 H25). destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Hm: Hpriopreserved22 H43. destruct Htk1 as (Htk11 & Htk12). destruct Htk12. eauto.
                          specialize(Hpriopreserved1 pr1 x24). 
                          specialize(Hpriopreserved1 H25).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Ht:Hpriopreserved11 H44.
                          unfolds in Ht. destruct Ht as (pr' & tcbs & st & msg0 & sus & Ht).
                          destruct Ht as (Ht1&Ht2).  repeat(try rewrite set_a_get_a in Ht1;rewrite set_a_get_a' in Ht1;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 5 eexists. split. 2:eauto. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Ht1. rewrite set_a_get_a. eauto.

                          intros.
                          unfold prio_preserved in *.
                          specialize(Hpriopreserved1 td).
                          specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *.
                          specialize(Hpriopreserved1 pr1 t0).
                          specialize(Hpriopreserved2 pr1 t3).
                          match goal with H: dom_for_prio pr1 = _ |- _=> rename H into Hdom end.
                          specialize(Hpriopreserved1 Hdom).
                          specialize(Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          destruct Hpriopreserved22.
                          unfolds.
                          do 5 eexists.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          eauto.

                          destruct Hpriopreserved12.
                          unfolds.
                          do 5 eexists.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          eauto.

                          simpljoin.
                          rename H25 into Habstcblsid2'.
                          rename H46 into Habstcblsid1'.
                          rewrite Habstcblsid1 in Habstcblsid1'.
                          rewrite Habstcblsid2 in Habstcblsid2'.
                          inverts Habstcblsid1'. inverts Habstcblsid2'.
                          lets H': Htk2 H49 H50. simpljoin. subst.
                          
                          destruct Hpriopreserved11.
                          unfolds.
                          do 5 eexists. split. eauto.
                          eauto.
                          eapply join_get_get_l in H22;eauto.
                          eapply join_get_get_l in H3;eauto.
                          rewrite H3 in Habstcblsid1. inverts Habstcblsid1.
                          rewrite H22 in Habstcblsid2. inverts Habstcblsid2.
                          lets H_:Htk2 H49 H50. unfolds in H11. unfolds in H37.
                          lets H':tickisr_tcbs_preserved H49 H50 H_  H43 H44;eauto.
                          (*data_equiv->kernel_mq_equiv*)
                          split.

                          lets Hmqecb1:mq_ecb.
                          lets Hmqecb2:mq_ecb. 
                          specialize (Hmqecb1 (set
                                                 (set
                                                    (set
                                                       (set
                                                          (set
                                                             (set
                                                                (set (set O1 absecblsid (absecblist x3)) abstcblsid
                                                                   (abstcblist x2)) ostmid 
                                                                (ostm (x1 +ᵢ  Int.one))) ksdomtimeid
                                                             (ksdomtime (x5 -ᵢ Int.one))) ksdschedidxid
                                                          (ksdschedidx
                                                             (if Int.ltu (x4 +ᵢ  Int.one) x6
                                                              then x4 +ᵢ  Int.one
                                                              else Int.zero))) kslastdomid 
                                                       (kslastdom x7)) kscurdomid (kscurdom x12)) ksdomtimeid
                                                 (ksdomtime x13))).
                          specialize (Hmqecb2 (set
                                                 (set
                                                    (set
                                                       (set
                                                          (set
                                                             (set
                                                                (set (set O2 absecblsid (absecblist x16)) abstcblsid
                                                                   (abstcblist x15)) ostmid 
                                                                (ostm (x14 +ᵢ  Int.one))) ksdomtimeid
                                                             (ksdomtime (x18 -ᵢ Int.one))) ksdschedidxid
                                                          (ksdschedidx
                                                             (if Int.ltu (x17 +ᵢ  Int.one) x19
                                                              then x17 +ᵢ  Int.one
                                                              else Int.zero))) kslastdomid 
                                                       (kslastdom x20)) kscurdomid (kscurdom x25)) ksdomtimeid
                                                 (ksdomtime x26))).
                          repeat(try rewrite set_a_get_a in Hmqecb1;rewrite set_a_get_a' in Hmqecb1;[idtac|introv Hfa;tryfalse]).
                          repeat(try rewrite set_a_get_a in Hmqecb2;rewrite set_a_get_a' in Hmqecb2;[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Hmqecb1.
                          rewrite set_a_get_a in Hmqecb2.


                          unfolds in Htkernelmq. destruct Htkernelmq as (mqatts1 & mqatts2 & Hgetmq1 & Hgetmq2 & Hmq).

                          unfolds. do 2 eexists. split. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          introv Hmqidxdom. specialize(Hmq i). specialize(Hmq Hmqidxdom). destruct Hmq as(Hmq1 & Hmq2).
                          split. eauto. introv Hgetmqatts1 Hgetmqatts2. lets Hmqequiv: Hmq2 Hgetmqatts1 Hgetmqatts2.
                          unfold mq_equiv in *. 
                          simpljoin. do 8 eexists. split. eauto. split. eauto.
                          match goal with H: _ = Null /\ _ = Null \/ _ |- _=>rename H into Hmqequiv end.
                          destruct Hmqequiv as [Hmqequiv|[Hmqequiv|Hmqequiv]].
                          left. eauto. right. left. eauto. right. right.
                          simpljoin. 

                          specialize (Hmqecb1 mqatts1 i x39 x27 x28 x29 x30 x31 x32 x3).
                          specialize (Hmqecb2 mqatts2 i x39 x27 x28 x29 x30 x31 x32 x16).
                          destruct Hmqecb1;eauto. 
                          destruct Hmqecb2;eauto.
                          simpljoin.

                          do 7 eexists. split. eauto. split. eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          split. eauto. split. eauto.

                          (*mq_ed_equiv*)
                          split. unfolds. 
                          match goal with H:mq_ed_equiv _ _ _ _ |- _ => rename H into Hmqed end.
                          unfolds in Hmqed. 
                          lets Hmq_:Hmq2 Hgetmqatts1 Hgetmqatts2.
                          destruct Hmq_ as(eo1 & eo2 & wtp & flgs & mms & msz & cms & csltidxs & Hmq_).
                          destruct Hmq_ as (Hmq1_ & Hmq2_ & Hmq3_). inverts Hmq1_. inverts Hmq2_.
                          destruct Hmq3_ as [Hmq3_|[Hmq3_|Hmq3_]]. simpljoin. tryfalse. simpljoin. tryfalse.
                          simpljoin. match goal with H: Valid_Addr _ = Valid_Addr _ |- _=> inverts H end.
                          match goal with H: mq_ed_equiv _ _ _ _ |- _ => rename H into Hmqedequiv end.
                          unfolds in Hmqedequiv. 
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          rewrite Hoabsecblsid1_ in H61. rewrite Hoabsecblsid2_ in H62. inverts H61. inverts H62.
                          
                          match goal with H: intspecs.tickstep x _ _ _ |- _ => rename H into Htickstep1 end.
                          match goal with H: intspecs.tickstep x10 _ _ _ |- _ => rename H into Htickstep2 end.

                          (*tidls_equiv2*)
                          lets H_:tickisr_els_same Htickstep1.
                          inverts H_.
                          inverts Htickstep1.

                          unfolds in Htpi1.
                          destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabs & Hgettcbs).
                          match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs. inverts Hgetabs.
                          rewrite emp_sem in Hgettcbs. tryfalse.
                          
                          lets H_:tickisr_els_same Htickstep2.
                          inverts H_.
                          inverts Htickstep2.
                          
                          destruct Htpi2 as (pr'' & tcbs' & st'' & msg0' & sus' & Hgetabs' & Hgettcbs').
                          match goal with H: get O0 abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs'. inverts Hgetabs'.
                          rewrite emp_sem in Hgettcbs'. tryfalse.

                          match goal with H: get x3 x29 = Some (absmsgq x23 x47 x48, x49) |- _=> rename H into Hr1 end.
                          match goal with H: get x16 x29 = Some (absmsgq x24 x44 x45, x46) |- _=> rename H into Hr2 end.
                          match goal with H: get x3 x29 = Some (x30, x32) |- _=> rename H into Hr1_ end.
                          match goal with H: get x16 x29 = Some (x31, x50) |- _=> rename H into Hr2_ end.
                          rewrite Hr1 in Hr1_. rewrite Hr2 in Hr2_. inverts Hr1_. inverts Hr2_.
                          simpljoin. 
                          match goal with H: absmsgq x23 x47 x48 = absmsgq x0 x11 x27 |- _ => inverts H end.
                          match goal with H: absmsgq x24 x44 x45 = absmsgq x0 x11 x28 |- _ => inverts H end.
                          do 4 eexists. split. eauto. split. eauto.

                          match goal with H: tidls_equiv x27 x28 O1 O2 |- _ => rename H into Htidlsequiv end.
                          unfolds in Htidlsequiv.
                          destruct Htidlsequiv as (Hlength & Htidlsequiv).
                          unfolds. split. eauto. intros.
                          specialize (Htidlsequiv pr3).
                          
                          destruct Htidlsequiv as (Htidlsequiv1 & Htidlsequiv2).
                          split. introv Hp. destruct Htidlsequiv1.
                          destruct Hp as (t' & Hin & Hp).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 t').
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved12 Hp. eauto.
                          
                          match goal with H: In _ _ /\ task_prio_id _ _ _ |- _ => rename H into Htask end.
                          destruct Htask as (Htin & Htask).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 x23).
                          specialize (Hpriopreserved2 pr3 x23).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved21  Htask. eauto.

                          introv Hp. destruct Hp as (t' & Htin & Htask).
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H' : Hpriopreserved22 Htask.
                          destruct Htidlsequiv2. eexists. split;eauto.
                          match goal with H: In _ _ /\ task_prio_id O1 _ _ |- _ => rename H into Hp end.
                          destruct Hp as (Hpin & Hptask).
                          specialize(Hpriopreserved1 td' pr3 x23).
                          specialize(Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets H''': Hpriopreserved11 Hptask.
                          eexists. split;eauto.


                          (*tidls_equiv2*)
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          rewrite Hoabsecblsid1_ in H47. rewrite Hoabsecblsid2_ in H54. inverts H47. inverts H54.
                          
                          match goal with H: intspecs.tickstep x _ _ _ |- _ => rename H into Htickstep1 end.
                          match goal with H: intspecs.tickstep x10 _ _ _ |- _ => rename H into Htickstep2 end.
                          lets H_:tickisr_els_same Htickstep1.
                          inverts H_.
                          inverts Htickstep1.

                          unfolds in Htpi1.
                          destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabs & Hgettcbs).
                          match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs. inverts Hgetabs.
                          rewrite emp_sem in Hgettcbs. tryfalse.
                          
                          lets H_:tickisr_els_same Htickstep2.
                          inverts H_.
                          inverts Htickstep2.
                          
                          destruct Htpi2 as (pr'' & tcbs' & st'' & msg0' & sus' & Hgetabs' & Hgettcbs').
                          match goal with H: get O0 abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs'. inverts Hgetabs'.
                          rewrite emp_sem in Hgettcbs'. tryfalse.

                          match goal with H: get x3 x39 = Some (absmsgq x23 x47 x48, x49) |- _=> rename H into Hr1 end.
                          match goal with H: get x16 x39 = Some (absmsgq x24 x44 x45, x46) |- _=> rename H into Hr2 end.
                          match goal with H: get x3 x39 = Some (x40, x42) |- _=> rename H into Hr1_ end.
                          match goal with H: get x16 x39 = Some (x41, x43) |- _=> rename H into Hr2_ end.
                          rewrite Hr1 in Hr1_. rewrite Hr2 in Hr2_. inverts Hr1_. inverts Hr2_.
                          unfolds in H57. simpljoin.
                          match goal with H: absmsgq x23 x47 x48 = absmsgq x0 x11 x37 |- _ => inverts H end.
                          match goal with H: absmsgq x24 x44 x45 = absmsgq x0 x11 x38 |- _ => inverts H end.
                          unfolds. 

                          match goal with H: tidls_equiv x42 x43 O1 O2 |- _ => rename H into Htidlsequiv end.
                          unfolds in Htidlsequiv.
                          destruct Htidlsequiv as (Hlength & Htidlsequiv).
                          split. eauto. intros.
                          specialize (Htidlsequiv pr3).
                          
                          destruct Htidlsequiv as (Htidlsequiv1 & Htidlsequiv2).
                          split. introv Hp. destruct Htidlsequiv1.
                          destruct Hp as (t' & Hin & Hp).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 t').
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved12 Hp. eauto.
                          
                          match goal with H: In _ _ /\ task_prio_id _ _ _ |- _ => rename H into Htask end.
                          destruct Htask as (Htin & Htask).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 x23).
                          specialize (Hpriopreserved2 pr3 x23).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved21  Htask. eauto.

                          introv Hp. destruct Hp as (t' & Htin & Htask).
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H' : Hpriopreserved22 Htask.
                          destruct Htidlsequiv2. eexists. split;eauto.
                          match goal with H: In _ _ /\ task_prio_id O1 _ _ |- _ => rename H into Hp end.
                          destruct Hp as (Hpin & Hptask).
                          specialize(Hpriopreserved1 td' pr3 x23).
                          specialize(Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets H''': Hpriopreserved11 Hptask.
                          eexists. split;eauto.

                          (*data_equiv-> ports_equiv*)
                          split. 
                          match goal with H: ports_equiv td _ _ |- _=> rename H into Hportsequiv end.
                          unfolds in Hportsequiv.
                          simpljoin. 
                          unfolds. do 4 eexists. split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          
                          match goal with H:intspecs.tickstep x x0 x2 x3 |- _ => rename H into Hstep1 end.
                          match goal with H:intspecs.tickstep x10 x11 x15 x16 |- _ => rename H into Hstep2 end.
                          lets Hx1:tickisr_els_same Hstep1.
                          lets Hx2:tickisr_els_same Hstep2.
                          subst x3. subst x16.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.

                          intros.
                          specialize(H51 a).
                          specialize(H51 H11). simpljoin.
                          split. eauto. split.
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          match goal with H:get O1 absecblsid = Some (absecblist x27) |- _ => rename H into Hgetabsecb1 end.
                          match goal with H:get O2 absecblsid = Some (absecblist x28) |- _ => rename H into Hgetabsecb2 end.
                          rewrite Hoabsecblsid1_ in Hgetabsecb1.
                          rewrite Hoabsecblsid2_ in Hgetabsecb2.
                          inverts Hgetabsecb1.
                          inverts Hgetabsecb2.
                          eauto.

                          intros. 
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          match goal with H:get O1 absecblsid = Some (absecblist x27) |- _ => rename H into Hgetabsecb1 end.
                          match goal with H:get O2 absecblsid = Some (absecblist x28) |- _ => rename H into Hgetabsecb2 end.
                          rewrite Hoabsecblsid1_ in Hgetabsecb1.
                          rewrite Hoabsecblsid2_ in Hgetabsecb2.
                          inverts Hgetabsecb1.
                          inverts Hgetabsecb2.

                          lets H':H56 H57 H58.
                          unfolds in H'.
                          destruct H' as (Hleng & H').
                          unfolds. split. eauto.
                          split. introv H''. destruct H'' as (t' & Hin & H'').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).

                          lets Ha: Hpriopreserved12 H''.
                          specialize(H' pr1).
                          destruct H' as (H1' & H2').
                          destruct H1'. eexists. split;eauto.

                          specialize (Hpriopreserved2 td').
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          simpljoin.
                          match goal with H:task_prio_id O2 pr1 x0 |- _ => lets Hp : Hpriopreserved21 H end.
                          eexists. split;eauto.

                          intros. 
                          simpljoin.
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          specialize (Hpriopreserved2 td').
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          match goal with H: task_prio_id _ pr1 x0 |- _ => rename H into Hp end.
                          eapply Hpriopreserved22 in Hp.
                          specialize (H' pr1).
                          destruct H' as (Hp1 & Hp2).
                          destruct Hp2. eexists. split;eauto.
                          match goal with H: In x3 tls1 /\ task_prio_id O1 pr1 x3 |- _=> destruct H as (Hin & Hpt) end.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved1 pr1 x3).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          eapply Hpriopreserved11 in Hpt.
                          eexists. split;eauto.

                          (*bufferequiv*)
                          destruct Htkernelcap as (Hbuffer&Htkernelcap).
                          split.
                          unfolds in Hbuffer.
                          destruct Hbuffer as (els1 & els2 & Hgetecb1 & Hgetecb2 & Hbuf).
                          unfolds.
                          do 2 eexists.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          split. eauto. split. rewrite set_a_get_a. eauto.
                          lets H1' :tickisr_els_same H11.
                          lets H2' :tickisr_els_same H37.
                          eapply join_get_get_l in H4;eauto.
                          eapply join_get_get_l in H23;eauto.
                          rewrite Hgetecb1 in H4. rewrite Hgetecb2 in H23.
                          inverts H4. inverts H23.
                          subst x0. subst x11.
                          introv Hbufindom.
                          lets Hdd:Hbuf Hbufindom.
                          destruct Hdd as (Heid & Hdd).
                          split. eauto.
                          introv Heid1 Heid2.
                          lets Hddd: Hdd Heid1 Heid2.
                          destruct Hddd as (Hmqed & Htided).
                          split.
                          unfolds in Hmqed. unfolds.
                          destruct Hmqed as (ms & mlen & pws1 & pws2 & Habs1 & Habs2 & Htideq').
                          do 4 eexists. split. eauto. split. eauto.
                          unfolds in Htideq'. unfolds.
                          destruct Htideq' as (Hlen & Htideq').
                          split. eauto.
                          intros.
                          split. introv Ht. destruct Ht as (t' & Hin & Htpi1').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1_ : Hpriopreserved12 Htpi1'.
                          lets Htideq_:Htideq' pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq1. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi2': Hpriopreserved21 Htpi2_.
                          eexists. eauto.
                          
                          introv Ht. destruct Ht as (t' & Hin & Htpi2').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi1_ : Hpriopreserved22 Htpi2'.
                          lets Htideq_:Htideq' pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq2. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 x0).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1': Hpriopreserved11 Htpi2_.
                          eexists. split;eauto.

                          unfolds in Htided. unfolds.
                          destruct Htided as (Hlen & Htided).
                          split. eauto.
                          intros.
                          split. introv Ht. destruct Ht as (t' & Hin & Htpi1').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1_ : Hpriopreserved12 Htpi1'.
                          lets Htideq_:Htided pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq1. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi2': Hpriopreserved21 Htpi2_.
                          eexists. eauto.
                          
                          introv Ht. destruct Ht as (t' & Hin & Htpi2').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi1_ : Hpriopreserved22 Htpi2'.
                          lets Htideq_:Htided pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq2. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 x0).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1': Hpriopreserved11 Htpi2_.
                          eexists. split;eauto.
                          (*bufferequiv end*)
                          
                          (*data_equiv->cap_equiv*)
                          unfolds in Htkernelcap.
                          simpljoin.
                          unfolds. do 2 eexists. split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          eauto.
                          intros.
                          specialize (H47 pr1).
                          specialize (H47 H52).
                          simpljoin.
                          split. eauto. 
                          intros. specialize(H53 idx). specialize(H53 H52).
                          simpljoin.
                          split. split. intros.
                          match goal with H:(exists objp, spec_aux_defs.mq_ptr O1 idx objp) <-> (exists objp, spec_aux_defs.mq_ptr O2 idx objp)|- _ => rename H into Hmqptr end.
                          destruct Hmqptr as (Hmqptr1 & Hmqptr2).
                          destruct Hmqptr1.
                          simpljoin.
                          match goal with H: spec_aux_defs.mq_ptr _ idx x31  |- _ =>rename H into Hmqptr' end.
                          unfolds in Hmqptr'.
                          simpljoin.
                          match goal with H:get _ absmqattrid = _ |- _ => rename H into Habsmq end.
                          repeat(try rewrite set_a_get_a in Habsmq ;rewrite set_a_get_a' in Habsmq;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 8 eexists.
                          split;eauto.

                          match goal with H: spec_aux_defs.mq_ptr O2 idx _ |- _ => unfolds in H end.
                          simpljoin.
                          eexists. unfolds. do 8 eexists.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split;eauto.


                          introv Hmqptr.
                          match goal with H: (exists objp, spec_aux_defs.mq_ptr O1 idx objp) <-> (exists objp, spec_aux_defs.mq_ptr O2 idx objp)|- _ => rename H into Hmqptr' end.
                          destruct Hmqptr' as (Hmqptr1 & Hmqptr2).
                          destruct Hmqptr2.
                          destruct Hmqptr as(objp & Hmqptr).
                          unfolds in Hmqptr. simpljoin.
                          match goal with H:get _ absmqattrid = _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 8 eexists.
                          eauto.
                          match goal with H: spec_aux_defs.mq_ptr O1 idx _ |- _ => unfolds in H end.
                          simpljoin.
                          eexists. unfolds. do 8 eexists.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          eauto.


                          introv Hmqptr1 Hmqptr2.
                          specialize(H54 objp1 objp2).
                          destruct H54.
                          
                          unfolds in Hmqptr1.
                          simpljoin.
                          match goal with H: get _ absmqattrid= _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          unfolds. do 8 eexists. eauto.

                          unfolds in Hmqptr2.
                          simpljoin.
                          match goal with H: get _ absmqattrid= _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          unfolds. do 8 eexists. eauto.
                          split;eauto.


                          unfolds in Htclient.
                          unfolds.
                          simpljoin.
                          do 6 eexists. split. eauto. split. eauto.
                          split. eauto.
                          split;eauto.
                          match goal with H: local_envs_equiv _ _ _ _ _ |- _ => rename H into Hlocal end.
                          unfolds in Hlocal.
                          unfolds.
                          introv Hdom Htpi1' Htpi2'.
                          specialize (Hpriopreserved1 td).
                          specialize (Hpriopreserved1 pr1 t0).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 td).
                          specialize (Hpriopreserved2 pr1 t3).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets H1':Hpriopreserved12 Htpi1'.
                          lets H2':Hpriopreserved22 Htpi2'.
                          lets H':Hlocal Hdom H1' H2'.
                          eauto.


                          (*domtime left=0 right !=0*)
                          match goal with H:get O0 ksdomtimeid = _ |- _ => rename H into Hgetdomtime1 end.
                          match goal with H:get O ksdomtimeid = _ |- _ => rename H into Hgetdomtime2 end.
                          eapply join_get_get_l in Hgetdomtime1;eauto.
                          eapply join_get_get_l in Hgetdomtime2;eauto.
                          match goal with H:get O1 ksdomtimeid = get O2 ksdomtimeid |- _ =>rename H into Hdomtimeeq end.
                          rewrite Hgetdomtime1 in Hdomtimeeq.
                          rewrite Hgetdomtime2 in Hdomtimeeq.
                          lets H': Int.eq_spec. specialize(H' (x5 -ᵢ Int.one) Int.zero ). rewrite H0 in H'. simpl in H'.
                          lets H'':Int.sub_idem. specialize(H'' Int.one). rewrite <-H'' in H'.



                          eapply x_sub_one_zero in H'. inverts H'.
                          inverts Hdomtimeeq. simpljoin.
                          tryfalse.

                          (*domtime impossible*)
                          simpljoin.
                          match goal with H: Some O'= _ |- _=> inverts H end.
                          eapply join_get_set_eq_4 in H21;eauto.
                          inverts H21.
                          clear H2.

                          match goal with H: intspecs.tickisr_spec _ _ _ _   |- _ => rename H into Hint2 end.
                          inverts Hint2.
                          simpljoin.
                          destruct H36.
                          simpljoin.
                          inverts H46.
                          eapply join_get_set_eq_8 in H25;eauto.
                          inverts H25.
                          clear H37.

                          match goal with H:get O0 ksdomtimeid = _ |- _ => rename H into Hgetdomtime1 end.
                          match goal with H:get O ksdomtimeid = _ |- _ => rename H into Hgetdomtime2 end.
                          eapply join_get_get_l in Hgetdomtime1;eauto.
                          eapply join_get_get_l in Hgetdomtime2;eauto.
                          match goal with H:get O1 ksdomtimeid = get O2 ksdomtimeid |- _ =>rename H into Hdomtimeeq end.
                          rewrite Hgetdomtime1 in Hdomtimeeq.
                          rewrite Hgetdomtime2 in Hdomtimeeq.
                          lets H': Int.eq_spec. specialize(H' (x11 -ᵢ Int.one) Int.zero ). rewrite H2 in H'. simpl in H'.
                          lets H'':Int.sub_idem. specialize(H'' Int.one). rewrite <-H'' in H'.
                          eapply x_sub_one_zero in H'. inverts H'.
                          inverts Hdomtimeeq. simpljoin.
                          tryfalse.

                          (*domtime=1 both  possible*)
                          simpljoin.
                          match goal with H: Some O'0= _ |- _=> inverts H end.
                          eapply join_get_set_eq_4 in H25;eauto.
                          inverts H25.
                          clear H18.
                          
                          split.
                          unfolds.
                          introv Hdom Htpi1' Htpi2'.

                          unfolds in Hpriopreserved1.
                          specialize (Hpriopreserved1 td).
                          unfolds in Hpriopreserved1.
                          lets Hpriopreserve : Hpriopreserved1 Hdom.
                          destruct Hpriopreserve as (Hpriop1 & Hpriop2).
                          
                          unfolds in Hpriopreserved2.
                          specialize (Hpriopreserved2 td).
                          unfolds in Hpriopreserved2.
                          lets Hpriopreserve : Hpriopreserved2 Hdom.
                          destruct Hpriopreserve as (Hpriop1_ & Hpriop2_).

                          lets Ht1: Hpriop2 Htpi1'.
                          lets Ht1_: Hpriop2_ Htpi2'.
                          casetac t1 t0 Hte Htne.
                          2:{
                            casetac pr pr1 Hpe Hpne.
                            subst pr.
                            lets Hfalse: tid_unique Htpi1 Ht1.
                            tryfalse.
                            casetac t2 t3 Hte_ Htne_.
                            subst t3.
                            lets H_:prio_unique Htpi2 Ht1_.
                            subst pr0.
                            lets H__: Hd Htpi1 Ht1_.
                            rewrite Hdom in H__.
                            lets H___:Hf Htpi1 Ht1_ H__.
                            tryfalse.
                 
                            rewrite set_a_get_a';eauto.
                            rewrite set_a_get_a';eauto.
                            lets Hfalse :Htce Hdom Ht1 Ht1_.
                            simpljoin.
                            do 5 eexists.
                            split. eauto. split. eauto. split.
                            unfolds.
                            match goal with H: cmd_equiv pr1 _ _ _ _ |-_=>rename H into Hcmd end.
                            destruct Hcmd as [Hcmd|Hcmd].
                            left;eauto.
                            simpljoin.
                            right.
                            do 2 eexists.
                            split. eauto. split. eauto.
                            
                            match goal with H: get T1 t0 = _ |- _ => rename H into Hgett0 end.
                            match goal with H: get T2 t3 = _ |- _ => rename H into Hgett3 end.
                            
                            unfold eqdomO in *.
                            destruct H16 as (Heqdom1 & Heqdom1_).
                            destruct H15 as (Heqdom2 & Heqdom2_).
                            unfold eqdomO0 in *.

                            clear Hpatc1.
                            clear Hpatc2.
                            match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                            lets Htype: Hstmte.
                            unfolds in Htype.
                            destruct Htype as [Htype|Htype].
                            simpljoin.
                            split. simpl. eauto. split. simpl. eauto. eauto. eauto.

                            destruct Htype as (HnotEND & Hapi).
                            destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].

                            (*mqsend_equiv x30 x31*)
                            unfolds in Hmqsend.

                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.
                            (*mqrecv _qref_asrt *)
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.

                            (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.
                            (*mqtimedrecv_equiv end*)


                            (*qprtpost_equiv *)
                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            unfolds. 
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. 
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.


                            (*qprtpend_equiv *)
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.  

                            (*sprtpost*)
                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            eapply dom_impl_4_proof;eauto.
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            eapply dom_impl_4_proof;eauto.
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.


                            (*prtaccept_equiv *)
                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_4_proof;eauto.

                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_4_proof;eauto.

                            split;eauto.

	                          (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*intr_equiv *)
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror2.
                            match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*ABORT*)
                            destruct Habort as (Habort1 & Habort2).
                            inverts Habort1.
                            inverts Habort2.
                            split. simpl. eauto.
                            split. simpl. eauto.
                            split;eauto.


                            (*cont_equiv*)
                            match goal with H: cont_equiv _ _ _ O1 O2 |- _ => rename H into Hcont end.
                            destruct Hcont as [Hcont|Hcont].
                            destruct Hcont as (Hcont1 & Hcont2 & Hcont3).
                            unfolds. left. split. eauto. split. eauto. eauto.

                            destruct Hcont as (c1 & c2 & ke & ks' & Hcont1 & Hcont2 & Hcont3).
                            unfolds. right. do 4 eexists. split. eauto. split. eauto.


                            destruct Hcont3 as [Hcont3|Hcont3].
                            simpljoin. unfolds. left. split. eauto. split. eauto. eauto.
                            
                            simpljoin.
                            match goal with H: get T1 t0 = _ |- _ => rename H into Hgett0 end.
                            match goal with H: get T2 t3 = _ |- _ => rename H into Hgett3 end.
                            
                            unfold eqdomO in *.
                            destruct H15 as (Heqdom1 & Heqdom1_).
                            destruct H16 as (Heqdom2 & Heqdom2_).
                            unfold eqdomO0 in *.

                            clear Hpatc1.
                            clear Hpatc2.
                            match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                            lets Htype: Hstmte.
                            unfolds in Htype.
                            destruct Htype as [Htype|Htype].

                            simpljoin.
                            unfolds. right. do 2 eexists. split. eauto. split. eauto.
                            split. simpl. eauto. split. simpl. eauto. eauto. eauto.

                            destruct Htype as (HnotEND & Hapi).
                            unfolds. right. do 2 eexists. split. eauto. split. eauto.
                            destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].

                            
                            (*mqsend_equiv x30 x31*)
                            unfolds in Hmqsend.

                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqsend_qref_asrt_preserve.
                            destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.
                            (*mqrecv _qref_asrt *)
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                            }
                            split.
                            eapply mqrecv_qref_asrt_preserve.
                            destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.

                            (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 

                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.
                            (*mqtimedrecv_equiv end*)

                            (*qprtpost_equiv *)
                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply qprtpost_asrt_preserve.
                            destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.


                            (*qprtpend_equiv *)
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply qprtpend_asrt_preserve.
                            destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                            inverts Hget'. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto.  
                            
                            (*sprtpost*)
                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            eapply dom_impl_4_proof;eauto.
                            eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split.
                            eapply sprtpost_asrt_preserve.
                            destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            eapply dom_impl_4_proof;eauto.
                            eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            do 4 (rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                            split;eauto.


                            (*prtaccept_equiv *)
                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_4_proof;eauto.

                            split.
                            eapply prtaccept_asrt_preserve.
                            destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                            eapply dom_impl_4_proof;eauto.

                            split;eauto.

	                          (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.
                            
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*intr_equiv *)
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror1. eapply H36.
                            
                            split.
                            eapply intr_asrt_preserve.
                            destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                            eexists.
                            eapply Hntherror2.
                            match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto.

                            (*ABORT*)
                            destruct Habort as (Habort1 & Habort2).
                            inverts Habort1.
                            inverts Habort2.
                            split. simpl. eauto.
                            split. simpl. eauto.
                            split;eauto.
                             }
                          subst t0.
                          assert (t2=t3).
                          {
                            lets H_:prio_unique Htpi1 Ht1.
                            subst pr.
                            lets H_: Hf Htpi1 Htpi2 Hdom.
                            subst pr0.
                            lets H_: prio_tid_corr Htpi1 Htpi2 Ht1 Ht1_.
                            destruct H_ as [H_|H_]. simpljoin. simpljoin. tryfalse. 
                          }
                          subst t3.
                          lets Htce' : Htce Hdom Ht1 Ht1_.
                          destruct Htce' as (c1' & c2' & ke' & ks1' & ks2' & Hgtt1 & Hgtt2 & Hcmde & Hconte ).
                          match goal with H: get T2 t2 = Some (curs (hapi_code intspecs.tickisr), (ke_, ks_)) |-_=> rename H into Hgtt2' end.
                          match goal with H: get T1 t1 = Some (curs (hapi_code intspecs.tickisr), (ke1, ks1)) |-_=> rename H into Hgtt1' end.
                          rewrite Hgtt1 in Hgtt1'.
                          rewrite Hgtt2 in Hgtt2'.
                          inverts Hgtt1'. inverts Hgtt2'.
                          do 5 eexists.
                          split. rewrite set_a_get_a. eauto. split. rewrite set_a_get_a. 
                          eauto. split.
                          (*cmd_equiv*)
                          unfolds in Hcmde. destruct Hcmde as [Hcmde|Hcmde]. unfolds. 
                          destruct Hcmde as ((Hcmde1 & Hcmde2) & Hcmde3). unfolds in Hcmde1. destruct Hcmde1 as [Hcmde1|Hcmde1]. simpljoin;tryfalse. 
                          simpljoin. destruct H13. inverts H5.  eauto. 
                          unfold eqdomO in *.
                          destruct H15 as (Heqdom1 & Heqdom1_).
                          destruct H16 as (Heqdom2 & Heqdom2_).
                          unfold eqdomO0 in *.
                          simpljoin.
                          match goal with H: stmt_equiv _ _ |-_=> rename H into Hstmte end.
                          lets Htype: Hstmte.
                          unfolds in Htype.
                          destruct Htype as [Htype|Htype].
                          simpljoin.
                          unfolds. right. do 2 eexists. split. eauto. split. eauto. split. simpl. eauto. split. eauto. split;eauto.
                          unfolds. intros. match goal with H:get_hd_vl _ = _ |- _ => rename H into H_ end. unfolds in H_.
                          match goal with H:get_hd_vl _ = _ |- _ => rename H into H__ end. unfolds in H__. inverts H_. inverts H__.
                          simpl in *. tryfalse. 
                          (*stmt_equiv*)
                          unfolds.
                          right. split. introv Hfalse. simpljoin. tryfalse. right. right. right. right. right. right. right. right. right. right. left.
                          unfolds. eexists. split. instantiate(1:=1%nat). simpl. eauto. simpl. eauto.
                          (*cmd_equiv*)
                          unfolds. destruct Htype as (Htypef & Htype). inverts H5. inverts H13.
                          right. do 2 eexists. split. eauto. split. eauto. split. simpl. eauto. split. simpl. eauto.
                          split. unfolds. intros. match goal with H:get_hd_vl (SCHED;; spec_skip_step (|nil|)) = Some vl1 |-_=> rename H into H_ end. 
                          simpl in H_. inverts H_. simpl in *. match goal with H: Some nil = Some vl2 |-_=> inverts H end. induction i. simpl in *. tryfalse. simpl in *. tryfalse.
                          unfolds. right. split. introv Hfalse. destruct Hfalse as (vo1 & vo2 & H1_ & H2_ ). tryfalse. do 10 right. left. unfolds. eexists. split. instantiate(1:= 1%nat). simpl. eauto. simpl. eauto.
                          
                          (*cont_equiv*)
                          unfolds in Hconte. destruct Hconte as [Hconte|Hconte]. destruct Hconte as (Hfalse1 & Hfalse2 &Heq). unfolds. left. split. eauto. split. eauto. eauto.
                          destruct Hconte as (c1 & c2 & ke & ks' & Hkev1 & Hkev2 & Hcmde_). unfolds. right. do 4 eexists. split. eauto. split. eauto. 
                          (*cont-cmd equiv*)
                          unfolds.
                          destruct Hcmde_ as [Hcmde_|Hcmde_]. eauto. right. destruct Hcmde_ as (cd1 & cd2 & Hc1 & Hc2 & Hheadasrt1 & Hheadast2 & Hvle & Hstmte).
                          do 2 eexists. split. eauto. split. eauto. unfolds in Hstmte. destruct Hstmte as [Hstmte|Hstmte]. simpljoin. simpl in *. tryfalse. split. eauto. split. eauto. split. eauto. unfolds. left. eauto.
                        
                          destruct Hstmte as (Hfa & Hstmte).

                          unfold eqdomO in *.
                          destruct H15 as (Heqdom1 & Heqdom1_).
                          destruct H16 as (Heqdom2 & Heqdom2_).
                          unfold eqdomO0 in *.

                          lets Hapi: Hstmte.
                          
                          destruct Hapi as [Hmqsend|[Hmqrecv|[Hmqtimedrecv|[Hqportpost|[Hqportpend|[Hsprtpost|[Hprtaccept|[Hbufferpost_equiv|[Hbufferaccept_equiv|[Hbufferpend_equiv|[Hinintr|Habort]]]]]]]]]]].

                          (*mqsend_equiv x30 x31*)
                          unfolds in Hmqsend.


                          split.
                          eapply mqsend_qref_asrt_preserve.
                          destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                            }
                          split.
                          eapply mqsend_qref_asrt_preserve.
                          destruct Hmqsend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                            }
                          split;eauto. unfolds. right. eauto.
                          (*mqrecv _qref_asrt *)
                          split.
                          eapply mqrecv_qref_asrt_preserve.
                          destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                            }
                          split.
                          eapply mqrecv_qref_asrt_preserve.
                          destruct Hmqrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          unfolds.
                          intros.
                          match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                          match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                          do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                          rewrite Hc in Hc_.
                          inverts Hc_. eauto.
                          { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                            }
                          split;eauto. unfolds. right. eauto.
                          
                          
                            (*mqtimedrecv_equiv begin*)
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O1 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 

                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                              }
                            split.
                            eapply mqtimedrecv_qref_asrt_preserve.
                            destruct Hmqtimedrecv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                            unfolds.
                            intros.
                            match goal with H: get O2 absmqattrid =_ |- _=> rename H into Hc end.
                            match goal with H: get _ absmqattrid = Some (absmqattr mqs') |- _ => rename H into Hc_ end.
                            do 4 (rewrite set_a_get_a' in Hc_;[idtac|introv Hfalse;tryfalse]).
                            rewrite Hc in Hc_.
                            inverts Hc_. eauto.
                            { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                            split;eauto. unfolds. right. split;eauto.
                            (*mqtimedrecv_equiv end*)

                          (*qprtpost_equiv *)
                          split.
                          eapply qprtpost_asrt_preserve.
                          destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1. 
                          
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                            }
                          eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa_;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 4 (rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse]). eauto.

                          split.
                          eapply qprtpost_asrt_preserve.
                          destruct Hqportpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                              }
                          eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfa_;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 4 (rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse]). eauto.

                          split;eauto. unfolds. right. eauto.


                          (*qprtpend_equiv *)
                          split.
                          eapply qprtpend_asrt_preserve.
                          destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                          inverts Hget'. eauto.
                          
                          destruct Heqdom1 as (Hdomimpl1 & Hdomimpl2). 
                          { 
                              lets H':dom_impl_4_proof H20 H3 H4 H6 H12.
                              eauto.
                          }
                          split.
                          eapply qprtpend_asrt_preserve.
                          destruct Hqportpend as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          unfolds. introv Hgetosdomainortid Hget' Hdpl. do 4 (rewrite set_a_get_a' in Hget';[idtac|introv H_;tryfalse]). rewrite Hgetosdomainortid in Hget'.
                          inverts Hget'. eauto.
                          { 
                              lets H':dom_impl_4_proof H24 H7 H10 H14 H22.
                              eauto.
                            }
                          split;eauto.  unfolds. right. eauto.
                          
                          (*sprtpost*)
                          split.
                          eapply sprtpost_asrt_preserve.
                          destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          eapply dom_impl_4_proof;eauto.
                          eapply Hpriopre1_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 4 (rewrite set_a_get_a';[idtac|introv Hfal;tryfalse]). eauto.

                          split.
                          eapply sprtpost_asrt_preserve.
                          destruct Hsprtpost as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          eapply dom_impl_4_proof;eauto.
                          eapply Hpriopre2_. unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          do 4 (rewrite set_a_get_a';[idtac|introv Hfal;tryfalse]). eauto.

                          split;eauto.
                          unfolds. eauto.


                          (*prtaccept_equiv *)
                          split.
                          eapply prtaccept_asrt_preserve.
                          destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                          unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          eapply dom_impl_4_proof;eauto.

                          split.
                          eapply prtaccept_asrt_preserve.
                          destruct Hprtaccept as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                          do 3 eexists.
                          split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          unfolds. introv Ha Hb Hc. do 4 (rewrite set_a_get_a' in Hb;[idtac|introv Hfal;tryfalse]). rewrite Hb in Ha. inverts Ha. eauto.
                          eapply dom_impl_4_proof;eauto.

                          split;eauto. unfolds. eauto.

	                        (*bufferpost*)
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferpost_asrt_preserve.
                            destruct Hbufferpost_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto. unfolds. eauto.
                            
                            (*bufferaccept*)
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferaccept_asrt_preserve.
                            destruct Hbufferaccept_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto. unfolds. eauto.
                            
                            (*bufferpend*)
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl1.  eapply Hntherror1. eapply Hheadasrt1.
                            
                            split.
                            eapply bufferpend_asrt_preserve.
                            destruct Hbufferpend_equiv as (vl & vl1 & vl2 & k & Hlengvl & Hlengvl1 & Hlengvl2 & Hntherror1 & Hntherror2).
                            do 3 eexists.
                            split. eapply Hlengvl. split. eapply Hlengvl2.  eapply Hntherror2. match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                            
                            split;eauto. unfolds. eauto.

                          (*intr_equiv *)
                          split.
                          eapply intr_asrt_preserve.
                          destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                          eexists.
                          eapply Hntherror1. eapply Hheadasrt1.
                          
                          split.
                          eapply intr_asrt_preserve.
                          destruct Hinintr as ( k &  Hntherror1 & Hntherror2).
                          eexists.
                          eapply Hntherror2.
                          match goal with H: head_asrt_sat _ _ O2 |-_=>rename H into Hheadasrt2 end. eapply Hheadasrt2.
                          
                          split;eauto. unfolds. right. eauto.

                          (*ABORT*)
                          destruct Habort as (Habort1 & Habort2).
                          inverts Habort1.
                          inverts Habort2.
                          split. simpl. eauto.
                          split. simpl. eauto.
                          split;eauto. unfolds. right. eauto.


                          (*data_equiv_tskd*)
                          unfolds. 
                          
                          (*data_equiv -> ctid_equiv*)
                          split. unfolds. do 2 eexists. split. repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]).
                          split. repeat (rewrite set_a_get_a';[eauto|introv Hfa;tryfalse]). intros. 
                          lets H1_:Hpriopreserved1.
                          lets H2_:Hpriopreserved2.
                          unfolds in H1_. unfolds in H2_. specialize (H1_ td). specialize(H2_ td).
                          unfold prio_preserved_d in *. match goal with H: dom_for_prio pr1 = _ |- _=>rename H into Hdom_ end. specialize (H1_ pr1 t1 Hdom_). specialize(H2_ pr1 t2 Hdom_).
                          destruct H1_ as (H11_ & H12_). destruct H2_ as (H21_ & H22_). lets Htpi1_ : H12_ H18. destruct Htoi as (Htoi1 & Htoi2). destruct Htoi1. eexists. eapply Htpi1_.
                          lets Hpe: prio_unique Htpi1 Htpi1_. subst pr. 
                          lets Hpe_:Hf Htpi1 Htpi2 Hdom_. subst pr0. lets Hm: H21_ Htpi2. lets Hm_: prio_unique H23 Hm. eauto.

                          (*tickisr t1=t0 t2=t3 data_equiv -> bufs_equiv*)(*sched  skip *)
                          lets Htde: Htde'. unfolds in Htde. destruct Htde as (Htctid &  Htbufs & Htkernel & Htclient). unfolds in Htbufs. destruct Htbufs as (Htbufs1 & Htbufs2).
                          unfolds in Htbufs1. unfolds in Htbufs2.
                          split. unfolds. split.  unfolds. repeat(rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                          (*data_equiv->obufs_equiv *)
                          unfolds. repeat(rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.

                          (*data_equiv->kernel_data_equiv *)
                          split. destruct Htkernel as (Htkerneltask & Htkernelmq & Htkernelport & Htkernelcap).
                          unfolds. 

                          (*data_equiv->kernel_data_equiv->kernel_task_equiv*)
                          split. unfolds in Htkerneltask. destruct Htkerneltask as (tcbs1 & tcbs2 & Habstcblsid1 & Habstcblsid2 & Htkerneltask).
                          unfolds. do 2 eexists. split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. instantiate(1:= x2). eauto.
                          intros. split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. instantiate(1:= x8). eauto.
                          intros.
                          lets Htke: Htkerneltask H18. destruct Htke as (Htk1 & Htk2). 
                          split. split. intros. 
                          destruct H23. unfold prio_preserved in *. 
                          specialize(Hpriopreserved1 td). specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *. specialize(Hpriopreserved1 pr1 x10).
                          specialize (Hpriopreserved1 H18). destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Hm: Hpriopreserved12 H23. destruct Htk1 as (Htk11 & Htk12). destruct Htk11. eauto. 
                          specialize(Hpriopreserved2 pr1 x12). 
                          specialize(Hpriopreserved2 H18).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Ht:Hpriopreserved21 H25.
                          unfolds in Ht. destruct Ht as (pr' & tcbs & st & msg0 & sus & Ht).
                          destruct Ht as (Ht1&Ht2).  repeat(try rewrite set_a_get_a in Ht1;rewrite set_a_get_a' in Ht1;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 5 eexists. split. 2:eauto. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Ht1. rewrite set_a_get_a. eauto.


                          intros.
                          destruct H23. unfold prio_preserved in *. 
                          specialize(Hpriopreserved1 td). specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *. specialize(Hpriopreserved2 pr1 x10).
                          specialize (Hpriopreserved2 H18). destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Hm: Hpriopreserved22 H23. destruct Htk1 as (Htk11 & Htk12). destruct Htk12. eauto.
                          specialize(Hpriopreserved1 pr1 x12). 
                          specialize(Hpriopreserved1 H18).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Ht:Hpriopreserved11 H25.
                          unfolds in Ht. destruct Ht as (pr' & tcbs & st & msg0 & sus & Ht).
                          destruct Ht as (Ht1&Ht2).  repeat(try rewrite set_a_get_a in Ht1;rewrite set_a_get_a' in Ht1;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 5 eexists. split. 2:eauto. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Ht1. rewrite set_a_get_a. eauto.

                          intros.
                          unfold prio_preserved in *.
                          specialize(Hpriopreserved1 td).
                          specialize(Hpriopreserved2 td).
                          unfold prio_preserved_d in *.
                          specialize(Hpriopreserved1 pr1 t0).
                          specialize(Hpriopreserved2 pr1 t3).
                          match goal with H: dom_for_prio pr1 = _ |- _=> rename H into Hdom end.
                          specialize(Hpriopreserved1 Hdom).
                          specialize(Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          destruct Hpriopreserved22.
                          unfolds.
                          do 5 eexists.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          eauto.

                          destruct Hpriopreserved12.
                          unfolds.
                          do 5 eexists.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          eauto.

                          simpljoin.
                          rename H18 into Habstcblsid2'.
                          rename H26 into Habstcblsid1'.
                          rewrite Habstcblsid1 in Habstcblsid1'.
                          rewrite Habstcblsid2 in Habstcblsid2'.
                          inverts Habstcblsid1'. inverts Habstcblsid2'.
                          lets H': Htk2 H37 H38. simpljoin. subst.
                          
                          destruct Hpriopreserved11.
                          unfolds.
                          do 5 eexists. split. eauto.
                          eauto.

                          eapply join_get_get_l in H7;eauto.
                          eapply join_get_get_l in H3;eauto.
                          rewrite H3 in Habstcblsid1. inverts Habstcblsid1.
                          rewrite H7 in Habstcblsid2. inverts Habstcblsid2.
                          unfolds in H11. unfolds in H21.
                          lets H_:Htk2 H37 H38. 
                          lets H':tickisr_tcbs_preserved H37 H38 H_  H23 H25;eauto.
                          (*data_equiv->kernel_mq_equiv*)
                          split.

                          lets Hmqecb1:mq_ecb.
                          lets Hmqecb2:mq_ecb. 
                          specialize (Hmqecb1 (set
                                                 (set (set (set O1 absecblsid (absecblist x3)) abstcblsid (abstcblist x2)) ostmid
                                                    (ostm (x1 +ᵢ  Int.one))) ksdomtimeid (ksdomtime (x5 -ᵢ Int.one)))).
                          specialize (Hmqecb2 (set
                                                 (set (set (set O2 absecblsid (absecblist x9)) abstcblsid (abstcblist x8)) ostmid
                                                    (ostm (x7 +ᵢ  Int.one))) ksdomtimeid (ksdomtime (x11 -ᵢ Int.one)))).
                          repeat(try rewrite set_a_get_a in Hmqecb1;rewrite set_a_get_a' in Hmqecb1;[idtac|introv Hfa;tryfalse]).
                          repeat(try rewrite set_a_get_a in Hmqecb2;rewrite set_a_get_a' in Hmqecb2;[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a in Hmqecb1.
                          rewrite set_a_get_a in Hmqecb2.


                          unfolds in Htkernelmq. destruct Htkernelmq as (mqatts1 & mqatts2 & Hgetmq1 & Hgetmq2 & Hmq).

                          unfolds. do 2 eexists. split. 
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          introv Hmqidxdom. specialize(Hmq i). specialize(Hmq Hmqidxdom). destruct Hmq as(Hmq1 & Hmq2).
                          split. eauto. introv Hgetmqatts1 Hgetmqatts2. lets Hmqequiv: Hmq2 Hgetmqatts1 Hgetmqatts2.
                          unfold mq_equiv in *. 
                          simpljoin. do 8 eexists. split. eauto. split. eauto.
                          match goal with H: _ = Null /\ _ = Null \/ _ |- _=>rename H into Hmqequiv end.
                          destruct Hmqequiv as [Hmqequiv|[Hmqequiv|Hmqequiv]].
                          left. eauto. right. left. eauto. right. right.
                          simpljoin. 

                          specialize (Hmqecb1 mqatts1 i x25 x13 x14 x15 x16 x17 x18 x3).
                          specialize (Hmqecb2 mqatts2 i x25 x13 x14 x15 x16 x17 x18 x9).
                          destruct Hmqecb1;eauto. 
                          destruct Hmqecb2;eauto.
                          simpljoin.

                          do 7 eexists. split. eauto. split. eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          split. repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.


                          split. eauto. split. eauto.

                          (*mq_ed_equiv*)
                          split. unfolds. 
                          match goal with H:mq_ed_equiv _ _ _ _ |- _ => rename H into Hmqed end.
                          unfolds in Hmqed. 
                          lets Hmq_:Hmq2 Hgetmqatts1 Hgetmqatts2.
                          destruct Hmq_ as(eo1 & eo2 & wtp & flgs & mms & msz & cms & csltidxs & Hmq_).
                          destruct Hmq_ as (Hmq1_ & Hmq2_ & Hmq3_). inverts Hmq1_. inverts Hmq2_.
                          destruct Hmq3_ as [Hmq3_|[Hmq3_|Hmq3_]]. simpljoin. tryfalse. simpljoin. tryfalse.
                          simpljoin. match goal with H: Valid_Addr _ = Valid_Addr _ |- _=> inverts H end.
                          match goal with H: mq_ed_equiv _ _ _ _ |- _ => rename H into Hmqedequiv end.
                          unfolds in Hmqedequiv. 
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          rewrite Hoabsecblsid1_ in H49. rewrite Hoabsecblsid2_ in H50. inverts H49. inverts H50.
                          
                          match goal with H: intspecs.tickstep x _ _ _ |- _ => rename H into Htickstep1 end.
                          match goal with H: intspecs.tickstep x4 _ _ _ |- _ => rename H into Htickstep2 end.


                          (*tidls_equiv2*)
                          lets H_:tickisr_els_same Htickstep1.
                          inverts H_.
                          inverts Htickstep1.

                          unfolds in Htpi1.
                          destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabs & Hgettcbs).
                          match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs. inverts Hgetabs.
                          rewrite emp_sem in Hgettcbs. tryfalse.
                          
                          lets H_:tickisr_els_same Htickstep2.
                          inverts H_.
                          inverts Htickstep2.
                          
                          destruct Htpi2 as (pr'' & tcbs' & st'' & msg0' & sus' & Hgetabs' & Hgettcbs').
                          match goal with H: get O0 abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs'. inverts Hgetabs'.
                          rewrite emp_sem in Hgettcbs'. tryfalse.

                          match goal with H: get x3 x15 = Some (absmsgq x10 x33 x34, x35) |- _=> rename H into Hr1 end.
                          match goal with H: get x9 x15 = Some (absmsgq x12 x30 x31, x32) |- _=> rename H into Hr2 end.
                          match goal with H: get x3 x15 = Some (x16, x18) |- _=> rename H into Hr1_ end.
                          match goal with H: get x9 x15 = Some (x17, x36) |- _=> rename H into Hr2_ end.
                          rewrite Hr1 in Hr1_. rewrite Hr2 in Hr2_. inverts Hr1_. inverts Hr2_.
                          simpljoin. 
                          match goal with H: absmsgq x10 x33 x34 = absmsgq x0 x6 x13 |- _ => inverts H end.
                          match goal with H: absmsgq x12 x30 x31 = absmsgq x0 x6 x14 |- _ => inverts H end.
                          do 4 eexists. split. eauto. split. eauto.

                          match goal with H: tidls_equiv x13 x14 O1 O2 |- _ => rename H into Htidlsequiv end.
                          unfolds in Htidlsequiv.
                          destruct Htidlsequiv as (Hlength & Htidlsequiv).
                          unfolds. split. eauto. intros.
                          specialize (Htidlsequiv pr3).
                          
                          destruct Htidlsequiv as (Htidlsequiv1 & Htidlsequiv2).
                          split. introv Hp. destruct Htidlsequiv1.
                          destruct Hp as (t' & Hin & Hp).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 t').
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved12 Hp. eauto.
                          
                          match goal with H: In _ _ /\ task_prio_id _ _ _ |- _ => rename H into Htask end.
                          destruct Htask as (Htin & Htask).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 x10).
                          specialize (Hpriopreserved2 pr3 x10).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved21  Htask. eauto.

                          introv Hp. destruct Hp as (t' & Htin & Htask).
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H' : Hpriopreserved22 Htask.
                          destruct Htidlsequiv2. eexists. split;eauto.
                          match goal with H: In _ _ /\ task_prio_id O1 _ _ |- _ => rename H into Hp end.
                          destruct Hp as (Hpin & Hptask).
                          specialize(Hpriopreserved1 td' pr3 x10).
                          specialize(Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets H''': Hpriopreserved11 Hptask.
                          eexists. split;eauto.


                          (*tidls_equiv2*)
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          rewrite Hoabsecblsid1_ in H35. rewrite Hoabsecblsid2_ in H42. inverts H35. inverts H42.
                          
                          match goal with H: intspecs.tickstep x _ _ _ |- _ => rename H into Htickstep1 end.
                          match goal with H: intspecs.tickstep x4 _ _ _ |- _ => rename H into Htickstep2 end.
                          lets H_:tickisr_els_same Htickstep1.
                          inverts H_.
                          inverts Htickstep1.

                          unfolds in Htpi1.
                          destruct Htpi1 as (pr' & tcbs & st & msg0 & sus & Hgetabs & Hgettcbs).
                          match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs. inverts Hgetabs.
                          rewrite emp_sem in Hgettcbs. tryfalse.
                          
                          lets H_:tickisr_els_same Htickstep2.
                          inverts H_.
                          inverts Htickstep2.
                          
                          destruct Htpi2 as (pr'' & tcbs' & st'' & msg0' & sus' & Hgetabs' & Hgettcbs').
                          match goal with H: get O0 abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
                          lets Hoabstcblsid_: Hoabstcblsid.
                          eapply join_get_get_l in Hoabstcblsid_;eauto.
                          rewrite Hoabstcblsid_ in Hgetabs'. inverts Hgetabs'.
                          rewrite emp_sem in Hgettcbs'. tryfalse.

                          match goal with H: get x3 x25 = Some (absmsgq x10 x33 x34, x35) |- _=> rename H into Hr1 end.
                          match goal with H: get x9 x25 = Some (absmsgq x12 x30 x31, x32) |- _=> rename H into Hr2 end.
                          match goal with H: get x3 x25 = Some (x26, x28) |- _=> rename H into Hr1_ end.
                          match goal with H: get x9 x25 = Some (x27, x29) |- _=> rename H into Hr2_ end.
                          rewrite Hr1 in Hr1_. rewrite Hr2 in Hr2_. inverts Hr1_. inverts Hr2_.
                          unfolds in H45. simpljoin.
                          match goal with H: absmsgq x10 x33 x34 = absmsgq x0 x6 x23 |- _ => inverts H end.
                          match goal with H: absmsgq x12 x30 x31 = absmsgq x0 x6 x24 |- _ => inverts H end.
                          unfolds. 

                          match goal with H: tidls_equiv x28 x29 O1 O2 |- _ => rename H into Htidlsequiv end.
                          unfolds in Htidlsequiv.
                          destruct Htidlsequiv as (Hlength & Htidlsequiv).
                          split. eauto. intros.
                          specialize (Htidlsequiv pr3).
                          
                          destruct Htidlsequiv as (Htidlsequiv1 & Htidlsequiv2).
                          split. introv Hp. destruct Htidlsequiv1.
                          destruct Hp as (t' & Hin & Hp).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 t').
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved12 Hp. eauto.
                          
                          match goal with H: In _ _ /\ task_prio_id _ _ _ |- _ => rename H into Htask end.
                          destruct Htask as (Htin & Htask).
                          eexists. split. eauto. 
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr3 x10).
                          specialize (Hpriopreserved2 pr3 x10).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H': Hpriopreserved21  Htask. eauto.

                          introv Hp. destruct Hp as (t' & Htin & Htask).
                          assert(exists td, dom_for_prio pr3 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr3 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          
                          lets H' : Hpriopreserved22 Htask.
                          destruct Htidlsequiv2. eexists. split;eauto.
                          match goal with H: In _ _ /\ task_prio_id O1 _ _ |- _ => rename H into Hp end.
                          destruct Hp as (Hpin & Hptask).
                          specialize(Hpriopreserved1 td' pr3 x10).
                          specialize(Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets H''': Hpriopreserved11 Hptask.
                          eexists. split;eauto.



                          (*data_equiv-> ports_equiv*)
                          split. 
                          match goal with H: ports_equiv td _ _ |- _=> rename H into Hportsequiv end.
                          unfolds in Hportsequiv.
                          simpljoin. 
                          unfolds. do 4 eexists. split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          
                          match goal with H:intspecs.tickstep x _ _ _ |- _ => rename H into Hstep1 end.
                          match goal with H:intspecs.tickstep x4 _ _ _ |- _ => rename H into Hstep2 end.
                          lets Hx1:tickisr_els_same Hstep1.
                          lets Hx2:tickisr_els_same Hstep2.
                          subst x3. subst x9.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          rewrite set_a_get_a. eauto.

                          intros.
                          specialize(H39 a).
                          specialize(H39 H11). simpljoin.
                          split. eauto. split.
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          match goal with H:get O1 absecblsid = Some (absecblist x13) |- _ => rename H into Hgetabsecb1 end.
                          match goal with H:get O2 absecblsid = Some (absecblist x14) |- _ => rename H into Hgetabsecb2 end.
                          rewrite Hoabsecblsid1_ in Hgetabsecb1.
                          rewrite Hoabsecblsid2_ in Hgetabsecb2.
                          inverts Hgetabsecb1.
                          inverts Hgetabsecb2.
                          eauto.

                          intros. 
                          match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid1 end. 
                          lets Hoabsecblsid1_: Hoabsecblsid1.
                          eapply join_get_get_l in Hoabsecblsid1_;eauto.
                          match goal with H: get O0 absecblsid = _ |-_=> rename H into Hoabsecblsid2 end. 
                          lets Hoabsecblsid2_: Hoabsecblsid2.
                          eapply join_get_get_l in Hoabsecblsid2_;eauto.
                          match goal with H:get O1 absecblsid = Some (absecblist x13) |- _ => rename H into Hgetabsecb1 end.
                          match goal with H:get O2 absecblsid = Some (absecblist x14) |- _ => rename H into Hgetabsecb2 end.
                          rewrite Hoabsecblsid1_ in Hgetabsecb1.
                          rewrite Hoabsecblsid2_ in Hgetabsecb2.
                          inverts Hgetabsecb1.
                          inverts Hgetabsecb2.

                          lets H':H44 H45 H46.

                          unfolds in H'.
                          destruct H' as (Hleng & H').
                          unfolds. split. eauto.
                          split. introv H''. destruct H'' as (t' & Hin & H'').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).

                          lets Ha: Hpriopreserved12 H''.
                          specialize(H' pr1).
                          destruct H' as (H1' & H2').
                          destruct H1'. eexists. split;eauto.
                          
                          
                          specialize (Hpriopreserved2 td').
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          simpljoin.
                          match goal with H:task_prio_id O2 pr1 x0 |- _ => lets Hp : Hpriopreserved21 H end.
                          eexists. split;eauto.

                          intros. 
                          simpljoin.
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          specialize (Hpriopreserved2 td').
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          match goal with H: task_prio_id _ pr1 x0 |- _ => rename H into Hp end.
                          eapply Hpriopreserved22 in Hp.
                          specialize (H' pr1).
                          destruct H' as (Hp1 & Hp2).
                          destruct Hp2. eexists. split;eauto.
                          match goal with H: In x3 tls1 /\ task_prio_id O1 pr1 x3 |- _=> destruct H as (Hin & Hpt) end.
                          specialize (Hpriopreserved1 td').
                          specialize (Hpriopreserved1 pr1 x3).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          eapply Hpriopreserved11 in Hpt.
                          eexists. split;eauto.

                          (*bufferequiv*)
                          destruct Htkernelcap as (Hbuffer&Htkernelcap).
                          split.
                          unfolds in Hbuffer.
                          destruct Hbuffer as (els1 & els2 & Hgetecb1 & Hgetecb2 & Hbuf).
                          unfolds.
                          do 2 eexists.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          split. eauto. split. rewrite set_a_get_a. eauto.
                          lets H1' :tickisr_els_same H11.
                          lets H2' :tickisr_els_same H21.
                          eapply join_get_get_l in H4;eauto.
                          eapply join_get_get_l in H10;eauto.
                          rewrite Hgetecb1 in H4. rewrite Hgetecb2 in H10.
                          inverts H4. inverts H10.
                          subst x0. subst x6.
                          introv Hbufindom.
                          lets Hdd:Hbuf Hbufindom.
                          destruct Hdd as (Heid & Hdd).
                          split. eauto.
                          introv Heid1 Heid2.
                          lets Hddd: Hdd Heid1 Heid2.
                          destruct Hddd as (Hmqed & Htided).
                          split.
                          unfolds in Hmqed. unfolds.
                          destruct Hmqed as (ms & mlen & pws1 & pws2 & Habs1 & Habs2 & Htideq').
                          do 4 eexists. split. eauto. split. eauto.
                          unfolds in Htideq'. unfolds.
                          destruct Htideq' as (Hlen & Htideq').
                          split. eauto.
                          intros.
                          split. introv Ht. destruct Ht as (t' & Hin & Htpi1').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1_ : Hpriopreserved12 Htpi1'.
                          lets Htideq_:Htideq' pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq1. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi2': Hpriopreserved21 Htpi2_.
                          eexists. eauto.
                          
                          introv Ht. destruct Ht as (t' & Hin & Htpi2').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi1_ : Hpriopreserved22 Htpi2'.
                          lets Htideq_:Htideq' pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq2. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 x0).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1': Hpriopreserved11 Htpi2_.
                          eexists. split;eauto.

                          unfolds in Htided. unfolds.
                          destruct Htided as (Hlen & Htided).
                          split. eauto.
                          intros.
                          split. introv Ht. destruct Ht as (t' & Hin & Htpi1').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 t').
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1_ : Hpriopreserved12 Htpi1'.
                          lets Htideq_:Htided pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq1. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 x0).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi2': Hpriopreserved21 Htpi2_.
                          eexists. eauto.
                          
                          introv Ht. destruct Ht as (t' & Hin & Htpi2').
                          assert(exists td, dom_for_prio pr1 = td). eexists. eauto.
                          match goal with H: exists _, dom_for_prio _ = _ |- _ => rename H into Hdom end.
                          destruct Hdom as (td' & Hdom).
                          unfold prio_preserved in *.
                          specialize (Hpriopreserved2 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved2 pr1 t').
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets Htpi1_ : Hpriopreserved22 Htpi2'.
                          lets Htideq_:Htided pr1. destruct Htideq_ as (Htideq1 & Htideq2).
                          destruct Htideq2. eexists. split. eauto. eauto.
                          destruct H4 as (Hin2 & Htpi2_).
                          specialize (Hpriopreserved1 td').
                          unfold prio_preserved_d in *.
                          specialize (Hpriopreserved1 pr1 x0).
                          specialize (Hpriopreserved1 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          lets Htpi1': Hpriopreserved11 Htpi2_.
                          eexists. split;eauto.
                          (*bufferequiv end*)

                          (*data_equiv->cap_equiv*)
                          unfolds in Htkernelcap.
                          simpljoin.
                          unfolds. do 2 eexists. split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          eauto.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]).
                          eauto.
                          intros.
                          specialize (H35 pr1).
                          specialize (H35 H40).
                          simpljoin.
                          split. eauto. 
                          intros. specialize(H41 idx). specialize(H41 H40).
                          simpljoin.
                          split. split. intros.
                          match goal with H:(exists objp, spec_aux_defs.mq_ptr O1 idx objp) <-> (exists objp, spec_aux_defs.mq_ptr O2 idx objp)|- _ => rename H into Hmqptr end.
                          destruct Hmqptr as (Hmqptr1 & Hmqptr2).
                          destruct Hmqptr1.
                          simpljoin.
                          match goal with H: spec_aux_defs.mq_ptr _ idx x17  |- _ =>rename H into Hmqptr' end.
                          unfolds in Hmqptr'.
                          simpljoin.
                          match goal with H:get _ absmqattrid = _ |- _ => rename H into Habsmq end.
                          repeat(try rewrite set_a_get_a in Habsmq ;rewrite set_a_get_a' in Habsmq;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 8 eexists.
                          split;eauto.

                          match goal with H: spec_aux_defs.mq_ptr O2 idx _ |- _ => unfolds in H end.
                          simpljoin.
                          eexists. unfolds. do 8 eexists.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          split;eauto.
                          introv Hmqptr.
                          match goal with H: (exists objp, spec_aux_defs.mq_ptr O1 idx objp) <-> (exists objp, spec_aux_defs.mq_ptr O2 idx objp)|- _ => rename H into Hmqptr' end.
                          destruct Hmqptr' as (Hmqptr1 & Hmqptr2).
                          destruct Hmqptr2.
                          destruct Hmqptr as(objp & Hmqptr).
                          unfolds in Hmqptr. simpljoin.
                          match goal with H:get _ absmqattrid = _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          eexists. unfolds. do 8 eexists.
                          eauto.
                          match goal with H: spec_aux_defs.mq_ptr O1 idx _ |- _ => unfolds in H end.
                          simpljoin.
                          eexists. unfolds. do 8 eexists.
                          split.
                          repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[idtac|introv Hfa;tryfalse]). eauto.
                          eauto.
                          introv Hmqptr1 Hmqptr2.
                          specialize(H42 objp1 objp2).
                          destruct H42.
                          
                          unfolds in Hmqptr1.
                          simpljoin.
                          match goal with H: get _ absmqattrid= _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          unfolds. do 8 eexists. eauto.

                          unfolds in Hmqptr2.
                          simpljoin.
                          match goal with H: get _ absmqattrid= _ |- _ =>rename H into Hgetabs end.
                          repeat(try rewrite set_a_get_a in Hgetabs ;rewrite set_a_get_a' in Hgetabs;[idtac|introv Hfa;tryfalse]).
                          unfolds. do 8 eexists. eauto.
                          split;eauto.


                          unfolds in Htclient.
                          unfolds.
                          simpljoin.
                          do 6 eexists. split. eauto. split. eauto.
                          split. eauto.
                          split;eauto.
                          match goal with H: local_envs_equiv _ _ _ _ _ |- _ => rename H into Hlocal end.
                          unfolds in Hlocal.
                          unfolds.
                          introv Hdom Htpi1' Htpi2'.
                          specialize (Hpriopreserved1 td).
                          specialize (Hpriopreserved1 pr1 t0).
                          specialize (Hpriopreserved1 Hdom).
                          specialize (Hpriopreserved2 td).
                          specialize (Hpriopreserved2 pr1 t3).
                          specialize (Hpriopreserved2 Hdom).
                          destruct Hpriopreserved1 as (Hpriopreserved11 & Hpriopreserved12).
                          destruct Hpriopreserved2 as (Hpriopreserved21 & Hpriopreserved22).
                          lets H1':Hpriopreserved12 Htpi1'.
                          lets H2':Hpriopreserved22 Htpi2'.
                          lets H':Hlocal Hdom H1' H2'.
                          eauto.

                          (*impossible*)
                          inverts H16.
                          unfolds in H14. simpljoin. destruct H24.
                          simpljoin. tryfalse. simpljoin. tryfalse.

                          (*impossible*)
                          inverts H11. simpljoin. destruct H3. eauto.

                          (*impossible*)
                          simpljoin. tryfalse.

                          (*impossible*)
                          inverts H15. unfolds in H14. simpljoin. destruct H20.
                          simpljoin. tryfalse. simpljoin. tryfalse.

                          (*impossible*)
                          inverts H11. simpljoin. destruct H3. eauto.

                          (*impossible*)
                          simpljoin. tryfalse.

                          (*impossible*)
                          inverts Hin2. specialize(Habsc Habsintcont). tryfalse.

                          (*impossible*)
                          inverts Hin2. specialize(Habsc Habsintcont). tryfalse.

                          (*impossible*)
                          simpljoin.
                          lets H_:Habsc Habsintcont. tryfalse.

                          (*(* SCHED for both side *)*)
                          inverts Hin1. destruct Hin2 as [[Hin2|[Hin2|[Hin2|Hin2]]]|Hin2];inverts Hin2; specialize(Habsc Habsintcont); tryfalse.
                          match goal with H: spec_step _ _ O1 _ _ _ |-_ =>rename H into Hstep1 end.
                          match goal with H: spec_step _ _ O2 _ _ _ |-_ =>rename H into Hstep2 end.
                          inverts Hstep1. inverts Hstep2. 
                          inverts H6. inverts H3.
                          match goal with H: spec_step _ _ O1 _ _ _ |-_ =>rename H into Hstep1 end.
                          match goal with H: spec_step _ _ O2 _ _ _ |-_ =>rename H into Hstep2 end.
                          inverts Hstep1. inverts Hstep2.
                          simpl in H12. simpl in H16.
                          match goal with H: get O curtid = _|-_=>rename H into Hgettid1 end.
                          match goal with H: get O0 curtid = _|-_=>rename H into Hgettid2 end.
                          eapply join_get_get_l in Hgettid1;eauto.
                          eapply join_get_get_l in Hgettid2;eauto.
                          split.
                          (*code_equiv*)
                          unfolds.
                          introv Hdom Htpi1' Htpi2'.
                          clear Hatc1. clear Hatc2. clear Hpatc1. clear Hpatc2.

                          match goal with H: task_prio_id O1' pr t1 |- _ => rename H into Htpi1 end.
                          match goal with H: task_prio_id O2' pr0 t2 |- _ => rename H into Htpi2 end.
                          casetac t1 t3 Heq1 Hneq1.
                          2:{
                            casetac pr pr1 He Hne.
                            subst pr1.
                            lets H_:Hf Htpi1 Htpi2 Hdom.
                            subst pr0.
                            lets H_: tid_unique Htpi1 Htpi1'.
                            tryfalse.
                            casetac t2 t4 Hte Htne.
                            subst t4.
                            lets H_: prio_unique Htpi2 Htpi2'.
                            subst pr0.
                            lets H__ : Hd Htpi1 Htpi2'.
                            rewrite Hdom in H__.
                            lets H___: Hf Htpi1 Htpi2' H__.
                            tryfalse.
                            rewrite set_a_get_a';eauto.
                            rewrite set_a_get_a';eauto.
                            }
                          subst t3.
                          assert (t2=t4).
                            {
                              lets H_:prio_unique Htpi1 Htpi1'.
                              subst pr.
                              lets H_: Hf Htpi1 Htpi2 Hdom.
                              subst pr0. 
                              lets H_: prio_tid_corr Htpi1 Htpi2 Htpi1' Htpi2'.
                              destruct H_ as [H_|H_]. simpljoin. simpljoin. tryfalse. 
                            }
                          subst t4.

                          (*t1=t3 t2=t4*)
                          lets H':Htce Hdom Htpi1' Htpi2'.
                          destruct H' as (c1' & c2' & ke' & ks1' & ks2' & Hgett1 & Hgett2 & Hcmd & Hcont).
                          rewrite H5 in Hgett1. rewrite H13 in Hgett2.
                          inverts Hgett1. inverts Hgett2.
                          do 5 eexists.
                          split. rewrite set_a_get_a. eauto. split. rewrite set_a_get_a. eauto.
                          split. unfolds. 
                          unfolds in Hcmd.
                          destruct Hcmd. simpljoin. unfold not_knl_stmt in *. 
                          simpljoin. destruct H4. destruct H0. tryfalse.
                          destruct H0. simpljoin. inverts H0. destruct H3.
                          eauto.
                          simpljoin. right.
                          do 2 eexists. split. eauto. split. eauto.
                          inverts H2. inverts H3.
                          split. simpl. eauto.
                          split. simpl. eauto.
                          split.
                          unfolds.
                          introv Hgethd1 Hgethd2 Hnth1 Hnth2.
                          simpl in *.
                          inverts Hgethd1. inverts Hgethd2.
                          destruct i. simpl in *.
                          tryfalse.
                          simpl in *.
                          tryfalse.
                          
                          unfolds.
                          right. split.
                          introv Hfa. simpljoin. tryfalse.
                          right. right. right. right. right. right. right. right. right. right. left.
                          unfolds. eexists.
                          split. instantiate (1:= 2%nat).
                          simpl. eauto. simpl. eauto.
                          eauto.
                          eauto.

                          match goal with H:spec_step _ _ O1 _ _ _ |- _ =>rename H into Hstep1 end.
                          match goal with H:spec_step _ _ O2' _ _ _ |- _ =>rename H into Hstep2 end.
                          inverts Hstep2.
                          inverts H14.
                          simpljoin. destruct H4. eauto.


                          inverts H17.
                          inverts H14. simpljoin. destruct H4. eauto.
      
                          (*spec_skip_step for both side*)
                          inverts Hin1. destruct Hin2 as [[Hin2|[Hin2|[Hin2|Hin2]]]|Hin2];inverts Hin2; specialize(Habsc Habsintcont); tryfalse.
                          match goal with H:spec_step _ _ O1 _ _ _ |- _ =>rename H into Hstep1 end.
                          match goal with H:spec_step _ _ O2 _ _ _ |- _ =>rename H into Hstep2 end.
                          inverts Hstep1. inverts Hstep2.
                          match goal with H:spec_skip_step  _ O _ _  |- _ =>rename H into Hstep1 end.
                          match goal with H:spec_skip_step _  O0 _ _  |- _ =>rename H into Hstep2 end.
                          unfold spec_skip_step in Hstep1.
                          unfold spec_skip_step in Hstep2.
                          simpljoin. 
                          inverts H16. inverts H11.
                          lets Hje1:join_unique H22 H23.
                          lets Hje2:join_unique H27 H28.
                          subst O1. subst O2.
                          split;eauto.
                          unfolds. introv Hdomprio Htpi1' Htpi2'.
                          lets Htce':Htce Hdomprio Htpi1' Htpi2'.
                          match goal with H: task_prio_id O1' pr t1 |- _ =>rename H into Htpi1 end.
                          match goal with H: task_prio_id O2' pr0 t2 |- _ =>rename H into Htpi2 end.
                          casetac t1 t0 Heq1 Hneq1.
                          2:{
                            casetac pr pr1 He Hne.
                            subst pr1.
                            lets H_:Hf Htpi1 Htpi2 Hdomprio.
                            subst pr0.
                            lets H_: tid_unique Htpi1 Htpi1'.
                            tryfalse.
                            casetac t2 t3 Hte Htne.
                            subst t3.
                            lets H_: prio_unique Htpi2 Htpi2'.
                            subst pr0.
                            lets H__ : Hd Htpi1 Htpi2'.
                            rewrite Hdomprio in H__.
                            lets H___: Hf Htpi1 Htpi2' H__.
                            tryfalse.
                            rewrite set_a_get_a';eauto.
                            rewrite set_a_get_a';eauto.
                            }
                          subst t0.
                          assert (t2=t3).
                            {
                              lets H_:prio_unique Htpi1 Htpi1'.
                              subst pr.
                              lets H_: Hf Htpi1 Htpi2 Hdomprio.
                              subst pr0. 
                              lets H_: prio_tid_corr Htpi1 Htpi2 Htpi1' Htpi2'.
                              destruct H_ as [H_|H_]. simpljoin. simpljoin. tryfalse.
                            }
                          subst t3.
                          destruct Htce' as (c1' & c2' & ke' & ks1' & ks2' & Hget1' & Hget2' & Hcmd' & Hcont').
                          rewrite Hget1' in H5.
                          rewrite Hget2' in H13.
                          inverts H5. inverts H13.
                          do 5 eexists. split. rewrite set_a_get_a. eauto.
                          split. rewrite set_a_get_a. eauto.
                          split;eauto. unfolds. 
                          right.
                          unfolds in Hcmd'.
                          simpljoin.
                          destruct Hcmd' as [Hcmd'|Hcmd'].
                          simpljoin. unfolds in H3. destruct H3.
                          destruct H2. tryfalse. simpljoin.
                          inverts H2. destruct H3.
                          eauto. simpljoin.
                          inverts H0. inverts H2.
                          do 2 eexists. split. eauto.
                          split. eauto. split. simpl. eauto.
                          split. simpl. eauto.
                          split. unfolds. 
                          intros. simpl in H0. tryfalse.
                          unfolds. left. eauto.

                          unfolds in H21. simpljoin. tryfalse. 

                          unfolds in H18. simpljoin. tryfalse. 
                          (*END for both side *)
                          inverts Hin1. destruct Hin2 as [[Hin2|[Hin2|[Hin2|Hin2]]]|Hin2];inverts Hin2; specialize(Habsc Habsintcont); tryfalse.
                          match goal with H:spec_step _ _ O1 _ _ _ |- _ =>rename H into Hstep1 end.
                          match goal with H:spec_step _ _ O2 _ _ _ |- _ =>rename H into Hstep2 end.
                          inverts Hstep1.
                      }
                      {(*act = Schact*)
                        lets Hfa: speccode_not_schedact H0 Hgood Hrch1 H3 H4 H5.
                        tryfalse.
                      }

                  ++++++(*hapiexit_step for right system*)
                      assert (t0 = t2) by congruence. subst.
                      lets Hp2 : reachable_intr_ncli Hrch2.
                      unfolds in Hp2.
                      lets Hp2_ : Hp2 H13.
                      unfolds in Hp2_.
                      destruct H7.
                      tryfalse.
                      destruct H7.
                      2:tryfalse.
                      destruct H7.
                      unfolds in H11.
                      destruct H11 as (c_ & e_ & s_ & Hcct & Habscont).
                      unfold code_cur_task in Hcct.
                      rewrite H9 in Hcct.
                      rewrite H13 in Hcct.
                      inverts Hcct.
                      destruct Hp2_.
                      tryfalse.
                      destruct H11 as (cd_ & H11).
                      tryfalse.
                  ++++++(*hintex_step for right system*)
                      lets Hgodt1: reachable_good_tasks Hgood Hrch1.
                      lets Hgodt2: reachable_good_tasks Hgood Hrch2.
                      unfolds in Htce.
                      unfolds in Hctide.
                      destruct Hctide as (t1_ & t2_ & Hgcs1_ & Hgcs2_ & Hf).
                      assert (t1_ = t1) by congruence. subst.
                      assert (t2_ = t2) by congruence. subst.
                      assert (t = t1) by congruence. subst.
                      assert (t0 = t2) by congruence. subst.
                      unfold code_cur_task in *.
                      rewrite Hgs1 in Hcct1.
                      rewrite  H5 in Hcct1.
                      rewrite H9 in Hcct2.
                      rewrite H13 in Hcct2.
                      match goal with H: _ \/ _ /\ _ T1 _  \/ _ |- _ => rename H into Hact1 end.
                      match goal with H: _ \/ _ /\ _ T2 _ \/ _ |- _ => rename H into Hact2 end.
                      destruct Hact1 as [Hact1|[Hact1|Hact1]].
                      tryfalse.
                      2:tryfalse.
                      destruct Hact2 as [Hact2|[Hact2|Hact2]].
                      tryfalse.
                      2:tryfalse.
                      destruct Hact1 as (Hact1 & Hinintr1).
                      destruct Hact2 as (Hact2 & Hinintr2).
                      unfolds in Hinintr1.
                      destruct Hinintr1 as (c1' & ke1' & ks1' & Hcct1' & Habsintcont1).
                      unfolds in Hcct1'.
                      rewrite Hgcs1_ in Hcct1'.
                      rewrite H5 in Hcct1'.
                      inverts Hcct1'.
                      unfolds in Hinintr2.
                      destruct Hinintr2 as (c2' & ke2' & ks2' & Hcct2' & Habsintcont2).
                      unfolds in Hcct2'.
                      rewrite Hgcs2_ in Hcct2'.
                      rewrite H13 in Hcct2'.
                      inverts Hcct2'.
                      lets Hpatc1: reachable_apicode_type_c Hpu Hrch1.
                      lets Hpatc2: reachable_apicode_type_c Hpu Hrch2.
                      unfold pool_apicode_type_c in *.
                      lets Hatc1: Hpatc1 H5.
                      lets Hatc2: Hpatc2 H13.
                      clear Hpatc1.
                      clear Hpatc2.
                      unfold apicode_type_c in *.
                      assert (Hcurs1: exists cd0, curs (hapi_code cd) = curs (hapi_code cd0));eauto.
                      assert (Hcurs2: exists cd, curs (hapi_code (END None)) = curs (hapi_code cd));eauto.
                      destruct Hcurs1 as (cd0 & Hcurs1).
                      destruct Hcurs2 as (cd1 & Hcurs2).
                      lets Hatc1_:Hatc1 Habsintcont1 Hcurs1.
                      lets Hatc2_:Hatc2 Habsintcont2 Hcurs2.
                      clear Hatc1.
                      clear Hatc2.
                      destruct Hatc1_ as (iid1 & Hintspec1 & Hin1).
                      destruct Hatc2_ as (iid2 & Hintspec2 & Hin2).
                      simpl in Hin1.
                      simpl in Hin2.
                      inverts Hcurs1.
                      inverts Hcurs2.
                      destruct Hin2 as [Hin2|Hin2].
                      destruct Hin2 as [Hin2|[Hin2|[Hin2|Hin2]]];tryfalse.
                      destruct Hin2 as (vs2 & Hin2).

                      inverts Hcct1.
                      inverts Hcct2.
                      lets H':Habsc Habsintcont1.
                      
                      destruct Hin1 as [Hin1|Hin1].
                      destruct Hin1 as [Hin1|[Hin1|[Hin1|Hin1]]];inverts Hin1;tryfalse.
                      destruct Hin1 as (vs & Hin1).
                      inverts Hin1. inverts H'.
                      match goal with H: spec_step _ _ O1 _ _ _ |- _ => rename H into Hstep1 end.
                      inverts Hstep1.

        ++++(*hi_step for right system*)
            destruct H0 as [H0|[H0|H0]];tryfalse.
            lets Hfa: speccode_not_eniact H0 Hgood Hrch1 H3 H4 H5.
            tryfalse.
            destruct H0. tryfalse.

        ++++(*hswi_step for right system*)
            destruct H0 as [H0|[H0|H0]];tryfalse.
            destruct H0. tryfalse.
            lets Hfa: speccode_not_schedact H0 Hgood Hrch1 H3 H4 H5.
            tryfalse.
    +++(* hapiexit_step for left system *)
          assert (t = t1) by congruence. subst.
          lets Hp1 : reachable_intr_ncli Hrch1.
          lets Hp2 : reachable_intr_ncli Hrch2.
          unfolds in Hp1.
          lets Hp1_ : Hp1 H5.
          unfolds in Hp1_.
          destruct H0.
          tryfalse.
          destruct H0.
          2:tryfalse.
          destruct H0.
          unfolds in H6.
          destruct H6 as (c_ & e_ & s_ & Hcct & Habscont).
          unfold code_cur_task in Hcct.
          rewrite Hgs1 in Hcct.
          rewrite H5 in Hcct.
          inverts Hcct.
          destruct Hp1_.
          tryfalse.
          destruct H6 as (cd & H6).
          tryfalse.
    +++(* hintex_step for left system *)
          inverts Hstep2.
          inverts H4.
          assert (t1 = t) by congruence. subst t.
          assert (t2 = t0) by congruence. subst t0.
          unfolds in Hcct1.
          unfolds in Hcct2.
          rewrite Hgs1 in Hcct1.
          rewrite Hgs2 in Hcct2.
          rewrite H5 in Hcct1.
          rewrite H12 in Hcct2.
          match goal with H: htstep _ _ _ _ _ _ _ _ _ _ |- _ =>rename H into Hstep2 end.
          inverts Hstep2.
          ++++
              lets Hp2 : reachable_intr_ncli Hrch2.
              unfolds in Hp2.
              lets Hp2_ : Hp2 H12.
              unfolds in Hp2_.
              destruct H6.
              tryfalse.
              destruct H6.
              2:tryfalse.
              destruct H6.
              unfolds in H14.
              destruct H14 as (c_ & e_ & s_ & Hcct & Habscont).
              unfold code_cur_task in Hcct.
              rewrite H8 in Hcct.
              rewrite H12 in Hcct.
              inverts Hcct.
              destruct Hp2_.
              tryfalse.
              destruct H14 as (cd_ & H14).
              inverts H14.
              inverts H13.
              inverts H16;tryfalse.
              inverts H16;tryfalse.
          ++++
              match goal with H: hapistep _ _ _ _ _ _ |- _ => rename H into Hstep2 end.
              inverts Hstep2.
              match goal with H: _ \/ _ \/ _ |- _ => rename H into Hact end.
              destruct Hact as [Hact|[Hact|Hact]];tryfalse.
              destruct Hact as (Hact & Hintr).
              unfolds in Hintr. destruct Hintr as (c' & ke' & ks' & Hcct_ & Habsint).
              unfolds in Hcct_. rewrite H8 in Hcct_.
              rewrite H12 in Hcct_. inverts Hcct1. inverts Hcct2.
              destruct Habse as (Habse1 & Habse2). inverts Hcct_.
              lets Hfalse : Habse2 Habsint. lets Hfa: Habsc Hfalse. tryfalse.
              (*impossible*)
              match goal with H: _ \/ _ /\ in_intr _ O1' \/ _ |- _ => rename H into Hact end.
              destruct Hact as [Hact|[Hact|Hact]];tryfalse.
              destruct Hact as (Hact & Hintr).
              unfolds in Hintr. destruct Hintr as (c' & ke' & ks' & Hcct_ & Habsint).
              unfolds in Hcct_. rewrite Hgs1 in Hcct_. 
              rewrite H5 in Hcct_. inverts Hcct_.
              inverts Hcct1. inverts Hcct2.
              lets Hfalse: Habsc Habsint.
              inverts Hfalse.
              inverts H10.
              (*impossible*)
              match goal with H: _ \/ _ /\ in_intr _ O1' \/ _ |- _ => rename H into Hact end.
              destruct Hact as [Hact|[Hact|Hact]];tryfalse.
              destruct Hact as (Hact & Hintr).
              unfolds in Hintr. destruct Hintr as (c' & ke' & ks' & Hcct_ & Habsint).
              unfolds in Hcct_. rewrite Hgs1 in Hcct_. 
              rewrite H5 in Hcct_. inverts Hcct1. inverts Hcct2.
              destruct Habse as (Habse1 & Habs2).
              inverts Hcct_. lets Halse : Habse1 Habsint.
              tryfalse.
              (*intexstep for both side possible*)
              inverts Hcct1. inverts Hcct2.
              split;eauto.
              unfolds. introv Hdomprio Htpi1' Htpi2'.
              match goal with H: task_prio_id O1' pr _ |- _=> rename H into Htpi1 end.
              match goal with H: task_prio_id O2' pr0 _ |- _=> rename H into Htpi2 end.
              destruct Hctide as (t1' & t2' & Hgoc1_ & Hgoc2_ & Hf).
              rewrite Hgs1 in Hgoc1_. inverts Hgoc1_.
              rewrite Hgs2 in Hgoc2_. inverts Hgoc2_.

              casetac t1' t0 Heq1 Hneq1.
              2:{
                casetac pr pr1 He Hne.
                subst pr1.
                lets H_:Hf Htpi1 Htpi2 Hdomprio.
                subst pr0.
                lets H_: tid_unique Htpi1 Htpi1'.
                tryfalse.
                casetac t2' t3 Hte Htne.
                subst t3.
                lets H_: prio_unique Htpi2 Htpi2'.
                subst pr0.
                lets H__ : Hd Htpi1 Htpi2'.
                rewrite Hdomprio in H__.
                lets H___: Hf Htpi1 Htpi2' H__.
                tryfalse.
                rewrite set_a_get_a';eauto.
                rewrite set_a_get_a';eauto.
                }
              subst t0.
              assert (t2'=t3).
                {
                  lets H_:prio_unique Htpi1 Htpi1'.
                  subst pr.
                  lets H_: Hf Htpi1 Htpi2 Hdomprio.
                  subst pr0. 
                  lets H_: prio_tid_corr Htpi1 Htpi2 Htpi1' Htpi2'.
                  destruct H_ as [H_|H_]. simpljoin. simpljoin. tryfalse.
                }
              subst t3.
              unfolds in Htce.
              lets Htce_:Htce Hdomprio Htpi1' Htpi2'.
              simpljoin.
              rewrite H5 in H2. rewrite H12 in H9.
              inverts H2. inverts H9.
              match goal with H: cont_equiv _ _ _ _ _ |- _ => rename H into Hcont end.
              unfolds in Hcont. 
              destruct Hcont as [Hcont|Hcont].
              simpljoin. destruct H2. eauto.
              simpljoin. inverts H2. inverts H3.
              do 5 eexists.
              split. rewrite set_a_get_a. eauto.
              split. rewrite set_a_get_a. eauto.
              split;eauto. 
              unfolds. 
              lets H1_: reachable_kevt_nnest Hrch1.
              lets H2_: reachable_kevt_nnest Hrch2.
              unfold pool_kevt_no_nest in *.
              lets Hnknl1: H1_ H5.
              lets Hnknl2: H2_ H12.
              unfold kevt_no_nest in *.
              left. split. introv Hfa. simpljoin. 
              simpl in *. tryfalse.
              split. introv Hfa. simpljoin. 
              simpl in *. tryfalse.
              eauto.
+(* htistep for left system *)
  inverts H5.
  inverts Hstep2.
  inverts H5.
  ++(*hapistep for right*)
    inverts H12.
    inverts H11.
    destruct H0 as [H0|[H0|H0]];tryfalse.
    lets Hfa: speccode_not_eniact H0 Hgood Hrch2 H5 H12 H13.
    tryfalse.
    destruct H0. tryfalse.
  ++(*htistep for both  system possible *)
    assert (t1 = t) by congruence. subst t.
    assert (t2 = t0) by congruence. subst t0.
    unfolds in Hctide.
    destruct Hctide as (t1_ & t2_ & Hgetotid1 & Hgetotid2 & Hf).
    rewrite Hgs1 in Hgetotid1. rewrite Hgs2 in Hgetotid2.
    inverts Hgetotid1. inverts Hgetotid2.
    destruct Htoi as (Htoi1 & Htoi2).
    inverts H13.
    split;eauto.
    unfolds. introv Hdomprio Htpi1' Htpi2'.
    inverts H9. inverts H.
    unfold int_spec in *.
    do 6 (destruct i;simpl in H4;tryfalse).
    do 6 (destruct i0;simpl in H5;tryfalse).
    inverts H4. inverts H5.
    casetac t1_ t1 Hte1 Htne1.
    {
      casetac t2_ t2 Hte2 Htne2.
      {
        subst t2. subst t1.
        lets Htce': Htce Hdomprio Htpi1' Htpi2'.
        do 5 eexists. split. rewrite set_a_get_a. eauto.
        split. rewrite set_a_get_a. eauto.
        split. unfolds. right. 
        do 2 eexists. split. eauto. split. eauto.
        split. simpl. eauto.
        split. simpl. eauto.
        split. unfolds. introv Hgethd1 Hgethd2 Hnth1 Hnth2.
        simpl in Hgethd1. inverts Hgethd1. destruct i.
        simpl in Hnth1. tryfalse. simpl in Hnth1. tryfalse.
        unfolds. right. split. introv Hfalse. 
        simpljoin. tryfalse.
        right. right. right. right. right. right. right. right. right. right. left.
        unfolds. eexists. split. instantiate(1:= 0%nat).
        simpl. eauto. simpl. eauto.
        destruct Htce' as (c1_ & c2_ & ke_ & ks1_ & ks2_ & Hgttc1 & Hgttc2 & Hcmd_ & Hcont_).
        rewrite H3 in Hgttc1. inverts Hgttc1. rewrite H11 in Hgttc2.  inverts Hgttc2.
        unfolds in Hcont_. destruct Hcont_ as [Hcont_|Hcont_].
        simpljoin. 
        unfolds. right. do 4 eexists. split. eauto. split. eauto. eauto.
        simpljoin. simpl in H12. tryfalse.
      }
      subst t1. lets Htce' : Htce Hdomprio Htpi1' Htpi2'.
      lets H': Htoi1. destruct H'. eauto.
      lets H': Hf Htpi1' H Hdomprio. subst x.
      lets Hfalse: tid_unique Htpi2' H. tryfalse.
    }
    {
      casetac t2_ t2 Hte2 Htne2.
      subst t2. lets H': Htoi2. destruct H'. eauto.
      lets H_: Hd H Htpi2'. rewrite Hdomprio in H_.
      lets H': Hf H Htpi2' H_. subst x.
      lets Hfalse: tid_unique H Htpi1'. tryfalse.

      (*t1_ <> t1 /\ t2_ <> t2*)
      lets Htce':Htce Hdomprio Htpi1' Htpi2'.
      simpljoin. do 5 eexists. split. rewrite set_a_get_a';eauto.
      split. rewrite set_a_get_a';eauto. split;eauto.
    }

+(* hswi_step for left system *)
  inverts Hstep2.
  inverts H5. inverts H11. inverts H10.
  destruct H6 as [Hact|[Hact|Hact]];tryfalse.
  destruct Hact. tryfalse.
  lets Hfa: speccode_not_schedact Hact Hgood Hrch2 H5 H11 H12.
  tryfalse.
  
  (*swistep possible *)
  match goal with H: (_ ,_)=(pc0,_) |- _ => inverts H end.
  match goal with H: (_ ,_)=(pc,_) |- _ => inverts H end.
  assert (t1 = t) by congruence. subst t.
  assert (t2 = t0) by congruence. subst t0.
  match goal with H: get_hprio_d O2 _ |- _ =>rename H into Hgethprio2 end.
  match goal with H: get_hprio_d O1 _ |- _ =>rename H into Hgethprio1 end.
  unfold get_hprio_d in Hgethprio1.
  unfold get_hprio_d in Hgethprio2.
  simpljoin.
  destruct Hctide as (t1_ & t2_ & Hgtid1 & Hgtid2 & Hf).
  destruct Htoi as (Htoi1 & Htoi2).
  split.
  unfolds.
  introv Hdomprio Htpi1' Htpi2'.
  lets Htpi1_:Htpi1'. lets Htpi2_:Htpi2'.
  unfolds in Htpi1'. unfolds in Htpi2'.
  destruct Htpi1' as (pr1_ & tcb1_ & st1_ & msg01_ & sus1_ & Hgetoabstcblsid1 & Hgettcb1).
  destruct Htpi2' as (pr2_ & tcb2_ & st2_ & msg02_ & sus2_ & Hgetoabstcblsid2 & Hgettcb2).
  rewrite set_a_get_a' in Hgetoabstcblsid1.
  rewrite set_a_get_a' in Hgetoabstcblsid2.
  casetac t1 t0 Hte1 Htne1.
  {
    casetac t2 t3 Hte2 Htne2.
    {
      subst t0.
      subst t3.
      lets Htce':Htce.
      unfolds in Htce'.
      unfold task_prio_id in Htce'.
      specialize (Htce' pr t1 t2).
      destruct Htce'.
      eauto. do 5 eexists. split;eauto.
      do 5 eexists. split;eauto.
      simpljoin.
      rewrite H12 in H4. inverts H4.
      rewrite H17 in H11. inverts H11.
      do 5 eexists.
      split. rewrite set_a_get_a;eauto.
      split. rewrite set_a_get_a;eauto.
      split.
      unfolds. right. do 2 eexists.
      split. eauto. split. eauto.
      unfolds in H27. destruct H27 as [Hcmd|Hcmd].
      simpljoin. inverts H11. unfolds in H4.
      destruct H4 as [H4|H4].
      simpljoin;tryfalse.
      simpljoin. inverts H4.
      destruct H11.  eauto.
      simpljoin. inverts H4. inverts H11.
      simpl in H27. simpl in H29.
      unfolds in H31.
      destruct H31 as [Hstmt|Hstmt].
      simpljoin;tryfalse.
      destruct Hstmt as (Hstmt1 & Hstmt2).
      destruct Hstmt2 as [Hstmt2|[Hstmt2|[Hstmt2|[Hstmt2|[Hstmt2|[Hstmt2|[Hstmt2|[Hstmt2|Hstmt2]]]]]]]].
      unfolds in Hstmt2.
      simpljoin.
      do 5 (destruct x4;simpl in H4;tryfalse).
      do 5 (destruct x10;simpl in H11;tryfalse).
      do 5 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v1.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v7.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v9.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v10.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. 
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. tryfalse.
      destruct Hin as [Hin|Hin]. tryfalse.
      simpl in Hin. tryfalse.

      unfolds in Hstmt2.
      simpljoin.
      do 5 (destruct x4;simpl in H4;tryfalse).
      do 5 (destruct x10;simpl in H11;tryfalse).
      do 5 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v1.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v7.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v9.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      simpl in Hin.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.

      (*timerecv begin*)
      unfolds in Hstmt2.
      simpljoin.
      do 6 (destruct x4;simpl in H4;tryfalse).
      do 5 (destruct x10;simpl in H11;tryfalse).
      do 5 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v1.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v3.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v8.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct v10.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      simpl in Hin.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      (*timerecv end*)

      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 2 (destruct x4;simpl in H4;tryfalse).
      do 3 (destruct x10;simpl in H11;tryfalse).
      do 3 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v2.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      inverts Hin.
      simpl in H29.
      match goal with H:nth_error _ x12 = Some(_ ;; s) |- _=>rename H into Hin2 end.
      eapply nth_error_in in Hin2.
      simpl in Hin2.
      destruct v0.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      inverts Hin2.
      split. simpl. eauto.
      split. simpl. eauto.
      split. unfolds. intros.
      simpl in H32.
      inverts H32.
      destruct i1. simpl in H34.
      tryfalse.
      simpl in H34. tryfalse.
      unfolds. right. split. 
      introv Hfa. simpljoin. tryfalse.  
      right. right. right. left.
      unfolds. do 4 eexists. split. eauto.
      split. eauto. split. eauto.
      split. instantiate(1:=9%nat). simpl. eauto.
      simpl. eauto.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.

      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 3 (destruct x4;simpl in H4;tryfalse).
      do 3 (destruct x10;simpl in H11;tryfalse).
      do 3 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v3.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      inverts Hin. 
      simpl in H29.
      match goal with H:nth_error _ x12 = Some(_ ;; s) |- _=>rename H into Hin2 end.
      eapply nth_error_in in Hin2.
      simpl in Hin2.
      destruct v1.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      inverts Hin2.
      unfolds in H29. simpl in H27. unfolds in H27.
      simpljoin.
      split. simpl. unfolds. eexists. split;eauto.
      split. simpl. unfolds. eexists. split;eauto.
      split. unfolds. introv Hgethd1 Hgethd2 Hnth1 Hnth2.
      simpl in Hgethd1. inverts Hgethd1.
      destruct i1;simpl in Hnth1;tryfalse.
      unfolds. right. split. introv Hfa.
      simpljoin. tryfalse.
      right. right. right. right. left.
      unfolds. do 4 eexists. split. eapply Hl1.
      split. eapply Hl2. split. eapply Hl3.
      split. instantiate(1:=9%nat).
      simpl. eauto. simpl. eauto.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      (*sprtpost*)
      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 2 (destruct x4;simpl in H4;tryfalse).
      do 3 (destruct x10;simpl in H11;tryfalse).
      do 3 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v2.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      (*sprtpost end*)
      (*prtaccept*)
      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 2 (destruct x4;simpl in H4;tryfalse).
      do 3 (destruct x10;simpl in H11;tryfalse).
      do 3 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v2.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      (*prtaccept end*)
      (*bufferpost*)
      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 3 (destruct x4;simpl in H4;tryfalse).
      do 2 (destruct x10;simpl in H11;tryfalse).
      do 2 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v2.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hstmt2 as [Hstmt2|Hstmt2].
      (*bufferaccept*)
      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 2 (destruct x4;simpl in H4;tryfalse).
      do 2 (destruct x10;simpl in H11;tryfalse).
      do 2 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v1.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hstmt2 as [Hstmt2|Hstmt2].
      (*bufferpend*)
      unfolds in Hstmt2.
      simpljoin.
      lets Hl1: H4. lets Hl2:H11. lets Hl3: H31.
      do 3 (destruct x4;simpl in H4;tryfalse).
      do 2 (destruct x10;simpl in H11;tryfalse).
      do 2 (destruct x11;simpl in H31;tryfalse).
      match goal with H:nth_error _ x12 = _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct v0.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      (*buffer end*)
      destruct Hstmt2 as [Hstmt2|Hstmt2].
      unfolds in Hstmt2.
      simpljoin.
      match goal with H:nth_error _ x4= _ |- _=>rename H into Hin end.
      eapply nth_error_in in Hin.
      simpl in Hin.
      destruct Hin as [Hin|Hin];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      inverts Hin. 
      simpl in H29.
      match goal with H:nth_error _ x4 = Some(_ ;; s) |- _=>rename H into Hin2 end.
      eapply nth_error_in in Hin2.
      simpl in Hin2.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      inverts Hin2.
      split. simpl. eauto.
      split. simpl. eauto.
      split.
      unfolds. introv Hgethd1 Hgethd2 Hnth1 Hnth2.
      simpl in Hgethd1. inverts Hgethd1.
      destruct i;simpl in Hnth1;tryfalse.
      unfolds. right. split. introv Hfa.
      simpljoin. tryfalse.
      right. right. right. right. right. right. right. right. right. right. left.
      unfolds. eexists.
      split. instantiate(1:=2%nat).
      simpl. eauto. simpl. eauto.
      destruct Hin2 as [Hin2|Hin2];tryfalse.
      destruct Hin as [Hin|Hin];tryfalse.
      simpljoin. tryfalse.
      unfolds.
      unfolds in H28.
      destruct H28.
      simpljoin. left. split. eauto. split;eauto.
      simpljoin. right. do 4 eexists. split. eauto.
      split. eauto. unfolds. unfolds in H28.
      destruct H28. simpljoin. left. split;eauto.
      right. simpljoin. do 2 eexists.
      split. eauto. split. eauto.
      split. 2:split. 3:split;eauto.
      unfolds in H31.
      destruct H31. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H11 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v4. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*timerecv end*)

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      (*prtaccept end*)
      (*buffer begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)

      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.


      unfolds in H31.
      destruct H31. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H11 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v8. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv end*)

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
 
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v3.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].

      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin]. 
      (*prtaccept end*)

      (*buffer begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x15;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)


      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.
    }
    subst t0.
    destruct Htoi1. eexists. unfolds.
    do 5 eexists. split;eauto.
    match goal with H: task_prio_id O2 _ _ |- _ =>rename H into Htpi2 end.
    unfolds in Htpi2. destruct Htpi2 as (pr_ & tcbs_ &st_ &msg0_ & sus_ & Hgetoabstcblsid_ & Hgettcb_).
    assert (dom_for_prio pr = dom_for_prio x4).
    eapply Hd.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split;eauto.
    rewrite Hdomprio in H12. 
    rewrite Hgs1 in Hgtid1. rewrite Hgs2 in Hgtid2.
    inverts Hgtid1. inverts Hgtid2.
    assert (pr= x4). eapply Hf.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split;eauto.
    eauto.
    subst x4.
    assert (t2_=t3). eapply tid_unique.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split. eapply Hgetoabstcblsid2.
    eauto. tryfalse.
  }
  {
    casetac t2 t3 Hte2 Htne2.
    subst t3.
    destruct Htoi2. eexists. unfolds.
    do 5 eexists. split;eauto.
    match goal with H: task_prio_id O1 _ _ |- _ =>rename H into Htpi1 end.
    unfolds in Htpi1. destruct Htpi1 as (pr_ & tcbs_ &st_ &msg0_ & sus_ & Hgetoabstcblsid_ & Hgettcb_).
    assert (dom_for_prio x4 = dom_for_prio pr).
    eapply Hd.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split;eauto.
    rewrite Hdomprio in H12. 
    rewrite Hgs1 in Hgtid1. rewrite Hgs2 in Hgtid2.
    inverts Hgtid1. inverts Hgtid2.
    assert (x4=pr). eapply Hf.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split;eauto.
    eauto.
    subst x4.
    assert (t1_=t0). eapply tid_unique.
    unfolds. do 5 eexists. split;eauto.
    unfolds. do 5 eexists. split. eapply Hgetoabstcblsid1.
    eauto. tryfalse.

    {
      lets Htce':Htce.
      unfolds in Htce'.
      unfold task_prio_id in Htce'.
      specialize (Htce' pr t0 t3).
      destruct Htce'.
      eauto. do 5 eexists. split;eauto.
      do 5 eexists. split;eauto.
      simpljoin.
      do 5 eexists.
      split. rewrite set_a_get_a';eauto.
      split. rewrite set_a_get_a';eauto.
      split.
      match goal with H: cmd_equiv pr _ _ _ _ |- _ =>rename H into Hcmd end.
      unfolds in Hcmd.
      destruct Hcmd as [Hcmd|Hcmd].
      unfolds. left. eauto.
      unfolds. simpljoin.
      right.
      do 2 eexists. split. eauto.
      split. eauto. split.

      destruct H33. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H29 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v4. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv end*)


      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as[Hin|Hin].


      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      destruct Hin as [Hin|Hin].
      (*prtaccept end*)

      (*buffer begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H11. lets Hlen1:H31. lets Hlen2:H32.
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)

      destruct Hin as[Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      match goal with H:nth_error _ _ = Some x14 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.

      split.
      unfolds in H33.
      destruct H33. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H29 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x4;simpl in Hlen;tryfalse).
      do 5 (destruct x10;simpl in Hlen1;tryfalse).
      do 5 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v8. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv end*)

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).


      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v3.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      
      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 3 (destruct x10;simpl in Hlen1;tryfalse).
      do 3 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      destruct Hin as [Hin|Hin].
      (*prtaccept end*)

      (*buffer begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x4;simpl in Hlen;tryfalse).
      do 2 (destruct x10;simpl in Hlen1;tryfalse).
      do 2 (destruct x16;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)

      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      match goal with H:nth_error _ _ = Some x15 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.
      split;eauto.
      
      unfolds.
      unfolds in H28.
      destruct H28 as [Hcont|Hcont].
      simpljoin. left. split. eauto. split; eauto.
      simpljoin.
      right.
      do 4 eexists. split. eauto. split. eauto.
      unfolds.
      unfolds in H30.
      destruct H30. simpljoin. left. split. eauto. split. eauto.
      right.
      simpljoin. do 2 eexists. split. eauto. split. eauto.
      
      split.

      destruct H33. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H29 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v5. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O1 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v4. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v6. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv end*)

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).


      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].

      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      destruct Hin as [Hin|Hin].
      (*prtaccept end*)

      (*buffer begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)


      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      match goal with H:nth_error _ _ = Some x12 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.

      split.
      unfolds in H33.
      destruct H33. simpljoin.
      simpl. eauto.
      simpljoin.
      destruct H29 as [Hin|[Hin|[Hin|[Hin|[Hin|Hin]]]]].

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 5 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v7. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v9. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      match goal with H: mqdes_dom_qptr _ _ O2 _ |- _=>rename H into Hmq end.
      unfolds in Hmq. destruct Hmq as (Hmq1 & Hmq2). unfolds.
      split. eauto. unfolds. unfolds in Hmq2. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. eauto. eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 6 (destruct x14;simpl in Hlen;tryfalse).
      do 5 (destruct x15;simpl in Hlen1;tryfalse).
      do 5 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v1. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v3. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v8. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct v10. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      unfolds. split. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. simpljoin. eauto. match goal with H:mqdes_dom_qptr _ _ _ _ |- _=> rename H into H' end.
      unfolds in H'. destruct H' as (mqs' & eo' & wtp' & qfls' & mmsg' & msz' & cmsgs' & sltidxs & Hgetoabsmqattrid & Hgetmqs & Hoth). 
      unfolds. do 8 eexists. split. rewrite set_a_get_a'. 2:introv Hfa;tryfalse. eauto. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      (*timerecv end*)

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v3.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      unfolds. match goal with H:has_port _ _ _  |- _=> rename H into H' end.
      unfolds in H'. destruct H' as [H'|H']. left. eauto. right. unfolds in H'. destruct v;simpl in H';tryfalse.
      simpljoin. unfolds. do 8 eexists. split. rewrite set_a_get_a'. eauto. introv Hfa. tryfalse. eauto.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].

      (*sprtpost begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.
      
      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      match goal with H: prt_indom _ _ _ /\ has_prtpost_cap _ _ |- _=>rename H into Hport end.
      destruct Hport as (Hport1 & Hport2). split. unfolds.
      unfolds in Hport1. simpljoin. eexists. split;eauto.
      unfolds. unfolds in Hport2. simpljoin.
      match goal with H:spec_aux_defs.tps_tst_corr _ _ |- _=>rename H into Htps end.
      unfolds in Htps. simpljoin. 
      do 3 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. split. unfolds. eexists.
      split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. split;eauto.

      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*sprtpost end*)
      (*prtaccept begin*)
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 3 (destruct x15;simpl in Hlen1;tryfalse).
      do 3 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      match goal with H: has_port _ _ _  |- _=>rename H into Hport1 end.
      unfolds in Hport1. destruct Hport1 as [Hport1|Hport1].
      left. eauto. right. unfolds in Hport1. unfolds.
      destruct v;tryfalse. simpljoin. 
      do 8 eexists. split. rewrite set_a_get_a';[idtac|introv Hfa_;tryfalse].
      eauto. eauto. 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      destruct Hin as [Hin|Hin].
      (*prtaccept end*)

      (*buffer begin*)
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v2.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 2 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      lets Hlen: H29. lets Hlen1:H33. lets Hlen2:H34.
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      do 3 (destruct x14;simpl in Hlen;tryfalse).
      do 2 (destruct x15;simpl in Hlen1;tryfalse).
      do 2 (destruct x18;simpl in Hlen2;tryfalse).
      simpl in Hnth1.
      destruct v0.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]). 
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).
      (*bufferend*)


      destruct Hin as [Hin|Hin].
      unfolds in Hin.
      simpljoin. 
      match goal with H:nth_error _ _ = Some x13 |- _=>rename H into Hnth1 end.
      eapply nth_error_in in Hnth1.
      simpl in Hnth1.
      try repeat (destruct Hnth1 as [Hnth1|Hnth1];[inverts Hnth1;simpl in *;eauto;try tryfalse|simpl in Hnth1;try tryfalse]).

      simpljoin. simpl in *. eauto.
      split;eauto.

    }
  }
  
  introv Hfa;tryfalse.
  introv Hfa;tryfalse.


  unfolds.
  split.
  unfolds.
  do 2 eexists.
  split. rewrite set_a_get_a. eauto.
  split. rewrite set_a_get_a. eauto.
  introv Htpi1' Htpi2' Hdomprio.
  unfold task_prio_id in Htpi1'.
  unfold task_prio_id in Htpi2'.
  destruct Htpi1' as (pr1' & tcbs1' & st1' & msg01' & sus1' & Hget1 & Hgettcb1').
  destruct Htpi2' as (pr2' & tcbs2' & st2' & msg02' & sus2' & Hget2 & Hgettcb2').
  rewrite set_a_get_a' in Hget1.
  rewrite set_a_get_a' in Hget2.
  2:introv Hfa;tryfalse.
  2:introv Hfa;tryfalse.
  rewrite Hget1 in H2. rewrite Hget2 in H.
  inverts H2. inverts H.
  rewrite Hgettcb1' in H14.
  rewrite Hgettcb2' in H5.
  inverts H14. inverts H5.
  rewrite H16 in H26. rewrite H9 in H26.
  rewrite Hdomprio in H26.
  inverts H26.
  unfolds in Hkernelde.
  destruct Hkernelde as (Hkernelde1 & Hkernelde2 & Hkernelde3 & Hkernelde4).
  unfolds in Hkernelde1.
  simpljoin.
  assert (dom_for_prio x3 = dom_for_prio x9).
  eauto.
  lets H':H17 H26.
  simpljoin.
  rewrite Hget1 in H2. inverts H2.
  rewrite Hget2 in H14. inverts H14.
  destruct H27 as (Hc1&Hc2).
  destruct Hc2.
  eexists. unfolds. do 5 eexists.
  split. eapply Hget2. eapply Hgettcb2'.
  unfolds in H2.
  simpljoin. rewrite Hget1 in H2. inverts H2.
  lets H': H28 H14 Hgettcb2'.
  simpljoin.

  casetac x t' Hte Htne.
  {
    subst t'. rewrite H14 in Hgettcb1'.
    inverts Hgettcb1'.
    eauto.
  }
  {
    lets H': H18 Htne H14 H8 H26.
    eapply Int.ltu_inv in H'.
    destruct H'.
    casetac x9 x3 Hpe Hpne.
    subst x3. 
    auto with zarith.
    assert (dom_for_prio x9 = dom_for_prio x9);eauto.
    lets H': H17 H29.
    simpljoin.
    destruct H30 as (Hc1' & Hc2').
    destruct Hc1'. eexists. unfolds.
    do 5 eexists. split. eapply Hget1. eapply Hgettcb1'.
    unfolds in H29. simpljoin.
    rewrite Hget2 in H29. inverts H29.
    casetac x4 t'0 Hte' Htne'.
    {
      subst x4. rewrite H30 in Hgettcb2'.
      inverts Hgettcb2'. eauto.
    }
    lets H': H31 Hgettcb1' H30.
    simpljoin.
    lets H': H13 Htne' H30 H15 H.
    eapply Int.ltu_inv in H'.
    destruct H'.
    rewrite H32 in H27.

    int auto.
  }
  lets Htde_:Htde'.
  destruct Htde_ as (Hd1 & Hd2 & Hd3 & Hd4).
  split.
  unfolds.
  split. unfolds.
  unfolds in Hd2.
  destruct Hd2 as (Hd21 & Hd22).
  unfolds in Hd21.
  simpljoin.
  do 2 eexists. split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  destruct Hd2 as (Hd21 & Hd22).
  unfolds in Hd22.
  unfolds.
  simpljoin.
  do 2 eexists. split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  unfolds in Hd3.
  destruct Hd3 as(Hd31 & Hd32 & Hd33).
  split.
  unfolds.
  split.
  unfolds.
  unfolds in Hd31.
  simpljoin.
  do 2 eexists. split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  intros. split. split.
  specialize(H30 pr).
  specialize(H30 H31).
  intros. destruct H32.
  unfolds in H32. simpljoin.
  rewrite set_a_get_a' in H32.
  destruct H30 as (He1 & He2).
  destruct He1.
  eexists. unfolds. do 5 eexists.
  split;eauto.
  unfolds in H30.
  simpljoin.
  eexists. unfolds. 
  do 5 eexists.
  split. rewrite set_a_get_a'.
  eauto.
  introv Hfa;tryfalse. eauto.
  introv Hfa;tryfalse.
  specialize(H30 pr).
  specialize(H30 H31).
  intros. destruct H32.
  unfolds in H32. simpljoin.
  rewrite set_a_get_a' in H32.
  destruct H30 as (He1 & He2).
  destruct He2.
  eexists. unfolds. do 5 eexists.
  split;eauto.
  unfolds in H30. simpljoin.
  eexists. unfolds. do 5 eexists. split.
  rewrite set_a_get_a'. eauto.
  introv Hfa;tryfalse.
  eauto. introv Hfa;tryfalse.
  intros.
  specialize(H30 pr).
  specialize(H30 H31).
  simpljoin.
  lets H': H34 H32 H33.
  eauto.

  split.
  unfolds in Hd32.
  simpljoin.
  unfolds.
  do 2 eexists. split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  split. rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  intros.
  lets H':H30 H31.
  simpljoin.
  split;eauto.
  intros.
  lets H': H33 H34 H35.
  unfolds.
  unfolds in H'.
  simpljoin.
  do 8 eexists.
  split. eauto.
  split. eauto.
  eauto.
  destruct H38 as [H'|[H'|H']].
  left. eauto. right. left. eauto.
  right. right.
  simpljoin.
  do 7 eexists.
  split. eauto.
  split. eauto.
  split. rewrite set_a_get_a'. eauto.
  introv Hfa;tryfalse.
  split. rewrite set_a_get_a'. eauto.
  introv Hfa;tryfalse.
  split. eauto. split. eauto.
  split. unfolds.
  unfolds in H42. simpljoin.
  do 4 eexists. split. eauto. split. eauto.
  unfolds. 
  unfolds in H42. simpljoin.
  split. eauto.
  split.
  intros. specialize (H37 pr).
  destruct H37 as (He1 & He2).
  destruct H32.
  destruct H42. simpljoin. unfolds in H44. 
  simpljoin. destruct He1.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H44.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H46.
  unfolds in H47. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  intros. specialize (H37 pr).
  destruct H37 as (He1 & He2).
  destruct H42. simpljoin. unfolds in H42. 
  simpljoin. destruct He2.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H42.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H45.
  unfolds in H46. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  
  unfolds.
  unfolds in H43.
  simpljoin. split. eauto. split.
  intros. specialize (H37 pr).
  destruct H37 as (He1 & He2).
  destruct H43. simpljoin. unfolds in H43. 
  simpljoin. destruct He1.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H43.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H45.
  unfolds in H46. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  intros. specialize (H37 pr).
  destruct H37 as (He1 & He2).
  destruct H43. simpljoin. unfolds in H43. 
  simpljoin. destruct He2.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H43.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H45.
  unfolds in H46. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.

  destruct Hd33 as (Hd33 & Hd34).
  split. unfolds. unfolds in Hd33.
  simpljoin.
  do 4 eexists.
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  intros.
  lets H': H31 H32.
  simpljoin. split. eauto.
  split;eauto.
  intros. lets H': H35 H36 H37.
  unfolds in H'.
  simpljoin. unfolds. split. eauto. split.
  intros. specialize (H39 pr).
  destruct H39 as (He1 & He2).
  destruct H40. simpljoin. unfolds in H40. 
  simpljoin. destruct He1.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H40.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H42.
  unfolds in H43. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.
  intros. specialize (H39 pr).
  destruct H39 as (He1 & He2).
  destruct H40. destruct H39. simpljoin. unfolds in H40. 
  simpljoin. destruct He2.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a' in H40.
  eauto.
  introv Hfa;tryfalse. eauto.
  destruct H42.
  unfolds in H43. simpljoin.
  eexists. split;eauto.
  unfolds. do 5 eexists. split.
  rewrite set_a_get_a'.
  eauto. introv Hfa;tryfalse.
  eauto.

  split.
  (*buffer*)
  destruct Hd34 as (Hd34 & Hd35).
  unfolds in Hd34.
  unfolds.
  destruct Hd34 as (els1 & els2 & Hecb1 & Hecb2 & Hbuf).
  do 2 eexists. split. rewrite set_a_get_a'. eauto.
  introv Hfa;tryfalse.
  split. rewrite set_a_get_a'. eauto.
  introv Hfa;tryfalse.
  introv Hspec.
  lets Hbuf':Hbuf Hspec.
  destruct Hbuf' as (Helse & Hbuf').
  split. eauto.
  introv Hels1 Hels2.
  lets Hbuf_:Hbuf' Hels1 Hels2.
  destruct Hbuf_ as (Hmq & Htid).
  split.
  unfolds in Hmq. unfolds.
  simpljoin.
  do 4 eexists. split. eauto.
  split. eauto.
  unfolds in H27. unfolds.
  destruct H27 as (Hlen & Htpi).
  split. eauto.
  intros.
  specialize (Htpi pr).
  unfold task_prio_id.
  rewrite set_a_get_a'. rewrite set_a_get_a'.
  unfold task_prio_id in Htpi.
  eauto.
  introv Hfa;tryfalse.
  introv Hfa;tryfalse.
  
  unfolds. unfolds in Htid.
  destruct Htid as (Hlen & Htpi).
  split. eauto.
  intros.
  specialize (Htpi pr).
  unfold task_prio_id.
  rewrite set_a_get_a'. rewrite set_a_get_a'.
  unfold task_prio_id in Htpi.
  eauto.
  introv Hfa;tryfalse.
  introv Hfa;tryfalse.
  (*buffer end*)
  destruct Hd34 as (_ & Hd34).
  unfolds in Hd34.
  simpljoin.
  unfolds. intros.
  do 2 eexists.
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  intros. lets H': H27 H28. simpljoin.
  split. eauto.
  intros.
  lets H' : H30 H28.
  simpljoin.
  split.
  destruct H31 as(He1 & He2).
  split.
  intros. destruct H31.
  unfolds in H31. simpljoin.
  destruct He1. eexists.
  unfolds. do 8 eexists.
  split. rewrite set_a_get_a' in H31;[eauto|introv Hfa;tryfalse].
  split. eauto.
  destruct H34. left. eauto. right. eauto.
  unfolds in H35. simpljoin.
  eexists. unfolds.
  do 8 eexists. 
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. eauto.
  destruct H37.
  left. eauto. right. eauto.
  intros. destruct H31.
  unfolds in H31. simpljoin.
  destruct He2. eexists.
  unfolds. do 8 eexists.
  split. rewrite set_a_get_a' in H31;[eauto|introv Hfa;tryfalse].
  split. eauto.
  destruct H34. left. eauto. right. eauto.
  unfolds in H35. simpljoin.
  eexists. unfolds.
  do 8 eexists. 
  split. rewrite set_a_get_a';[eauto|introv Hfa;tryfalse].
  split. eauto.
  destruct H37.
  left. eauto. right. eauto.

  intros.
  unfolds in H33. unfolds in H34.
  simpljoin.
  rewrite set_a_get_a' in H33;[eauto|introv Hfa;tryfalse].
  rewrite set_a_get_a' in H34;[eauto|introv Hfa;tryfalse].
  specialize(H32 objp1 objp2).
  destruct H32. unfolds.
  do 8 eexists. split. eauto. split. eauto. eauto.
  unfolds.
  do 8 eexists. split. eauto. split. eauto. eauto.
  split;eauto.
  
  unfolds in Hd4.
  simpljoin.
  unfolds.
  do 6 eexists. split. eauto. split. eauto.
  split. eauto. split;eauto.
  unfolds in H28.
  unfolds. intros.
  lets H':H28 H12.
  unfolds in H17. unfolds in H33.
  simpljoin.
  rewrite set_a_get_a' in H17;[eauto|introv Hfa;tryfalse].
  rewrite set_a_get_a' in H33;[eauto|introv Hfa;tryfalse].
  specialize(H' t0 t3).
  destruct H'.
  unfolds. do 5 eexists. split;eauto.
  unfolds. do 5 eexists. split;eauto.
  eauto.

+(* ~ flowsTo SchedDom (TaskDom td) *)
  false.
  eapply Hstepdm'.
  eapply sched_flows_to_all.
Qed.

