
Require Import memory.
Require Import sem_language. 
Require Import sem_opsem. 
Require Import aux_notations.
Require Import join_lib.
Require Import sem_tacs.

Require Import sem_sys.

Require Import rc_kevt_nonest.

(* given command is not a kernel statement *) 
Definition not_knl_stmt (c: cureval) :=   
  (exists e, c = cure e)
  \/ exists s, c = curs s /\ (~exists ss, s = hapi_code ss).

Definition nknl_nkevt c ks :=
  not_knl_stmt c -> absintcont ks = None. 

Definition pool_nknl_nkevt T :=
  forall t c ke ks,
    get T t = Some (c, (ke, ks)) -> nknl_nkevt c ks. 


Lemma no_intcont_cc:
  forall ks ks' f s E, 
    absintcont ks = None -> 
    callcont ks = Some (kcall f s E ks') -> 
    absintcont ks' = None.
Proof.
  induction ks; 
    introv Hnn Hcc; 
    try (simpl in Hcc; tryfalse); 
    try (simpl in Hnn; eapply IHks; eauto; fail).  
  inverts Hcc. simpl in Hnn. auto.
Qed.

Lemma nknl_nkevt_cstep_preserve: 
  forall pc c ke ks c' ke' ks' ge le M ge' le' M', 
    cstep pc (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') -> 
    nknl_nkevt c ks ->
    nknl_nkevt c' ks'.
Proof.
  introv Hcs Hnn.
  inverts Hcs; 
  match goal with H: (_, (_, _)) = _ |- _ => inverts H end.

  - (* estep *)
    match goal with H: estep _ _ _ _ _ _ |- _ => inverts H end; 
    unfold nknl_nkevt in *; 
    unfold not_knl_stmt in *; 
    introv H_; try (eapply Hnn; eauto; fail); 
    try (eapply Hnn; eauto; 
         right; eexists; split; eauto; introv Hf; simpljoin; tryfalse).  

  - (* sstep *)
    match goal with H: sstep _ _ _ _ _ _ _ |- _ => inverts H end;
    try (
        unfold nknl_nkevt in *; 
        unfold not_knl_stmt in *; 
        introv H_; eapply Hnn; eauto;
        right; eexists; split; eauto; introv Hf; simpljoin; tryfalse).
    inverts H. inverts H0.
    unfolds in Hnn.
    assert (Hnk: not_knl_stmt (curs (sfree nil v))).
    {
      unfolds. right. eexists. split; eauto. introv Hf; simpljoin; tryfalse. 
    }
    specialize (Hnn Hnk).
    unfolds; intros.
    eapply no_intcont_cc; eauto. 
Qed. 

Lemma knl_api: forall cd, ~not_knl_stmt (curs (hapi_code cd)).
Proof.
  intros.
  introv Hf.
  unfolds in Hf.
  inverts Hf.
  inverts H; tryfalse.
  simpljoin.
  inverts H.
  apply H0.
  eexists; eauto.
Qed.

Lemma nknl_nkevt_hapistep_preserve: 
  forall spc c ke ks O c' ke' ks' O' lau lau', 
    kevt_no_nest ks ->  
    hapistep spc (c, (ke, ks)) O lau (c', (ke', ks')) O' lau' ->  
    nknl_nkevt c ks ->
    nknl_nkevt c' ks'. 
Proof.
  introv Hnst Hstep Hnn.
  inverts Hstep.
  -
    match goal with H: (_, (_, _)) = _ |- _ => inverts H end.
    match goal with H: (_, (_, _)) = _ |- _ => inverts H end.
    unfolds.
    introv Hf. eapply knl_api in Hf. tryfalse.
  -
    unfolds.
    introv Hf. eapply knl_api in Hf. tryfalse.
  -
    unfolds. introv Hf. auto.
  -
    simpl in Hnst.
    unfolds; intros. auto.
Qed.

Lemma nknl_nkevt_htstep_preserve: 
  forall t hp c ke ks cst O c' ke' ks' cst' O' lau lau',   
    kevt_no_nest ks ->  
    htstep hp t (c, (ke, ks)) cst O lau (c', (ke', ks')) cst' O' lau' ->  
    nknl_nkevt c ks ->
    nknl_nkevt c' ks'. 
Proof.
  introv Hnst Hstep Hnn.
  inverts Hstep.
  - eapply nknl_nkevt_cstep_preserve; eauto.
  - eapply nknl_nkevt_hapistep_preserve; eauto. 
Qed.

Lemma nknl_nkevt_htistep_preserve:
  forall ospc c ke ks O c' ke' ks'  O', 
    htistep ospc (c, (ke, ks)) O (c', (ke', ks')) O' ->
    nknl_nkevt c ks ->
    nknl_nkevt c' ks'. 
Proof.
  introv Hstep Hnn.
  inverts Hstep.
  unfolds; introv Hf.
  unfolds in Hf.
  inverts Hf.
  simpljoin. tryfalse.
  simpljoin. inverts H. false. apply H0. eexists; eauto. 
Qed.

Lemma nknl_nkevt_hpstep_preserve:
  forall hp T cst O T' cst' O' lau lau', 
    pool_kevt_no_nest T -> 
    hpstep hp T cst O lau T' cst' O' lau' ->
    pool_nknl_nkevt T ->
    pool_nknl_nkevt T'. 
Proof.
  introv Hpn Hstep Hnn.
  inverts Hstep.
  -
    unfold pool_nknl_nkevt in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)). 
      eapply nknl_nkevt_htstep_preserve; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -
    unfold pool_nknl_nkevt in *. 
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)). 
      eapply nknl_nkevt_htistep_preserve; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -  
    unfold pool_nknl_nkevt in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget.
      inverts Hget.
      introv Hf. unfolds in Hf.
      inverts Hf.
      simpljoin; tryfalse.
      simpljoin. inverts H. false. apply H3. eexists; eauto.  
    * rewrite set_a_get_a' in Hget; eauto.    
Qed.

Lemma nknl_nkevt_hpstepokstar_preserve: 
  forall pu aspc sc T cst O T' cst' O' lau lau',    
    hpstepokstar (pu, (aspc, int_spec, sc)) T cst O lau T' cst' O' lau' ->
    pool_kevt_no_nest T ->     
    pool_nknl_nkevt T ->
    pool_nknl_nkevt T'. 
Proof.
  introv Hstepstar.
  remember (pu, (aspc, int_spec, sc)) as hp.
  induction Hstepstar.
  intros; auto.
  introv Hpn Hnn.
  inverts H. 
  lets H_: nknl_nkevt_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
  subst p.
  eapply pool_kevt_nnest_preserve_hpstep; eauto. 
Qed.

Require Import sem_init.

Lemma reachable_nknl_nkevt:
  forall pu aspc sc T cst O lau, 
    reachable (pu, (aspc, int_spec, sc)) T cst O lau ->
    pool_nknl_nkevt T.
Proof.
  introv Hrc.
  inverts Hrc.
  simpljoin.
  eapply nknl_nkevt_hpstepokstar_preserve; eauto.
  -
    unfold init in H0.
    destruct H0 as (Hit & His).
    unfolds in Hit.
    destruct Hit as (_ & Ha).
    unfolds. introv Hget. lets H_: Ha Hget. simpljoin.
    inverts H.
    simpl. auto.
  -
    unfold init in H0.
    destruct H0 as (Hit & His).
    unfolds in Hit.
    destruct Hit as (_ & Ha).
    unfolds. introv Hget. lets H_: Ha Hget. simpljoin.
    unfolds in H. inverts H.
    unfolds; intros.
    simpl. auto. 
Qed. 
