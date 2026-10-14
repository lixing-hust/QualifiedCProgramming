
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import seplog_lemmas.

Require Import mq_apispecs. 
Require Import osspecs. 

Require Export properties.

Require Import confidentiality_tactics. 

Set Keyed Unification.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

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
  forall pc c ke ks c' ke' ks' d ge le M ge' le' M', 
    cstep pc d (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') -> 
    nknl_nkevt c ks ->
    nknl_nkevt c' ks'.
Proof.
  introv Hcs Hnn.
  inverts Hcs; 
  match goal with H: (_, (_, _)) = _ |- _ => inverts H end.

  - (* estep *)
    match goal with H: estep _ _ _ _ _ _ _ |- _ => inverts H end; 
    unfold nknl_nkevt in *; 
    unfold not_knl_stmt in *; 
    introv H_; try (eapply Hnn; eauto; fail); 
    try (eapply Hnn; eauto; 
         right; eexists; split; eauto; introv Hf; simpljoin; tryfalse).  

  - (* sstep *)
    match goal with H: sstep _ _ _ _ _ _ _ _ |- _ => inverts H end;
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

Require Import sem_prop.

Lemma nknl_nkevt_hapistep_preserve: 
  forall spc c ke ks O c' ke' ks' O' act, 
    kevt_no_nest ks ->  
    hapistep spc (c, (ke, ks)) O (c', (ke', ks')) O' act ->  
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
  forall td t hp c ke ks cst O c' ke' ks' cst' O' act,  
    kevt_no_nest ks ->  
    htstep hp t td (c, (ke, ks)) cst O (c', (ke', ks')) cst' O' act ->  
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
  forall hp T cst O T' cst' O' act, 
    pool_kevt_no_nest T -> 
    hpstep hp T cst O T' cst' O' act ->
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
  forall hp T cst O T' cst' O',    
    hpstepokstar hp T cst O T' cst' O' ->
    pool_kevt_no_nest T ->     
    pool_nknl_nkevt T ->
    pool_nknl_nkevt T'. 
Proof.
  introv Hstepstar.
  induction Hstepstar.
  intros; auto.
  introv Hpn Hnn.
  inverts H. 
  lets H_: nknl_nkevt_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
  eapply pool_kevt_nnest_preserve_hpstep; eauto. 
Qed.

Lemma reachable_nknl_nkevt:
  forall hp T cst O, 
    reachable hp T cst O ->
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
    


Definition intr_not_clicode (C: code) :=
  match C with
    (c, (ke, ks)) =>
      absintcont ks = None \/ (exists cd, c = curs (hapi_code cd))
  end.

Definition pool_intr_not_clicode (T: tasks) :=
  forall t C, get T t = Some C -> intr_not_clicode C. 

Lemma intr_ncli_sstep_preserve:
  forall pu td c ks m c' ks' m' ke, 
    sstep pu td c ks m c' ks' m' ->
    intr_not_clicode (c, (ke, ks)) ->
    intr_not_clicode (c', (ke, ks')).
Proof.
  introv Hstep Hncli.
  inverts Hstep;
    try (
        unfolds in Hncli; 
        inverts Hncli; 
        [idtac | simpljoin; tryfalse ]; 
        unfolds; 
        simpl; auto).
  left. eapply no_intcont_cc; eauto. 
Qed.

Lemma intr_ncli_estep_preserve:
  forall td c ke m c' ke' m' ks, 
    estep td c ke m c' ke' m' -> 
    intr_not_clicode (c, (ke, ks)) ->
    intr_not_clicode (c', (ke', ks)). 
Proof.
  introv Hstep Hncli.
  inverts Hstep;
    try (
        simpl in Hncli; 
        inverts Hncli; [idtac | simpljoin; tryfalse]; 
        simpl; auto; fail).  
Qed.

Lemma intr_ncli_cstep_preserve: 
  forall pu td C m C' m', 
    cstep pu td C m C' m' ->
    intr_not_clicode C ->
    intr_not_clicode C'.
Proof.
  introv Hstep Hncli.
  inverts Hstep.
  - eapply intr_ncli_estep_preserve; eauto.
  - eapply intr_ncli_sstep_preserve; eauto. 
Qed.     

Lemma intr_ncli_specstep_preserve:
  forall sc cd O cd' O' act ke ks, 
    spec_step sc cd O cd' O' act ->
    intr_not_clicode (curs (hapi_code cd), (ke, ks)) ->
    intr_not_clicode (curs (hapi_code cd'), (ke, ks)). 
Proof.
  introv Hsstep Hnc.
  unfolds. right. eexists; eauto. 
Qed.

Lemma intr_ncli_hapistep_preserve: 
  forall spc C O C' O' act c ke ks, 
    hapistep spc C O C' O' act ->
    C = (c, (ke, ks)) -> 
    kevt_no_nest ks ->  
    intr_not_clicode C ->
    intr_not_clicode C'. 
Proof.
  introv Hstep HC Hnnest Hnc.
  inverts Hstep.
  - right. eexists; eauto.
  - inverts H0. eapply intr_ncli_specstep_preserve; eauto.
  - left. auto.
  - inverts H.
    simpl in Hnnest.
    simpl. auto. 
Qed.     


Lemma intr_ncli_htstep_preserve:
  forall hp t td C cst O C' cst' O' act ke ks c, 
    htstep hp t td C cst O C' cst' O' act ->
    C = (c, (ke, ks)) ->
    kevt_no_nest ks ->  
    intr_not_clicode C ->
    intr_not_clicode C'. 
Proof.
  introv Hstep HC Hnn Hncli.
  subst C.
  inverts Hstep.
  - eapply intr_ncli_cstep_preserve; eauto.
  - eapply intr_ncli_hapistep_preserve; eauto. 
Qed.


Lemma pool_intr_ncli_hpstep_preserve: 
  forall hp T cst O T' cst' O' act, 
    hpstep hp T cst O T' cst' O' act ->
    pool_kevt_no_nest T ->      
    pool_intr_not_clicode T ->
    pool_intr_not_clicode T'.   
Proof.
  introv Hstep Hpn Hncli. 
  inverts Hstep.
  -
    unfold pool_intr_not_clicode in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)).
      eapply intr_ncli_htstep_preserve; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      destruct C as (c_, (ke_, ks_)). 
      inverts H3.
      right. eexists; eauto. 
    * rewrite set_a_get_a' in Hget; eauto.
  -
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      right; eexists; eauto.
    * rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma pool_intr_ncli_hpstepokstar_preserve: 
  forall hp T cst O T' cst' O',    
    hpstepokstar hp T cst O T' cst' O' ->
    pool_kevt_no_nest T ->     
    pool_intr_not_clicode T ->
    pool_intr_not_clicode T'. 
Proof. 
  introv Hstepstar.
  induction Hstepstar.
  intros; auto.
  introv Hpn Hnc.
  inverts H. 
  lets H_: pool_intr_ncli_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
  eapply pool_kevt_nnest_preserve_hpstep; eauto.
Qed.

Lemma reachable_intr_ncli: 
  forall hp T cst O, 
    reachable hp T cst O ->
    pool_intr_not_clicode T. 
Proof.
  introv Hrc.
  unfolds in Hrc.
  destruct Hrc as (pu & spc & Hhp & Hex).
  destruct Hex as (T0 & cst0 & O0 & Hini & Hsstar).
  eapply pool_intr_ncli_hpstepokstar_preserve; eauto.
  - unfolds in Hini.
    destruct Hini as (Hit & _).
    unfolds in Hit.
    destruct Hit as (Heqd & Hall).
    unfolds. introv Hget.
    lets H_: Hall Hget.
    simpljoin.
    unfold nilcont in H.  inverts H.
    simpl. auto.
  - unfolds in Hini.
    destruct Hini as (Hit & _).
    unfolds in Hit.
    destruct Hit as (Heqd & Hall).
    unfolds. introv Hget. 
    lets H_: Hall Hget.
    simpljoin.
    simpl. left; auto. 
Qed.     

Require Import if_succ_gen. 

Definition ks_noint_apicode_c c ks :=
  forall cd, 
    c = curs (hapi_code cd) -> 
    absintcont ks = None ->
    ((exists fid acode ft vl,
         api_spec fid = Some (acode, ft) /\  (In cd (get_all_succs (acode vl)))) 
     \/ cd = ABORT \/ (exists vo, cd = END vo)).

Fixpoint ks_noint_apicode_cont (ks: stmtcont) :=
  match ks with
    kseq _ ks
  | kcall _ _ _ ks
  | kint _ _ _ ks
  | kassignr _ _ ks
  | kassignl _ _ ks
  | kfuneval _ _ _ _ ks
  | kif _ _ ks
  | kwhile _ _ ks
  | kret ks
    => ks_noint_apicode_cont ks
  | kevent c ke ks =>
      ks_noint_apicode_cont ks /\ 
        (absintcont ks = None ->
         forall cd,         
           c = curs (hapi_code cd) ->
           ((exists fid acode ft vl,
                api_spec fid = Some (acode, ft) /\  (In cd (get_all_succs (acode vl)))) 
            \/ cd = ABORT \/ (exists vo, cd = END vo)))
  | kstop => True
  end.

Definition ks_noint_apicode (C: code) :=
  match C with
    (c, (ke, ks)) => 
      ks_noint_apicode_c c ks /\
        ks_noint_apicode_cont ks
  end.

Definition pool_ks_no_int_apicode (T: tasks) :=
  forall t C,
    get T t = Some C ->
    ks_noint_apicode C.

Lemma ks_noint_apicode_estep_preserve:
  forall td c ke m c' ke' m' ks, 
    estep td c ke m c' ke' m' ->
    ks_noint_apicode (c, (ke, ks)) ->
    ks_noint_apicode (c', (ke', ks)).
Proof.   
  introv Hes Hkna.
  unfolds in Hkna.
  simpljoin.
  inverts Hes; 
  try (unfolds; split; [unfolds; introv Heq; inverts Heq | auto]). 
Qed.

Lemma callcont_noint_apicode: 
  forall ks f s le' ks', 
    ks_noint_apicode_cont ks ->
    callcont ks = Some (kcall f s le' ks') ->
    ks_noint_apicode_cont ks'. 
Proof.
  inductions ks; 
  introv Hkna Hk; 
    try (simpl in Hk; inverts Hk);
    try (eapply IHks; eauto; fail).
  - 
    simpl in Hkna; auto.
  -
    eapply IHks; eauto.
    simpl in Hkna. simpljoin. 
    auto.
Qed.     

Lemma ks_noint_apicode_sstep_preserve:
  forall pu td c ks m c' ks' m' ke, 
    sstep pu td c ks m c' ks' m' ->
    ks_noint_apicode (c, (ke, ks)) ->
    tskcode_no_sub_abs (c, (ke, ks)) -> 
    ks_noint_apicode (c', (ke, ks')).
Proof.
  introv Hss Hkna Htcna.
  unfolds.
  inverts Hss;
    try 
      (split; 
       [ unfolds; introv Heq Hnone; inverts Heq | 
         simpl; 
         simpl in Hkna; simpljoin; 
         auto]; fail).
  -
    split.
    +
      unfolds.
      introv Heq Hnone.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl. simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hnone.
      inverts Heq.
    +
      unfolds in Hkna.
      destruct Hkna as (_ & Hk).
      eapply callcont_noint_apicode; eauto. 
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      destruct Htcna as (Hf & _).
      simpl in Hf.
      destruct Hf; simpljoin; tryfalse.
    +
      simpl.
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna. simpljoin. auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      unfolds in Htcna.
      destruct Htcna as (_ & Hf).
      simpl in Hf.
      simpljoin.
      false.
    +
      simpl in Hkna.
      simpljoin.
      auto.
  -
    split.
    +
      unfolds.
      introv Heq Hk.
      inverts Heq.
      simpl in Htcna.
      simpljoin; tryfalse.
    +
      simpl.
      simpl in Hkna.
      simpljoin; auto.
 Qed.

Lemma ks_noint_apicode_cstep_preserve:
  forall pu td C m C' m', 
    cstep pu td C m C' m' ->
    ks_noint_apicode C ->
    tskcode_no_sub_abs C -> 
    ks_noint_apicode C'.
Proof.
  introv Hsp Hkna Hna.
  inverts Hsp.
  eapply ks_noint_apicode_estep_preserve; eauto.
  eapply ks_noint_apicode_sstep_preserve; eauto. 
Qed.   

Require Import if_good_code.

Lemma ks_noint_apicode_spec_step_preserve:
  forall cd O cd' O' act ke ks, 
    spec_step get_hprio_d cd O cd' O' act ->
    ks_noint_apicode (curs (hapi_code cd), (ke, ks)) ->
    ks_noint_apicode (curs (hapi_code cd'), (ke, ks)).
Proof.
  introv Hsps Hkna.
  unfold ks_noint_apicode in *.
  simpljoin. split; auto.
  introv Heq.
  inverts Heq.
  introv Hnone.
  specializes H; eauto.
  destruct H as [Hac | [Habt | Hend]].
  -
    simpljoin.
    lets H__: api_spec_step_succs_preserve Hsps; eauto.
    destruct H__ as [Ha | [Habt | Hend]].
    + left. do 4 eexists. split; eauto.
    + right. left. auto.
    + right; right. auto.
  -
    subst.
    inverts Hsps.
  -
    simpljoin. inverts Hsps.
Qed.

Lemma ks_noint_apicode_apistep_preserve:
  forall C O C' O' act ispc, 
    hapistep (api_spec, ispc, get_hprio_d) C O C' O' act ->
    ks_noint_apicode C ->
    ks_noint_apicode C'. 
Proof.
  introv Has Hkna.
  inverts Has.
  - 
    unfolds.
    unfolds in Hkna.
    simpljoin. split; auto.
    introv Heq Hnone.
    inverts Heq.
    left.
    do 3 eexists. exists (vl++vl').
    split; eauto. 
    unfold get_all_succs.
    simpl. left; auto.
  -
    eapply ks_noint_apicode_spec_step_preserve; eauto.
  -
    unfolds.
    unfolds in Hkna.
    simpljoin. split; auto.
    introv Heq Hnone.
    inverts Heq.
  -
    unfolds in Hkna.
    unfolds.
    destruct Hkna as (Hc & Hk).
    split.
    + 
      simpl in Hk.
      destruct Hk as (_ & H').      
      introv Hce Hke.
      subst.
      specializes H'; eauto.
    +
      simpl in Hk.
      simpljoin.
      auto.
Qed. 

Lemma ks_noint_apicode_htstep_preserve:
  forall C O C' O' cst cst' act pu ispc td t, 
    htstep (pu, (api_spec, ispc, get_hprio_d)) t td C cst O C' cst' O' act -> 
    tskcode_no_sub_abs C -> 
    ks_noint_apicode C ->
    ks_noint_apicode C'. 
Proof.
  introv Hsp Hna Hkna.
  inverts Hsp; 
    try match goal with H: (_, _) = _ |- _ => inverts H end.
  -
    eapply ks_noint_apicode_cstep_preserve; eauto.
  -
    eapply ks_noint_apicode_apistep_preserve; eauto.  
Qed.

Lemma get_hprio_d_preserve: 
  forall O O' t, 
    get O abstcblsid = get O' abstcblsid ->
    get O kscurdomid = get O' kscurdomid -> 
    get_hprio_d O t ->
    get_hprio_d O' t.
Proof.
  introv Hgteq Hgdeq Hp.
  unfold get_hprio_d in *.
  simpljoin.
  rewrite <- Hgteq.
  rewrite <- Hgdeq.
  do 6 eexists.
  split; eauto.
Qed.

Lemma pool_ks_noint_apicode_hpstep_preserve:
  forall T O T' O' cst cst' act pu ispc,
    hpstep (pu, (api_spec, ispc, get_hprio_d)) T cst O T' cst' O' act -> 
    task_pool_no_sub_abs T -> 
    pool_ks_no_int_apicode T ->
    pool_ks_no_int_apicode T'.
Proof.
  introv Hsp Hna Hpkna.
  unfold pool_ks_no_int_apicode in *.
  introv Hgt.
  inverts Hsp.
  -
    casetac t0 t Ht Hf.
    +
      subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      specializes Hpkna; eauto.
      specializes Hna; eauto.
      eapply ks_noint_apicode_htstep_preserve; eauto.
    +
      rewrite set_a_get_a' in Hgt; eauto.
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with
      H: context [htistep] |- _ => inverts H
    end.
    casetac t0 t Ht Hf.
    + subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      unfolds.
      split.
      *
        unfolds. introv Heq Hk. simpl in Hk. inverts Hk.
      * 
        specializes Hpkna; eauto.
        simpl.
        unfolds in Hpkna.
        simpljoin.
        split; auto.
        unfold ks_noint_apicode_c in *.
        introv Hnone Hc.
        subst.
        specializes H3; auto.
    +
      rewrite set_a_get_a' in Hgt; eauto.
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    casetac t0 t Ht Hf.
    + subst. rewrite set_a_get_a in Hgt. inverts Hgt.
      specializes Hpkna; eauto.
      simpl. simpl in Hpkna.
      simpljoin. split; auto.
      unfolds.
      unfolds in H.
      introv Heq Hnone.
      specializes H; eauto.
      destruct H as [Hff | [Hff | Hff]]; simpljoin; tryfalse.
      inverts Heq.
      remember (set O curtid (oscurt t')) as O'.
      assert (Hsp: spec_step get_hprio_d (sched asrt;; cd) O' (cd) O' TauAct).
      {
        constructors. instantiate (1:=None). 
        eapply spec_sched_step with (Of:=emp) (O:=O') (t:=t').
        subst.
        rewrite set_a_get_a; auto.
        2: join auto.
        eapply get_hprio_d_preserve with (O:=O); eauto.
        subst.
        rewsimp. auto.
        subst.
        rewsimp. auto.
      }
      
      lets H__: api_spec_step_succs_preserve Hsp; eauto.
      destruct H__ as [Ha | [Habt | Hend]].
      * left. do 4 eexists. split; eauto.
      * right; left; auto.
      * right; right; auto.
    +
      rewrite set_a_get_a' in Hgt; eauto.
Qed.

Lemma pool_ks_noint_apicode_hpstepokstar_preserve: 
  forall pu ispc T cst O T' cst' O',    
    pu_noabs pu -> 
    hpstepokstar (pu, (api_spec, ispc, get_hprio_d)) T cst O T' cst' O' ->
    task_pool_no_sub_abs T -> 
    pool_ks_no_int_apicode T ->
    pool_ks_no_int_apicode T'.
Proof. 
  introv Hpn Hstepstar.
  remember (pu, (api_spec, ispc, get_hprio_d)) as hp0.
  induction Hstepstar.
  intros; auto.
  introv Hpna Hni.
  subst. 
  inverts H. 
  lets H_: pool_ks_noint_apicode_hpstep_preserve H0; eauto.
  eapply IHHstepstar; eauto.
  eapply noabs_preserve_hpstep; eauto.  
Qed.

Lemma reachable_ks_noint_apicode: 
  forall pu ispc T cst O, 
    pu_noabs pu -> 
    reachable (pu, (api_spec, ispc, get_hprio_d)) T cst O -> 
    pool_ks_no_int_apicode T.
Proof.
  introv Hn Hrc.
  assert (Hr := Hrc).
  inverts Hrc.
  simpljoin.
  eapply pool_ks_noint_apicode_hpstepokstar_preserve; eauto.
  { (* task_pool_no_sub_abs *)
    unfold init in *.
    simpljoin.
    unfolds.
    introv HC.
    unfold init_tsk in *.
    simpljoin.
    eapply H2 in HC; eauto.
    simpljoin.
    unfolds in Hn.
    specializes Hn; eauto.
    unfold nilcont. 
    unfolds.
    split; simpl; auto.
  }
  { (* pool_ks_no_int_apicode *)
    unfold init in *.
    simpljoin.
    unfolds.
    introv HC.
    unfold init_tsk in *.
    simpljoin.
    eapply H2 in HC; eauto.
    simpljoin.
    unfolds in Hn.
    specializes Hn; eauto.
    unfold nilcont.
    unfolds.
    split; simpl; auto.
    unfolds.
    introv Hs Hk.
    inverts Hs.
    simpl in Hn. false.
  }
Qed.  
