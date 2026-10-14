
Require Import memory. 
Require Import sem_language.
Require Import sem_opsem. 
Require Import asrt_sat_apis.

Require Import rc_no_subabs.
Require Import rc_kevt_nonest.
Require Import rc_nknl_nkevt.
Require Import rc_int_code. 

Require Import sem_sys.

Require Import join_lib. 

Fixpoint hasrt_sat_cont (ks: stmtcont) lau :=
  match ks with
    kstop => True
  | kseq _ ks 
  | kint _ _ _ ks
  | kassignr _ _ ks
  | kassignl _ _ ks 
  | kfuneval _ _ _ _ ks
  | kif _ _ ks 
  | kwhile _ _ ks 
  | kret ks => hasrt_sat_cont ks lau
  | kcall f s E ks => (* no abs stmt in s *) 
      hasrt_sat_cont ks lau 
  | kevent c ke ks =>
      hasrt_sat_cont ks lau
      /\
        (absintcont ks = None ->
         ((forall cd, c = curs (hapi_code cd) -> head_asrt_sat cd lau)
          /\ 
            (((exists vo, c = curs (hapi_code (spec_done vo))) \/ ~(exists cd, c = curs (hapi_code cd))) ->
             tskpt lau = PtNormal)))
  end.    

Definition hasrt_sat (C: code) lau :=
  exists c ke ks,
    C = (c, (ke, ks))
    /\ (
        absintcont ks = None -> 
        ((forall cd, c = curs (hapi_code cd) -> head_asrt_sat cd lau)
         /\
           (((exists vo, c = curs (hapi_code (spec_done vo))) \/ ~(exists cd, c = curs (hapi_code cd))) ->
            tskpt lau = PtNormal)
        ) 
      )
    /\ hasrt_sat_cont ks lau.

Definition pool_hasrt_sat (T: tasks) laump :=
  forall t C lau, get T t = Some C -> get laump t = Some lau -> hasrt_sat C lau.

Lemma expr_not_absstmt:
  forall e, 
    ~(exists cd, cure e = curs (hapi_code cd)).
Proof.
  introv Hf.
  simpljoin.
  inverts H.
Qed.

Local Hint Resolve expr_not_absstmt: not_absstmt_lemmas. 

Lemma sskip_not_absstmt:
  forall vo, 
    ~ (exists cd, [vo] = curs (hapi_code cd)). 
Proof.
  introv Hf.
  simpljoin.
  inverts H.
Qed.   

Local Hint Resolve sskip_not_absstmt: not_absstmt_lemmas. 

Lemma hsat_preserve_estep:
  forall c ke m c' ke' m' lau ks, 
    estep c ke m c' ke' m' ->
    hasrt_sat (c, (ke, ks)) lau ->
    hasrt_sat (c', (ke', ks)) lau. 
Proof.
  introv Hes Hhs.
  inverts Hes; 
    try (
        unfolds; unfolds in Hhs;
        destruct Hhs as (c_ & ke_ & ks_ & Heq & Himpl & Hcont);
        inverts Heq; 
        do 3 eexists; 
        splits; eauto;
        introv Hnone; 
        specializes Himpl; eauto; 
        destruct Himpl as (Hsat & Hnml); 
        split; 
        [introv Hf; inverts Hf |
          introv Hor; eapply Hnml; eauto; 
          right; eauto with not_absstmt_lemmas]).
Qed.

Lemma nknl_nkevt_free_ks: 
  forall v ke ks, 
    nknl_nkevt (curs (sfree nil v), (ke, ks)) -> absintcont ks = None.
Proof.
  introv Hnn.
  unfolds in Hnn.
  eapply Hnn; eauto.
  unfolds.
  right.
  eexists; split; eauto.
  introv Hf.
  simpljoin.
  inverts H.
Qed. 

Lemma hsat_callcont_preserve:
  forall ks ks' f s le' lau, 
    hasrt_sat_cont ks lau -> 
    callcont ks = Some (kcall f s le' ks') ->
    hasrt_sat_cont ks' lau.
Proof.
  inductions ks;
    try (introv Hsat Hcc; simpl in Hsat, Hcc; tryfalse; inverts Hcc; auto); 
    try (simpl in Hsat; eapply IHks; eauto).
  -
    simpljoin; auto. 
Qed.

Lemma stmt_noabs_false: 
  forall cd, stmt_noabs (hapi_code cd) -> False. 
Proof.
  introv Hf.
  unfolds in Hf.
  auto.
Qed. 

Lemma hsat_preserve_sstep:
  forall pu c ks m c' ks' m' lau ke, 
    tskcode_no_sub_abs (c, (ke, ks)) -> 
    nknl_nkevt (c, (ke, ks)) -> 
    sstep pu c ks m c' ks' m' ->
    hasrt_sat (c, (ke, ks)) lau ->
    hasrt_sat (c', (ke, ks')) lau. 
Proof.
  introv Hns Hnk Hss Hhs.
  remember (c, (ke, ks)) as C. 
  inverts Hss; subst C; 
    try (
        unfolds in Hhs; unfolds; 
        destruct Hhs as (c_ & ke_ & ks_ & Heq & Himpl & Hcont); 
        inverts Heq; 
        do 3 eexists; 
        splits; eauto; 
        introv Hnone; 
        specializes Himpl; eauto; 
        destruct Himpl as (Hsat & Hnml)); 
    try (
        split; 
        [introv Hf; inverts Hf; simpl in Hns; simpljoin; tryfalse |
          introv Hor; eapply Hnml; eauto; 
          right;
          introv Hf; simpljoin;
          match goal with H: curs _ = curs _ |- _ => inverts H end]; fail).

  -
    unfolds.
    unfolds in Hhs.
    destruct Hhs as (c_ & ke_ & ks_ & Heq & Himpl & Hcont).
    inverts Heq.
    do 3 eexists.
    splits; eauto.
    introv Hnone.
    lets H__: nknl_nkevt_free_ks Hnk; eauto.
    specializes Himpl; eauto.
    destruct Himpl as (Hsat & Hnml). 
    split.
    + 
      introv Hf; inverts Hf.
    +
      introv Hor.
      eapply Hnml; eauto.
      right.
      introv Hf; simpljoin;
        match goal with H: curs _ = curs _ |- _ => inverts H end. 
    +
      eapply hsat_callcont_preserve; eauto.
  -
    simpl in Hns.
    destruct Hns as (Hnss & Hnsk).
    destruct Hnss as [(Hns1 & Hns2) | Hf].
    + split.
      *
        introv Hf.
        inverts Hf. 
        apply stmt_noabs_false in Hns1; false.
      *
        introv Hor.
        eapply Hnml; eauto. 
        right. 
        introv Hf; simpljoin;
          match goal with H: curs _ = curs _ |- _ => inverts H end.
    +
      destruct Hf as (cd & Hf).
      inverts Hf. 
Qed.

Lemma hsat_preserve_cstep:
  forall pu c ke ks m c' ke' ks' m' lau, 
    tskcode_no_sub_abs (c, (ke, ks)) -> 
    nknl_nkevt (c, (ke, ks)) -> 
    cstep pu (c, (ke, ks)) m (c', (ke', ks')) m' ->
    hasrt_sat (c, (ke, ks)) lau ->
    hasrt_sat (c', (ke', ks')) lau. 
Proof.
  introv Htn Hnn Hcs Hhs.
  inverts Hcs; 
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
  - 
    eapply hsat_preserve_estep; eauto. 
  -  
    eapply hsat_preserve_sstep; eauto. 
Qed.


Lemma pt_nml_asrt:
  forall lau, 
    tskpt lau = PtNormal ->
    nml_asrt lau. 
Proof.
  introv Hpt.
  unfold nml_asrt. 
  destruct lau. simpl in Hpt. subst.
  auto.
Qed. 

Ltac simp_solve := 
  solve [simpl; auto | simpl; splits; eapply pt_nml_asrt; eauto]. 

Ltac des_arg :=
  match goal with
  | vl: list val, vl': list val, H: _ |- _ =>
      first [ simp_solve | destruct vl; destruct vl' ]
  | vl': list val, H: _ |- _ =>
      first [ simp_solve | destruct vl' ]
  | H: _ |- _ => simp_solve
  end.

Lemma semtrywait_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (semtrywait (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed.

Local Hint Resolve semtrywait_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma semwait_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (semwait (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve semwait_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma semtimedwait_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (semtimedwait (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve semtimedwait_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma semsignal_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (semsignal (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve semsignal_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma seminit_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (seminit (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve seminit_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma seminitbin_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (seminitbin (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve seminitbin_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Lemma semdestroy_body_nml_asrt_sat:      
  forall lau vl vl', 
    tskpt lau = PtNormal ->
    head_asrt_sat (semdestroy (vl ++ vl')) lau. 
Proof.
  introv Htl.
  repeat des_arg.
Qed. 

Local Hint Resolve semdestroy_body_nml_asrt_sat : hasrt_sat_body_lemmas.

Require Import good_code.
Require Import sem_lemmas. 
Require Import sem_tacs.
Require Import succ_gen.

Lemma absintcont_none_hasrt_sat:
  forall ks lau, 
    absintcont ks = None -> 
    hasrt_sat_cont ks lau. 
Proof.
  inductions ks; 
    introv Hn; try (simpl; auto).
  simpl in Hn.
  tryfalse. 
Qed. 

Lemma hasrt_sat_spec_step_preserve: 
  forall sc (r: vallist -> spec_code) cd cd' ke ks vl n lau lau' O O', 
    (
      forall sc n vl cd O cd' O' lau lau',
        r vl <> ABORT -> 
        nth_error (get_all_succs (r vl)) n = Some cd -> 
        head_asrt_sat cd lau -> 
        spec_step sc cd O lau cd' O' lau' ->
        head_asrt_sat cd' lau'
    ) ->
    (
      forall sc n vl cd O vo O' lau lau',
        r vl <> ABORT -> 
        nth_error (get_all_succs (r vl)) n = Some cd ->
        head_asrt_sat cd lau -> 
        spec_step sc cd O lau (END vo) O' lau' ->
        tskpt lau' = PtNormal
    ) -> 
    rc_int_code.int_code (curs (hapi_code cd), (ke, ks)) ->
    nth_error (get_all_succs (r vl)) n = Some cd -> 
    hasrt_sat (curs (hapi_code cd), (ke, ks)) lau ->
    spec_step sc cd O lau cd' O' lau' ->
    hasrt_sat (curs (hapi_code cd'), (ke, ks)) lau'.
Proof.
  introv Hsatpv Hsatend Hatc Hnth Hhs Hsp.
  unfold hasrt_sat in *.
  destruct Hhs as (c & ke0 & ks0 & Heq & Himpl & Hcont).
  inverts Heq.
  do 3 eexists.
  splits; eauto.
  *
    introv Hnone.
    specializes Himpl; eauto.
    destruct Himpl as (Hhsat & Hnml).
    casetac (r vl) spec_abort Ht Hf.
    **
      rewrite Ht in Hnth.
      assert (cd = spec_abort) by (eapply abt_succs_contra; eauto).
      subst cd.
      match goal with H: context [spec_step] |- _ => inverts H end.
    ** (* r vl <> ABORT *)
      split.
      ***
        introv Haceq; inverts Haceq.
        specializes Hhsat; eauto.
      ***
        introv Hor.
        destruct Hor as [Hend | Hnend].
        ****
          destruct Hend as (vo & Heqend).
          inverts Heqend.
          eapply Hsatend; eauto. 
        ****
          false. apply Hnend. eexists; eauto.
  *
    simpl in Hatc.
    casetac (absintcont ks0) (None : option stmtcont) Ht Hf.
    **
      eapply absintcont_none_hasrt_sat; eauto.
    **
      destruct Hatc as (Hatc & H__). 
      specializes Hatc; eauto.  
      destruct Hatc as (iid & ti & Hf' & _).
      unfolds in Hf'.
      unfold int_spec_list in Hf'.
      simpl in Hf'.
      tryfalse.
Qed.
      
Lemma hsat_preserve_spec_step:
  forall sc cd ke ks O lau cd' O' lau'
         (Hhs : hasrt_sat (curs (hapi_code cd), (ke, ks)) lau)
         (Hatc : rc_int_code.int_code (curs (hapi_code cd), (ke, ks)))
         (Hgc : goodcode_h (curs (hapi_code cd), (ke, ks)))
         (H : spec_step sc cd O lau cd' O' lau'),     
    hasrt_sat (curs (hapi_code cd'), (ke, ks)) lau'. 
Proof.
  intros. 
  simpl in Hgc.
  destruct Hgc as (Hgs & Hgk).
  unfolds in Hgs.    
  destruct Hgs as [Hapi | [Hend | Habt]].
  + destruct Hapi as (fid & ac & ft & vl & Hapi & Hin).
    unfold api_spec' in Hapi.
    unfold api_spec_list' in Hapi.
    simpl in Hapi.
    eapply In_nth_error in Hin; eauto. 
    destruct (Zeq_bool sem_trywait fid) eqn : Etw.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply semtrywait_nabt_spec_step_sat_preserve; eauto. 
      eapply semtrywait_nabt_spec_step_sat_end; eauto.
    }
    destruct (Zeq_bool sem_wait fid) eqn : Ew.      
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply semwait_nabt_spec_step_sat_preserve; eauto. 
      eapply semwait_nabt_spec_step_sat_end; eauto.
    }
    destruct (Zeq_bool sem_timedwait fid) eqn: Etmw.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply semtimedwait_nabt_spec_step_sat_preserve; eauto. 
      eapply semtimedwait_nabt_spec_step_sat_end; eauto.        
    }
    destruct (Zeq_bool sem_signal fid) eqn: Esg.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply semsignal_nabt_spec_step_sat_preserve; eauto. 
      eapply semsignal_nabt_spec_step_sat_end; eauto.                
    }
    destruct (Zeq_bool sem_init fid) eqn: Esi.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply seminit_nabt_spec_step_sat_preserve; eauto. 
      eapply seminit_nabt_spec_step_sat_end; eauto.                        
    }
    destruct (Zeq_bool sem_init_bin fid) eqn: Esib.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply seminitbin_nabt_spec_step_sat_preserve; eauto. 
      eapply seminitbin_nabt_spec_step_sat_end; eauto.                        
    }
    destruct (Zeq_bool sem_destroy fid) eqn: Ed.
    {
      inverts Hapi.
      simpljoin.
      eapply hasrt_sat_spec_step_preserve; eauto.
      eapply semdestroy_nabt_spec_step_sat_preserve; eauto. 
      eapply semdestroy_nabt_spec_step_sat_end; eauto.                        
    }
    tryfalse.
  +
    destruct Hend as (vo & Hend).
    subst cd.
    match goal with H: context [spec_step] |- _ => inverts H end.
  +
    subst cd.
    match goal with H: context [spec_step] |- _ => inverts H end.    
Qed.   
  
Lemma hsat_preserve_apistep:
  forall sc C O lau C' O' lau',    
    goodcode_h C -> 
    rc_int_code.int_code C -> 
    hapistep (api_spec', int_spec, sc) C O lau C' O' lau' ->
    hasrt_sat C lau ->
    hasrt_sat C' lau'. 
Proof.
  introv Hgc Hatc Has Hhs.
  inverts Has; try match goal with H: (_, _) = (_, _) |- _ => inverts H end.

  - (* api enter *)    
    match goal with H: api_spec' _ = _ |- _ => rename H into Haspc end.
    unfold api_spec' in Haspc.
    unfold api_spec_list' in Haspc.
    simpl in Haspc.
    unfolds in Hhs.
    destruct Hhs as (c & ke & ks0 & Heq & Himpl & Hcont).
    inverts Heq.
    unfolds.
    do 3 eexists.
    splits; eauto.
    introv Hnone.
    specializes Himpl; eauto.
    destruct Himpl as (_ & Hnml).
    specializes Hnml; eauto.
    right. introv Hf. simpljoin. 
    match goal with H: curs _ = curs _ |- _ => inverts H end.
    split.
    2: { introv Hor; auto. }
    introv Hcdeq.
    inverts Hcdeq. 
    repeat 
      match type of Haspc with
        (if ?t then _ else _) = _ =>
          let en := fresh "E" in 
          destruct t eqn: en; [ inverts Haspc; eauto with hasrt_sat_body_lemmas | idtac ]
      end. 
    tryfalse.

  - (* idapi *)
    match goal with H: context[spec_step] |- _ => simpl in H end.
    eapply hsat_preserve_spec_step; eauto. 
      
  - (* api exit *)
    unfold hasrt_sat in *.
    destruct Hhs as (c & ke0 & ks0 & Heq & Himpl & Hcont).
    inverts Heq.
    do 3 eexists.
    splits; eauto.
    introv Hnone.
    specializes Himpl; eauto.
    destruct Himpl as (Hsat & Hnml).
    split.
    +
      introv Hf.
      inverts Hf.
    +
      introv Hor.
      eapply Hnml; eauto.

  - (* int exit *)
    unfold hasrt_sat in *.
    destruct Hhs as (c0 & ke0 & ks0 & Heq & Himpl & Hcont).
    inverts Heq.
    do 3 eexists.
    splits; eauto.
    introv Hnone.
    simpl in Hcont. 
    split.
    + introv Hc.
      subst c.
      simpljoin.
      specializes H0; eauto.
      simpljoin; auto.
    + 
      destruct Hcont as (Hhc & Himpl_).
      introv Hor.
      specializes Himpl_; eauto.
      destruct Himpl_ as (Hsat & Himpl_).
      eapply Himpl_; eauto. 
    +
      simpl in Hcont.
      simpljoin; auto.
Qed.

Lemma hsat_preserve_htistep:  
  forall ispc c ke ks O l lau, 
    htistep ispc (c, (ke, ks)) O (curs (hapi_code l), (kenil, kevent c ke ks)) O ->
    hasrt_sat (c, (ke, ks)) lau ->
    hasrt_sat (curs (hapi_code l), (kenil, kevent c ke ks)) lau. 
Proof.
  introv Hsp Hhs.
  unfolds.
  do 3 eexists.
  splits; eauto.
  - 
    introv Hf.
    simpl in Hf.
    tryfalse.
  -
    simpl.
    unfolds in Hhs.
    destruct Hhs as (c0 & ke0 & ks0 & Heq & Hn & Hhs).
    inverts Heq.
    splits; eauto.
Qed. 

Lemma hsat_preserve_htstep:
  forall pu sc t c ke ks cst O lau c' ke' ks' cst' O' lau', 
    tskcode_no_sub_abs (c, (ke, ks)) -> 
    nknl_nkevt (c, (ke, ks)) -> 
    goodcode_h (c, (ke, ks)) -> 
    rc_int_code.int_code (c, (ke, ks)) -> 
    htstep (pu, (api_spec', int_spec, sc)) t (c, (ke, ks)) cst O lau (c', (ke', ks')) cst' O' lau' ->
    hasrt_sat (c, (ke, ks)) lau ->
    hasrt_sat (c', (ke', ks')) lau'.
Proof.
  introv Hnsub Hnn Hgc Hatc Hsp Hsat.
  inverts Hsp.
  - (* cstep *) 
    match goal with H: (_, _) = _ |- _ => inverts H end.
    eapply hsat_preserve_cstep; eauto.
  - (* api step *)
    match goal with H: (_, _) = _ |- _ => inverts H end.
    eapply hsat_preserve_apistep; eauto.
Qed.     
  
Lemma hsat_preserve_hpstep:
  forall pu sc T cst O lau T' cst' O' lau',
    good_task_code T -> 
    pool_int_code T ->
    task_pool_no_sub_abs T -> 
    pool_nknl_nkevt T -> 
    hpstep (pu, (api_spec', int_spec, sc)) T cst O lau T' cst' O' lau' ->
    pool_hasrt_sat T lau ->
    pool_hasrt_sat T' lau'. 
Proof.
  introv Hgtc Hatc Hnos Hnn Hsp Hsat.
  unfold pool_hasrt_sat in *.
  inverts Hsp; try match goal with H: (_, _) = _ |- _ => inverts H end.
  - 
    introv Hget Hgetl.
    casetac t t0 Ht Hf.
    + subst.
      rewrite set_a_get_a in Hget.
      rewrite set_a_get_a in Hgetl.
      inverts Hget.
      inverts Hgetl.
      destruct C as (c & ke & ks).
      destruct C0 as (c0 & ke0 & ks0).
      lets Hgtc_: Hgtc t0. specializes Hgtc_; eauto.
      lets Hatc_: Hatc t0. specializes Hatc_; eauto.
      lets Hnos_: Hnos t0. specializes Hnos_; eauto.
      lets Hnn_: Hnn t0. specializes Hnn_; eauto.
      eapply hsat_preserve_htstep; eauto. 
    + rewrite set_a_get_a' in Hget; eauto.
      rewrite set_a_get_a' in Hgetl; eauto.
  -
    introv Hget Hgetl.     
    casetac t t0 Ht Hf.
    + subst.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      specializes Hsat; eauto.
      destruct C as (c & ke & ks).
      match goal with H: context [htistep] |- _ => inverts H end.
      eapply hsat_preserve_htistep; eauto. 
      constructors.
      eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  -
    introv Hget Hgetl.
    casetac t t0 Ht Hf.
    +
      subst.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      specializes Hsat; eauto.

      Definition sc0 (O: osabst) (t: tid) : Prop := (get O curtid = Some (oscurt t)).
      assert (spec_step sc0 (sched asrt;; s) O lau s O lau).
      {
        constructors; eauto. 
        constructors; eauto.  
        instantiate (1:=emp).
        eapply map_join_emp; eauto. 
      }
      eapply hsat_preserve_spec_step; eauto.
    +
      rewrite set_a_get_a' in Hget; eauto. 

      Unshelve.
      trivial.
Qed.

Lemma GoodStmt_noabs: 
  forall s, GoodStmt_h s -> stmt_noabs s.
Proof.
  inductions s; 
    introv HGS;
    try (simpl; auto).
  - 
    simpl in HGS.
    simpljoin.
    split; eauto.
  -
    simpl in HGS.
    simpljoin.
    split; eauto.
Qed. 

Lemma good_client_code_impl_noabs:
  forall cliprogs, 
    good_client_code cliprogs ->
    pu_noabs cliprogs.
Proof.
  introv Hgcc.
  unfolds in Hgcc.
  unfolds.
  introv Hcf.
  lets H__: Hgcc Hcf.
  apply GoodStmt_noabs; auto. 
Qed. 

Lemma hsat_preserve_hpstepokstar:
  forall pu T cst O lau T' cst' O' lau',
    good_client_code pu -> 
    good_task_code T -> 
    pool_int_code T ->
    task_pool_no_sub_abs T -> 
    (* pool_kevt_no_nest T ->  *)
    pool_nknl_nkevt T -> 
    hpstepokstar (pu, os_spec') T cst O lau T' cst' O' lau' ->
    pool_hasrt_sat T lau ->
    pool_hasrt_sat T' lau'. 
Proof.
  introv Hgcli Hgtc Hatc Hnsub (* Hnst *) Hnn Hsp.
  remember (pu, os_spec') as hp.
  induction Hsp.
  -
    introv Hps. auto.
  -
    introv Hhs.
    assert (Hspok := H).
    match goal with H: context [hpstep_ok] |- _ => inverts H end. 
    subst p.
    eapply IHHsp; eauto.    
    eapply hpstep_goodcode_h; eauto.     
    eapply pool_int_code_hpstep_preserve; eauto.      
    {
      eapply noabs_preserve_hpstep; eauto.
      eapply good_client_code_impl_noabs; eauto.
    }
    eapply nknl_nkevt_hpstep_preserve; eauto. 
    eapply hsat_preserve_hpstep; eauto.
Qed.

Require Import sem_init.

Lemma init_hasrt_sat:
  forall pu T cst O lau, 
    good_client_code pu -> 
    init pu T cst O lau ->
    pool_hasrt_sat T lau. 
Proof.
  introv Hgcc Hini.
  unfolds in Hini.
  destruct Hini as (Hit & His).
  unfolds in Hit.
  destruct Hit as (Heqd & Hs).
  unfolds in His.
  destruct His as (_ & _ & _ & _ & Hlau).
  unfolds in Hlau.
  unfolds.
  introv HgC Hgl.
  unfolds.
  specializes Hs; eauto.
  destruct Hs as (s & f & d1 & d2 & t_ & Hnc & Hpu).
  destruct C as (c & ke & ks). 
  do 3 eexists.
  splits; eauto.
  -
    introv Hnone.
    unfolds in Hnc.
    inverts Hnc.
    split.
    + introv Hse.
      inverts Hse.
      unfolds in Hgcc.
      specializes Hgcc; eauto.
      unfolds in Hgcc.
      false.
    + introv Hor.
      assert (get T t <> None).
      {
        rewrite HgC. introv Hf; inverts Hf.
      }
      specializes Hlau; eauto.
      rewrite Hgl in Hlau.
      inverts Hlau.
      simpl. auto. 
  -
    unfolds in Hnc.
    inverts Hnc.
    simpl. auto. 
Qed.

Lemma reachable_hasrt_sat:
  forall pu T cst O aust, 
    good_client_code pu -> 
    reachable (pu, os_spec') T cst O aust ->
    pool_hasrt_sat T aust.
Proof.
  introv Hgcc Hrc.
  assert (Hrc_ := Hrc).
  unfolds in Hrc.
  destruct Hrc as (pu_ & spc & Heq & Hex). 
  inverts Heq.
  destruct Hex as (T0 & cst0 & O0 & aust0 & Hini & Hsp).
  lets Hsat0: init_hasrt_sat Hini; eauto.
  assert (Hrc: reachable (pu_, os_spec') T0 cst0 O0 aust0).
  {
    unfolds.
    do 2 eexists.
    splits; eauto.
    do 4 eexists.
    split; eauto.
    constructors.
  }
  eapply hsat_preserve_hpstepokstar; eauto.
  {
    destruct Hini.
    eapply init_good_tasks; eauto.
  }
  {
    eapply reachable_apicode_type_c; eauto.
    eapply good_client_code_impl_noabs; eauto.
  }
  {
    eapply reachable_no_sub_abs; eauto.
    eapply good_client_code_impl_noabs; eauto.
  }
  eapply reachable_nknl_nkevt; eauto. 
Qed.

 
