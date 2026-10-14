Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs. 
Require Import osspecs. 

Require Export properties.

Set Keyed Unification.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Lemma nknl_expr: forall e, not_knl_stmt (cure e).
Proof.
  intros.
  unfolds.
  left.
  eexists; eauto.
Qed.   

Lemma nknl_cstmt:
  forall s, (~(exists cd, s = hapi_code cd)) -> not_knl_stmt (curs s).  
Proof.
  intros.
  unfolds.
  right.
  eexists.
  splits; eauto.
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

Lemma cstep_not_knl_eval:
  forall pc c ke ks c' ke' ks' d ge le M ge' le' M', 
    cstep pc d (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') -> 
    not_knl_stmt c. 
Proof.
  introv Hcstep.
  inverts Hcstep.
  - (* estep *) 
    inverts H7.
    inverts H8; 
      try (unfolds; left; eexists; eauto; fail);
      try (unfolds; right; eexists; splits; eauto; introv Hex; simpljoin; tryfalse).
  - (* sstep *)
    inverts H7.
    inverts H8; 
      try (unfolds; right; eexists; splits; eauto; introv Hex; simpljoin; tryfalse). 
Qed.

Definition ceval_ke_cond (c: cureval) (ke: exprcont) : Prop := 
  (not_knl_stmt c -> 
   (exists s, c = curs s /\ ke = kenil) \/
     (exists e, c = cure e) \/
     (exists vo, c = curs (sskip vo) /\ ke <> kenil)). 

Fixpoint ks_cond (ks: stmtcont) : Prop :=
  match ks with
    kstop => True
  | kseq _ ks 
  | kcall _ _ _ ks
  | kint _ _ _ ks
  | kassignr _ _ ks
  | kassignl _ _ ks 
  | kfuneval _ _ _ _ ks
  | kif _ _ ks 
  | kwhile _ _ ks 
  | kret ks => ks_cond ks 
  | kevent c ke ks => ceval_ke_cond c ke /\ ks_cond ks 
  end.
    
Definition ctrl_state_cond (C: code) : Prop :=
  match C with
    (c, (ke, ks)) => ceval_ke_cond c ke /\ ks_cond ks
  end.

Lemma cs_preserve_estep:
  forall c c' ke ke' ks td m m', 
    estep td c ke m c' ke' m' ->
    ctrl_state_cond (c, (ke, ks)) ->
    ctrl_state_cond (c', (ke', ks)). 
Proof.
  introv Hestep Hc.
  inverts Hestep; 
    try (
        (unfolds; unfolds in Hc; 
         destruct Hc; splits; eauto; 
         unfolds; 
         introv Hnknl; 
         casetac ke' kenil Ht Hf; 
         [ left; eexists; splits; eauto | 
           right; right; eexists; splits; eauto]; fail)); 
    try ( 
        unfolds; unfolds in Hc; 
        destruct Hc; 
        splits; eauto; 
        unfolds; 
        introv Hnknl; 
        right; left; eexists; eauto; fail).
Qed.  

Lemma callcont_ks_cond: 
  forall ks ks' f s le, 
    callcont ks = Some (kcall f s le ks') ->
    ks_cond ks ->
    ks_cond ks'. 
Proof.
  induction ks; introv Heq Hkc; 
    try (inverts Heq; fail); 
    try (simpl in Heq;  simpl in Hkc; eapply IHks; eauto; fail).
  - simpl in Heq. inverts Heq.  simpl in Hkc. auto. 
  - simpl in Heq. simpl in Hkc. destruct Hkc. eapply IHks; eauto.
Qed.   

Lemma cs_preserve_sstep:
  forall pu td c c' ks ks' m m', 
    sstep pu td c ks m c' ks' m' ->
    ctrl_state_cond (c, (kenil, ks)) ->
    ctrl_state_cond (c', (kenil, ks')).  
Proof.
  introv Hsstep Hc.
  inverts Hsstep; 
    try (
        unfolds; 
        unfolds in Hc; 
        simpl ks_cond; 
        destruct Hc; 
        splits; eauto;
        unfolds; introv Hnknl; right; left; eexists; eauto; fail); 
    try (
        unfolds; unfolds in Hc;
        simpl ks_cond in Hc;
        destruct Hc;
        splits; eauto;
        unfolds; introv Hnkl; 
        casetac ke kenil Ht Hf; 
        [ left; eexists; splits; eauto | 
          right; right; eexists; splits; eauto]; fail); 
    try (
        unfolds; unfolds in Hc; 
        simpl ks_cond; simpl ks_cond in Hc; 
        destruct Hc; splits; eauto; 
        unfold ceval_ke_cond in *; 
        match goal with
          H: ?P -> ?Q |- _ =>
            cut P; [idtac | eapply nknl_cstmt; eauto; introv Hf; destruct Hf; tryfalse]
        end; 
        introv Hnknl; 
        match goal with H: _ -> _ |- _ => specialize (H Hnknl) end; intro; 
        match goal with
          H: _ \/ _ |- _ => 
            inversion H;
            [simpljoin; left; eexists; eauto |
              clear H;
              match goal with H1: _ \/ _ |- _ => inversion H1; simpljoin; tryfalse end] 
        end; fail).
  -
    unfolds; unfolds in Hc.
    destruct Hc.
    split.    
    2: { simpl in H0. eapply callcont_ks_cond; eauto. }
    unfold ceval_ke_cond in *.
    introv Hnknl.
    left. eexists; eauto.
Qed. 

Lemma cs_preserve_cstep:
  forall pu td C m C' m', 
    cstep pu td C m C' m' -> 
    ctrl_state_cond C ->
    ctrl_state_cond C'.
Proof.
  introv Hcstep Hcs.
  inverts Hcstep.
  eapply cs_preserve_estep; eauto.
  eapply cs_preserve_sstep; eauto. 
Qed.

Lemma cs_preserve_hapistep:
  forall osspc cd O cd' O' act,
    hapistep osspc cd O cd' O' act ->
    ctrl_state_cond cd ->
    ctrl_state_cond cd'. 
Proof.
  introv Hastep Hcs.
  inverts Hastep.
  -
    unfold ctrl_state_cond in *.
    destruct Hcs. splits; eauto.
    unfolds.
    introv Hnknl.
    unfolds in Hnknl.
    inverts Hnknl.
    inverts H2; tryfalse.
    simpljoin.
    inverts H2. 
    false. apply H4. eexists. eauto. 
  -
    unfold ctrl_state_cond in *.
    destruct Hcs. splits; auto.
    unfolds.
    introv Hnknl.
    unfolds in Hnknl.
    inverts Hnknl.
    inverts H2; tryfalse.
    simpljoin.
    inverts H2. 
    false. apply H3. eexists. eauto. 
  -
    unfold ctrl_state_cond in *.
    destruct Hcs. splits; eauto.
    unfolds.
    introv Hnknl.
    casetac ke kenil Ht Hf; 
      [ left; eexists; splits; eauto | 
        right; right; eexists; splits; eauto]. 
  -
    unfold ctrl_state_cond in *.
    destruct Hcs.
    simpl in H0.
    auto.
Qed. 
    
Lemma cs_preserve_htstep: 
  forall hp t td C cst O C' cst' O' act, 
    htstep hp t td C cst O C' cst' O' act ->
    ctrl_state_cond C ->
    ctrl_state_cond C'. 
Proof.
  introv Hstep Hcs.
  inverts Hstep.
  eapply cs_preserve_cstep; eauto.
  eapply cs_preserve_hapistep; eauto. 
Qed.

(* Lemma cs_preserve_cstepstar: *)
(*   forall pc d C ge le M C' ge' le' M',  *)
(*     cstepstar pc d C (ge, le, M) C' (ge', le', M') -> *)
(*     ctrl_state_cond C -> *)
(*     ctrl_state_cond C'. *)
(* Proof. *)
(*   introv Hstepstar. *)
(*   inductions Hstepstar. *)
(*   - intros; auto. *)
(*   - destruct m'. destruct p0.  *)
(*     specialize (IHHstepstar e e0 m ge' le' M'). *)
(*     intros. *)
(*     eapply IHHstepstar; eauto. *)
(*     clear IHHstepstar. *)
(*     eapply cs_preserve_cstep; eauto. *)
(* Qed.      *)

Definition task_pool_ctrl_cond (T: tasks) :=
  forall t C, get T t = Some C -> ctrl_state_cond C. 

Lemma cs_preserve_hpstep:
  forall hp T cst O T' cst' O' act,
    hpstep hp T cst O T' cst' O' act ->
    task_pool_ctrl_cond T ->
    task_pool_ctrl_cond T'. 
Proof.
  introv Hstep Hcs.
  inverts Hstep.
  -
    unfold task_pool_ctrl_cond in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      eapply cs_preserve_htstep; eauto.
    * rewrite set_a_get_a' in Hget; eauto.
  -
    unfold task_pool_ctrl_cond in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget. inverts Hget.
      match goal with H: htistep _ _ _ _ _ |- _ => inverts H end.
      unfolds. simpl.
      lets Hcs_: Hcs H1.
      unfolds in Hcs_.
      destruct Hcs_. splits; eauto.
      unfolds.
      introv Hf. apply knl_api in Hf. tryfalse.
    * rewrite set_a_get_a' in Hget; eauto.
  -
    unfold task_pool_ctrl_cond in *.
    introv Hget.
    casetac t t0 Ht Hf.
    * subst. rewrite set_a_get_a in Hget.
      inverts Hget.
      unfolds.
      lets Hcs_: Hcs H2. unfolds in Hcs_.
      destruct Hcs_. splits; eauto.
      unfolds. introv Hf. apply knl_api in Hf. tryfalse.
    * rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma cs_preserve_hpstepokstar:
  forall hp T cst O T' cst' O', 
    hpstepokstar hp T cst O T' cst' O' ->
    task_pool_ctrl_cond T ->
    task_pool_ctrl_cond T'.
Proof.
  introv Hstepstar.
  induction Hstepstar.
  intros; auto.
  introv Htcs.
  inverts H.
  eapply cs_preserve_hpstep in H0; eauto.
Qed.

Lemma reachable_ctrl_state_cond:
  forall hp T cst O, 
    reachable hp T cst O ->
    task_pool_ctrl_cond T.
Proof.
  introv Hrc.
  inverts Hrc.
  simpljoin.
  eapply cs_preserve_hpstepokstar; eauto.
  unfold init in H0.
  destruct H0.
  unfold init_tsk in H.
  simpljoin.
  unfolds.
  introv Hget.
  lets HC: H2 Hget.
  simpljoin.
  unfolds. unfold nilcont.
  split.
  unfolds. introv Hknl. left. eexists; splits; eauto.
  unfolds. auto.
Qed.   


Fixpoint stmt_noabs (s: stmts) :=
  match s with
    sskip _ | sassign _ _ | sret | srete _ | scall _ _ | scalle _ _ _ | sprint _
  | sfexec _ _ _ | sfree _ _ | salloc _ _ | sprim _ => True 
  | sif e s1 s2 => stmt_noabs s1 /\ stmt_noabs s2
  | sifthen e s => stmt_noabs s 
  | swhile e s => stmt_noabs s
  | sseq s1 s2 => stmt_noabs s1 /\ stmt_noabs s2 
  | hapi_code cd => False
  end.

Definition ceval_noabs (c: cureval) :=
  match c with
    cure e => True 
  | curs s => stmt_noabs s
  end.

Fixpoint ks_noabs (ks: stmtcont) :=
  match ks with 
    kstop => True
  | kseq s ks => stmt_noabs s /\ ks_noabs ks
  | kcall f s E ks => stmt_noabs s /\ ks_noabs ks
  | kint ce ke E ks => ceval_noabs ce /\ ks_noabs ks
  | kassignr e tp ks => ks_noabs ks
  | kassignl v tp ks => ks_noabs ks
  | kfuneval f vl tl el ks => ks_noabs ks 
  | kif s1 s2 ks => stmt_noabs s1 /\ stmt_noabs s2 /\ ks_noabs ks
  | kwhile e s ks => stmt_noabs s /\ ks_noabs ks 
  | kret ks => ks_noabs ks 
  | kevent ce ke ks =>
      (ceval_noabs ce \/ (exists cd, ce = curs (hapi_code cd)))
      /\ ks_noabs ks
  end.

Definition tskcode_no_sub_abs (C: code) :=
  match C with
    (c, (ke, ks)) =>
      (ceval_noabs c \/ (exists cd, c = curs (hapi_code cd)))
        /\ ks_noabs ks
  end.

Lemma noabs_preserve_estep: 
  forall c c' ke ke' ks td m m', 
    estep td c ke m c' ke' m' ->
    tskcode_no_sub_abs (c, (ke, ks)) ->
    tskcode_no_sub_abs (c', (ke', ks)). 
Proof.
  introv Hestep Hnabs.
  inverts Hestep; 
    try (simpl in Hnabs; simpl; simpljoin; split; auto; fail). 
Qed. 

Definition pu_noabs (pu: progunit) :=  
  (forall f t dl1 dl2 s, pu f = Some (t, dl1, dl2, s) -> stmt_noabs s). 

Lemma callcont_noabs:
  forall ks f s E ks', 
    ks_noabs ks ->
    callcont ks = Some (kcall f s E ks') ->
    ks_noabs ks'.
Proof.
  induction ks; introv Hnabs Hcc;
    try (simpl in Hcc; tryfalse; fail); 
    try (simpl in Hcc; simpl in Hnabs; simpljoin; auto;
         eapply IHks; eauto; fail).    
  -
    simpl in Hcc.
    inverts Hcc.
    simpl in Hnabs. simpljoin. auto.
Qed.     
  
Lemma noabs_preserve_sstep:
  forall pu td c c' ks ks' m m',
    pu_noabs pu -> 
    sstep pu td c ks m c' ks' m' ->
    tskcode_no_sub_abs (c, (kenil, ks)) ->
    tskcode_no_sub_abs (c', (kenil, ks')).  
Proof.
  introv Hpu Hsstep Hnabs.
  unfolds in Hpu.
  inverts Hsstep; simpl; simpl in Hnabs; simpljoin; 
    try (split; auto; fail).
  - split; auto. 
    split; auto. eapply Hpu; eauto.
  - split; auto.
    eapply callcont_noabs; eauto.
  - inverts H.
    simpljoin. splits; auto.
    simpljoin. tryfalse.
  - inverts H.
    simpljoin.
    splits; auto.
    simpljoin. tryfalse.
  - splits; auto.
    inverts H.
    auto.
    simpljoin. tryfalse. 
  - splits; auto.
    inverts H.
    auto.
    simpljoin. tryfalse. 
Qed.     

Lemma noabs_preserve_cstep:
  forall pu td C m C' m',
    pu_noabs pu -> 
    cstep pu td C m C' m' -> 
    tskcode_no_sub_abs C ->
    tskcode_no_sub_abs C'.
Proof.
  introv Hpu Hcstep Hnabs.
  inverts Hcstep.
  - eapply noabs_preserve_estep; eauto.
  - eapply noabs_preserve_sstep; eauto.
Qed. 

Lemma noabs_preserve_hapistep:
  forall osspc cd O cd' O' act,
    hapistep osspc cd O cd' O' act ->
    tskcode_no_sub_abs cd ->
    tskcode_no_sub_abs cd'. 
Proof.
  introv Hastep Hnabs.
  inverts Hastep; 
    try (simpl; simpl in Hnabs;
         simpljoin;
         split; auto; 
         right; eexists; eauto; fail).
Qed. 
    
Lemma noabs_preserve_htstep: 
  forall hp pu aspc t td C cst O C' cst' O' act,
    hp = (pu, aspc) -> 
    pu_noabs pu -> 
    htstep hp t td C cst O C' cst' O' act ->
    tskcode_no_sub_abs C ->
    tskcode_no_sub_abs C'. 
Proof.
  introv Hhp Hpu Hstep Hnabs.
  destruct hp as (pu_ & spc_).
  inverts Hhp.
  invert Hstep.
  - intros. inverts H. eapply noabs_preserve_cstep; eauto.
  - intros. inverts H. eapply noabs_preserve_hapistep; eauto.
Qed.

Definition task_pool_no_sub_abs (T: tasks) :=
  forall t C, get T t = Some C -> tskcode_no_sub_abs C. 

Lemma noabs_preserve_cstepstar:
  forall pu d C ge le M C' ge' le' M',
    pu_noabs pu -> 
    cstepstar pu d C (ge, le, M) C' (ge', le', M') ->
    tskcode_no_sub_abs C ->
    tskcode_no_sub_abs C'.
Proof.
  introv Hpu Hstepstar.
  inductions Hstepstar.
  - auto.
  - introv Hnabs.
    assert (tskcode_no_sub_abs C').
    { eapply noabs_preserve_cstep; eauto. }
    destruct m' as ((ge_ & le_) & m_).
    lets H_: IHHstepstar Hpu H0; eauto.
Qed. 

Lemma noabs_preserve_hpstep:
  forall hp pu spc T cst O T' cst' O' act,
    hp = (pu, spc) ->
    pu_noabs pu -> 
    hpstep hp T cst O T' cst' O' act ->
    task_pool_no_sub_abs T ->
    task_pool_no_sub_abs T'. 
Proof.
  introv Hhp Hpu Hstep Hnabs.
  inverts Hstep.
  - unfold task_pool_no_sub_abs in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0. rewrite set_a_get_a in Hget.
      inverts Hget.
      eapply noabs_preserve_htstep; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - inverts H.
    match goal with H': htistep _ _ _ _ _ |- _ => inverts H' end.
    unfolds.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      simpl. apply Hnabs in H1. simpl in H1.
      simpljoin.
      splits; auto.
      right; eexists; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - inverts H.
    unfold task_pool_no_sub_abs in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0.
      rewrite set_a_get_a in Hget.
      inverts Hget.
      apply Hnabs in H2.
      simpl in H2. simpl.
      simpljoin.
      split; auto.
      right. eexists; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
Qed.       

Lemma no_sub_abs_preserve_hpstepokstar:
  forall hp pu spc T cst O T' cst' O', 
    hp = (pu, spc) ->
    pu_noabs pu -> 
    hpstepokstar hp T cst O T' cst' O' ->
    task_pool_no_sub_abs T ->
    task_pool_no_sub_abs T'.
Proof.
  introv Hhp Hpu Hsteps.
  induction Hsteps.
  - auto.
  - introv Hnabs.
    eapply IHHsteps; eauto.
    inverts H.
    eapply noabs_preserve_hpstep; eauto.
Qed. 

Lemma reachable_no_sub_abs: 
  forall hp pu spc T cst O,
    hp = (pu, spc) -> 
    pu_noabs pu -> 
    reachable hp T cst O ->
    task_pool_no_sub_abs T. 
Proof.
  introv Hhp Hnabs Hrc. 
  unfolds in Hrc.
  destruct Hrc as (pu_ & spc_ & Hhp' & Hex).
  destruct Hex as (T0 & cst0 & O0 & Hinit & Hsteps). 

  unfold init in Hinit.
  destruct Hinit as (Hit & His).
  unfolds in Hit.
  destruct Hit as (Heqd & Hall).
  rewrite Hhp in Hhp'. inverts Hhp'.

  eapply no_sub_abs_preserve_hpstepokstar; eauto.
  unfolds.
  introv Hget.
  unfold get in Hget. unfold TasksMap in Hget.
  apply Hall in Hget.
  simpl.
  simpljoin.
  unfolds in Hnabs.
  unfolds.
  unfold nilcont.
  simpl.
  split; auto.
  left. eapply Hnabs; eauto.
Qed. 
    
    
Lemma cstep_not_knl_eval':
  forall hp pu spc T cst O t c ke ks c' ke' ks' d ge le M ge' le' M',
    hp = (pu, spc) -> 
    pu_noabs pu -> 
    reachable hp T cst O ->
    get T t = Some (c, (ke, ks)) -> 
    cstep pu d (c, (ke, ks)) (ge, le, M) (c', (ke', ks')) (ge', le', M') ->
    not_knl_stmt c'.
Proof.
  introv Hhp Hpu Hrc Hget Hstep.
  lets H_: reachable_no_sub_abs Hhp Hpu Hrc.
  unfold task_pool_no_sub_abs in H_.
  apply H_ in Hget.
  simpl in Hget.
  destruct Hget as (Hnas & Hnak).
  inverts Hstep;
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
  -
    inverts H8; 
      try (unfolds; right; eexists; splits; eauto; introv Hex; simpljoin; tryfalse; fail);  
      try (unfolds; left; eexists; eauto).
  -    
    inverts H8;
      try (unfolds; left; eexists; eauto; fail);  
      try (unfolds; right; eexists; split; eauto; introv Hex; simpljoin; tryfalse; fail).
    +
      simpl in Hnak.
      destruct Hnak as (Hns & Hnk).
      unfolds.
      right. eexists; splits; eauto.
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns. simpl in Hns. tryfalse.
    +
      destruct Hnas as [Hnabs | Hf].
      2: { simpljoin. tryfalse. }
      simpl in Hnabs.
      destruct Hnabs as (Hnabs1 & Hnabs2).
      unfolds. right. eexists; splits; eauto.
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hnabs1. simpl in Hnabs1. tryfalse.
    +
      unfolds. right. eexists; splits; eauto.
      simpl in Hnak.
      destruct Hnak as (Hns & Hnk).
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns. simpl in Hns. tryfalse.
    +
      unfolds. right. eexists; splits; eauto.
      simpl in Hnak.
      destruct Hnak as (Hns & Hnk).
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns. simpl in Hns. tryfalse.
    +
      unfolds. right. eexists; splits; eauto.
      simpl in Hnak.
      destruct Hnak as (Hns & Hnk).
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns. simpl in Hns. tryfalse.
    +
      unfolds. right. eexists; splits; eauto.
      simpl in Hnak.
      destruct Hnak as (Hns1 & Hns2 & Hnk).
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns2. simpl in Hns2. tryfalse.
    +
      unfolds. right. eexists; splits; eauto.
      simpl in Hnak.
      destruct Hnak as (Hns & Hnk).
      introv Hf.
      destruct Hf as (ss & Heq). rewrite Heq in Hns. simpl in Hns. tryfalse.
Qed.



Fixpoint kevt_no_nest (ks: stmtcont) :=
  match ks with
    kevent c ke ks => absintcont ks = None
  | kseq _ ks' | kcall _ _ _ ks' | kint _ _ _ ks'
  | kassignr _ _ ks' | kassignl _ _ ks' | kfuneval _ _ _ _ ks'
  | kif _ _ ks' | kwhile _ _ ks' | kret ks' => kevt_no_nest ks' 
  | kstop => True 
  end.

Definition pool_kevt_no_nest (T: tasks) :=
  forall t c ke ks,
    get T t = Some (c, (ke, ks)) ->
    kevt_no_nest ks. 


Lemma noevt_nonest: 
  forall ks, 
    absintcont ks = None ->
    kevt_no_nest ks.
Proof.
  induction ks; 
    introv Hncont; try (simpl; auto). 
  simpl in Hncont. tryfalse.
Qed.   
  
Lemma callcont_nnest:
  forall ks f s le' ks',  
    kevt_no_nest ks -> 
    callcont ks = Some (kcall f s le' ks') -> 
    kevt_no_nest ks'. 
Proof.
  induction ks; 
    introv Hnn Hcc;
    try (simpl in Hcc; simpl in Hnn; eapply IHks; eauto; fail).
  - inverts Hcc.
  - simpl in Hcc. inverts Hcc. simpl in Hnn. auto.
  - simpl in Hcc. tryfalse.
  - simpl in Hcc. simpl in Hnn. 
    eapply IHks; eauto.
    eapply noevt_nonest; eauto.
Qed.     
  
Lemma kevt_nnest_preserve_sstep:
  forall pu td c ks m c' ks' m', 
    sstep pu td c ks m c' ks' m' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'. 
Proof.
  introv Hstep Hnn.
  inverts Hstep; try (simpl; auto; fail). 
  eapply callcont_nnest; eauto.
Qed.

Lemma kevt_nnest_preserve_cstep:
  forall pu td c ke ks m c' ke' ks' m', 
    cstep pu td (c, (ke, ks)) m (c', (ke', ks')) m' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'. 
Proof.
  introv Hcstep Hnn.
  inverts Hcstep.
  - inverts H7. auto.
  - inverts H7.
    eapply kevt_nnest_preserve_sstep; eauto.
Qed.     

Lemma kevt_nnest_preserve_hapistep:
  forall spc c ke ks O c' ke' ks' O' act, 
    hapistep spc (c, (ke, ks)) O (c', (ke', ks')) O' act ->
    kevt_no_nest ks ->
    kevt_no_nest ks'. 
Proof.
  introv Hstep Hnn. 
  inverts Hstep; auto.
  - inverts H1. inverts H2. auto.
  - simpl in Hnn. 
    eapply noevt_nonest; eauto.
Qed.

Lemma kevt_nnest_preserve_htstep: 
  forall hp t td c ke ks cst O c' ke' ks' cst' O' act, 
    htstep hp t td (c, (ke, ks)) cst O (c', (ke', ks')) cst' O' act ->
    kevt_no_nest ks ->
    kevt_no_nest ks'.
Proof.
  introv Hstep Hnn.
  inverts Hstep.
  - eapply kevt_nnest_preserve_cstep; eauto.
  - eapply kevt_nnest_preserve_hapistep; eauto.
Qed.     

Lemma kevt_nnest_preserve_htistep: 
  forall ispc c ke ks O c' ke' ks' O', 
    htistep ispc (c, (ke, ks)) O (c', (ke', ks')) O' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'.
Proof.
  introv Hstep Hnn.
  inverts Hstep.
  simpl. auto.
Qed.

Lemma pool_kevt_nnest_preserve_hpstep: 
forall hp T cst O T' cst' O' act, 
  hpstep hp T cst O T' cst' O' act -> 
  pool_kevt_no_nest T ->
  pool_kevt_no_nest T'. 
Proof.
  introv Hstep Hnn. 
  inverts Hstep.
  - unfold pool_kevt_no_nest in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst t0. rewrite set_a_get_a in Hget.
      inverts Hget.
      destruct C as (c_ & ke_ & ks_). 
      eapply kevt_nnest_preserve_htstep; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - destruct C as (c & ke & ks).
    destruct C' as (c' & ke' & ks').
    unfold pool_kevt_no_nest in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst. rewrite set_a_get_a in Hget. inverts Hget.
      eapply kevt_nnest_preserve_htistep; eauto.
    + rewrite set_a_get_a' in Hget; eauto.
  - unfold pool_kevt_no_nest in *.
    introv Hget.
    casetac t t0 He Hne.
    + subst. rewrite set_a_get_a in Hget. inverts Hget.
      eapply Hnn; eauto. 
    + rewrite set_a_get_a' in Hget; eauto. 
Qed.       
      
Lemma pool_kevt_nnest_preserve_hpstepokstar: 
  forall hp T cst O T' cst' O', 
    hpstepokstar hp T cst O T' cst' O' ->
    pool_kevt_no_nest T ->
    pool_kevt_no_nest T'. 
Proof.
  introv Hsteps.
  induction Hsteps.
  - auto.
  - introv Hnn.
    eapply IHHsteps; eauto.
    inverts H.
    eapply pool_kevt_nnest_preserve_hpstep; eauto.
Qed. 

Lemma reachable_kevt_nnest:
  forall hp T cst O, 
    reachable hp T cst O ->
    pool_kevt_no_nest T. 
Proof.
  introv Hrc.
  unfold reachable in Hrc.
  destruct Hrc as (pu & spc & Hhp & Hex).
  destruct Hex as (T0 & cst0 & O0 & Hinit & Hss).
  unfold init in Hinit.
  destruct Hinit as (Hit & His).
  unfolds in Hit.
  destruct Hit as (_ & Ha).
  eapply pool_kevt_nnest_preserve_hpstepokstar; eauto.
  unfolds.
  introv Hget.  
  lets H_: Ha Hget.
  simpljoin.
  unfold nilcont in H.
  inverts H.
  simpl; auto. 
Qed.


