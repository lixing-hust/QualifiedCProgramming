
Require Import memory.
Require Import sem_language. 
Require Import sem_opsem. 
Require Import aux_notations.
Require Import join_lib.
Require Import sem_tacs.

Require Import sem_sys. 

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
  forall pu c ks m c' ks' m', 
    sstep pu c ks m c' ks' m' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'. 
Proof.
  introv Hstep Hnn.
  inverts Hstep; try (simpl; auto; fail). 
  eapply callcont_nnest; eauto.
Qed.

Lemma kevt_nnest_preserve_cstep:
  forall pu c ke ks m c' ke' ks' m', 
    cstep pu (c, (ke, ks)) m (c', (ke', ks')) m' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'. 
Proof.
  introv Hcstep Hnn.
  inverts Hcstep.
  - inverts H6. auto.
  - inverts H6.
    eapply kevt_nnest_preserve_sstep; eauto.
Qed.     

Lemma kevt_nnest_preserve_hapistep:
  forall spc c ke ks O c' ke' ks' O' lau lau', 
    hapistep spc (c, (ke, ks)) O lau (c', (ke', ks')) O' lau' ->
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
  forall hp t c ke ks cst O c' ke' ks' cst' O' lau lau', 
    htstep hp t (c, (ke, ks)) cst O lau (c', (ke', ks')) cst' O' lau' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'.
Proof.
  introv Hstep Hnn.
  inverts Hstep.
  - eapply kevt_nnest_preserve_cstep; eauto.
  - eapply kevt_nnest_preserve_hapistep; eauto.
Qed.     

Lemma kevt_nnest_preserve_htistep: 
  forall c ke ks O c' ke' ks' O', 
    htistep int_spec (c, (ke, ks)) O (c', (ke', ks')) O' ->
    kevt_no_nest ks ->
    kevt_no_nest ks'.
Proof.
  introv Hstep Hnn.
  inverts Hstep.
  unfold int_spec in *.
  simpl in *. 
  tryfalse. 
Qed.

Lemma pool_kevt_nnest_preserve_hpstep: 
forall pu aspc sc T cst O T' cst' O' lau lau', 
  hpstep (pu, (aspc, int_spec, sc)) T cst O lau T' cst' O'  lau' -> 
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
      inverts H.
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
  forall pu aspc sc T cst O T' cst' O' lau lau', 
    hpstepokstar (pu, (aspc, int_spec, sc)) T cst O lau T' cst' O' lau' ->
    pool_kevt_no_nest T ->
    pool_kevt_no_nest T'. 
Proof.
  introv Hsteps.
  remember (pu, (aspc, int_spec, sc)) as hp.
  induction Hsteps.
  - auto.
  - introv Hnn.
    subst p. 
    eapply IHHsteps; eauto.
    inverts H.
    eapply pool_kevt_nnest_preserve_hpstep; eauto.
Qed. 

Require Import sem_init.

Lemma reachable_kevt_nnest:
  forall pu aspc sc T cst O lau, 
    reachable (pu, (aspc, int_spec, sc)) T cst O lau ->
    pool_kevt_no_nest T. 
Proof.
  introv Hrc.
  unfold reachable in Hrc.
  destruct Hrc as (pu_ & spc & Hhp & Hex).
  destruct Hex as (T0 & cst0 & O0 & au0 & Hinit & Hss).
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

