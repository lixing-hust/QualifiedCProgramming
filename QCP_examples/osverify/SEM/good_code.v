
Require Import sem_language.
Require Import sem_opsem.
Require Import sem_sys.
Require Import succ_gen.

Require Import sem_init.
Require Import sem_tacs.
Require Import join_lib. 

Require Import good_apis. 

Fixpoint GoodStmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sifthen _ s => GoodStmt_h s
    | swhile _ s' => GoodStmt_h s'
    | sret => True
    | srete  _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => True
    | hapi_code _ => False
  end.

Definition good_client_code (client_code: progunit) :=
      (forall (f : fid) (a : type) (b c : decllist) (s : stmts),
       client_code f = Some (a, b, c, s) -> GoodStmt_h s).

Definition good_api_stmt s:=
  (exists fid acode ft vl,
      api_spec' fid = Some (acode, ft)
      /\  (In s (get_all_succs (acode vl))))
  (* \/ (exists hid icode,  int_spec hid = Some icode /\ In s (get_all_succs icode)) *)
  \/ (exists v, s = END v) \/ (s = ABORT).

Fixpoint goodstmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sifthen _ s => goodstmt_h s
    | swhile _ s' => goodstmt_h s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sfexec _ _ _ => True
    | sfree _ _ => True
    | salloc _ _ => True
    | sprim _ => True
    | hapi_code s => good_api_stmt s
  end.

Definition goodeval_h (c:cureval):=
  match c with
    | cure _ => True
    | curs s => goodstmt_h s
  end.

Fixpoint goodks_h ks:=
  match ks with
    | kint _ _ _ _ => False
    | kevent c ke ks' => goodeval_h c /\ goodks_h ks'
    | kstop => True
    | kcall _ s _ ks' => goodks_h ks' /\ goodstmt_h s
    | kseq s ks' => goodks_h ks' /\ goodstmt_h s
    | kassignr _ _ ks' => goodks_h ks'
    | kassignl _ _ ks' => goodks_h ks'
    | kfuneval _ _ _ _ ks' => goodks_h ks'
    | kif s1 s2 ks' => goodks_h ks' /\ goodstmt_h s1 /\ goodstmt_h s2
    | kwhile _ s ks' => goodks_h ks' /\ goodstmt_h s
    | kret ks' => goodks_h ks'
  end.

Definition goodcode_h (c:code):=
  match c with
    | (c,(ke,ks)) => goodeval_h c /\ goodks_h ks
  end.

Definition good_task_code (T: tasks):=
  forall t c, get T t = Some c -> goodcode_h c.


Lemma GoodStmt_imp_goodstmt:
  forall s,
    GoodStmt_h s ->
    goodstmt_h s.
Proof.
  induction s; intros; simpl in *; auto.
  simpljoin.
  split.
  eapply IHs1; eauto.
  eapply IHs2; eauto.
  simpljoin.
  split.
  eapply IHs1; eauto.
  eapply IHs2; eauto.
  tryfalse.
Qed.

Lemma callcont_goodks:
  forall ks f s le ks',
    callcont ks = Some (kcall f s le ks') ->
    goodks_h ks ->
    goodks_h ks'.
Proof.
  induction ks;intros;simpl in *;auto;tryfalse; simpljoin; auto.
  apply IHks in H;auto.
  inverts H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
  apply IHks in H;auto.
Qed.
               
Lemma init_good_tasks:
  forall cliprogs T cst O,
    init_tsk cliprogs T cst O ->
    good_client_code cliprogs ->
    good_task_code T.
Proof.
  introv Htsk Hgc.
  destruct Htsk as (Heqdom & Hgetex).
  unfolds in Hgc.
  unfold good_task_code.
  introv Hget.
  destruct c as (c & (ke & ks)).
  unfold goodcode_h.
  eapply Hgetex in Hget.
  destruct Hget as (s & f & d1 & d2 & tp & Heq & Hpu).
  inverts Heq.
  eapply Hgc in Hpu.
  simpl.
  split; auto.
  eapply GoodStmt_imp_goodstmt; eauto.
Qed.

Lemma good_task_estep_preserve:
  forall T t c ke ks m m' c' ke',
    get T t = Some (c, (ke, ks)) ->
    good_task_code T ->
    estep c ke m c' ke' m' ->
    good_task_code (set T t (c', (ke', ks))).
Proof.
  introv Hget Htsk Hstep.
  lets Htsk': Htsk t (c, (ke, ks)) Hget.
  destruct Htsk' as (Heval &Hks).
  introv Hget'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  unfolds.
  split; auto.
  inverts Hstep; auto.
  rewrite set_a_get_a' in Hget'; auto.
  eapply Htsk; eauto.
Qed.

Lemma good_task_sstep_preserve:
  forall T t c ke ks m m' c' ks' p,
    get T t = Some (c, (ke, ks)) ->
    good_task_code T ->
    good_client_code p ->
    sstep p c ks m c' ks' m' ->
    good_task_code (set T t (c', (ke, ks'))).
Proof.
  introv Hget Htsk Hclt Hstep.
  lets Htsk': Htsk t (c, (ke, ks)) Hget.
  destruct Htsk' as (Heval &Hks).
  introv Hget'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  unfolds.
  inverts Hstep; simpl in Heval, Hks; simpljoin; simpl; split; auto.
  split; auto.
  eapply GoodStmt_imp_goodstmt; eauto.
  eapply callcont_goodks; eauto.
  rewrite set_a_get_a' in Hget'; auto.
  eapply Htsk; eauto.
Qed.

Lemma good_task_cstep_preserve:
  forall T t C m m' C' p,
    get T t = Some C ->
    good_task_code T ->
    good_client_code p ->
    cstep p C m C' m' ->
    good_task_code (set T t C').
Proof.
  introv Hget Htsk Hclt Hstep.
  inverts Hstep.
  eapply good_task_estep_preserve; eauto.
  eapply good_task_sstep_preserve; eauto.
Qed.

(* Lemma abt_succs_contra:  *)
(*   forall cd i,  *)
(*     nth_error (get_all_succs (ABORT)) i = Some cd -> *)
(*     cd = ABORT. *)
(* Proof. *)
(*   induction i.  *)
(*   introv H. *)
(*   simpl in H. inverts H. auto. *)
(*   introv H. *)
(*   simpl in H. *)
(*   rewrite nth_error_nil in H. tryfalse. *)
(* Qed. *)

Lemma good_api_stmt_spec_step_preserve:
  forall cd cd' O O' laust laust' sc,
    good_api_stmt cd ->
    spec_step sc cd O laust cd' O' laust' ->
    good_api_stmt cd'.
Proof.
  introv Hcd Hstep.
  destruct Hcd as [Hapi | [Hend | Habt]];
    [ | simpljoin; inverts Hstep | subst; inverts Hstep].
  (* api_spec *)
  destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
  eapply api_spec_step_succs_preserve in Hin; eauto.
  unfold good_api_stmt.
  destruct Hin as [ | [ | ]]; eauto.
  left.
  repeat eexists; eauto.
Qed. 

Lemma good_task_hapistep_preserve:
  forall T p O t C C' O' laust laust',
    get T t = Some C ->
    good_task_code T ->
    good_client_code p ->
    get O curtid = Some (oscurt t) ->
    hapistep os_spec' C O laust C' O' laust' ->
    good_task_code (set T t C').
Proof.
  introv Hgetc Htsk Hclt Hgett Hstep.
  unfold os_spec' in Hstep.
  lets Htsk': Htsk t C Hgetc.
  destruct C as (c, (ke, ks)).
  destruct C' as (c', (ke', ks')).
  destruct Htsk' as (Heval &Hks).
  introv Hgetc'.
  destruct c0 as (c0 & (ke0 & ks0)).
  casetac t t0 Heq Hneq.
  2:{
    rewrite set_a_get_a' in Hgetc'; auto.
    eapply Htsk; eauto.
  }
  subst.
  rewrite set_a_get_a in Hgetc'.
  inverts Hgetc'.
  unfolds.
  inverts Hstep;
    repeat try (match goal with H: (_, _) = (_, _) |- _ => inverts H end);
    simpl in Heval, Hks; simpljoin; simpl; split; auto.
  (* hapienter_step *)
  unfolds.
  left.
  exists f r (tp,tl) (vl ++ vl').
  split; auto.
  unfold get_all_succs.
  rewrite <- app_comm_cons.
  simpl; auto.
  (* hidapi_step *)
  match goal with H: spec_step _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
  simpl in Hstep.
  eapply good_api_stmt_spec_step_preserve; eauto.
Qed.

Lemma good_task_htstep_preserve:
  forall T p O t C cst C' cst' O' aust aust',
    get T t = Some C ->
    good_task_code T ->
    good_client_code p ->
    get O curtid = Some (oscurt t) ->
    htstep (p, os_spec') t C cst O aust C' cst' O' aust' ->
    good_task_code (set T t C').
Proof.
  introv Hgetc Htsk Hclt Hgett Hstep.
  inverts Hstep; 
    try (match goal with H: (_, _) = (_, _) |- _ => inverts H end). 
  eapply good_task_cstep_preserve; eauto.
  eapply good_task_hapistep_preserve; eauto.
Qed.

Lemma hpstep_goodcode_h:
  forall pc T cst O T' cst' O' aust aust',
    good_task_code T ->
    good_client_code pc ->
    hpstep_ok (pc, os_spec') T cst O aust T' cst' O' aust' ->
    good_task_code T'.
Proof.
  introv Hgt Hgc Hstep.
  inverts Hstep.
  match goal with H: hpstep _ _ _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
  inverts Hstep.
  - (* htstep *)
    eapply good_task_htstep_preserve; eauto.
  - (* htistep *)
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    inverts H4.
    unfold int_spec in *.
    unfold int_spec_list in *.
    simpl in H. tryfalse. 
  - (* hswi_step *)
    match goal with H: nabt _  |- _ => rename H into Hnabt end.
    match goal with H: get T _ = _  |- _ => rename H into Hgetc end.
    match goal with H: get _ curtid = _  |- _ => rename H into Hgett end.
    match goal with H: (_, _) = (_, _) |- _ => inverts H end.
    lets Hgt': Hgt Hgetc; eauto. 
    destruct Hgt' as (Heval & Hks).
    introv Hgetc'.
    destruct c as (c0 & (ke0 & ks0)).
    casetac t t0 Heq Hneq.
    2:{
      rewrite set_a_get_a' in Hgetc'; eauto.
    }
    subst.
    rewrite set_a_get_a in Hgetc'.
    inverts Hgetc'.
    simpl in Heval.
    simpl.
    split; eauto.
    destruct Heval as [Hapi | [Hend | Habt]];
      [ | simpljoin; tryfalse | tryfalse ].
    destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
    eapply api_spec_step_succs_preserve with (cd' := s) in Hin; eauto.
    2:{
      eapply spec_seq_step_end; eauto. 
      eapply spec_sched_step with (O:= set O curtid (oscurt t')) (t:= t'); eauto. 
      rewrite set_a_get_a; eauto.
      instantiate (1:=GetHPrio).
      unfold GetHPrio in *.
      simpljoin. 
      rewrite set_a_get_a'; eauto. 
      repeat eexists; eauto.
      introv Hf; tryfalse.
      eapply map_join_emp; eauto. 
    }
    unfolds.
    destruct Hin as [ | [ | ]]; eauto.
    left; repeat eexists; eauto.

    Unshelve.
    exact {| tskpt := PtNormal |}. 
Qed. 

Lemma hpstepstar_goodcode_h:
  forall pc T cst O T' cst' O' aust aust',
    hpstepokstar (pc, os_spec') T cst O aust T' cst' O' aust' ->
    good_task_code T ->
    good_client_code pc ->
    good_task_code T'.
Proof.
  introv Hstep.
  inductions Hstep; intros.
  auto.
  eapply IHHstep; eauto.
  eapply hpstep_goodcode_h; eauto.
Qed.

Lemma reachable_good_tasks:
  forall cliprogs T cst O aust,
    good_client_code cliprogs ->
    reachable (cliprogs, os_spec') T cst O aust ->
    good_task_code T.
Proof.
  introv Hgc Hr.
  destruct Hr as (pu & spc & Heq & Hr).
  inverts Heq.
  destruct Hr as (T0 & cst0 & O0 & aust0 & Hinit & Hstep).
  lets Hgt: init_good_tasks Hinit Hgc.
  eapply hpstepstar_goodcode_h; eauto.
Qed.


    

