
Require Import memory.
Require Import if_language.
Require Import if_opsem.
Require Import if_succ_gen.

Require Import properties.
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import buffer_apispecs. 
Require Import intspecs.
Require Import osspecs.
Require Import equiv_prop. 
Require Import join_lib.
Require Import spec_aux_defs.


Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Ltac re_err_contra k:=
     repeat try
        (match goal with
         | H: nth_error (nil) _ = Some _ |- _ => idtac
         | H: nth_error _ _ = Some _ |- _ => destruct k; simpl in H
        end).

Ltac re_step_contra :=
  repeat try (match goal with
              | H: spec_step _ (_ ;; _) _ _ _ _ |- _ => inverts H
              | H: spec_step _ _ _ _ _ _ |- _ => idtac
              end);
  (match goal with H: spec_step _ _ _ _ _ _ |- _ => inverts H end).

Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end].

Ltac my_succs_solver :=
match goal with
Hnth: nth_error _ _ = Some _ |- _
=> simpl in Hnth;
    inverts Hnth;
    repeat try re_step_contra;
    try solve [solve_endabt];
    try solve [auto];
    try solve [eauto]
end.


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
    | sprint _ => True
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
 (exists fid acode ft vl, api_spec fid = Some (acode, ft)
                                           /\  (In s (get_all_succs (acode vl))))
 \/ (exists hid icode,  int_spec hid = Some icode /\ In s (get_all_succs icode))
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
    | sprint _ => True
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

Definition hapi_abs_c T  (aspec: osapispec) (ispec: osintspec) :=
  forall t c ke ks,
    get T t = Some (curs (hapi_code c), (ke, ks)) -> 
   ( exists fid s ft vl, aspec fid = Some (s, ft)
                                     /\  (In c (get_all_succs (s vl)))
                                     /\ ~(exists c' ke' ks', ks = kevent c' ke' ks'))
    \/ ( exists hid s,  ispec hid = Some s /\
                                     In c (get_all_succs s) /\ (exists c' ke' ks', ks = kevent c' ke' ks')).


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
  forall T t c ke ks td m m' c' ke',
    get T t = Some (c, (ke, ks)) ->
    good_task_code T ->
    estep td c ke m c' ke' m' ->
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
  forall T t c ke ks td m m' c' ks' p,
    get T t = Some (c, (ke, ks)) ->
    good_task_code T ->
    good_client_code p ->
    sstep p td c ks m c' ks' m' ->
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
  forall T t C td m m' C' p,
    get T t = Some C ->
    good_task_code T ->
    good_client_code p ->
    cstep p td C m C' m' ->
    good_task_code (set T t C').
Proof.
  introv Hget Htsk Hclt Hstep.
  inverts Hstep.
  eapply good_task_estep_preserve; eauto.
  eapply good_task_sstep_preserve; eauto.
Qed.

Lemma mqsend_succs_nabt:
  forall vl k,
    (mqsend vl) <> ABORT ->
    nth_error (get_all_succs (mqsend vl)) k <> Some (ABORT).
Proof.
  introv Hnabt.
  do 12 try (destruct vl; simpl in Hnabt;tryfalse);
  try destruct v; simpl in Hnabt; tryfalse;
  try destruct v1; simpl in Hnabt; tryfalse;
  try destruct v3; simpl in Hnabt; tryfalse;
  try destruct v5; simpl in Hnabt; tryfalse;
  try destruct v6; simpl in Hnabt; tryfalse.
  introv Hnth.
  re_err_contra k; simpl in Hnth; inverts Hnth.
  erewrite nth_error_nil in *; tryfalse.
Qed.

Lemma mqsend_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    mqsend vl <> ABORT -> 
    nth_error (get_all_succs (mqsend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (mqsend vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as send_vl. 
  do 11 try (destruct send_vl; simpl in Hnabt;tryfalse); 
  try destruct v; simpl in Hnabt; tryfalse;
  try destruct v1; simpl in Hnabt; tryfalse;
  try destruct v3; simpl in Hnabt; tryfalse;
  try destruct v5; simpl in Hnabt; tryfalse;
  try destruct v6; simpl in Hnabt; tryfalse.
   clear Hnabt.
  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  (* n = 7 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  (* n = 8 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 9 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 20.
  (* n = 10 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 11 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 12 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 13 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 14 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 15 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 16 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 17 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 18 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 19 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 20 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 21 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 22 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 23 *)
  re_err_contra n; try my_succs_solver.
  tryfalse.
  tryfalse.
Qed.

Lemma mqrecv_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    mqreceive vl <> ABORT -> 
    nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (mqreceive vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  remember vl as recv_vl.
  do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
  try destruct v; simpl in Hnabt; tryfalse;
  try destruct v1; simpl in Hnabt; tryfalse;
  try destruct v3; simpl in Hnabt; tryfalse;
  try destruct v5; simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 7 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 8 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 20.
  (* n = 9 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* left; simpl; auto 30. *)
  (* left; simpl; auto 30. *)
  (* n = 10 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 11 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 12 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 13 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 14 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 15 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 16 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 17 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 18 *)
  destruct n; [ my_succs_solver | idtac].
  simpl in Hnth.
  rewrite nth_error_nil in Hnth. 
  tryfalse.
Qed.

Lemma mqtimedrecv_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    mqtimedreceive vl <> ABORT -> 
    nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (mqtimedreceive vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  remember vl as recv_vl.
  do 12 try (destruct recv_vl; simpl in Hnabt;tryfalse);
  try destruct v; simpl in Hnabt; tryfalse;
  try destruct v1; simpl in Hnabt; tryfalse;
  try destruct v3; simpl in Hnabt; tryfalse;
  try destruct v4; simpl in Hnabt; tryfalse;
  try destruct v6; simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 7 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 8 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 20.
  (* n = 9 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 10 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 11 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 12 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.  
  (* n = 13 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.  
  (* n = 14 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 15 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 16 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 17 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 18 *)
  destruct n; simpl in Hnth; inverts Hnth.
  re_step_contra.
  right; right. eexists; eauto.
  right; left. auto.
  rewrite nth_error_nil in H0. 
  tryfalse. 
Qed.

Lemma qportpost_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    qportpost vl <> ABORT -> 
    nth_error (get_all_succs (qportpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (qportpost vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as post_vl.
  do 4 try (destruct post_vl; simpl in Hnabt;tryfalse);
  try destruct v0; simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  left; simpl; auto 10.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  left; simpl; auto 10.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
 left; simpl; auto 15.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 7 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 8 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n = 9 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 10 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 11 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 12 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 13 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 14 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 15 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 16 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 17 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 18 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 19 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 20 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 21 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 22 *)
  re_err_contra n; try my_succs_solver.
  tryfalse.
  tryfalse.
Qed.

Lemma qportpend_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    qportpend vl <> ABORT -> 
    nth_error (get_all_succs (qportpend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (qportpend vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as pend_vl.
  do 5 try (destruct pend_vl; simpl in Hnabt;tryfalse);
  try destruct v1; simpl in Hnabt; tryfalse.
  clear Hnabt.
  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  left; simpl; auto 10.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 10.
  left; simpl; auto 10.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 7 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 8 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 9 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 10 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 11 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 12 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 13 *)
  destruct n; [ my_succs_solver | idtac].
  (* n = 14 *)
  re_err_contra n; try my_succs_solver.
  tryfalse.
  tryfalse.
Qed.

Lemma sportpost_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    sampleportpost vl <> ABORT -> 
    nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (sampleportpost vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as spost_vl.
  do 5 try (destruct spost_vl; simpl in Hnabt;tryfalse);
  try destruct v0; simpl in Hnabt; tryfalse.
  clear Hnabt.
  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  left; simpl; auto 30.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 30.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 20.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].

  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 
Qed. 

Lemma portaccept_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    portaccept vl <> ABORT -> 
    nth_error (get_all_succs (portaccept vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (portaccept vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as pacc_vl.
  do 5 try (destruct pacc_vl; simpl in Hnabt;tryfalse);
  try destruct v0; simpl in Hnabt; tryfalse.
  clear Hnabt.
  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 20.
  (* n = 3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 20.
  (* n = 4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  (* n = 5 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 20.
  left; simpl; auto 20.
  (* n = 6 *)
  destruct n; [ my_succs_solver | idtac].

  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 
Qed. 

Lemma bufferpost_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    bufferpost vl <> ABORT -> 
    nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (bufferpost vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as post_vl.
  do 5 try (destruct post_vl; simpl in Hnabt;tryfalse);
  try destruct v1; simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n = 0 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n = 1 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n = 2 *)
  destruct n; [ my_succs_solver | idtac].
  (* n=3 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n=4 *)
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto 15.
  (* n=5 *)
  destruct n; [ my_succs_solver | idtac].  
  left; simpl; auto 15.
  (* n=6 *)
  destruct n; [ my_succs_solver | idtac].  

  simpl in Hnth. rewrite nth_error_nil in Hnth. false. 
Qed.   

Lemma bufferaccept_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    bufferaccept vl <> ABORT -> 
    nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (bufferaccept vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as acc_vl.
  do 5 try (destruct acc_vl; simpl in Hnabt;tryfalse).
  clear Hnabt.

  (* n=0 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  (* n=1 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.  
  left; simpl; auto 15.  
  (* n=2 *)
  destruct n; [ my_succs_solver | idtac ].
  (* n=3 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.

  (* n=4 *)
  destruct n; [ my_succs_solver | idtac ].

  simpl in Hnth. rewrite nth_error_nil in Hnth. false. 
Qed. 

Lemma bufferpend_nabt_spec_step_succs_preserve:
  forall n vl cd O cd' O' act,
    bufferpend vl <> ABORT -> 
    nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (bufferpend vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep. 
  remember vl as pend_vl.
  do 4 try (destruct pend_vl; simpl in Hnabt;tryfalse);
  try destruct v0;  simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n=0 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  (* n=1 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n=2 *)
  destruct n; [ my_succs_solver | idtac ].
  (* n=3 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  left; simpl; auto 15.
  (* n=4 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  (* n=5 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.
  (* n=6 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.  
  (* n=7 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.  
  (* n=8 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.    
  left; simpl; auto 15.    
  (* n=9 *)
  destruct n; [ my_succs_solver | idtac ].
  left; simpl; auto 15.      
  (* n=10 *)
  destruct n; [ my_succs_solver | idtac ].

  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 
Qed. 

Lemma api_spec_step_succs_preserve:
  forall fid acode ft vl cd cd' O O' act,
    api_spec fid = Some (acode, ft) ->
    In cd (get_all_succs (acode vl)) ->
    spec_step get_hprio_d cd O cd' O' act ->
    In cd' (get_all_succs (acode vl)) \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hpu Hcd Hstep.
  unfold api_spec in Hpu.
  lets Hnth: In_nth_error cd Hcd.
  destruct Hnth as (n & Hnth).
  simpl in Hpu.
  destruct (Zeq_bool mq_send fid) eqn: eq1;
    try destruct (Zeq_bool mq_recv fid) eqn: eq2;
    try destruct (Zeq_bool mq_timedrecv fid) eqn: eq2_; 
    try destruct (Zeq_bool q_port_post fid) eqn: eq3;
    try destruct (Zeq_bool q_port_pend fid) eqn: eq4;
    try destruct (Zeq_bool sample_port_post fid) eqn: eq4_; 
    try destruct (Zeq_bool port_accept fid) eqn: eq4__; 
    try destruct (Zeq_bool buffer_post fid) eqn: eq5;
    try destruct (Zeq_bool buffer_accept fid) eqn: eq6;
    try destruct (Zeq_bool buffer_pend fid) eqn: eq7; 
    try inverts Hpu;
    tryfalse;
    try rewrite <- Zeq_is_eq_bool in eq1;
    try rewrite <- Zeq_is_eq_bool in eq2;
    try rewrite <- Zeq_is_eq_bool in eq2_; 
    try rewrite <- Zeq_is_eq_bool in eq3;
    try rewrite <- Zeq_is_eq_bool in eq4;
    try rewrite <- Zeq_is_eq_bool in eq4_; 
    try rewrite <- Zeq_is_eq_bool in eq4__; 
    try rewrite <- Zeq_is_eq_bool in eq5;
    try rewrite <- Zeq_is_eq_bool in eq6;
    try rewrite <- Zeq_is_eq_bool in eq7; 
    unfold mq_send, mq_recv, mq_timedrecv,
    q_port_pend, q_port_pend, sample_port_post, port_accept in *;
    subst;
    tryfalse.
  - (* mqsend *)
    assert (Habt: mqsend vl = ABORT \/ mqsend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* mqsend vl <> ABORT *)
    eapply mqsend_nabt_spec_step_succs_preserve; eauto.
  - (* mqreceive *)
    assert (Habt: mqreceive vl = ABORT \/ mqreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* mqreceive vl <> ABORT *)
    eapply mqrecv_nabt_spec_step_succs_preserve; eauto.
  - (* mqtimedreceive *)
    assert (Habt: mqtimedreceive vl = ABORT \/ mqtimedreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* mqtimedreceive vl <> ABORT *)
    eapply mqtimedrecv_nabt_spec_step_succs_preserve; eauto.  
  - (* qportpost *)
    assert (Habt: qportpost vl = ABORT \/ qportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* qportpost vl <> ABORT *)
    eapply qportpost_nabt_spec_step_succs_preserve; eauto.
  - (* qportpend *)
    assert (Habt: qportpend vl = ABORT \/ qportpend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* qportpend vl <> ABORT *)
    eapply qportpend_nabt_spec_step_succs_preserve; eauto.
  - (* sampleportpost *)
    assert (Habt: sampleportpost vl = ABORT \/ sampleportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* sampleportpost vl <> ABORT *)
    eapply sportpost_nabt_spec_step_succs_preserve; eauto.    
  - (* portaccept *)
    assert (Habt: portaccept vl = ABORT \/ portaccept vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* portaccept vl <> ABORT *)
    eapply portaccept_nabt_spec_step_succs_preserve; eauto. 
  - (* bufferpost *)
    assert (Habt: bufferpost vl = ABORT \/ bufferpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* bufferpost vl <> ABORT *)
    eapply bufferpost_nabt_spec_step_succs_preserve; eauto.
  - (* bufferaccept *)
    assert (Habt: bufferaccept vl = ABORT \/ bufferaccept vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* bufferaccept vl <> ABORT *)
    eapply bufferaccept_nabt_spec_step_succs_preserve; eauto.
  - (* bufferpend *)
    assert (Habt: bufferpend vl = ABORT \/ bufferpend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    simpl in Hcd.
    destruct Hcd; tryfalse.
    subst.
    inverts Hstep.
    (* bufferpend vl <> ABORT *)
    eapply bufferpend_nabt_spec_step_succs_preserve; eauto.    
Qed.


Lemma tickisr_spec_step_succs_preserve:
  forall n cd O cd' O' act,
    nth_error (get_all_succs tickisr) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    List.In cd' (get_all_succs (tickisr))
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnth Hstep. 
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  destruct n; [ my_succs_solver | idtac].
  left; simpl; auto.
  destruct n; [ my_succs_solver | idtac].
  re_err_contra n; try my_succs_solver.
  tryfalse.
  tryfalse.
Qed.

Lemma int_spec_step_succs_preserve:
forall hid icode cd cd' O O' act,
int_spec hid = Some icode ->
In cd (get_all_succs icode) ->
spec_step get_hprio_d cd O cd' O' act ->
In cd' (get_all_succs (icode)) \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
introv Hpu Hcd Hstep.
unfold int_spec in Hpu.
lets Hnth: In_nth_error cd Hcd.
destruct Hnth as (n & Hnth).
simpl in Hpu.
do 6 try destruct hid; tryfalse.
inverts Hpu.
eapply tickisr_spec_step_succs_preserve; eauto.
Qed.

Lemma good_api_stmt_spec_step_preserve:
forall cd cd' O O' act,
good_api_stmt cd ->
spec_step get_hprio_d cd O cd' O' act ->
good_api_stmt cd'.
Proof.
introv Hcd Hstep.
destruct Hcd as [Hapi | [Hint | [Hend | Habt]]];
[ | | simpljoin; inverts Hstep | subst; inverts Hstep].
(* api_spec *)
destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
eapply api_spec_step_succs_preserve in Hin; eauto.
unfold good_api_stmt.
destruct Hin as [ | [ | ]]; eauto.
left.
repeat eexists; eauto.
(* int_spec *)
destruct Hint as (hid & icode & Hint & Hin).
eapply int_spec_step_succs_preserve in Hin; eauto.
unfold good_api_stmt.
destruct Hin as [ | [ | ]]; eauto.
right.
repeat eexists; eauto.
Qed.

Lemma good_task_hapistep_preserve:
forall T p O t pr d C C' O' act ,
get T t = Some C ->
good_task_code T ->
good_client_code p ->
get O curtid = Some (oscurt t) ->
task_prio_id O pr t ->
dom_for_prio pr = d ->
hapistep os_spec C O C' O' act ->
good_task_code (set T t C').
Proof.
introv Hgetc Htsk Hclt Hgett Hpr Hdom Hstep.
unfold os_spec in Hstep.
lets Htsk': Htsk t C Hgetc.
destruct C as (c, (ke, ks)).
destruct C' as (c', (ke', ks')).
destruct Htsk' as (Heval &Hks).
introv Hgetc'.
destruct c0 as (c0 & (ke0 & ks0)).
casetac t t0 Heq Hneq.
2:{ rewrite set_a_get_a' in Hgetc'; auto.
      eapply Htsk; eauto. }
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
match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end.
simpl in Hstep.
eapply good_api_stmt_spec_step_preserve; eauto.
Qed.

Lemma good_task_htstep_preserve:
forall T p O t pr d C cst C' cst' O' act ,
get T t = Some C ->
good_task_code T ->
good_client_code p ->
get O curtid = Some (oscurt t) ->
task_prio_id O pr t ->
dom_for_prio pr = d ->
htstep (p, os_spec) t d C cst O C' cst' O' act ->
good_task_code (set T t C').
Proof.
introv Hgetc Htsk Hclt Hgett Hpr Hdom Hstep.
inverts Hstep; 
try (match goal with H: (_, _) = (_, _) |- _ => inverts H end). 
eapply good_task_cstep_preserve; eauto.
eapply good_task_hapistep_preserve; eauto.
Qed.

Lemma good_task_htistep_preserve:
forall T p O t C C' O',
get T t = Some C ->
good_task_code T ->
good_client_code p ->
get O curtid = Some (oscurt t) ->
htistep int_spec C O C' O' ->
good_task_code (set T t C').
Proof.
introv Hgetc Htsk Hclt Hgett Hstep.
lets Htsk': Htsk t C Hgetc.
destruct C as (c, (ke, ks)).
destruct C' as (c', (ke', ks')).
destruct Htsk' as (Heval &Hks).
introv Hgetc'.
destruct c0 as (c0 & (ke0 & ks0)).
casetac t t0 Heq Hneq.
2:{ rewrite set_a_get_a' in Hgetc'; auto.
      eapply Htsk; eauto. }
subst.
rewrite set_a_get_a in Hgetc'.
inverts Hgetc'.
unfolds.
inverts Hstep;
repeat try (match goal with H: (_, _) = (_, _) |- _ => inverts H end).
simpl.
splits; auto.
unfold good_api_stmt.
right. left.
repeat eexists; eauto.
simpl; auto.
Qed.

Lemma hpstep_goodcode_h:
  forall pc T cst O T' cst' O' act,
    good_task_code T ->
    good_client_code pc ->
    hpstep_ok (pc,os_spec) T cst O T' cst' O' act ->
    good_task_code T'.
Proof.
introv Hgt Hgc Hstep.
inverts Hstep.
match goal with H: hpstep _ _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
inverts Hstep.
- (* htstep *)
   eapply good_task_htstep_preserve; eauto.
- (* htistep *)
  match goal with H: (_, _) = (_, _) |- _ => inverts H end.
   eapply good_task_htistep_preserve; eauto.
- (* hswi_step *)
   match goal with H: nabt _  |- _ => rename H into Hnabt end.
   match goal with H: get T _ = _  |- _ => rename H into Hgetc end.
   match goal with H: get _ curtid = _  |- _ => rename H into Hgett end.
   match goal with H: (_, _) = (_, _) |- _ => inverts H end.
   lets Hgt': Hgt Hgetc.
   destruct Hgt' as (Heval &Hks).
   introv Hgetc'.
   destruct c as (c0 & (ke0 & ks0)).
   casetac t t0 Heq Hneq.
    2:{ rewrite set_a_get_a' in Hgetc'; auto.
          eapply Hgt; eauto. }
   subst.
   rewrite set_a_get_a in Hgetc'.
   inverts Hgetc'.
   simpl in Heval.
   simpl.
   split; auto.
   destruct Heval as [Hapi | [Hint | [Hend | Habt]]];
   [ | | simpljoin; tryfalse | tryfalse ].
   destruct Hapi as (fid & acode & ft & vl & Hapi & Hin).
   eapply api_spec_step_succs_preserve with (cd' := s) in Hin; eauto.
   2:{ eapply spec_seq_step_end.
          eapply spec_sched_step with (O:= set O curtid (oscurt t')) (t:= t').
          rewrite set_a_get_a; auto.
          unfold get_hprio_d in *.
          simpljoin.
          rewrite set_a_get_a'.
          rewrite set_a_get_a'.
          repeat eexists; eauto.
          introv Hf; tryfalse.
          introv Hf; tryfalse.
          eapply map_join_emp.
      }
    unfolds.
    destruct Hin as [ | [ | ]]; eauto.
    left; repeat eexists; eauto.
    destruct Hint as (hid & icode & Hint & Hin).
   eapply int_spec_step_succs_preserve with (cd' := s) in Hin; eauto.
   2:{ eapply spec_seq_step_end.
          eapply spec_sched_step with (O:= set O curtid (oscurt t')) (t:= t').
          rewrite set_a_get_a; auto.
          unfold get_hprio_d in *.
          simpljoin.
          rewrite set_a_get_a'.
          rewrite set_a_get_a'.
          repeat eexists; eauto.
          introv Hf; tryfalse.
          introv Hf; tryfalse.
          eapply map_join_emp.
      }
    unfolds.
    destruct Hin as [ | [ | ]]; eauto.
    right; left; repeat eexists; eauto.
Qed.

Lemma hpstepstar_goodcode_h:
  forall pc T cst O T' cst' O',
    hpstepokstar (pc,os_spec) T cst O T' cst' O' ->
    good_task_code T ->
    good_client_code pc ->
    good_task_code T'.
Proof.
do 7 intro.
introv Hstep.
inductions Hstep; intros.
auto.
eapply IHHstep; eauto.
eapply hpstep_goodcode_h; eauto.
Qed.

Lemma reachable_good_tasks:
forall cliprogs T cst O,
  good_client_code cliprogs ->
  reachable (cliprogs, os_spec) T cst O ->
  good_task_code T.
Proof.
introv Hgc Hr.
destruct Hr as (pu & spc & Heq & Hr).
inverts Heq.
destruct Hr as (T0 & cst0 & O0 & Hinit & Hstep).
lets Hgt: init_good_tasks Hinit Hgc.
eapply hpstepstar_goodcode_h; eauto.
Qed.

