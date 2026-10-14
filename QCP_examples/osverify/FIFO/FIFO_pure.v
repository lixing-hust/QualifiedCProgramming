Require Import log_code_defs.
Require Import log_code_notations.

Open Scope type_scope.
Open Scope list_scope.


Require Import FIFO_inv_and_init.
Require Import FIFO_spec. 
(* Require Import FIFO_succ.  *)

Require Import seplog_tactics.
Import DeprecatedTactic.

Require Import auxdef.
Require Import join_lib.
Require Import Lia.

Lemma nth_error_single:
  forall A n (v:A) d ,
  nth_error ( v :: nil ) n = Some d ->
  n = O /\ d = v.
Proof.
  induction n.
  simpl.
  intros. 
  inverts H. auto.
  
  simpl.
  rewrite nth_error_nil.
  intros. tryfalse.
Qed.

Lemma nth_error_app_eq : forall A (l1 l2 : list A) (n : nat) x,
  nth_error (l1 ++ l2) n = Some x ->
  (n < length l1 /\ nth_error l1 n = Some x) \/ (n >= length l1 /\ nth_error l2 (n - length l1) = Some x).
Proof.
  intros A l1 l2 n x H.
  assert ( n < length l1  \/ n >= length l1 ).
  apply Nat.lt_ge_cases.
  destruct H0 as [H1 | H2].
  - left. split. apply H1. rewrite <- H. symmetry. apply nth_error_app1. congruence.
  - right. split. apply H2. rewrite <- H. symmetry. apply nth_error_app2. auto.
Qed.


Lemma nth_error_app_right : forall A (l1 l2 : list A) n x,
  nth_error (l1 ++ l2) n = Some x ->
  n >= length l1 ->
  nth_error l2 (n - length l1) = Some x.
Proof.
  intros A l1 l2 n x H Hn.
  rewrite nth_error_app2 in H by lia. auto.
Qed.
Lemma nth_error_app_left : forall A (l1 l2 : list A) n x,
  nth_error (l1 ++ l2) n = Some x ->
  n < length l1 ->
  nth_error l1 n = Some x.
Proof.
  intros A l1 l2 n x H Hn.
  rewrite nth_error_app1 in H by lia.
  assumption.
Qed.


Lemma fifo_cre:
  forall log x eid,
  FIFO log x->
  FIFO (log ++ (creque eid::nil)) x.
Proof.
 intros log x eid H_fifo.
  unfold FIFO in *.
  intros i1 i2 m1 m2 cnt1 cnt2 H_nth1 H_nth2 H_lt.
  
  lets HH : H_nth1.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H.
  destruct (i1 - length log) in H0.
  simpl in H0. tryfalse.
  inverts H0. 
  rewrite nth_error_nil in H2.
  inverts H2. }
  destruct H.
  
  lets HH : H_nth2.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H1.
  destruct (i2 - length log) in H2.
  simpl in H2. tryfalse.
  inverts H2. 
  rewrite nth_error_nil in H4.
  inverts H4. }
  destruct H1.
  specialize (H_fifo i1 i2 m1 m2 cnt1 cnt2 ).
  apply H_fifo in H_lt;auto.
Qed.

Lemma fifo_del:
  forall log x eid,
  FIFO log x->
  FIFO (log ++ (delque eid::nil)) x.
Proof.
 intros log x eid H_fifo.
  unfold FIFO in *.
  intros i1 i2 m1 m2 cnt1 cnt2 H_nth1 H_nth2 H_lt.
  
  lets HH : H_nth1.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H.
  destruct (i1 - length log) in H0.
  simpl in H0. tryfalse.
  inverts H0. 
  rewrite nth_error_nil in H2.
  inverts H2. }
  destruct H.
  
  lets HH : H_nth2.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H1.
  destruct (i2 - length log) in H2.
  simpl in H2. tryfalse.
  inverts H2. 
  rewrite nth_error_nil in H4.
  inverts H4. }
  destruct H1.
  specialize (H_fifo i1 i2 m1 m2 cnt1 cnt2 ).
  apply H_fifo in H_lt;auto.
Qed.

Lemma fifo_en:
  forall log x eid msg cnt,
  FIFO log x->
  FIFO (log ++ (enque eid msg cnt) ::nil) x.
Proof.
 intros log x eid msg cnt H_fifo.
  unfold FIFO in *.
  intros  i1 i2 m1 m2 cnt1 cnt2 H_nth1 H_nth2 H_lt.
  
  lets HH : H_nth1.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H.
  destruct (i1 - length log) in H0.
  simpl in H0. tryfalse.
  inverts H0. 
  rewrite nth_error_nil in H2.
  inverts H2. }
  destruct H.
  
  lets HH : H_nth2.
  apply nth_error_app_eq in HH.
  destruct HH.
  2:{ 
  destruct H1.
  destruct (i2 - length log) in H2.
  simpl in H2. tryfalse.
  inverts H2. 
  rewrite nth_error_nil in H4.
  inverts H4. }
  destruct H1.
  specialize (H_fifo i1 i2 m1 m2 cnt1 cnt2 ).
  apply H_fifo in H_lt;auto.
Qed.

  
Ltac unfolddef:=
  try
    (unfold code in *;unfold cont in *;unfold tid in *;unfold TMSpecMod.B in *;
     unfold mmapspec.image in *;
     unfold TOSpecMod.B in *;
     unfold omapspec.image in *;unfold Maps.sub in *;unfold disjoint in *;unfold osabst in *).
     

Lemma join_get_set_eq:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    join (set O1 a b') O2 O' ->
    O' = set O a b'.
  intros.
  assert (join (set O1 a b') O2 (set O a b')).
  {
    clear H2.
    geat.
  }
  eapply map_join_deter; eauto.
Qed.

Lemma join_get_set_eq_2:
  forall (A B T:Type) (X:PermMap A B T) O1 O2 O O' a b b' a' c c',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c -> 
    join (set (set O1 a b') a' c') O2 O' ->
    O' = set (set O a b') a' c'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.

Lemma join_get_set_eq_3
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' d d',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    join (set ((set (set O1 a b') a' c')) a'' d') O2 O' -> O' = set (set (set O a b') a' c') a'' d'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed. 

Lemma join_get_set_eq_4
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' d d' a''' e e',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    get O1 a''' = Some e ->
    join (set (set (set (set O1 a b') a' c') a'' d') a''' e') O2 O' -> O' = set (set (set (set O a b') a' c') a'' d') a''' e'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed. 

Lemma join_get_set_eq_5
: forall (A B T : Type) (X : PermMap A B T) (O1 O2 O O' : T) 
         (a : A) (b b' : B) (a' : A) (c c' : B) a'' d d' a''' e e' a'''' f f',
    usePerm = false ->
    join O1 O2 O ->
    get O1 a = Some b ->
    get O1 a' = Some c ->
    get O1 a'' = Some d ->
    get O1 a''' = Some e ->
    get O1 a'''' = Some f ->
    join (set (set (set (set (set O1 a b') a' c') a'' d') a''' e') a'''' f') O2 O' -> O' = set (set (set (set (set O a b') a' c') a'' d') a''' e') a'''' f'.
  intros.
  Ltac infer ::= infer_v.
  hy.
  Ltac infer ::= infer_q.
Qed.
  

  
