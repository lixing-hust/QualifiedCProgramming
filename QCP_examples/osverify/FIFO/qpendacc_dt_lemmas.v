
Require Import FIFO_sys.
(* Require Import PIF_succs. *)
Require Import FIFO_spec.
Require Import log_language.
Require Import List.
Require Import log_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import FIFO_inv_and_init.

Open Scope nat_scope.
Require Import base_tac. 
Require Import Integers.

Require Import mq_succ_gen. 
Require Import fifo_tacs. 

Open Scope int_scope.

Require Import seplog_lemmas.
Require Import fifo_lemmas. 

Require Import protect. 
Require Import join_lib.

Require Import FIFO_pure. 

Lemma fifo_ext_qpend_get_no_pwl_succ_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x3 : EcbMod.map)
    (x5 : msg)
    (x6 : list (msg * nat))
    (x7 : maxlen)
    (x8 : waitset)
    (x10 : list act)
    (x12 : nat)
    (H8 : join
            (set (set O loglsid (oslog (x10 ++ deque x x5 x12 :: nil))) absecblsid
               (absecblist (set x3 x (absmsgq x6 x7 nil, x8)))) Of O'')
    (x0 : val)
    (x2 : addrval)
    (x4 : TcbMod.map)
    (H1 : get O curtid = Some (oscurt x2))
    (H2 : get O absecblsid = Some (absecblist x3))
    (H3 : get O abtcblsid = Some (abstcblist x4))
    (H4 : get x3 x = Some (absmsgq ((x5, x12) :: x6) x7 nil, x8))
    (H5 : get O loglsid = Some (oslog x10))
    (Heqv : x0 = x5),

    FIFO_ext O''. 
Proof.
  intros. 
  assert (get O' loglsid = Some (oslog x10)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x3)) as Hecbls.
  eapply join_get_get_l;eauto. 
  lets Heq : H8 .
  eapply  join_get_set_eq_2 in Heq;eauto.
  subst.

  unfold FIFO_ext in *.
  rename H0 into Hext.
  rewrite map_get_set'; auto.

  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'. 
  rewrite map_get_set in Hget_e; eauto.
  do 2 rewrite map_get_set' in Hget_c; eauto.
  inverts Hget_e. 

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x0) x1. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (Hnth1': forall j : nat,nth_error l2' j <> Some (creque eid)).
  { introv Hf.
    eapply Hnth1.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  assert (Hnth2': forall j : nat,nth_error l2' j <> Some (delque eid)).
  { introv Hf.
    eapply Hnth2.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }

  assert (He:eid = x \/ eid <> x) by tauto.
  destruct He;subst.
  (* eid = x *)
  {
    lets Hext': Hnth1'.
    eapply Hext in Hext';eauto.
    rewrite EcbMod.map_get_set in Hget_ecb; eauto.
    inverts Hget_ecb.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre &Hfifo).
    splits;auto.
    (*subgoals - is_inc*) 
    unfold is_inc in *.
    intros i1 i2 m1 m2 cnt cnt' Hn1 Hn2 Hi.
    eapply Hisinc with (i1:= S i1) (i2:= S i2);eauto.
    auto with zarith.

    (*subgoals - lt_cnt_log_que*)
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    unfold is_inc in *.
    assert (Hlt: (x12 < cnt')%nat).
    { eapply Hisinc with (i1 := 0) (i2 := (S j)%nat) ;eauto.
      simpl;eauto.
      auto with zarith.
    }
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    destruct Hn1 as (Hlt' & Hn1).
    eapply Hltlogq with (j := S j) ;eauto.
    destruct Hn1 as (Hlt' & Hn1).
    eapply nth_error_single in Hn1.
    destruct Hn1 as ( _ & Heq).
    inverts Heq;auto.
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    eapply Hltqcmp with (i := S i);eauto.
    
    (*subgoals - lt_cnt_log_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    unfold lt_cnt_que_cmp in*.
    assert (Hlt: (x12 < cnt')%nat).
    { eapply Hltqcmp with (i:= 0)  ;eauto.
      simpl;eauto.
    }
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'];
      [destruct Hnth' as (Hlt' & Hnth');
       eapply Hltlogcmp in Hget'; eauto
      |
        destruct Hnth' as (Hlt' & Hnth');
        eapply nth_error_single in Hnth';
        destruct Hnth' as (Hi1 & Hnth');
        inverts Hnth';auto
      ].

    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.

    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    specialize Hnde with (j:= length l2') (m := x5) (cnt:= x12).
    assert (Hlengthl2': (length l2')<=(length l2')) by auto.
    eapply nth_error_app2  in Hlengthl2' .
    rewrite Hlengthl2' in Hnde. 
    rewrite Nat.sub_diag in Hnde.
    simpl in Hnde.
    tryfalse.
    (*Hbackward*)
    introv Hinitq.
    destruct Hinitq as (Hgetcmp & Hms).
    unfold lt_cnt_que_cmp in*.
    eapply Hltqcmp with (m:= x5)(cnt:= x12) in Hgetcmp.
    2:{  instantiate (1:= 0). auto. }
    unfold lt_cnt_log_cmp in*.
    inverts Hgetcmp.
    
    (*FIFO*)
    unfold FIFO in *.
    intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    2:{
      destruct Hn1 as (Hlt' & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as ( Hi1 & Heq).
      lets Hi2: nth_error_Some i2.
      rewrite  Hn2 in Hi2.
      rewrite last_length in Hi2.
      assert (Hi2s: i2 < S (length l2')  ).
      {  rewrite <- Hi2;  auto.  }
      false.
      auto with zarith.
    }
    destruct Hn1 as (Hlt' & Hn1).
    
    eapply nth_error_app_eq in Hn2;eauto.
    destruct Hn2 as [Hn2 | Hn2].
    destruct Hn2 as (Hlt2' & Hn2).
    eapply Hfifo;eauto.

    destruct Hn2 as (Hlt2' & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2' & Hn2);inverts Hn2.
    eapply Hltlogq with (i:= i1 ) (j := 0);eauto.
    instantiate (1:= x5).
    auto.
  }

  (*eid <> x*)
  {
    lets Hext': Hnth1'.
    rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
    eapply Hext in Hext';eauto.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
    splits;auto.

    (*subgoals - lt_cnt_log_que*)
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (Hlt & Hn1).
    eapply Hltlogq in Hn1;eauto.
    
    (*subgoals - lt_cnt_log_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (Hlt & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      tryfalse.
    }
    destruct Hnth' as (Hlt & Hnth').
    eapply Hltlogcmp;eauto.
    
    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.
    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    assert (Hndel' : forall j : nat, nth_error l2' j <> Some (delque eid)).
    {
      clear- Hndel.
      intros j Hf.
      eapply Hndel.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (Hnen' : forall j m cnt, nth_error l2' j <> Some (enque eid m cnt)).
    {
      clear- Hnen.
      intros j m cnt Hf.
      eapply Hnen.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (Hnde' : forall j m cnt, nth_error l2' j <> Some (deque eid m cnt)).
    {
      clear- Hnde.
      intros j m cnt Hf.
      eapply Hnde.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    eapply Hforward ;auto.
    (*Hbackward*)
    introv Hinitq.
    eapply Hbackward in Hinitq;eauto.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    splits;auto.
    intros.
    introv Hfalse.
    eapply nth_error_app_eq in Hfalse.
    destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
    specialize Hnen with (j:=j)(m:=m)(cnt:= cnt).
    tryfalse.
    destruct (j - length l2') in Hfalse.
    simpl in Hfalse; tryfalse.
    inverts Hfalse. 
    rewrite nth_error_nil in *.
    tryfalse.
    
    intros.
    introv Hfalse.
    eapply nth_error_app_eq in Hfalse.
    destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
    specialize Hnde with (j:=j)(m:=m)(cnt:= cnt).
    tryfalse.
    destruct (j - length l2') in Hfalse.
    simpl in Hfalse; tryfalse.
    inverts Hfalse. 
    rewrite nth_error_nil in *.
    tryfalse.
    (*FIFO*)
    unfold FIFO in *.
    intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (Hlt & Hn1).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    2:{ (*false*)
      destruct Hn2 as (Hlt' & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hi2 & Hn2).
      tryfalse.
    }
    destruct Hn2 as (Hlt2 & Hn2).
    eapply Hfifo ;eauto.
  }
Qed.

Lemma fifo_ext_qpend_expwl_before_sched_preserved: 
  forall
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : TcbMod.map)
    (x4 : msg)
    (x5 : list (msg * nat))
    (x6 : maxlen)
    (x7 : list tid)
    (x8 : waitset)
    (x9 : priority)
    (x12 : msg)
    (x13 : tid)
    (x15 : susstatus)
    (x16 x17 : nat) 
    (x20 : list act)
    (x22 : MqcntMod.map)
    (H8 : join
            (set
               (set
                  (set (set O loglsid (oslog (x20 ++ deque x x4 x16 :: enque x x12 x17 :: nil))) mqcntid
                     (mqcnt (set x22 x (x17 + 1)%nat))) abtcblsid
                  (abstcblist (set x3 x13 (x9, rdy, x12, x15)))) absecblsid
               (absecblist (set x2 x (absmsgq (x5 ++ (x12, x17) :: nil) x6 (remove_tid x13 x7), x8)))) Of
            O'')
    (x0 : val)
    (x14 : taskstatus)
    (H1 : get O absecblsid = Some (absecblist x2))
    (H2 : get O abtcblsid = Some (abstcblist x3))
    (H3 : x7 <> nil)
    (H4 : get x2 x = Some (absmsgq ((x4, x16) :: x5) x6 x7, x8))
    (H6 : GetHWait x3 x7 x13)
    (H9 : get x3 x13 = Some (x9, x14, x12, x15))
    (H11 : get O loglsid = Some (oslog x20))
    (H13 : get O mqcntid = Some (mqcnt x22))
    (H14 : get x22 x = Some x17)
    (Heqv : x0 = x4), 

    FIFO_ext O''.
Proof.
  intros.
  assert (get O' loglsid = Some (oslog x20)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x2)) as Hecbls.
  eapply join_get_get_l;eauto.
  assert (get O' abtcblsid = Some (abstcblist x3)) as Htcbls.
  eapply join_get_get_l;eauto.
  assert (get O' mqcntid = Some (mqcnt x22)) as Hmqcnt.
  eapply join_get_get_l;eauto.
  lets Heq : H8 .
  eapply  join_get_set_eq_4 in Heq;eauto.
  subst.

  unfold FIFO_ext in *.
  rename H0 into Hext.

  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  rewrite map_get_set' in Hget'; eauto.
  rewrite map_get_set' in Hget'; eauto.
  rewrite map_get_set' in Hget'; eauto.
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'. 
  rewrite map_get_set in Hget_e; eauto.
  rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set in Hget_c; eauto.
  inverts Hget_e. 
  inverts Hget_c.

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x0) x1. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  change (x20 ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (x20 ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)) in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  change (x20 ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (x20 ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)) in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (Hl2': forall l2': list act, l2' = nil \/ (exists l2'' v, l2' = l2'' ++ (v::nil))).
  { induction l2'0. auto.
    right.
    destruct IHl2'0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x0) x1. simpl; auto.
  }
  specialize Hl2' with (l2':= l2').
  destruct Hl2' as [ Heq | (l2'' & v & Heq)]; subst l2'.
  rewrite app_inj_tail_iff in Hlog'.
  destruct Hlog' as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in Hlog'.
  rewrite app_assoc in Hlog'.
  rewrite app_inj_tail_iff in Hlog'.
  destruct Hlog' as (Hlog' & Heq); subst v.
  rewrite app_assoc_reverse in *.

  assert (Hnth1': forall j : nat,nth_error l2'' j <> Some (creque eid)).
  { introv Hf.
    eapply Hnth1.
    lets Hlen: nth_error_Some l2'' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  assert (Hnth2': forall j : nat,nth_error l2'' j <> Some (delque eid)).
  { introv Hf.
    eapply Hnth2.
    lets Hlen: nth_error_Some l2'' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }

  assert (He:eid = x \/ eid <> x) by tauto.
  destruct He;subst.
  (* eid = x *)
  {
    lets Hext': Hnth1'.
    eapply Hext in Hext';eauto.
    rewrite EcbMod.map_get_set in Hget_ecb; eauto.
    inverts Hget_ecb.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
    splits;auto.
    (*subgoals - is_inc*) 
    unfold is_inc in *.
    intros i1 i2 m1 m2 cnt cnt' Hn1 Hn2 Hi.
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    2:{
      destruct Hn1 as (Hlt' & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as ( Hi1 & Heq).
      lets Hi2: nth_error_Some i2.
      rewrite  Hn2 in Hi2.
      rewrite last_length in Hi2.
      assert (Hi2s: i2 < S (length x5)  ).
      {  rewrite <- Hi2.
         auto.
      }
      false.
      auto with zarith.
    }
    destruct Hn1 as (Hlt' & Hn1).
    eapply nth_error_app_eq in Hn2;eauto.
    destruct Hn2 as [Hn2 | Hn2].
    destruct Hn2 as (Hlt2' & Hn2).
    eapply Hisinc with (i1:= S i1) (i2:= S i2);eauto.
    auto with zarith.
    destruct Hn2 as (Hlt2' & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2' & Hn2);inverts Hn2.
    eapply Hltqcmp with (i:= S i1 );eauto.
    
    (*subgoals - lt_cnt_log_que*)
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)) in Hn1.
    rewrite app_assoc in Hn1.
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (_ & Hn1).
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    (*in l2''*)
    {
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_app_eq in Hn2;eauto.
      destruct Hn2 as [Hn2 | Hn2].
      (*in x5*)
      destruct Hn2 as (Hlt2 & Hn2).
      eapply Hltlogq with (i := i) (j:= (S j)%nat );eauto.
      (*not in x5*)
      destruct Hn2 as (Hi2 & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hlt2 & Hn2).
      inverts Hn2.
      eapply Hltlogcmp ;eauto.
    }
    (*not in l2''*)
    {
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      inverts Hn1.
      eapply nth_error_app_eq in Hn2;eauto.
      destruct Hn2 as [Hn2 | Hn2].
      (*in x5*)
      destruct Hn2 as (Hlt2 & Hn2).
      eapply Hisinc with (i1 := 0) (i2:= (S j)%nat );eauto.
      simpl;eauto.
      auto with zarith.
      (*not in x5*)
      destruct Hn2 as (Hi2 & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hlt2 & Hn2).
      inverts Hn2.
      eapply Hltqcmp with (i := 0) ;eauto.
      simpl;eauto.
    }
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    rewrite map_get_set in Hget'; eauto.
    inverts Hget'.
    
    eapply nth_error_app_eq in Hnth';eauto.
    destruct Hnth' as [Hnth' | Hnth'].
    {
      destruct Hnth' as (_ & Hnth').
      eapply Hltqcmp with (i := (S i)) in H14;eauto.
      auto with zarith.
    }
    { 
      destruct Hnth' as (Hlt & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (_ & Hnth').
      inverts Hnth'.
      auto with zarith.
    }
    
    (*subgoals - lt_cnt_log_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)) in Hnth'.
    rewrite app_assoc in Hnth'.
    eapply nth_error_app_eq in Hnth';eauto.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (Hlt & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      tryfalse.
    }
    destruct Hnth' as (_ & Hnth').
    eapply nth_error_app_eq in Hnth';eauto.
    destruct Hnth' as [Hnth' | Hnth'].
    (*in l2''*)
    {
      destruct Hnth' as (Hlt & Hnth').
      rewrite map_get_set in Hget'; eauto.
      inverts Hget'.
      eapply Hltlogcmp with (i := i ) in H14;eauto.
      auto with zarith.
    }
    (*not in l2''*)
    {
      destruct Hnth' as (_ & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (_ & Hnth').
      inverts Hnth'.
      assert (x16 < x17).
      eapply Hltqcmp with (i := 0) ;eauto.
      simpl;auto.
      rewrite map_get_set in Hget'; eauto.
      inverts Hget'.
      auto with zarith.
    }
    
    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.
    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)).
    rewrite app_assoc .
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    specialize Hnen with (j:= length (l2'' ++ deque x x4 x16 :: nil)) (m := x12) (cnt:= x17).
    assert (Hlengthl2'': (length (l2'' ++ deque x x4 x16 :: nil) <=(length (l2'' ++ deque x x4 x16 :: nil)))) by auto.
    eapply nth_error_app2  in Hlengthl2'' .
    rewrite Hlengthl2'' in Hnen. 
    rewrite Nat.sub_diag in Hnen.
    simpl in Hnen.
    tryfalse.
    (*Hbackward*)
    introv Hinitq.
    destruct Hinitq as (Hgetcmp & Hms).
    destruct x5 in Hms;tryfalse.

    (*FIFO*)
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)).
    rewrite app_assoc .
    unfold FIFO in *.
    intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (_ & Hn1).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    2:{ (*false*)
      destruct Hn2 as (Hlt' & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hi2 & Hn2).
      tryfalse.
    }
    destruct Hn2 as (_ & Hn2).
    
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    2:{
      destruct Hn1 as (Hlt' & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as ( Hi1 & Heq).
      lets Hi2: nth_error_Some i2.
      rewrite  Hn2 in Hi2.
      rewrite last_length in Hi2.
      assert (Hi2s: i2 < S (length l2'')  ).
      {  rewrite <- Hi2;  auto.  }
      false.
      auto with zarith.
    }
    destruct Hn1 as (Hlt' & Hn1).
    
    eapply nth_error_app_eq in Hn2;eauto.
    destruct Hn2 as [Hn2 | Hn2].
    (*in l2''*)
    destruct Hn2 as (Hlt2' & Hn2).
    eapply Hfifo;eauto.
    (*not in l2''*)
    destruct Hn2 as (Hlt2' & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2' & Hn2);inverts Hn2.
    eapply Hltlogq with (i:= i1 ) (j := 0);eauto.
    instantiate (1:= x4).
    auto.
  }
  
  (*eid <> x*)
  {
    lets Hext': Hnth1'.
    rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
    eapply Hext in Hext';eauto.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
    
    splits;auto.

    (*subgoals - lt_cnt_log_que*)
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)).
    rewrite app_assoc .
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (_ & Hn1).
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (_ & Hn1).
    
    eapply Hltlogq in Hn1;eauto.
    
    (*lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    intros.
    rewrite map_get_set' in H5;eauto.
    
    (*subgoals - lt_cnt_log_cmp*)
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)).
    rewrite app_assoc .
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (_ & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      tryfalse.
    }
    destruct Hnth' as (_ & Hnth').
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (_ & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      tryfalse.
    }
    destruct Hnth' as (_ & Hnth').
    rewrite map_get_set' in Hget';eauto.
    
    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.
    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).

    assert (Hnen' : forall j m cnt, nth_error l2'' j <> Some (enque eid m cnt)).
    {
      clear- Hnen.
      intros j m cnt Hf.
      eapply Hnen.
      lets Hlen: nth_error_Some l2'' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (Hnde' : forall j m cnt, nth_error l2'' j <> Some (deque eid m cnt)).
    {
      clear- Hnde.
      intros j m cnt Hf.
      eapply Hnde.
      lets Hlen: nth_error_Some l2'' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    rewrite map_get_set' ;eauto.

    (*Hbackward*)
    introv Hinitq.
    rewrite map_get_set' in Hinitq ;eauto.
    eapply Hbackward in Hinitq;eauto.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    splits;auto.
    intros.
    introv Hfalse.
    eapply nth_error_app_eq in Hfalse.
    destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
    specialize Hnen with (j:=j)(m:=m)(cnt:= cnt).
    tryfalse.
    destruct (j - length l2'') in Hfalse.
    simpl in Hfalse; tryfalse.
    inverts Hfalse. 
    eapply nth_error_single in H5.
    destruct H5 as (_ & H5).
    tryfalse.
    
    intros.
    introv Hfalse.
    eapply nth_error_app_eq in Hfalse.
    destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
    specialize Hnde with (j:=j)(m:=m)(cnt:= cnt).
    tryfalse.
    destruct (j - length l2'') in Hfalse.
    simpl in Hfalse; tryfalse.
    inverts Hfalse.
    eapply nth_error_single in H5.
    destruct H5 as (_ & H5).
    tryfalse.
    
    (*FIFO*)
    change (l2'' ++ deque x x4 x16 :: enque x x12 x17 :: nil) with (l2'' ++ (deque x x4 x16 :: nil)++ (enque x x12 x17 :: nil)).
    rewrite app_assoc .
    unfold FIFO in *.
    intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (_ & Hn1).
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (_ & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      tryfalse.
    }
    destruct Hn1 as (Hlt & Hn1).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    2:{ (*false*)
      destruct Hn2 as (_ & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hi2 & Hn2).
      tryfalse.
    }
    destruct Hn2 as (Hlt2 & Hn2).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    2:{ (*false*)
      destruct Hn2 as (Hlt' & Hn2).
      eapply nth_error_single in Hn2.
      destruct Hn2 as (Hi2 & Hn2).
      tryfalse.
    }
    destruct Hn2 as (_ & Hn2).
    eapply Hfifo ;eauto.
  }
Qed.    

Lemma fifo_ext_qpend_block_preserved: 
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : msg)
    (x3 : TcbMod.map)
    (x5 : EcbMod.map)
    (x7 : list addrval)
    (x8 : priority)
    (x10 : maxlen)
    (x11 : addrval)
    (x12 : option int32)
    (x13 : list tid)
    (x14 : susstatus)
    (H8 : join
            (set (set O abtcblsid (abstcblist (set x3 x11 (x8, wait (os_stat_q x) x12, x2, x14))))
               absecblsid (absecblist (set x5 x (absmsgq nil x10 x13, x11 :: x7)))) Of O'')
    (x0 : int32)
    (x9 : taskstatus)
    (H1 : get O curtid = Some (oscurt x11))
    (H2 : get O absecblsid = Some (absecblist x5))
    (H3 : get x5 x = Some (absmsgq nil x10 x13, x7))
    (H5 : get O abtcblsid = Some (abstcblist x3))
    (H6 : get x3 x11 = Some (x8, x9, x2, x14))
    (H9 : x0 <> Int.zero /\ x12 = Some x0 \/ x0 = Int.zero /\ x12 = None), 

    FIFO_ext O''.
Proof.
  intros.
  assert (get O' absecblsid = Some (absecblist x5)) as Hecbls.
  eapply join_get_get_l;eauto. 
  lets Heq : H8 .
  eapply  join_get_set_eq_2 in Heq;eauto.
  subst.
  
  unfold FIFO_ext in *.
  rename H0 into Hext.

  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  rewrite map_get_set' in Hget;auto.
  rewrite map_get_set' in Hget;auto.
  
  rewrite map_get_set in Hget_e; auto.
  inverts Hget_e.
  do 2 rewrite map_get_set' in Hget_c; auto.
  assert (He:eid = x \/ eid <> x)by tauto.
  destruct He;subst.
  (*eid = x*)
  eapply Hext in H3;eauto.
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  eauto.
  (*eid <> x*)
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
Qed.   

Lemma fifo_ext_qpend_to_preserved:
  forall
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : TcbMod.map)
    (x3 : priority)
    (x4 : addrval)
    (x6 : EcbMod.map)
    (x8 : list ms)
    (x9 : maxlen)
    (x10 : list tid)
    (x11 : list addrval)
    (x12 : susstatus)
    (H8 : join
            (set (set O abtcblsid (abstcblist (set x2 x4 (x3, rdy, Vnull, x12)))) absecblsid
               (absecblist (set x6 x (absmsgq x8 x9 x10, remove_tid x4 x11)))) Of O'')
    (x0 : val)
    (H1 : get O curtid = Some (oscurt x4))
    (H2 : get O abtcblsid = Some (abstcblist x2))
    (H3 : get x2 x4 = Some (x3, wait (os_stat_q x) (Some Int.zero), Vnull, x12))
    (H5 : get O absecblsid = Some (absecblist x6))
    (H6 : get x6 x = Some (absmsgq x8 x9 x10, x11))
    (H9 : In x4 x11)
    (Heqv : x0 = Vnull), 

    FIFO_ext O''. 
Proof.
  intros.
  assert (get O' absecblsid = Some (absecblist x6)) as Hecbls.
  eapply join_get_get_l;eauto. 
  lets Heq : H8 .
  eapply  join_get_set_eq_2 in Heq;eauto.
  subst.
  
  unfold FIFO_ext in *.
  rename H0 into Hext.
  
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  do 2 rewrite map_get_set' in Hget;auto.
  rewrite map_get_set in Hget_e; auto.
  inverts Hget_e.
  do 2 rewrite map_get_set' in Hget_c; auto.
  assert (He:eid = x \/ eid <> x)by tauto.
  destruct He;subst.
  (*eid = x*)
  eapply Hext in H6;eauto.
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  eauto.
  (*eid <> x*)
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
Qed.

Lemma fifo_ext_qacc_succ_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : EcbMod.map)
    (x3 : msg)
    (x4 : list (msg * nat))
    (x5 : maxlen)
    (x6 : list tid)
    (x7 : waitset)
    (x8 : list act)
    (x10 : nat)
    (H8 : join
            (set (set O loglsid (oslog (x8 ++ deque x x3 x10 :: nil))) absecblsid
               (absecblist (set x2 x (absmsgq x4 x5 x6, x7)))) Of O'')
    (x0 : val)
    (H2 : get O absecblsid = Some (absecblist x2))
    (H3 : get x2 x = Some (absmsgq ((x3, x10) :: x4) x5 x6, x7))
    (H4 : get O loglsid = Some (oslog x8))
    (Heqv : x0 = x3),
    FIFO_ext O''. 
Proof.
  intros.
  assert (get O' loglsid = Some (oslog x8)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x2)) as Hecbls.
  eapply join_get_get_l;eauto. 
  lets Heq : H8 .
  eapply  join_get_set_eq_2 in Heq;eauto.
  subst.

  unfold FIFO_ext in *.
  rename H0 into Hext.
  rewrite map_get_set'; auto.


  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'. 
  (*  rewrite map_get_set' in Hget_e; eauto. *)
  rewrite map_get_set in Hget_e; eauto.
  do 2 rewrite map_get_set' in Hget_c; eauto.
  (*   rewrite map_get_set' in Hget_c; eauto. *)
  inverts Hget_e. 
  (*   inverts Hget_c. *)

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x0) x1. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (Hnth1': forall j : nat,nth_error l2' j <> Some (creque eid)).
  { introv Hf.
    eapply Hnth1.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  assert (Hnth2': forall j : nat,nth_error l2' j <> Some (delque eid)).
  { introv Hf.
    eapply Hnth2.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }

  assert (He:eid = x \/ eid <> x) by tauto.
  destruct He;subst.
  (* eid = x *)
  {
    lets Hext': Hnth1'.
    eapply Hext in Hext';eauto.
    rewrite EcbMod.map_get_set in Hget_ecb; eauto.
    inverts Hget_ecb.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
    splits;auto.
    (*subgoals - is_inc*) 
    unfold is_inc in *.
    intros i1 i2 m1 m2 cnt cnt' Hn1 Hn2 Hi.
    eapply Hisinc with (i1:= S i1) (i2:= S i2);eauto.
    auto with zarith.

    (*subgoals - lt_cnt_log_que*)
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    unfold is_inc in *.
    assert (Hlt: (x10 < cnt')%nat).
    { eapply Hisinc with (i1 := 0) (i2 := (S j)%nat) ;eauto.
      simpl;eauto.
      auto with zarith.
    }
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    destruct Hn1 as (Hlt' & Hn1).
    eapply Hltlogq with (j := S j) ;eauto.
    destruct Hn1 as (Hlt' & Hn1).
    eapply nth_error_single in Hn1.
    destruct Hn1 as ( _ & Heq).
    inverts Heq;auto.
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    eapply Hltqcmp with (i := S i);eauto.
    
    (*subgoals - lt_cnt_log_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    unfold lt_cnt_que_cmp in*.
    assert (Hlt: (x10 < cnt')%nat).
    { eapply Hltqcmp with (i:= 0)  ;eauto.
      simpl;eauto.
    }
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'];
      [destruct Hnth' as (Hlt' & Hnth');
       eapply Hltlogcmp in Hget'; eauto
      |
        destruct Hnth' as (Hlt' & Hnth');
        eapply nth_error_single in Hnth';
        destruct Hnth' as (Hi1 & Hnth');
        inverts Hnth';auto
      ].

    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.
    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    specialize Hnde with (j:= length l2') (m := x3) (cnt:= x10).
    assert (Hlengthl2': (length l2')<=(length l2')) by auto.
    eapply nth_error_app2  in Hlengthl2' .
    rewrite Hlengthl2' in Hnde. 
    rewrite Nat.sub_diag in Hnde.
    simpl in Hnde.
    tryfalse.
    (*Hbackward*)
    introv Hinitq.
    destruct Hinitq as (Hgetcmp & Hms).
    unfold lt_cnt_que_cmp in*.
    eapply Hltqcmp with (m:= x3)(cnt:= x10) in Hgetcmp.
    2:{  instantiate (1:= 0). auto. }
    unfold lt_cnt_log_cmp in*.
    inverts Hgetcmp.
    
    (*FIFO*)
    unfold FIFO in *.
    intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
    eapply nth_error_app_eq in Hn1;eauto.
    destruct Hn1 as [Hn1 | Hn1].
    2:{
      destruct Hn1 as (Hlt' & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as ( Hi1 & Heq).
      lets Hi2: nth_error_Some i2.
      rewrite  Hn2 in Hi2.
      rewrite last_length in Hi2.
      assert (Hi2s: i2 < S (length l2')  ).
      {  rewrite <- Hi2;  auto.  }
      false.
      auto with zarith.
    }
    destruct Hn1 as (Hlt' & Hn1).
    
    eapply nth_error_app_eq in Hn2;eauto.
    destruct Hn2 as [Hn2 | Hn2].
    destruct Hn2 as (Hlt2' & Hn2).
    eapply Hfifo;eauto.

    destruct Hn2 as (Hlt2' & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2' & Hn2);inverts Hn2.
    eapply Hltlogq with (i:= i1 ) (j := 0);eauto.
    instantiate (1:= x3).
    auto.
  }

  (*eid <> x*)
  lets Hext': Hnth1'.
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
  eapply Hext in Hext';eauto.
  destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
  splits;auto.

  (*subgoals - lt_cnt_log_que*)
  unfold lt_cnt_log_que in *.
  intros i j m m' cnt cnt' Hn1 Hn2.
  apply nth_error_app_eq in Hn1.
  destruct Hn1 as [Hn1 | Hn1].
  2:{ (*false*)
    destruct Hn1 as (Hlt & Hn1).
    eapply nth_error_single in Hn1.
    destruct Hn1 as (Hi1 & Hn1).
    tryfalse.
  }
  destruct Hn1 as (Hlt & Hn1).
  eapply Hltlogq in Hn1;eauto.
  
  (*subgoals - lt_cnt_log_cmp*)
  unfold lt_cnt_log_cmp in *.
  introv Hnth' Hget'.
  apply nth_error_app_eq in Hnth'.
  destruct Hnth' as [Hnth' | Hnth'].
  2:{ (*false*)
    destruct Hnth' as (Hlt & Hnth').
    eapply nth_error_single in Hnth'.
    destruct Hnth' as (Hi1 & Hnth').
    tryfalse.
  }
  destruct Hnth' as (Hlt & Hnth').
  eapply Hltlogcmp;eauto.
  
  (*subgoals - cre_log_cmp*)
  unfold cre_log_cmp in *.
  destruct Hcre as (Hforward & Hbackward).
  split.
  (*Hforward*)
  introv Hinitq.
  destruct Hinitq as (Hndel & Hnen & Hnde).
  assert (Hndel' : forall j : nat, nth_error l2' j <> Some (delque eid)).
  {
    clear- Hndel.
    intros j Hf.
    eapply Hndel.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  assert (Hnen' : forall j m cnt, nth_error l2' j <> Some (enque eid m cnt)).
  {
    clear- Hnen.
    intros j m cnt Hf.
    eapply Hnen.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  assert (Hnde' : forall j m cnt, nth_error l2' j <> Some (deque eid m cnt)).
  {
    clear- Hnde.
    intros j m cnt Hf.
    eapply Hnde.
    lets Hlen: nth_error_Some l2' j.
    rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
    rewrite <- Hf.
    eapply nth_error_app1; eauto.
  }
  eapply Hforward ;auto.
  (*Hbackward*)
  introv Hinitq.
  eapply Hbackward in Hinitq;eauto.
  destruct Hinitq as (Hndel & Hnen & Hnde).
  splits;auto.
  intros.
  introv Hfalse.
  eapply nth_error_app_eq in Hfalse.
  destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
  specialize Hnen with (j:=j)(m:=m)(cnt:= cnt).
  tryfalse.
  destruct (j - length l2') in Hfalse.
  simpl in Hfalse; tryfalse.
  inverts Hfalse. 
  rewrite nth_error_nil in *.
  tryfalse.
  
  intros.
  introv Hfalse.
  eapply nth_error_app_eq in Hfalse.
  destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
  specialize Hnde with (j:=j)(m:=m)(cnt:= cnt).
  tryfalse.
  destruct (j - length l2') in Hfalse.
  simpl in Hfalse; tryfalse.
  inverts Hfalse. 
  rewrite nth_error_nil in *.
  tryfalse.
  
  (*FIFO*)
  unfold FIFO in *.
  intros i1 i2 m1 m2 cnt1 cnt2 Hn1 Hn2 H_lt.
  apply nth_error_app_eq in Hn1.
  destruct Hn1 as [Hn1 | Hn1].
  2:{ (*false*)
    destruct Hn1 as (Hlt & Hn1).
    eapply nth_error_single in Hn1.
    destruct Hn1 as (Hi1 & Hn1).
    tryfalse.
  }
  destruct Hn1 as (Hlt & Hn1).
  apply nth_error_app_eq in Hn2.
  destruct Hn2 as [Hn2 | Hn2].
  2:{ (*false*)
    destruct Hn2 as (Hlt' & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2 & Hn2).
    tryfalse.
  }
  destruct Hn2 as (Hlt2 & Hn2).
  eapply Hfifo ;eauto.    
Qed.
