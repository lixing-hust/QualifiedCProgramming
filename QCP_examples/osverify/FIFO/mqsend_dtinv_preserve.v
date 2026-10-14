
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

Ltac some_none_tac Hs :=
  match Hs with
    (pnil, ?hyp) => 
      match type of hyp with
        ?P /\ ?Q => let h1 := fresh "h" in let h2 := fresh "h" in destruct hyp as (h1 & h2); some_none_tac pnil
      | ?P \/ ?Q =>
          let h1 := fresh "h" in
          let h2 := fresh "h" in
          destruct hyp as [h1 | h2];
          [some_none_tac (pnil, h1) | some_none_tac (pnil, h2)]
      | Some _ = None => solve [false]
      (* | Some _ = Some _ => inverts hyp *)
      | _ => idtac
      end
  | pnil =>
      match goal with
        h: context [Some ?t1 = None] |- _ => some_none_tac (pnil, h)
      | h: context [Some ?t1 = Some ?t2] |- _ => some_none_tac (pnil, h) 
      | h: _ |- _ => idtac
      end
  end.
  
Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); tac h1; tac h2
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.
       
Ltac symexe0 := 
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; tryfalse; some_none_tac pnil; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | H: Some _ = Some _ |- _ => inverts H; symexe0 
  | H: FIFO_ext ?O |- FIFO_ext ?O => solve[auto]
  | Hjo1: join ?O ?Of ?OO, Hjo2: join ?O ?Of ?OO' |- _ =>
      assert (OO = OO') by join auto; subst; symexe0 
  | H: _ |- _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.

Require Import FIFO_pure. 

Lemma fifo_ext_qpost_exwt_succ_preserved: 
  forall
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x0 : val)
    (x3 : EcbMod.map)
    (x4 : list tid)
    (x6 : tid)
    (x7 : TcbMod.map)
    (x10 : priority)
    (x12 : maxlen)
    (x13 : list tid)
    (x14 : susstatus)
    (H8 : join
            (set (set O abtcblsid (abstcblist (set x7 x6 (x10, rdy, x0, x14)))) absecblsid
               (absecblist (set x3 x (absmsgq nil x12 x13, remove_tid x6 x4)))) Of O'')
    (x2 : val)
    (x9 : msg)
    (x11 : taskstatus)
    (H2 : get O abtcblsid = Some (abstcblist x7))
    (H3 : get O absecblsid = Some (absecblist x3))
    (H4 : get x3 x = Some (absmsgq nil x12 x13, x4))
    (H5 : x4 <> nil)
    (H6 : GetHWait x7 x4 x6)
    (H9 : get x7 x6 = Some (x10, x11, x9, x14))
    (Heqv : x2 = Vint32 (Int.repr OS_NO_ERR)),
    
    FIFO_ext O''.
Proof.
  intros. 
  assert (get O' absecblsid = Some (absecblist x3)) as Hecbls.
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
  eapply Hext in H4;eauto.
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  eauto.
  (*eid <> x*)
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.

Qed.

Lemma FIFO_ext_qpost_ovf_block_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x0 : val)
    (x2 : priority)
    (x7 : addrval)
    (x8 : EcbMod.map)
    (x10 : TcbMod.map)
    (x12 : list ms)
    (x13 : maxlen)
    (x14 : list tid)
    (x15 : waitset)
    (x16 : susstatus)
    (H8 : join
            (set (set O abtcblsid (abstcblist (set x10 x7 (x2, wait (os_stat_postq x) None, x0, x16))))
               absecblsid (absecblist (set x8 x (absmsgq x12 x13 (x7 :: x14), x15)))) Of O'')
    (x3 : taskstatus)
    (x4 : msg)
    (x5 : int32)
    (x6 : val)
    (H1 : get O curtid = Some (oscurt x7))
    (H2 : get O absecblsid = Some (absecblist x8))
    (H3 : get O abtcblsid = Some (abstcblist x10))
    (H4 : get x8 x = Some (absmsgq x12 x13 x14, x15))
    (H5 : (Z.of_nat (length x12) >= Int.unsigned x13)%Z)
    (H9 : get x10 x7 = Some (x2, x3, x4, x16)), 

    FIFO_ext O''.
Proof.
  intros. 
  assert (get O' absecblsid = Some (absecblist x8)) as Hecbls.
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
  eapply Hext in H4;eauto.
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  eauto.
  (*eid <> x*)
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
Qed.

Lemma fifo_ext_qpost_timeout_err_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x x4 : addrval)
    (x5 : TcbMod.map)
    (x6 : priority)
    (x8 : EcbMod.map)
    (x10 : list tid)
    (x11 : maxlen)
    (x12 : list ms)
    (x13 : waitset)
    (x14 : susstatus)
    (H8 : join
            (set (set O abtcblsid (abstcblist (set x5 x4 (x6, rdy, Vnull, x14)))) absecblsid
               (absecblist (set x8 x (absmsgq x12 x11 (remove_tid x4 x10), x13)))) Of O'')
    (x0 x2 x3 : val)
    (x7 : msg)
    (H1 : get O curtid = Some (oscurt x4))
    (H2 : get O abtcblsid = Some (abstcblist x5))
    (H3 : get x5 x4 = Some (x6, wait (os_stat_postq x) None, x7, x14))
    (H4 : get O absecblsid = Some (absecblist x8))
    (H5 : get x8 x = Some (absmsgq x12 x11 x10, x13))
    (H6 : In x4 x10)
    (Heqv : x3 = Vint32 (Int.repr OS_TIMEOUT)),
    
    FIFO_ext O''.
Proof.
  intros. 
  assert (get O' absecblsid = Some (absecblist x8)) as Hecbls.
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
  eapply Hext in H5;eauto.
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  eauto.
  (*eid <> x*)
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
Qed.       

Lemma fifo_ext_qpost_nowt_succ_preserved:
  forall
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : val)
    (x4 : nat)
    (x5 : EcbMod.map)
    (x6 : maxlen)
    (x7 : list ms)
    (x8 : list tid)
    (x9 : list act)
    (x11 : MqcntMod.map)
    (H8 : join
            (set
               (set (set O loglsid (oslog (x9 ++ enque x x2 x4 :: nil))) mqcntid
                  (mqcnt (set x11 x (x4 + 1)%nat))) absecblsid
               (absecblist (set x5 x (absmsgq (x7 ++ (x2, x4) :: nil) x6 x8, nil)))) Of O'')
    (x0 x3 : val)
    (H2 : get O absecblsid = Some (absecblist x5))
    (H3 : get x5 x = Some (absmsgq x7 x6 x8, nil))
    (H4 : (Z.of_nat (length x7) < Int.unsigned x6)%Z)
    (H5 : get O loglsid = Some (oslog x9))
    (H9 : get O mqcntid = Some (mqcnt x11))
    (H10 : get x11 x = Some x4)
    (Heqv : x3 = Vint32 (Int.repr OS_NO_ERR)),
    
    FIFO_ext O''. 
Proof.
  intros. 
  assert (get O' loglsid = Some (oslog x9)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x5)) as Hecbls.
  eapply join_get_get_l;eauto. 
  assert (get O' mqcntid = Some (mqcnt x11)) as Hmqcnt.
  eapply join_get_get_l;eauto.
  lets Heq : H8 .
  eapply  join_get_set_eq_3 in Heq;eauto.
  subst.

  unfold FIFO_ext in *.
  rename H0 into Hext.

  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  do 2 rewrite map_get_set' in Hget';auto.
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'. 
  (*  rewrite map_get_set' in Hget_e; eauto. *)
  rewrite map_get_set in Hget_e; eauto.
  do 1 rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set in Hget_c; eauto.
  inverts Hget_e. 
  inverts Hget_c.

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x1) x3. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (He:eid = x \/ eid <> x) by tauto.
  destruct He;subst.
  (* eid = x *)
  { 
    rewrite EcbMod.map_get_set in Hget_ecb; eauto.
    inverts Hget_ecb.
    specialize Hext with (l2:= l2') (ms:= x7) (eid:=x).
    assert (forall j : nat,nth_error l2' j <> Some (delque x)).
    { introv Hf.
      eapply Hnth2.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (forall j : nat,nth_error l2' j <> Some (creque x)).
    { introv Hf.
      eapply Hnth1.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    lets Hext' : H0.
    eapply Hext in Hext';eauto.
    destruct Hext' as (Hisinc & Hltlogq & Hltqcmp & Hltlogcmp & Hcre & Hfifo).
    splits.
    (*subgoals - is_inc*)
    unfold is_inc in *.
    intros i1 i2 m1 m2 cnt cnt' Hn1 Hn2 Hi.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      assert (Hi2: i2 < length (x7 ++ (x2, x4) :: nil)).
      rewrite <- nth_error_Some.
      rewrite Hn2;auto. 
      rewrite last_length in Hi2.
      false.
      eapply NPeano.Nat.sub_0_le in Hi1.
      eapply NPeano.Nat.le_antisymm in Hlt;auto.
      subst.
      eapply lt_not_le in Hi.
      eapply lt_n_Sm_le in Hi2.
      auto with zarith.
    }
    destruct Hn1 as (Hlt & Hn1).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    {
      destruct Hn2 as (Hlt2 & Hn2).
      eapply Hisinc in Hi;eauto.
    }
    destruct Hn2 as (Hlt2 & Hn2).
    (*i2 = length x7*)
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hi2 &Hn2).
    eapply NPeano.Nat.sub_0_le in Hi2.
    eapply NPeano.Nat.le_antisymm in Hlt2;auto.
    unfold lt_cnt_que_cmp in Hltqcmp.
    eapply Hltqcmp in Hn1;eauto.
    inverts Hn2;auto.
    
    (*subgoals - lt_cnt_log_que*)
    unfold lt_cnt_log_que in *.
    intros i j m m' cnt cnt' Hn1 Hn2.
    apply nth_error_app_eq in Hn1.
    destruct Hn1 as [Hn1 | Hn1].
    2:{ (*false*)
      destruct Hn1 as (Hlt & Hn1).
      eapply nth_error_single in Hn1.
      destruct Hn1 as (Hi1 & Hn1).
      inverts Hn1.
    }
    destruct Hn1 as (Hlt & Hn1).
    apply nth_error_app_eq in Hn2.
    destruct Hn2 as [Hn2 | Hn2].
    (*j0 < length x7*)
    destruct Hn2 as (Hj0 & Hn2).
    eapply Hltlogq in Hn2;eauto.
    (*j0 >= length x7*)
    destruct Hn2 as (Hj0 & Hn2).
    eapply nth_error_single in Hn2.
    destruct Hn2 as (Hj0' & Hcnt').
    eapply NPeano.Nat.sub_0_le in Hj0'.
    eapply NPeano.Nat.le_antisymm in Hj0;auto.
    clear Hj0'. 
    unfold lt_cnt_log_cmp in Hltlogcmp.
    eapply Hltlogcmp in Hn1;eauto.
    inverts Hcnt';auto.
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    (*i < length x7*)
    destruct Hnth' as (Hlt & Hnth).
    specialize Hltqcmp with (cnt' := x4).
    eapply Hltqcmp in Hnth;eauto.
    rewrite map_get_set in Hget';eauto.
    eapply MqcntMod.option2val in Hget'.
    auto with zarith.
    (*i >= length x7*)
    destruct Hnth' as (Hlt & Hnth).
    eapply nth_error_single in Hnth.
    destruct Hnth as (Heq & Hnth ).
    inverts Hnth.
    rewrite map_get_set in Hget';eauto.
    eapply MqcntMod.option2val in Hget'.
    auto with zarith.
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (Hlt & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      inverts Hnth'.
    }
    destruct Hnth' as (Hlt & Hnth').
    specialize Hltlogcmp with (cnt' := x4).
    eapply Hltlogcmp in Hnth';eauto.
    rewrite map_get_set in Hget';eauto.
    eapply MqcntMod.option2val in Hget'.
    auto with zarith.
    
    (*subgoals - cre_log_cmp*)
    unfold cre_log_cmp in *.
    destruct Hcre as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    (*nen false*)
    specialize Hnen with (j:= (length l2')) (m:= x2) (cnt:= x4).
    assert (Hlengthl2': (length l2')<=(length l2')) by auto.
    eapply nth_error_app2  in Hlengthl2' .
    rewrite Hlengthl2' in Hnen. 
    rewrite Nat.sub_diag in Hnen.
    simpl in Hnen.
    tryfalse.
    (*Hbackward*)
    introv Hinitq.
    destruct Hinitq as (Hget' & Hnil).
    induction x7 in Hnil.
    simpl in Hnil. tryfalse.
    tryfalse.
    (*FIFO*)
    apply fifo_en;auto.
  }
  
  (* eid <> x *)
  {
    rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
    assert (forall j : nat,nth_error l2' j <> Some (creque eid)).
    { introv Hf.
      eapply Hnth1.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (forall j : nat,nth_error l2' j <> Some (delque eid)).
    { introv Hf.
      eapply Hnth2.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    lets Hext' : H0.
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
      inverts Hn1.
    }
    destruct Hn1 as (Hlt & Hn1).
    eapply Hltlogq in Hn1;eauto.
    
    (*subgoals - lt_cnt_que_cmp*)
    unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    rewrite map_get_set' in Hget';eauto.
    
    (*subgoals - lt_cnt_log_cmp*)
    unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    apply nth_error_app_eq in Hnth'.
    destruct Hnth' as [Hnth' | Hnth'].
    2:{ (*false*)
      destruct Hnth' as (Hlt & Hnth').
      eapply nth_error_single in Hnth'.
      destruct Hnth' as (Hi1 & Hnth').
      inverts Hnth'.
    }
    destruct Hnth' as (Hlt & Hnth').
    rewrite map_get_set' in Hget';eauto.
    
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
    assert (MqcntMod.get x11 eid = Some 0%nat /\ ms = nil).
    {eapply Hforward ;splits;auto. }
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
    apply fifo_en;auto.
  }
Qed.

Lemma mqsend_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mqsend vl) cd ->
    FIFO_ext O ->
    spec_step sc cd O cd' O' -> 
    FIFO_ext O'.
Proof.
  introv Hhs Hgd Hsp. 
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto; fail).

  repeat symexe.

  Set Nested Proofs Allowed.      
  { fifo_ext_preserve_eq. }
  { eapply fifo_ext_qpost_exwt_succ_preserved; eauto. } 
  { eapply FIFO_ext_qpost_ovf_block_preserved; eauto. }
  { eapply fifo_ext_qpost_timeout_err_preserved; eauto. }
  { eapply fifo_ext_qpost_nowt_succ_preserved; eauto. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { eapply fifo_ext_qpost_nowt_succ_preserved; eauto. }
  { eapply fifo_ext_qpost_exwt_succ_preserved; eauto. }
  { fifo_ext_preserve_eq. }
Qed.   
  

  
