
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

Lemma fifo_ext_qdel_succ_exwait_preserved:
  forall
    (O' O'' : OSAbstMod.map)
    (O Of : osabst)
    (x : addrval)
    (x2 : EcbMod.map)
    (x5 : list tid)
    (x6 : list addrval)
    (x7 : TcbMod.map)
    (x10 : EvAuxPtrMod.map)
    (x12 : addrval)
    (x13 : list act)
    (x18 : MqcntMod.map)
    (H8 : join
            (set
               (set
                  (set
                     (set
                        (set O loglsid
                           (oslog (x13 ++ delque x :: nil))) mqcntid
                        (mqcnt x18)) absecblsid 
                     (absecblist x2)) abtcblsid
                  (abstcblist (set_tls_rdy0 x5 (set_tls_rdy x6 x7))))
               evptrid (evptr (set x10 x12 (Vnull, Vnull, Vnull))))
            Of O'')
    (H7 : join O Of O')
    (H0 : FIFO_ext O')
    (x0 : EcbMod.map)
    (x3 : list ms)
    (x4 : maxlen)
    (x14 : MqcntMod.map)
    (x17 : nat)
    (H2 : get O absecblsid = Some (absecblist x0))
    (H3 : get x0 x = Some (absmsgq x3 x4 x5, x6))
    (H4 : x6 <> nil \/ x5 <> nil)
    (H5 : join x2 (sig x (absmsgq x3 x4 x5, x6)) x0)
    (H6 : get O abtcblsid = Some (abstcblist x7))
    (H11 : get O evptrid = Some (evptr x10))
    (H12 : get O curtid = Some (oscurt x12))
    (H14 : get O loglsid = Some (oslog x13))
    (H16 : get O mqcntid = Some (mqcnt x14))
    (H17 : get x14 x = Some x17)
    (H18 : join x18 (sig x x17) x14),

    FIFO_ext O''. 
Proof.
  intros. 
  assert (get O' loglsid = Some (oslog x13)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x0)) as Hecbls.
  eapply join_get_get_l;eauto. 
  assert (get O' mqcntid = Some (mqcnt x14)) as Hmqcnt.
  eapply join_get_get_l;eauto.
  lets Heq : H8 .
  eapply  join_get_set_eq_5 in Heq;eauto.
  subst.
  
  unfold FIFO_ext in *.
  rename H0 into Hext.

  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  do 4 (rewrite map_get_set' in Hget' ; auto) . 
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'.
  do 2 rewrite map_get_set' in Hget_e; eauto.
  rewrite map_get_set in Hget_e; eauto.
  do 3 rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set in Hget_c; eauto.
  (*   symmetry in Hget_e. *)
  inverts Hget_e.  inverts Hget_c.

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x1) x2. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (He:eid = x \/ eid <> x)by tauto.
  destruct He;subst.
  (* eid = x2 *)
  {
    eapply join_comm in H5.
    clear - H5 Hget_ecb.
    unfold get,join,sig in *.
    simpl in *.
    unfold EcbMod.join in *.
    lets Hf : H5 x. clear H5.
    rewrite EcbMod.map_get_sig in Hf.
    rewrite Hget_ecb in Hf; tryfalse.
  }
  (* eid <> x2 *)
  {
    assert (forall j : nat,nth_error l2' j <> Some (delque eid)).
    { introv Hf.
      eapply Hnth2.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (forall j : nat,nth_error l2' j <> Some (creque eid)).
    { introv Hf.
      eapply Hnth1.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    lets Hext' : H0.
    eapply Hext in Hext';eauto.
    
    Focus 2.
    eapply join_comm in H5.
    eapply EcbMod.join_get_r in Hget_ecb.
    2: { eapply H5. } eapply Hget_ecb.
    
    simpljoin.
    (*is_inc*)
    splits;auto.
    (*lt_cnt_log_que*)
    { unfold lt_cnt_log_que in *.
      introv Hnth' Hnth''.
      eapply nth_error_app_eq in Hnth'.
      destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
      eapply H10;eauto.
      destruct (i - length l2') in Hnth.
      simpl in Hnth. tryfalse.
      inverts Hnth. 
      rewrite nth_error_nil in *.
      tryfalse. }
    (*lt_cnt_que_cmp*)
    {
      clear - H17 H18 H13.
      unfold lt_cnt_que_cmp in *.
      introv Hnth' Hget'.
      eapply join_comm in H18.
      unfold get,join,sig in *.
      simpl in *.
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      false.
      unfold MqcntMod.join in *.
      lets Hf : H18 x. clear H18.
      rewrite MqcntMod.map_get_sig in Hf.
      rewrite Hget' in *. tryfalse.
      eapply H13; eauto.
      eapply MqcntMod.join_get_r; eauto.
    }
    (*lt_cnt_log_cmp*)
    {
      clear - H17 H18 H15.
      unfold lt_cnt_log_cmp in *.
      introv Hnth' Hget'.
      eapply join_comm in H18.
      unfold get,join,sig in *.
      simpl in *.
      eapply nth_error_app_eq in Hnth';eauto.
      destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
      2:{
        destruct (i - length l2') in Hnth.
        simpl in Hnth. tryfalse.
        inverts Hnth. 
        rewrite nth_error_nil in *.
        tryfalse. 
      }
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      false.
      unfold MqcntMod.join in *.
      lets Hf : H18 x. clear H18.
      rewrite MqcntMod.map_get_sig in Hf.
      rewrite Hget' in *. tryfalse.
      eapply H15; eauto.
      eapply MqcntMod.join_get_r; eauto.
    }
    (*cre_log_cmp*)
    {
      clear - H17 H18 H19 Hnth1 Hnth2.
      unfold cre_log_cmp in *.
      destruct H19 as (Hforward & Hbackward).
      split.
      (*Hforward*)
      introv Hinitq.
      destruct Hinitq as (Hndel & Hnen & Hnde).
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      (*eid = x*)
      specialize Hndel with (j:= (length l2')).
      simpl in Hndel.
      assert (Hlengthl2': (length l2')<=(length l2')) by auto.
      eapply nth_error_app2  in Hlengthl2' .
      rewrite Hlengthl2' in Hndel. 
      rewrite Nat.sub_diag in Hndel.
      simpl in Hndel.
      tryfalse.
      (*eid <> x*)
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
      eapply join_comm in H18.
      unfold get,join,sig in *.
      simpl in *.
      assert (MqcntMod.get x14 eid = Some 0%nat /\ ms = nil).
      {eapply Hforward ;splits;auto. }
      destruct H0;splits;auto.
      eapply joinsig_neq_get; eauto.
      (*Hbackward*)
      introv Hinitq.
      assert (Hgeteid: get x14 eid = Some 0%nat /\ ms = nil).
      {
        destruct Hinitq;split;auto.
        eapply join_get_l; eauto.
      }
      eapply Hbackward in Hgeteid;eauto.
      destruct Hgeteid as (Hndel & Hnen & Hnde).
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
    }  
    (*FIFO*)
    apply fifo_del;auto.
  }    
Qed.

Lemma fifo_ext_qdel_succ_nexwait_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (H0 : FIFO_ext O')
    (O Of : osabst)
    (H7 : join O Of O')
    (x : addrval)
    (x2 : EcbMod.map)
    (x7 : EvAuxPtrMod.map)
    (x9 : addrval)
    (x10 : list act)
    (x15 : MqcntMod.map)
    (H8 : join
            (set
               (set
                  (set
                     (set O loglsid (oslog (x10 ++ delque x :: nil)))
                     mqcntid (mqcnt x15)) absecblsid 
                  (absecblist x2)) evptrid
               (evptr (set x7 x9 (Vnull, Vnull, Vnull)))) Of O'')
    (x0 : EcbMod.map)
    (x3 : list ms)
    (x4 : maxlen)
    (x5 : list tid)
    (x6 : waitset)
    (x12 : MqcntMod.map)
    (x13 : nat)
    (H2 : get O absecblsid = Some (absecblist x0))
    (H3 : get x0 x = Some (absmsgq x3 x4 nil, nil))
    (H4 : join x2 (sig x (absmsgq x3 x4 x5, x6)) x0)
    (H5 : get O evptrid = Some (evptr x7))
    (H6 : get O curtid = Some (oscurt x9))
    (H10 : get O loglsid = Some (oslog x10))
    (H12 : get O mqcntid = Some (mqcnt x12))
    (H13 : get x12 x = Some x13)
    (H14 : join x15 (sig x x13) x12),

    FIFO_ext O''.
Proof.
  intros.
  
  assert (get O' loglsid = Some (oslog x10)) as Hoslog.
  eapply join_get_get_l;eauto.
  assert (get O' absecblsid = Some (absecblist x0)) as Hecbls.
  eapply join_get_get_l;eauto. 
  assert (get O' mqcntid = Some (mqcnt x12)) as Hmqcnt.
  eapply join_get_get_l;eauto.
  lets Heq : H8 .
  eapply  join_get_set_eq_4 in Heq;eauto.
  subst.
  
  unfold FIFO_ext in *.
  rename H0 into Hext.

  (*FIFO_ext*)
  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  do 3 (rewrite map_get_set' in Hget'; auto) .
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'.
  do 1 rewrite map_get_set' in Hget_e; eauto.
  rewrite map_get_set in Hget_e; eauto.
  do 2 rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set in Hget_c; eauto.
  (*   symmetry in Hget_e. *)
  inverts Hget_e.  inverts Hget_c.

  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x1) x2; simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  destruct H as (Hlog' & Heq); subst v.
  
  assert (He:eid = x \/ eid <> x)by tauto.
  destruct He;subst.
  (* eid = x2 *)
  {
    eapply join_comm in H4.
    clear - H4 Hget_ecb.
    unfold get,join,sig in *.
    simpl in *.
    unfold EcbMod.join in *.
    lets Hf : H4 x. clear H4.
    rewrite EcbMod.map_get_sig in Hf.
    rewrite Hget_ecb in Hf; tryfalse.
  }
  (* eid <> x2 *)
  {
    assert (forall j : nat,nth_error l2' j <> Some (delque eid)).
    { introv Hf.
      eapply Hnth2.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (forall j : nat,nth_error l2' j <> Some (creque eid)).
    { introv Hf.
      eapply Hnth1.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    lets Hext' : H0.
    eapply Hext in Hext';eauto.
    
    Focus 2.
    eapply join_comm in H4.
    eapply EcbMod.join_get_r in Hget_ecb.
    2: { eapply H4. } eapply Hget_ecb.
    
    simpljoin.
    (*is_inc*)
    splits;auto.
    (*lt_cnt_log_que*)
    { unfold lt_cnt_log_que in *.
      introv Hnth' Hnth''.
      eapply nth_error_app_eq in Hnth'.
      destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
      eapply H11;eauto.
      destruct (i - length l2') in Hnth.
      simpl in Hnth. tryfalse.
      inverts Hnth. 
      rewrite nth_error_nil in *.
      tryfalse. }
    (*lt_cnt_que_cmp*)
    {
      clear - H14 H15.
      unfold lt_cnt_que_cmp in *.
      introv Hnth' Hget'.
      eapply join_comm in H14.
      unfold get,join,sig in *.
      simpl in *.
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      false.
      unfold MqcntMod.join in *.
      lets Hf : H14 x. clear H14.
      rewrite MqcntMod.map_get_sig in Hf.
      rewrite Hget' in *. tryfalse.
      eapply H15; eauto.
      eapply MqcntMod.join_get_r; eauto.
    }
    (*lt_cnt_log_cmp*)
    {
      clear - H13 H14 H16.
      unfold lt_cnt_log_cmp in *.
      introv Hnth' Hget'.
      eapply join_comm in H14.
      unfold get,join,sig in *.
      simpl in *.
      eapply nth_error_app_eq in Hnth';eauto.
      destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
      2:{
        destruct (i - length l2') in Hnth.
        simpl in Hnth. tryfalse.
        inverts Hnth. 
        rewrite nth_error_nil in *.
        tryfalse. 
      }
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      false.
      unfold MqcntMod.join in *.
      lets Hf : H14 x. clear H14.
      rewrite MqcntMod.map_get_sig in Hf.
      rewrite Hget' in *. tryfalse.
      eapply H16; eauto.
      eapply MqcntMod.join_get_r; eauto.
    }
    (*cre_log_cmp*)
    {
      clear - H13 H14 H17 Hnth1 Hnth2.
      unfold cre_log_cmp in *.
      destruct H17 as (Hforward & Hbackward).
      split.
      (*Hforward*)
      introv Hinitq.
      destruct Hinitq as (Hndel & Hnen & Hnde).
      assert (Hc: eid = x \/ eid <> x) by tauto.
      destruct Hc.
      subst.
      (*eid = x*)
      specialize Hndel with (j:= (length l2')).
      simpl in Hndel.
      assert (Hlengthl2': (length l2')<=(length l2')) by auto.
      eapply nth_error_app2  in Hlengthl2' .
      rewrite Hlengthl2' in Hndel. 
      rewrite Nat.sub_diag in Hndel.
      simpl in Hndel.
      tryfalse.
      (*eid <> x*)
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
      eapply join_comm in H14.
      unfold get,join,sig in *.
      simpl in *.
      assert (MqcntMod.get x12 eid = Some 0%nat /\ ms = nil).
      {eapply Hforward ;splits;auto. }
      destruct H0;splits;auto.
      eapply joinsig_neq_get; eauto.
      (*Hbackward*)
      introv Hinitq.
      assert (Hgeteid: get x12 eid = Some 0%nat /\ ms = nil).
      {
        destruct Hinitq;split;auto.
        eapply join_get_l; eauto.
      }
      eapply Hbackward in Hgeteid;eauto.
      destruct Hgeteid as (Hndel & Hnen & Hnde).
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
    }
    (*FIFO*)
    apply fifo_del;auto.
  }
Qed.  

Lemma mqdelete_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mqdelete vl) cd ->
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
  
  { fifo_ext_preserve_eq. }
  
  { eapply fifo_ext_qdel_succ_exwait_preserved; eauto. }
  { eapply fifo_ext_qdel_succ_nexwait_preserved; eauto. }
  { fifo_ext_preserve_eq. }
Qed.


  
