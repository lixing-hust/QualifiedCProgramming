
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

Lemma fifo_ext_qcre_ecb_activate_preserved:
  forall 
    (O' O'' : OSAbstMod.map)
    (x0 : int32)
    (x2 : addrval)
    (x3 : EcbMod.map)
    (x4 : addrval)
    (x5 : EvAuxLocMod.map)
    (x9 : list act)
    (x11 : MqcntMod.map)
    (O Of : osabst)
    (H8 : join
            (set
               (set
                  (set
                     (set O loglsid (oslog (x9 ++ creque x2 :: nil)))
                     mqcntid (mqcnt (set x11 x2 0))) absecblsid
                  (absecblist (set x3 x2 (absmsgq nil x0 nil, nil))))
               evlocid
               (evloc
                  (set x5 x4 (Vint32 (Int.repr __EvLoc_ecbcre2)))))
            Of O'')
    (H7 :  join O Of O')      
    (H0 : FIFO_ext O')
    (x : val)
    (H2 : get O absecblsid = Some (absecblist x3))
    (H3 : get x3 x2 = None)
    (H4 : get O evlocid = Some (evloc x5))
    (H5 : get O curtid = Some (oscurt x4))
    (H9 : get O loglsid = Some (oslog x9))
    (H11 : get O mqcntid = Some (mqcnt x11))
    (H12 : get x11 x2 = None)
    (Heq1 : x = Vptr x2)
    (* (Hoslog : get O' loglsid = Some (oslog x9)) *)
    (* (Hecbls : get O' absecblsid = Some (absecblist x3)) *)
  (* (Hmqcnt : get O' mqcntid = Some (mqcnt x11)) *), 
    
    FIFO_ext O''. 

Proof.
  intros. 
  subst.
  lets Heq : H8 .
  eapply  join_get_set_eq_4 in Heq;eauto.
  subst.
  
  unfold FIFO_ext in *.
  rename H0 into Hext.
  rewrite map_get_set'; auto. 
  rewrite map_get_set'; auto.
  rewrite map_get_set'; auto.

  introv Hget Heq Hnth1 Hnth2 Hget_e Hget_ecb Hget_c.
  lets Hget': Hget.
  rewrite map_get_set in Hget'; eauto.
  inverts Hget'.
  rewrite map_get_set' in Hget_e; eauto.
  rewrite map_get_set in Hget_e; eauto.
  do 2 rewrite map_get_set' in Hget_c; eauto.
  rewrite map_get_set in Hget_c; eauto.
  inverts Hget_e; inverts Hget_c.

  assert (He:eid = x2 \/ eid <> x2)by tauto.
  destruct He. rewrite H0 in *;clear H0.
  (* eid = x2 *)
  rewrite EcbMod.map_get_set in Hget_ecb; eauto.
  inverts Hget_ecb.
  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x) x0. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  splits;unfolds.
  intros;rewrite nth_error_nil in *; tryfalse.
  intros;rewrite nth_error_nil in *; tryfalse.
  intros;rewrite nth_error_nil in *; tryfalse.
  intros;rewrite nth_error_nil in *; tryfalse.
  split.
  intros; rewrite map_get_set;auto.
  intro. 
  splits;intros;rewrite nth_error_nil in *; auto.
  intros;rewrite nth_error_nil in *; tryfalse.
  rewrite app_comm_cons in H.
  erewrite app_assoc in H.
  eapply app_inj_tail in H.
  destruct H as (H& Hv);subst v.
  specialize Hnth1 with (j:= (length l2')).
  simpl in Hnth1.
  assert (Hlengthl2': (length l2')<=(length l2')) by auto.
  eapply nth_error_app2  in Hlengthl2' .
  rewrite Hlengthl2' in Hnth1. 
  rewrite Nat.sub_diag in Hnth1.
  simpl in Hnth1.
  tryfalse.
  
  (* eid <> x2 *)
  assert (Hl2: forall l2: list act, l2 = nil \/ (exists l2' v, l2 = l2' ++ (v::nil))).
  { induction l0. auto.
    right.
    destruct IHl0; simpljoin.
    exists (nil: list act) a. simpl; auto.
    exists (a :: x) x1. simpl; auto.
  }
  specialize Hl2 with (l2:= l2).
  destruct Hl2 as [ Heq | (l2' & v & Heq)]; subst l2.
  rewrite app_inj_tail_iff in H.
  destruct H as (_ & Hf); inverts Hf; tryfalse.
  rewrite app_comm_cons in H.
  rewrite app_assoc in H.
  rewrite app_inj_tail_iff in H.
  
  destruct H as (Hlog' & Heq); subst v.
  assert (forall j : nat, nth_error l2' j <> Some (creque eid)).
  {
    introv Heq. eapply  Hnth1.
    rewrite <- Heq.
    eapply nth_error_app1.   
    rewrite <- nth_error_Some. rewrite Heq. auto.
  }
  assert (forall j : nat, nth_error l2' j <> Some (delque eid) ).
  {
    introv Heq. eapply  Hnth2.
    rewrite <- Heq.
    eapply nth_error_app1.   
    rewrite <- nth_error_Some. rewrite Heq. auto.
  }
  rewrite EcbMod.map_get_set' in Hget_ecb; eauto.
  eapply Hext with (log:= x9) in H1;eauto;
    try solve [eapply join_get_get_l;eauto].

  simpljoin.
  (*is_inc*)
  splits;auto.
  (*lt_cnt_log_que*)
  { unfold lt_cnt_log_que in *.
    introv Hnth' Hnth''.
    eapply nth_error_app_eq in Hnth'.
    destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
    eapply H6;eauto.
    destruct (i - length l2') in Hnth.
    simpl in Hnth. tryfalse.
    inverts Hnth. 
    rewrite nth_error_nil in *.
    tryfalse. }
  (*lt_cnt_que_cmp*)
  { unfold lt_cnt_que_cmp in *.
    introv Hnth' Hget'.
    rewrite MqcntMod.set_sem in Hget'.
    rewrite tidspec.neq_beq_false in Hget';eauto.
  }
  (*lt_cnt_log_cmp*)
  { unfold lt_cnt_log_cmp in *.
    introv Hnth' Hget'.
    eapply nth_error_app_eq in Hnth';eauto.
    destruct Hnth' as [ (Hlt & Hnth ) | (Hlt &Hnth) ].
    rewrite MqcntMod.set_sem in Hget'.
    rewrite tidspec.neq_beq_false in Hget';eauto.
    eapply nth_error_single in Hnth.
    destruct Hnth as (Heq & Hnth ).
    inverts Hnth.
  }
  (*cre_log_cmp*)
  { unfold cre_log_cmp in *.
    destruct H14 as (Hforward & Hbackward).
    split.
    (*Hforward*)
    introv Hinitq.
    rewrite map_get_set';auto.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    assert (Hndel' : forall j : nat, nth_error l2' j <> Some (delque eid)).
    {
      clear- H0 Hndel.
      intros j Hf.
      eapply Hndel.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (Hnen' : forall j m cnt, nth_error l2' j <> Some (enque eid m cnt)).
    {
      clear- H0 Hnen.
      intros j m cnt Hf.
      eapply Hnen.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    assert (Hnde' : forall j m cnt, nth_error l2' j <> Some (deque eid m cnt)).
    {
      clear- H0 Hnde.
      intros j m cnt Hf.
      eapply Hnde.
      lets Hlen: nth_error_Some l2' j.
      rewrite Hf in Hlen. destruct Hlen as (Hlen & _).
      rewrite <- Hf.
      eapply nth_error_app1; eauto.
    }
    eapply Hforward;splits;auto.
    (*Hbackward*)
    introv Hinitq.
    rewrite map_get_set' in Hinitq;auto.
    eapply Hbackward in Hinitq.
    destruct Hinitq as (Hndel & Hnen & Hnde).
    splits.
    intros.
    introv Hfalse.
    eapply nth_error_app_eq in Hfalse.
    destruct Hfalse as [ (Hlt & Hfalse ) | (Hlt &Hfalse) ];  tryfalse.
    destruct (j - length l2') in Hfalse.
    simpl in Hfalse; tryfalse.
    inverts Hfalse. 
    rewrite nth_error_nil in *.
    tryfalse.
    
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
  (*   FIFO *)
  apply fifo_cre;auto.    
Qed.
  
Lemma mqcreate_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mqcreate vl) cd ->
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
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. } 
  { eapply fifo_ext_qcre_ecb_activate_preserved; eauto.  }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }

Qed. 
  
