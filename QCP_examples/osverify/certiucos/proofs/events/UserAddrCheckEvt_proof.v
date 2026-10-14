Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Export os_inv.
Require Import abs_op.
Require Import code_notations.
Require Import ifun_spec.

Require Import useraddrcheck.

Require Import ucos_include.
Require Import symbolic_lemmas.

Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope code_scope.
Local Open Scope list_scope.

Lemma ptrconst_rv: 
  forall (s : RstateOP) a, s |= Rv eptrconst a @ (Tptr Tint32) == Vptr a.
Proof.
  intros.
  simpl.
  destruct s as [[[[[[[]]]]]]].
  simpl.
  splits; auto.
Qed.

Axiom user_space_not_empty: 
  cmpaddr Clt userAddrStart userAddrEnd = true.

Lemma cmpaddr_trans: 
  forall a1 a2 a3, 
    cmpaddr Clt a1 a2 = true -> cmpaddr Clt a2 a3 = true -> cmpaddr Clt a1 a3 = true.
Proof.
  intros.
  unfold cmpaddr in *.
  destruct a1; destruct a2; destruct a3.
  destruct ((b <? b0)%positive) eqn: E1; destruct ((b0 <? b1)%positive) eqn: E2.
  -
    apply Pos.ltb_lt in E1. apply Pos.ltb_lt in E2.
    asserts_rewrite ((b <? b1)%positive = true).
    {
      apply Pos.ltb_lt.
      eapply Pos.lt_trans; eauto.
    }
    simpl; auto.
  -
    simpl in H0.
    destruct (Int.ltu i0 i1).
    apply Pos.ltb_lt in E1. 
    asserts_rewrite ((b <? b1)%positive = true).
    {
      apply Pos.ltb_lt.
      destruct ((b0 =? b1)%positive) eqn: E0.
      apply Pos.eqb_eq in E0.
      subst. auto.
      simpl in H0. tryfalse.
    }
    simpl. auto.
    destruct ((b0 =? b1)%positive) eqn: E''; simpl in H0; tryfalse.
  -
    simpl in H.
    destruct (Int.ltu i i0).
    asserts_rewrite ((b <? b1)%positive = true). 
    {
      destruct ((b =? b0)%positive) eqn: E0.
      apply Pos.ltb_lt in E2. apply Pos.eqb_eq in E0.
      apply Pos.ltb_lt.
      subst. auto.
      simpl in H. tryfalse.
    }
    simpl. auto.
    clear H0.  
    destruct ((b =? b0)%positive) eqn: E'; simpl in H; tryfalse. 
  -
    simpl in H. simpl in H0.
    destruct ((b =? b0)%positive) eqn: E1';
      destruct ((b0 =? b1)%positive) eqn: E2';
      destruct (Int.ltu i i0) eqn: E3; destruct (Int.ltu i0 i1) eqn: E4;
      tryfalse.
    asserts_rewrite ((b =? b1)%positive = true).
    {
      apply Pos.eqb_eq in E1', E2'.
      subst.
      apply Pos.eqb_eq. auto.
    }
    asserts_rewrite (Int.ltu i i1 = true).
    { int auto. }
    destruct ((b <? b1)%positive); simpl; auto.
Qed.

Lemma cmpaddr_clt_self_false: 
  forall a, cmpaddr Clt a a = false.
Proof.
  intros.
  destruct a.
  simpl.
  destruct ((b <? b)%positive) eqn: E1.
  rewrite Pos.ltb_irrefl in E1. inverts E1.
  simpl.
  asserts_rewrite (Int.ltu i i = false).
  { int auto. }
  destruct ((b =? b)%positive); simpl; auto.
Qed.

Lemma cmpaddr_lt_le:
  forall a1 a2,
    cmpaddr Clt a1 a2 = true -> cmpaddr Cle a1 a2 = true.
Proof.
  intros.
  unfold cmpaddr in *.
  destruct a1; destruct a2.
  destruct ((b <? b0)%positive); destruct (Int.ltu i i0); auto.
  simpl. simpl in H. rewrite H. simpl; auto.
  simpl. simpl in H. rewrite H. simpl; auto.
Qed.

Lemma cmpaddr_not_lt:
  forall a1 a2, 
    cmpaddr Clt a1 a2 = false -> cmpaddr Cle a2 a1 = true. 
Proof.
  intros.
  unfold cmpaddr in *.
  destruct a1; destruct a2.
  destruct ((b <? b0)%positive) eqn: E1;
    destruct ((b =? b0)%positive && Int.ltu i i0) eqn: E2;
    destruct (Int.eq i0 i) eqn: E3; tryfalse. 
  destruct ((b =? b0)%positive) eqn: E'; tryfalse.
  simpl in E2.
  assert (b = b0). apply Pos.eqb_eq in E'. auto.
  subst.
  asserts_rewrite ((b0 =? b0)%positive = true).
  apply Pos.eqb_eq; auto.
  simpl.
  rewrite E1. simpl.
  destruct (Int.ltu i0 i); auto.
  simpl.
  apply Pos.ltb_ge in E1.
  assert (b0 <> b).
  {
    assert (b0 = b \/ b0 <> b) by tauto.
    inversion H0.
    subst.
    rewrite Pos.eqb_refl in E'. tryfalse.
    auto.
  }
  assert (b0 < b)%positive.
  { clear - E1 H0. int auto. }
  asserts_rewrite ((b0 <? b)%positive = true).
  { apply Pos.ltb_lt; auto. }
  simpl; auto.
  apply Pos.ltb_ge in E1.
  assert (b0 = b \/ b0 <> b) by tauto.
  inversion H0.
  subst.
  assert (Heq: (b =? b)%positive = true).
  { apply Pos.eqb_eq; auto. }
  rewrite Heq in E2.
  simpl in E2.
  assert (Hlt: Int.ltu i0 i = true).
  { int auto. }
  rewrite Hlt. 
  rewrite Heq.
  destruct ((b <? b)%positive); simpl; auto. 
  
  assert (b0 < b)%positive.
  { clear - E1 H1. int auto. }
  asserts_rewrite ((b0 <? b)%positive = true).
  { apply Pos.ltb_lt; auto. }
  simpl; auto.
Qed.   

Lemma cmpaddr_lt_switch:
  forall b1 o1 b2 o2, 
    cmpaddr Clt (b1, o1) (b2, o2) = false -> 
    b1 = b2 -> 
    Int.eq o1 o2 = false ->  
    cmpaddr Clt (b2, o2) (b1, o1) = true.  
Proof.
  intros.
  apply cmpaddr_not_lt in H.
  unfold cmpaddr in *.
  destruct ((b2 <? b1)%positive) eqn: E1;
    destruct ((b2 =? b1)%positive) eqn: E2;
    destruct (Int.ltu o2 o1) eqn: E3;
    destruct (Int.eq o2 o1) eqn: E4; tryfalse; try (simpl; auto).  
  clear -H1 E4.
  int auto.
Qed.   

Lemma cmpaddr_lt_switch':
  forall b1 o1 b2 o2, 
    cmpaddr Clt (b1, o1) (b2, o2) = false -> 
    b1 <> b2 -> 
    cmpaddr Clt (b2, o2) (b1, o1) = true.  
Proof.
  intros.
  apply cmpaddr_not_lt in H.
  unfold cmpaddr in *.
  destruct ((b2 <? b1)%positive) eqn: E1;
    destruct ((b2 =? b1)%positive) eqn: E2;
    destruct (Int.ltu o2 o1) eqn: E3;
    destruct (Int.eq o2 o1) eqn: E4; tryfalse; try (simpl; auto).  
  apply Pos.eqb_eq in E2. subst.
  false. 
Qed.


Lemma UserAddrCheck_proof:
  forall vl p r logicl ct, 
    Some p =
      BuildPreI os_internal UserAddrCheck
        vl logicl UserAddrCheckEvtPre ct ->
    Some r =
      BuildRetI os_internal UserAddrCheck vl logicl UserAddrCheckEvtPost ct ->
    exists t d1 d2 s,
      os_internal UserAddrCheck = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  hoare unfold.
  destruct H as [Hptr | Hptr]; inverts Hptr.
  - (* Vnull *)
    hoare forward.
    hoare unfold.
    eapply rete_rule with (v:=Vint32 Int.zero).
    intros.
    split.
    sep pauto.
    sep cancel A_dom_lenv.
    apply adisj_intro; left.
    sep pauto.

    sep get rv.

    eapply hoare_disj_afalseP_l_pre; eauto.
    hoare_split_pure_all.
    inverts H; tryfalse.

  - (* Vptr ... *)  
    inverts H. destruct x0.
    hoare forward.
    hoare unfold.
    false.
    instantiate (1:=Afalse).
    eapply hoare_disj_afalseP_l_pre; eauto.
    hoare_split_pure_all.
    hoare forward.
    eapply ift_rule''.
    intros.
    sep remember (8::9::nil)%nat in H0.
    clear HeqH2.
    eapply bop_rv; eauto.
    eapply bop_rv; eauto.
    eapply bop_rv; eauto.
    eapply lvar_rv; eauto.
    apply ptrconst_rv.
    destruct userAddrStart.
    unfold bop_eval.
    simpl. pure_auto.
    simpl. eauto.
    eapply bop_rv; eauto.
    apply ptrconst_rv.
    eapply lvar_rv; eauto.
    destruct userAddrStart.
    unfold bop_eval.
    simpl. pure_auto.
    simpl. eauto.
    unfold bop_eval. unfold cmp_val.
    destruct (cmpaddr Clt (b, i) userAddrStart).
    simpl. destruct userAddrStart. pure_auto.
    simpl. destruct userAddrStart.
    pure_auto.
    simpl. eauto.
    eapply bop_rv; eauto.
    apply ptrconst_rv.
    eapply lvar_rv; eauto.
    destruct (cmpaddr Clt userAddrEnd (b, i)).
    simpl. destruct userAddrEnd. pure_auto.
    destruct userAddrEnd. 
    unfold bop_eval.
    unfold cmp_val.
    destruct (cmpaddr Clt (b0, i0) (b, i)); pure_auto.
    simpl; eauto.
    destruct userAddrStart.
    destruct userAddrEnd.
    simpl.
    pure_auto.
    simpl; eauto.
    hoare unfold.
    unfold bop_eval in *.
    unfold cmp_val in *.
    clear H2 H3.
    assert (Hcmp_cases:
             cmpaddr Cle (b, i) userAddrStart = true \/ cmpaddr Clt userAddrEnd (b, i) = true).
    {
      destruct (cmpaddr Clt (b, i) userAddrStart) eqn: E1;
        destruct (val_eq (Vptr userAddrStart) (Vptr (b, i))) eqn: E2; 
        destruct (cmpaddr Clt userAddrEnd (b, i)) eqn: E3.
      lets Hf1: cmpaddr_trans E1 user_space_not_empty.
      lets Hf2: cmpaddr_trans Hf1 E3.
      rewrite cmpaddr_clt_self_false in Hf2. tryfalse.
      apply cmpaddr_lt_le in E1. rewrite E1.
      left. auto.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
      right. auto.
      simpl in E2.
      destruct userAddrStart.
      destruct (peq b0 b) eqn: Ea; destruct (Int.eq i0 i) eqn: Eb.
      inverts E2.
      subst.
      simpl. 
      asserts_rewrite (Int.eq i i0 = true). { clear -Eb. int auto. }
      left.
      asserts_rewrite ((b =? b)%positive = true).
      { apply Pos.eqb_eq. auto.  }
      destruct ((b <? b)%positive); destruct (true && Int.ltu i i0); auto.
      inverts E2. 
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0. tryfalse.
      inverts E2.
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0.
      tryfalse.
      inverts E2.
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H0.
      simpl in H0.
      tryfalse.
      right. auto.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
    }
    eapply rete_rule with (v:=Vint32 Int.zero); eauto. 
    intros.
    split.
    sep pauto.
    sep cancel A_dom_lenv.
    apply adisj_intro; left.
    sep pauto.
    right.
    exists (b, i).
    splits; auto.

    sep get rv.

    eapply hoare_disj_afalseP_l_pre; eauto.
    hoare unfold.
    unfold bop_eval in *.
    assert (cmpaddr Clt userAddrStart (b, i) = true /\ cmpaddr Cle (b, i) userAddrEnd = true).
    {
      unfold cmp_val in H0. 
      inversion H0.

      destruct (cmpaddr Clt (b, i) userAddrStart) eqn: E1; 
        destruct (val_eq (Vptr userAddrStart) (Vptr (b, i))) eqn: E2;
        destruct (cmpaddr Clt userAddrEnd (b, i)) eqn: E3.
      lets Hf1: cmpaddr_trans E1 user_space_not_empty.
      lets Hf2: cmpaddr_trans Hf1 E3.
      rewrite cmpaddr_clt_self_false in Hf2. tryfalse.
      destruct (val_inj (Some v)); simpl in H2; tryfalse.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i).
      inverts E2. 
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with (true) in H2.
      simpl in H2.
      change (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.one) with (true) in H2.
      simpl in H2.
      inverts H2.
      inverts E2. 
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with (false) in H2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H2.
      simpl in H2.
      inverts H2.
      inverts E2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H2.
      simpl in H2.
      inverts H2.
      inverts E2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.zero) with false in H2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H2.
      simpl in H2.
      inverts H2.
      simpl in E2.
      destruct userAddrStart eqn: Est.
      destruct (peq b0 b); destruct (Int.eq i0 i) eqn: E'; tryfalse.
      inverts E2.
      simpl in H2.
      change (Int.ltu Int.zero Int.zero || Int.ltu Int.zero Int.one) with true in H2.
      simpl in H2.
      change (Int.ltu Int.zero Int.one || Int.ltu Int.zero Int.zero) with true in H2.
      simpl in H2.
      inverts H2.
      inverts E2.
      subst. 
      apply cmpaddr_not_lt in E3. rewrite E3.
      split; auto.
      eapply cmpaddr_lt_switch in E1; eauto.
      clear -E'. int auto.
      eapply cmpaddr_lt_switch' in E1; eauto. 
      rewrite E1.
      split; auto.
      apply cmpaddr_not_lt in E3; auto. 
      eapply cmpaddr_lt_switch' in E1; eauto. 
      rewrite E1.
      split; auto.
      apply cmpaddr_not_lt in E3; auto. 
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.
      simpl in E2. destruct userAddrStart.
      destruct (peq b0 b); destruct (Int.eq i0 i); tryfalse.

      destruct (cmpaddr Clt (b, i) userAddrStart);
        destruct (val_eq (Vptr userAddrStart) (Vptr (b, i))); 
        destruct (cmpaddr Clt userAddrEnd (b, i));
        tryfalse.
      simpl in H2.
      destruct v; simpl in H2; tryfalse.
      destruct v; simpl in H2; tryfalse.
      simpl in H2.
      destruct v; simpl in H2; tryfalse.
      destruct (Int.ltu Int.zero i0); simpl in H2; tryfalse.
      destruct v; simpl in H2; tryfalse.
      destruct (Int.ltu Int.zero i0); simpl in H2; tryfalse.
    }
    
    eapply rete_rule with (v:=Vint32 Int.one); eauto. 
    intros. 
    split.
    sep pauto.
    sep cancel A_dom_lenv.
    apply adisj_intro; right.
    sep pauto.
    exists (b, i). splits; auto.
    
    sep get rv.

Qed. 

