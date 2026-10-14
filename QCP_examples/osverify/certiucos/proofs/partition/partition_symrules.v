Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.

(************************************************** symbolic lemmas **************************************)
(*********************************************************************************************************)

Fixpoint sub_decllist_skipn (n: nat) (d1 d2: decllist)  : bool :=
 match n, d2 with 
 | 0%nat, d2 => symbolic_lemmas.sub_decllist d1 d2  
 | S n', dcons x1 t1 d2' => sub_decllist_skipn n' d1 d2'
 | _, _ => false
 end.

Fixpoint sum_offset (n: nat) (d : decllist) : nat :=
  match n, d with 
  | 0%nat, d => 0%nat 
  | S n', dcons x1 t1 d' => (typelen t1 + (sum_offset n' d'))%nat 
  | S n', dnil => 0%nat 
  end.

Fixpoint id_notin_n id n d : bool :=
  match n with 
  | 0%nat => true 
  | S n' => match d with 
           | dnil => true 
           | dcons x t d' => andb (negb (Zeq_bool id x)) (id_notin_n id n' d') 
           end
  end.

Lemma sub_decllist_skipn_ftype:
  forall n d1 d2 t id, 
    sub_decllist_skipn n d1 d2 =true -> 
    id_notin_n id n d2 = true ->
    ftype id d1 = Some t -> 
    ftype id d2 = Some t. 
Proof.
  inductions n;
  simpl; intros. 
  - eapply symbolic_lemmas.sub_decllist_ftype;eauto.
  - 
    destruct d2; tryfalse.
    apply andb_true_iff in H0 as [? ?].
    apply Bool.negb_true_iff in H0.
    cbn.
    rewrite H0.
    eapply IHn;eauto.
Qed.

Lemma sub_decllist_offsetfld_baseneq:
  forall d1 d2 t id i z0,
    symbolic_lemmas.sub_decllist d1 d2 =true -> 
    field_offsetfld id d1 i = Some t  -> 
    field_offsetfld id d2 ($ z0 +ᵢ  i)  = Some ($ z0 +ᵢ  t). 
Proof.
  inductions d1.
    simpl; intros; tryfalse. 
  intros.
  simpl in H.
  destruct d2; tryfalse.
  apply andb_true_iff in H.
  destruct H.
  apply andb_true_iff in H.
  destruct H.
  apply type_eq_true_eq in H2.
  subst.
  apply Zeq_bool_eq in H.
  subst.
  simpl in *.
  remember (Zeq_bool id i1) as Ha.
  destruct Ha; auto.
    inverts H0. auto. 
  rewrite <- Int.add_assoc.
  rewrite (Int.add_commut ($ Z.of_nat (typelen t1))).
  rewrite Int.add_assoc.
  eapply IHd1;eauto. 
Qed.

Lemma sub_decllist_skipn_offsetfld:
  forall n d1 d2  id  i i0 z0 z,
    sub_decllist_skipn n d1 d2 =true -> 
    id_notin_n id n d2 = true ->
    z = Z.of_nat (sum_offset n d2) ->
    0 <= z <= Int.max_unsigned ->
    field_offsetfld id d1 i = Some i0 -> 
    field_offsetfld id d2 ($z0 +ᵢ i) = Some ($z0  +ᵢ $ z +ᵢ i0) . 
Proof.
  induction n;simpl; intros; tryfalse.
  - subst.
    rewrite (Int.add_commut ($ z0)  ($ 0)).
    rewrite  Int.add_zero_l.
    eapply sub_decllist_offsetfld_baseneq; eauto.
  - 
    destruct d2; tryfalse.
    apply andb_true_iff in H0 as [? ?].
    apply Bool.negb_true_iff in H0.
    cbn. rewrite H0.
    assert (z = Z.of_nat (typelen t) + Z.of_nat (sum_offset n d2)) by lia.
    clear H1.
    subst z.
    rewrite <- (Int.unsigned_repr (Z.of_nat (typelen t))) by lia.
    rewrite <- (Int.unsigned_repr (Z.of_nat (sum_offset n d2)))  by lia.
    rewrite <- Int.add_unsigned .
    rewrite <- Int.add_assoc.
    rewrite <- Int.add_assoc.
    rewrite Int.unsigned_repr by lia.
    rewrite (Int.add_commut ($ (Z.of_nat (typelen t)))).
    assert (0 <= Z.of_nat (sum_offset n d2) <= Int.max_unsigned) by lia.
    eapply IHn ;eauto.
Qed. 

Theorem struct_member_rv_typeneq_addrneq:
  forall s x l i m vl decl n id t' v P perm tp tid' decl',
    s |= LV x @ (Tptr tp) |=> Vptr l @ perm ** Astruct' (get_off_addr l ($ i)) decl vl ** P ->
    tp = Tstruct tid' decl' -> 
    sub_decllist_skipn m decl decl' =true -> 
    good_decllist decl = true ->
    sum_offset m decl' = Z.to_nat i ->
    0 <= i <= Int.max_unsigned ->
    id_notin_n id m decl' = true  ->
    ftype id decl = Some t' ->
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall ids dl, t' <> Tunion ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    id_nth id decl = Some n ->
    (n < length vl)%nat ->
    struct_type_vallist_match' decl vl  ->
    nth_val' n vl = v ->
    s |= Rv (efield (ederef (evar x)) id) @ t' == v.
Proof.
  intros * H H0 H1 H2 H3 H4 H5 H6 H7 H7'. intros.
  destruct_s s. 
  simpl in *;DeprecatedTactic.mytac.
  unfold get in *; simpl in *.
  rewrite H27.
  lets Hfs : sub_decllist_skipn_ftype H1 H5 H6; eauto.
  rewrite Hfs.
  unfold load;unfold loadm.
  rewrite Int.unsigned_zero in H28.
  lets Hf: symbolic_lemmas.mapstoval_loadbytes H28.
  simpl;auto.
  destruct Hf.
  destruct H.
  lets Hf: loadbytes_local H14 H.
  assert (loadbytes m0 (x19, 0%Z) (typelen (Tptr (Tstruct tid' decl'))) = Some x2) by auto.
  rewrite H12. clear H12.
  rewrite H0.
  destruct l.
  unfold getoff.
  unfold evaltype.
  unfold get ; simpl.
  rewrite H27.
  lets Hx : symbolic_lemmas.id_nth_eq H2 H9.
  lets Hoff: symbolic_lemmas.nth_id_exists_off Hx.
  destruct Hoff.
  unfold field_offset in *.
  assert (field_offsetfld id decl' (Int.zero +ᵢ Int.zero) = Some (Int.zero +ᵢ $ ( i) +ᵢ x3)) as Hy.
  { eapply sub_decllist_skipn_offsetfld with (n:= m);eauto. rewrite H3. lia. }
  rewrite Int.add_zero_l in Hy.
  rewrite Hy.
  rewrite Int.add_zero_l.
  assert (load t' x1 (addrval_to_addr (b, $ Int.unsigned i4 +ᵢ  ($ i +ᵢ  x3))) =
          Some  (nth_val' n vl)).
  { unfold addrval_to_addr.
    lets Hz: symbolic_lemmas.nth_val_imp_nth_val'_2 H10.
    unfold get_off_addr in H22. cbn [fst snd] in H22.
    rewrite symbolic_lemmas.struct_asrt_eq with (n:=n) in H22;eauto.
    unfold sat in H22;fold sat in H22; DeprecatedTactic.mytac.
    simpl in H16.
    rewrite Int.repr_unsigned.
    simpl in H20. destruct H20.
    eapply symbolic_lemmas.load_local;eauto.
    eapply symbolic_lemmas.load_local;eauto.
    eapply symbolic_lemmas.mapstoval_load;auto.
    eapply symbolic_lemmas.struct_tvmatch_imp_rule_tvmatch;eauto.
    rewrite <- Int.add_assoc. eauto. }
  apply map_join_comm in H14.
  eapply symbolic_lemmas.load_local;eauto.
  rewrite H27.
  eapply sub_decllist_skipn_ftype;eauto.
  eapply symbolic_lemmas.rule_type_val_match_nvundef;eauto.
  eapply symbolic_lemmas.struct_tvmatch_imp_rule_tvmatch;eauto.
Qed.

Lemma corport_nextPort_rv : forall s p_v v dport P,
  OS_Port_V_nextPort dport = Some v ->
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  s  |= LV corPort_ptr @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv corPort_ptr ′ → nextPort @ (Tptr Void) == v.
Proof.
  intros.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H0.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.
  do 11 (destruct dport;destruct H0 as [? H0];tryfalse).
  simpl;lia.
  unfold OS_Port_V_nextPort in H.
  eapply nth_val_nth_val'_some_eq; eauto.
Qed.

Lemma dmPort_direction_rv : forall s dmportp dmport P,
  struct_type_vallist_match' OS_Port_Seg_dls dmport ->
  s  |= LV dmPort @ OS_Port ∗ |-> Vptr dmportp **
        APortStruct dmportp dmport ** P ->
  s |= Rv dmPort ′ → os_code_defs.direction @ long == nth_val' 4 dmport.
Proof.
  intros.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dmport;tryfalse.
  do 4 (destruct dmport;destruct H as [? H];tryfalse).
  simpl;lia.
Qed.

Lemma port_coreNum_rv' : forall s p_v dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv port_ptr ′ → coreNum @ Int8u == nth_val' 2 dport.
Proof.
  intros * ? ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  destruct dport;destruct H as [? H];tryfalse.  destruct dport;destruct H as [? H];tryfalse.
  simpl;lia.
Qed.

Lemma port_coreNum_rv_gen' : forall s p_v dport P port_ptr,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv port_ptr ′ → coreNum @ Int8u == nth_val' 2 dport.
Proof.
  intros * ? ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  destruct dport;destruct H as [? H];tryfalse.  destruct dport;destruct H as [? H];tryfalse.
  simpl;lia.
Qed.

Lemma port_coreNum_rv'' : forall s p_v v dport P,
  OS_Port_V_coreNum dport = Some v ->
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv port_ptr ′ → coreNum @ Int8u == v.
Proof.
  intros.
  lets H2: port_coreNum_rv' H0 H1.
  assert (nth_val' 2 dport = v).
  {
    unfold OS_Port_V_coreNum in H.
    eapply nth_val_nth_val'_some_eq; eauto.
  }
  now subst.
Qed.

Lemma port_coreNum_rv : forall x s p_v dport port msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport port msgl ->
  s  |= LV x @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv x ′ → coreNum @ Int8u == Vint32 (Int.repr DNUM).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  destruct dport;destruct H as [? H];tryfalse.  destruct dport;destruct H as [? H];tryfalse.
  simpl;lia.
  unfold Domainport_nat_P in H0.
  destruct port as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
  simpljoin1.
  unfold OS_Port_V_coreNum in H0.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_OSEventType_rv : forall s p_v dport port msgl ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport port msgl ->
  (exists wt, get ecbls p_v = Some (absport, wt)) ->
  s  |= EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl **
        LV port_ptr @ OS_Port ∗ |-> Vptr p_v **
        APortStruct p_v dport ** P ->
  s |= Rv port_ptr ′ → OSEventType @ Int8u == (Vint32 ($ OS_EVENT_TYPE_PORT)).
Proof.
  intros * ? (? & ? & ?) (wt & ?) ?.
  unfold EvtInv,AECBList in H4.
  sep normal in H4. sep destruct H4. sep split in H4. subst.
  apply ECBList_P_abs_getPtrList in H5 as ?. destruct H7 as (eptrls & ?). 
  rename x1 into ectrls. rename x4 into edatals. 
  assert (exists n ectr edata,
  nth_error ectrls n = Some ectr /\
  nth_error edatals n = Some edata /\
  nth_error eptrls n = Some p_v /\
  RLH_ECBData_P edata (absport, wt)) as (n & ? & ?& ?& ?& ?& ?).
  { eapply ECBList_P_abs_getsome;eauto.  }
  apply nth_error_split in H14 as (ectrls1 & ectrls2 & ? & ?).
  apply nth_error_split in H15 as (edatals1 & edatals2 & ? & ?).
  subst ectrls edatals.
  sep name lift evsllseg in H4.
  eapply evsllseg_app'_frm with (n := n)in H4;eauto.
  cbn [evsllseg] in H4.
  destruct x1 as [[? ?] ?].
  sep normal in H4. sep destruct H4. sep split in H4.
  unfold AEventNode, AOSEvent, node, Astruct in H4.
  sep normal in H4. sep destruct H4. sep split in H4.
  simpljoin1.
  unfold OS_EVENT in H26.
  unfold OS_EVENT in H4 at 1.
  inverts H15.
  eapply struct_member_rv_typeneq_addrneq with (l := (x23, Int.zero)) (i := 0) (m := 0%nat); eauto.
  {
    sep name lift port_ptr in H4.
    unfold get_off_addr.
    simpl fst. simpl snd.
    assert (Int.zero +ᵢ  $ 0 = Int.zero) by apply Int.add_zero.
    rewrite H15.
    apply H4.
  }
  { cbn; go. }
  { cbn; go. }
  { clear; mauto. }
  { cbn; go. }
  { cbn; go. }
  {
    destruct v; tryfalse.
    simpl; lia.
  }
  unfold AEventData in H4.
  destruct x4; sep normal in H4; sep destruct H4; sep split in H4;
  unfold RLH_ECBData_P in H17; tryfalse.
  unfold V_OSEventType in H15.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_domain_rv : forall s pptr p p0 p1 d p2 p3 p4 p5 dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, p5) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → domain @ Int32u == (Vint32 ($ (Z.of_nat p0))).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  { cbn; go. }
  { cbn; go. }
  { cbn; lia. }
  { clear; mauto. }
  { cbn; auto. }
  { cbn; eauto. }
  { 
    destruct dport; tryfalse.
    simpl; lia.
  }
  unfold Domainport_nat_P in H0.
  simpljoin1.
  unfold OS_Port_V_domain in H5.
  eapply nth_val_nth_val'_some_eq in H5.
  rewrite H5; f_equal.
  pose proof unsigned_to_z_eq x; rewrite H4.
  pose proof Int.unsigned_range_2 x; destruct H6.
  pose proof Z2Nat.id (Int.unsigned x) H6; rewrite H11.
  pose proof Int.repr_unsigned x; auto.
Qed.

Lemma tcbcur_OSTCBY_rv:
  forall s tcbls tid x x0 x1 x2 v v0 tcbl1 tcbcur tcbl2 rtbl P ls,
    get tcbls tid = Some (x, x0, x1, x2) ->
    symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
    s |=
      A_dom_lenv ls **
      AOSTCBList v v0 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls ** P ->
    s |= Rv OSTCBCur ′ → OSTCBY @ Int8u == (Vint32 (x >>ᵢ $ 3)).
Proof.
  intros.
  unfold AOSTCBList in H1.
  sep normal in H1; sep destruct H1; sep split in H1.
  destruct H2; subst.
  cbn [TCBList_P] in H5.
  destruct H5 as [? [? [? [? [? [? [? [? ?]]]]]]]].
  inverts H5; rename x7 into tid.
  unfold TcbJoin in H8.
  assert (get x6 tid = Some x10).
  { eapply join_sig_get; eauto. }
  destruct x10 as [[[? ?] ?] ?].
  assert (get tcbls tid = Some (p, t, m, s0)).
  { eapply join_get_get_r; eauto. }
  unfold priority in H11.
  rewrite H in H11; inverts H11.
  unfold tcbdllseg in H1.
  cbn [dllseg] in H1; unfold node in H1.
  sep normal in H1; sep destruct H1; sep split in H1.
  destruct H11; inverts H11.
  eapply symbolic_lemmas.struct_member_rv_g_typeneq.
  {
    sep split; eauto.
    sep lifts (5::nil)%nat in H1.
    apply H1.
  }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { cbn; go. }
  { 
    destruct tcbcur; tryfalse.
    do 9 (destruct tcbcur; destruct H15 as [? H15]; tryfalse).
    simpl; lia.
  }
  { auto. }
  unfold TCBNode_P, RL_TCBblk_P in H9.
  simpljoin1.
  rewrite H11 in H16; inverts H16.
  unfold V_OSTCBY in H19.
  eapply nth_val_nth_val'_some_eq; eauto.
Qed.

Lemma tcby_port_domain_rv_abt :
  forall s ls tcbls tid x x0 x1 x2 dportls pptr p p0 p1 d p2 p3 p4 p5 v v0 tcbl1 tcbcur tcbl2 rtbl dport msg P,
    get tcbls tid = Some (x, x0, x1, x2) ->
    get dportls pptr = Some (p, p0, p1, d, p2, p3, p4, p5) ->
    struct_type_vallist_match' OS_Port_Seg_dls dport ->
    DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, p5) msg ->
    Int.eq (x >>ᵢ $ 3) ($ Z.of_nat p0) = false ->
    symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
    s |=
      APortStruct pptr dport **
      LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
      AOSTCBList v v0 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls **
      A_dom_lenv ls ** P ->
    s |= Rv OSTCBCur ′ → OSTCBY ==ₑ port_ptr ′ → domain @ long == (Vint32 Int.zero).
Proof.
  intros.
  assert (s |= Rv port_ptr ′ → domain @ long == (V$ Z.of_nat p0)).
  {
    eapply port_domain_rv; eauto.
    sep name lift APortStruct; apply H5.
  }
  assert (s |= Rv OSTCBCur ′ → OSTCBY @ char_t == Vint32 (x >>ᵢ $ 3)).
  {
    eapply tcbcur_OSTCBY_rv; eauto.
    sep lifts (4::3::nil)%nat in H5; apply H5.
  }
  eapply symbolic_lemmas.bop_rv; eauto.
  { simpl; rewrite H3; auto. }
Qed.

Lemma tcby_port_domain_rv_con :
  forall s ls tcbls tid x x0 x1 x2 dportls pptr p p0 p1 d p2 p3 p4 p5 v v0 tcbl1 tcbcur tcbl2 rtbl dport msg P,
    get tcbls tid = Some (x, x0, x1, x2) ->
    get dportls pptr = Some (p, p0, p1, d, p2, p3, p4, p5) ->
    struct_type_vallist_match' OS_Port_Seg_dls dport ->
    DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, p5) msg ->
    Int.eq (x >>ᵢ $ 3) ($ Z.of_nat p0) = true ->
    symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
    s |=
      APortStruct pptr dport **
      LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
      AOSTCBList v v0 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls **
      A_dom_lenv ls ** P ->
    s |= Rv OSTCBCur ′ → OSTCBY ==ₑ port_ptr ′ → domain @ long == (Vint32 Int.one).
Proof.
  intros.
  assert (s |= Rv port_ptr ′ → domain @ long == (V$ Z.of_nat p0)).
  {
    eapply port_domain_rv; eauto.
    sep name lift APortStruct; apply H5.
  }
  assert (s |= Rv OSTCBCur ′ → OSTCBY @ char_t == Vint32 (x >>ᵢ $ 3)).
  {
    eapply tcbcur_OSTCBY_rv; eauto.
    sep lifts (4::3::nil)%nat in H5; apply H5.
  }
  eapply symbolic_lemmas.bop_rv; eauto.
  { simpl; rewrite H3; auto. }
Qed.

Lemma tcby_port_domain_rv :
  forall s ls tcbls tid x x0 x1 x2 dportls pptr p p0 p1 d p2 p3 p4 p5 v v0 tcbl1 tcbcur tcbl2 rtbl dport msg P,
    get tcbls tid = Some (x, x0, x1, x2) ->
    get dportls pptr = Some (p, p0, p1, d, p2, p3, p4, p5) ->
    struct_type_vallist_match' OS_Port_Seg_dls dport ->
    DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, p5) msg ->
    symbolic_lemmas.var_notin_dom OSTCBCur ls = true ->
    s |=
      APortStruct pptr dport **
      LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
      AOSTCBList v v0 tcbl1 (tcbcur :: tcbl2) rtbl tid tcbls **
      A_dom_lenv ls ** P ->
    s |= Rv OSTCBCur ′ → OSTCBY ==ₑ port_ptr ′ → domain @ long == val_inj (val_eq (Vint32 (x >>ᵢ $ 3)) (Vint32 (Int.repr (Z.of_nat p0)))).
Proof.
  intros; cbn [val_eq].
  destruct (Int.eq (x >>ᵢ $ 3) ($ Z.of_nat p0)) eqn: Heq.
  {
    cbn [val_inj].
    eapply tcby_port_domain_rv_con; eauto.
  }
  cbn [val_inj].
  eapply tcby_port_domain_rv_abt; eauto.
Qed.

Lemma port_direction_rv_source : forall s pptr p p0 p1 p2 p3 p4 p5 dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, SourceP, p2, p3, p4, p5) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → os_code_defs.direction @ long == (Vint32 ($ SOURCE)).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 4 (destruct dport;destruct H as [? H];tryfalse).
  simpl;lia.
  unfold Domainport_direction_P in H1.
  unfold OS_Port_V_direction in H1.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_direction_rv_destination : forall s pptr p p0 p1 p2 p3 p4 p5 dport nextdst msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, DestinationP nextdst, p2, p3, p4, p5) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → os_code_defs.direction @ long == (Vint32 ($ DESTINATION)).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 4 (destruct dport;destruct H as [? H];tryfalse).
  simpl;lia.
  unfold Domainport_direction_P in H1.
  unfold OS_Port_V_direction in H1.
  eapply nth_val_nth_val'_some_eq;tauto.
Qed.

Lemma port_direction_rv : forall s pptr p p0 p1 pdir p2 p3 p4 p5 dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, pdir, p2, p3, p4, p5) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → os_code_defs.direction @ long == (Vint32 ($ (match pdir with| SourceP => SOURCE | DestinationP nextdst => DESTINATION end))).
Proof.
  intros.
  destruct pdir.
  eapply port_direction_rv_source;eauto.
  eapply port_direction_rv_destination;eauto.
Qed.


Lemma port_mode_rv : forall s pptr p p0 p1 d p2 p3 p4 pt dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, pt) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → mode @ long == (Vint32 ($ (match pt with| SamplePort _ => SAMPLE | QueuePort _ _ => QUEUE end))).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 5 (destruct dport;destruct H as [? H];tryfalse).
  simpl;lia.
  unfold Domainport_Portt_P in H2.
  destruct pt.
  -  destruct H2 as  (? & ? & ? & ?).
  unfold OS_Port_V_direction in H5.
  eapply nth_val_nth_val'_some_eq;eauto.
  -  destruct H2 as  (? & ? & ? ).
  unfold OS_Port_V_direction in H5.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_id_rv : forall s pptr p p0 p1 d p2 p3 p4 pt dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, pt) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → portID @ long == (Vint32 ($ (Z.of_nat p1))).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 5 (destruct dport;destruct H as [? H];tryfalse).
  simpl;lia.
  unfold Domainport_nat_P in H0.
  simpljoin1.
  unfold OS_Port_V_portID in H7.
  eapply nth_val_nth_val'_some_eq;eauto.
  rewrite H7.
  f_equal.
  rewrite unsigned_to_z_eq.
  rewrite Z2Nat.id.
  { rewrite Int.repr_unsigned; auto. }
  apply Int.unsigned_range_2.
Qed.

Lemma port_msgInTick_rv : forall s pptr p p0 p1 d p2 p3 p4 pt dport msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  DomainportNode_P dport (p, p0, p1, d, p2, p3, p4, pt) msgl ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → msgInTick @ long == (Vint32 (Int.repr (Z.of_nat p3))).
Proof.
  intros * ? (? & ? & ?) ?.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 8 (destruct dport;destruct H as [? H];tryfalse).
  simpl;lia.
  unfold Domainport_nat_P in H0.
  simpljoin1.
  unfold OS_Port_V_msgInTick in H12.
  eapply nth_val_nth_val'_some_eq;eauto.
  rewrite H12.
  f_equal.
  rewrite unsigned_to_z_eq.
  rewrite Z2Nat.id.
  { rewrite Int.repr_unsigned; auto. }
  apply Int.unsigned_range_2.
Qed.

Lemma kport_channel_rv:
  forall s kpptr kport P,
  struct_type_vallist_match OS_K_Port kport ->
  s |=  LV os_code_defs.kport @ OS_K_Port ∗ |-> Vptr kpptr **
        Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv os_code_defs.kport ′ → os_code_defs.channel @ (Void) ∗ == nth_val' 3 kport.
Proof.
  intros.
  eapply symbolic_lemmas.struct_member_rv_typeneq with (n:=3%nat) (vl:=(firstn 6 kport)); eauto.
  unfold Astruct; eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  {
    unfold OS_K_Port in H; simpl in H.
    unfold struct_type_vallist_match' in H.
    destruct kport; tryfalse.
    do 3 (destruct H as [? H]; destruct kport; tryfalse).
    simpl; lia.
  }
  apply AKPortStructType_split; auto.
  unfold OS_K_Port in H; simpl in H.
  unfold struct_type_vallist_match' in H.
  destruct kport; tryfalse.
  do 3 (destruct H as [? H]; destruct kport; tryfalse).
  simpl; auto.
  Unshelve. 
  exact (1).
Qed.

Lemma cslsemacc_rule' : forall  Spec sd  I r ri p e1 v1 n aop0 aop1 pa t,
forall x,
   can_change_aop p ->
   (Z.of_nat n <= Int.max_unsigned)%Z ->
   (LV x @ char_t |-> v1 ** p) ==> Rv e1 @ Tint8 == Vint32 ((Int.repr (Z.of_nat n)))  ->
   (LV x @ char_t |-> Vint32 Int.zero ** p)  ==> CurLINV pa t ->
   (LV x @ char_t |-> Vint32 Int.one ** p)  ==> CurLINV pa t ->
   {|Spec, sd, pa, I, r, ri|}|- t
   {{ <|| cslsemacc n (Vint32 Int.zero);; aop0 ?? cslsemacc n (Vint32 Int.one);; aop1 ||>  **
     LV x @ char_t |-> v1 ** p}} CSLSEMACC (e1, (evar x))
   {{ <|| aop0 ||>  ** LV x @ char_t |-> Vint32 Int.zero ** p \\//
      <|| aop1 ||>  ** LV x @ char_t |-> Vint32 Int.one ** p }}.
Proof.
  intros.
  unfold Alvarmapsto.
  pure intro.
  hoare remember (2:: 3:: nil)%nat pre.
  hoare lifts (2::3::nil)%nat pre.
  eapply forward_rule2.
  eapply cslsemacc_rule;eauto.
  { subst. can_change_aop_solver. }
  { subst. intros. split.
    eapply H1. unfold Alvarmapsto. sep pauto.
    sep normal in H4.
    eapply symbolic_lemmas.addrof_lvar_rv in H4.
    eapply addrof_rv_to_lv in H4.
    eauto. }
  { subst. intros.
    eapply H2.  unfold Alvarmapsto. sep pauto. }
  { subst. intros.
    eapply H3.  unfold Alvarmapsto. sep pauto. }
  intros.
  destruct H5.
  left. subst. sep autocancel. sep eexists. sep pauto.
  right. subst. sep autocancel. sep eexists. sep pauto.
Qed.

Lemma port_QEntries_rv : forall x s pptr qentries dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQEntries dport = Some (Vint32 qentries) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv x ′ → OSQEntries @ Int16u == (Vint32 qentries).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 17 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_QSize_rv : forall s pptr qsize dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQSize dport = Some (Vint32 qsize) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → OSQSize @ Int16u == (Vint32 qsize).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 16 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma assign_rule_struct_member : 
forall Spec I r ri  p p' x id e tid decl l off vi v tp1 t' tp2 aop sc li ct perm ,
  good_decllist decl = true ->
  p <==>  LV x @ (Tptr tp1) |=> Vptr l @ perm ** PV (get_off_addr l off) @ t' |-> vi  ** p' ->
  tp1 = Tstruct tid decl ->
  ftype id decl = Some t' ->
  field_offset id decl = Some off->
  rule_type_val_match t' v = true ->
  assign_type_match t' tp2 ->
  p ==>  Rv e @ tp2 == v ->
  LV x @ (Tptr tp1) |=> Vptr l @ perm ** PV (get_off_addr l off) @ t' |-> v ** p' ==>
     EX lg : list logicvar, p_local li ct lg ** Atrue ->
  {| Spec, sc, li, I, r, ri |} |-ct {{ <|| aop ||> ** p }} (sassign (efield (ederef (evar x)) id) e)  
                                    {{(LV x @ (Tptr tp1) |=> Vptr l @ perm ** PV (get_off_addr l off) @ t' |-> v ** p' ** <|| aop ||>)}}.
Proof.
  intros.
  rewrite H1 in *.
  destruct l as (b&i).
  assert ((LV x @ (STRUCT tid ­{ decl }­) ∗ |=> Vptr (b, i) @ perm **
          PV get_off_addr (b, i) off @ t' |-> vi ** p')
        ==> (Lv (efield (ederef (evar x)) id) @ t' == (b,Int.add i off))).
  { eapply symbolic_lemmas.field_asrt_impl with (b:=b) (i:=i);eauto. }
  assert (p ==> (Lv (efield (ederef (evar x)) id) @ t' == (b,Int.add i off))).  
  { eapply eq_impl_trans;eauto. }
  assert (p <==>
          PV (b, i +ᵢ  off) @ t' |-> vi **
          LV x @ (STRUCT tid ­{ decl }­) ∗ |=> Vptr (b, i) @ perm ** p').
  { eapply asrt_eq_trans;eauto.
    split;intros.
    sep auto.
    sep auto. }
  unfold get_off_addr in * . cbn [fst snd] in *.
  assert ({|Spec , sc, li, I, r, ri|}|-ct  {{p **  <|| aop ||> }} sassign (efield (ederef (evar x)) id) e
    {{PV (b, i +ᵢ  off) @ t' |-> v  ** (LV x @ (STRUCT tid ­{ decl }­) ∗ |=> Vptr (b, i) @ perm ** p') ** <|| aop ||> }}).
  { eapply assign_rule'';eauto.
    intros.
    apply H7.
    sep auto. }
  eapply forward_rule2.
  eapply backward_rule2.
  exact H11.
  intros.
  sep auto.
  intros.
  sep auto.
Qed.

Lemma struct_member_off_rv:
  forall s e t l off tid decl id t' v P perm,
    (forall ids dl, t' <> Tstruct ids dl) ->
    (forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
    s |= Rv e @ Tptr t == Vptr l ->
    s |= PV (get_off_addr l off) @ t' |=> v @ perm ** P ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some t' ->
    field_offset id decl = Some off->
    rule_type_val_match t' v = true ->
    s |= Rv (efield (ederef e) id) @ t' == v.
Proof. 
  intros.
  assert (v<> Vundef) as Hvn.
  { eapply symbolic_lemmas.rule_type_val_match_nvundef;eauto. }
  destruct s as ((o&O)&aop).
  unfold sat in *;fold sat in *;DeprecatedTactic.mytac.
  { unfold substmo in *.
  destruct o as [[[[[]]]]].
  unfold substaskst in *.
  unfold getsmem in *.
  unfold getmem in *.
  unfold get_smem in *.
  unfold get_mem in *.
  simpl in *;DeprecatedTactic.mytac.
  rewrite H13.
  rewrite H5.
  rewrite H1.
  destruct l.
  unfold getoff.
  cbn [ evaltype].
  rewrite H13.
  rewrite H6.
  cbn [fst snd] in *.
  unfold addrval_to_addr.
  rewrite Int.repr_unsigned.
  eapply symbolic_lemmas.load_local;eauto.
  eapply symbolic_lemmas.mapstoval_load;eauto. }
  2: auto.
  destruct o as [[[[[]]]]].
  simpl in *;DeprecatedTactic.mytac.
  rewrite H13.
  auto.
Qed.

Lemma struct_member_array_rv:
  forall s e t l tid decl id t' n ad ,
    s |= Rv e @ Tptr t == Vptr l ->
    t = Tstruct tid decl ->
    good_decllist decl = true ->
    ftype id decl = Some (Tarray t' n) ->
    id_addrval l id t = Some ad ->
    s |= Rv (efield (ederef e) id) @ (Tarray t' n) == Vptr ad.
Proof. 
  intros.
  destruct_s s.
  simpl in *;DeprecatedTactic.mytac.
  destruct l as (b&pi).
  { rewrite H4.
  rewrite H2.
  rewrite H.
  unfold getoff.
  cbn.
  rewrite H4.
  unfold id_addrval in H3.
  remember (field_offset id decl ) as X.
  destruct X;tryfalse.
  rewrite Int.repr_unsigned.
  simpl.
  rewrite Int.repr_unsigned.
  inverts H3;auto. }
  rewrite H4.
  auto.
  intro; tryfalse.
Qed.

Lemma port_QOut_rv : forall x s pptr qout dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv x ′ → OSQOut @ (Tptr OSMsg_t) == (Vptr qout).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_OSQOut_len_rv' : forall  x s pptr dport qout z P,
  0 <= z <= CHANNEL_CACHE_SZIE ->
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qout @ char_t |-> (Vint32 ($ z)) ** P ->
  s |= Rv (x ′ → OSQOut) → len @ char_t == (Vint32 ($ z)).
Proof.
  intros.
  destruct qout as [qout_b qout_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H0.
  eapply struct_member_off_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H1;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  { instantiate (3:= Int.zero).
    unfold get_off_addr.  cbn [fst snd] in *.
    rewrite Int.add_zero.
    sep auto. }
  cbn. auto.
  cbn. auto.
  cbn. auto.
  cbn. clear - H. unfold CHANNEL_CACHE_SZIE in *. 
  rewrite Int.unsigned_repr.
  assert ( z <=? 255 = true) by lia. rewrite H0. auto.
  mauto.
Qed.

Lemma port_OSQOut_data_rv' : forall x s pptr dport qout z P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qout @ char_t |-> (Vint32 ($ z)) ** P ->
  s  |= Rv (x ′ → OSQOut) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qout, (snd qout) +ᵢ Int.one).
Proof.
  intros.
  destruct qout as [qout_b qout_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  cbn. auto.
  cbn. auto.
  cbn. auto.
Qed.

Lemma port_OSQOut_len_rv : forall x s pptr dport qout qin qstart qend n msg msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        dmportp_sllseg_qport_msg qout qin qstart qend n (msg :: msgl) ** P ->
  s |= Rv (x ′ → OSQOut) → len @ char_t == (Vint32 ($ (Z.of_nat (length msg)))).
Proof.
  intros.
  destruct n.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    sep name lift Afalse in H1.
    eapply astar_l_afalse_elim in H1.
    tryfalse. }
  destruct qout as [qout_b qout_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_off_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    instantiate (3:= Int.zero).
    unfold get_off_addr.  cbn [fst snd] in *.
    rewrite Int.add_zero.
    sep name lift (Aptrmapsto (qout_b, qout_i)) in H1.
    exact H1. }
  cbn. auto.
  cbn. auto.
  cbn. auto.
  cbn [dmportp_sllseg_qport_msg] in H1.
  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  clear- H2.
  cbn.
  unfold CHANNEL_CACHE_SZIE in H2.
  rewrite <- Zabs2Nat.abs_nat_nonneg in H2. 2: lia.
  assert (0 <= (length msg) <= 32)%nat by lia. clear H2.
  rewrite Int.unsigned_repr by mauto.
  assert (Z.of_nat (length msg) <=? 255 = true) by lia.
  rewrite H0.
  auto.
Qed.

Lemma port_OSQOut_data_rv : forall s pptr dport qout qin qstart qend n msg msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQOut dport = Some (Vptr qout) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        dmportp_sllseg_qport_msg qout qin qstart qend n (msg :: msgl) ** P ->
  s  |= Rv (port_ptr ′ → OSQOut) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qout, (snd qout) +ᵢ Int.one).
Proof.
  intros.
  destruct n.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    sep name lift Afalse in H1.
    eapply astar_l_afalse_elim in H1.
    tryfalse. }
  cbn [dmportp_sllseg_qport_msg] in H1.
  destruct qout as [qout_b qout_i].
  cbn [fst snd] in *.
  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  sep name lift APortStruct in H1.
  sep name lift (Alvarmapsto) in H1. 
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  cbn. auto.
  cbn. auto.
  cbn. rewrite Int.add_zero. auto.
Qed.

Lemma port_OSQStart_data_rv : forall s pptr dport qstart P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQStart dport = Some (Vptr qstart) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        (* PV (fst qstart, snd qstart +ᵢ  Int.zero) @ char_t |-> len ** *)
        (* Aarray' (get_off_addr qstart Int.one) ∘ CHANNEL_CACHE_SZIE char_t (v'1 ++ v'3) ** *)
        P ->
  s  |= Rv (port_ptr ′ → OSQStart) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qstart, (snd qstart) +ᵢ Int.one).
Proof.
  intros.
  (* unfold dmportp_sllseg_sampleport_msg in H1. *)
  destruct qstart as [qstart_b qstart_i].
  cbn [fst snd] in *.
  (* sep normal in H1. *)
  (* sep destruct H1. *)
  (* sep split in H1. *)
  (* inverts H3. *)
  sep name lift APortStruct in H1.
  sep name lift (Alvarmapsto) in H1. 
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 12 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  cbn. auto.
  cbn. auto.
  cbn. rewrite Int.add_zero. auto.
Qed.

Lemma port_QEnd_rv : forall x s pptr qend dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQEnd dport = Some (Vptr qend) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv x ′ → OSQEnd @ (Tptr OSMsg_t) == (Vptr qend).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 13 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_QStart_rv : forall x s pptr qstart dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQStart dport = Some (Vptr qstart) ->
  s  |= LV x @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv x ′ → OSQStart @ (Tptr OSMsg_t) == (Vptr qstart).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 12 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_QStart_rv' : forall s pptr dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  (* OS_Port_V_OSQStart dport = Some (Vptr qstart) -> *)
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → OSQStart @ (Tptr OSMsg_t) == nth_val' 12 dport.
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport; simpl in H; tryfalse. 
  do 12 (destruct H as [? H];destruct dport;simpl in H;tryfalse).
  simpl;lia.
Qed.

Lemma port_QIn_rv : forall s pptr qinptr dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qinptr) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → OSQIn @ (Tptr OSMsg_t) == (Vptr qinptr).
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  destruct dport;tryfalse. 
  do 14 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.


Lemma port_OSQIn_len_rv : forall s pptr dport qout qin qstart qend n msg msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qin) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        dmportp_sllseg_qport_msg qin qout qstart qend n (msg :: msgl) ** P ->
  s |= Rv (port_ptr ′ → OSQIn) → len @ char_t == (Vint32 ($ (Z.of_nat (length msg)))).
Proof.
  intros.
  destruct n.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    sep name lift Afalse in H1.
    eapply astar_l_afalse_elim in H1.
    tryfalse. }
  destruct qin as [qin_b qin_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_off_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  destruct dport;tryfalse. 
  do 14 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    instantiate (3:= Int.zero).
    unfold get_off_addr.  cbn [fst snd] in *.
    rewrite Int.add_zero.
    sep name lift (Aptrmapsto (qin_b, qin_i)) in H1.
    exact H1. }
  all: try reflexivity.
  cbn.
  cbn [dmportp_sllseg_qport_msg] in H1.
  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  clear- H2.
  unfold CHANNEL_CACHE_SZIE in H2.
  rewrite <- Zabs2Nat.abs_nat_nonneg in H2. 2: lia.
  assert (0 <= (length msg) <= 32)%nat by lia. clear H2.
  rewrite Int.unsigned_repr by mauto.
  assert (Z.of_nat (length msg) <=? 255 = true) by lia.
  now rewrite H0.
Qed.

Lemma port_OSQIn_len_rv' : forall s pptr dport qin z P,
  0 <= Int.unsigned z <= CHANNEL_CACHE_SZIE ->
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qin) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qin @ char_t |-> (Vint32 z) ** P ->
  s |= Rv (port_ptr ′ → OSQIn) → len @ char_t == (Vint32 z).
Proof.
  intros.
  destruct qin as [qin_b qin_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H0.
  eapply struct_member_off_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  destruct dport;tryfalse. 
  do 14 (destruct dport;simpl in H1;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto; try reflexivity.
  { instantiate (3:= Int.zero).
    unfold get_off_addr.  cbn [fst snd] in *.
    rewrite Int.add_zero.
    sep auto. }
  all: try reflexivity.
  cbn. clear - H. unfold CHANNEL_CACHE_SZIE in *. 
  assert ( Int.unsigned z <=? 255 = true) by lia. rewrite H0. auto.
Qed.

Lemma port_OSQIn_data_rv : forall s pptr dport qout qin qstart qend n msg msgl P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qin) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        dmportp_sllseg_qport_msg qin qout qstart qend n (msg :: msgl) ** P ->
  s  |= Rv (port_ptr ′ → OSQIn) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qin, (snd qin) +ᵢ Int.one).
Proof.
  intros.
  destruct n.
  { cbn [dmportp_sllseg_qport_msg] in H1.
    sep name lift Afalse in H1.
    eapply astar_l_afalse_elim in H1.
    tryfalse. }
  cbn [dmportp_sllseg_qport_msg] in H1.
  destruct qin as [qin_b qin_i].
  cbn [fst snd] in *.
  sep normal in H1.
  sep destruct H1.
  sep split in H1.
  sep name lift APortStruct in H1.
  sep name lift (Alvarmapsto) in H1. 
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  destruct dport;tryfalse. 
  do 14 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  all: reflexivity.
Qed.

Lemma port_OSQIn_data_rv' : forall s pptr dport qin z P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQIn dport = Some (Vptr qin) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qin @ char_t |-> (Vint32 z) ** P ->
  s  |= Rv (port_ptr ′ → OSQIn) → data @ (Tarray Int8u ∘CHANNEL_CACHE_SZIE) == Vptr (fst qin, (snd qin) +ᵢ Int.one).
Proof.
  intros.
  destruct qin as [qin_b qin_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_array_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto; try reflexivity.
  clear. mauto.
  do 15 (destruct dport;simpl in H0;tryfalse).
  simpl; lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  all: reflexivity.
Qed.

Theorem cast_rv_tint8_tint32 :
  forall s e v,
    s |= Rv e @ Tint8 == (Vint32 v) ->
    s |= Rv (ecast e (Tint32)) @ (Tint32) == (Vint32 v).
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H.
  simpl.
  rewrite H0.
  auto.
  simpl.
  rewrite H0.
  auto.
Qed.

Theorem cast_rv_tint8_tint32' :
  forall s e v,
    rule_type_val_match char_t v = true ->
    s |= Rv e @ Tint8 == v ->
    s |= Rv (ecast e (Tint32)) @ (Tint32) == v.
Proof.
  intros.
  unfold rule_type_val_match in H.
  destruct v; tryfalse.
  eapply cast_rv_tint8_tint32.
  auto.
Qed.

Theorem cast_rv_tint32_tint16 :
  forall s e v v',
    s |= Rv e @ Tint32 == (Vint32 v) ->
    cast_eval v Tint32 Tint16 = Some v' ->
    s |= Rv (ecast e (Tint16)) @ (Tint16) == (Vint32 v').
Proof.
  intros.
  unfold sat;fold sat.
  destruct_s s.
  simpl in H.
  destructs H.
  splits;auto.
  simpl.
  rewrite H1.
  auto.
  simpl.
  rewrite H.
  simpl in H0.
  inverts H0.
  auto.
  simpl.
  rewrite H1.

  auto.
Qed.


Lemma port_memeber_asgn  : forall 
r ri aop (p p':asrt ) (tid: tid) pptr dport e tp2 v' v n t' id ,
p <==> LV port_ptr @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr dport ** p' ->
p ==>  Rv e @ tp2 == v ->
nth_id n OS_Port_Seg_dls = Some id ->
nth_val n dport = Some v' -> 
ftype id OS_Port_Seg_dls = Some t' ->
(forall (ids : ident) (dl : decllist), t' <> STRUCT ids ­{ dl }­) ->
(forall (ids : ident) (dl : decllist), t' <> Tunion ids dl ) ->
(forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
assign_type_match t' tp2 ->
rule_type_val_match t' v = true ->
LV port_ptr @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' ==>
       EX lg : list logicvar, p_local OSLInv tid lg ** Atrue ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  ** p }} 
  port_ptr ′ → id =ₑ e
{{  <|| aop ||> ** LV port_ptr @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' }}.
Proof.
  intros * H H0 H1 H2 H3 H4 H4'. intros.
  unfold APortStruct in *.
  lets Hoff: symbolic_lemmas.nth_id_exists_off H1.
  destruct Hoff as (off&Hoff).
  destruct pptr as (b&i).
  assert (p <==> PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v' **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV port_ptr @ OS_Port ∗ |-> Vptr (b, i) ** p').
  {  assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v' ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id).
  { eapply symbolic_lemmas.struct_asrt_eq;eauto. }
  eapply asrt_eq_trans;eauto.
  split.
  intros.
  sep name lift Astruct' in H10.
  eapply astar_mono in H10.
  2: apply H9.
  2: intros s' Hs';exact Hs'.
  sep auto. 
  intros.
  sep name lift Astruct'.
  eapply astar_mono.
  apply H9. instantiate (1:=LV port_ptr @ OS_Port ∗ |-> Vptr (b, i) ** p'). sep auto.
  sep auto. }
  clear H.
  assert (PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV port_ptr @ OS_Port ∗ |-> Vptr (b, i) ** p' ==> EX lg : list logicvar, p_local OSLInv tid lg ** Atrue).
  { intros. apply H8.
    assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) id).
    { eapply symbolic_lemmas.struct_asrt_eq;eauto. eapply update_nth;eauto. }
    sep name lift Astruct_rm in H.
    eapply astar_mono in H.
    2: { intros. eapply symbolic_lemmas.struct_rm_update_eq in H11;eauto. }
    2: { intros s' Hs';exact Hs'. }
    sep auto.
    apply H10.
    sep auto. }
  eapply backward_rule1.
  { eapply astar_mono. intros s Hs;exact Hs. apply H9. }
  eapply forward_rule2.
  eapply assign_rule_general.
  { intros.
  eapply symbolic_lemmas.struct_offset_rv.
  eapply symbolic_lemmas.addrof_deref_rv.
  symbolic_execution.
  unfold OS_Port. eauto.
  unfold field_offset in *. 
  rewrite <- (Int.add_zero Int.zero).
  eapply sub_decllist_skipn_offsetfld with (n:= 8%nat);eauto.
  cbn. auto.
  { clear - H1. 
    do 18 (destruct n;[simpl in H1;inverts H1;cbn;auto | ]).
    destruct n.
    simpl in H1. inversion H1. simpl in H1. inversion H1. } 
  cbn. lia.
  clear - H3 H1.
  do 18 (destruct n;[simpl in H1;inverts H1;simpl in H3;inverts H3;cbn;auto  | ]).
  destruct n.
  simpl in H1. inversion H1. simpl in H1. inversion H1.  }
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  reflexivity. }
  { intros. apply H9 in H10. apply H0. auto. }
  auto.
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros. apply H in H10. auto. }
  unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros.
  sep auto.
  eapply symbolic_lemmas.struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply symbolic_lemmas.struct_rm_update_eq;eauto.
Qed.

Lemma dstKPort_dmport_rv:
  forall s kpptr kport P,
  struct_type_vallist_match OS_K_Port kport ->
  s |=  LV dstKPort @ OS_K_Port ∗ |-> Vptr kpptr **
        Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv dstKPort ′ → dmport @ OS_Port ∗ == nth_val' 2 kport.
Proof.
  intros.
  eapply symbolic_lemmas.struct_member_rv_typeneq with (n:=2%nat) (vl:=(firstn 6 kport)); eauto.
  unfold Astruct; eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  {
    unfold OS_K_Port in H; simpl in H.
    unfold struct_type_vallist_match' in H.
    destruct kport; tryfalse.
    do 2 (destruct H as [? H]; destruct kport; tryfalse).
    simpl; lia.
  }
  apply AKPortStructType_split; auto.
  unfold OS_K_Port in H; simpl in H.
  unfold struct_type_vallist_match' in H.
  destruct kport; tryfalse.
  do 3 (destruct H as [? H]; destruct kport; tryfalse).
  simpl; auto.
  Unshelve. 
  exact (1).
Qed.

Lemma KPort_coreNum_rv:
  forall x s kpptr kport P,
  struct_type_vallist_match OS_K_Port kport ->
  s |=  LV x @ OS_K_Port ∗ |-> Vptr kpptr **
        Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv x ′ → coreNum @ char_t == nth_val' 4 kport.
Proof.
  intros.
  eapply symbolic_lemmas.struct_member_rv_typeneq with (n:=4%nat) (vl:=(firstn 6 kport)); eauto.
  unfold Astruct; eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  {
    unfold OS_K_Port in H; simpl in H.
    unfold struct_type_vallist_match' in H.
    destruct kport; tryfalse.
    do 4 (destruct H as [? H]; destruct kport; tryfalse).
    simpl; lia.
  }
  apply AKPortStructType_split; auto.
  unfold OS_K_Port in H; simpl in H.
  unfold struct_type_vallist_match' in H.
  destruct kport; tryfalse.
  do 5 (destruct H as [? H]; destruct kport; tryfalse).
  simpl; auto.
  Unshelve. 
  exact x.
Qed.

Lemma KPort_coreNum_rv_kportnode:
  forall x s kportvl kportl n kpptr kport P,
  struct_type_vallist_match OS_K_Port kport ->
  nth_error kportvl n = Some (Vptr kpptr) ->
  nth_error kportl n = Some kport ->
  s |=  LV x @ OS_K_Port ∗ |-> Vptr kpptr **
        kportNode_P kportvl kportl  ** P ->
  s |= Rv x ′ → coreNum @ char_t == nth_val' 4 kport.
Proof.
  intros.
  sep name lift kportNode_P in H2.
  eapply kportNode_P_getsome_frm in H2;eauto.
  sep normal in H2.
  sep destruct H2.
  sep split in H2.
  eapply KPort_coreNum_rv;eauto.
  sep autocancel.
  exact H2.
Qed.

Lemma channel_srcport_dmport_rv:
  forall s chanptr chan kpptr kport P,
  struct_type_vallist_match OS_Channel chan ->
  struct_type_vallist_match OS_K_Port kport ->
  OS_Channel_V_srcPort chan = Some (Vptr kpptr) ->
  s |= LV channel @ OS_Channel ∗ |-> Vptr chanptr **
       Astruct chanptr OS_Channel chan **
       Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv (channel ′ → srcPort) → dmport @ OS_Port ∗ == nth_val' 2 kport.
Proof.
  intros.
  destruct kpptr as [kpptr_b kpptr_i].
  unfold OS_K_Port_Seg_dls in H2.
  do 7 (destruct kport as [ | ? kport];tryfalse; destruct H0 as [? H0]).
  destruct kport;simpl in H0;tryfalse.
  cbn [firstn Astruct' typelen] in H2.
  sep normal in H2.
  sep name lift (PV (kpptr_b, (kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1) @
  OS_Port ∗ |-> v1) in H2.
  assert ((kpptr_b, (kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1)  = get_off_addr (kpptr_b, kpptr_i) ($ 2)).
  { clear. unfold get_off_addr, fst, snd.
    rewrite Int.add_assoc.
    assert (($ Z.of_nat 1 +ᵢ  $ Z.of_nat 1) =  $ 2) by mauto.
    rewrite H. 
    auto. } 
  rewrite H10 in H2. clear H0.
  eapply struct_member_off_rv;eauto.
  sep name lift Astruct in H2.
  sep name lift (Alvarmapsto channel) in H2.
  eapply symbolic_lemmas.struct_member_rv;eauto.
  unfold OS_Channel;eauto.
  eauto.
  cbn. unfold OS_K_Port. eauto.
  unfold id_nth. cbn. eauto.
  {  do 7 (destruct chan as [ | ? chan];tryfalse; destruct H as [? H]).
     simpl. lia.
  }
  eapply nth_val_nth_val'_some_eq;eauto.
  eauto.
  eauto.
  eauto.
Qed.

Lemma port_OSQStart_len_rv' : forall s pptr dport qstart z P,
  0 <= z <= CHANNEL_CACHE_SZIE ->
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSQStart dport = Some (Vptr qstart) ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport **
        PV qstart @ char_t |-> (Vint32 ($ z)) ** P ->
  s |= Rv (port_ptr ′ → OSQStart) → len @ char_t == (Vint32 ($ z)).
Proof.
  intros.
  destruct qstart as [qstart_b qstart_i].
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H0.
  eapply struct_member_off_rv;eauto.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. unfold OSMsg_t. eauto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 12 (destruct dport;simpl in H1;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
  { instantiate (3:= Int.zero).
    unfold get_off_addr.  cbn [fst snd] in *.
    rewrite Int.add_zero.
    sep auto. }
  cbn. auto.
  cbn. auto.
  cbn. auto.
  cbn. clear - H. unfold CHANNEL_CACHE_SZIE in *. 
  rewrite Int.unsigned_repr.
  assert ( z <=? 255 = true) by lia. rewrite H0. auto.
  mauto.
Qed.

Lemma port_OSEventPtrPort_rv : forall s pptr qptr dport P,
  struct_type_vallist_match' OS_Port_Seg_dls dport ->
  OS_Port_V_OSEventPtrPort dport = Some qptr ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        APortStruct pptr dport ** P ->
  s |= Rv port_ptr ′ → OSEventPtrPort @ (Tptr Tvoid) == qptr.
Proof.
  intros.
  unfold APortStruct in *.
  unfold OS_Port_Seg_dls in H.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse. 
  do 10 (destruct dport;simpl in H0;tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma channel_dstPortsHead_coreNum_rv:
  forall s chanptr chan kpptr kport P,
  struct_type_vallist_match OS_Channel chan ->
  struct_type_vallist_match OS_K_Port kport ->
  OS_Channel_V_dstPortsHead chan = Some (Vptr kpptr) ->
  s |= LV channel @ OS_Channel ∗ |-> Vptr chanptr **
       Astruct chanptr OS_Channel chan **
       Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv (channel ′ → dstPortsHead) → coreNum @ Int8u == nth_val' 4 kport.
Proof.
  intros.
  destruct kpptr as [kpptr_b kpptr_i].
  unfold OS_K_Port_Seg_dls in H2.
  do 7 (destruct kport as [ | ? kport];tryfalse; destruct H0 as [? H0]).
  destruct kport;simpl in H0;tryfalse.
  cbn [firstn Astruct' typelen] in H2.
  sep normal in H2.
  sep name lift (PV (kpptr_b, (((kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
  $ Z.of_nat 4) @ char_t |-> v3) in H2.
  assert ((kpptr_b, (((kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
  $ Z.of_nat 4)  = get_off_addr (kpptr_b, kpptr_i) ($ 10)).
  { clear. unfold get_off_addr, fst, snd.
    rewrite ! Int.add_assoc.
    assert (($ Z.of_nat 1 +ᵢ  ($ Z.of_nat 1 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4))) =  $ 10) by mauto.
    rewrite H. 
    auto. } 
  rewrite H10 in H2. clear H0.
  eapply struct_member_off_rv;eauto.
  sep name lift Astruct in H2.
  sep name lift (Alvarmapsto channel) in H2.
  eapply symbolic_lemmas.struct_member_rv;eauto.
  unfold OS_Channel;eauto.
  eauto.
  cbn. unfold OS_K_Port. eauto.
  unfold id_nth. cbn. eauto.
  {  do 7 (destruct chan as [ | ? chan];tryfalse; destruct H as [? H]).
     simpl. lia.
  }
  eapply nth_val_nth_val'_some_eq;eauto.
  eauto.
  eauto.
  eauto.
Qed.

Lemma channel_srcPort_coreNum_rv:
  forall s chanptr chan kpptr kport P,
  struct_type_vallist_match OS_Channel chan ->
  struct_type_vallist_match OS_K_Port kport ->
  OS_Channel_V_srcPort chan = Some (Vptr kpptr) ->
  s |= LV channel @ OS_Channel ∗ |-> Vptr chanptr **
       Astruct chanptr OS_Channel chan **
       Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  ** P ->
  s |= Rv (channel ′ → srcPort) → coreNum @ Int8u == nth_val' 4 kport.
Proof.
  intros.
  destruct kpptr as [kpptr_b kpptr_i].
  unfold OS_K_Port_Seg_dls in H2.
  do 7 (destruct kport as [ | ? kport];tryfalse; destruct H0 as [? H0]).
  destruct kport;simpl in H0;tryfalse.
  cbn [firstn Astruct' typelen] in H2.
  sep normal in H2.
  sep name lift (PV (kpptr_b, (((kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
  $ Z.of_nat 4) @ char_t |-> v3) in H2.
  assert ((kpptr_b, (((kpptr_i +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
  $ Z.of_nat 4)  = get_off_addr (kpptr_b, kpptr_i) ($ 10)).
  { clear. unfold get_off_addr, fst, snd.
    rewrite ! Int.add_assoc.
    assert (($ Z.of_nat 1 +ᵢ  ($ Z.of_nat 1 +ᵢ  ($ Z.of_nat 4 +ᵢ  $ Z.of_nat 4))) =  $ 10) by mauto.
    rewrite H. 
    auto. } 
  rewrite H10 in H2. clear H0.
  eapply struct_member_off_rv;eauto.
  sep name lift Astruct in H2.
  sep name lift (Alvarmapsto channel) in H2.
  eapply symbolic_lemmas.struct_member_rv;eauto.
  unfold OS_Channel;eauto.
  eauto.
  cbn. unfold OS_K_Port. eauto.
  unfold id_nth. cbn. eauto.
  {  do 7 (destruct chan as [ | ? chan];tryfalse; destruct H as [? H]).
     simpl. lia.
  }
  eapply nth_val_nth_val'_some_eq;eauto.
  eauto.
  eauto.
  eauto.
Qed.

Lemma port_memeber_asgn'  : forall 
r ri aop (p p':asrt ) (tid: tid) pptr dport e tp2 v' v n t' id ptr',
p <==> LV ptr' @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr dport ** p' ->
p ==>  Rv e @ tp2 == v ->
nth_id n OS_Port_Seg_dls = Some id ->
nth_val n dport = Some v' -> 
ftype id OS_Port_Seg_dls = Some t' ->
(forall (ids : ident) (dl : decllist), t' <> STRUCT ids ­{ dl }­) ->
(forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
(forall (ids : ident) (dl : decllist), t' <> UNION ids ­{ dl }­) ->
assign_type_match t' tp2 ->
rule_type_val_match t' v = true ->
LV ptr' @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' ==>
       EX lg : list logicvar, p_local OSLInv tid lg ** Atrue ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  ** p }} 
  ptr' ′ → id =ₑ e
{{  <|| aop ||> ** LV ptr' @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' }}.
Proof.
  intros * H H0 H1 H2 H3 H4 H5 H6 H6'. intros.
  unfold APortStruct in *.
  lets Hoff: symbolic_lemmas.nth_id_exists_off H1.
  destruct Hoff as (off&Hoff).
  destruct pptr as (b&i).
  assert (p <==> PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v' **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV ptr' @ OS_Port ∗ |-> Vptr (b, i) ** p').
  {  assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v' ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id).
  { eapply symbolic_lemmas.struct_asrt_eq;eauto. }
  eapply asrt_eq_trans;eauto.
  split.
  intros.
  sep name lift Astruct' in H10.
  eapply astar_mono in H10.
  2: apply H9.
  2: intros s' Hs';exact Hs'.
  sep auto. 
  intros.
  sep name lift Astruct'.
  eapply astar_mono.
  apply H9. instantiate (1:=LV ptr' @ OS_Port ∗ |-> Vptr (b, i) ** p'). sep auto.
  sep auto. }
  clear H.
  assert (PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV ptr' @ OS_Port ∗ |-> Vptr (b, i) ** p' ==> EX lg : list logicvar, p_local OSLInv tid lg ** Atrue).
  { intros. apply H8.
    assert (Astruct' (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) <==> PV (b,Int.add (i +ᵢ  $ 29) off) @ t' |-> v ** Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls (update_nth_val n dport v) id).
    { eapply symbolic_lemmas.struct_asrt_eq;eauto. eapply update_nth;eauto. }
    sep name lift Astruct_rm in H.
    eapply astar_mono in H.
    2: { intros. eapply symbolic_lemmas.struct_rm_update_eq in H11;eauto. }
    2: { intros s' Hs';exact Hs'. }
    sep auto.
    apply H10.
    sep auto. }
  eapply backward_rule1.
  { eapply astar_mono. intros s Hs;exact Hs. apply H9. }
  eapply forward_rule2.
  eapply assign_rule_general.
  { intros.
  eapply symbolic_lemmas.struct_offset_rv.
  eapply symbolic_lemmas.addrof_deref_rv.
  symbolic_execution.
  unfold OS_Port. eauto.
  unfold field_offset in *. 
  rewrite <- (Int.add_zero Int.zero).
  eapply sub_decllist_skipn_offsetfld with (n:= 8%nat);eauto.
  cbn. auto.
  { clear - H1. 
    do 18 (destruct n;[simpl in H1;inverts H1;cbn;auto | ]).
    destruct n.
    simpl in H1. inversion H1. simpl in H1. inversion H1. } 
  cbn. lia.
  clear - H3 H1.
  do 18 (destruct n;[simpl in H1;inverts H1;simpl in H3;inverts H3;cbn;auto  | ]).
  destruct n.
  simpl in H1. inversion H1. simpl in H1. inversion H1.  }
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  reflexivity. }
  { intros. apply H9 in H10. apply H0. auto. }
  auto.
  { unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros. apply H in H10. auto. }
  unfold get_off_addr, OS_EVENT_TBL_SIZE in *.
  cbn [fst snd sum_offset typelen] in *.
  rewrite <-Zabs2Nat.abs_nat_nonneg by lia.
  assert (Z.of_nat (1 + (1 + (2 + (4 + (1 * Z.abs_nat 8 + (4 + (1 + (1 * Z.abs_nat 8 + 0))))))))= 29) by lia.
  rewrite H10;clear H10.
  rewrite Int.add_zero_l.
  rewrite <- Int.add_assoc.
  intros.
  sep auto.
  eapply symbolic_lemmas.struct_asrt_eq;eauto.
  eapply update_nth;eauto.
  sep auto.
  eapply symbolic_lemmas.struct_rm_update_eq;eauto.
Qed.