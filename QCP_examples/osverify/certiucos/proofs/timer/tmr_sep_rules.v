Require Import ucos_include.
Require Import Lia.

Open Scope code_scope.

Open Scope int_scope.

Require Import aux_pureLib.
Require Import tmr_rules.

Lemma AOSTMRList_eq_AOSTMRList_vallist: 
forall tmrl1 tmrl2 p,
  (length tmrl1 = 8)%nat ->
  (length tmrl2 = 8)%nat ->
  AOSTMRList' (tmrl1 ++ tmrl2) ** p <==> 
  AOSTMRList_vallist tmrl1 O ** AOSTMRList_vallist tmrl2 8%nat ** p.
Proof.
  split;intros.
  - sep cancel p.
    unfold AOSTMRList' in H1.
    sep destruct H1. sep split in H1.
    do 8 (destruct tmrl1;[ tryfalse| ]).
    destruct tmrl1;[ | tryfalse].
    do 8 rewrite <- app_comm_cons in H2.
    simpl ( nil ++ _) in H2.
    inversion H2. subst.
    cbn [AOSTMRList_vallist].
    sep auto.
  - sep cancel p. 
    sep split in H1.
    do 9 (destruct tmrl1;tryfalse).
    do 9 (destruct tmrl2;tryfalse).
    cbn [ AOSTMRList_vallist] in *. 
    unfold AOSTMRList'.
    sep auto.
Qed.

Lemma AOSTMRList_separate' : forall 
    q
    (i: int32)
    (v'23: list vallist),
    Int.lt ($ -1) i = true -> 
    Int.lt i ($ 16) = true ->
    AOSTMRList' v'23 ** q ==> 
    EX tmri, 
    [| nth_error v'23 (Z.to_nat (Int.unsigned i)) = Some tmri |] ** AOSTMRNode i tmri **
    AOSTMRList_exi v'23 i ** 
    [|length v'23 = 16%nat|] ** q.
Proof.
  intros.
  lets Hi : tmrid_destruct H H0.
  unfold AOSTMRList' in H1.
  sep normal in H1.
  sep destruct H1. sep split in H1.
  clear H H0.
  destruct Hi as [H | [H | [H | [H | [H | [H | [ H| [H | [H | [H | [H | [H | [H | [ H| [ H| H]]]]]]]]]]]]]]];
  rewrite H.
  all : 
  match goal with 
  | H1: context [AOSTMRNode ?i ?tmri] 
    |- context [AOSTMRNode ?i _ ] => exists tmri;
    sep cancel q;
    subst v'23; unfold AOSTMRList_exi; cbn  [ AOSTMRList_exi'];
  repeat erewrite int_usign_eq by mauto
  end;
  sep auto;
  do 16 match goal with 
  | |- context [if ( ?a =? Z.to_nat ?i)%nat then _ else _ ] => let h := fresh in 
  assert ((a =? Z.to_nat i)%nat = false) as h by mauto;rewrite h;clear h
  | |- context [if ( ?a =? Z.to_nat ?i)%nat then _ else _ ] => let h := fresh in 
  assert ((a =? Z.to_nat i)%nat = true) as h by mauto;rewrite h;clear h
  end;
  cbn [AOSTMRList_vallist];
  sep lift 16%nat;
  apply astar_l_aemp_intro;
  apply H1.
Qed.

Lemma AOSTMRList_separate : forall 
    q
    (i: int32)
    (v'23: list vallist),
    Int.ltu i ($ 16) = true ->
    AOSTMRList' v'23 ** q ==> 
    EX tmri, 
    [| nth_error v'23 (Z.to_nat (Int.unsigned i)) = Some tmri |] ** AOSTMRNode i tmri **
    AOSTMRList_exi v'23 i ** 
    [|length v'23 = 16%nat|] ** q.
Proof.
  intros.
  eapply AOSTMRList_separate';eauto.
  { apply tmri_ltmone;auto. }
  { apply tmri_lt16;auto. }
Qed.

Lemma AOSTMRList_merge' : forall 
    q
    (i: int32)
    (v'23: list vallist)
    (tmri: vallist),
    Int.lt ($ -1) i = true -> 
    Int.lt i ($ 16) = true -> 
    length v'23 = 16%nat ->
    AOSTMRNode i tmri **
    AOSTMRList_exi v'23 i ** q ==>
    AOSTMRList' (update_nth_vallist (Z.to_nat (Int.unsigned i)) v'23 tmri) ** q.
Proof.
  intros.
  sep cancel q.
  do 17 (destruct v'23;tryfalse).
  lets Hi : tmrid_destruct H H0.
  unfold AOSTMRList_exi in H2.
  cbn  [ AOSTMRList_exi'] in H2.
  clear H H0.
  unfold AOSTMRList'.
  sep normal.
  destruct Hi as [H | [H | [H | [H | [H | [H | [ H| [H | [H | [H | [H | [H | [H | [ H| [ H| H]]]]]]]]]]]]]]];
  rewrite H in *.
  all: repeat erewrite int_usign_eq in H2 by mauto;
  repeat match goal with 
  | H: context [if ( ?a =? Z.to_nat ?i)%nat then _ else _ ] |- _ => let h := fresh in 
  assert ((a =? Z.to_nat i)%nat = false) as h by mauto;rewrite h in  H;clear h
  | H: context [if ( ?a =? Z.to_nat ?i)%nat then _ else _ ] |- _ => let h := fresh in 
  assert ((a =? Z.to_nat i)%nat = true) as h by mauto;rewrite h in H;clear h
  end;
  cbn [AOSTMRList_vallist] in H2;
  apply step_prop.StarEmpER;
  sep auto.
Qed.

Lemma AOSTMRList_merge : forall 
    q
    (i: int32)
    (v'23: list vallist)
    (tmri: vallist),
    Int.ltu i ($ 16) = true -> 
    length v'23 = 16%nat ->
    AOSTMRNode i tmri **
    AOSTMRList_exi v'23 i ** q ==>
    AOSTMRList' (update_nth_vallist (Z.to_nat (Int.unsigned i)) v'23 tmri) ** q.
Proof.
  intros.
  eapply AOSTMRList_merge';eauto.
  { apply tmri_ltmone;auto. }
  { apply tmri_lt16;auto. }
Qed.


Lemma AOSTMRNode_imply_length_frm : forall i tmri p,
  AOSTMRNode i tmri ** p ==>  [| length tmri = 10%nat |] **AOSTMRNode i tmri ** p.
Proof.
  intros.
  sep split.
  sep cancel AOSTMRNode. 
  sep cancel p.
  unfold AOSTMRNode in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  rewrite H0.
  simpl.
  auto.
Qed.

(* Lemma TMRcntList_P_merge_lowl':
  forall n m tmrl lowl' lowl s p,
  (length lowl = n)%nat ->
  (length tmrl = n)%nat ->
  lowl' = map V_OSCNTLO' tmrl ->
  (n + m  < 32)%nat ->
  array_type_vallist_match Tint32 lowl ->
  s |= AOSTMRList_vallist tmrl m **
  Aarray_fixoffset tmr_off (timer_CNTLO ($ Z.of_nat m)) n Int32u lowl ** p ->
  lowl' = lowl .
Proof.
  induction n;intros.
  - destruct lowl;tryfalse. destruct tmrl;tryfalse.
    simpl. auto.
  - destruct lowl;tryfalse. destruct tmrl;tryfalse.
    destruct (timer_CNTLO ($ Z.of_nat m)) eqn :Hl.
    cbn [map V_OSCNTLO' val_inj V_OSCNTLO nth_val] in *.
    cbn [AOSTMRList_vallist Aarray_fixoffset] in *.
    assert ((b, i +ᵢ  tmr_off) = (timer_CNTLO ($ Z.of_nat (S m)))).
    { clear - Hl H2. unfold tmr_off. 
      unfold timer_CNTLO in *. destruct tmrRegsAddr.
      unfold get_off_addr in *.
      cbn [snd fst] in *.
      inversion Hl.
      assert ((Z.of_nat (S m)) = Z.of_nat m + 1)%Z by lia.
      rewrite H.
      rewrite Int.add_assoc.
      assert (($ (Z.of_nat m + 1)) = ($ Z.of_nat m) +ᵢ Int.one)
      by mauto.
      rewrite H3.
      rewrite Int.mul_add_distr_l.
      rewrite (Int.mul_commut Int.one).
      rewrite Int.mul_one.
      auto. }
    rewrite H5 in H4. clear H5.
    simpl in H,H0.
    apply eq_add_S in H,H0.
    inversion H1.
    unfold AOSTMRNode in H4.
    sep normal in H4.
    sep destruct H4. sep split in H4. subst v0 lowl'.
    rewrite Hl in H4.
    sep lifts (3::11::nil)%nat in H4.
    destruct H3 as [? ?]. destruct v;tryfalse.
    apply read_only_merge_all in H4; pauto.
    destruct H4.
    inversion H6;subst x2.
    cbn [V_OSCNTLO' val_inj V_OSCNTLO nth_val].
    sep lifts (10::11::nil)%nat in H4.
    assert (map V_OSCNTLO' tmrl = lowl).
    { eapply IHn;eauto.
      lia.  }
    rewrite H8. auto.
Qed.
 *)

(* Lemma TMRcntList_P_merge_lowl :
  forall tmrl1 tmrl2 lowl lowl' highl  p,
    TMRcntList_P tmrl2 lowl' highl ->
    array_type_vallist_match Tint32 lowl ->
    length lowl = 8%nat ->
    length tmrl1 = 8%nat ->
    length tmrl2 = 8%nat ->
    AOSTMRList' (tmrl1 ++ tmrl2) ** 
    Aarray_fixoffset tmr_off (timer_CNTLO ($ 8)) 8%nat Int32u lowl ** p ==>
    AOSTMRList' (tmrl1 ++ tmrl2) ** 
    Aarray_fixoffset tmr_off (timer_CNTLO ($ 8)) 8%nat Int32u lowl **
    [| lowl' = lowl|] ** p.
Proof. 
  intros. sep lift 3%nat.
  apply astar_l_apure_intro.
  sep auto.
  unfold TMRcntList_P in *.
  destruct H.
  clear highl H5. 
  eapply AOSTMRList_eq_AOSTMRList_vallist in H4;auto.
  sep lifts (2::3::nil)%nat in H4.
  eapply TMRcntList_P_merge_lowl' with (m:= 8%nat);eauto.
  lia.
Qed.

Lemma TMRcntList_P_merge_highl':
  forall n m tmrl highl' highl s p,
  (length highl = n)%nat ->
  (length tmrl = n)%nat ->
  highl' = map V_OSCNTHI' tmrl ->
  (n + m  < 32)%nat ->
  array_type_vallist_match Tint32 highl ->
  s |= AOSTMRList_vallist tmrl m **
  Aarray_fixoffset tmr_off (timer_CNTHI ($ Z.of_nat m)) n Int32u highl ** p ->
  highl' = highl .
Proof.
  induction n;intros.
  - destruct highl;tryfalse. destruct tmrl;tryfalse.
    simpl. auto.
  - destruct highl;tryfalse. destruct tmrl;tryfalse.
    destruct (timer_CNTHI ($ Z.of_nat m)) eqn :Hl.
    cbn [map ] in *.
    cbn [AOSTMRList_vallist Aarray_fixoffset] in *.
    assert ((b, i +ᵢ  tmr_off) = (timer_CNTHI ($ Z.of_nat (S m)))).
    { clear - Hl H2. unfold tmr_off. 
      unfold timer_CNTHI in *. destruct tmrRegsAddr.
      unfold get_off_addr in *.
      cbn [snd fst] in *.
      inversion Hl.
      assert ((Z.of_nat (S m)) = Z.of_nat m + 1)%Z by lia.
      rewrite H.
      rewrite Int.add_assoc.
      assert (($ (Z.of_nat m + 1)) = ($ Z.of_nat m) +ᵢ Int.one)
      by mauto.
      rewrite H3.
      rewrite Int.mul_add_distr_l.
      rewrite (Int.mul_commut Int.one).
      rewrite Int.mul_one.
      auto. }
    rewrite H5 in H4. clear H5.
    simpl in H,H0.
    apply eq_add_S in H,H0.
    inversion H1.
    unfold AOSTMRNode in H4.
    sep normal in H4.
    sep destruct H4. sep split in H4. subst v0 highl'.
    rewrite Hl in H4.
    sep lifts (4::11::nil)%nat in H4.
    destruct H3 as [? ?]. destruct v;tryfalse.
    apply read_only_merge_all in H4; pauto.
    destruct H4.
    inversion H6;subst x3.
    cbn [V_OSCNTHI' val_inj V_OSCNTHI nth_val].
    sep lifts (10::11::nil)%nat in H4.
    assert (map V_OSCNTHI' tmrl = highl).
    { eapply IHn;eauto.
      lia.  }
    rewrite H8. auto.
Qed.

Lemma TMRcntList_P_merge_highl :
  forall tmrl1 tmrl2 lowl highl highl' p,
    TMRcntList_P tmrl2 lowl highl' ->
    array_type_vallist_match Tint32 highl ->
    length highl= 8%nat ->
    length tmrl1 = 8%nat ->
    length tmrl2 = 8%nat ->
    AOSTMRList' (tmrl1 ++ tmrl2) **  
    Aarray_fixoffset tmr_off (timer_CNTHI ($ 8)) 8%nat Int32u highl ** p ==>
    AOSTMRList' (tmrl1 ++ tmrl2) **  
    Aarray_fixoffset tmr_off (timer_CNTHI ($ 8)) 8%nat Int32u highl **
    [|highl' = highl|] ** p.
Proof. 
  intros. sep lift 3%nat.
  apply astar_l_apure_intro.
  sep auto.
  unfold TMRcntList_P in *.
  destruct H.
  clear lowl H. 
  apply AOSTMRList_eq_AOSTMRList_vallist in H4;eauto.
  sep lifts (2::3::nil)%nat in H4.
  eapply TMRcntList_P_merge_highl' with (m:= 8%nat);eauto.
  lia.
Qed.

Lemma TMRcntList_P_merge :
  forall tmrl1 tmrl2  lowl lowl' highl highl' p,
    TMRcntList_P tmrl2 lowl' highl' ->
    array_type_vallist_match Tint32 lowl ->
    length lowl = 8%nat ->
    array_type_vallist_match Tint32 highl ->
    length highl = 8%nat ->
    length tmrl1 = 8%nat ->
    length tmrl2 = 8%nat ->
    AOSTMRList' (tmrl1 ++ tmrl2) **  
    Aarray_fixoffset tmr_off (timer_CNTLO ($ 8)) 8%nat Int32u lowl **
    Aarray_fixoffset tmr_off (timer_CNTHI ($ 8)) 8%nat Int32u highl ** p ==>
    AOSTMRList' (tmrl1 ++ tmrl2) **  
    Aarray_fixoffset tmr_off (timer_CNTLO ($ 8)) 8%nat Int32u lowl **
    Aarray_fixoffset tmr_off (timer_CNTHI ($ 8)) 8%nat Int32u highl ** p.
Proof.
  intros.
  eapply TMRcntList_P_merge_lowl in H6;eauto.
  sep split in H6. subst lowl'.
  sep lifts (1::3::nil)%nat in H6.
  eapply TMRcntList_P_merge_highl in H6;eauto.
  sep split in H6. subst highl'.
  sep auto.
Qed. *)

(* Lemma tcbdllloc_lengtheq_frm:
 forall l p vl P s , s |= tcbdllloc p l vl ** P -> s |= tcbdllloc p l vl ** P /\ length l = length vl.
Proof.
 induction l; intros.
 - intros. destruct vl. split;auto.
   unfold  tcbdllloc in H. 
   cbn [dllsegloc] in H. sep normal in H. 
   afalse_tryfalse.
 - intros. destruct vl.

   unfold tcbdllloc in H. 
   cbn [dllsegloc] in H. sep normal in H. 
   afalse_tryfalse.

   unfold tcbdllloc in *. 
   cbn [dllsegloc] in *.
   sep normal in H; sep destruct H; sep split in H.
  
   assert (s |= dllsegloc x0 Vnull l vl V_OSTCBNext ** 
   PV get_off_addr x loc_off @ Int32u |-r-> v **
   P /\ length l = length vl).
   { eapply IHl. sep auto.  }
   clear H. destruct H2.
   split;[ | simpl;auto].
   sep auto.
Qed.

Lemma dllsegloc_separate_locvl : 
 forall tcbl1 p1 hp curtcb tcbl2 locvl ct x x0 ,
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 Vnull (tcbl1 ++ curtcb :: tcbl2) locvl V_OSTCBNext ==>
  EX locvl1 locv locvl2 p2,  
  [| locvl = locvl1 ++ locv :: locvl2 /\
  length locvl1 = length tcbl1 /\ length locvl2 = length tcbl2 |] ** 
  [| V_OSTCBNext curtcb = Some p2 |] **
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
  PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
  dllsegloc p2 Vnull tcbl2 locvl2 V_OSTCBNext. 
Proof.
  induction tcbl1;intros.
  - destruct locvl.
    + sep lift 3%nat in H.
      apply tcbdllloc_lengtheq_frm in H as [H H0].
      simpl in H0;inversion H0.
    + sep lift 3%nat in H.
      apply tcbdllloc_lengtheq_frm in H as [H H0].
      unfold tcbdllloc in *.
      simpl (nil ++ _) in *.
      cbn [dllsegloc] in H.
      unfold tcbdllseg in *.
      unfold dllseg in H at 1.
      sep normal in H. sep destruct H. sep split in H.
      simpljoin1. inverts H3.
      exists (@nil val) v locvl x2.
      cbn [dllsegloc]. 
      unfold dllseg at 1.
      sep auto.
      split;auto.
      simpl in H0. split;auto.
      apply eq_add_S;auto.
  - destruct locvl.
    + sep lift 3%nat in H.
      apply tcbdllloc_lengtheq_frm in H as [H H0].
      simpl in H0;inversion H0.
    + simpl ((_ :: _) ++ _ ) in *. 
      unfold tcbdllseg in *.
      unfold dllseg in H at 1;fold dllseg in H.
      cbn [dllsegloc] in H.
      sep normal in H. sep destruct H. sep split in H.
      simpljoin1. rewrite H1 in H2. inverts H2.
      sep remember (1::3::nil)%nat in H.
      sep remember (3::nil)%nat in H.
      subst H0 H2.
      eapply astar_mono in H.
      3: { intros s' Hs. exact Hs. }
      2: { clear s H. intros.
           sep lifts (2::3::nil)%nat in H.
           apply IHtcbl1 in H.
           exact H. }
      sep normal in H. sep destruct H. sep split in H.
      simpljoin1.
      exists (v::x3) x4 x5 x6.
      simpl ((_ :: _) ++ _ ).
      unfold dllseg at 1;fold dllseg.
      cbn [dllsegloc].
      sep auto.
      simpl. split;auto.
Qed.

Lemma AOSTCBLoc_separate_locvl :
 forall p1 p2 tcbl1 curtcb tcbl2 locvl rtbl ct tcbls,
 AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) locvl ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ==> 
 EX locvl1 locv locvl2 p3,  
 [| locvl = locvl1 ++ locv :: locvl2 /\ length locvl1 = length tcbl1 /\ length locvl2 = length tcbl2|] ** 
 [| V_OSTCBNext curtcb = Some p3 |] **
 [|array_type_vallist_match Int32u locvl|] ** 
 dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
 PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
 dllsegloc p3 Vnull tcbl2 locvl2 V_OSTCBNext ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls.
Proof.
  intros.
  unfold AOSTCBList, AOSTCBLoc in *.
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpljoin1.
  sep remember (2::4::5::nil)%nat in H.
  sep remember (4::nil)%nat in H.
  subst H5 H6.
  eapply astar_mono in H.
  2: { intros s' Hs;exact Hs. }
  2: { apply dllsegloc_separate_locvl. }
  sep normal in H.
  sep destruct H.
  sep split in H.
  simpljoin1.
  exists x3 x4 x5 x6.
  sep auto.
  all: eauto.
Qed.

Lemma AOSTCBLoc_separate_locvl_frm :
 forall p1 p2 tcbl1 curtcb tcbl2 locvl rtbl ct tcbls P,
 AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) locvl ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ** P ==> 
 EX locvl1 locv locvl2 p3,  
 [| locvl = locvl1 ++ locv :: locvl2 /\ length locvl1 = length tcbl1 /\ length locvl2 = length tcbl2|] ** 
 [| V_OSTCBNext curtcb = Some p3 |] **
 [|array_type_vallist_match Int32u locvl|] ** 
 dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
 PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
 dllsegloc p3 Vnull tcbl2 locvl2 V_OSTCBNext ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ** P.
Proof.
  intros.
  sep lifts (3::nil)%nat in H.
  eapply astar_mono in H.
  2: { intros s' Hs; exact Hs. }
  2: { apply AOSTCBLoc_separate_locvl. }
  sep auto.
Qed.

Lemma dllsegloc_merge_locvl : 
 forall tcbl1 p1 hp curtcb tcbl2 locvl1 locv locvl2 ct x x0 p2,
  length locvl1 = length tcbl1 -> length locvl2 = length tcbl2 ->
  V_OSTCBNext curtcb = Some p2 ->
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
  PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
  dllsegloc p2 Vnull tcbl2 locvl2 V_OSTCBNext ==>
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 Vnull (tcbl1 ++ curtcb :: tcbl2) (locvl1 ++ locv :: locvl2) V_OSTCBNext.
Proof.
  induction tcbl1;intros.
  - destruct locvl1.
    + unfold tcbdllloc in *.
      simpl (nil ++ _) in *.
      unfold tcbdllseg in *.
      unfold dllseg in H2 at 1.
      sep normal in H2. sep destruct H2. sep split in H2.
      simpljoin1. 
      cbn [dllsegloc] in *. 
      unfold dllseg at 1.
      sep auto.
    + sep lift 3%nat in H2.
      cbn [dllsegloc] in H2.
      afalse_tryfalse.
  - destruct locvl1.
    + sep lift 3%nat in H2.
      cbn [dllsegloc] in H2.
      afalse_tryfalse.
    + simpl ((_ :: _) ++ _ ) in *. 
      unfold tcbdllseg in *.
      unfold dllseg in H2 at 1;fold dllseg in H2.
      sep normal in H2. sep destruct H2. sep split in H2.
      simpljoin1.
      cbn [dllsegloc] in H2.
      sep normal in H2. sep destruct H2. sep split in H2.
      simpljoin1. rewrite H3 in H7. inverts H7.
      sep remember (1::3::nil)%nat in H2.
      sep remember (3::nil)%nat in H2.
      subst H6 H7.
      eapply astar_mono in H2.
      3: { intros s' Hs. exact Hs. }
      2: { clear s H2. intros.
           sep lifts (2::3::nil)%nat in H2.
           apply IHtcbl1 in H2;auto.
           exact H2. }
      sep normal in H2.
      unfold dllseg at 1;fold dllseg.
      cbn [dllsegloc].
      sep auto.
Qed.

Lemma dllsegloc_merge_locvl_frm : 
 forall tcbl1 p1 hp curtcb tcbl2 locvl1 locv locvl2 ct x x0 p2 P,
  length locvl1 = length tcbl1 -> length locvl2 = length tcbl2 ->
  V_OSTCBNext curtcb = Some p2 ->
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
  PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
  dllsegloc p2 Vnull tcbl2 locvl2 V_OSTCBNext ** P ==>
  tcbdllseg p1 hp x (Vptr ct) tcbl1 **
  tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: tcbl2) **
  dllsegloc p1 Vnull (tcbl1 ++ curtcb :: tcbl2) (locvl1 ++ locv :: locvl2) V_OSTCBNext ** P.
Proof.
 intros.
 sep cancel P. 
 eapply dllsegloc_merge_locvl;eauto.
Qed.

Lemma AOSTCBLoc_merge_locvl :
 forall p1 p2 tcbl1 curtcb tcbl2 rtbl tcbls locvl1 locv locvl2 ct p3,
 length locvl1 = length tcbl1 -> length locvl2 = length tcbl2 ->
 V_OSTCBNext curtcb = Some p3 ->
 array_type_vallist_match Int32u (locvl1 ++ locv :: locvl2) ->
 dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
 PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
 dllsegloc p3 Vnull tcbl2 locvl2 V_OSTCBNext ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ==>
 AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) (locvl1 ++ locv :: locvl2) ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls .
Proof.
  intros.
  unfold AOSTCBList, AOSTCBLoc in *.
  sep normal in H3.
  sep destruct H3.
  sep split in H3.
  simpljoin1.
  sep remember (2::4::5::6::7::nil)%nat in H3.
  sep remember (6::nil)%nat in H3.
  subst H9 H8.
  eapply astar_mono in H3.
  2: { intros s' Hs;exact Hs. }
  2: { apply dllsegloc_merge_locvl;eauto. }
  sep normal in H3.
  sep auto.
  all: eauto.
Qed.

Lemma AOSTCBLoc_merge_locvl_frm :
 forall p1 p2 tcbl1 curtcb tcbl2 rtbl tcbls locvl1 locv locvl2 ct p3 P,
 length locvl1 = length tcbl1 -> length locvl2 = length tcbl2 ->
 V_OSTCBNext curtcb = Some p3 ->
 array_type_vallist_match Int32u (locvl1 ++ locv :: locvl2) ->
 dllsegloc p1 (Vptr ct) tcbl1 locvl1 V_OSTCBNext** 
 PV get_off_addr ct loc_off @ Int32u |-r-> locv ** 
 dllsegloc p3 Vnull tcbl2 locvl2 V_OSTCBNext ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ** P ==>
 AOSTCBLoc p1 (tcbl1 ++ curtcb :: tcbl2) (locvl1 ++ locv :: locvl2) ** 
 AOSTCBList p1 p2 tcbl1 (curtcb :: tcbl2) rtbl ct tcbls ** P.
Proof.
  intros.
  sep lifts (5::nil)%nat in H3.
  eapply astar_mono in H3.
  2: { intros s' Hs; exact Hs. }
  2: { apply AOSTCBLoc_merge_locvl;auto. }
  sep auto.
Qed. *)

Lemma In_heape_addrval_split:
  forall cHeape l t,
  In_heape_addrval cHeape l t ->
  forall P,
  AOScoreheape cHeape ** P
  ==>
  EX l1 l2  v,
  [| cHeape = l1 ++ (l, t, v) :: l2  |] **
  AOScoreheape cHeape ** P.
Proof.
  intros.
  destruct H as [v  ?].
  apply in_split in H as [l1 [l2 ?]].
  simpljoin1.
  exists l1 l2 v.
  sep auto. 
Qed.

Lemma coreheape_separate:
  forall cheape1 l t v cheape2,
  AOScoreheape
    (cheape1 ++ (l, t, v) :: cheape2)
  ==>
  AOScoreheape cheape1 **  PV l @ t |-> v **
  AOScoreheape cheape2.
Proof.
  induction cheape1;intros.
  - simpl (nil ++ _) in H.
    cbn [AOScoreheape] in *.
    sep auto.
  - simpl ((_::_) ++ _ ) in *.
    destruct a as [[? ?] ?].
    cbn [AOScoreheape] in *.
    sep normal in H.
    eapply astar_mono in H.
    2: intros s' Hs';exact Hs'.
    2: eapply IHcheape1.
    sep auto.
Qed.

Lemma coreheape_separate_frm:
  forall cheape1 l t v cheape2 P,
  AOScoreheape
    (cheape1 ++ (l, t, v) :: cheape2) ** P
  ==>
  AOScoreheape cheape1 **  PV l @ t |-> v **
  AOScoreheape cheape2 ** P.
Proof.
  intros.
  sep cancel P.
  eapply coreheape_separate;eauto.
Qed.

Lemma coreheape_merge:
  forall cheape1 l t v cheape2,
  AOScoreheape cheape1 **  PV l @ t |-> v **
  AOScoreheape cheape2 ==>
  AOScoreheape
    (cheape1 ++ (l, t, v) :: cheape2).
Proof.
  induction cheape1;intros.
  - simpl (nil ++ _) in *.
    cbn [AOScoreheape] in *.
    sep auto.
  - simpl ((_::_) ++ _ ) in *.
    destruct a as [[? ?] ?].
    cbn [AOScoreheape] in *.
    sep normal in H.
    eapply astar_mono in H.
    2: intros s' Hs';exact Hs'.
    2: eapply IHcheape1.
    sep auto.
Qed.

Lemma coreheape_merge_frm:
  forall cheape1 l t v cheape2 P,
  AOScoreheape cheape1 **  PV l @ t |-> v **
  AOScoreheape cheape2 ** P ==>
  AOScoreheape
    (cheape1 ++ (l, t, v) :: cheape2) ** P.
Proof.
  intros.
  sep cancel P.
  eapply coreheape_merge;eauto.
Qed.

Lemma Int_add_mul_S : forall i off m, 
  (i +ᵢ  off) +ᵢ  Int.mul off ($ Z.of_nat m) = 
  i +ᵢ  Int.mul off ($ Z.of_nat (S m)).
Proof.
  intros. 
  rewrite Int.add_assoc.
  assert ((Int.repr (Z.of_nat (S m))) = Int.add (Int.repr (Z.of_nat m)) Int.one).
  { clear. assert (S m = m + 1)%nat by lia.
  rewrite H.
  rewrite Nat2Z.inj_add.
  simpl.
  unfold Int.add.
  rewrite Int.unsigned_one.
  rewrite Int.unsigned_repr_eq.
  assert (1 = 1 mod Int.modulus)%Z by mauto.
  rewrite H0 at 2.
  apply Int.eqm_samerepr.
  unfold Int.eqm.
  apply Int.eqmod_add.
  apply Int.eqmod_mod.
  compute.
  auto.
  apply Int.eqmod_mod. mauto.  }
  rewrite H.
  rewrite Int.mul_add_distr_r.
  rewrite Int.mul_one.
  rewrite (Int.add_commut off).
  auto. 
Qed.

(* Lemma Aarray_fixoffset_split:
  forall m off l t n vl, 
  (m < n)%nat ->
  length vl = n ->
  Aarray_fixoffset off l n t vl
  ==>
  EX l1 l2  v,
  [| vl = l1 ++ v :: l2 /\ length l1 = m |] **
  Aarray_fixoffset off l m t l1 **
  PV (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) @ t |-r-> v ** Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat (S m)))))  (n - m - 1)%nat t l2.
Proof.
  induction m;intros.
  - destruct n.
    inversion H.
    destruct vl. inversion H0.
    destruct l as [b i].
    cbn [Aarray_fixoffset] in H1.
    exists (@nil val) vl v.
    sep auto.
    assert (($ Z.of_nat 0) = Int.zero) by mauto.
    rewrite H2.
    unfold get_off_addr.
    cbn [fst snd].
    rewrite Int.mul_zero.
    rewrite Int.add_zero.
    assert (($ Z.of_nat 1) =Int.one ) by mauto.
    rewrite H3. 
    rewrite Int.mul_one.
    assert ((S n - 0 - 1) = n)%nat by lia.
    rewrite H4.
    cbn [Aarray_fixoffset].
    sep auto.
  - destruct n. inversion H.
    destruct vl. inversion H0.
    simpl in H0.
    destruct l as [b i].
    cbn [Aarray_fixoffset] in H1.
    apply lt_S_n in H.
    apply eq_add_S in H0.
    eapply astar_mono in H1.
    2: intros s' Hs';exact Hs'.
    2: eapply IHm;eauto.
    sep normal in H1.
    sep destruct H1.
    sep split in H1.
    destruct H2.
    exists (v::x) x0 x1.
    unfold get_off_addr in *.
    cbn [fst snd] in *.
    rewrite Int_add_mul_S in H1.
    rewrite Int_add_mul_S in H1.
    rewrite Nat.sub_succ.
    sep auto.
    cbn [Aarray_fixoffset].
    sep auto.
Qed.

Lemma Aarray_fixoffset_split_frm:
  forall m off l t n vl P, 
  (m < n)%nat ->
  length vl = n ->
  Aarray_fixoffset off l n t vl ** P
  ==>
  EX l1 l2  v,
  [| vl = l1 ++ v :: l2 /\ length l1 = m |] **
  Aarray_fixoffset off l m t l1 **
  PV (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) @ t |-r-> v ** Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat (S m)))))  (n - m - 1)%nat t l2 ** P.
Proof.
 intros.
 eapply astar_mono with (Q':= P)in H1.
 2: eapply Aarray_fixoffset_split;eauto.
 2: sep auto.
 sep auto.
Qed.

Lemma Aarray_fixoffset_app:
  forall m off l t n l1 l2, 
  length l1 = m ->
  length (l1 ++ l2) = n ->
  Aarray_fixoffset off l n t (l1 ++ l2) <==> 
  Aarray_fixoffset off l m t l1 ** 
  Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) (n - m) t l2.
Proof.
 induction m;intros.
 - destruct l1;tryfalse.
   simpl (nil ++ _) in *.
   cbn [Aarray_fixoffset].
   destruct l.
   unfold get_off_addr. cbn [fst snd].
   assert ($ Z.of_nat 0 = Int.zero) by mauto.
   rewrite H1.
   rewrite Int.mul_zero.
   rewrite Int.add_zero.
   assert (n - 0 = n)%nat by lia.
   rewrite H2.
   split;intro;sep auto.
 - destruct l1;tryfalse.
   simpl ((_ :: _) ++ _) in *.
   simpl in H,H0.
   destruct n;tryfalse.
   apply eq_add_S in H, H0.
   destruct l.
   cbn [Aarray_fixoffset].
   split;intros.
   + sep normal.
     sep cancel Aptrmapsto.
     apply IHm in H1;auto.
     rewrite Nat.sub_succ.
     unfold get_off_addr in *.
     cbn [fst snd ] in *.
     rewrite Int_add_mul_S in *.
     sep auto.
   + sep normal in H1.
     sep cancel Aptrmapsto.
     apply IHm;auto.
     rewrite Nat.sub_succ in H1.
     unfold get_off_addr in *.
     cbn [fst snd ] in *.
     rewrite Int_add_mul_S in *.
     sep auto.
Qed.

Lemma Aarray_fixoffset_app_frm:
  forall m off l t n l1 l2 P, 
  length l1 = m ->
  length (l1 ++ l2) = n ->
  Aarray_fixoffset off l n t (l1 ++ l2) ** P<==> 
  Aarray_fixoffset off l m t l1 ** 
  Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) (n - m) t l2 ** P.
Proof.
  intros. 
  split;intros;
  sep cancel P.
  apply Aarray_fixoffset_app;auto.
  eapply Aarray_fixoffset_app;eauto.
Qed.

Lemma Aarray_fixoffset_cons_frm:
  forall off l t n v vl P, 
  (0 < n)%nat ->
  Aarray_fixoffset off l n t (v::vl) ** P ==> 
  PV l @ t |-r-> v ** Aarray_fixoffset off (get_off_addr l off) (n - 1) t vl ** P.
Proof.
  intros. 
  destruct n;[inversion H| ].
  destruct l.
  cbn [Aarray_fixoffset] in H0.
  unfold get_off_addr.
  cbn [fst snd].
  assert (S n - 1 = n)%nat by lia.
  rewrite H1.
  sep auto. 
Qed.

Lemma Aarray_fixoffset_combine:
  forall m off l t n l1 l2  v, 
  (m < n)%nat ->
  length (l1 ++ v :: l2) = n ->
  length l1 = m ->
  Aarray_fixoffset off l m t l1 **
  PV (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) @ t |-r-> v ** Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat (S m)))))  (n - m - 1)%nat t l2 ==>
  Aarray_fixoffset off l n t (l1 ++ v :: l2) .
Proof.
  induction m;intros.
  - destruct n.
    inversion H.
    destruct l1;tryfalse.
    simpl (nil ++ _ ) in *.
    destruct l as [b i].
    cbn [Aarray_fixoffset] in *.
    sep auto.
    assert (($ Z.of_nat 0) = Int.zero) by mauto.
    rewrite H3 in H2.
    unfold get_off_addr in H2.
    cbn [fst snd] in H2.
    rewrite Int.mul_zero in *.
    rewrite Int.add_zero in *.
    assert (($ Z.of_nat 1) =Int.one ) by mauto.
    rewrite H4 in *. 
    rewrite Int.mul_one in *.
    assert ((S n - 0 - 1) = n)%nat by lia.
    rewrite H5 in *.
    sep auto.
  - destruct n. inversion H.
    destruct l1;tryfalse. 
    simpl ((_ :: _) ++ _ )in *.
    destruct l as [b i].
    cbn [Aarray_fixoffset] in *.
    apply lt_S_n in H.
    simpl in H0,H1.
    apply eq_add_S in H0, H1.
    sep normal in H2.
    eapply astar_mono in H2.
    2: intros s' Hs';exact Hs'.
    2: { intros. clear H2. 
         assert (get_off_addr (b, i) (Int.mul off ($ Z.of_nat (S m))) =
         get_off_addr (b, i +ᵢ  off) (Int.mul off ($ Z.of_nat m))).
         { unfold get_off_addr. cbn [fst snd]. 
         rewrite Int_add_mul_S. auto. }
         rewrite H2 in H3.
         assert ((get_off_addr (b, i) (Int.mul off ($ Z.of_nat (S (S m))))) = get_off_addr (b, i +ᵢ  off) (Int.mul off ($ Z.of_nat ((S m))))).
         { unfold get_off_addr. cbn [fst snd]. 
         rewrite Int_add_mul_S. auto. }
         rewrite H4 in H3.
         assert (S n - S m - 1 = n - m - 1)%nat by lia. 
         rewrite H5 in H3.
         apply IHm in H3;eauto.
    }
    sep auto.
Qed.

Lemma Aarray_fixoffset_combine_frm:
forall m off l t n l1 l2 v P, 
(m < n)%nat ->
length (l1 ++ v :: l2) = n ->
length l1 = m ->
Aarray_fixoffset off l m t l1 **
PV (get_off_addr l (Int.mul off (Int.repr (Z.of_nat m)))) @ t |-r-> v ** Aarray_fixoffset off (get_off_addr l (Int.mul off (Int.repr (Z.of_nat (S m)))))  (n - m - 1)%nat t l2 ** P==>
Aarray_fixoffset off l n t (l1 ++ v :: l2) ** P.
Proof.
 intros.
 sep cancel P.
 eapply Aarray_fixoffset_combine;eauto.
Qed. *)

Definition V_OSCNTLO' tmri :=
  match V_OSCNTLO tmri with 
  | Some a => a 
  | None => Vnull
  end.

Definition V_OSCNTHI' tmri :=
  match V_OSCNTHI tmri with 
  | Some a => a 
  | None => Vnull
  end.

Lemma TMRListP_gettklow:
 forall n m utmrl usedl tmrls tmri tm tmst tk om,
  (n < length utmrl)%nat ->
  get tmrls (Z.of_nat (n + m + 8)) = Some (tm,tmst,tk,om) ->
  nth_error utmrl n = Some tmri ->
  TMRList_P_user m utmrl usedl tmrls -> 
  V_OSCNTLO' tmri = V$ tk.
Proof.
 induction n;intros.
 - 
   destruct utmrl;[ inversion H| ].
   destruct usedl;[ inversion H2| ].
   cbn in H1,H2.
   inversion H1;subst v.
   destruct v0;tryfalse.
   destruct H2.
   + my_destruct H2.
   assert (get tmrls (Z.of_nat (m + 8))  = Some x).
   { eapply join_sig_get;eauto. }
   assert (x = (tm, tmst, tk, om)).
   { eapply map_get_unique;eauto. }
   subst x.
   unfold TMRNode_P in *.
   destruct H4 as [? [? _]].
   unfold TMRNode_Pcnt in *.
   destruct H8 as [? [? [? [? [? ?]]]]].
   unfold V_OSCNTLO' in *.
   rewrite H10, H8.
   cbn.
   auto.
   + my_destruct H2.
     false.
     apply H4.
     eapply get_indom.
     eexists. eauto.
 - destruct utmrl;[ inversion H| ].
   destruct usedl;[ inversion H2| ].
   cbn in H1,H2.
   destruct v0;tryfalse.
   cbn [length] in *.
   destruct H2.
   + my_destruct H2.
   eapply (IHn (S m) utmrl usedl x0);[lia |  | auto | auto ].
   assert (n + S m + 8 = S n + m + 8)%nat by lia.
   rewrite H7.
   eapply join_lib_aux.join_sig_get_neq;eauto.
   lia.
   + my_destruct H2. 
   eapply (IHn (S m) utmrl usedl tmrls);[lia |  | auto | auto ].
   assert (n + S m + 8 = S n + m + 8)%nat by lia.
   rewrite H6; eauto.
Qed.

Lemma RLH_TMRList_P_sys_idrange': forall tmrl tmrls n v m,
  TMRList_P_sys m tmrl tmrls ->
  get tmrls (Z.of_nat (m + n)) = Some v -> (n < (length tmrl))%nat.
Proof.
  induction tmrl;intros.
  - simpl in H. subst. tryfalse.
  - simpl in H.
    my_destruct H.
    destruct n.
    + simpl. lia.
    + assert (m + S n = S m + n)%nat by lia.
      rewrite H3 in H0.
      assert (get x0 (Z.of_nat (S m + n)) = Some v).
      { eapply join_lib_aux.join_sig_get_neq;eauto. lia. }
      specialize (IHtmrl _ _ _ _ H2 H4).
      simpl. lia.
Qed.

Lemma RLH_TMRList_P_sys_idrange: forall tmrl m n v,
  RLH_TMRList_P_sys tmrl m ->
  get m (Z.of_nat n) = Some v -> (n < (length tmrl))%nat.
Proof.
  unfold RLH_TMRList_P_sys;intros.
  assert ((Z.of_nat n) = ((Z.of_nat (0 + n)))) by lia.
  rewrite H1 in H0.
  eapply RLH_TMRList_P_sys_idrange';eauto.
Qed.

Lemma RLH_TMRList_P_sys_indom': forall tmrl tmrls n m,
  (n < length tmrl)%nat ->
  TMRList_P_sys m tmrl tmrls ->
  indom tmrls (Z.of_nat (m + n)).
Proof.
  induction tmrl;intros.
  - simpl in H. lia.
  - simpl in H.
    destruct n.
    + cbn in H0.
      my_destruct H0.
      rewrite Nat.add_0_r.
      unfold indom.
      eexists.
      eapply join_sig_get;eauto.
    + assert (m + S n = S m + n)%nat by lia.
      rewrite H1.
      cbn in H0.
      my_destruct H0.
      assert (indom x0 (Z.of_nat (S m + n))).
      { eapply IHtmrl;eauto. lia. }
      eapply join_in_r;eauto.
Qed.

Lemma RLH_TMRList_P_sys_indom: forall tmrl m n,
  (n < length tmrl)%nat ->
  RLH_TMRList_P_sys tmrl m  ->
  indom m (Z.of_nat n).
Proof.
  unfold RLH_TMRList_P_sys;intros.
  assert ((Z.of_nat n) = ((Z.of_nat (0 + n)))) by lia.
  rewrite H1.
  eapply RLH_TMRList_P_sys_indom';eauto.
Qed.

Lemma AOSTMRList_TMRcntList_P_gettklow_frm:
 forall systmrl utmrl usedl tmrls i tmri tm tmst tk om P,
 Int.ltu ($7) i = true ->
 Int.ltu i ($16) = true -> 
 get tmrls (Int.unsigned i) = Some (tm,tmst,tk,om) ->
 nth_error utmrl (Z.to_nat (Int.unsigned i) - 8) = Some tmri ->
 AOSTMRList_TMRused systmrl utmrl usedl (Some tmrls) ** P ==> 
 [|V_OSCNTLO' tmri = V$ tk |] ** 
 AOSTMRList_TMRused systmrl utmrl usedl (Some tmrls) ** P.
Proof.
  intros.
  sep split.
  sep auto.
  unfold AOSTMRList_TMRused in *.
  sep split in H3. clear H3.
  unfold RLH_TMRList_P_user in *.
  destruct H4. 
  destruct H5 as [[?[H5_ H5] ] | ];[ | discriminate].
  inversion H5_;subst x;clear H5_.
  my_destruct H5.
  simpl_intltbool.
  eapply TMRListP_gettklow;eauto.
  lia.

  rewrite Nat.add_0_r.
  assert (Z.to_nat (Int.unsigned i) - 8 + 8 = Z.to_nat (Int.unsigned i))%nat by lia.
  rewrite H8.
  erewrite <- map_join_get_none;eauto.
  erewrite Z2Nat.id by (apply Int.unsigned_range). eauto.
  destruct (get x (Z.of_nat (Z.to_nat (Int.unsigned i)))) eqn:?;[ | auto].
  false.
  lets Hfalse : RLH_TMRList_P_sys_idrange H6 Heqo.
  lia.
Qed.

Lemma TMRListP_gettkhigh:
 forall n m utmrl usedl tmrls tmri tm tmst tk om,
  (n < length utmrl)%nat ->
  get tmrls (Z.of_nat (n + m + 8)) = Some (tm,tmst,tk,om) ->
  nth_error utmrl n = Some tmri ->
  TMRList_P_user m utmrl usedl tmrls -> 
  V_OSCNTHI' tmri = V$ tk / Int.modulus.
Proof.
 induction n;intros.
 - 
   destruct utmrl;[ inversion H| ].
   destruct usedl;[ inversion H2| ].
   cbn in H1,H2.
   inversion H1;subst v.
   destruct v0;tryfalse.
   destruct H2.
   + my_destruct H2.
   assert (get tmrls (Z.of_nat (m + 8))  = Some x).
   { eapply join_sig_get;eauto. }
   assert (x = (tm, tmst, tk, om)).
   { eapply map_get_unique;eauto. }
   subst x.
   unfold TMRNode_P in *.
   destruct H4 as [? [? _]].
   unfold TMRNode_Pcnt in *.
   destruct H8 as [? [? [? [? [? ?]]]]].
   unfold V_OSCNTHI' in *.
   rewrite H11, H9.
   cbn.
   auto.
   + my_destruct H2.
     false.
     apply H4.
     eapply get_indom.
     eexists. eauto.
 - destruct utmrl;[ inversion H| ].
   destruct usedl;[ inversion H2| ].
   cbn in H1,H2.
   destruct v0;tryfalse.
   cbn [length] in *.
   destruct H2.
   + my_destruct H2.
   eapply (IHn (S m) utmrl usedl x0);[lia |  | auto | auto ].
   assert (n + S m + 8 = S n + m + 8)%nat by lia.
   rewrite H7.
   eapply join_lib_aux.join_sig_get_neq;eauto.
   lia.
   + my_destruct H2. 
   eapply (IHn (S m) utmrl usedl tmrls);[lia |  | auto | auto ].
   assert (n + S m + 8 = S n + m + 8)%nat by lia.
   rewrite H6; eauto.
Qed.

Lemma RLH_TMRList_P_user_gettklowhigh:
forall utmrl usedl tmrls i tmri tm tmst tk om,
 Int.ltu ($7) i = true ->
 Int.ltu i ($16) = true -> 
 length utmrl = 8%nat ->
 get tmrls (Int.unsigned i) = Some (tm,tmst,tk,om) ->
 nth_error utmrl (Z.to_nat (Int.unsigned i) - 8) = Some tmri ->
 RLH_TMRList_P_user utmrl usedl tmrls ->
 V_OSCNTLO' tmri = V$ tk /\ V_OSCNTHI' tmri = V$ tk / Int.modulus.
Proof.
  intros.
  simpl_intltbool.
  assert (get tmrls (Z.of_nat (Z.to_nat (Int.unsigned i) - 8 + 0 + 8)) = Some (tm, tmst, tk, om)).
  { rewrite Nat.add_0_r.
  assert (Z.to_nat (Int.unsigned i) - 8 + 8 = Z.to_nat (Int.unsigned i))%nat by lia.
  rewrite H5.
  erewrite Z2Nat.id by (apply Int.unsigned_range). eauto. }
  
  split.
  eapply TMRListP_gettklow;eauto.
  lia.
  eapply TMRListP_gettkhigh;eauto.
  lia.
Qed.

(* Lemma fold_p_local: forall tid locv,
  GoodLInvAsrt OSLInv -> 
  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv**
  PV get_off_addr tid flag_off @ Int8u |-r-> (V$ 1)  **
  CurTid tid ==> p_local OSLInv tid init_lg .
Proof.
  intros.
  unfold p_local, LINV, OSLInv, init_lg'.
  sep auto.
  split;auto.
  unfold isflag. auto.
Qed.

Lemma fold_p_local_frm : forall tid locv P,
  GoodLInvAsrt OSLInv -> 
  PV get_off_addr tid loc_off @ Int32u |-r-> Vint32 locv**
  PV get_off_addr tid flag_off @ Int8u |-r-> (V$ 1)  **
  CurTid tid ** P ==> p_local OSLInv tid init_lg ** P.
Proof.
  intros.
  unfold p_local, LINV, OSLInv, init_lg'.
  sep auto.
  split;auto.
  unfold isflag. auto.
Qed. *)

