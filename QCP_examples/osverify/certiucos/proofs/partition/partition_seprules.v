Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.

Require Import abs_op_corecommu_rules.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import corecommu_sep_added.


Lemma APortStruct_merge:  forall p vl1 vl2,
    Astruct p OS_EVENT vl1 ** APortStruct p vl2 ** 
    [| struct_type_vallist_match OS_EVENT vl1 |] ** 
    [| struct_type_vallist_match' OS_Port_Seg_dls vl2 |]==> 
    Astruct p OS_Port (vl1 ++ vl2) ** 
    [| struct_type_vallist_match OS_Port (vl1++vl2) |].
Proof.
  intros.
  sep split in H.
  struct_type_vallist_match_elim .
  unfold OS_Port_Seg_dls in *.
  struct_type_vallist_match'_elim .
  unfold APortStruct in *.
  unfold Astruct in *.
  unfold OS_Port.
  unfold OS_EVENT in *.
  sep split.
  + simpl Astruct' in *. destruct p.
    unfold get_off_addr in *.
    simpl fst in *. simpl snd in *. 
    assert (i15 +ᵢ  $ 29 = (((((((i15 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 2) +ᵢ  $ 4) +ᵢ  $ 8) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 8 ).
    {
      do 7 rewrite Int.add_assoc.
      f_equal.
    }
    repeat rewrite H1 in H.
    sep auto.
  + simpl. 
    repeat rewrite byte_max_unsigned_val.
    repeat rewrite int16_max_unsigned_val.
    rewrite <- Z.leb_le in *.
    assert (forall x, isptr x -> match x with
        | Vundef | Vint32 _ => false
        | _ => true
        end = true ) as isptr_match.
    {
      intros. destruct H7; inverts H1; auto.
      destruct H7. subst. auto.
    }
    repeat (splits; match goal with
    | |- (if ?b then true else false) = true => 
        match goal with
        | H: b = true |- _ =>
          rewrite H; reflexivity
        end 
    | |- _ = true => try apply isptr_match; auto
    | _ => auto
    end).
Qed.

Lemma APortStruct_split1:  forall p vl,
    Astruct p OS_Port vl ** 
    [| struct_type_vallist_match OS_Port vl |] ==> 
    Astruct p OS_EVENT (firstn 8 vl) ** APortStruct p (skipn 8 vl) ** 
    [| struct_type_vallist_match OS_EVENT (firstn 8 vl) |] ** 
    [| struct_type_vallist_match' OS_Port_Seg_dls (skipn 8 vl) |].
Proof.
  intros.
  sep split in H.
  struct_type_vallist_match_elim .
  unfold OS_Port_Seg_dls in *.
  unfold APortStruct in *.
  unfold Astruct in *.
  unfold OS_Port in *.
  unfold OS_EVENT in *.
  simpl firstn in *.
  simpl skipn in *.
  rewrite <- Z.leb_le in *.
  assert (forall x, isptr x -> match x with
      | Vundef | Vint32 _ => false
      | _ => true
      end = true ) as isptr_match.
  {
    intros. destruct H6; inverts H6; auto.
  }
  sep split.
  + simpl Astruct' in *. destruct p.
    unfold get_off_addr in *.
    simpl fst in *. simpl snd in *. 
    assert (i15 +ᵢ  $ 29 = (((((((i15 +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 2) +ᵢ  $ 4) +ᵢ  $ 8) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 8 ).
    {
      do 7 rewrite Int.add_assoc.
      f_equal.
    }
    repeat rewrite H6.
    sep auto.
  + simpl.
    repeat rewrite byte_max_unsigned_val.
    repeat rewrite int16_max_unsigned_val. 
    repeat (splits; match goal with
    | |- (if ?b then true else false) = true => 
        match goal with
        | H: b = true |- _ =>
          rewrite H; reflexivity
        end 
    | |- _ = true => try apply isptr_match; auto
    | _ => auto
    end).
  + simpl.
    repeat rewrite byte_max_unsigned_val.
    repeat rewrite int16_max_unsigned_val.
    repeat (splits; match goal with
    | |- (if ?b then true else false) = true => 
        match goal with
        | H: b = true |- _ =>
          rewrite H; reflexivity
        end 
    | |- _ = true => try apply isptr_match; auto
    | _ => auto
    end).
Qed.

Lemma APortStruct_split2:  forall p vl1 vl2,
    length vl1 = 8%nat ->
    Astruct p OS_Port (vl1++vl2) ** 
    [| struct_type_vallist_match OS_Port (vl1++vl2) |] ==> 
    Astruct p OS_EVENT vl1 ** APortStruct p vl2 ** 
    [| struct_type_vallist_match OS_EVENT vl1 |] ** 
    [| struct_type_vallist_match' OS_Port_Seg_dls vl2 |].
Proof.
  intros.
  lets Hx: APortStruct_split1 H0. clear H0.
  lets Happ1: firstn_app_2 0%nat vl1 vl2.
  rewrite H in Happ1.
  simpl plus in Happ1.
  simpl firstn at 2 in Happ1.
  rewrite app_nil_r in Happ1.
  lets Happ2: skipn_app 8%nat vl1 vl2.
  rewrite H in Happ2.
  simpl Nat.sub in Happ2.
  simpl skipn at 3 in Happ2.
  rewrite <- H in Happ2 at 2.
  rewrite skipn_all in Happ2.
  simpl app in Happ2.
  rewrite Happ1 in Hx.
  rewrite Happ2 in Hx.
  auto.
Qed.

Lemma AKPortStructType_split:  forall vl,
    struct_type_vallist_match OS_K_Port vl ->
    struct_type_vallist_match' OS_K_Port_Seg_dls (firstn 6 vl).
Proof.
  intros.
  struct_type_vallist_match_elim .
  unfold OS_K_Port_Seg_dls in *.
  simpl firstn in *.
  rewrite <- Z.leb_le in *.
  assert (forall x, isptr x -> match x with
      | Vundef | Vint32 _ => false
      | _ => true
      end = true ) as isptr_match.
  {
    intros. destruct H6; inverts H6; auto.
  }
  simpl.
  repeat rewrite byte_max_unsigned_val.
  repeat rewrite int16_max_unsigned_val. 
  repeat (splits; match goal with
  | |- (if ?b then true else false) = true => 
      match goal with
      | H: b = true |- _ =>
        rewrite H; reflexivity
      end 
  | |- _ = true => try apply isptr_match; auto
  | _ => auto
  end).
Qed.

Lemma dmportp_sllseg_app : forall n dportlptr dportl1 dportl2 dportmsgll1 dportmsgll2,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    dmportp_sll dportlptr (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort  ==>
    EX dportlptr', 
        dmportp_sllseg dportlptr dportlptr' dportl1 dportmsgll1 OS_Port_V_nextPort **
        dmportp_sllseg dportlptr' Vnull dportl2 dportmsgll2 OS_Port_V_nextPort.
Proof.
  intros ?.
  unfold dmportp_sll.
  induction n;intros.
  - destruct dportl1, dportmsgll1;tryfalse.
    cbn in H1.
    exists dportlptr.
    cbn [dmportp_sllseg ].
    sep pauto.
  - destruct dportl1, dportmsgll1;tryfalse.
    cbn in H, H0.
    simpl ((_ :: _ ) ++ _) in *.
    cbn [dmportp_sllseg ] in H1.
    sep normal in H1.
    sep destruct H1.
    sep split in H1.
    sep lift 2%nat in H1.
    apply disj_star_elim_disj in H1 as [? | ?]. 
    + sep split in H1.
      sep lift 3%nat in H1.
      eapply astar_mono in H1.
      3: { intros s' Hs'; exact Hs'. }
      2: { eapply IHn. lia. lia.  }
      sep normal in H1.
      sep destruct H1.
      exists x2.
      cbn [dmportp_sllseg ].
      sep normal.
      sep eexists.
      sep split;eauto.
      sep lift 2%nat.
      apply disj_split.
      left.
      sep pauto.
    + sep normal in H1.
      sep destruct H1.
      sep split in H1.
      sep lift 4%nat in H1.
      eapply astar_mono in H1.
      3: { intros s' Hs'; exact Hs'. }
      2: { eapply IHn. lia. lia.  }
      sep normal in H1.
      sep destruct H1.
      exists x8.
      cbn [dmportp_sllseg ].
      sep normal.
      sep eexists.
      sep split;eauto.
      sep lift 2%nat.
      apply disj_split.
      right.
      sep pauto.
Qed. 

Lemma dmportp_sllseg_app_frm : forall n dportlptr dportl1 dportl2 dportmsgll1 dportmsgll2 P,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    dmportp_sll dportlptr (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort ** P ==>
    EX dportlptr',  
        dmportp_sllseg dportlptr dportlptr' dportl1 dportmsgll1 OS_Port_V_nextPort**
        dmportp_sllseg dportlptr' Vnull dportl2 dportmsgll2 OS_Port_V_nextPort** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H1.
  2: eapply dmportp_sllseg_app;eauto.
  sep normal in H1.
  sep pauto.
  sep auto.
Qed.


Lemma dmportp_sllseg_app' : forall n dportlptr dportl1 dportl2 dportmsgll1 dportmsgll2 dpptrl p_v,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    nth_error dpptrl n = Some p_v -> 
    RL_PortPtrList dportlptr (dportl1 ++ dportl2) dpptrl ->
    dmportp_sll dportlptr (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort  <==>
        dmportp_sllseg dportlptr (Vptr p_v) dportl1 dportmsgll1 OS_Port_V_nextPort **
        dmportp_sllseg (Vptr p_v) Vnull dportl2 dportmsgll2 OS_Port_V_nextPort.
Proof.
  intros ?.
  unfold dmportp_sll.
  induction n;intros.
  - split;intros.
    + destruct dportl1, dportmsgll1, dpptrl;tryfalse.
    cbn in H1, H2, H3.
    inverts H1.
    destruct dportl2;tryfalse.
    cbn in H2.
    simpljoin1.
    cbn [dmportp_sllseg ].
    sep pauto.
    + destruct dportl1, dportmsgll1, dpptrl;tryfalse.
    cbn in H1, H2.
    inverts H1.
    simpl (nil ++ _).
    cbn [dmportp_sllseg ] in *.
    sep pauto.
  - split;intros.
    * destruct dportl1, dportmsgll1, dpptrl;tryfalse.
      cbn in H, H0, H1, H2.
      simpljoin1.
      simpl ((_ :: _ ) ++ _) in *.
      cbn [dmportp_sllseg] in H3.
      sep normal in H3.
      sep destruct H3.
      sep split in H3.
      inverts H2.
      rewrite H4 in H6. inverts H6.
      sep lift 2%nat in H3.
      apply disj_star_elim_disj in H3 as [? | ?]. 
      + sep split in H2.
        sep lift 3%nat in H2.
        eapply astar_mono in H2.
        3: { intros s' Hs'; exact Hs'. }
        2: { eapply IHn. lia. lia. eauto. eauto. }
        sep normal in H2.
        cbn [dmportp_sllseg ].
        sep normal.
        sep eexists.
        sep split;eauto.
        sep lift 2%nat.
        apply disj_split.
        left.
        sep pauto.
      + sep normal in H2.
        sep destruct H2.
        sep split in H2.
        sep lift 4%nat in H2.
        eapply astar_mono in H2.
        3: { intros s' Hs'; exact Hs'. }
        2: { eapply IHn;eauto.  }
        sep normal in H2.
        cbn [dmportp_sllseg ].
        sep normal.
        sep eexists.
        sep split;eauto.
        sep lift 2%nat.
        apply disj_split.
        right.
        sep pauto.
    * destruct dportl1, dportmsgll1, dpptrl;tryfalse.
      cbn in H, H0, H1, H2.
      simpljoin1.
      simpl ((_ :: _ ) ++ _) in *.
      cbn [dmportp_sllseg] in H3.
      sep normal in H3.
      sep destruct H3.
      sep split in H3.
      inverts H2.
      rewrite H4 in H6. inverts H6.
      sep lift 2%nat in H3.
      apply disj_star_elim_disj in H3 as [? | ?]. 
      + sep split in H2.
        cbn [dmportp_sllseg ].
        sep normal.
        sep eexists.
        sep split;eauto.
        sep lift 2%nat.
        apply disj_split.
        left.
        sep pauto.
        eapply IHn;eauto.
      + sep normal in H2.
        sep destruct H2.
        sep split in H2.
        cbn [dmportp_sllseg ].
        sep normal.
        sep eexists.
        sep split;eauto.
        sep lift 2%nat.
        apply disj_split.
        right.
        sep pauto;eauto.
        sep autocancel.
        eapply IHn;eauto.
Qed. 


Lemma dmportp_sllseg_app'_frm : forall n dportlptr dportl1 dportl2 dportmsgll1 dportmsgll2 dpptrl p_v P,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    nth_error dpptrl n = Some p_v -> 
    RL_PortPtrList dportlptr (dportl1 ++ dportl2) dpptrl ->
    dmportp_sll dportlptr (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort ** P <==>
    dmportp_sllseg dportlptr (Vptr p_v)  dportl1 dportmsgll1 OS_Port_V_nextPort **
    dmportp_sllseg (Vptr p_v)  Vnull dportl2 dportmsgll2 OS_Port_V_nextPort** P.
Proof.
  intros.
  split;intros.
  sep cancel P.
  eapply dmportp_sllseg_app';eauto.
  sep cancel P.
  eapply dmportp_sllseg_app';eauto.
Qed.

Lemma OtherPortPtrList_app' : forall n otherppl1 otherppl2 otherpl1 otherpl2 othermsgll1 othermsgll2,
    length otherppl1 = n ->
    length otherpl1 = n ->
    length othermsgll1 = n ->
    OtherPortPtrList (otherppl1 ++ otherppl2) (otherpl1 ++ otherpl2) (othermsgll1 ++ othermsgll2)  ==>
    OtherPortPtrList otherppl1 otherpl1 othermsgll1 **
    OtherPortPtrList otherppl2 otherpl2 othermsgll2.
Proof.
  induction n;intros.
  - destruct otherppl1, otherpl1, othermsgll1;tryfalse.
    cbn [OtherPortPtrList] in *.
    cbn in H2.
    sep pauto.
  - destruct otherppl1, otherpl1, othermsgll1;tryfalse.
    cbn in H, H0, H1.
    simpl ((_ :: _ ) ++ _) in *.
    cbn [OtherPortPtrList] in *.
    sep normal in H2.
    sep destruct H2.
    sep split in H2.
    sep pauto; eauto.
    sep autocancel.
    eapply IHn; eauto.
Qed. 

Lemma OtherPortPtrList_app'_frm : forall n P otherppl1 otherppl2 otherpl1 otherpl2 othermsgll1 othermsgll2,
    length otherppl1 = n ->
    length otherpl1 = n ->
    length othermsgll1 = n ->
    OtherPortPtrList (otherppl1 ++ otherppl2) (otherpl1 ++ otherpl2) (othermsgll1 ++ othermsgll2) ** P ==>
    OtherPortPtrList otherppl1 otherpl1 othermsgll1 **
    OtherPortPtrList otherppl2 otherpl2 othermsgll2 ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H2.
  2: eapply OtherPortPtrList_app';eauto.
  sep normal in H2.
  sep pauto.
  sep auto.
Qed.

Lemma evsllseg_app :
  forall n headptr ectrl1 ectrl2 edatal1 edatal2,
    length ectrl1 = n ->
    length edatal1 = n ->
    evsllseg headptr Vnull (ectrl1 ++ ectrl2) (edatal1 ++ edatal2) ==>
    EX headptr',
      evsllseg headptr headptr' ectrl1 edatal1 **
      evsllseg headptr' Vnull ectrl2 edatal2.
Proof.
  intros ?.
  induction n; intros.
  {
    destruct ectrl1, edatal1; tryfalse.
    cbn in H1.
    exists headptr.
    cbn [evsllseg].
    sep pauto.
  }
  {
    destruct ectrl1, edatal1; tryfalse.
    cbn in H, H0.
    simpl ((_ :: _ ) ++ _) in *.
    cbn [evsllseg ] in H1.
    destruct e, p.
    sep normal in H1.
    sep destruct H1.
    sep split in H1.
    sep lift 2%nat in H1.
    eapply astar_mono in H1.
    3: { intros s' Hs'; exact Hs'. }
    2: { eapply IHn. lia. lia.  }
    sep normal in H1.
    sep destruct H1.
    exists x0.
    cbn [evsllseg ].
    sep normal.
    sep eexists.
    sep split; eauto.
    sep pauto.
  }
Qed. 

Lemma evsllseg_app_frm :
  forall n headptr ectrl1 ectrl2 edatal1 edatal2 P,
    length ectrl1 = n ->
    length edatal1 = n ->
    evsllseg headptr Vnull (ectrl1 ++ ectrl2) (edatal1 ++ edatal2) ** P ==>
    EX headptr',
      evsllseg headptr headptr' ectrl1 edatal1 **
      evsllseg headptr' Vnull ectrl2 edatal2 ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H1.
  2: eapply evsllseg_app; eauto.
  sep normal in H1.
  sep pauto.
  sep auto.
Qed.

Lemma evsllseg_app' :
  forall n headptr eptrls pptr ectrl1 ectrl2 edatal1 edatal2,
    length ectrl1 = n ->
    length edatal1 = n ->
    RL_ECBPtrList headptr Vnull (ectrl1 ++ ectrl2) eptrls ->
    nth_error eptrls n = Some pptr ->
    evsllseg headptr Vnull (ectrl1 ++ ectrl2) (edatal1 ++ edatal2) ==>
      evsllseg headptr (Vptr pptr) ectrl1 edatal1 **
      evsllseg (Vptr pptr) Vnull ectrl2 edatal2.
Proof.
  intros ?.
  induction n;intros.
  {
    destruct ectrl1, edatal1, eptrls; tryfalse.
    cbn in H1, H2.
    inverts H2.
    destruct ectrl2; tryfalse.
    cbn in H1.
    simpljoin1.
    cbn [evsllseg].
    sep pauto.
  }
  destruct ectrl1, edatal1, eptrls; tryfalse.
  cbn in H, H0, H1, H2.
  destruct e, p.
  simpljoin1.
  simpl ((_ :: _ ) ++ _) in *.
  cbn [evsllseg] in H3.
  sep normal in H3.
  sep destruct H3.
  sep split in H3.
  rewrite H1 in H4.
  inverts H4.
  sep lift 2%nat in H3.
  eapply astar_mono in H3.
  3: { intros s' Hs'; exact Hs'. }
  2: { eapply IHn. lia. lia. eauto. eauto. }
  sep normal in H3.
  cbn [evsllseg ].
  sep normal.
  sep eexists.
  sep split;eauto.
  sep pauto.
Qed.

Lemma evsllseg_app'_frm :
  forall n headptr eptrls pptr ectrl1 ectrl2 edatal1 edatal2 P,
    length ectrl1 = n ->
    length edatal1 = n ->
    RL_ECBPtrList headptr Vnull (ectrl1 ++ ectrl2) eptrls ->
    nth_error eptrls n = Some pptr ->
    evsllseg headptr Vnull (ectrl1 ++ ectrl2) (edatal1 ++ edatal2) ** P ==>
      evsllseg headptr (Vptr pptr) ectrl1 edatal1 **
      evsllseg (Vptr pptr) Vnull ectrl2 edatal2 ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H3.
  2: eapply evsllseg_app'; eauto.
  sep normal in H3.
  sep pauto.
  sep auto.
Qed.

Lemma OtherPortPtrList_compose:
  forall otherppl1 otherppl2 otherpl1 otherpl2 othermsgll1 othermsgll2
        pptr dport msg s P v'18,
    length otherpl1 = length otherppl1 ->
    length otherpl1 = length othermsgll1 ->
    struct_type_vallist_match' OS_Port_Seg_dls dport ->
    OS_Port_V_OSQStart dport = Some (Vptr v'18) ->
    s |=  OtherPortPtrList otherppl2 otherpl2 othermsgll2 **
          OtherPortPtrList otherppl1 otherpl1 othermsgll1 **
          APortStruct pptr dport **
         (
          [|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
          dmportp_sllseg_sampleport_msg v'18 msg \\//
          (EX (qend qin qout : addrval)
           (qsize qentries : int32) vl2,
           [|OS_Port_V_mode dport =
             Some (Vint32 (ZToInt QUEUE))|] **
           [|OS_Port_V_OSQEnd dport = Some (Vptr qend)|] **
           [|OS_Port_V_OSQIn dport = Some (Vptr qin)|] **
           [|OS_Port_V_OSQOut dport = Some (Vptr qout)|] **
           [|OS_Port_V_OSQSize dport = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535|] **
           [|OS_Port_V_OSQEntries dport = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize|] **
           [| Qport_msg_ptrs_P v'18 qend qout qin (Int.unsigned qsize) |] **
           dmportp_sllseg_qport_msg qout qin v'18 qend ∘ (Int.unsigned qentries) msg **
           dmportp_sllseg_qport_msg qin qout v'18 qend (nat_of_Z (Int.unsigned qsize - Int.unsigned qentries)) vl2) ) ** P
    ->
    s |= OtherPortPtrList (otherppl1 ++ pptr :: otherppl2) (otherpl1 ++ dport :: otherpl2)
        (othermsgll1 ++ msg :: othermsgll2) ** P.
Proof.
  induction otherppl1; intros.
  {
    destruct otherpl1; destruct othermsgll1; tryfalse.
    do 3 rewrite app_nil_l.
    cbn [OtherPortPtrList] in *.
    sep normal; sep eexists; sep autocancel; sep split; eauto.
  }
  destruct otherpl1; destruct othermsgll1; tryfalse.
  do 3 rewrite <- app_comm_cons.
  cbn [OtherPortPtrList] in *.
  sep normal in H3; sep destruct H3; sep split in H3.
  sep normal; sep eexists; sep autocancel; sep split; eauto.
  simpl in H, H0; apply Nat.succ_inj in H, H0.
  apply astar_r_aemp_elim.
  eapply IHotherppl1 with (pptr:= pptr); eauto.
  sep pauto.
Qed.

Lemma dmportp_sllseg_compose:
  forall s headptr dportl1 dport dportl2 dportmsgll1 msg dportmsgll2 P pptr v'16 v'18,
    length dportmsgll1 = length dportl1 ->
    OS_Port_V_nextPort dport = Some v'16 ->
    struct_type_vallist_match' OS_Port_Seg_dls dport ->
    OS_Port_V_OSQStart dport = Some (Vptr v'18) ->
    s |=  dmportp_sllseg headptr (Vptr pptr) dportl1 dportmsgll1 OS_Port_V_nextPort ** 
          dmportp_sllseg v'16 Vnull dportl2 dportmsgll2 OS_Port_V_nextPort **
          APortStruct pptr dport **
         (
          [|OS_Port_V_mode dport = Some (Vint32 (ZToInt SAMPLE))|] **
          dmportp_sllseg_sampleport_msg v'18 msg \\//
          (EX (qend qin qout : addrval) (qsize qentries : int32) (vl2 : list vallist),
           [|OS_Port_V_mode dport =
             Some (Vint32 (ZToInt QUEUE))|] **
           [|OS_Port_V_OSQEnd dport = Some (Vptr qend)|] **
           [|OS_Port_V_OSQIn dport = Some (Vptr qin)|] **
           [|OS_Port_V_OSQOut dport = Some (Vptr qout)|] **
           [|OS_Port_V_OSQSize dport = Some (Vint32 qsize) /\ Int.unsigned qsize <= 65535|] **
           [|OS_Port_V_OSQEntries dport = Some (Vint32 qentries) /\ Int.unsigned qentries <= Int.unsigned qsize|] **
           [| Qport_msg_ptrs_P v'18 qend qout qin (Int.unsigned qsize) |] **
           dmportp_sllseg_qport_msg qout qin v'18 qend ∘ (Int.unsigned qentries) msg ** 
           dmportp_sllseg_qport_msg qin qout v'18 qend (nat_of_Z (Int.unsigned qsize - Int.unsigned qentries)) vl2 ) 
           ) ** P
    ->
    s |= dmportp_sllseg headptr Vnull (dportl1 ++ dport :: dportl2)
        (dportmsgll1 ++ msg :: dportmsgll2) OS_Port_V_nextPort ** P.
Proof.
  intros ? ? ?; revert s headptr.
  induction dportl1; intros.
  {
    destruct dportmsgll1; tryfalse.
    do 2 rewrite app_nil_l.
    cbn [dmportp_sllseg] in *.
    sep normal; sep eexists; sep autocancel; sep split; eauto.
  }
  destruct dportmsgll1; tryfalse.
  do 2 rewrite <- app_comm_cons.
  cbn [dmportp_sllseg] in *.
  sep normal in H3; sep destruct H3; sep split in H3.
  sep normal; sep eexists; sep autocancel; sep split; eauto.
  simpl in H; apply Nat.succ_inj in H.
  apply astar_r_aemp_elim.
  eapply IHdportl1 with (pptr:= pptr); eauto.
  do 2 sep cancel dmportp_sllseg.
  sep cancel APortStruct.
  apply step_prop.StarEmpIR; apply H3.
Qed.

Lemma kportNode_P_getsome:
  forall n kportvl kpptr kportl kport,
    nth_error kportvl n = Some (Vptr kpptr) ->
    nth_error kportl n = Some kport ->
    kportNode_P kportvl kportl ==>
    EX b kportvl1 kportvl2 kportl1 kportl2,
      kportNode_P kportvl1 kportl1 **
      [| kpptr = (b,Int.zero) /\ struct_type_vallist_match OS_K_Port kport |] ** 
      Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport)  **
      kportNode_P kportvl2 kportl2 **
      [| kportvl = kportvl1 ++ (Vptr kpptr) :: kportvl2 |] **
      [| kportl = kportl1 ++ kport :: kportl2 |] ** 
      [| length kportvl1 = n /\ length kportl1 = n |].
Proof.
  intro.
  induction n; intros.
  {
    destruct kportvl; destruct kportl; tryfalse.
    cbn [kportNode_P] in H1.
    simpl in H; simpl in H0; inversion H0; subst.
    apply disj_star_elim_disj in H1 as [? | ?].
    { sep split in H1. destruct H2; tryfalse. }
    inverts H.
    sep pauto; eauto; inverts H.
    3: instantiate (1:= kportl); instantiate (1:= nil); auto.
    3: instantiate (1:= kportvl); instantiate (1:= nil); auto.
    cbn [kportNode_P]; sep pauto.
    auto.
    eauto.
  }
  {
    destruct kportvl; destruct kportl; tryfalse.
    simpl in H; simpl in H0.
    cbn [kportNode_P] in H1.
    apply disj_star_elim_disj in H1 as [? | ?].
    {
      sep split in H1.
      apply astar_l_aemp_intro in H1.
      eapply astar_mono in H1.
      2: eauto.
      2: eapply IHn; eauto.
      eapply astar_l_aemp_elim in H1.
      sep normal in H1; sep destruct H1; sep split in H1.
      exists x (v :: x0) x1 (v0 :: x2) x3.
      sep pauto.
      cbn [kportNode_P].
      sep pauto; left; sep pauto.
      split; simpl; lia.
    }
    {
      sep normal in H1; sep destruct H1; sep split in H1.
      eapply astar_mono in H1.
      2: eauto.
      2: eapply IHn; eauto.
      sep normal in H1; sep destruct H1; sep split in H1.
      exists x0 (v :: x1) x2 (v0 :: x3) x4.
      sep pauto.
      cbn [kportNode_P].
      sep pauto; right; sep pauto.
      split; simpl; lia.
    }
  }
Qed.

Lemma kportNode_P_getsome_frm:
  forall n kportvl kpptr kportl kport P,
    nth_error kportvl n = Some (Vptr kpptr) ->
    nth_error kportl n = Some kport ->
    kportNode_P kportvl kportl ** P ==>
    EX b kportvl1 kportvl2 kportl1 kportl2,
      kportNode_P kportvl1 kportl1 **
      [| kpptr = (b,Int.zero) /\ struct_type_vallist_match OS_K_Port kport |] ** 
      Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport) **
      kportNode_P kportvl2 kportl2 **
      [| kportvl = kportvl1 ++ (Vptr kpptr) :: kportvl2 |] **
      [| kportl = kportl1 ++ kport :: kportl2 |] ** 
      [| length kportvl1 = n /\ length kportl1 = n |] ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H1.
  2: eapply kportNode_P_getsome; eauto.
  sep normal in H1.
  sep pauto.
  sep auto.
Qed.

Lemma kportNode_P_compose:
  forall s kportvl1 kpptr kportvl2 kportl1 kport kportl2 P b,
    length kportvl1 = length kportl1 ->
    struct_type_vallist_match OS_K_Port kport ->
    kpptr = (b, Int.zero) ->
    s |= kportNode_P kportvl1 kportl1 **
         Astruct' kpptr OS_K_Port_Seg_dls (firstn 6 kport) **
         kportNode_P kportvl2 kportl2 ** P ->
    s |= kportNode_P (kportvl1 ++ (Vptr kpptr) :: kportvl2) (kportl1 ++ kport :: kportl2) ** P.
Proof.
  intros ? ?; revert s; induction kportvl1; intros.
  {
    destruct kportl1; tryfalse.
    do 2 rewrite app_nil_l.
    cbn [kportNode_P] in *; sep pauto.
    right; sep pauto.
  }
  destruct kportl1; tryfalse; simpl in H.
  do 2 rewrite <- app_comm_cons.
  cbn [kportNode_P] in *; sep pauto.
  apply Nat.succ_inj in H.
  remember (b, Int.zero) as kpptr.
  apply step_prop.StarEmpIR in H2; sep normal in H2.
  lets IH: IHkportvl1 H H0 Heqkpptr H2; sep pauto.
Qed.

Lemma ChannelNode_compose:
  forall s chanvl1 v'34 v'35 v'36 chanvl2 chanl1 chan chanl2 chandstportll1 dstportl chandstportll2 P,
    length chanvl1 = length chanl1 ->
    length chanvl1 = length chandstportll1 ->
    OS_Channel_V_dstPortsHead chan = Some v'34 ->
    OS_Channel_V_dstPortsNum chan = Some (Vint32 v'35) ->
    struct_type_vallist_match OS_Channel chan ->
    s |= ChannelNode chanvl1 chanl1 chandstportll1 **
         Astruct (v'36, Int.zero) OS_Channel chan **
         ChannelNode chanvl2 chanl2 chandstportll2 **
         Channel_dstkport_get v'34 Vnull ∘ (Int.unsigned v'35) dstportl ** P ->
    s |= ChannelNode (chanvl1 ++ (Vptr (v'36, Int.zero)) :: chanvl2)
        (chanl1 ++ chan :: chanl2)
        (chandstportll1 ++ dstportl :: chandstportll2) ** P.
Proof.
  intros ? ?; revert s; induction chanvl1; intros.
  {
    destruct chanl1; destruct chandstportll1; tryfalse.
    do 3 rewrite app_nil_l.
    cbn [ChannelNode] in *; sep auto.
    right; unfold node.
    sep normal; sep eexists; sep split.
    sep autocancel.
    split; pauto. auto. auto.
  }
  destruct chanl1; destruct chandstportll1; tryfalse.
  do 3 rewrite <- app_comm_cons.
  cbn [ChannelNode] in *; sep pauto.
  simpl in H; apply Nat.succ_inj in H.
  simpl in H0; apply Nat.succ_inj in H0.
  apply step_prop.StarEmpIR in H4; sep normal in H4.
  lets IH: IHchanvl1 H H0 H1 H2 H3 H4; sep pauto.
Qed.

Lemma ChannelNode_getsome:
  forall n chanvl chanptr chanl chan chandstportll dstportl,
    nth_error chanvl n = Some (Vptr chanptr) ->
    nth_error chanl n = Some chan ->
    nth_error chandstportll n = Some dstportl ->
      ChannelNode chanvl chanl chandstportll ==>
      EX chanvl1 chanl1 chandstportll1 chanvl2 chanl2 chandstportll2 dphead dpnum,
        [| chanvl = chanvl1 ++ (Vptr chanptr) :: chanvl2 |] **
        [| chanl = chanl1 ++ chan :: chanl2 |] **
        [| chandstportll = chandstportll1 ++ dstportl :: chandstportll2 |] **
        ChannelNode chanvl1 chanl1 chandstportll1 **
        ChannelNode chanvl2 chanl2 chandstportll2 **
        [| length chanvl1 = n /\ length chanl1 = n /\ length chandstportll1 = n |] **
        node (Vptr chanptr) chan OS_Channel **
        [| OS_Channel_V_dstPortsHead chan = Some dphead |] **
        [| OS_Channel_V_dstPortsNum chan = Some (Vint32 dpnum) |] **
        Channel_dstkport_get dphead Vnull (nat_of_Z (Int.unsigned dpnum)) dstportl.
Proof.
  intro; induction n; intros.
  {
    destruct chanvl; destruct chanl; destruct chandstportll; tryfalse.
    cbn [ChannelNode] in H2.
    simpl in H; simpl in H0; simpl in H1; inverts H; inverts H0; inverts H1.
    apply disj_star_elim_disj in H2 as [? | ?].
    sep split in H; destruct H0 as [? [? ?]]; tryfalse.
    sep pauto; eauto.
    3: instantiate (1:= chandstportll); instantiate (1:= nil); auto.
    3: instantiate (1:= chanl); instantiate (1:= nil); auto.
    3: instantiate (1:= chanvl); instantiate (1:= nil); auto.
    cbn [ChannelNode]; sep pauto.
    auto.
  }
  {
    destruct chanvl; destruct chanl; destruct chandstportll; tryfalse.
    simpl in H; simpl in H0; simpl in H1.
    cbn [ChannelNode] in H2.
    apply disj_star_elim_disj in H2 as [? | ?].
    {
      sep split in H2.
      apply astar_l_aemp_intro in H2.
      eapply astar_mono in H2.
      2: eauto.
      2: eapply IHn; eauto.
      sep normal in H2; sep destruct H2; sep split in H2.
      exists (v :: x) (v0 :: x0) (l :: x1) x2 x3 x4.
      cbn [ChannelNode].
      sep normal; sep eexists; sep split; eauto.
      sep autocancel; left; sep auto.
      simpl; lia.
      all: subst; auto.
    }
    {
      sep normal in H2; sep destruct H2; sep split in H2.
      sep lift 3%nat in H2.
      eapply astar_mono in H2.
      2: eapply IHn; eauto.
      2: eauto.
      sep normal in H2; sep destruct H2; sep split in H2.
      exists (v :: x1) (v0 :: x2) (l :: x3) x4 x5 x6.
      cbn [ChannelNode].
      sep normal; sep eexists; sep split; eauto.
      sep autocancel; right; sep pauto.
      simpl; lia.
      all: subst; auto.
    }
  }
Qed.

Lemma ChannelNode_getsome_frm:
  forall n chanvl chanptr chanl chan chandstportll dstportl P,
    nth_error chanvl n = Some (Vptr chanptr) ->
    nth_error chanl n = Some chan ->
    nth_error chandstportll n = Some dstportl ->
      ChannelNode chanvl chanl chandstportll ** P ==>
      EX chanvl1 chanl1 chandstportll1 chanvl2 chanl2 chandstportll2 dphead dpnum,
        [| chanvl = chanvl1 ++ (Vptr chanptr) :: chanvl2 |] **
        [| chanl = chanl1 ++ chan :: chanl2 |] **
        [| chandstportll = chandstportll1 ++ dstportl :: chandstportll2 |] **
        ChannelNode chanvl1 chanl1 chandstportll1 **
        ChannelNode chanvl2 chanl2 chandstportll2 **
        [| length chanvl1 = n /\ length chanl1 = n /\ length chandstportll1 = n |] **
        node (Vptr chanptr) chan OS_Channel **
        [| OS_Channel_V_dstPortsHead chan = Some dphead |] **
        [| OS_Channel_V_dstPortsNum chan = Some (Vint32 dpnum) |] **
        Channel_dstkport_get dphead Vnull (nat_of_Z (Int.unsigned dpnum)) dstportl ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H2.
  2: eapply ChannelNode_getsome; eauto.
  sep normal in H2.
  sep pauto.
  sep auto.
Qed.

Lemma sep_exist_Afalse: forall s,
  s |= Afalse -> False.
Proof.
  intros.
  eapply astar_l_afalse_intro in H.
  eapply astar_mono in H.
  2: sep auto.
  2: instantiate (2:=[|1 = 0|]); sep auto.
  sep split in H; tryfalse.
Qed.

Lemma Channel_dstkport_get_app:
  forall dstkportl1 dstkportl2 m dstkptr headptr n,
    length dstkportl1 = m ->
    Channel_dstkport_get headptr Vnull n (dstkportl1 ++ dstkptr :: dstkportl2) ==>
    Channel_dstkport_get headptr (Vptr dstkptr) m dstkportl1 **
    EX vl vn ,
      [| struct_type_vallist_match OS_K_Port vl |] **
      PV (get_off_addr dstkptr (Int.repr 12)) @ (Tptr Tvoid) |-> vn **
      [| OS_K_Port_V_OSEventPtr vl = Some vn |] **
      Channel_dstkport_get vn Vnull (n - m - 1%nat)%nat dstkportl2.
Proof.
  intro; induction dstkportl1; intros.
  {
    destruct m; tryfalse.
    rewrite app_nil_l in *.
    destruct n; cbn [Channel_dstkport_get] in *.
    exfalso; eapply sep_exist_Afalse; eauto.
    sep normal in H0; sep destruct H0; sep split in H0; inverts H2.
    sep normal; sep eexists; sep split; eauto.
    assert ((S n - 0%nat - 1%nat)%nat = n) by (clear; mauto).
    rewrite H2; sep pauto.
  }
  destruct m; tryfalse.
  simpl ((_ :: _ ) ++ _) in *.
  simpl in H; inversion H; clear H.
  destruct n; cbn [Channel_dstkport_get] in *.
  exfalso; eapply sep_exist_Afalse; eauto.
  unfold node in H0.
  sep normal in H0; sep destruct H0; sep split in H0.
  inverts H3.
  assert (isptr x0).
  {
    clear - H H1.
    unfold struct_type_vallist_match, OS_K_Port, struct_type_vallist_match' in H.
    unfold OS_K_Port_V_OSEventPtr in H1.
    destruct x; tryfalse.
    do 6 (destruct H as [? H]; destruct x; tryfalse).
    destruct H; simpl in H1; inverts H1; simpl in H.
    unfold isptr.
    clear - H.
    destruct x0; pauto.
  }
  destruct H3 as [? | [? ?]]; subst x0.
  {
    destruct n; cbn [Channel_dstkport_get] in *.
    {
      destruct (dstkportl1 ++ dstkptr :: dstkportl2) eqn: I.
      {
        exfalso; clear - I.
        apply length_zero_iff_nil in I.
        destruct dstkportl1.
        rewrite app_nil_l in I; simpl in I; tryfalse.
        simpl ((_ :: _ ) ++ _) in *; simpl in I; tryfalse.
      }
      sep lift 2%nat in H0.
      eapply astar_l_afalse_elim in H0.
      exfalso; eapply sep_exist_Afalse; eauto.
    }
    destruct (dstkportl1 ++ dstkptr :: dstkportl2) eqn: I.
    {
      sep lift 2%nat in H0.
      eapply astar_l_afalse_elim in H0.
      exfalso; eapply sep_exist_Afalse; eauto.
    }
    sep split in H0. inverts H3.
  }
  eapply astar_mono in H0.
  2: eauto.
  2: eapply IHdstkportl1.
  2: eapply H2.
  sep normal in H0; sep destruct H0; sep split in H0.
  sep normal.
  exists x (Vptr x1) x0 x2.
  sep split; eauto.
  rewrite H2 in *.
  sep autocancel.
Qed.

Lemma Channel_dstkport_get_app_frm:
  forall dstkportl1 dstkportl2 m dstkptr n headptr P,
    length dstkportl1 = m ->
    Channel_dstkport_get headptr Vnull n (dstkportl1 ++ dstkptr :: dstkportl2) ** P ==>
    Channel_dstkport_get headptr (Vptr dstkptr) m dstkportl1 **
    (EX vl vn ,
      [| struct_type_vallist_match OS_K_Port vl |] **
      PV (get_off_addr dstkptr (Int.repr 12)) @ (Tptr Tvoid) |-> vn **
      [| OS_K_Port_V_OSEventPtr vl = Some vn |] **
      Channel_dstkport_get vn Vnull (n - m - 1%nat)%nat dstkportl2) ** P.
Proof.
  intros.
  eapply astar_mono with (Q':= P)in H0.
  2: eapply Channel_dstkport_get_app; eauto.
  sep normal in H0.
  sep pauto.
  all: eauto.
Qed.

Lemma dmportp_sllseg_qport_msg_ngt0 :forall qout qin qstart qend n msgl P,
  (n > 0)%nat -> 
  dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P ==>
  [| exists msg msgl', msgl = msg :: msgl' /\ Z.of_nat (length (msg)) <= CHANNEL_CACHE_SZIE |] ** dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P.
Proof.
  intros.
  destruct n;[lia | ].
  destruct msgl.
  cbn [dmportp_sllseg_qport_msg] in H0.
  apply astar_l_afalse_elim in H0. tryfalse.
  cbn [dmportp_sllseg_qport_msg] in *.
  sep normal in H0. sep destruct H0. sep split in H0.
  sep pauto.
  do 2 eexists;split;eauto.
  unfold CHANNEL_CACHE_SZIE in *.
  rewrite <- Zabs2Nat.abs_nat_nonneg in H1 by lia.
  lia.
Qed.

Lemma dmportp_sllseg_Forall_struct_type_vallist_match':
  forall dportl headptr tailptr dportmsgll P,
    dmportp_sllseg headptr tailptr dportl dportmsgll OS_Port_V_nextPort ** P ==>
    [| Forall (struct_type_vallist_match' OS_Port_Seg_dls) dportl |] **
    dmportp_sllseg headptr tailptr dportl dportmsgll OS_Port_V_nextPort ** P.
Proof.
  induction dportl; intros.
  destruct dportmsgll; cbn [dmportp_sllseg] in *; sep pauto.
  destruct dportmsgll; cbn [dmportp_sllseg] in *.
  sep cancel P; apply sep_exist_Afalse in H; tryfalse.
  sep split; sep pauto.
  apply Forall_cons;
  sep normal in H; sep destruct H; sep split in H; auto.
  sep lifts (3::nil)%nat in H.
  apply IHdportl in H.
  sep pauto.
Qed.

Lemma dmportp_sllseg_qport_msg_split :forall pnow pend qstart qend n msgl P,
  (n > 0)%nat -> 
  dmportp_sllseg_qport_msg pnow pend qstart qend n msgl ** P ==>
  EX msg msgl', [| msgl = msg :: msgl' /\ Z.of_nat (length (msg)) <= CHANNEL_CACHE_SZIE |] ** 
  PV pnow @ Tint8 |-> (Vint32 ($ (Z.of_nat (length msg)))) **
  (EX invalidmsg, [| (length msg + length invalidmsg = nat_of_Z CHANNEL_CACHE_SZIE)%nat /\
  array_type_vallist_match Tint8 (msg++invalidmsg)|] **
  Aarray (get_off_addr pnow (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++invalidmsg)) **
  dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next pnow qstart qend) pend qstart qend (pred n) msgl' ** P.
Proof.
  intros.
  destruct n;[lia | ].
  destruct msgl.
  cbn [dmportp_sllseg_qport_msg] in H0.
  apply astar_l_afalse_elim in H0. tryfalse.
  cbn [dmportp_sllseg_qport_msg] in *.
  sep normal in H0. sep destruct H0. sep split in H0.
  sep pauto.
  splits; auto. 
  unfold CHANNEL_CACHE_SZIE in *. clear - H1.
  unfold Coqlib.nat_of_Z in H1. lia.
Qed.
 
Lemma dmportp_sllseg_qport_msg_merge :forall pnow pend qstart qend n msg invalidmsg msgl P,
  (n > 0)%nat -> 
  Z.of_nat (length (msg)) <= CHANNEL_CACHE_SZIE ->
  (length msg + length invalidmsg = nat_of_Z CHANNEL_CACHE_SZIE)%nat ->
  array_type_vallist_match Tint8 (msg++invalidmsg)->
  PV pnow @ Tint8 |-> (Vint32 ($ (Z.of_nat (length msg)))) **
  Aarray (get_off_addr pnow (Int.one)) (Tarray Tint8 (nat_of_Z CHANNEL_CACHE_SZIE)) (msg++invalidmsg) **
  dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next pnow qstart qend) pend qstart qend (pred n) msgl ** P ==>
  dmportp_sllseg_qport_msg pnow pend qstart qend n (msg::msgl) ** P.
Proof.
  intros.
  destruct n;[lia | ].
  cbn [dmportp_sllseg_qport_msg].
  sep normal. sep eexists. sep split; eauto.
  sep pauto.
Qed.

Lemma dmportp_sllseg_qport_msg_append_tail_lemma:forall n pnow pendb pendo qstart qend  mlen msg msgl P,
  length msg = Z.to_nat (Int.unsigned mlen) -> 
  Int.unsigned mlen <= CHANNEL_CACHE_SZIE ->
  EX invalidmsg, 
  dmportp_sllseg_qport_msg pnow (pendb, pendo) qstart qend n msgl **
  PV (pendb, pendo) @ Tint8 |-> (Vint32 mlen) **
  Aarray (pendb, pendo +ᵢ  Int.one) (Tarray char_t (Z.to_nat (Int.unsigned mlen))) msg **
  [| array_type_vallist_match Tint8 (msg++invalidmsg)|] **
  Aarray (get_off_addr (pendb, pendo +ᵢ  Int.one)
              (Int.mul ($ Z.of_nat (Z.to_nat (Int.unsigned mlen)))
                 ($ Z.of_nat (typelen char_t))))
           (Tarray char_t
              (∘ CHANNEL_CACHE_SZIE -
               Z.to_nat (Int.unsigned mlen))) invalidmsg **
  P ==>
  dmportp_sllseg_qport_msg pnow (dmportp_sllseg_qport_msg_next (pendb, pendo) qstart qend) qstart qend (S n) (msgl++(msg::nil)) ** P.
Proof.
  induction n; intros.
  + cbn [dmportp_sllseg_qport_msg] in H1. sep destruct H1.
    destruct msgl.
    - sep split in H1. subst. simpl app. cbn [dmportp_sllseg_qport_msg].
      sep normal. exists x.
      sep name lift x in H1.
      lets Hs: Aarray_vl_len_eq H1.
      assert ((length msg + length x)%nat = ∘ CHANNEL_CACHE_SZIE).
      { rewrite H. rewrite Hs. unfold Coqlib.nat_of_Z. lia. }
      sep split; auto.
      rewrite H. rewrite Z2Nat.id by apply Int.unsigned_range. 
      rewrite <- H2. apply Aarray_merge. 
      rewrite H2. cbv. intros. congruence.
      1,2: reflexivity. rewrite Hs. rewrite H.
      unfold get_off_addr at 1. cbn [fst snd]. sep autocancel.
      rewrite Int.repr_unsigned. assumption.
    - apply astar_l_afalse_elim in H1. tauto.
  + sep destruct H1. cbn [dmportp_sllseg_qport_msg] in H1.
    destruct msgl.
    - apply astar_l_afalse_elim in H1. tauto.
    - sep normal in H1. sep destruct H1. sep split in H1.
      simpl app. remember (msgl ++ msg :: nil) as vl.
      cbn [dmportp_sllseg_qport_msg]. sep normal. sep eexists.
      sep split; auto.
      do 2 sep cancel 1%nat 1%nat.
      cut (s
      |=  dmportp_sllseg_qport_msg (dmportp_sllseg_qport_msg_next pnow qstart qend) 
      (dmportp_sllseg_qport_msg_next (pendb, pendo) qstart qend) qstart qend
      (S n) (msgl ++ msg :: nil)**P).
      * intros. cbn [dmportp_sllseg_qport_msg] in H4. subst vl. assumption.
      * eapply IHn; eauto. 
        sep eexists. sep autocancel. sep auto.
      * tauto.
Qed.

Lemma dmportp_sllseg_qport_msg_append_tail:forall n pnow pendb pendo qstart qend  mlen msg msgl P,
  length msg = Z.to_nat (Int.unsigned mlen) -> 
  Int.unsigned n < 65535 ->
  Int.unsigned mlen <= CHANNEL_CACHE_SZIE ->
  EX invalidmsg, 
  dmportp_sllseg_qport_msg pnow (pendb, pendo) qstart qend (Z.to_nat (Int.unsigned n)) msgl **
  PV (pendb, pendo) @ Tint8 |-> (Vint32 mlen) **
  Aarray (pendb, pendo +ᵢ  Int.one) (Tarray char_t (Z.to_nat (Int.unsigned mlen))) msg **
  [| array_type_vallist_match Tint8 (msg++invalidmsg)|] **
  Aarray (get_off_addr (pendb, pendo +ᵢ  Int.one)
              (Int.mul ($ Z.of_nat (Z.to_nat (Int.unsigned mlen)))
                 ($ Z.of_nat (typelen char_t))))
           (Tarray char_t
              (∘ CHANNEL_CACHE_SZIE -
               Z.to_nat (Int.unsigned mlen))) invalidmsg **
  P ==>
  dmportp_sllseg_qport_msg pnow (dmportp_sllseg_qport_msg_next (pendb, pendo) qstart qend) qstart qend (Z.to_nat(Int.unsigned (n +ᵢ  $ 1))) (msgl++(msg::nil)) ** P.
Proof.
  intros.
  assert (Z.to_nat(Int.unsigned (n +ᵢ  $ 1)) = S (Z.to_nat(Int.unsigned n))).
  {
    apply Int_add_one_Sn. lia.
  }
  rewrite H3.
  eapply dmportp_sllseg_qport_msg_append_tail_lemma; eauto.
Qed.

Lemma OtherPortPtrList_Forall_struct_type_vallist_match':
  forall otherppl otherpl othermsgll P,
    OtherPortPtrList otherppl otherpl othermsgll ** P ==>
    [| Forall (struct_type_vallist_match' OS_Port_Seg_dls) otherpl |] **
    OtherPortPtrList otherppl otherpl othermsgll ** P.
Proof.
  induction otherppl; intros.
  destruct otherpl; cbn [OtherPortPtrList] in *; sep pauto.
  eapply astar_l_afalse_elim in H.
  apply sep_exist_Afalse in H; tryfalse.
  destruct otherpl; destruct othermsgll; cbn [OtherPortPtrList] in *.
  all: try eapply astar_l_afalse_elim in H.
  all: try apply sep_exist_Afalse in H; tryfalse.
  sep split; sep pauto.
  apply Forall_cons;
  sep normal in H; sep destruct H; sep split in H; auto.
  sep lifts (3::nil)%nat in H.
  apply IHotherppl in H.
  sep pauto.
Qed.

Lemma update_nth_same:
  forall [A:Type] dportl1 x1 dport dportl2 x3,
  (x3 < length dportl1)%nat->
  nth_error
    (ifun_spec.update_nth A x3 dportl1 x1 ++
    dport :: dportl2) x3 = Some x1.
Proof.
  induction dportl1; destruct x3; simpl; intros; try lia; auto.
  apply IHdportl1; lia.
Qed.

Lemma update_nth_same':
  forall [A:Type] dportl1 x1 dport dportl2 x3,
  (x3 > length dportl1)%nat->
  (x3 < length (dportl1 ++ dport :: dportl2))%nat ->
  nth_error (dportl1 ++ dport
   :: ifun_spec.update_nth A (x3 - S (length dportl1))
        dportl2 x1) x3 = Some x1.
Proof.
  induction dportl1; destruct x3; simpl; try lia; intros.
  {
    assert ((x3 - 0)%nat = x3) by lia. rewrite H1.
    assert ((x3 < length dportl2)%nat) by lia; clear H0 H H1.
    revert x3 H2; induction dportl2; destruct x3; simpl; try lia; auto.
    intros; eapply IHdportl2; lia.
  }
  eapply IHdportl1; lia.
Qed.

Lemma update_nth_dif:
  forall [A:Type] dportl1 x1 dport dportl2 x3 x6 x,
  (x < length dportl1)%nat->
  (x <> x3)%nat ->
  nth_error (dportl1 ++ dport :: dportl2) x3 = Some x6 ->
  nth_error
    (ifun_spec.update_nth A x dportl1 x1 ++
    dport :: dportl2) x3 = Some x6.
Proof.
  induction dportl1; destruct x; destruct x3; simpl; intros; try lia; auto.
  apply IHdportl1; try lia; auto.
Qed.

Lemma update_nth_dif':
  forall [A:Type] dportl1 x1 dport dportl2 x3 x6 x,
  (x > length dportl1)%nat ->
  (x <> x3)%nat ->
  (x < length (dportl1 ++ dport :: dportl2))%nat ->
  nth_error (dportl1 ++ dport :: dportl2) x3 = Some x6 ->
  nth_error (dportl1 ++ dport
    :: ifun_spec.update_nth A (x - S (length dportl1))
          dportl2 x1) x3 = Some x6.
Proof.
  induction dportl1; destruct x; simpl; try lia; intros; auto.
  {
    assert ((x - 0)%nat = x) by lia. rewrite H3.
    assert ((x < length dportl2)%nat) by lia; clear H H1 H3.
    revert x x3 dport H2 H0 H4; induction dportl2; destruct x; simpl; try lia; auto.
    {
      intros; destruct x3; simpl in *; auto.
      destruct x3; simpl in *; try lia; auto.
    }
    intros; destruct x3; simpl in *; auto.
    eapply IHdportl2; eauto. lia.
  }
  destruct x3; simpl in *; auto.
  eapply IHdportl1; try lia; auto.
Qed.

Lemma update_nth_length_same:
  forall [A:Type] dportl1 n0 v,
    length (ifun_spec.update_nth A n0 dportl1 v) = length dportl1.
Proof.
  induction dportl1; destruct n0; simpl; intros; try lia; auto.
Qed.

Lemma set_dportl_msgll_get_srcptr:
  forall n dportl1 dport dportl2 dportmsgll1 srcmsgl dportmsgll2
         pptr headptr dstpptrnl dstportupdl msgl dpptrl P,
  RL_PortPtrList headptr (dportl1 ++ dport :: dportl2) dpptrl ->
  (forall m, (m < length dstpptrnl)%nat ->
    exists dstpptrn dstportp dstportupd dstport,
      nth_error dstpptrnl m = Some dstpptrn /\
      nth_error dpptrl dstpptrn = Some dstportp /\
      nth_error (dportl1 ++ dport :: dportl2) dstpptrn = Some dstport /\
      nth_error dstportupdl m = Some dstportupd /\
      OS_Port_V_nextPort dstport = OS_Port_V_nextPort dstportupd /\
      OS_Port_V_direction dstport = Some (Vint32 (Int.repr DESTINATION)) /\
      OS_Port_V_direction dstportupd = Some (Vint32 (Int.repr DESTINATION))) ->
  (n <= length dstpptrnl)%nat ->
  length dstpptrnl = length dstportupdl ->
  nth_error dpptrl (length dportl1) = Some pptr ->
  length dportmsgll1 = length dportl1 ->
  OS_Port_V_direction dport = Some (Vint32 (Int.repr SOURCE)) ->
  dmportp_sllseg headptr Vnull
    (set_dportl_n_times (dportl1 ++ dport :: dportl2) n dstpptrnl dstportupdl)
    (set_dportmsgll_n_times (dportmsgll1 ++ srcmsgl :: dportmsgll2) n dstpptrnl msgl)
    OS_Port_V_nextPort ** P ==>
  EX dportl1' dportl2' dportmsgll1' dportmsgll2',
    [| length dportl1' = length dportmsgll1' |] **
    [| length dportl1 = length dportl1' |] **
    [| RL_PortPtrList headptr (dportl1' ++ dport :: dportl2') dpptrl |] **
    [| dportl1' ++ dport :: dportl2' = (set_dportl_n_times (dportl1 ++ dport :: dportl2) n dstpptrnl dstportupdl) |] **
    [| dportmsgll1' ++ srcmsgl :: dportmsgll2' = (set_dportmsgll_n_times (dportmsgll1 ++ srcmsgl :: dportmsgll2) n dstpptrnl msgl) |]  **
    dmportp_sllseg headptr Vnull (dportl1' ++ dport :: dportl2')
      (dportmsgll1' ++ srcmsgl :: dportmsgll2') OS_Port_V_nextPort ** P.
Proof.
  induction n.
  {
    cbn [set_dportl_n_times].
    cbn [set_dportmsgll_n_times].
    intros.
    exists dportl1 dportl2 dportmsgll1 dportmsgll2.
    sep pauto.
  }
  intros.
  destruct dstpptrnl; destruct dstportupdl;
  cbn [set_dportl_n_times] in *; cbn [set_dportmsgll_n_times] in *;
  simpl in H1, H2; try lia.
  assert ((n <= length dstpptrnl)%nat) by lia.
  assert (length dstpptrnl = length dstportupdl) by lia.
  clear H1 H2.
  assert ((n0 = length dportl1)%nat \/ (n0 < length dportl1)%nat \/ (n0 > length dportl1)%nat) by lia.
  destruct H1; subst.
  {
    exfalso.
    assert ((0 < length (length dportl1 :: dstpptrnl))%nat) by (simpl; lia).
    specialize (H0 0%nat H1).
    simpl in H0; simpljoin1; inverts H0.
    rewrite nth_error_middle in H9; inverts H9.
    rewrite H12 in H5; inverts H5.
  }
  destruct H1.
  {
    assert (
      (ifun_spec.update_nth vallist n0 (dportl1 ++ dport :: dportl2) v) = 
      (ifun_spec.update_nth vallist n0 dportl1 v) ++ dport :: dportl2
    ).
    {
      clear - H1.
      revert n0 H1.
      induction dportl1; intros; simpl in H1; try lia.
      destruct n0; simpl in *; auto.
      assert ((n0 < length dportl1)%nat) by lia.
      specialize (IHdportl1 n0 H).
      rewrite IHdportl1.
      auto.
    }
    rewrite H2 in *; clear H2.
    assert(
      (ifun_spec.update_nth (list vallist) n0 (dportmsgll1 ++ srcmsgl :: dportmsgll2) msgl) = 
      (ifun_spec.update_nth (list vallist) n0 dportmsgll1 msgl) ++ srcmsgl :: dportmsgll2
    ).
    {
      rewrite <- H4 in H1.
      clear - H1.
      revert n0 H1.
      induction dportmsgll1; intros; simpl in H1; try lia.
      destruct n0; simpl in *; auto.
      assert ((n0 < length dportmsgll1)%nat) by lia.
      specialize (IHdportmsgll1 n0 H).
      rewrite IHdportmsgll1.
      auto.
    }
    rewrite H2 in *; clear H2.
    assert (length (ifun_spec.update_nth vallist n0 dportl1 v) = length dportl1).
    eapply update_nth_length_same.
    rewrite <- H2; clear H2.
    eapply IHn; auto.
    {
      (* instantiate (1:=dpptrl). *)
      clear - H H0 H1.
      assert ((0 < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
      specialize (H0 0%nat H2).
      simpl in H0; simpljoin1.
      inverts H0; inverts H5.
      clear H2 H7 H8.
      revert headptr x dpptrl H H1 H3 H4 H6.
      induction dportl1; intros; cbn [ifun_spec.update_nth] in *; auto.
      destruct x; destruct dpptrl; simpl in *; tryfalse.
      {
        inverts H4; inverts H3.
        simpljoin1; splits; try eexists; try splits; eauto.
        rewrite <- H0; auto.
      }
      simpljoin1.
      split; auto.
      exists x3; split; auto.
      assert ((x < length dportl1)%nat) by lia.
      apply (IHdportl1 _ _ _ H2 H H3 H4 H6).
    }
    {
      intros.
      assert (((S m) < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
      assert ((0 < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
      pose proof H0 _ H10.
      simpl in H11; simpljoin1.
      inverts H11; inverts H14.
      specialize (H0 _ H9).
      simpl in H0; simpljoin1.
      assert ((x = x3)%nat \/ (x <> x3)%nat) by lia.
      destruct H22.
      {
        exists x3 x4 x5 x1.
        subst x; splits; auto.
        apply update_nth_same; apply H1.
        rewrite H13 in H14; inverts H14.
        rewrite <- H15; auto.
      }
      exists x3 x4 x5 x6.
      splits; auto.
      apply update_nth_dif; auto.
    }
    { rewrite update_nth_length_same; eauto. }
    { do 2 rewrite update_nth_length_same; lia. }
  }
  assert (
    (ifun_spec.update_nth vallist n0 (dportl1 ++ dport :: dportl2) v) = 
    dportl1 ++ dport :: (ifun_spec.update_nth vallist (n0 - S (length dportl1)) dportl2 v)
  ).
  {
    clear - H1.
    revert n0 dport dportl2 H1.
    induction dportl1; destruct n0; simpl; intros; try lia.
    assert ((n0 - 0 = n0)%nat) by lia; rewrite H; auto.
    assert ((n0 > length dportl1)%nat) by lia.
    specialize (IHdportl1 n0 dport dportl2 H).
    rewrite IHdportl1.
    auto.
  }
  rewrite H2 in *; clear H2.
  assert(
    (ifun_spec.update_nth (list vallist) n0 (dportmsgll1 ++ srcmsgl :: dportmsgll2) msgl) = 
    dportmsgll1 ++ srcmsgl :: (ifun_spec.update_nth (list vallist) (n0 - S (length dportmsgll1)) dportmsgll2 msgl)
  ).
  {
    rewrite <- H4 in H1.
    clear - H1.
    revert n0 srcmsgl dportmsgll2 H1.
    induction dportmsgll1; destruct n0; simpl; intros; try lia.
    assert ((n0 - 0 = n0)%nat) by lia; rewrite H; auto.
    assert ((n0 > length dportmsgll1)%nat) by lia.
    specialize (IHdportmsgll1 n0 srcmsgl dportmsgll2 H).
    rewrite IHdportmsgll1.
    auto.
  }
  rewrite H2 in *; clear H2.
  eapply IHn; auto.
  {
    (* instantiate (1:=dpptrl). *)
    clear - H H0 H1.
    assert ((0 < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
    specialize (H0 0%nat H2).
    simpl in H0; simpljoin1.
    inverts H0; inverts H5.
    clear H2 H7 H8.
    revert headptr x dport dportl2 dpptrl H H1 H3 H4 H6.
    induction dportl1; intros; cbn [ifun_spec.update_nth] in *; auto.
    {
      rewrite app_nil_l in *.
      destruct dpptrl; simpl in *; tryfalse.
      simpljoin1.
      splits; eauto.
      exists x3; split; auto.
      revert dpptrl dport x x0 x1 x2 x3 H0 H1 H2 H3 H4 H6.
      induction dportl2; simpl; intros; destruct dpptrl; auto.
      tryfalse.
      destruct x; try lia; simpljoin1; simpl in *.
      assert ((x - 0)%nat = x) by lia. rewrite H.
      destruct x; simpl in *.
      {
        inverts H3; inverts H4.
        split; auto.
        eexists; split; eauto.
        rewrite <- H6; auto.
      }
      split; auto.
      eexists; split; eauto.
      assert ((x = (S x) - 1)%nat) by lia. rewrite H7.
      eapply IHdportl2; eauto; try lia.
    }
    simpl ((_ :: _) ++ _) in *.
    destruct dpptrl; simpl in *; tryfalse.
    simpljoin1.
    split; auto.
    exists x3; split; auto.
    destruct x; try lia; simpl in *.
    eapply IHdportl1; eauto.
    lia.
  }
  {
    intros.
    assert (((S m) < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
    assert ((0 < length (n0 :: dstpptrnl))%nat) by (simpl; lia).
    pose proof H0 _ H10.
    simpl in H11; simpljoin1.
    inverts H11; inverts H14.
    specialize (H0 _ H9).
    simpl in H0; simpljoin1.
    assert ((x = x3)%nat \/ (x <> x3)%nat) by lia.
    destruct H22.
    {
      exists x3 x4 x5 x1.
      subst x; splits; auto.
      apply update_nth_same'; auto.
      {
        apply nth_error_Some.
        rewrite H13. auto.
      }
      rewrite H13 in H14; inverts H14.
      rewrite <- H15; auto.
    }
    exists x3 x4 x5 x6.
    splits; auto.
    apply update_nth_dif'; auto.
    apply nth_error_Some.
    rewrite H13. auto.
  }
  { eauto. }
Qed.

Lemma Channel_dstkport_get_compose:
  forall dstkportl1 dstkportl2 s m headptr dstkptr n vl vn tail,
  length dstkportl1 = m ->
  length dstkportl2 = n ->
  struct_type_vallist_match OS_K_Port vl ->
  OS_K_Port_V_OSEventPtr vl = Some vn ->
  s |= Channel_dstkport_get headptr (Vptr dstkptr) m dstkportl1 **
  PV (get_off_addr dstkptr (Int.repr 12)) @ (Tptr Tvoid) |-> vn **
  Channel_dstkport_get vn tail n dstkportl2 ->
  s |= Channel_dstkport_get headptr tail (S (m + n)) (dstkportl1 ++ dstkptr :: dstkportl2).
Proof.
  induction dstkportl1; intros.
  {
    rewrite app_nil_l.
    simpl (length _) in *; subst.
    cbn [Channel_dstkport_get] in *.
    sep pauto; eauto.
  }
  rewrite <- app_comm_cons.
  simpl (length _ ) in *; subst.
  cbn [Channel_dstkport_get];
  cbn [Channel_dstkport_get] in H3.
  sep normal in H3; sep destruct H3; sep split in H3.
  inverts H4.
  sep pauto; eauto.
Qed.

Fixpoint dmportp_msg_next_n (n :nat) (pnow qstart qend: addrval) : addrval :=
  match n with 
  | O => pnow 
  | S n' => dmportp_msg_next_n n' (dmportp_sllseg_qport_msg_next pnow qstart qend) qstart qend
  end.

Lemma dmportp_msg_next_n_to_qstart:
  forall (x : nat) (qstartb : block) (y : Z),
    (0 < x)%nat -> 0 <= y ->
    Z.of_nat x + y <= 65535 ->
    (qstartb, Int.zero) =
      dmportp_msg_next_n x (qstartb, Int.mul ($ y) ($ 33))
        (qstartb, Int.zero)
        (qstartb, Int.mul ($ (Z.of_nat x + y)) ($ 33)).
Proof.
  induction x; intros; try lia.
  cbn [dmportp_msg_next_n].
  unfold dmportp_sllseg_qport_msg_next.
  unfold msg_distance.
  unfold snd.
  assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
  rewrite H2 in *; clear H2.
  assert (Z.of_nat (S x) <= 65535) by lia.
  assert ($ (Z.of_nat (S x) + y) = ($ (Z.of_nat (S x))) +ᵢ ($ y)).
  { clear - H H0 H1 H2; mauto. }
  rewrite H3.
  assert ((Int.mul ($ Z.of_nat (S x) +ᵢ  $ y) ($ 33)) = Int.mul ($ (Z.of_nat (S x))) ($ 33) +ᵢ Int.mul ($ y) ($ 33)).
  { apply Int.mul_add_distr_l. }
  rewrite H4 at 1.
  assert (((Int.mul ($ Z.of_nat (S x)) ($ 33) +ᵢ
  Int.mul ($ y) ($ 33)) -ᵢ Int.mul ($ y) ($ 33)) = Int.mul ($ Z.of_nat (S x)) ($ 33)).
  { rewrite Int.add_commut, Int.sub_add_l, Int.sub_idem; apply Int.add_zero_l. }
  rewrite H5.
  assert (Int.divu (Int.mul ($ Z.of_nat (S x)) ($ 33)) ($ 33) = ($ Z.of_nat (S x))).
  { clear - H2. mauto. rewrite Z_div_mult; mauto. }
  rewrite H6. destruct x.
  {
    assert (Int.unsigned ($ Z.of_nat 1) = 1) by (clear; mauto).
    rewrite H7; simpl; auto.
  }
  assert (Int.unsigned ($ Z.of_nat (S (S x))) > 1).
  {
    rewrite int_usign_eq.
    lia. lia. mauto.
  }
  destruct (Int.unsigned ($ Z.of_nat (S (S x))) =? 1) eqn: I; [lia|clear I].
  assert ((0 < S x)%nat) by lia.
  assert (0 <= y + 1) by lia.
  assert (Z.of_nat (S x) + (y + 1) = Z.of_nat (S (S x)) + y) by mauto.
  rewrite <- H10 in H1.
  specialize (IHx qstartb (y + 1) H8 H9 H1).
  rewrite IHx at 1.
  rewrite H10.
  assert (Int.mul ($ y) ($ 33) +ᵢ  $ 33 = Int.mul ($ (y + 1)) ($ 33)).
  { clear - H0 H1; mauto. f_equal; mauto. }
  rewrite H11.
  assert (($ (Z.of_nat (S (S x)) + y)) = ($ Z.of_nat (S (S x)) +ᵢ  $ y)).
  { clear - H H0 H1; mauto. }
  rewrite H12; auto.
Qed.

Lemma dmportp_sllseg_qport_msg_app : forall n m qout qin qstart qend msgl1 msgl2 qmid,
  length msgl1 = n -> length msgl2 = m ->
  qmid = (dmportp_msg_next_n n qout qstart qend) ->
  dmportp_sllseg_qport_msg qout qin qstart qend (n + m)%nat (msgl1 ++ msgl2) <==>
  dmportp_sllseg_qport_msg qout qmid qstart qend n msgl1 ** 
  dmportp_sllseg_qport_msg qmid qin qstart qend m msgl2.
Proof.
  intro n.
  induction n;intros.
  - split;intros.
    + destruct msgl1;tryfalse.
    rewrite Nat.add_0_l in *.
    simpl (nil ++ _ ) in *.
    cbn [dmportp_sllseg_qport_msg dmportp_msg_next_n] in *.
    sep pauto.
    + destruct msgl1;tryfalse.
    rewrite Nat.add_0_l in *.
    simpl (nil ++ _ ) in *.
    cbn [dmportp_sllseg_qport_msg dmportp_msg_next_n] in *.
    sep pauto.
  - split;intros.
    + destruct msgl1;tryfalse.
    assert (S n + m = S (n + m))%nat by lia.
    rewrite H3 in H2. clear H3.
    simpl ((_ :: _) ++ _ ) in *.
    cbn [dmportp_sllseg_qport_msg dmportp_msg_next_n] in *.
    sep normal in H2. sep destruct H2. sep split in H2.
    sep normal.
    exists x.
    sep autocancel.
    eapply IHn in H2;eauto.
    sep split;auto.
    + destruct msgl1;tryfalse.
    assert (S n + m = S (n + m))%nat by lia.
    rewrite H3. clear H3.
    simpl ((_ :: _) ++ _ ) in *.
    cbn [dmportp_sllseg_qport_msg dmportp_msg_next_n] in *.
    sep normal in H2. sep destruct H2. sep split in H2.
    sep normal.
    exists x.
    sep autocancel.
    eapply IHn in H2;eauto.
    sep split;auto. 
Qed.

Lemma dmportp_sllseg_qport_msg_app_frm : forall n m qout qin qstart qend msgl1 msgl2 qmid P,
  length msgl1 = n -> length msgl2 = m ->
  qmid = (dmportp_msg_next_n n qout qstart qend) ->
  dmportp_sllseg_qport_msg qout qin qstart qend (n + m)%nat (msgl1 ++ msgl2) ** P <==>
  dmportp_sllseg_qport_msg qout qmid qstart qend n msgl1 ** 
  dmportp_sllseg_qport_msg qmid qin qstart qend m msgl2 ** P.
Proof.
  intros.
  split;intros;
  sep cancel P;
  eapply dmportp_sllseg_qport_msg_app;eauto.
Qed.

Lemma dmportp_sllseg_qport_msg_length :forall n qout qin qstart qend  msgl P,
  dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P ==>
  [| length msgl = n |] ** dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P.
Proof.
  intro.
  induction n;intros.
  - cbn [dmportp_sllseg_qport_msg] in *.
    destruct msgl. sep pauto.
    apply astar_l_afalse_elim in H;tryfalse.
  - destruct msgl;
    cbn [dmportp_sllseg_qport_msg] in *.
    apply astar_l_afalse_elim in H;tryfalse.
    sep normal in H. sep destruct H. sep split in H.
    sep normal. exists x.
    sep name lift dmportp_sllseg_qport_msg in H.
    eapply IHn in H;eauto.
    sep pauto.
Qed.

Lemma dmportp_sllseg_qport_msg_R_qout_qin:
  forall n qout qin qstart qend  msgl P,
  dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P ==>
  [| qin = dmportp_msg_next_n n qout qstart qend |] **
  dmportp_sllseg_qport_msg qout qin qstart qend n msgl ** P.
Proof.
  induction n;intros.
  - cbn [dmportp_sllseg_qport_msg] in *.
    destruct msgl. sep pauto.
    apply astar_l_afalse_elim in H;tryfalse.
  - destruct msgl;
    cbn [dmportp_sllseg_qport_msg] in *.
    apply astar_l_afalse_elim in H;tryfalse.
    sep normal in H. sep destruct H. sep split in H.
    sep normal. exists x.
    sep name lift dmportp_sllseg_qport_msg in H.
    eapply IHn in H;eauto.
    sep pauto.
Qed.

Lemma dmportp_sllseg_qport_msg_Rle_z1_z2_pre:
  forall n z1 z2 sz qstartb msg P,
  z1 + (Z.of_nat n) <= Int.unsigned ($ Z.of_nat sz) ->
  0 < z1 < Int.unsigned ($ Z.of_nat sz) ->
  0 < z2 < Int.unsigned ($ Z.of_nat sz) ->
  Int.unsigned ($ Z.of_nat sz) <= 65535 ->
  dmportp_sllseg_qport_msg
  (qstartb, Int.mul ($ z1) ($ 33))
  (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
  (qstartb, Int.mul ($ Z.of_nat sz) ($ 33)) n msg ** P ==>
  [| ((qstartb, Int.mul ($ (z1 + (Z.of_nat n))) ($ 33))) =
      dmportp_msg_next_n n
        (qstartb, Int.mul ($ z1) ($ 33))
        (qstartb, Int.zero)
        (qstartb, Int.mul ($ Z.of_nat sz) ($ 33)) |] **
  dmportp_sllseg_qport_msg
  (qstartb, Int.mul ($ z1) ($ 33))
  (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
  (qstartb, Int.mul ($ Z.of_nat sz) ($ 33)) n msg ** P.
Proof.
  induction n;intros.
  - cbn [dmportp_sllseg_qport_msg] in *.
    destruct msg. sep pauto.
    {
      unfold dmportp_msg_next_n.
      rewrite Z.add_0_r.
      auto.
    }
    apply astar_l_afalse_elim in H3;tryfalse.
  - destruct msg;
    cbn [dmportp_sllseg_qport_msg] in *.
    apply astar_l_afalse_elim in H3;tryfalse.
    sep normal in H3. sep destruct H3. sep split in H3.
    sep normal. exists x.
    sep name lift dmportp_sllseg_qport_msg in H3.
    sep pauto.
    cbn [dmportp_msg_next_n].
    unfold dmportp_sllseg_qport_msg_next, msg_distance, snd in *.
    assert (Z.of_nat (typelen OSMsg_t) = 33) by (clear; simpl; lia).
    rewrite H8 in *; clear H8.
    assert (Int.mul ($ Z.of_nat sz) ($ 33) = 
    Int.mul ($ Z.of_nat sz -ᵢ $ z1) ($ 33) +ᵢ Int.mul ($ z1) ($ 33)).
    {
      rewrite <- Int.mul_add_distr_l.
      assert (($ Z.of_nat sz -ᵢ $ z1) +ᵢ  $ z1 = $ Z.of_nat sz).
      {
        rewrite Int.sub_add_opp, Int.add_assoc.
        assert (Int.neg ($ z1) +ᵢ  $ z1 = $ z1 +ᵢ Int.neg ($ z1)).
        apply Int.add_commut.
        rewrite H8, Int.add_neg_zero, Int.add_zero; auto.
      }
      rewrite H8; auto.
    }
    rewrite H8 at 1. rewrite H8 in H3 at 1.
    rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero.
    rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero in H3.
    assert ($ Z.of_nat sz -ᵢ $ z1 = $ (Int.unsigned ($ Z.of_nat sz) - z1)).
    {
      assert ($ (Int.unsigned ($ Z.of_nat sz)) = $ Z.of_nat sz) by apply Int.repr_unsigned.
      rewrite <- H9 at 1.
      rewrite Int.sub_signed.
      rewrite ! Int.signed_repr; auto.
      1,2: rewrite min_signed_val, max_signed_val; lia.
    }
    rewrite H9 in *.
    assert ((Int.divu (Int.mul ($ (Int.unsigned ($ Z.of_nat sz) - z1)) ($ 33)) ($ 33)) = ($ (Int.unsigned ($ Z.of_nat sz) - z1))).
    {
      remember (Int.unsigned ($ Z.of_nat sz) - z1) as A.
      assert (0 <= A <= 65535) by lia.
      assert (exists a, Z.of_nat a = A).
      { exists (Z.to_nat A); apply Z2Nat.id; lia. }
      destruct H11; rewrite <- H11 in *; clear H11.
      destruct H10. clear - H11. mauto.
      rewrite Z_div_mult; mauto.
    }
    rewrite H10 in *.
    rewrite int_usign_eq. rewrite int_usign_eq in H3.
    2,4: lia.
    2,3: rewrite max_unsigned_val; lia.
    clear H8 H9 H10.
    destruct (Int.unsigned ($ Z.of_nat sz) - z1 =? 1) eqn: I.
    {
      rewrite Z.eqb_eq in I.
      assert (Int.unsigned ($ Z.of_nat sz) - z1 >= Z.of_nat (S n)) by lia.
      assert (n = 0%nat) by lia; subst n.
      exfalso. cbn [dmportp_sllseg_qport_msg] in H3.
      destruct msg.
      2: apply astar_l_afalse_elim in H3; tryfalse.
      sep split in H3.
      remember (Int.mul ($ z2) ($ 33)) as A; inverts H9.
      assert (z2 <= 65535) by lia.
      clear - H1 H9 H10.
      assert (exists a, Z.of_nat a = z2).
      { exists (Z.to_nat z2); apply Z2Nat.id; lia. }
      destruct H; subst z2.
      destruct x; try lia.
      clear H1; mauto.
      assert (Int.divu Int.zero ($ 33) = Int.divu (Int.mul ($ Z.of_nat (S x)) ($ 33)) ($ 33)).
      {
        mauto.
        assert ($ (0 / 33) = Int.divu (Int.zero) ($ 33)) by (clear; mauto).
        rewrite H, H10; mauto.
      }
      rewrite int_divu_zero in H.
      assert (Int.divu (Int.mul ($ Z.of_nat (S x)) ($ 33)) ($ 33) = ($ Z.of_nat (S x))).
      { mauto; rewrite Z_div_mult; mauto. }
      rewrite H0 in H. clear H0 H10.
      assert (Int.unsigned ($ (Z.of_nat (S x))) = 0).
      { rewrite <- H; mauto. }
      rewrite int_usign_eq in H0.
      lia. lia. rewrite max_unsigned_val; lia.
    }
    assert (z1 <= 65535) by lia.
    assert (Int.mul ($ z1) ($ 33) +ᵢ  $ 33 = Int.mul ($ (z1 + 1)) ($ 33)).
    { clear - H0 H8; mauto. f_equal; mauto. }
    rewrite H9; rewrite H9 in H3.
    eapply IHn in H3.
    {
      sep split in H3. rewrite <- H10.
      assert ((z1 + Z.of_nat (S n)) = (z1 + 1 + Z.of_nat n)) by lia.
      rewrite H11; auto.
    }
    all: lia.
Qed.

Lemma dmportp_sllseg_qport_msg_Rle_z1_z2:
  forall n z1 z2 sz qstartb msg P,
  z1 + (Z.of_nat n) <= Int.unsigned ($ Z.of_nat sz) ->
  0 < z1 < Int.unsigned ($ Z.of_nat sz) ->
  0 < z2 < Int.unsigned ($ Z.of_nat sz) ->
  Int.unsigned ($ Z.of_nat sz) <= 65535 ->
  dmportp_sllseg_qport_msg
  (qstartb, Int.mul ($ z1) ($ 33))
  (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
  (qstartb, Int.mul ($ Z.of_nat sz) ($ 33)) n msg ** P ==>
  [| (z1 + (Z.of_nat n)) = z2 |] **
  dmportp_sllseg_qport_msg
  (qstartb, Int.mul ($ z1) ($ 33))
  (qstartb, Int.mul ($ z2) ($ 33)) (qstartb, Int.zero)
  (qstartb, Int.mul ($ Z.of_nat sz) ($ 33)) n msg ** P.
Proof.
  intros.
  eapply dmportp_sllseg_qport_msg_R_qout_qin in H3.
  sep split in H3.
  eapply dmportp_sllseg_qport_msg_Rle_z1_z2_pre in H3; eauto.
  sep split in H3.
  rewrite <- H5 in H4.
  sep pauto. clear H3 H5.
  remember (Int.mul ($ z2) ($ 33)) as A.
  remember (Int.mul ($ (z1 + Z.of_nat n)) ($ 33)) as B.
  inverts H4; subst B.
  assert (exists a, Z.of_nat a = z2).
  { exists (Z.to_nat z2); apply Z2Nat.id; lia. }
  assert (exists a, Z.of_nat a = z1 + Z.of_nat n).
  { exists (Z.to_nat (z1 + Z.of_nat n)); apply Z2Nat.id; lia. }
  destruct H4, H5; subst z2; rewrite <- H5 in *.
  assert (Z.of_nat x0 <= 65535) by lia.
  assert (Z.of_nat x <= 65535) by lia.
  clear - H3 H4 H8.
  assert (Int.divu (Int.mul ($ Z.of_nat x) ($ 33)) ($ 33) = Int.divu (Int.mul ($ Z.of_nat x0) ($ 33)) ($ 33)).
  { rewrite H3; auto. }
  assert (Int.divu (Int.mul ($ Z.of_nat x) ($ 33)) ($ 33) = ($ Z.of_nat x)).
  { mauto; rewrite Z_div_mult; mauto. }
  assert (Int.divu (Int.mul ($ Z.of_nat x0) ($ 33)) ($ 33) = ($ Z.of_nat x0)).
  { mauto; rewrite Z_div_mult; mauto. }
  rewrite H0, H1 in H; clear H0 H1.
  assert (x = x0); auto.
  eapply rulesoundlib.nat_repr_eq; auto.
  all: rewrite max_unsigned_val; lia.
Qed.

Lemma port_split_coreheapl:
  forall coreheapl l m,
  In_heapl_addrval coreheapl l m ->
  forall P,
  AOScoreheapl coreheapl ** P
  ==>
  EX l1 l2 n vl1 vl2,
  [| coreheapl = l1 ++ (l, n, vl1 ++ vl2) :: l2 |] **
  AOScoreheapl (l1 ++ (get_off_addr l (Int.repr (Z.of_nat m)), (n - m)%nat, vl2) :: l2) **
  Aarray l (Tarray Tint8 m) vl1 **
  [| array_type_vallist_match Tint8 vl1 /\ (n <= (Z.to_nat HEAP_MAX_LENGTH ))%nat /\ 
    (length vl1 + length vl2 = n)%nat /\ (length vl1 = m)%nat |] ** P.
Proof.
  intros.
  eapply In_heapl_addrval_split in H0; [ | apply H].
  sep destruct H0.
  sep split in H0.
  destruct H1; subst coreheapl.
  assert (In (l, x1, x2 ++ x3) (x ++ (l, x1, x2 ++ x3) :: x0)) by (apply in_elt).
  eapply AOScoreheapl_length_frm in H0;eauto.
  sep split in H0.
  eapply split_coreheapl with (m:=m) in H0; auto.
  sep split in H0.
  destruct H4. 
  rewrite <- H3 in H5.
  rewrite app_length in H3. symmetry in H3.
  sep auto.
Qed.


Lemma AOSCorePortPtrList_update_dportls_frm : forall  cportlptr cportpl dportls
  p_v pcn pd pid d pst dstpin  dstpout pm pin tm msg P,
  get dportls p_v = Some (pcn, pd, pid, d, pst, dstpin, dstpout, pm) ->
  AOSCorePortPtrList cportlptr cportpl dportls ** P  ==> 
  AOSCorePortPtrList cportlptr cportpl (set dportls p_v (pcn, pd, pid, d, pst, pin, tm, msg)) **P.
Proof.
  unfold AOSCorePortPtrList;intros.
  sep auto.
  eapply RH_CorePortPtrList_upd_dportls;eauto.
Qed.

Lemma ChannelNode_length: forall chanvl s chanl chandstkportll P,
  s |= ChannelNode chanvl chanl chandstkportll ** P ->
 length chanvl = length chandstkportll  /\ length chanvl = length chanl.
Proof.
  induction chanvl; destruct chanl; destruct chandstkportll; intros; auto.
  + simpl in H. simpljoin. now exfalso.
  + simpl in H. simpljoin. now exfalso.
  + simpl in H. simpljoin. now exfalso.
  + simpl in H. simpljoin. now exfalso.
  + simpl in H. simpljoin. now exfalso.
  + simpl in H. simpljoin. now exfalso.
  + cbn [ChannelNode] in H. sep normal in H.
    apply disj_split in H.
    destruct H.
    - sep split in H.
      lets Hx: IHchanvl H.
      simpljoin. split; simpl; congruence.
    - sep normal in H. sep destruct H.
      sep split in H.
      sep name lift ChannelNode in H.
      lets Hx: IHchanvl H.
      simpljoin. split; simpl; congruence.
Qed.

Lemma nth_error_same_length: forall {A:Type} {B:Type} n (l1: list A) (l2: list B) a,
  length l1 = length l2 ->
  nth_error l1 n = Some a ->
  exists b, nth_error l2 n = Some b.
Proof.
  induction n; destruct l1; destruct l2; intros; simpl in *; try lia.
  + inversion H0.
  + eauto.
  + discriminate.
  + inverts H. eauto.
Qed.

Lemma ChannelNode_getsome_frm':
forall (n : nat) (chanvl : list val) (chanptr : addrval)
(chanl : list vallist) 
  (chandstportll : list (list addrval)) 
  (P : asrt),
  nth_error chanvl n = Some (Vptr chanptr) ->
  ChannelNode chanvl chanl chandstportll ** P ==>
  EX (chanvl1 : list val) (chanl1 : list vallist)
  (chandstportll1 : list (list addrval)) (chanvl2 : list val)
  (chanl2 : list vallist) (chandstportll2 : list (list addrval))
  (dphead : val) (dpnum : int32) (chan : vallist) (dstportl : list addrval),
  [| nth_error chanl n = Some chan |] **
  [| nth_error chandstportll n = Some dstportl |] **
  [|chanvl = chanvl1 ++ Vptr chanptr :: chanvl2|] **
  [|chanl = chanl1 ++ chan :: chanl2|] **
  [|chandstportll = chandstportll1 ++ dstportl :: chandstportll2|] **
  ChannelNode chanvl1 chanl1 chandstportll1 **
  ChannelNode chanvl2 chanl2 chandstportll2 **
  [|length chanvl1 = n /\ length chanl1 = n /\ length chandstportll1 = n|] **
  node (Vptr chanptr) chan OS_Channel **
  [|OS_Channel_V_dstPortsHead chan = Some dphead|] **
  [|OS_Channel_V_dstPortsNum chan = Some (Vint32 dpnum)|] **
  Channel_dstkport_get dphead Vnull ∘ (Int.unsigned dpnum) dstportl ** P.
Proof.
  intros.
  lets Htmp: ChannelNode_length H0.
  simpljoin.
  pose proof (nth_error_same_length n _ _ _ H1 H).
  simpljoin.
  pose proof (nth_error_same_length n _ _ _ H2 H).
  simpljoin.
  lets Htmp: ChannelNode_getsome_frm H H4 H3 H0.
  sep destruct Htmp.
  sep split in Htmp.
  sep auto.
Qed.

Lemma ChannelNode_getsome_Vnull_frm:
  forall n chanvl chanl chandstportll P,
    nth_error chanvl n = Some Vnull ->
      ChannelNode chanvl chanl chandstportll ** P ==>
      EX chanvl1 chanl1 chandstportll1 chanvl2 chanl2 chandstportll2,
        [| chanvl = chanvl1 ++ Vnull :: chanvl2 |] **
        [| chanl = chanl1 ++ nil :: chanl2 |] **
        [| chandstportll = chandstportll1 ++ nil :: chandstportll2 |] **
        ChannelNode chanvl1 chanl1 chandstportll1 **
        ChannelNode chanvl2 chanl2 chandstportll2 **
        [| length chanvl1 = n /\ length chanl1 = n /\ length chandstportll1 = n |] **
        P.
Proof.
  intro; induction n; intros.
  {
    destruct chanvl; destruct chanl; destruct chandstportll; tryfalse.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H; inverts H.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H; inverts H.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H; inverts H.
    cbn [ChannelNode] in H0.
    sep normal in H0.
    apply disj_star_elim_disj in H0 as [? | ?].
    sep split in H; destruct H0 as [? [? ?]]; tryfalse.
    sep pauto; eauto.
    3: instantiate (1:= chandstportll); instantiate (1:= nil); auto.
    3: instantiate (1:= chanl); instantiate (1:= nil); auto.
    3: instantiate (1:= chanvl); instantiate (1:= nil); auto.
    cbn [ChannelNode]; sep pauto.
    auto.
    sep normal in H. sep destruct H.
    sep split in H.
    unfold node in H.
    sep normal in H.
    sep destruct H.
    sep split in H.
    simpljoin.
    discriminate.
  }
  {
    destruct chanvl; destruct chanl; destruct chandstportll; tryfalse.
    simpl in H.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H.
    cbn [ChannelNode] in H0.
    simpl in H0. simpljoin. now exfalso.
    cbn [ChannelNode] in H0.
    sep normal in H0.
    apply disj_star_elim_disj in H0 as [? | ?].
    {
      sep split in H0.
      simpljoin. simpl in H.
      lets Hx: IHn H H0. clear H.
      sep destruct Hx.
      exists (Vnull::x).
      exists (nil::x0).
      exists (nil::x1).
      simpl app. sep eexists.
      sep autocancel.
      cbn [ChannelNode].
      sep auto.
      apply disj_split. left.
      sep auto.
      simpljoin. simpl. splits; congruence.
    }
    {
      sep normal in H0. sep destruct H0.
      sep split in H0.
      sep name lift ChannelNode in H0.
      lets Hx: IHn H H0. clear H0.
      sep destruct Hx.
      exists (v::x1).
      exists (v0::x2).
      exists (l::x3).
      simpl app. sep eexists.
      sep autocancel.
      cbn [ChannelNode].
      sep auto.
      apply disj_split. right.
      sep auto.
      simpljoin. simpl. splits; congruence.
    }
  }
Qed.

Lemma kportNode_getsome_Vnull_frm:
  forall n kportpl kportl P,
    nth_error kportpl n = Some Vnull ->
    kportNode_P kportpl kportl ** P ==>
    EX kportpl1 kportl1 kportpl2 kportl2,
      [| kportpl = kportpl1 ++ Vnull :: kportpl2 |] **
      [| kportl = kportl1 ++ nil :: kportl2 |] **
      kportNode_P kportpl1 kportl1 **
      kportNode_P kportpl2 kportl2 **
      [| length kportpl1 = n /\ length kportl1 = n |] **
      P.
Proof.
  intro; induction n; intros.
  {
    destruct kportpl; destruct kportl; tryfalse.
    cbn [kportNode_P] in H0.
    simpl in H0. simpljoin. now exfalso.
    simpl in H; inverts H.
    cbn [kportNode_P] in H0.
    sep normal in H0.
    apply disj_star_elim_disj in H0 as [? | ?].
    sep split in H; destruct H0 as [? ?]; tryfalse.
    sep pauto; eauto.
    3: instantiate (1:= kportl); instantiate (1:= nil); auto.
    3: instantiate (1:= kportpl); instantiate (1:= nil); auto.
    cbn [kportNode_P]; sep pauto.
    auto.
    sep normal in H. sep destruct H.
    sep split in H.
    destruct H0. inverts H0.
  }
  {
    destruct kportpl; destruct kportl; tryfalse.
    simpl in H.
    cbn [kportNode_P] in H0.
    simpl in H0. simpljoin. now exfalso.
    cbn [kportNode_P] in H0.
    sep normal in H0.
    apply disj_star_elim_disj in H0 as [? | ?].
    {
      sep split in H0.
      simpljoin. simpl in H.
      lets Hx: IHn H H0. clear H.
      sep destruct Hx.
      exists (Vnull::x).
      exists (nil::x0).
      (* exists (nil::x1). *)
      simpl app. sep eexists.
      sep autocancel.
      cbn [kportNode_P].
      sep auto.
      apply disj_split. left.
      sep auto.
      simpljoin. simpl. splits; congruence.
    }
    {
      sep normal in H0. sep destruct H0.
      sep split in H0.
      sep name lift kportNode_P in H0.
      lets Hx: IHn H H0. clear H0.
      sep destruct Hx.
      exists (v::x0).
      exists (v0::x1).
      (* exists (l::x3). *)
      simpl app. sep eexists.
      sep autocancel.
      cbn [kportNode_P].
      sep auto.
      apply disj_split. right.
      sep auto.
      simpljoin. simpl. splits; congruence.
    }
  }
Qed.

Lemma kport_V_OSEventPtr_add_dportl:
  forall kportvl2 kportl2 dportl dpptrl dmport dmportp,
    kport_V_OSEventPtr kportvl2 kportl2 dportl dpptrl ==>
    kport_V_OSEventPtr kportvl2 kportl2 (dmport :: dportl) (dmportp :: dpptrl).
Proof.
  induction kportvl2; destruct kportl2; cbn [kport_V_OSEventPtr];
  intros; eauto.
  destruct a; eauto.
  apply disj_split in H. destruct H.
  { apply disj_split. left.
    sep normal in H. sep destruct H.
    sep normal. exists (S x) x0 x1.
    sep pauto. eauto. eauto. }
  { apply disj_split. right.
    sep normal in H. sep normal. sep pauto. }
Qed.

Lemma kport_V_OSEventPtr_add_dportl_frm:
  forall kportvl2 kportl2 dportl dpptrl dmport dmportp P,
    kport_V_OSEventPtr kportvl2 kportl2 dportl dpptrl ** P ==>
    kport_V_OSEventPtr kportvl2 kportl2 (dmport :: dportl) (dmportp :: dpptrl) ** P.
Proof.
  induction kportvl2; destruct kportl2; cbn [kport_V_OSEventPtr];
  intros; eauto.
  destruct a; eauto. sep normal. sep normal in H.
  apply disj_split in H. destruct H.
  { apply disj_split. left.
    sep normal in H. sep destruct H.
    sep normal. exists (S x) x0 x1.
    sep pauto. apply kport_V_OSEventPtr_add_dportl.
    eauto. eauto. }
  { apply disj_split. right.
    sep normal in H. sep normal. sep pauto.
    apply kport_V_OSEventPtr_add_dportl. eauto. }
Qed.

Lemma kport_V_OSEventPtr_sig_add_dportl:
  forall kportv kport dportl dpptrl dmport dmportp,
    kport_V_OSEventPtr_sig kportv kport dportl dpptrl  ==>
    kport_V_OSEventPtr_sig kportv kport (dmport :: dportl) (dmportp :: dpptrl).
Proof.
  intros. unfold kport_V_OSEventPtr_sig in *.
  destruct kportv; eauto.
  sep normal in H. sep normal.
  destruct H; [left|right]; eauto.
  sep split in H. sep destruct H.
  sep split; eauto. exists (S x) x0 x1.
  sep split in H. sep split; eauto.
Qed.

Lemma kport_V_OSEventPtr_sig_add_dportl_frm:
  forall kportv kport dportl dpptrl dmport dmportp P,
    kport_V_OSEventPtr_sig kportv kport dportl dpptrl ** P  ==>
    kport_V_OSEventPtr_sig kportv kport (dmport :: dportl) (dmportp :: dpptrl) ** P.
Proof.
  intros.
  eapply astar_mono.
  eapply kport_V_OSEventPtr_sig_add_dportl.
  eauto. eauto.
Qed.

Lemma kport_V_OSEventPtr_upd:
  forall kportvl1 kportv kportvl2 kportl1 kport_ kportl2 dportl dpptrl kportp kport dmport dmportp,
    length kportvl1 = length kportl1 ->
    OS_K_Port_V_channel kport = Some Vnull ->
    kport_V_OSEventPtr (kportvl1 ++ kportv :: kportvl2)
    (kportl1 ++ kport_ :: kportl2) dportl dpptrl **
    PV get_off_addr kportp ($ 12) @ (Void) ∗ |-> Vnull ==>
    kport_V_OSEventPtr (kportvl1 ++ (Vptr kportp) :: kportvl2)
    (kportl1 ++ kport :: kportl2) (dmport :: dportl) (dmportp :: dpptrl) **
    kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl.
Proof.
  induction kportvl1; destruct kportl1; cbn [length];
  intros; tryfalse.
  { repeat rewrite app_nil_l in *.
    cbn [kport_V_OSEventPtr] in *.
    sep normal. eapply disj_split. right.
    sep normal. sep autocancel.
    destruct kportv.
    1,2,3: exfalso; eapply sep_exist_Afalse; eauto.
    sep pauto. apply kport_V_OSEventPtr_add_dportl_frm.
    sep autocancel.
    unfold kport_V_OSEventPtr_sig. sep pauto. }
  simpl ((_ :: _) ++ _) in *.
  cbn [kport_V_OSEventPtr] in *. destruct a.
  1,2,3: exfalso; eapply sep_exist_Afalse;
          eapply astar_l_afalse_elim; eauto.
  sep normal. sep normal in H1.
  eapply astar_mono.
  eauto. eapply IHkportvl1. eauto. eauto.
  sep autocancel.
  destruct H1; [left|right]; sep pauto.
  eauto. instantiate (1:= (S x)). eauto.
Qed.

Lemma kport_V_OSEventPtr_upd_frm:
  forall kportvl1 kportv kportvl2 kportl1 kport_ kportl2 dportl dpptrl kportp kport dmport dmportp P,
    length kportvl1 = length kportl1 ->
    OS_K_Port_V_channel kport = Some Vnull ->
    kport_V_OSEventPtr (kportvl1 ++ kportv :: kportvl2)
    (kportl1 ++ kport_ :: kportl2) dportl dpptrl **
    PV get_off_addr kportp ($ 12) @ (Void) ∗ |-> Vnull ** P ==>
    kport_V_OSEventPtr (kportvl1 ++ (Vptr kportp) :: kportvl2)
    (kportl1 ++ kport :: kportl2) (dmport :: dportl) (dmportp :: dpptrl) **
    kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl ** P.
Proof.
  intros.
  sep lift 3%nat.
  eapply astar_mono.
  eauto.
  eapply kport_V_OSEventPtr_upd.
  eauto. eauto. sep pauto.
Qed.

Lemma kportNode_P_len_eq:
  forall kportvl kportl,
    kportNode_P kportvl kportl ==>
    [| length kportvl = length kportl |] **
    kportNode_P kportvl kportl.
Proof.
  induction kportvl; destruct kportl;
  cbn [kportNode_P]; sep pauto.
  { exfalso. eapply sep_exist_Afalse. eauto. }
  { exfalso. eapply sep_exist_Afalse. eauto. }
  eapply astar_mono in H.
  2: eauto.
  2: eapply IHkportvl.
  sep split in H. simpl. lia.
Qed.

Lemma kportNode_P_len_eq_frm:
  forall kportvl kportl P,
    kportNode_P kportvl kportl ** P ==>
    [| length kportvl = length kportl |] **
    kportNode_P kportvl kportl ** P.
Proof.
  intros.
  eapply astar_mono in H.
  2: eapply kportNode_P_len_eq.
  2: eauto.
  sep pauto.
Qed.