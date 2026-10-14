Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.
Require Import gjb_common.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_symrules.


Lemma can_change_aop_kport_V_OSEventPtr: forall kportvl kportl dportl dpptrl,
  can_change_aop (kport_V_OSEventPtr kportvl kportl dportl dpptrl).
Proof.
  induction kportvl; intros;destruct kportl; cbn[kport_V_OSEventPtr]; can_change_aop_solver.
  destruct a;can_change_aop_solver.
  destruct a;can_change_aop_solver.
  split;can_change_aop_solver.
  split;can_change_aop_solver. Qed.
Hint Resolve can_change_aop_kport_V_OSEventPtr: can_change_aop.

Lemma good_frm_kport_V_OSEventPtr: forall kportvl kportl dportl dpptrl,
 GoodFrm (kport_V_OSEventPtr kportvl kportl dportl dpptrl).
Proof.
  induction kportvl; intros;destruct kportl; cbn[kport_V_OSEventPtr]; good_frm_sovler.
  destruct a;good_frm_sovler.
  destruct a;good_frm_sovler.
  split;good_frm_sovler.
  split;good_frm_sovler. Qed.
Hint Resolve good_frm_kport_V_OSEventPtr: good_frm_lemmas.

Lemma R_Kernelport_DomainPort_init_nth_getsome:
  forall kportvl kportl dportl1 dport dportl2 dpptrl pptr,
    R_Kernelport_DomainPort_init kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl ->
    nth_error dpptrl (length dportl1) = Some pptr ->
    ((exists id kportptr kport,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vptr kportptr) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some kport /\
        struct_type_vallist_match OS_K_Port kport /\
        OS_K_Port_V_portID kport = Some (Vint32 id) /\
        OS_K_Port_V_dmport kport = Some (Vptr pptr) /\
        OS_K_Port_V_coreNum kport = OS_Port_V_coreNum dport) \/ 
        (exists id,
        OS_Port_V_portID dport = Some (Vint32 id) /\
        nth_error kportvl (nat_of_Z (Int.unsigned id)) = Some (Vnull) /\ 
        nth_error kportl (nat_of_Z (Int.unsigned id)) = Some nil)).
Proof.
  intros ? ? ?; revert kportvl kportl; induction dportl1; intros.
  {
    destruct dpptrl; tryfalse.
    simpl in H0. inverts H0.
    simpl in H; simpljoin1; simpl.
    auto.
  }
  destruct dpptrl; tryfalse.
  cbn in H; simpljoin1.
  eapply IHdportl1; eauto.
Qed.

Lemma channel_V_dstPortsTail_app: forall chanl1 chanl2 dstkportl1 dstkportl2, 
  length chanl1 = length dstkportl1 ->
  channel_V_dstPortsTail (chanl1 ++ chanl2) (dstkportl1 ++ dstkportl2) <->
  channel_V_dstPortsTail chanl1 dstkportl1 /\ channel_V_dstPortsTail chanl2 dstkportl2.
Proof.
  induction chanl1;intros.
  - destruct dstkportl1;tryfalse.
    cbn; split;tauto.
  - destruct dstkportl1;tryfalse.
    simpl in H.
    cbn;split;intros.
    + destruct H0.
      eapply IHchanl1 in H1;[ |  lia]. splits;tauto.
    + destruct H0 as [[? ?] ?].
      split;auto.
      eapply IHchanl1;eauto.
Qed.

Lemma Channel_dstkport_get_length: forall n p tail l P,
  Channel_dstkport_get p tail n l ** P ==>
  [| length l = n |] ** Channel_dstkport_get p tail n l ** P.
Proof.
  induction n;intros.
  - destruct l;cbn [Channel_dstkport_get] in *.
    sep auto.  apply astar_l_afalse_elim in H. tryfalse.
  - destruct l;cbn [Channel_dstkport_get] in *.
    apply astar_l_afalse_elim in H. tryfalse.

    sep normal in H. sep destruct H. sep split in H. 
    sep lift 2%nat in H.
    eapply IHn in H.
    sep auto.
    1,2: eauto.
Qed.


Lemma Channel_dstkport_get_headVnull: forall n  tail l P,
  Channel_dstkport_get Vnull tail n l ** P ==>
  [| tail = Vnull |] ** Channel_dstkport_get Vnull tail n l ** P.
Proof.
  induction n;intros.
  - destruct l;cbn [Channel_dstkport_get] in *.
    sep auto.  apply astar_l_afalse_elim in H. tryfalse.
  - destruct l;cbn [Channel_dstkport_get] in *.
    apply astar_l_afalse_elim in H. tryfalse.

    sep normal in H. sep destruct H. sep split in H.
    inversion H2. 
Qed.

Lemma port_mode_rv_ntherror : forall s n pptr dport msgl dportlptr dportl dportmsgll dpptrl v P,
  nth_error dportl n = Some dport ->
  nth_error dportmsgll n = Some msgl ->
  nth_error dpptrl n = Some pptr -> 
  RL_PortPtrList dportlptr dportl dpptrl ->
  OS_Port_V_mode dport = Some v ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **  P ->
  s |= Rv port_ptr ′ → mode @ long == v.
Proof.
  intros.
  apply nth_error_split in H as (dportl1 & dportl2 & ? & ? ).
  apply nth_error_split in H0 as (dportmsgll1 & dportmsgll2 & ? & ? ).
  subst.
  sep name lift dmportp_sllseg in H4.
  eapply dmportp_sllseg_app'_frm in H4;eauto.
  cbn [dmportp_sllseg ] in H4.
  sep normal in H4.
  sep destruct  H4.
  sep split in H4.
  inverts H. 
  sep name lift (Alvarmapsto port_ptr) in H4.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H4.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  
  do 5 (destruct dport;destruct H5 as [? H5];tryfalse).
  simpl;lia.
  unfold OS_Port_V_mode in *.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_OSQEntries_rv_ntherror : forall s n pptr dport msgl dportlptr dportl dportmsgll dpptrl v P,
  nth_error dportl n = Some dport ->
  nth_error dportmsgll n = Some msgl ->
  nth_error dpptrl n = Some pptr -> 
  RL_PortPtrList dportlptr dportl dpptrl ->
  OS_Port_V_OSQEntries dport = Some v ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **  P ->
  s |= Rv port_ptr ′ → OSQEntries @ Int16u == v.
Proof.
  intros.
  apply nth_error_split in H as (dportl1 & dportl2 & ? & ? ).
  apply nth_error_split in H0 as (dportmsgll1 & dportmsgll2 & ? & ? ).
  subst.
  sep name lift dmportp_sllseg in H4.
  eapply dmportp_sllseg_app'_frm in H4;eauto.
  cbn [dmportp_sllseg ] in H4.
  sep normal in H4.
  sep destruct  H4.
  sep split in H4.
  inverts H. 
  sep name lift (Alvarmapsto port_ptr) in H4.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H4.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  
  do 17 (destruct dport;destruct H5 as [? H5];tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.

Lemma port_OSQSize_rv_ntherror : forall s n pptr dport msgl dportlptr dportl dportmsgll dpptrl v P,
  nth_error dportl n = Some dport ->
  nth_error dportmsgll n = Some msgl ->
  nth_error dpptrl n = Some pptr -> 
  RL_PortPtrList dportlptr dportl dpptrl ->
  OS_Port_V_OSQSize dport = Some v ->
  s  |= LV port_ptr @ OS_Port ∗ |-> Vptr pptr **
        dmportp_sllseg dportlptr Vnull dportl dportmsgll OS_Port_V_nextPort **  P ->
  s |= Rv port_ptr ′ → OSQSize @ Int16u == v.
Proof.
  intros.
  apply nth_error_split in H as (dportl1 & dportl2 & ? & ? ).
  apply nth_error_split in H0 as (dportmsgll1 & dportmsgll2 & ? & ? ).
  subst.
  sep name lift dmportp_sllseg in H4.
  eapply dmportp_sllseg_app'_frm in H4;eauto.
  cbn [dmportp_sllseg ] in H4.
  sep normal in H4.
  sep destruct  H4.
  sep split in H4.
  inverts H. 
  sep name lift (Alvarmapsto port_ptr) in H4.
  unfold  APortStruct in *.
  unfold OS_Port_Seg_dls in H4.
  eapply struct_member_rv_typeneq_addrneq with (m := 8%nat);eauto.
  unfold OS_Port. go.
  cbn. go.
  cbn. lia.
  clear. mauto.
  cbn. auto.
  cbn. eauto.
  destruct dport;tryfalse.  
  do 17 (destruct dport;destruct H5 as [? H5];tryfalse).
  simpl;lia.
  eapply nth_val_nth_val'_some_eq;eauto.
Qed.


Lemma channel_V_srcdstkport_src_node: forall n chanptr chanvl chann srckp chanl chandstkportll kportvl kportl dportl dpptrl,
  nth_error chanvl n =Some (Vptr chanptr) ->
  nth_error chanl n = Some chann ->
  OS_Channel_V_srcPort chann = Some (Vptr srckp) ->
  channel_V_srcdstkport chanvl chanl chandstkportll kportvl kportl dportl dpptrl ->
  (exists n kport, nth_error kportvl n = Some (Vptr srckp)  /\  nth_error kportl n = Some kport  /\ 
    OS_K_Port_V_channel kport = Some (Vptr chanptr) /\
   exists pid dmptr dmport, OS_K_Port_V_dmport kport = Some (Vptr dmptr) /\ 
                            nth_error dpptrl pid = Some dmptr /\ nth_error dportl pid = Some dmport /\ 
                            OS_Port_V_direction dmport = Some (Vint32 (Int.repr SOURCE))).
Proof.
  induction n;intros.
  - destruct chanvl, chanl;simpl in H, H0;try  discriminate.
    inversion H. subst. inversion H0. subst.
    destruct chandstkportll; cbn in H1; try contradiction.
    destruct H2 as [? _]. 
    destruct H2. simpljoin1. tryfalse.
    destruct H2 as [? [? [? _]]]. 
    inversion H2;subst x.
    apply H3;eauto.
  - destruct chanvl, chanl;simpl in H, H0;try  discriminate.
    destruct chandstkportll; cbn in H1. contradiction.
    destruct H2 as [_ ?].
    eapply IHn; eauto.
Qed.

Lemma dmportp_sllseg_length_frm: forall  l head tail msglist next P,
dmportp_sllseg head tail l msglist next ** P ==>
[| length l = length msglist|] ** dmportp_sllseg head tail l msglist next ** P.
Proof.
  induction l;intros.
  - destruct msglist;cbn [dmportp_sllseg] in *. sep pauto.
    apply astar_l_afalse_elim in H.
    tryfalse.
  - destruct msglist;cbn [dmportp_sllseg] in *.
    apply astar_l_afalse_elim in H.
    tryfalse.
    sep normal in H.
    sep destruct H.
    sep name lift dmportp_sllseg in H.
    apply IHl in H.
    sep normal.
    sep eexists.
    sep autocancel.
    sep pauto.
    simpl. lia.
Qed.

Fixpoint RL_PortPtrList_tail (headptr tailptr: val) (dportl: list vallist)  (dpptrl: list addrval)  : Prop :=
  match dportl, dpptrl with 
  | nil, nil => headptr = tailptr 
  | dport :: dportl',  pptr:: dpptrl' => headptr = Vptr pptr /\ 
                                         exists hd',  OS_Port_V_nextPort dport = Some hd' /\
                                                      RL_PortPtrList_tail hd' tailptr dportl' dpptrl' 
  | _, _ => False
end.

Lemma RL_PortPtrList_app: forall dportl1 dport dportl2 dpptrl  dportlptr dportlptr',
RL_PortPtrList dportlptr (dportl1 ++ dport :: dportl2) dpptrl ->
nth_error dpptrl (length dportl1) = Some  dportlptr' ->
exists  dpptrl1 dpptrl2,  dpptrl  = dpptrl1  ++ (dportlptr' :: dpptrl2) /\ length dpptrl1 = (length dportl1) /\
  RL_PortPtrList_tail dportlptr (Vptr dportlptr') dportl1 dpptrl1  /\
  RL_PortPtrList (Vptr dportlptr')  (dport :: dportl2) (dportlptr' :: dpptrl2).
Proof.
  induction dportl1;intros.
  - cbn in *.
    destruct dpptrl;tryfalse.
    simpljoin1.
    inverts H0.
    exists (@nil addrval) dpptrl.
    splits;cbn;auto.
    eexists.
    split;eauto.
  -  cbn in *.
     destruct dpptrl;tryfalse.
     simpljoin1.
     eapply IHdportl1 in H2;eauto.
     simpljoin1.
     exists (a0 :: x0) x1.
     splits;eauto.
     simpl. lia.
Qed.

Lemma dmportp_sllseg_app_tail : forall n dportlptr tail dportl1 dportl2 dportmsgll1 dportmsgll2 dpptrl p_v,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    nth_error dpptrl n = Some p_v -> 
    RL_PortPtrList_tail dportlptr tail (dportl1 ++ dportl2) dpptrl ->
    dmportp_sllseg dportlptr tail (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort  <==>
        dmportp_sllseg dportlptr (Vptr p_v) dportl1 dportmsgll1 OS_Port_V_nextPort **
        dmportp_sllseg (Vptr p_v) tail dportl2 dportmsgll2 OS_Port_V_nextPort.
Proof.
  intros ?.
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


Lemma dmportp_sllseg_app_tail_frm : forall n dportlptr tail dportl1 dportl2 dportmsgll1 dportmsgll2 dpptrl p_v P,
    length dportl1 = n ->
    length dportmsgll1 = n ->
    nth_error dpptrl n = Some p_v -> 
    RL_PortPtrList_tail dportlptr tail (dportl1 ++ dportl2) dpptrl ->
    dmportp_sllseg dportlptr tail (dportl1 ++ dportl2) 
                        (dportmsgll1 ++ dportmsgll2) OS_Port_V_nextPort ** P <==>
    dmportp_sllseg dportlptr (Vptr p_v)  dportl1 dportmsgll1 OS_Port_V_nextPort **
    dmportp_sllseg (Vptr p_v) tail dportl2 dportmsgll2 OS_Port_V_nextPort** P.
Proof.
  intros.
  split;intros.
  sep cancel P.
  eapply dmportp_sllseg_app_tail;eauto.
  sep cancel P.
  eapply dmportp_sllseg_app_tail;eauto.
Qed.

Lemma port_memeber_asgn_lv  : forall x
r ri aop (p p':asrt ) (tid: tid) pptr dport e tp2 v' v n t' id ,
p <==> LV x @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr dport ** p' ->
p ==>  Rv e @ tp2 == v ->
nth_id n OS_Port_Seg_dls = Some id ->
nth_val n dport = Some v' -> 
ftype id OS_Port_Seg_dls = Some t' ->
(forall (ids : ident) (dl : decllist), t' <> STRUCT ids ­{ dl }­) ->
(forall (t'0 : type) (n0 : nat), t' <> Tarray t'0 n0) ->
(forall (ids : ident) (dl : decllist), t' <> UNION ids ­{ dl }­) ->
assign_type_match t' tp2 ->
rule_type_val_match t' v = true ->
LV x @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' ==>
       EX lg : list logicvar, p_local OSLInv tid lg ** Atrue ->
{| OS_spec, GetHPrio, OSLInv, I, r, ri |} |-tid
{{  <|| aop ||>  ** p }} 
  x ′ → id =ₑ e
{{  <|| aop ||> ** LV x @ OS_Port ∗ |-> Vptr pptr ** APortStruct pptr (update_nth_val n dport v) ** p' }}.
Proof.
  intros * H H0 H1 H2 H3 H4 H5 H5'. intros.
  unfold APortStruct in *.
  lets Hoff: symbolic_lemmas.nth_id_exists_off H1.
  destruct Hoff as (off&Hoff).
  destruct pptr as (b&i).
  assert (p <==> PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v' **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV x @ OS_Port ∗ |-> Vptr (b, i) ** p').
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
  apply H9. instantiate (1:=LV x @ OS_Port ∗ |-> Vptr (b, i) ** p'). sep auto.
  sep auto. }
  clear H.
  assert (PV (b, (i +ᵢ  $ 29) +ᵢ  off) @ t' |-> v **
  Astruct_rm (b, i +ᵢ  $ 29) OS_Port_Seg_dls dport id **
  LV x @ OS_Port ∗ |-> Vptr (b, i) ** p' ==> EX lg : list logicvar, p_local OSLInv tid lg ** Atrue).
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

Lemma  kport_V_OSEventPtr_app: forall kportvl1 kportvl2 kportl1 kportl2 dportl dpptrl,
  length kportvl1 = length kportl1 ->
  kport_V_OSEventPtr (kportvl1 ++ kportvl2) (kportl1 ++ kportl2) dportl dpptrl <==>
  kport_V_OSEventPtr kportvl1 kportl1 dportl dpptrl **
  kport_V_OSEventPtr kportvl2 kportl2 dportl dpptrl.
Proof.
  induction kportvl1;intros.
  destruct kportl1;simpl in H;tryfalse.
  - cbn [ kport_V_OSEventPtr]. split; sep auto.
  - destruct kportl1;simpl in H;tryfalse.
    simpl ((_ :: _) ++ _).
    cbn [ kport_V_OSEventPtr]. split; intros.
    + destruct a;tryfalse.
      sep autocancel.
      apply IHkportvl1;auto.
    + destruct a.
      1,2,3: apply astar_l_afalse_elim in H0;tryfalse.
      sep autocancel.
      apply IHkportvl1;auto.  
Qed.


Lemma  kport_V_OSEventPtr_app_frm: forall kportvl1 kportvl2 kportl1 kportl2 dportl dpptrl P,
  length kportvl1 = length kportl1 ->
  kport_V_OSEventPtr (kportvl1 ++ kportvl2) (kportl1 ++ kportl2) dportl dpptrl ** P <==>
  kport_V_OSEventPtr kportvl1 kportl1 dportl dpptrl **
  kport_V_OSEventPtr kportvl2 kportl2 dportl dpptrl ** P.
Proof.
  intros;split;intros;
  sep cancel P;
  apply  kport_V_OSEventPtr_app;auto.
Qed.


Lemma nth_error_middle_neq {A: Type}:
  forall l1 l2 (a a': A) n,
    n <> (length l1) ->
    nth_error (l1 ++ a :: l2) n = nth_error (l1 ++ a' :: l2) n.
Proof.
  intros.
  assert (n < length l1 \/ (n > (length l1)))%nat as [ | ] by lia.
  - do 2 rewrite nth_error_app1 by lia. auto.
  - assert (n - (length l1) =  S (n - (length l1) - 1))%nat by lia.
     do 2 rewrite nth_error_app2 by lia.
     rewrite H1. 
     cbn. auto.
Qed.


Lemma  kport_V_OSEventPtr_update_dport: forall kportvl kportl dportl1 dport dport' dportl2   dpptrl,
  OS_Port_V_direction dport = OS_Port_V_direction dport' ->
  kport_V_OSEventPtr kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl ==>
  kport_V_OSEventPtr kportvl kportl (dportl1 ++ dport' :: dportl2) dpptrl.
Proof.
  induction kportvl;intros;
  destruct kportl;cbn [kport_V_OSEventPtr] in *;tryfalse;auto.
  destruct a;tryfalse.
  eapply astar_mono.
  3: exact H0.
  2: apply IHkportvl;auto.
  clear  s H0.
  intros s Hs.
  destruct Hs as [Hs | Hs].
  - left.
    sep normal in Hs. sep destruct Hs.
    sep split in Hs.
    simpljoin1.
    assert (x = length dportl1 \/ x <> length dportl1) as [ | ] by lia.
    + subst x. rewrite nth_error_middle in H3. inversion H3;subst x1. clear H3.
      sep normal. exists (length dportl1) x0 dport'.
      rewrite H in Hs.
      sep split;eauto.
      splits;eauto.
      rewrite nth_error_middle;auto.
    + erewrite nth_error_middle_neq with (a':= dport') in H3 by lia.
      sep normal. sep eexists.
      sep split;eauto. 
  - right.
    sep auto.
Qed.

Lemma update_nth_vallist_middle: forall n vl1 vl vl2 vl', 
  length vl1 = n ->
  update_nth_vallist n (vl1 ++ vl :: vl2) vl'  = (vl1 ++ vl' :: vl2).
Proof.
  induction n; intros;destruct vl1;tryfalse.
  - cbn. auto.
  - cbn. erewrite IHn. auto.
    simpl in H. lia.
Qed.

Lemma R_Kernelport_DomainPort_init_upd_kport:
forall dportl dpptrl kportl1 kport kport' kportl2 kportvl ,
R_Kernelport_DomainPort_init  kportvl (kportl1 ++ kport :: kportl2) dportl dpptrl ->
struct_type_vallist_match OS_K_Port kport' ->
OS_K_Port_V_portID kport = OS_K_Port_V_portID kport' ->
OS_K_Port_V_dmport kport = OS_K_Port_V_dmport kport' ->
OS_K_Port_V_coreNum kport = OS_K_Port_V_coreNum kport' -> 
R_Kernelport_DomainPort_init  kportvl (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof. 
  induction dportl; destruct dpptrl; simpl; intros; tryfalse; simpljoin1.
  split;eauto.
  destruct H.
  - simpljoin1.
    left.
    exists x x0.
    assert (∘ (Int.unsigned x) = length (kportl1) \/ ∘ (Int.unsigned x) <> length (kportl1)) as [ | ] by lia.
    + rewrite H11 in H6.
      rewrite nth_error_middle in H6.
      inverts H6.
      exists kport'.
      splits;eauto.
      rewrite  H11. rewrite nth_error_middle. auto.
      1,2,3: congruence.
    + exists x1. 
      splits;eauto.
      assert (∘ (Int.unsigned x) < length (kportl1) \/ ∘ (Int.unsigned x) >= S (length (kportl1)))%nat as [ | ] by lia.
      rewrite nth_error_app1 in * by lia. auto.
      rewrite nth_error_app2 in * by lia.
      assert ((∘ (Int.unsigned x) - length kportl1) = S (∘ (Int.unsigned x) - S (length kportl1)))%nat by lia.
      rewrite H13 in *.
      cbn [nth_error] in *.
      auto.
  - simpljoin1.
    right.
    eexists.
    splits;eauto.
    assert (∘ (Int.unsigned x) = length (kportl1) \/ ∘ (Int.unsigned x) <> length (kportl1)) as [ | ] by lia.
    * rewrite H7 in H6.
      rewrite nth_error_middle in H6. inverts H6.
      destruct kport' as [ | ? kport'].
      simpl in H0;tryfalse.
      cbn in H1. inversion H1.
    * assert (∘ (Int.unsigned x) < length (kportl1) \/ ∘ (Int.unsigned x) >= S (length (kportl1)))%nat as [ | ] by lia.
      rewrite nth_error_app1 in * by lia. auto.
      rewrite nth_error_app2 in * by lia.
      assert ((∘ (Int.unsigned x) - length kportl1) = S (∘ (Int.unsigned x) - S (length kportl1)))%nat by lia.
      rewrite H9 in *.
      cbn [nth_error] in *.
      auto.
Qed.


Lemma R_Kernelport_DomainPort_init_app:
  forall (dportl1 : list vallist)  (dportl2 : list vallist) (dpptrl1 : list addrval)  (dpptrl2 : list addrval) 
    (kportpl : vallist) (kportl : list vallist),
    length dportl1 = length dpptrl1 ->
  R_Kernelport_DomainPort_init kportpl kportl (dportl1 ++ dportl2)
    (dpptrl1 ++  dpptrl2) <->
  R_Kernelport_DomainPort_init kportpl kportl dportl1 dpptrl1 /\
  R_Kernelport_DomainPort_init kportpl kportl dportl2 dpptrl2.
Proof.
  induction dportl1;intros;destruct dpptrl1;simpl in H;tryfalse; simpl (nil ++ _); simpl ((_ :: _) ++ _ );cbn [R_Kernelport_DomainPort_init].
  tauto.
  split;intros.
  - simpljoin1.
    apply IHdportl1 in H1;[ | lia].
    splits; try tauto.
  - simpljoin1.
    split;auto.
    apply IHdportl1;auto.
Qed.  


Lemma R_Kernelport_DomainPort_init_upd_headport:
  forall (dportl : list vallist)  (dpptrl : list addrval)  dport dport' dpptr
    (kportpl : vallist) (kportl : list vallist),
    OS_Port_V_portID dport  = OS_Port_V_portID dport' ->
    OS_Port_V_coreNum dport  = OS_Port_V_coreNum dport' ->
  R_Kernelport_DomainPort_init kportpl kportl (dport:: dportl)
    (dpptr :: dpptrl) ->
    R_Kernelport_DomainPort_init kportpl kportl (dport':: dportl)
    (dpptr :: dpptrl).
Proof.
  intros.
  cbn in *.
  simpljoin1.
  split;auto.
  destruct H1.
  - simpljoin1.
    left.
    do 3 eexists.
    splits;eauto.
    congruence.
    congruence.
  - simpljoin1.
    right.
    eexists.
    splits;eauto.
    congruence.
Qed.  


Lemma array_type_vallist_match_skipn: forall n vl t, 
array_type_vallist_match t vl ->
array_type_vallist_match t (skipn n vl).
Proof.
  induction n;intros;cbn;auto.
  destruct vl;auto.
  destruct H.
  apply IHn;auto.
Qed.

Lemma Qport_msg_ptrs_P_qin_next: forall qstart qend qout qin qsize,
  Int.unsigned qsize <= 65535 ->
  Qport_msg_ptrs_P qstart qend qout qin (Int.unsigned qsize) ->
  Qport_msg_ptrs_P qstart qend qout (dmportp_sllseg_qport_msg_next qin qstart qend) (Int.unsigned qsize).
Proof.
  intros * Hle. intros.
  unfold Qport_msg_ptrs_P in *.
  destruct qstart as [qstartb qstarti].
  simpljoin1.
  splits;auto.
  unfold dmportp_sllseg_qport_msg_next, get_off_addr. 
  cbn [fst snd].
  assert (($ Z.of_nat (typelen OSMsg_t)) = $ 33) by (clear;mauto).
  rewrite H.
  rewrite !Int.add_zero_l.
  destruct (msg_distance (qstartb, Int.mul ($ x0) ($ 33))
  (qstartb, Int.mul ($ Int.unsigned qsize) ($ 33)) =? 1) eqn:?.
  - exists x 0.
    rewrite !Int.add_zero_l.
    splits;eauto.
    lia. lia.
  -  exists x (x0 + 1). 
    rewrite !Int.add_zero_l.
    splits;eauto.
    2: lia.
    rewrite Int_add_one_Sn'' by lia.
    rewrite Int.mul_add_distr_l. 
    assert (Int.mul Int.one ($ 33) = $ 33) by (clear;mauto).
    rewrite H0.
    auto.
    assert (x0 + 1 = Int.unsigned qsize \/ x0 + 1 < Int.unsigned qsize) as [ | ] by lia;auto.
    exfalso.
    rewrite <- H0 in *.
    unfold msg_distance in *.
    cbn [snd] in Heqb.
    rewrite H in Heqb.
    rewrite Int_add_one_Sn'' in Heqb by lia.
    rewrite Int.mul_add_distr_l in Heqb. 
    assert (Int.mul Int.one ($ 33) = $ 33) by (clear;mauto).
    rewrite H1 in Heqb.
    clear - Heqb.
    rewrite Int.sub_add_l in Heqb.
    rewrite Int.sub_idem in Heqb.
    rewrite Int.add_zero_l in Heqb.
    assert ((Int.divu ($ 33) ($ 33))  = $ 1) by mauto.
    rewrite H in Heqb.
    rewrite Int.unsigned_repr in Heqb by (clear;mauto).
    false.
Qed.



Lemma Qport_msg_ptrs_P_qout_next: forall qstart qend qout qin qsize,
  Int.unsigned qsize <= 65535 ->
  Qport_msg_ptrs_P qstart qend qout qin (Int.unsigned qsize) ->
  Qport_msg_ptrs_P qstart qend (dmportp_sllseg_qport_msg_next qout qstart qend) qin (Int.unsigned qsize).
Proof.
  intros * Hle. intros.
  unfold Qport_msg_ptrs_P in *.
  destruct qstart as [qstartb qstarti].
  simpljoin1.
  splits;auto.
  unfold dmportp_sllseg_qport_msg_next, get_off_addr. 
  cbn [fst snd].
  assert (($ Z.of_nat (typelen OSMsg_t)) = $ 33) by (clear;mauto).
  rewrite H.
  rewrite !Int.add_zero_l.
  destruct (msg_distance (qstartb, Int.mul ($ x) ($ 33))
  (qstartb, Int.mul ($ Int.unsigned qsize) ($ 33)) =? 1) eqn:?.
  - exists  0 x0.
    rewrite !Int.add_zero_l.
    splits;eauto.
    lia. 
  -  exists (x + 1) x0. 
    rewrite !Int.add_zero_l.
    splits;eauto.
    rewrite Int_add_one_Sn'' by lia.
    rewrite Int.mul_add_distr_l. 
    assert (Int.mul Int.one ($ 33) = $ 33) by (clear;mauto).
    rewrite H0.
    auto.
    assert (x + 1 = Int.unsigned qsize \/ x + 1 < Int.unsigned qsize) as [ | ] by lia;[ | lia].
    exfalso.
    rewrite <- H0 in *.
    unfold msg_distance in *.
    cbn [snd] in Heqb.
    rewrite H in Heqb.
    rewrite Int_add_one_Sn'' in Heqb by lia.
    rewrite Int.mul_add_distr_l in Heqb. 
    assert (Int.mul Int.one ($ 33) = $ 33) by (clear;mauto).
    rewrite H1 in Heqb.
    clear - Heqb.
    rewrite Int.sub_add_l in Heqb.
    rewrite Int.sub_idem in Heqb.
    rewrite Int.add_zero_l in Heqb.
    assert ((Int.divu ($ 33) ($ 33))  = $ 1) by mauto.
    rewrite H in Heqb.
    rewrite Int.unsigned_repr in Heqb by (clear;mauto).
    false.
Qed.

Lemma RL_PortPtrList_tail_null : forall  (dportl: list vallist) (headptr : val) (dpptrl: list addrval),
RL_PortPtrList headptr dportl dpptrl <->
RL_PortPtrList_tail headptr Vnull dportl dpptrl.
Proof.
  induction dportl;intros;destruct dpptrl;cbn;try tauto.
  split;intros.
  - simpljoin1.
    splits;eauto.
    eexists.
    split;eauto.
    eapply IHdportl. auto. 
  - simpljoin1.
    splits;eauto.
    eexists.
    split;eauto.
    eapply IHdportl. auto.
Qed. 

Lemma RL_PortPtrList_tail_app: forall dportl1 dport dportl2  dpptrl1 dpptrl2 dportlptr dportlptr' tail, 
length dpptrl1 = (length dportl1) ->
RL_PortPtrList_tail dportlptr (Vptr dportlptr') dportl1 dpptrl1  /\
RL_PortPtrList_tail (Vptr dportlptr') tail (dport :: dportl2) (dportlptr' :: dpptrl2) <->
RL_PortPtrList_tail dportlptr tail (dportl1 ++ dport :: dportl2) (dpptrl1  ++ (dportlptr' :: dpptrl2)).
Proof.
  induction dportl1;intros;destruct dpptrl1;simpl in H;tryfalse.
  - cbn in *. split;intros.
    + simpljoin1. 
    splits;cbn;auto.
    eexists.
    split;eauto.
    +
    simpljoin1.
    splits;auto.
    eexists.
    split;eauto.
  - simpl  ((_ :: _) ++ _). split;intros.
    * simpljoin1. cbn in H0.
    simpljoin1. 
    cbn.
    splits;auto.
    eexists.
    splits;eauto.
    eapply IHdportl1;eauto.
    *  cbn in H0.
    simpljoin1.
    eapply IHdportl1 in H2;eauto.
    simpljoin1.
    split;auto.
    cbn.
    split;eauto.
Qed.

Lemma RL_PortPtrList_tail_upd:
  forall dportl1 ndstport dportl2 headptr tailptr dpptrl1 dstportp dpptrl2 upd,
  RL_PortPtrList_tail headptr tailptr
  (dportl1 ++ ndstport :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2) ->
  length dportl1 = length dpptrl1 ->
  struct_type_vallist_match' OS_Port_Seg_dls ndstport ->
  OS_Port_V_nextPort upd = OS_Port_V_nextPort ndstport ->
  RL_PortPtrList_tail headptr tailptr
  (dportl1 ++ upd :: dportl2) (dpptrl1 ++ dstportp :: dpptrl2).
Proof.
  induction dportl1; destruct dpptrl1; simpl; intros; tryfalse; simpljoin1; eauto.
  split; eauto.
  exists x; split; eauto.
  rewrite H2; auto.
Qed.


Lemma  channel_V_dst_P_update_dport: forall l ptr kportvl kportl dportl1 dport dport' dportl2   dpptrl,
  OS_Port_V_direction dport = OS_Port_V_direction dport' ->
  channel_V_dst_P ptr l kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl ->
  channel_V_dst_P ptr l kportvl kportl (dportl1 ++ dport' :: dportl2) dpptrl.
Proof.
  induction l;intros;cbn [channel_V_dst_P] in *;auto.
  simpljoin1.
  eapply IHl in H1;eauto.
  split;auto.
  do 2 eexists.
  splits;eauto.
  assert (x1 = length dportl1 \/ x1 <> length dportl1) as [ | ] by lia.
  + subst x1. rewrite nth_error_middle in H6. inversion H6;subst x3. clear H6.
    exists (length dportl1) x2 dport'.
    split;eauto.
    splits;eauto.
    rewrite nth_error_middle;auto.
    congruence.
  + erewrite nth_error_middle_neq with (a':= dport') in H6 by lia.
    do 3 eexists.
    split;eauto.
Qed. 



Lemma  channel_V_srcdstkport_update_dport: forall chanvl  channell  dstkportll kportvl kportl dportl1 dport dport' dportl2   dpptrl,
  OS_Port_V_direction dport = OS_Port_V_direction dport' ->
  channel_V_srcdstkport chanvl channell  dstkportll kportvl kportl (dportl1 ++ dport :: dportl2) dpptrl ->
  channel_V_srcdstkport chanvl channell  dstkportll kportvl kportl (dportl1 ++ dport' :: dportl2) dpptrl.
Proof.
  induction chanvl;intros;
  destruct channell, dstkportll;cbn [channel_V_srcdstkport] in *;tryfalse;auto.
  simpljoin1.
  eapply IHchanvl in H1;eauto.
  split;auto.
  clear H1.
  destruct H0.
  left;auto.
  simpljoin1.
  right.
  eexists.
  split;eauto.
  split.
  - unfold channel_V_src_P in *.
    intros.
    specialize (H1 _ H0).
    simpljoin1.
    do 2 eexists.
    splits;eauto.
    assert (x2 = length dportl1 \/ x2 <> length dportl1) as [ | ] by lia.
    + subst x2. rewrite nth_error_middle in H7. inversion H7;subst x4. clear H7.
      exists (length dportl1) x3 dport'.
      split;eauto.
      splits;eauto.
      rewrite nth_error_middle;auto.
      congruence.
    + erewrite nth_error_middle_neq with (a':= dport') in H7 by lia.
      do 3 eexists.
      split;eauto. 
  - eapply channel_V_dst_P_update_dport;eauto.
Qed.


Lemma  channel_V_srcdstkport_app: forall chanvl1 chanvl2 channell1  dstkportll1  channell2  dstkportll2
  kportvl kportl  dportl  dpptrl,
  length chanvl1 = length channell1 ->
  length chanvl1 = length dstkportll1 ->
  channel_V_srcdstkport (chanvl1 ++ chanvl2) (channell1 ++ channell2)  (dstkportll1 ++ dstkportll2) kportvl kportl dportl dpptrl <->
  channel_V_srcdstkport chanvl1  channell1  dstkportll1 kportvl kportl dportl dpptrl /\ 
  channel_V_srcdstkport chanvl2 channell2  dstkportll2 kportvl kportl dportl dpptrl.
Proof.
  induction chanvl1;intros;
  destruct  channell1, dstkportll1;cbn in H;tryfalse;
  simpl  ((_ :: _) ++ _);
  cbn [channel_V_srcdstkport];try tauto.
  split;intros.
  - simpljoin1. 
    apply IHchanvl1 in H2;eauto.
    tauto.
  - simpljoin1.
    split;auto.
    apply IHchanvl1;auto.
Qed.  

Lemma  channel_V_dst_P_update_kport: forall l ptr kportvl1 kptr kportvl2  kportl1 kport kport' kportl2 dportl  dpptrl,
  length kportl1 = length kportvl1 ->
  OS_K_Port_V_channel kport = Some (Vnull) -> 
  channel_V_dst_P ptr l (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport :: kportl2) dportl dpptrl ->
  channel_V_dst_P ptr l (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction l;intros * Hlen Hkpchannull H;cbn [channel_V_dst_P] in *;auto.
  simpljoin1.
  eapply IHl  with (kport' := kport') in H0;eauto.
  split;auto.
  assert (x = length kportvl1 \/ x <> length kportvl1) as [ | ] by lia.
  + subst x.  rewrite <- Hlen in H1. rewrite nth_error_middle in H1. 
    inversion H1. subst x0.
    rewrite Hkpchannull in H2. inversion H2.
  + erewrite nth_error_middle_neq with (a':= kport') in H1 by (congruence).
    do 2 eexists.
    splits;eauto.
    do 3 eexists.
    split;eauto.
Qed. 

Lemma  channel_V_srcdstkport_update_kport: forall chanvl  channell  dstkportll kportvl1 kptr kportvl2  kportl1 kport kport' kportl2 dportl  dpptrl,
  length kportl1 = length kportvl1 ->
  OS_K_Port_V_channel kport = Some (Vnull) -> 
  channel_V_srcdstkport chanvl channell  dstkportll (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport :: kportl2) dportl dpptrl ->
  channel_V_srcdstkport chanvl channell  dstkportll (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction chanvl;intros * Hlen Hkpchannull H;
  destruct channell, dstkportll;cbn [channel_V_srcdstkport] in *;tryfalse;auto.
  simpljoin1.
  eapply IHchanvl  with (kport' := kport') in H0;eauto.
  split;auto.
  clear H0.
  destruct H.
  left;auto.
  simpljoin1.
  right.
  eexists.
  split;eauto.
  split.
  - unfold channel_V_src_P in *.
    intros.
    specialize (H0 _ H).
    simpljoin1.
    assert (x0 = length kportvl1 \/ x0 <> length kportvl1) as [ | ] by lia.
    + subst x0. rewrite <- Hlen in H2. rewrite nth_error_middle in H2. inversion H2;subst x1. 
      rewrite nth_error_middle in H0. inversion H0;subst kptr.  clear H0 H2.
      rewrite Hkpchannull in H3. inversion H3. 
    + erewrite nth_error_middle_neq with (a':= kport') in H2 by (congruence).
      do 2 eexists.
      splits;eauto.
      do 3 eexists.
      split;eauto. 
  - eapply channel_V_dst_P_update_kport;eauto.
Qed.

Lemma  channel_V_src_P_update_kport: forall l l' ptr dstkportl dstkportl' kportvl1 kptr kportvl2  kportl1 kport kport' kportl2 dportl  dpptrl,
  OS_Channel_V_srcPort l' = OS_Channel_V_srcPort l ->
  length kportl1 = length kportvl1 ->
  OS_K_Port_V_channel kport = Some (Vnull) -> 
  channel_V_src_P ptr l dstkportl (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport :: kportl2) dportl dpptrl ->
  channel_V_src_P ptr l' dstkportl' (kportvl1 ++ kptr :: kportvl2) (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  unfold channel_V_src_P. intros.
  rewrite H in H3.
  specialize (H2 _ H3).
  simpljoin1.
  assert (x = length kportvl1 \/ x <> length kportvl1) as [ | ] by lia.
  + subst x.  rewrite <- H0 in H4. rewrite nth_error_middle in H4. inversion H4;subst x0.
    rewrite H1 in H5. inversion H5. 
  + erewrite nth_error_middle_neq with (a':= kport') in H4 by (congruence).
    do 2 eexists.
    splits;eauto.
    do 3 eexists.
    split;eauto. 
Qed. 

Lemma  channel_V_dst_P_update_kport_adddst: forall   dstkportl ptr kportvl1 kptr kportvl2  kportl1 kport kport' kportl2 dportl  dpptrl,
  length kportl1 = length kportvl1 ->
  OS_K_Port_V_channel kport = Some (Vnull) -> 
  OS_K_Port_V_channel kport' = Some (Vptr ptr) ->
  (exists pid dmptr dmport,
    OS_K_Port_V_dmport kport' = Some (Vptr dmptr) /\
    nth_error dpptrl pid = Some dmptr /\
    nth_error dportl pid = Some dmport /\
    OS_Port_V_direction dmport = Some (V$ DESTINATION)) ->
  channel_V_dst_P ptr dstkportl (kportvl1 ++ (Vptr kptr)  :: kportvl2) (kportl1 ++ kport :: kportl2) dportl dpptrl ->
  channel_V_dst_P ptr (dstkportl ++ kptr :: nil) (kportvl1 ++ (Vptr kptr) :: kportvl2) (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction dstkportl;intros;cbn [channel_V_dst_P] in *;auto.
  - cbn. split;auto. 
    exists (length kportl1) kport'.
    splits;auto.
    rewrite H. eapply nth_error_middle.
    eapply nth_error_middle.
  - simpl ((_ :: _) ++ _).
    cbn.
    destruct H3. 
    eapply IHdstkportl in H4;eauto.
    split;auto.
    clear H2 H4.
    simpljoin1.
    assert (x = length kportvl1 \/ x <> length kportvl1) as [ | ] by lia.
    +  subst x.  rewrite <- H in H3. rewrite nth_error_middle in H3. inversion H3;subst x0.
      rewrite H0 in H4. inversion H4.
    +  erewrite nth_error_middle_neq with (a':= kport') in H3 by (congruence).
      do 2 eexists.
      splits;eauto.
      do 3 eexists.
      split;eauto. 
Qed. 

Lemma channel_V_srcdstkport_P_updatedst: forall chanptr (chann chann': vallist) (dstkportl dstkportl':  (list addrval)) kportvl kportl (dportl: list vallist) dpptrl,
OS_Channel_V_srcPort chann = OS_Channel_V_srcPort chann' ->
channel_V_dst_P chanptr dstkportl' kportvl kportl dportl dpptrl ->
channel_V_srcdstkport_P (Vptr chanptr)  chann dstkportl kportvl kportl dportl dpptrl ->
channel_V_srcdstkport_P (Vptr chanptr) chann' dstkportl' kportvl kportl dportl dpptrl.
Proof. 
  intros * Hchansrc Hchandst.
  unfold channel_V_srcdstkport_P;intros.
  destruct H. simpljoin1. tryfalse.
  destruct H as [? [? H]].
  inversion H0;subst x. clear H0.
  right.
  eexists.
  split;eauto.
  split.
  - destruct H as [H _].
    unfold channel_V_src_P in *.
    intros.
    rewrite <- Hchansrc in H0.
    specialize (H _ H0).
    simpljoin1.
    do 2 eexists.
    splits;eauto.
    do 3 eexists.
    splits;eauto.
  - destruct H as [_ H].
    auto.
Qed.


Lemma nth_error_nodup_midlle: forall kportvl1 kptr  kportvl2 n,
nth_error (kportvl1 ++  Vptr kptr :: kportvl2) n = Some (Vptr kptr) ->
NoDup (filter (fun a : val => match a with
                   | Vptr _ => true
                   | _ => false
                   end) (kportvl1 ++ Vptr kptr :: kportvl2)) ->
 n = length (kportvl1).
Proof.
  induction kportvl1;intros.
  - cbn in H.
    destruct n. 
    auto.
    cbn in H.
    apply nth_error_split in H as (? & ? & ? & ?). 
    subst.
    cbn in H0.
    rewrite filter_app in H0.
    cbn in H0.
    inversion H0.
    exfalso.
    apply H2.
    apply in_elt.
  - destruct n.
    { exfalso.
      cbn in H. 
      inversion H;subst a.
      rewrite filter_app in H0.
      cbn in H0.
      inversion H0.
      apply H3.
      apply in_elt. }
    cbn.
    simpl ((_ :: _) ++ _ ) in *.
    cbn in H.
    cbn in H0.
    destruct a.
    eapply IHkportvl1 in H;eauto.
    eapply IHkportvl1 in H;eauto.
    eapply IHkportvl1 in H;eauto.
    inversion H0.
    eapply IHkportvl1 in H;eauto.
Qed.

Lemma kportNode_P_app:
  forall kportvl1 kportvl2 kportl1 kportl2  b  kport,
    length kportvl1 = length kportl1 ->
    kportNode_P (kportvl1 ++ (Vptr (b,Int.zero)) :: kportvl2) (kportl1 ++ kport :: kportl2) ==>
      kportNode_P kportvl1 kportl1 **
      [| struct_type_vallist_match OS_K_Port kport |] ** 
      Astruct' (b,Int.zero) OS_K_Port_Seg_dls (firstn 6 kport)  **
      kportNode_P kportvl2 kportl2.
Proof.
  induction kportvl1; intros;destruct kportl1;simpl in H;tryfalse.
  { rewrite !app_nil_l in H0.
    cbn [kportNode_P] in *.
    sep normal in H0.
    sep autocancel.
    destruct H0.
    sep split in H0. simpljoin1. tryfalse.
    sep destruct H0.
    sep pauto.
    inversion H1.
    subst.
    auto.
  }
  {
    simpl ((_ :: _) ++ _ ) in *.
    cbn [kportNode_P] in *.
    apply disj_star_elim_disj in H0 as [? | ?].
    {
      sep split in H0.
      simpljoin1.
      apply IHkportvl1 in H0;[ | lia].
      sep autocancel.
      sep pauto.
      left.
      sep auto.
    }
    {
      sep normal in H0; sep destruct H0; sep split in H0.
      eapply astar_mono in H0.
      2: eauto.
      2: eapply IHkportvl1; eauto.
      sep pauto.
      right; sep pauto.
    }
  }
Qed.


Lemma kportNode_P_app_frm:
  forall kportvl1 kportvl2 kportl1 kportl2  b  kport P, 
    length kportvl1 = length kportl1 ->
    kportNode_P (kportvl1 ++ (Vptr (b,Int.zero)) :: kportvl2) (kportl1 ++ kport :: kportl2) ** P ==>
      kportNode_P kportvl1 kportl1 **
      [| struct_type_vallist_match OS_K_Port kport |] ** 
      Astruct' (b,Int.zero) OS_K_Port_Seg_dls (firstn 6 kport)  **
      kportNode_P kportvl2 kportl2 ** P.
Proof.
  intros.
  sep cancel P.
  eapply kportNode_P_app;eauto.
Qed.

Lemma good_frm_kport_V_OSEventPtr_sig: forall kportv kport_ dpptrl dportl,
 GoodFrm (kport_V_OSEventPtr_sig kportv kport_ dpptrl dportl).
Proof.
  destruct kportv; cbn; go.
  intros. splits; go.
  split; go. Qed.
Hint Resolve good_frm_kport_V_OSEventPtr_sig: good_frm_lemmas.

Lemma NoDup_kportvl_upd:
  forall kportvl1 kportv kportvl2 kportp kportfl,
    ( forall (id1 id2 : nat) (p1 p2 : addrval),
        id1 <> id2 ->
        nth_val id1 (kportvl1 ++ kportv :: kportvl2) =
        Some (Vptr p1) ->
        nth_val id2 (kportvl1 ++ kportv :: kportvl2) =
        Some (Vptr p2) -> p1 <> p2 ) ->
    NoDup_kportf_kportvl kportp kportfl
        (kportvl1 ++ kportv :: kportvl2) ->
    ( forall (id1 id2 : nat) (p0 p3 : addrval),
        id1 <> id2 ->
        nth_val id1 (kportvl1 ++ kportp :: kportvl2) =
        Some (Vptr p0) ->
        nth_val id2 (kportvl1 ++ kportp :: kportvl2) =
        Some (Vptr p3) -> p0 <> p3 ).
Proof.
  intros.
  destruct kportfl; cbn [NoDup_kportf_kportvl] in H0.
  { subst.
    assert (id1 = length kportvl1 \/ id1 <> length kportvl1) by tauto.
    destruct H0.
    { subst.
      rewrite nth_val_middle in H2.
      invertsr H2. }
    assert (id2 = length kportvl1 \/ id2 <> length kportvl1) by tauto.
    destruct H4.
    { subst.
      rewrite nth_val_middle in H3.
      invertsr H3. }
    eapply H.
    { apply H1. }
    { apply nth_val_nth_error.
      apply nth_val_nth_error in H2.
      rewrite <- H2.
      apply nth_error_middle_neq. auto. }
    { apply nth_val_nth_error.
      apply nth_val_nth_error in H3.
      rewrite <- H3.
      apply nth_error_middle_neq. auto. } }
  destruct H0.
  assert (id1 = length kportvl1 \/ id1 <> length kportvl1) by tauto.
  assert (id2 = length kportvl1 \/ id2 <> length kportvl1) by tauto.
  destruct H5; destruct H6.
  { subst. lia. }
  { subst.
    rewrite nth_val_middle in H2.
    invertsr H2.
    intro. destruct H0. subst.
    eapply nth_error_in with (n:=id2).
    apply nth_val_nth_error in H3.
    rewrite <- H3.
    apply nth_error_middle_neq. auto. }
  { subst.
    rewrite nth_val_middle in H3.
    invertsr H3.
    intro. destruct H0. subst.
    eapply nth_error_in with (n:=id1).
    apply nth_val_nth_error in H2.
    rewrite <- H2.
    apply nth_error_middle_neq. auto. }
  eapply H.
  { apply H1. }
  { apply nth_val_nth_error.
    apply nth_val_nth_error in H2.
    rewrite <- H2.
    apply nth_error_middle_neq. auto. }
  { apply nth_val_nth_error.
    apply nth_val_nth_error in H3.
    rewrite <- H3.
    apply nth_error_middle_neq. auto. }
Qed.

Lemma NoDup_kportf_eq:
  forall kportvl,
    ( forall (id1 id2 : nat) (p0 p3 : addrval),
        id1 <> id2 -> nth_val id1 kportvl = Some (Vptr p0) ->
        nth_val id2 kportvl = Some (Vptr p3) -> p0 <> p3 ) ->
    NoDup (filter (fun a : val => match a with | Vptr _ => true | _ => false end) (kportvl)).
Proof.
  induction kportvl; intros.
  { cbn. apply NoDup_nil. }
  destruct a; cbn.
  { eapply IHkportvl. intros. eapply H.
    { instantiate (1:=(S id2)).
      instantiate (1:=(S id1)). lia. }
    all: auto. }
  { eapply IHkportvl. intros. eapply H.
    { instantiate (1:=(S id2)).
      instantiate (1:=(S id1)). lia. }
    all: auto. }
  { eapply IHkportvl. intros. eapply H.
    { instantiate (1:=(S id2)).
      instantiate (1:=(S id1)). lia. }
    all: auto. }
  apply NoDup_cons.
  2:{ eapply IHkportvl. intros. eapply H.
      { instantiate (1:=(S id2)).
        instantiate (1:=(S id1)). lia. }
      all: auto. }
  intro.
  apply filter_In in H0. destruct H0.
  eapply In_nth_error in H0. simpljoin1.
  specialize (H O (S x) a a).
  assert (a <> a).
  2:{ destruct H1. auto. }
  apply H. { lia. } { simpl; auto. }
  apply nth_val_nth_error. simpl. auto.
Qed.

Lemma channel_V_src_P_upd_dport:
  forall x v l kportvl kportl dportl dpptrl dmport dmportp,
    channel_V_src_P x v l kportvl kportl dportl dpptrl ->
    channel_V_src_P x v l kportvl kportl (dmport :: dportl) (dmportp :: dpptrl).
Proof.
  unfold channel_V_src_P. intros.
  specialize (H srckp H0). simpljoin1.
  exists x0 x1. splits; eauto.
  exists (S x2) x3 x4. simpl.
  splits; auto.
Qed.

Lemma channel_V_dst_P_upd_dport:
  forall l x kportvl kportl dportl dpptrl dmport dmportp,
    channel_V_dst_P x l kportvl kportl dportl dpptrl ->
    channel_V_dst_P x l kportvl kportl (dmport :: dportl) (dmportp :: dpptrl).
Proof.
  induction l; cbn [channel_V_dst_P]; intros; auto.
  simpljoin1. splits; eauto.
  exists x0 x1. splits; eauto.
  exists (S x2) x3 x4. simpl.
  splits; auto.
Qed.

Lemma channel_V_srcdstkport_upd_dport:
  forall chanvl chanl chandstkportll kportvl kportl dmport dportl dmportp dpptrl,
    channel_V_srcdstkport chanvl chanl chandstkportll kportvl kportl dportl dpptrl ->
    channel_V_srcdstkport chanvl chanl chandstkportll kportvl kportl (dmport :: dportl) (dmportp :: dpptrl).
Proof.
  induction chanvl; destruct chanl; destruct chandstkportll; simpl; eauto.
  intros. destruct H. split; eauto.
  unfold channel_V_srcdstkport_P in *.
  destruct H; [left|right]; eauto.
  simpljoin1. exists x. splits; eauto.
  { apply channel_V_src_P_upd_dport; auto. }
  { apply channel_V_dst_P_upd_dport; auto. }
Qed.

Lemma channel_V_src_P_upd_kport_null:
  forall x v l kportvl1 kportvl2 kportl1 kport kportl2 dportl dpptrl kportp kport',
    length kportvl1 = length kportl1->
    channel_V_src_P x v l (kportvl1 ++ Vnull :: kportvl2)
      (kportl1 ++ kport :: kportl2) dportl dpptrl ->
    channel_V_src_P x v l (kportvl1 ++ kportp :: kportvl2)
      (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  unfold channel_V_src_P. intros.
  specialize (H0 srckp H1). simpljoin1.
  assert (x0 = length kportvl1 \/ x0 <> length kportvl1) by tauto.
  destruct H8; [subst| ].
  { exfalso. rewrite nth_error_middle in H0. invertsr H0. }
  exists x0 x1; splits; eauto.
  { erewrite nth_error_middle_neq; eauto. }
  { erewrite nth_error_middle_neq; eauto. lia. }
  do 3 eexists; splits; eauto.
Qed.

Lemma channel_V_dst_P_upd_kport_null:
  forall l x kportvl1 kportvl2 kportl1 kport kportl2 dportl dpptrl kportp kport',
    length kportvl1 = length kportl1->
    channel_V_dst_P x l (kportvl1 ++ Vnull :: kportvl2)
      (kportl1 ++ kport :: kportl2) dportl dpptrl ->
    channel_V_dst_P x l (kportvl1 ++ kportp :: kportvl2)
      (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction l; cbn [channel_V_dst_P]; intros; auto.
  simpljoin1. splits; eauto.
  assert (x0 = length kportvl1 \/ x0 <> length kportvl1) by tauto.
  destruct H8; [subst| ].
  { exfalso. rewrite nth_error_middle in H0. invertsr H0. }
  exists x0 x1. splits; eauto.
  { erewrite nth_error_middle_neq; eauto. }
  { erewrite nth_error_middle_neq; eauto. lia. }
  do 3 eexists; splits; eauto.
Qed.

Lemma channel_V_srcdstkport_P_upd_kport_null:
  forall a v l kportvl1 kportvl2 kportl1 kport kportl2 dportl dpptrl kportp kport',
    length kportvl1 = length kportl1 ->
    channel_V_srcdstkport_P a v l (kportvl1 ++ Vnull :: kportvl2) (kportl1 ++ kport :: kportl2) dportl dpptrl ->
    channel_V_srcdstkport_P a v l (kportvl1 ++ kportp :: kportvl2) (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  unfold channel_V_srcdstkport_P in *.
  intros. destruct H0; [left|right]; eauto.
  simpljoin1. exists x; splits; eauto.
  { eapply channel_V_src_P_upd_kport_null; eauto. }
  { eapply channel_V_dst_P_upd_kport_null; eauto. }
Qed.

Lemma channel_V_srcdstkport_upd_kport_null:
  forall chanvl chanl chandstkportll kportvl1 kportp kportvl2 kportl1 kport kport' kportl2 dportl dpptrl,
    length kportvl1 = length kportl1 ->
    channel_V_srcdstkport chanvl chanl chandstkportll
                          (kportvl1 ++ Vnull :: kportvl2)
                          (kportl1 ++ kport :: kportl2) dportl dpptrl ->
    channel_V_srcdstkport chanvl chanl chandstkportll
                          (kportvl1 ++ kportp :: kportvl2)
                          (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction chanvl; destruct chanl;
  destruct chandstkportll; cbn; eauto; intros.
  simpljoin1; split; eauto.
  eapply channel_V_srcdstkport_P_upd_kport_null; eauto.
Qed.

Lemma R_Kernelport_DomainPort_init_nonull_upd_kport_null:
  forall dportl dpptrl kportvl1 kportvl2 kportl1 kport kportl2 kportp kport',
    length kportvl1 = length kportl1 ->
    struct_type_vallist_match OS_K_Port kport' ->
    R_Kernelport_DomainPort_init_nonull (kportvl1 ++ Vnull :: kportvl2)
      (kportl1 ++ kport :: kportl2) dportl dpptrl ->
      R_Kernelport_DomainPort_init_nonull (kportvl1 ++ (Vptr kportp) :: kportvl2)
      (kportl1 ++ kport' :: kportl2) dportl dpptrl.
Proof.
  induction dportl; destruct dpptrl; cbn; eauto.
  intros. simpljoin1. split; eauto.
  assert (∘ (Int.unsigned x) = length kportvl1 \/
            ∘ (Int.unsigned x) <> length kportvl1) by tauto.
  destruct H9.
  { rewrite H9 in *. exfalso.
    rewrite nth_error_middle in H3. invertsr H3. }
  exists x x0 x1. splits; eauto.
  { erewrite nth_error_middle_neq; eauto. }
  { erewrite nth_error_middle_neq; eauto. lia. }
Qed.

Lemma R_Kernelport_DomainPort_init_inj:
  forall dportl dpptrl kportvl kportl,
    R_Kernelport_DomainPort_init_nonull kportvl kportl dportl dpptrl ->
    R_Kernelport_DomainPort_init kportvl kportl dportl dpptrl.
Proof.
  induction dportl; destruct dpptrl; cbn; eauto.
  intros. simpljoin1. split; eauto.
  left. do 3 eexists. splits; eauto.
Qed.

Lemma channel_V_src_P'_upd_dport:
  forall chann dstkportl kportvl kportl dport dportl dmportp dpptrl mode,
    OS_Port_V_mode dport = Some (V$ mode) ->
    channel_V_src_P' chann dstkportl kportvl kportl dportl dpptrl mode ->
    channel_V_src_P' chann dstkportl kportvl kportl (dport :: dportl) (dmportp :: dpptrl) mode.
Proof.
  unfold channel_V_src_P'. intros.
  destruct pid; simpl in H5, H6; eauto.
  invertsr H5. invertsr H6. auto.
Qed.

Lemma channel_V_src_P'_upd_kport_null:
  forall x l kportvl1 kportvl2 kportl1 kport kportl2 dportl dpptrl kportp kport' mode dmportp,
    length kportvl1 = length kportl1->
    (~ In dmportp dpptrl) ->
    OS_K_Port_V_dmport kport' = Some (Vptr dmportp) ->
    channel_V_src_P' x l (kportvl1 ++ Vnull :: kportvl2)
      (kportl1 ++ kport :: kportl2) dportl dpptrl mode ->
    channel_V_src_P' x l (kportvl1 ++ (Vptr kportp) :: kportvl2)
      (kportl1 ++ kport' :: kportl2) dportl dpptrl mode.
Proof.
  unfold channel_V_src_P'. intros.
  assert (n = length kportvl1 \/ n <> length kportvl1) by tauto.
  destruct H9.
  { subst n. rewrite H in H5.
    rewrite nth_error_middle in H4. invertsr H4.
    rewrite nth_error_middle in H5. invertsr H5.
    rewrite H1 in H6. invertsr H6.
    exfalso. destruct H0. eapply nth_error_in. eauto. }
  assert (nth_error (kportvl1 ++ Vnull :: kportvl2) n = Some (Vptr srckp)).
  { erewrite nth_error_middle_neq; eauto. }
  assert (nth_error (kportl1 ++ kport :: kportl2) n = Some kport0).
  { erewrite nth_error_middle_neq; eauto. lia. }
  eapply H2; eauto.
Qed.

Lemma kportNode_P_len_eq:
  forall kportvl kportl,
    kportNode_P kportvl kportl ==>
    [| length kportvl = length kportl |] **
    kportNode_P kportvl kportl.
Proof.
  induction kportvl; destruct kportl; cbn [kportNode_P];
  intros; sep pauto.
  { exfalso; eapply sep_exist_Afalse; eauto. }
  { exfalso; eapply sep_exist_Afalse; eauto. }
  simpl.
  eapply astar_mono in H.
  2: eauto.
  2: eapply IHkportvl.
  sep split in H. lia.
Qed.

Lemma struct_type_vallist_match_OSport_attr_t: forall portattrvl,
  struct_type_vallist_match OSport_attr_t portattrvl ->
  exists i i0 i1 i2 i3 i4,
    portattrvl = Vint32 i :: Vint32 i0 :: Vint32 i1 :: 
                 Vint32 i2 :: Vint32 i3 :: Vint32 i4 :: nil /\
  Int.unsigned i <= 255 /\
  Int.unsigned i0 <= 255 /\
  Int.unsigned i1 <= 255 /\
  Int.unsigned i4 <= 255.
Proof.
  intros.
  struct_type_vallist_match_elim.
  jauto.
Qed.