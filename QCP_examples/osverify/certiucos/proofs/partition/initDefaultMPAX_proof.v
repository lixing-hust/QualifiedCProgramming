Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import abs_op.
Require Import inv_prop.
Require Import os_inv.
Require Import ifun_spec.
Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_code_defs.
Require Import seplog_trm_tacs.
Require Import gjb_common.
Require Import MPAX_common.
Require Import MPAX_pure.
Require Import partition_common.
Require Import abs_op_partition_ext.

Open Scope Z_scope.
Open Scope int_scope.
Open Scope code_scope.


Local Open Scope list_scope.

Lemma mpaxl_succ':
   forall sch P q0 t evheap s l l' v v0 v1 v2 v3 v4 v5, 
    can_change_aop P ->
    l = (v :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil) ->
    l' = (v :: Vint32 Int.one :: Vint32 Int.one :: Vint32 Int.one :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) ->
    Get_struct evheap q0 = Some (q0, t, l) ->
    absinfer sch
      (<|| mpaxl_succ (|Vptr q0 :: nil|) ;; s ||> ** HEvStructHeap evheap ** P)
      (<|| s ||> ** HEvStructHeap (Set_struct evheap q0 t l') ** P).
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq.
  can_change_aop_solver.
  instantiate (1 := HEvStructHeap (Set_struct evheap q0 t l') ** P).
  can_change_aop_solver.
  instantiate (1 := END None).
  subst.
  infer_solver 0%nat.
  eapply absinfer_seq_end.
  can_change_aop_solver.
  can_change_aop_solver.
  auto.
Qed.

Lemma initDefaultMPAX_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal initDefaultMPAX vl logicl initDefaultMPAXPre ct->
    Some r =
    BuildRetI os_internal initDefaultMPAX vl logicl initDefaultMPAXPost ct->
    exists t d1 d2 s,
      os_internal initDefaultMPAX = Some (t, d1, d2, s) /\
      {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v' into corenum.
  rename v'0 into index.
  rename v'1 into isr.
  rename v'2 into ie.
  rename v'3 into is.
  rename v'4 into ier.
  rename v'5 into cs.
  rename v'6 into xmpax.
  rename v'7 into sms_mpax.
  rename v'8 into ses_mpax.
  rename v'9 into xmpaxvl.
  rename v'10 into sms_mpaxvl.
  rename v'11 into ses_mpaxvl.
  rename v'12 into evstructs.
  rename v'13 into q0.
  rename v'14 into q1.
  rename v'15 into q2.
  rename v'16 into vl0.
  rename v'17 into vl1.
  rename v'18 into vl2.
  rename v'19 into s.
  hoare forward.
  hoare forward.
  unfold AXMpax, ASMSMpax, ASESMpax in *.
  hoare_split_pure_all.
  lets HRH1: H8.
  lets HRH2: H10.
  lets HRH3: H12.
  unfold RH_XMpax_P in H8.
  unfold RH_SMS_Mpax_P in H10.
  unfold RH_SES_Mpax_P in H12.
  destruct H8 as (Hf1 & Ht1).
  destruct H10 as (Hf2 & Ht2).
  destruct H12 as (Hf3 & Ht3).
  lets Ht1': Ht1.
  lets Ht1'': Ht1.
  lets Ht2': Ht2.
  lets Ht3': Ht3.
  specialize Ht1' with (index := Int.zero).
  specialize Ht1'' with (index := Int.one).
  specialize Ht2' with (index := Int.zero).
  specialize Ht3' with (index := Int.zero).
  change get with XmcMod.get in Ht1'.
  change get with XmcMod.get in Ht1''.
  change get with SmsMod.get in Ht2'.
  change get with SesMod.get in Ht3'.
  assert(0 <= Int.unsigned Int.zero < 16).
  int auto.
  assert(0 <= Int.unsigned Int.one < 16).
  int auto.
  assert(0 <= Int.unsigned Int.zero < 8).
  int auto.
  assert(0 <= Int.unsigned Int.zero < 8).
  int auto.
  eapply Ht1' in H8.
  do 2 destruct H8.
  eapply Ht1'' in H10.
  do 2 destruct H10.
  eapply Ht2' in H12.
  do 2 destruct H12.
  eapply Ht3' in H14.
  do 2 destruct H14.
  unfold Axmpaxinfo in *.
  unfold xmpax_addr in *.
  hoare_lifts_trms_pre (Aarray).
(* xmpaxvl *)
  destruct xmpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; eauto | idtac];
  try eapply pfalse_rule) | idtac].
  do 31 (destruct xmpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse;
   eauto | idtac];
  try eapply pfalse_rule) | idtac]).
  destruct xmpaxvl;simpl Aarray;
  [idtac |try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse; eauto |
   idtac];
  try eapply pfalse_rule)].
  lets Hsg: H8.
  unfold R_XMpax_P in H9.
  destruct H9.
  unfold RHL_XMpax_P in H9.
  eapply H9 in Hsg.
  destruct Hsg.
  lets Hsg': H10.
  eapply H9 in Hsg'.
  destruct Hsg'.
  change (Z.to_nat (Int.unsigned Int.zero * 2)) with O in H16.
  simpl in H16; inverts H16.
  change (Z.to_nat (Int.unsigned Int.zero * 2 + 1)) with (S O) in H17.
  simpl in H17; inverts H17.
  change (Z.to_nat (Int.unsigned Int.one * 2)) with (S (S (O))) in H18.
  simpl in H18; inverts H18.
  change (Z.to_nat (Int.unsigned Int.one * 2 + 1)) with (S (S (S (O)))) in H19.
  simpl in H19; inverts H19.
  hoare unfold.
  inverts H6.
  substs.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_XMCL_unfold'.
  sep cancel AEvStructHeap.
  sep_lifts_trms_in Hsat mpaxl.
  instantiate(3:= mpaxl).
  sep cancel mpaxl.
  eauto.
  eauto.
  hoare_split_pure_all.
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply csl_xmc_getXMPAXL_rule; eauto.
(* 0 <= Int.unsigned Int.zero < 16 *)
  2: int auto.
  2:{ introv Hsat.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      sep split; eauto.
      change ($ Int.unsigned Int.zero * 8) with Int.zero.
      sep pauto.
    }
  Ltac can_change_aop_solver :=
    try unfold AOSInthandler;
    try unfold AOSInthandlerParam;
    try unfold AOSExchandler;
    try unfold tcblist;
    try unfold LINV;
    try unfold OSLInv;
    try unfold Axmpaxinfo;
    try unfold Asms_mpaxinfo;
    try unfold Ases_mpaxinfo;
    go.
  can_change_aop_solver.
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  hoare abscsq.
  apply noabs_oslinv.
  eapply mpaxl_succ'; eauto.
  can_change_aop_solver.
  instantiate (8 := XMC_XMPAXL).
  instantiate (7 := Vint32 (get_part x2 0 8)).
  instantiate (6 := Vint32 (get_part x2 26 5)).
  instantiate (5 := Vint32 (get_part x2 27 4)).
  instantiate (4 := Vint32 (get_part x2 28 3)).
  instantiate (3 := Vint32 (get_part x2 29 2)).
  instantiate (2 := Vint32 (get_part x2 30 1)).
  instantiate (1 := Vint32 (get_part x2 31 0)).
  unfold get_mpax_struct, get_mpax.
  eapply get_set_struct_xmcl_vl; eauto.
(* CSL_XMC_setXMPAXL (os_initDefaultMPAX.index ′, xmpaxl ′); *)
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply csl_xmc_setXMPAXL_rule; eauto.
  2: int auto.
  2:{ introv Hsat.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      sep pauto.
      splits; eauto.
      rewrite set_struct_update_vl; eauto.
      eapply get_set_struct_xmcl_vl; eauto.
      eapply get_struct_vl'; eauto.
      unfold struct_type_vallist_match.
      unfold struct_type_vallist_match'.
      splits; eauto.
    }
    can_change_aop_solver.
(*  ==> CurLINV OSLInv ct *)
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
(* index = 1 *)
  hoare forward.
  hoare_split_pure_all.
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply csl_xmc_getXMPAXL_rule with 
       (xmc := (XmcMod.set xmpax Int.zero
     (set_mpax_struct x2
        (xmc_raddr
         :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
        (Vint32 (get_part x2 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil), x3))); eauto.
(* 0 <= Int.unsigned Int.zero < 16 *)
  2: int auto.
  2: rewrite XmcMod.map_get_set'; eauto.
  2:{ introv Hsat.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      change ($ Int.unsigned Int.one * 8) with ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4).
      sep pauto.
    }
  can_change_aop_solver.
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  hoare abscsq.
  apply noabs_oslinv.
  eapply mpaxl_succ'; eauto.
  can_change_aop_solver.
  instantiate (8 := XMC_XMPAXL).
  instantiate (7 := Vint32 (get_part x4 0 8)).
  instantiate (6 := Vint32 (get_part x4 26 5)).
  instantiate (5 := Vint32 (get_part x4 27 4)).
  instantiate (4 := Vint32 (get_part x4 28 3)).
  instantiate (3 := Vint32 (get_part x4 29 2)).
  instantiate (2 := Vint32 (get_part x4 30 1)).
  instantiate (1 := Vint32 (get_part x4 31 0)).
  do 2 (rewrite set_struct_update_vl; eauto).
  2: eapply get_struct_vl'; eauto.
  unfold get_mpax_struct, get_mpax.
  eapply get_set_struct_xmcl_vl; eauto.
  eapply get_struct_vl'; eauto.
(* CSL_XMC_setXMPAXL (os_initDefaultMPAX.index ′, xmpaxl ′); *)
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply csl_xmc_setXMPAXL_rule with 
   (xmc := (XmcMod.set xmpax Int.zero
   (set_mpax_struct x2
      (xmc_raddr
       :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
      (Vint32 (get_part x2 0 8)
       :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil), x3))); eauto.
(* 0 <= Int.unsigned Int.zero < 16 *)
  2: int auto.
(*  XmcMod.get (XmcMod.set _ _ _) _ = _ *)
  2: rewrite XmcMod.map_get_set'; eauto.
  2:{ introv Hsat.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      sep pauto.
      splits; eauto.
      do 2 (rewrite set_struct_update_vl; eauto).
      2: eapply get_struct_vl'; eauto.
      rewrite set_struct_update_vl; eauto.
      eapply get_set_struct_xmcl_vl; eauto.
      eapply get_struct_vl'; eauto.
      eapply get_struct_vl'; eauto.
    }
  can_change_aop_solver.
(*  ==> CurLINV OSLInv ct *)
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_XMCL_fold.
  instantiate (2:= q0).
  exists (Vint32 (get_part x4 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  exists v'. exists v'0.
  sep pauto.
(* R_MutexAttr_P XMC_XMPAXL vl' *)
  unfold R_MutexAttr_P.
  intros; tryfalse.
(* index = 0 *)
  hoare forward.
  unfold Asms_mpaxinfo in *.
  unfold sms_mpax_addr in *.
  hoare unfold.
  hoare_lifts_trms_pre (Aarray).
  destruct sms_mpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; eauto | idtac];
  try eapply pfalse_rule) | idtac].
  do 15 (destruct sms_mpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse;
   eauto | idtac];
  try eapply pfalse_rule) | idtac]).
  destruct sms_mpaxvl;simpl Aarray;
  [idtac |try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse; eauto |
   idtac];
  try eapply pfalse_rule)].
  lets Hsg: H12.
  unfold R_SMS_Mpax_P in H11.
  destruct H11.
  unfold RHL_SMS_Mpax_P in H11.
  eapply H11 in Hsg.
  destruct Hsg.
  change (Z.to_nat (Int.unsigned Int.zero * 2)) with O in H47.
  simpl in H47; inverts H47.
  change (Z.to_nat (Int.unsigned Int.zero * 2 + 1)) with (S O) in H48.
  simpl in H48; inverts H48.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_SMSL_unfold with (smsmpaxl:= sms_mpaxl).
  sep cancel AEvStructHeap.
  sep_lifts_trms_in Hsat sms_mpaxl.
  sep cancel sms_mpaxl.
  eauto.
  rewrite <- H0.
  assert (Get_struct
          (v' ++
           (q0, XMC_XMPAXL,
           Vint32 (get_part x4 0 8)
           :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) :: v'0) q1 =
        Get_struct
        (v' ++
           (q0, XMC_XMPAXL,
              Vint32 i17
              :: Vint32 i4
                 :: Vint32 i3
                    :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
              :: v'0) q1).
  { clear -H0 H5.
    induction v'.
    change (nil ++ (q0, XMC_XMPAXL, Vint32 i17 :: Vint32 i4 ::
                     Vint32 i3 :: Vint32 i2 :: Vint32 i1 ::
                     Vint32 i0 :: Vint32 i :: nil) :: v'0) with
                  ((q0, XMC_XMPAXL, Vint32 i17 :: Vint32 i4 ::
                     Vint32 i3 :: Vint32 i2 :: Vint32 i1 ::
                     Vint32 i0 :: Vint32 i :: nil) :: v'0) in *.
    change (nil ++ (q0, XMC_XMPAXL, Vint32 (get_part x4 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'0) with
                  ((q0, XMC_XMPAXL, Vint32 (get_part x4 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'0) in *.
    unfold Get_struct in *.
    destruct (os_inv.beq_addrval q0 q1) eqn :H1'.
    eapply OSTimeTickPure.beq_addrval_eq in H1'.
    tryfalse.
    fold Get_struct in *. auto.
    destruct a. destruct p.
    assert(a = q1 \/ a <> q1) by tauto.
    destruct H.
    inverts H.
    unfold Get_struct in *.
    simpl.
    rewrite beq_tid_true. auto.
    unfold Get_struct in H0.
    simpl in H0.
    unfold Get_struct.
    simpl.
    destruct (os_inv.beq_addrval a q1) eqn : H2. auto.
    auto.
  }
  auto.
(* CSL_MSMC_getSMSMPAXL (os_code_defs.corenum ′, os_initDefaultMPAX.index ′, smsmpaxl0 ′); *)
  hoare_split_pure_all.
  hoare forward.
  do 4 (rewrite set_struct_update_vl in H39; 
        try(eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in H39; eauto.
  eapply XmcMod.option2val in H39.
  hoare_lifts_trms_pre (Aop).
  substs.
  eapply csl_msmc_getSMSMPAXL_rule; eauto.
(* Z.of_nat (Z.to_nat DNUM) <= Int.max_unsigned *)
  2: { int auto.
       lets Hd :dnum_range.
       int auto. 
     }
(* 0 <= Int.unsigned Int.zero < 8 *)
  2: int auto.
  2:{ introv Hsat.
      rewrite Z2Nat.id.
      2: { lets Hd :dnum_range; mauto. }
      eapply aconj_intro.
      sep get rv.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      change ($ Int.unsigned Int.zero * 8) with Int.zero.
      sep pauto.
      splits; eauto.
      do 4 (rewrite set_struct_update_vl in *; 
            try(eapply get_struct_vl'); eauto).
      rewrite H39. rewrite H49.
      eapply get_struct_vl'; eauto.
    }
  can_change_aop_solver.
(*  ==> CurLINV OSLInv ct *)
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  hoare abscsq.
  apply noabs_oslinv.
  eapply mpaxl_succ'; eauto.
  can_change_aop_solver.
  instantiate (8 := MSMC_SMSMPAXL).
  instantiate (7 := Vint32 (get_part x6 0 8)).
  instantiate (6 := Vint32 (get_part x6 26 5)).
  instantiate (5 := Vint32 (get_part x6 27 4)).
  instantiate (4 := Vint32 (get_part x6 28 3)).
  instantiate (3 := Vint32 (get_part x6 29 2)).
  instantiate (2 := Vint32 (get_part x6 30 1)).
  instantiate (1 := Vint32 (get_part x6 31 0)).
  do 4 (rewrite set_struct_update_vl in *; 
      try(eapply get_struct_vl'); eauto).

  change (q0, XMC_XMPAXL,
            Vint32 (get_part x4 0 8)
            :: Vint32 Int.one
               :: Vint32 Int.one
                  :: Vint32 Int.one
                     :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
        (q0, XMC_XMPAXL,
         Vint32 (get_part x4 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  rewrite H49.
  unfold get_mpax_struct, get_mpax.
  eapply get_set_struct_smsl_vl; eauto.
  eapply get_struct_vl'; eauto.
(* CSL_MSMC_setSMSMPAXL ((os_code_defs.corenum ′, os_initDefaultMPAX.index ′,
smsmpaxl ′); *)
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply csl_msmc_setSMSMPAXL_rule; eauto.
  2: { int auto.
       lets Hd :dnum_range.
       int auto. 
     }
  2: int auto.
  2:{ introv Hsat.
      rewrite Z2Nat.id.
      2: { lets Hd :dnum_range; mauto. }
      eapply aconj_intro.
      sep get rv.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
   2:{ intros.
       sep pauto.
       splits; eauto.
       do 4 (rewrite set_struct_update_vl in *; 
        try(eapply get_struct_vl'); eauto).

       change (q0, XMC_XMPAXL,
                Vint32 (get_part x4 0 8)
                :: Vint32 Int.one
                   :: Vint32 Int.one
                      :: Vint32 Int.one
                         :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
            (q0, XMC_XMPAXL,
             Vint32 (get_part x4 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
       rewrite H49.
       rewrite set_struct_update_vl'; eauto.
       eapply get_set_struct_smsl_vl; eauto.
       eapply get_struct_vl'; eauto.
       eapply get_struct_vl'; eauto.
     }
  can_change_aop_solver.
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_SMSL_fold.
  instantiate (2:= q1).
  exists (Vint32 (get_part x6 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  exists v'1. exists v'2.
  sep pauto.
  unfold R_MutexAttr_P.
  intros; tryfalse.
  unfold Ases_mpaxinfo in *.
  unfold ses_mpax_addr in *.
  hoare unfold.
  hoare_lifts_trms_pre (Aarray).
  destruct ses_mpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; eauto | idtac];
  try eapply pfalse_rule) | idtac].
  do 15 (destruct ses_mpaxvl;simpl Aarray;
  [try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse;
   eauto | idtac];
  try eapply pfalse_rule) | idtac]).
  destruct ses_mpaxvl;simpl Aarray;
  [idtac |try (eapply backward_rule1;
  [intros; eapply astar_l_afalse_elim; sep cancel Afalse; eauto | idtac];
  try eapply pfalse_rule)].
  lets Hsg: H14.
  unfold R_SES_Mpax_P in H13.
  destruct H13.
  unfold RHL_SES_Mpax_P in H13.
  eapply H13 in Hsg.
  destruct Hsg.
  change (Z.to_nat (Int.unsigned Int.zero * 2)) with O in H57.
  simpl in H57; inverts H57.
  change (Z.to_nat (Int.unsigned Int.zero * 2 + 1)) with (S O) in H58.
  simpl in H58; inverts H58.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_SESL_unfold with (sesmpaxl:= ses_mpaxl).
  sep cancel AEvStructHeap.
  sep_lifts_trms_in Hsat ses_mpaxl.
  sep cancel ses_mpaxl.
  eauto.
  instantiate (1 := (Vint32 i19 :: Vint32 i16 :: Vint32 i15 ::
                     Vint32 i14 :: Vint32 i13 :: Vint32 i12 ::
                     Vint32 i11 :: nil)).
  assert (Get_struct
          (v'1 ++
             (q1, MSMC_SMSMPAXL,
             Vint32 (get_part x6 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) :: v'2) q2 =
        Get_struct
        (v'1 ++
          (q1, MSMC_SMSMPAXL,
            Vint32 i18
             :: Vint32 i10
                :: Vint32 i9
                   :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: nil)
          :: v'2) q2).
  { clear -H4 H18.
    induction v'1.
    change (nil ++ (q1, MSMC_SMSMPAXL, Vint32 i18 :: Vint32 i10 ::
                     Vint32 i9 :: Vint32 i8 :: Vint32 i7 ::
                     Vint32 i6 :: Vint32 i5 :: nil) :: v'2) with
                  ((q1, MSMC_SMSMPAXL, Vint32 i18 :: Vint32 i10 ::
                     Vint32 i9 :: Vint32 i8 :: Vint32 i7 ::
                     Vint32 i6 :: Vint32 i5 :: nil) :: v'2) in *.
    change (nil ++ (q1, MSMC_SMSMPAXL, Vint32 (get_part x6 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'2) with
                  ((q1, MSMC_SMSMPAXL, Vint32 (get_part x6 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'2) in *.
    unfold Get_struct in *.
    destruct (os_inv.beq_addrval q1 q2) eqn :H1'.
    eapply OSTimeTickPure.beq_addrval_eq in H1'.
    tryfalse.
    fold Get_struct in *. auto.
    destruct a. destruct p.
    assert(a = q2 \/ a <> q2) by tauto.
    destruct H.
    inverts H.
    unfold Get_struct in *.
    simpl.
    rewrite beq_tid_true. auto.
    unfold Get_struct in H4.
    simpl in H4.
    unfold Get_struct.
    simpl.
    destruct (os_inv.beq_addrval a q2) eqn : H2. auto.
    auto.
  }
  rewrite <- H49 in H57.
  assert (Get_struct
          (v' ++
           (q0, XMC_XMPAXL,
           Vint32 (get_part x4 0 8)
           :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) :: v'0) q2 =
        Get_struct
        (v' ++
           (q0, XMC_XMPAXL,
              Vint32 i17
              :: Vint32 i4
                 :: Vint32 i3
                    :: Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: nil)
              :: v'0) q2).
  { clear -H4 H17.
    induction v'.
    change (nil ++ (q0, XMC_XMPAXL, Vint32 i17 :: Vint32 i4 ::
                     Vint32 i3 :: Vint32 i2 :: Vint32 i1 ::
                     Vint32 i0 :: Vint32 i :: nil) :: v'0) with
                  ((q0, XMC_XMPAXL, Vint32 i17 :: Vint32 i4 ::
                     Vint32 i3 :: Vint32 i2 :: Vint32 i1 ::
                     Vint32 i0 :: Vint32 i :: nil) :: v'0) in *.
    change (nil ++ (q0, XMC_XMPAXL, Vint32 (get_part x4 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'0) with
                  ((q0, XMC_XMPAXL, Vint32 (get_part x4 0 8) ::
            V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 ::
            nil) :: v'0) in *.
    unfold Get_struct in *.
    destruct (os_inv.beq_addrval q0 q2) eqn :H1'.
    eapply OSTimeTickPure.beq_addrval_eq in H1'.
    tryfalse.
    fold Get_struct in *. auto.
    destruct a. destruct p.
    assert(a = q2 \/ a <> q2) by tauto.
    destruct H.
    inverts H.
    unfold Get_struct in *.
    simpl.
    rewrite beq_tid_true. auto.
    unfold Get_struct in H4.
    simpl in H4.
    unfold Get_struct.
    simpl.
    destruct (os_inv.beq_addrval a q2) eqn : H2. auto.
    auto.
  }
  rewrite H57.
  rewrite H58.
  eapply H4.
  hoare_split_pure_all.
  hoare forward.
  do 4 (rewrite set_struct_update_vl in H51; 
        try(eapply get_struct_vl'); eauto).
  change (q0, XMC_XMPAXL,
                Vint32 (get_part x4 0 8)
                :: Vint32 Int.one
                   :: Vint32 Int.one
                      :: Vint32 Int.one
                         :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
            (q0, XMC_XMPAXL,
             Vint32 (get_part x4 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) in *.
  rewrite H49 in H51.
  do 2 (rewrite set_struct_update_vl' in H51;
         try(eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in H51; eauto.
  eapply SmsMod.option2val in H51.
  hoare_lifts_trms_pre (Aop).
  substs.
  eapply csl_msmc_getSESMPAXL_rule; eauto.
  2: { int auto.
       lets Hd :dnum_range.
       int auto. 
     }
  2: int auto.
  2:{ introv Hsat.
      rewrite Z2Nat.id.
      2: { lets Hd :dnum_range; mauto. }
      eapply aconj_intro.
      sep get rv.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
  2:{ intros.
      change ($ Int.unsigned Int.zero * 8) with Int.zero.
      sep pauto.
      splits; eauto.
      do 4 (rewrite set_struct_update_vl in *; 
            try(eapply get_struct_vl'); eauto).
      change (q0, XMC_XMPAXL,
                Vint32 (get_part x4 0 8)
                :: Vint32 Int.one
                   :: Vint32 Int.one
                      :: Vint32 Int.one
                         :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
            (q0, XMC_XMPAXL,
             Vint32 (get_part x4 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil) in *.
      rewrite H49.
      do 2 (rewrite set_struct_update_vl';
         try(eapply get_struct_vl'); eauto).
      rewrite H51.
      rewrite H59.
      eapply get_struct_vl'; eauto.
    }
  can_change_aop_solver.
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  hoare_lifts_trms_pre (Aop, evstructheapid).
  hoare abscsq.
  apply noabs_oslinv.
  eapply mpaxl_succ'; eauto.
  can_change_aop_solver.
  instantiate (8 := MSMC_SESMPAXL).
  instantiate (7 := Vint32 (get_part x8 0 8)).
  instantiate (6 := Vint32 (get_part x8 26 5)).
  instantiate (5 := Vint32 (get_part x8 27 4)).
  instantiate (4 := Vint32 (get_part x8 28 3)).
  instantiate (3 := Vint32 (get_part x8 29 2)).
  instantiate (2 := Vint32 (get_part x8 30 1)).
  instantiate (1 := Vint32 (get_part x8 31 0)).
  do 4 (rewrite set_struct_update_vl in *; 
      try(eapply get_struct_vl'); eauto).
  change (q0, XMC_XMPAXL,
            Vint32 (get_part x4 0 8)
            :: Vint32 Int.one
               :: Vint32 Int.one
                  :: Vint32 Int.one
                     :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
        (q0, XMC_XMPAXL,
         Vint32 (get_part x4 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  rewrite H49.
  do 2 (rewrite set_struct_update_vl';
     try(eapply get_struct_vl'); eauto).
  change (q1, MSMC_SMSMPAXL,
            Vint32 (get_part x6 0 8)
            :: Vint32 Int.one
               :: Vint32 Int.one
                  :: Vint32 Int.one
                     :: Vint32 Int.zero
                        :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
        (q1, MSMC_SMSMPAXL,
         Vint32 (get_part x6 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  rewrite H59.
  unfold get_mpax_struct, get_mpax.
  eapply get_set_struct_sesl_vl; eauto.
  eapply get_struct_vl'; eauto.
(* CSL_MSMC_setSESMPAXL ((os_code_defs.corenum ′, os_initDefaultMPAX.index ′,
sesmpaxl ′); *)
  hoare forward.
  hoare_lifts_trms_pre (Aop).
  eapply csl_msmc_setSESMPAXL_rule; eauto.
  2: { int auto.
       lets Hd :dnum_range.
       int auto. 
     }
  2: int auto.
  2:{ introv Hsat.
      rewrite Z2Nat.id.
      2: { lets Hd :dnum_range; mauto. }
      eapply aconj_intro.
      sep get rv.
      eapply aconj_intro.
      sep get rv.
      sep get rv.
    }
   2:{ intros.
       sep pauto.
       splits; eauto.
       do 4 (rewrite set_struct_update_vl in *; 
       try(eapply get_struct_vl'); eauto).
       change (q0, XMC_XMPAXL,
                Vint32 (get_part x4 0 8)
                :: Vint32 Int.one
                   :: Vint32 Int.one
                      :: Vint32 Int.one
                         :: Vint32 Int.zero :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
            (q0, XMC_XMPAXL,
             Vint32 (get_part x4 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
       rewrite H49.
       do 2 (rewrite set_struct_update_vl';
       try(eapply get_struct_vl'); eauto).
       change (q1, MSMC_SMSMPAXL,
                Vint32 (get_part x6 0 8)
                :: Vint32 Int.one
                   :: Vint32 Int.one
                      :: Vint32 Int.one
                         :: Vint32 Int.zero
                            :: Vint32 Int.zero :: Vint32 Int.zero :: nil) with 
              (q1, MSMC_SMSMPAXL,
                Vint32 (get_part x6 0 8)
                :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
       rewrite H59.
       do 2 (rewrite set_struct_update_ses_vl;
       try(eapply get_struct_vl'); eauto).
     }
  can_change_aop_solver.
  introv Hsat.
  unfold CurLINV.
  exists init_lg.
  unfold p_local in Hsat.
  sep normal in Hsat.
  sep auto.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply AEvStructHeap_SESL_fold.
  instantiate (2:= q2).
  exists (Vint32 (get_part x8 0 8)
             :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil).
  exists v'3. exists v'4.
  sep pauto.
  unfold R_MutexAttr_P.
  intros; tryfalse.
  hoare_split_pure_all.
  hoare unfold.
  do 2 (rewrite set_struct_update_vl in H20;
        try (eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in H20; eauto.
  eapply XmcMod.option2val in H20.
  do 4 (rewrite set_struct_update_vl in H39; 
        try (eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in H39; eauto.
  eapply SmsMod.option2val in H39.
  do 4 (rewrite set_struct_update_vl in H51; 
        try (eapply get_struct_vl'); eauto).
  rewrite H39 in H51.
  rewrite H49 in H51.
  do 2 (rewrite set_struct_update_vl' in H51; 
        try (eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in H51; eauto.
  eapply SmsMod.option2val in H51.
  do 4 (rewrite set_struct_update_vl in *; 
        try (eapply get_struct_vl'); eauto).
  rewrite H39 in *.
  rewrite H49 in *.
  do 2 (rewrite set_struct_update_vl' in *; 
        try (eapply get_struct_vl'); eauto).
  rewrite H51 in *.
  rewrite H59 in *.
  do 2 (rewrite set_struct_update_ses_vl in *; 
        try (eapply get_struct_vl'); eauto).
  rewrite get_struct_vl' in *; eauto.
  eapply SesMod.option2val in H61.
(* Return *)
  hoare forward.
  instantiate (1:= 
      Vint32
             (set_mpax_struct x8
                (sesl_raddr
                 :: sesl_sr
                    :: sesl_sw
                       :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
                (Vint32 (get_part x8 0 8)
                 :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
     :: Vint32 x9 :: v43 :: v44 :: v45 :: v46 :: v47
     :: v48 :: v49 :: v50 :: v51 :: v52 :: v53 :: v54
     :: v55 :: v56 :: nil).
  instantiate (1:= 
          Vint32
                 (set_mpax_struct x6
                    (smsl_raddr
                     :: smsl_sr
                        :: smsl_sw
                           :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
                    (Vint32 (get_part x6 0 8)
                     :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
         :: Vint32 x7 :: v1 :: v2 :: v31 :: v32 :: v33
         :: v34 :: v35 :: v36 :: v37 :: v38 :: v39 :: v40
         :: v41 :: v42 :: nil).
  instantiate (1:= 
          Vint32
               (set_mpax_struct x2
                  (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
               (Vint32 (get_part x2 0 8)
                   :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
         :: Vint32 x3
         :: Vint32
                 (set_mpax_struct x4
                    (xmc_raddr
                     :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                    (Vint32 (get_part x4 0 8)
                    :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
         :: Vint32 x5 
         :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 
         :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 
         :: v15 :: v16 :: v17 :: v18 :: v19 :: v20
         :: v21 :: v22 :: v23 :: v24 :: v25 :: v26 
         :: v27 :: v28 :: v29 :: v30 :: nil).
  destruct (Vint32
           (set_mpax_struct x2
              (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
           (Vint32 (get_part x2 0 8)
               :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
     :: Vint32 x3
     :: Vint32
             (set_mpax_struct x4
                (xmc_raddr
                 :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                (Vint32 (get_part x4 0 8)
                :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
     :: Vint32 x5 
     :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 
     :: v9 :: v10 :: v11 :: v12 :: v13 :: v14
     :: v15 :: v16 :: v17 :: v18 :: v19 :: v20
     :: v21 :: v22 :: v23 :: v24 :: v25 :: v26 
     :: v27 :: v28 :: v29 :: v30 :: nil)
  eqn:eq; subst; inverts eq.
  change ($ Int.unsigned Int.zero * 8) with Int.zero in *.
  change ($ Int.unsigned Int.one * 8) with ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) in *.
  sep pauto.
  split; auto. clear.
  instantiate (1:= q2).
  instantiate (1:= q1).
  instantiate (1:= q0). auto.
  instantiate (1:= (set_mpax_struct x8
        (sesl_raddr
         :: sesl_sr
            :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
        (Vint32 (get_part x8 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))); auto.
  splits; eauto.
  rewrite get_mpax_struct_sesl with (v:= (get_part x8 0 8)); eauto.
  instantiate (1:= (v'3 ++
                    (q2, MSMC_SESMPAXL,
                    Vint32 i19
                    :: Vint32 i16
                       :: Vint32 i15
                          :: Vint32 i14 :: Vint32 i13 :: Vint32 i12 :: Vint32 i11 :: nil)
                    :: v'4)).
  rewrite set_struct_update_ses_vl; eauto.
  eapply get_struct_vl'; eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x8) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
  rewrite get_mpax_struct_sesl with (v:= (get_part x8 0 8)); eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x8) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
  instantiate (1:= (set_mpax_struct x6
        (smsl_raddr
         :: smsl_sr
            :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
        (Vint32 (get_part x6 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))); auto.
  splits; eauto.
  rewrite get_mpax_struct_smsl with (v:= (get_part x6 0 8)); eauto.
  rewrite <- H59.
  instantiate (1:= v'1 ++ (q1, MSMC_SMSMPAXL,
                     Vint32 i18
                     :: Vint32 i10
                        :: Vint32 i9
                           :: Vint32 i8 :: Vint32 i7 :: Vint32 i6 :: Vint32 i5 :: nil) :: v'2).
  rewrite set_struct_update_vl'; eauto.
  eapply get_struct_vl'; eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x6) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
  rewrite get_mpax_struct_smsl with (v:= (get_part x6 0 8)); eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x6) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
  instantiate (1:= (set_mpax_struct x4
              (xmc_raddr
               :: xmc_sr
                  :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
              (Vint32 (get_part x4 0 8)
               :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))); auto.
  splits; eauto.
  rewrite get_mpax_struct_xmc with (v:= (get_part x4 0 8)); eauto.
  rewrite <- H49.
  rewrite set_struct_update_vl; eauto.
  eapply get_struct_vl'; eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x4) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
  rewrite get_mpax_struct_xmc with (v:= (get_part x4 0 8)); eauto.
  clear.
  intros.
  assert (0 <= d <= 31) by int auto.
  assert (0 <= 0 + 8 <= 31)%nat by int auto.
  lets Hte: get_part_testbit_eq H0 H1.
  instantiate (1:= x4) in Hte.
  destruct Hte as (Heq & Hfs).
  apply Hfs; eauto.
(* R_SES_Mpax_P *)
  change (Vint32
       (set_mpax_struct x8
          (sesl_raddr
           :: sesl_sr
              :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
          (Vint32 (get_part x8 0 8)
           :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
      :: Vint32 x9
        :: v43
           :: v44
              :: v45
                 :: v46
                    :: v47
                       :: v48
                          :: v49
                             :: v50
                                :: v51 :: v52 :: v53 :: v54 :: v55 :: v56 :: nil) with (update_nth_val 0 (Vint32 x8
          :: Vint32 x9
             :: v43
                :: v44
                   :: v45
                      :: v46
                         :: v47
                            :: v48
                               :: v49
                                  :: v50
                                     :: v51
                                        :: v52
                                           :: v53 :: v54 :: v55 :: v56 :: nil) (Vint32
       (set_mpax_struct x8
          (sesl_raddr
           :: sesl_sr
              :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
          (Vint32 (get_part x8 0 8)
           :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil)))).
  eapply R_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  change (0 * 2) with 0.
  instantiate (1:= x8); eauto.
  unfold R_SES_Mpax_P; eauto.
  eapply RH_SES_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  clear -H52.
  unfold array_type_vallist_match in *.
  split.
  unfold rule_type_val_match; auto.
  destruct H52; auto.
(* R_SMS_Mpax_P *)
  change (Vint32
       (set_mpax_struct x6
          (smsl_raddr
           :: smsl_sr
              :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
          (Vint32 (get_part x6 0 8)
           :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
     :: Vint32 x7
        :: v1
         :: v2
            :: v31
               :: v32
                  :: v33
                     :: v34
                        :: v35
                           :: v36
                              :: v37 :: v38 :: v39 :: v40 :: v41 :: v42 :: nil) with (update_nth_val 0 (Vint32 x6
          :: Vint32 x7
             :: v1
         :: v2
            :: v31
               :: v32
                  :: v33
                     :: v34
                        :: v35
                           :: v36
                              :: v37 :: v38 :: v39 :: v40 :: v41 :: v42 :: nil) (Vint32
       (set_mpax_struct x6
        (smsl_raddr
         :: smsl_sr
            :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
        (Vint32 (get_part x6 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil)))).
  eapply R_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  change (0 * 2) with 0.
  instantiate (1:= x6); eauto.
  unfold R_SMS_Mpax_P; eauto.
  eapply RH_SMS_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  clear -H40.
  unfold array_type_vallist_match in *.
  split.
  unfold rule_type_val_match; auto.
  destruct H40; auto.
  change (Vint32
     (set_mpax_struct x2
        (xmc_raddr
         :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
        (Vint32 (get_part x2 0 8)
         :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
   :: Vint32 x3
      :: Vint32
           (set_mpax_struct x4
              (xmc_raddr
               :: xmc_sr
                  :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
              (Vint32 (get_part x4 0 8)
               :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil))
         :: Vint32 x5
            :: v3 :: v4 :: v5 :: v6 :: v7 :: v8
            :: v9 :: v10 :: v11 :: v12 :: v13 :: v14
            :: v15 :: v16 :: v17 :: v18 :: v19 :: v20
            :: v21 :: v22 :: v23 :: v24 :: v25 :: v26
            :: v27 :: v28 :: v29 :: v30 :: nil) with
  (update_nth_val 2 
    (update_nth_val 0 
      (Vint32 x2 
       :: Vint32 x3
          :: Vint32 x4
             :: Vint32 x5
                :: v3 :: v4 :: v5 :: v6 :: v7 :: v8
                :: v9 :: v10 :: v11 :: v12 :: v13 :: v14
                :: v15 :: v16 :: v17 :: v18 :: v19 :: v20
                :: v21 :: v22 :: v23 :: v24 :: v25 :: v26
                :: v27 :: v28 :: v29 :: v30 :: nil)
       (Vint32 (set_mpax_struct x2
              (xmc_raddr
               :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
              (Vint32 (get_part x2 0 8)
               :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil)))) 
  (Vint32 (set_mpax_struct x4
              (xmc_raddr
               :: xmc_sr
                  :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
              (Vint32 (get_part x4 0 8)
               :: V$ 1 :: V$ 1 :: V$ 1 :: V$ 0 :: V$ 0 :: V$ 0 :: nil)))).
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  change (1 * 2) with 2.
  instantiate (1:= x4); eauto.
  eapply R_XMC_Mpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  change (0 * 2) with 0.
  instantiate (1:= x2); eauto.
  unfold R_XMpax_P; eauto.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  eapply RH_XMpax_P_update_hold_comm; eauto.
  solve_part_int_rgn.
  clear -H16.
  unfold array_type_vallist_match in *.
  split.
  unfold rule_type_val_match; auto.
  destruct H16; auto.
Qed.
