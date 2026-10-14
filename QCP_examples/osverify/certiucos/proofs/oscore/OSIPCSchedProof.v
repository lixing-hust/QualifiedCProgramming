Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import oscore_common.
Require Import Lia.
Require Import List.

Open Scope code_scope.


Import DeprecatedTactic.

Ltac p_local_go:= 
  try unfold p_local;
  try unfold CurTid;
  try unfold OSLInv;
  try unfold AOSInthandler;
  try unfold AOSInthandlerParam;
  try unfold AOSExchandler;
  try unfold LINV;
  try unfold IntInv;
  try good_frm_sovler;
  try go.

Lemma OSIPCSched_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_IPCSched
                  vl logicl OS_IPCSchedPre ct->
      Some r =
      BuildRetI os_internal OS_IPCSched vl logicl OS_IPCSchedPost ct->
      exists t d1 d2 s,
        os_internal OS_IPCSched = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  pure intro.


  eapply backward_rule1.
  intros.
  sep lift 8%nat in H.

  apply disj_split in H.
  exact H.
  apply disj_rule.

  (*---ie=false---*)

  unfold isflag in H0.
  destruct H0.

  (* p_local holds 1 *)
  subst v'1.
  pure intro.



(*----------------en_crit---------------------*)


  eapply seq_rule.
  hoare lifts (1::6::5::nil)%nat pre.
  eapply encrit2_rule'.
  intros.
  sep cancel 1%nat 2%nat.
  exact H0.
  apply GoodI_I.

  p_local_go.


 (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) *)
  hoare_forward_stmts_nsepauto.

(* OSIntNesting == 0 && OSLockNesting == 0 *)
  int auto.
  int auto.
  int auto.

  instantiate (1:= Afalse).

  pure intro.

  (*
  assert(Hbt:Int.eq v'7 Int.zero = true /\ Int.eq v'8 Int.zero = true).
  unfold Int.zero.
  unfold val_inj in H.
  int auto.
  clear H H0 H1.
*)

  false.
  destruct H0.

  destruct H.
  unfold Int.zero in H.
  rewrite H.
  unfold val_inj. 
  int auto.

  unfold Int.zero in H.
  rewrite H.
  unfold val_inj. 
  int auto. 
  
  intros.
  exact H0.

(* OSIntNesting != 0 || OSLockNesting != 0 *)
  hoare forward.
  pure intro.

  eapply seq_rule.

  hoare lifts (1::3::2::nil)%nat pre.

  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  apply ret_rule'.
  intros.

  sep normal.
  unfold isflag.

  do 11 eexists.
  sep lifts (10::nil)%nat.
  apply disj_split.
  left.
  sep split in H1.
  sep auto.
  rewrite H5.
  auto.

  (* p_local holds 0 *)
  subst v'1.
  pure intro.



(*----------------en_crit---------------------*)


eapply seq_rule.
hoare lifts (1::6::5::nil)%nat pre.
eapply encrit2_rule'.
intros.
sep cancel 1%nat 2%nat.
exact H0.
apply GoodI_I.

p_local_go.


(*prove If(OSIntNesting == 0 && 
OSLockNesting == 0) *)
hoare_forward_stmts_nsepauto.

(* OSIntNesting == 0 && OSLockNesting == 0 *)

int auto.
int auto.
int auto.


instantiate (1:= Afalse).

pure intro.

false.
destruct H0.

destruct H.
unfold Int.zero in H.
rewrite H.
unfold val_inj. 
int auto.

unfold Int.zero in H.
rewrite H.
unfold val_inj. 
int auto. 

intros.
exact H0.

(* OSIntNesting != 0 || OSLockNesting != 0 *)

hoare forward.
pure intro.

eapply seq_rule.

hoare lifts (1::3::2::nil)%nat pre.

eapply excrit2_rule';eauto.
apply GoodI_I. (* GoodI *)
p_local_go.
apply ret_rule'.
intros.

sep normal.
unfold isflag.


do 11 eexists.
sep lifts (10::nil)%nat.
apply disj_split.
left.
sep split in H1.
sep auto.
rewrite H5.
auto.

  (*---ie=true---*)


  unfolds in  H0.
  destruct H0;subst.
  pure intro.

  rename H into Hv8eq0.
  rename H4 into Hv9eq0.

  (* p_local holds 1 *)

(*
  eapply seq_rule.

  hoare lifts (6::4::1::2::3::5::nil)%nat pre.
  eapply encrit1_rule'_ISnil_ISRemp.
  intros.
  sep cancel 2%nat 2%nat.
  sep cancel 3%nat 3%nat.
  sep cancel 3%nat 3%nat.

  sep auto.
  *)
  (*----------------en_crit---------------------*)
  hoare forward prim.
(*   splits; auto. *)
(*   intros; splits; auto. *)

   (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) *)

  unfold AGVars.
  sep normal.
  pure intro.



 hoare lifts (42::41::nil)%nat pre.


  hoare forward.

  (* OSIntNesting == 0 && OSLockNesting == 0 *)

  int auto.
  int auto.
  int auto.
  
  instantiate (1:= Afalse).
  pure intro.
  clear H3 H4 H5.
  rename H into Hv24.
  rename H0 into Hv21.
  rename H1 into H.
  rename H2 into H0.

  (*---------------get y------------------------*)

  hoare unfold.
  rename v'21 into vcspace.
  rename v'22 into v22. 
  rename v'23 into v23. 
  rename v'24 into v24. 

  rename v'25 into v'21. 
  rename v'26 into v'22. 
  rename v'27 into v'23. 
  rename v'28 into v'24. 
  rename v'29 into v'25. 
  rename v'30 into v'26. 
  rename v'31 into v'27. 
  rename v'32 into v'28. 
  rename v'33 into v'29. 
  rename v'34 into v'30. 
  rename v'35 into v'31. 
  rename v'36 into v'32. 



  unfold AOSUnMapTbl.
  hoare forward.

  pauto.

  lets Hx:osunmapvallist_prop H1.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.  

  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H1.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  lia.
  auto.

  rename Hv24 into H7.
  rename Hv21 into H8.
  pure intro.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'11) as X. 
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  rewrite H6.
  auto.

  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.



  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)

  hoare unfold.
  hoare forward.
  go.


  
  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  unfold AOSTCBPrioTbl.
  seplog_trm_tacs.hoare_lifts_trms_pre RH_PrioTbl_P. (* new add *)
  eapply pure_split_rule'; introv Hrh_ptbl. (* new add *)
  lets Hran:shl3_add_range H5 H13.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34. 
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H34;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.
  rewrite H35;auto.
  destruct H31;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  
  hoare forward;eauto.
  pure intro.

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  Require Import List.
  hoare lifts (1::13::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

 
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  apply absinfer_seq;auto.
  subst H38.
  go.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                        LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  
  eapply sc_isched_step with (t:=x1) (ct:=(v'37, Int.zero));eauto. 
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is; can_change_aop_solver.
  split.

  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;auto.

  instantiate (2:=  (v'37, Int.zero)). 
  instantiate (2:= (v'36
          :: v'12
             :: x8
                :: x7
                   :: Vint32 i7
                      :: Vint32 i6
                         :: Vint32 i5
                            :: Vint32 i4
                               :: Vint32 i3 :: Vint32 i2 :: Vint32 i1 :: nil):: v'10).

  instantiate (2:=v'6). 
  instantiate (2:=v'4). 
  subst H38.
  unfold p_local in H39.
  unfold CurTid in H39.
  unfold LINV in H39.
  Set Printing Depth 99.
  unfold AOSTCBList.
  sep normal in H39.
  sep destruct H39.
  sep split in H39.
  sep lift 11%nat in H39.
  apply read_only_merge_vptr in H39.
  destruct H39.
  clear H45.
  sep normal.
  sep eexists.
  sep split.
  unfold tcbdllseg.
  sep cancel 10%nat 3%nat.
  sep cancel 9%nat 2%nat.
  apply read_only_split_vptr.
  sep cancel 1%nat 1%nat.
  sep cancel abstcblist.

  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep split;eauto.
  sep cancel Astruct.
  sep cancel dllseg.
  exact H39.
  unfolds;simpl;auto.
  split;auto.
  go.
  eauto.
  eauto.
  auto.
  split;auto.
  subst H38.
  sep auto.

  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'37, Int.zero)). 
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                         LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H38).
  apply absinfer_seq;auto.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H38.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.

  apply backward_rule1 with ( <|| sched;; v'0 ||>  ** 
                                  ( LV y @ Int8u |-> Vint32 x **  A_dom_lenv ((y, Int8u) :: nil)) ** H38).
  intros.
  sep normal.
  auto.
  subst H38.

  eapply frame_rule' with (frm:=  LV y @ Int8u |-> Vint32 x ** 
                                     A_dom_lenv ((y, Int8u) :: nil) ).

  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.


  intros;sep auto.


  (* hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::nil) pre. *)

  eapply switch_rule'.

 (*
  instantiate (1:= LINV OSLInv (v'37, Int.zero) (logic_val (V$ 1) :: v'2)).
*) 

  instantiate (1:= GV OSLockNesting @ long |-> Vint32 v'9 **
  GV OSIntNesting @ long |-> Vint32 v'8 ** LINV OSLInv (v'37, Int.zero) (logic_val (V$ 1) :: v'2)).




  Set Printing Depth 999.

  intros.
  unfold p_local in H38.
  sep cancel OSLInv.

  (* sep remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::nil) in H38. *)
  sep cancel 12%nat 2%nat. 
  sep cancel 12%nat 2%nat. 


  exact H38.

  intros.



  unfold SWINVt.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.




  unfold OSInv.
  unfold AGVars.


  unfold AOSTCBPrioTbl.


  sep semiauto; eauto.
  sep cancel EvtInv. (* new add *)
  sep cancel 1%nat 1%nat.

  sep cancel 6%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  left.
  sep normal.
  sep eexists.
  unfold AOSTCBFreeList'.
  sep lift 12%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  unfold AOSTCBFreeList in H38.
  sep normal.
  sep cancel tcbdllflag.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.

  sep auto;eauto.

    
  split;auto.
  go.
  intro.
  subst.

  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.


  instantiate (1:= v'3). auto.
  destruct_s s.
  simpl in H42;subst i11.
  simpl.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.

  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  
  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H37.
  rewrite H37 in *.

  exists x1.

  sep lift 2%nat.
  apply imp_isrclr.

  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'4 (Vptr (v'37, Int.zero)) v'6 (  (v'36
            :: v'12
               :: x8
                  :: x7
                     :: Vint32 i7
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i2
                                       :: 
                                       Vint32 i1 :: nil) :: v'10) v'11 (v'37, Int.zero) v'14 ** H39).

  unfold AOSTCBList.
  sep normal.
  clear HeqH39.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.

  split;auto.
  go.
  clear H38.
  subst H39.
  
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.

  seplog_trm_tacs.sep_lifts_trms_in H40 (AOSTCBList, abstcblist, CurTid).

  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  unfold LINV.
  exists v'14. 
  sep auto.
  unfolds in H0.
  unfold indom.
  mytac;eauto.
  
  simpl;auto.
  pauto. (* new add *)
  intros.
  sep cancel 3%nat 1%nat.
  simpl;auto.
  
  apply disj_rule.
  pure intro.
  
  apply backward_rule1 with (<|| v'0 ||>  ** OSInv  ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier v'3 ** GV OSLockNesting @ long |-> Vint32 v'9 ** GV OSIntNesting @ long |-> Vint32 v'8 ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'37, Int.zero) **  LINV OSLInv (v'37, Int.zero) (logic_val (V$ 1) :: v'2)).
  intros.
  unfold SWINVt in H33.
  unfold SWINV in H33.
  sep normal in H33.
  sep destruct H33.

  sep lifts (2::9::nil)%nat in H33.  
  lets Hi:topis_nil H33.
  subst x1.
  sep lifts (8::4::nil)%nat in H33.
  apply isrclr_imp  in H33.
  apply simpl_inv_encrit in H33.

  clear -H33.

  sep lifts (4::7::2::3::10::5::11::1::nil)%nat in H33.  

  apply atopis_pure in H33.

  sep lifts (2::8::nil)%nat in H33.
  
  apply ostcbcur_tp_os_tcb in H33.
  sep pauto.
  seplog_trm_tacs.sep_lifts_trms_in H33 (Aisr , Ais, aemp_isr_is).
  eapply elim_aemp_isr_is_prop in H33.
  sep cancel Aier.
  sep auto.
  eapply backward_rule1.
  introv Hsat.
  seplog_trm_tacs.sep_lifts_trms_in Hsat (Aisr , Ais, Aier).
  eapply add_aemp_isr_is_prop in Hsat. eauto. 

  seplog_trm_tacs.hoare_lifts_trms_pre(Aop, Aisr, Aier, Aie, Ais, Acs, OSInv, aemp_isr_is).

  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp; eauto.

  unfold LINV.
  unfold OSLInv.
  go.
  intros. 
  unfold p_local. unfold CurTid.
  sep auto.

  hoare forward.
  eapply disj_split.
  right.

  sep split.

  unfold p_local.
  unfold CurTid.
  sep auto.
  auto.
  splits; auto.
  auto.
  unfold isflag; auto.


  rewrite H35.
  rewrite H37.
  rewrite H38.
  rewrite H39.
  
  auto.


  (* ----exit crit ----*)

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  hoare lifts (2::11::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  unfold isched.
  (*
  instantiate (1:= <|| (ASSUME nsc ?? END None) ;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).
  apply absinfer_seq;auto.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  apply absinfer_choice2;auto.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
*)
 
 instantiate (1:= <|| ASSUME nsc;;v'0 ||>  **
                      LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).
 apply absinfer_seq;auto.
 subst H36;can_change_aop_solver.
 unfold aemp_isr_is. can_change_aop_solver.
 subst H36;can_change_aop_solver.
 unfold aemp_isr_is. can_change_aop_solver.
 apply absinfer_choice2;auto.
 subst H36;can_change_aop_solver.
 unfold aemp_isr_is. can_change_aop_solver.
 subst H36;can_change_aop_solver.
 unfold aemp_isr_is. can_change_aop_solver.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| spec_done None;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'37, Int.zero));eauto.
  subst H36.
  can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.

  instantiate (2:=  (v'37, Int.zero)). 
  instantiate (2:= (v'36
          :: v'12
             :: x8
                :: x7
                   :: Vint32 i7
                      :: Vint32 i6
                         :: Vint32 i5
                            :: Vint32 i4
                               :: Vint32 i3
                                  :: Vint32 i2
                                     :: Vint32 i1 :: nil) :: v'10).

  instantiate (2:=v'6). 
  instantiate (2:=v'4). 
  subst H36.
  unfold p_local in H37.

  unfold CurTid in H37.
  sep normal in H37.
  sep normal.
  sep destruct H37.
  exists x2.
  sep cancel 1%nat 1%nat.
  sep cancel abstcblist.

  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  subst H36.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'37, Int.zero)).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <||v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.
  subst H36;can_change_aop_solver.
  unfold aemp_isr_is. can_change_aop_solver.

  apply backward_rule1 with ( <|| v'0 ||>  ** OSInv (* ** atoy_inv' *) ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** Aier v'3 ** GV OSIntNesting @ long |-> Vint32 v'8 ** GV OSLockNesting @ long |-> Vint32 v'9 ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) **  p_local OSLInv (v'37, Int.zero) (logic_val (V$ 1) :: v'2) ).
  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
   assert(s|=AOSTCBList v'4 (Vptr (v'37, Int.zero)) v'6 (  (v'36
            :: v'12
               :: x8
                  :: x7
                     :: Vint32 i7
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i2
                                       :: Vint32 i1 :: nil) :: v'10) v'11 (v'37, Int.zero) v'14 ** H36).

  unfold AOSTCBList.
  sep normal.
  clear HeqH36.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.

  clear H37.
  subst H36.
  sep lifts (2::12::nil)%nat.
  apply inv_change.
  unfold OldOSInvWL.
  seplog_trm_tacs.sep_lifts_trms_in H38 (Aisr , Ais, aemp_isr_is).
  eapply elim_aemp_isr_is_prop in H38.

  sep normal.
  do 20 eexists.

  sep cancel 10%nat 31%nat. 
  sep cancel 10%nat 30%nat. 


  sep semiauto;eauto.
  sep cancel EvtInv. (* new add *)
  sep cancel 2%nat 1 %nat.

  sep cancel AOSTCBList.
  sep pauto. 

  simpl;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.


  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.



  eapply backward_rule1.
  introv Hsat.
  seplog_trm_tacs.sep_lifts_trms_in Hsat (Aisr , Ais, Aier).
  eapply add_aemp_isr_is_prop in Hsat. eauto. 

  seplog_trm_tacs.hoare_lifts_trms_pre(Aop, Aisr, Aier, Aie, Ais, Acs, OSInv, aemp_isr_is).
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp; eauto.

  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.

  intros;sep auto.
  hoare forward.

  eapply disj_split.
  right.

  sep split.

  unfold p_local.
  unfold CurTid.
  sep auto.
  auto.
  splits; auto.


  auto.
  unfold isflag; auto.
  rewrite H39.
  rewrite H41.
  rewrite H42.
  rewrite H43. 

  auto.



(* OSIntNesting != 0 || OSLockNesting != 0 *)
  hoare forward.
  pure intro.

  assert(val_inj
  (bool_and
     (val_inj
        (if Int.eq v'8 ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)))
     (val_inj
        (if Int.eq v'9 ($ 0)
         then Some (Vint32 Int.one)
         else Some (Vint32 Int.zero)))) = Vint32 Int.one).
  unfold val_inj.
  int auto.
  rewrite H4 in H3.
  false.
  destruct H3.
  invert H3.
  invert H3.



  (*****p_local holds 0 ****** self deleted case ******)

  (*----------------en_crit---------------------*)

  pure intro.
  
  hoare forward prim.
(*   splits; eauto. *)
(*   intros; splits; auto. *)



  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) *)
  hoare unfold.
  rename v'22 into vcspace.
  rename v'23 into v23. 
  rename v'24 into v24. 
  rename v'25 into v25. 


  unfold AGVars.
  sep normal.
  pure intro.



 hoare lifts (40::39::nil)%nat pre.



  rename H into Hv8eq0.
  rename H4 into Hv9eq0.
(*
  hoare unfold.
  unfold AGVars.  *)
  hoare forward.



(* OSIntNesting == 0 && OSLockNesting == 0 *)

  int auto.
  int auto.
  int auto.
  
  instantiate (1:= Afalse).
  
  pure intro.

  clear H H3 H4.


  rename H1 into Hv25.
  rename H2 into Hv22.
  rename H0 into H.
  
  (*---------------get y------------------------*)

  hoare unfold.
  unfold AOSTCBList'.
  hoare lift 18%nat pre. 
  eapply backward_rule1.
  intros.

  apply disj_split in H3.
  eauto.
  apply disj_rule.
  unfold p_local.
  unfold CurTid.
  pure intro.
  eapply backward_rule1.
  intros.
  sep lifts (4::1::nil)%nat in H8.
  apply read_only_merge_vptr in H8.
  destruct H8 as (H8 & Hp).
  eapply astar_l_apure_intro in Hp ;eauto.

  hoare_split_pure_all.
  subst v'16.
  unfold tcbdllseg.
  unfold tcbdllflag.

  seplog_trm_tacs.hoare_lifts_trms_pre ((dllseg v'4), (dllseg (Vptr ct)), dllsegflag, OSLInv).

  eapply backward_rule1.
  intros.
  eapply task_del_noexists in H8.
  exact H8.
  apply pfalse_rule.
  (*************)
  hoare unfold.
  unfold AOSUnMapTbl.
  hoare forward.
  pauto.
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.

  rename H8 into H10.
  rename H7 into H9.
  rename Hv25 into H7.
  rename Hv22 into H8.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'11) as X.
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  
  rewrite H6.
  auto.
  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.

  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)
  unfold AOSTCBFreeList'.
  hoare normal pre.
  hoare lift 27%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H11.
  destruct H11.
  unfold TCBFree_Not_Eq in H11.
  sep split in H11;tryfalse.
  eauto.
  unfold TCBFree_Eq.
  unfold p_local.
  unfold CurTid.
  hoare unfold.
  eapply backward_rule1.
  intros.
  seplog_trm_tacs.sep_lifts_trms_in H14 (Vptr v'16 ).


  Set Printing Depth 999.
  apply read_only_merge_vptr in H14.
  destruct H14 as (H14 & Hp).
  eapply astar_l_apure_intro in Hp ;eauto.

  hoare_split_pure_all.
  subst v'16.
  
  hoare forward.
  go.
  unfold p_local.
  unfold CurTid.
  sep normal.
  sep eexists.
  sep cancel LINV.
  sep lift 2%nat in H14.
  apply read_only_split_vptr in H14.
  sep cancel 1%nat 1%nat.
  simpl;auto.

  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H14.
  unfold AOSTCBPrioTbl.
  seplog_trm_tacs.hoare_lifts_trms_pre RH_PrioTbl_P. (* new add *)
  eapply pure_split_rule'; introv Hrh_ptbl. (* new add *)
  lets Hran:shl3_add_range H5 H17.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H30.  
  rewrite H30;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H30;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H31.  
  rewrite H31;auto.
  destruct H27.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H31.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H32.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 4%nat 1%nat.
  simpl;auto.
  hoare forward;eauto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 5%nat 1%nat.
  simpl;auto.
  instantiate (1:=Afalse).
  pure intro.
  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H14;auto.
  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx1).
  split;lia.
  destruct Hhastid.
  seplog_trm_tacs.hoare_lifts_trms_pre (Aop, Alvarmapsto y, A_dom_lenv).

  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  apply absinfer_seq;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  go.
(*   unfold aemp_isr_is. go. *)
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  apply absinfer_choice1;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  split.

  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H33;auto.

  subst H34.
  sep cancel tcblist.
  sep cancel abstcblist.
(*   sep cancel 31%nat 1%nat. *)
  sep cancel  7%nat 1%nat.
  exact H35.
  subst H34.
  sep auto.

  seplog_trm_tacs.sep_lifts_trms_in H35 (tcblist, TCB_Not_In, abstcblist, OSTCBCur).
(*   sep lifts (15::16::31::7::nil)%nat in H35. *)
  eapply  highest_ct_dead_neq in H35;eauto.
  rewrite Int.repr_unsigned in H33;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H34).
  apply absinfer_seq;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  apply absinfer_seq_end;auto.
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  subst H34.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
(*   unfold aemp_isr_is. go. *)
  
  apply backward_rule1 with ( <|| sched;; v'0 ||>  **
                                  (LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil)) ** H34).
  intros.
  sep normal.
  auto.
  subst H34.

  eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0) :: v'2) ** LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** GV OSIntNesting @ long |-> Vint32 v'8 **
  GV OSLockNesting @ long |-> Vint32 v'9 ).
  unfold LINV,OSLInv.
  simpl;auto.
  pauto. (* new add *)
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.

  sep cancel 21%nat 2%nat. 
  sep cancel 20%nat 2%nat. 
(*
    sep remember (1::2::3::4::5::6::7::8::9::10::11::12::13::14::15::nil) in H34.
*)

  exact H34.
  
  intros.
  unfold SWINVt.
  
  sep normal.
  exists OS_TCB.
  sep cancel 6%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.

  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  
  sep semiauto;eauto.
  sep cancel EvtInv.
  sep cancel 2%nat 1%nat.

  sep cancel OSPlaceHolder.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
(*   sep cancel 10%nat 1%nat. *)
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'12.
  sep cancel TCB_Not_In.
  unfold AOSTCBFreeList'.
  sep lift 8%nat.
  apply disj_split.
  right.
  unfold TCBFree_Eq.
  sep auto.
  go.
  eexists;split.
  unfolds;simpl;auto.
  auto.
  simpl;auto.
  rewrite Int.repr_unsigned in H33;eauto.
  instantiate (1:= v'3). eauto.
  destruct_s s.
  simpl;simpl in H38;subst;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H33.
  rewrite H33 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  sep auto.
  auto.

  exists v'14.

  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
(*   sep cancel 14%nat 1%nat. *)
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.

  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H29.
  remember (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0) as X.
  destruct X.
  simpl in H29.

  assert (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0 =false).
  eapply dead_not_ready;eauto.
  eapply prio_not_in_tcbls_nready;eauto.
  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H;inverts H.
  auto.
  rewrite H31 in HeqX0;tryfalse.
  simpl in H30.
  clear -H29;int auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0);simpl in H29;tryfalse. 

(* OSIntNesting != 0 || OSLockNesting != 0 *)
hoare forward.
pure intro.


assert(val_inj
(bool_and
   (val_inj
      (if Int.eq v'8 ($ 0)
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))
   (val_inj
      (if Int.eq v'9 ($ 0)
       then Some (Vint32 Int.one)
       else Some (Vint32 Int.zero)))) = Vint32 Int.one).
unfold val_inj.
int auto.


rewrite H3 in H.
false.
destruct H.
invert H.
invert H.

Qed.