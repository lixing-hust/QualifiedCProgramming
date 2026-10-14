Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Require Import oscore_common. 
Require Import OSIntExitIntPure.
Import DeprecatedTactic.
Require Import Lia.
Open Scope code_scope.

Open Scope list_scope.
Open Scope Z_scope.
Lemma OSIntExitInt_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSIntExit
                  vl logicl OSIntExitIntPre ct->
      Some r =
      BuildRetI os_internal OSIntExit vl logicl OSIntExitIntPost ct->
      exists t d1 d2 s,
        os_internal OSIntExit = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  pure intro. 
  rename H1 into Hirange.
  eapply backward_rule1.
  intros.
  sep lift 7%nat in H.
  (*split 2 cases: interrupt is allowed, or not allowed.*)
  apply disj_split in H.
  exact H.
  apply disj_rule.
  unfold IntInv.
  pure intro.
  (*The value of flag.*)
  unfolds in Hirange.
  (*split to 2 cases: p_local OSLInv ct (logic_val (V$ 0) :: nil) and p_local OSLInv ct (logic_val (V$ 1) :: nil)*)
  destruct Hirange;subst v'5.
  (*till now, there are three cases. *)
  (*split in 2 case: i = 1 or i <> 1*)
  eapply backward_rule1.
  intros.
  sep lift 26%nat in H1.
  apply disj_split in H1.
  exact H1.
  apply disj_rule.
  eapply backward_rule1.
  intros.
  
  sep lifts (13::14::32::nil)%nat in H1.
  apply inv_change_aux in H1. 
  exact H1.
  (*local_val = 1 && i == 1*)
  unfold AGVars.
  hoare forward.
  instantiate (1:= Afalse). (*not for sequential composition, so Afalse is enough.*)
  pure intro.
  rename H1 into Hm. rename H2 into Hn.
  (*These three facts are true, and not needed for future proof*)
  clear H4 H5 H6. 
  eapply seq_rule.
  (*prove ENTER_CRITICAL*)
  hoare lifts (44::40::17::41::42::43::nil)%nat pre.
  eapply encrit2_rule'.
  intros.
  exact H1.
  apply GoodI_I.  (* GoodI *)
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
  p_local_go.

  (*prove If OSIntNesting*)
  hoare forward.
  destruct (Int.ltu (Int.repr 0) v'43); auto.
  (*prove --OSIntNesting*)
  pure intro.
  clear H1 H2 H3. 
  hoare forward.
  apply disj_rule.
  pure intro.
  clear H1 H2 H3.

  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8 :: logic_val v'9 :: logic_val v'10 :: nil)).
  intros.
  sep lifts (3::4::5::6::7::45::nil)%nat in H1.
  sep lift 2%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H1.
  unfold Int.zero in H1.
  remember (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero in H1. unfold Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H1. rewrite H0 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. tryfalse.
  unfold is_length in H1.
  destruct v'3; simpl in H1; tryfalse.
  auto.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. unfold Int.zero in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.

  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H4.
  hoare unfold.
  rename H2 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H6;omega.*)
  rename H3 into Hm. rename H4 into Hn.

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  Optimize Proof.
  Optimize Heap.
  auto.
  rename Hm into H5. rename Hn into H6.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H7.
  rewrite H8.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H9.
  unfold OS_RDY_TBL_SIZE in H8.
  eapply GAarray_imp_length_P in H9.
  rewrite H9.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H11;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H11.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  Ltac can_change_aop_solver :=
    (*try unfold AIntNumCurrent;*)
    try unfold AOSInthandler;
    try unfold AOSInthandlerParam;
    try unfold AOSExchandler;
    try unfold tcblist;
    try unfold LINV;
    try unfold OSLInv;
    go.
  can_change_aop_solver.
  can_change_aop_solver.

  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x0) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H33.  
  rewrite H33;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H33;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x0) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.
  rewrite H34;auto.
  destruct H29;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H34.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H35.
  eapply int_unsigned_le_z2nat_lt.
  auto.

  hoare forward;eauto.
  pure intro.
  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H10;auto.

  lets Hhastid:prio_in_rtbl_has_tid H29 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  lia.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  can_change_aop_solver.
  2:apply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  can_change_aop_solver.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H36;eauto.
  instantiate (2:=  (v'47 ↝ {Int.zero})).
  instantiate (3:= ((v'46
  :: v'3
     :: x8
        :: x7
           :: Vint32 i7
              :: Vint32 i6
                 :: Vint32 i5
                    :: Vint32 i4
                       :: Vint32 i3
                          :: 
                          Vint32 i2
                          :: 
                          Vint32 i1 :: nil):: v'16) %list).
  instantiate (3:=v'14).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H37.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  sep lifts (7::1::nil)%nat%list in H37.
  apply read_only_merge_vptr in H37.
  destruct H37.
  clear H38.
  apply read_only_split_vptr in H37.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H36;eauto.
  clear -H32.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H32;auto.
  unfold Int.notbool in H32.
  int auto.
  instantiate (2:=(v'47 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  hoare remember (1::2::19::nil)%nat%list pre.

  apply backward_rule1 with (<|| sched;; END None ||>  **
  (A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) )**  H37).
  intros.
  sep normal.
  auto.
  subst H37.
  eapply frame_rule' with (frm:=
  A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil)).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=LINV OSLInv (v'47 ↝ {Int.zero})
  (logic_val (V$ 1)
   :: logic_val v'7
      :: logic_val v'8
         :: logic_val v'9
            :: logic_val v'10
               :: nil)).
  intros.
  sep cancel LINV.
  exact H37.
  intros.
  unfold SWINVt.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists 1%nat.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.

  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  eapply A_isr_is_prop_elim.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  unfold IntInv.
  sep split in H37.
  sep semiauto; eauto.
  sep cancel 1%nat 1%nat.
(*sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.*)
  sep cancel 8%nat 1%nat.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
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
  unfold AOSTCBFreeList in H37.
  sep normal.
  sep cancel tcbdllflag.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel assertion.sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  unfold IntInv.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H37.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H37.
  eapply Astruct_sll_OS_TCB_dup_false; eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H36.
  eauto.
  
  destruct_s s.
  simpl in H42;subst i11.
  simpl.
  auto.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H16.
  clear -H16;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  simpl in H42,H39.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.

  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H36.
  rewrite H36 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s|=AOSTCBList v'12 (Vptr (v'47 ↝ {Int.zero})) v'14 ((
                v'46
                :: v'3
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'47 ↝ {Int.zero}) v'20 ** H38).
  unfold AOSTCBList.
  sep normal.
  clear HeqH38.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  split;auto.
  go.
  clear H37.
  subst H38.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep lifts (1::37::21::nil)%nat in H39.
  unfold CurTid in H39.
  eapply highest_rdy_eq in H39;eauto.
  clear -Hran.
  remember ( Int.add (Int.shl x (Int.repr 3)) x0 ) as X.
  clear HeqX.
  int auto.
  exists v'20.
  sep auto.
  clear -H14 H16.
  simpl in H16.
  mytac.
  inverts H.
  assert (join (sig (v'47 ↝ {Int.zero}) x2) x1 v'45).
  auto.
  clear H1.
  clear -H H14.
  assert (get (sig (v'47 ↝ {Int.zero}) x2) (v'47 ↝ {Int.zero}) = Some x2).
  apply map_get_sig.
  eapply join_get_l in H;eauto.
  eapply join_get_r in H14;eauto.
  unfolds;eauto.
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat. 
  simpl; auto.
  intros.
  exact H18.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
    A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
    Aisr (isrupd v'0 1%nat false) **
    Aie false **
    Ais (1%nat :: nil) **
    Acs (false :: nil) ** 
    Aier (ierupd v'1 1%nat false) ** 
    LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** p_local OSLInv (v'47 ↝ {Int.zero}) (logic_val (V$ 1) :: logic_val v'7
    :: logic_val v'8
       :: logic_val v'9 :: logic_val v'10 ::nil))).
  intros.
  ssplit_apure_in H18.

  unfold SWINVt in H18.
  unfold SWINV in H18.  
  sep normal in H18.
  sep destruct H18.
  sep lifts (2::3::9::7::nil)%nat in H18.
  apply invlth_isr_invlth_isr'_imp in H18.
  unfold aemp_isr_is in H18.
  sep normal in H18.
  eapply A_isr_is_prop_elim'''' in H18.
  sep cancel 1%nat 9%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  rewrite Hempisr; auto.

  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20 ::nil)%nat pre.
  hoare lifts (28::30::21::26::25::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.  
  apply elim_a_isr_is_prop' in H29.
  exact H29.
  rewrite Hempisr.
  unfolds;simpl;auto.
  hoare lifts (3::1::31::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  (*unfold AOSRunning.*)
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'58 = (v'47 ↝ {Int.zero})).
  sep lifts (33::11::nil)%nat in H29.
  eapply p_local_ostcblist_eq_ct in H29.
  auto.
  subst v'58.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  sep normal.
  sep split.
  apply disj_split.
  left. 
  sep split.
 
  sep cancel 32%nat 3%nat.
  apply disj_split.
  left.
  unfold AOSTCBPrioTbl in H29.
  unfold AGVars in H29.
  sep lift 19%nat in H29.
  sep normal in H29.
  sep destruct H29.
  sep normal.
  sep eexists.

  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  sep split in H29; eauto. auto.
  sep split in H29. auto.
  sep split in H29. auto.
  sep split in H29. auto.
  sep split in H29. apply H34.
  sep split in H29. apply H33.
  sep split in H29. apply H31.
  unfold isflag. auto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.

  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H10;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H29 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  split; lia.
  destruct Hhastid.
  hoare lifts (2::17::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.

  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35;p_local_go.
  subst H35;p_local_go.

  apply absinfer_choice2;auto.
  subst H35;p_local_go.
  subst H35;p_local_go.

  eapply abscsq_rule'.
  apply noabs_oslinv.

  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'47 ↝ {Int.zero}));eauto.
  subst H35; p_local_go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  instantiate (2:=  (v'47 ↝ {Int.zero})).
  instantiate(2:= (v'46
  :: v'3
   :: x8
      :: x7
         :: Vint32 i7
            :: Vint32 i6
               :: Vint32 i5
                  :: Vint32 i4
                     :: Vint32 i3
                        :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16).
   instantiate (2:=v'14).
   instantiate (2:=v'12).
   subst H35.
   unfold p_local in H36.
   unfold CurTid in H36.
   sep normal in H36.
   sep destruct H36.
   unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList. 
  sep cancel 39%nat 9%nat.
  sep split;eauto.
  split;auto.
  go.
  subst H35.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H34;eauto.
  clear -H32.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H32;destruct H32;auto;tryfalse.
  instantiate (2:=(v'47 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq_end;auto.
  subst H35; p_local_go.
  subst H35; p_local_go.
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** Aie false ** Ais (1%nat::nil) ** Acs (false::nil) ** Aisr empisr ** Aier (ierupd v'1 1%nat false) **   LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** (
                                  p_local OSLInv (v'47 ↝ {Int.zero}) (logic_val (V$ 1) :: logic_val v'7
                                  :: logic_val v'8
                                     :: logic_val v'9
                                        :: logic_val v'10 ::nil) )).

  intros.
  subst H35.
  sep remember (6::7::8::9::10::nil)%nat in H36.
  assert(s|=AOSTCBList v'12 (Vptr (v'47 ↝ {Int.zero})) v'14 ((
   v'46
   :: v'3
    :: x8
       :: x7
          :: Vint32 i7
             :: Vint32 i6
                :: Vint32 i5
                   :: Vint32 i4
                      :: Vint32 i3
                         :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'47 ↝ {Int.zero}) v'20 ** H35).
  unfold AOSTCBList.
  sep normal.
  clear HeqH35.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H36.
  subst H35.
  unfold OSInv.
  unfold IntInv.
  unfold A_isr_is_prop.
  sep lifts (1::23::24::25::nil)%nat in H37.
  rewrite <- inv_change_aux in H37.
  sep semiauto;eauto.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep lifts (3::4::1::2::nil)%nat in H37.
  exact H37.
  simpl;auto.
  rewrite <- Hempisr. auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  simpl in H16.
  clear -H16;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  rewrite H38, H41.
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (30::28::21::24::26::27::29::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply elim_a_isr_is_prop' in H35.
  exact H35.
  unfolds;simpl;auto.
  hoare lifts (4::1::30::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'58 = (v'47 ↝ {Int.zero})).
  sep lifts (33::18::nil)%nat in H35.
  eapply p_local_ostcblist_eq_ct in H35.
  auto.
  subst v'58.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep auto;eauto.
  sep split in H35. eauto. eauto.
  sep split in H35. eauto. 
  sep split in H35. eauto.
  sep split in H35. eauto. 
  sep split in H35. apply H41.
  sep split in H35. eauto.
  sep split in H35. rewrite <- Hempisr in H38. apply H38.
  unfolds; auto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.
  intros.
  exact H1.
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal.
  sep split.
  apply disj_split.
  left.
  sep lifts (21::22::23::24::nil)%nat in H2.
  eapply inv_change_aux in H2.
  sep normal.
  sep eexists.
  

  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  sep split in H2; eauto.
  auto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  
  unfolds; auto.
  auto.
  auto.
  (*second checkis*)
  eapply seq_rule.
  hoare lifts (1::3::2::nil)%nat pre.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil)).
  intros.
  sep lifts (1::2::3::4::5::44::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'42 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq v'43
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H2.
  unfold Int.zero in H2.
  remember (Int.eq v'43 (Int.repr 0)) as X.
  remember (Int.eq v'44 (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero in H2. unfold Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H2. rewrite H0 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. tryfalse.
  unfold is_length in H2.
  destruct v'3; simpl in H2; tryfalse.
  auto.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. unfold Int.zero in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H5. 
  hoare unfold.
  rename H2 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H7;omega.*)
  rename H3 into Hm. rename H5 into Hn.

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H6. rename Hn into H7.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  Optimize Proof.
  Optimize Heap.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H12;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H12.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.

  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x0) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.  
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H34;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x0) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.
  rewrite H35;auto.
  destruct H30;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.

  hoare forward;eauto.
  pure intro.
  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H11;auto.

  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  lia.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  can_change_aop_solver.
  2:apply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  can_change_aop_solver.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  instantiate (2:=  (v'47↝ {Int.zero})).
  instantiate (3:= ((v'46
  :: v'3
     :: x8
        :: x7
           :: Vint32 i7
              :: Vint32 i6
                 :: Vint32 i5
                    :: Vint32 i4
                       :: Vint32 i3
                          :: 
                          Vint32 i2
                          :: 
                          Vint32 i1 :: nil):: v'16) %list).
  instantiate (3:=v'14).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H38.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep lifts (7::1::nil)%nat%list in H38.
  apply read_only_merge_vptr in H38.
  destruct H38.
  clear H39.
  apply read_only_split_vptr in H38.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'47 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  hoare remember (1::2::19::nil)%nat%list pre.

  apply backward_rule1 with (<|| sched;; END None ||>  **
  (A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) )**  H38).
  intros.
  sep normal.
  auto.
  Optimize Proof.
  Optimize Heap.
  subst H38.
  eapply frame_rule' with (frm:=
  A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil)).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=(LINV OSLInv (v'47, Int.zero)(logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil))).
  intros.
  sep cancel LINV.
  exact H38.
  intros.
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
  exists 1%nat.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.

  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  eapply A_isr_is_prop_elim.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  unfold IntInv.
  sep semiauto; eauto.
  sep cancel APthreadAttr.
  sep cancel 1%nat 1%nat.
  sep cancel 8%nat 1%nat.
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
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel assertion.sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false; eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.
  
  destruct_s s.
  simpl in H43;subst i11.
  simpl.
  auto.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  simpl in H43,H40.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.

  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H37.
  rewrite H37 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'12 (Vptr (v'47 ↝ {Int.zero})) v'14 ((
                v'46
                :: v'3
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'47 ↝ {Int.zero}) v'20 ** H39).
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
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep lifts (1::37::21::nil)%nat in H40.
  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  clear -Hran.
  remember ( Int.add (Int.shl x (Int.repr 3)) x0 ) as X.
  clear HeqX.
  int auto.

  exists v'20.
  sep auto.
  clear -H15 H17.
  simpl in H17.
  mytac.
  inverts H.
  assert (join (sig (v'47 ↝ {Int.zero}) x2) x1 v'45).
  auto.
  clear H1.
  clear -H H15.
  assert (get (sig (v'47 ↝ {Int.zero}) x2) (v'47 ↝ {Int.zero}) = Some x2).
  apply map_get_sig.
  eapply join_get_l in H;eauto.
  eapply join_get_r in H15;eauto.
  unfolds;eauto.
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat. 
  simpl; auto.
  intros.
  exact H19.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
    A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
    Aisr (isrupd v'0 1%nat false) **
    Aie false **
    Ais (1%nat :: nil) **
    Acs (false :: nil) **
    Aier (ierupd v'1 1%nat false) ** 
    LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** p_local OSLInv (v'47 ↝ {Int.zero}) (logic_val (V$ 1)
    :: logic_val v'7
       :: logic_val v'8
          :: logic_val v'9
             :: logic_val v'10 :: nil))).
  intros.
  ssplit_apure_in H19.

  unfold SWINVt in H19.
  unfold SWINV in H19.  
  sep normal in H19.
  sep destruct H19.
  sep lifts (2::3::9::7::nil)%nat in H19.
  apply invlth_isr_invlth_isr'_imp in H19.
  unfold aemp_isr_is in H19.
  sep normal in H19.
  eapply A_isr_is_prop_elim'''' in H19.
  sep cancel 1%nat 9%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  rewrite Hempisr; auto.

  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  (* 1.22 *)
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (28::30::25::26::27::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.  
  sep lifts (1::2::21::nil)%nat in H30.
  apply elim_a_isr_is_prop' in H30.
  exact H30.
  rewrite Hempisr.
  unfolds;simpl;auto.
  hoare lifts (4::1::31::6::2::7::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'58 = (v'47 ↝ {Int.zero})).
  sep lifts (33::12::nil)%nat in H30.
  eapply p_local_ostcblist_eq_ct in H30.
  auto.
  subst v'58.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  sep normal.
  sep split.
  sep cancel 33%nat 3%nat.
  apply disj_split.
  left.  
  sep normal. sep split.
  apply disj_split.
  left.
  unfold AOSTCBPrioTbl in H30.
  unfold AGVars in H30.
  sep normal in H30.
  sep destruct H30.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  sep split in H30. eauto.
  eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  unfolds; eauto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.

  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H11;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  split; lia.
  destruct Hhastid.
  hoare lifts (2::17::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.

  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq;auto.
  subst H36;p_local_go.
  subst H36;p_local_go.

  apply absinfer_choice2;auto.
  subst H36;p_local_go.
  subst H36;p_local_go.

  eapply abscsq_rule'.
  apply noabs_oslinv.

  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'47 ↝ {Int.zero}));eauto.
  subst H36; p_local_go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.
  instantiate (2:=  (v'47 ↝ {Int.zero})).
  instantiate(2:= (v'46
  :: v'3
   :: x8
      :: x7
         :: Vint32 i7
            :: Vint32 i6
               :: Vint32 i5
                  :: Vint32 i4
                     :: Vint32 i3
                        :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16).
   instantiate (2:=v'14).
   instantiate (2:=v'12).
   subst H36.
   unfold p_local in H37.
   unfold CurTid in H37.
   sep normal in H37.
   sep destruct H37.
   unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList. 
  sep cancel 39%nat 9%nat.
  sep split;eauto.
  split;auto.
  go.
  subst H36.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'47 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  subst H36; p_local_go.
  subst H36; p_local_go.
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** Aie false ** Ais (1%nat::nil) ** Acs (false::nil) ** Aisr empisr ** Aier (ierupd v'1 1%nat false) **   LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** p_local OSLInv (v'47 ↝ {Int.zero}) (logic_val (V$ 1)
                                  :: logic_val v'7
                                     :: logic_val v'8
                                        :: logic_val v'9
                                           :: logic_val v'10 :: nil)).

  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s|=AOSTCBList v'12 (Vptr (v'47 ↝ {Int.zero})) v'14 ((
   v'46
   :: v'3
    :: x8
       :: x7
          :: Vint32 i7
             :: Vint32 i6
                :: Vint32 i5
                   :: Vint32 i4
                      :: Vint32 i3
                         :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'47 ↝ {Int.zero}) v'20 ** H36).
  unfold AOSTCBList.
  sep normal.
  clear HeqH36.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  split;auto.
  go.
  clear H37.
  subst H36.
  unfold OSInv.
  unfold IntInv.
  unfold A_isr_is_prop.
  sep lifts (1::23::24::25::nil)%nat in H38.
  rewrite <- inv_change_aux in H38.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 3%nat 1 %nat.
  sep cancel 3%nat 1 %nat.
  exact H38.
  simpl;auto.
  rewrite <- Hempisr. auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  rewrite H39, H42.
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (30::28::25::26::27::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.
  sep lifts (1::2::21::nil)%nat in H36.
  apply elim_a_isr_is_prop' in H36.
  exact H36.
  unfolds;simpl;auto.
  hoare lifts (4::1::7::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'58 = (v'47 ↝ {Int.zero})).
  sep lifts (33::11::nil)%nat in H36.
  eapply p_local_ostcblist_eq_ct in H36.
  auto.
  subst v'58.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal.
  
  sep semiauto;eauto.
  sep cancel p_local.
  left.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36. rewrite <- Hempisr in H39. eauto.
  unfolds; auto.
  rewrite Hempisr;unfolds;simpl;auto.
  sep split in H36;auto.
  intros.
  exact H1.
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.

  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  sep normal.
  do 5 eexists.
  exists 1%nat.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal.
  sep split.

  apply disj_split.
  left.
  sep lifts (20::21::22::23::nil)%nat in H3.
  eapply inv_change_aux in H3.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep auto.
  sep split in H3;auto.
  auto.
  sep split in H3;auto.
  sep split in H3; eauto.
  auto.
  sep split in H3;auto.
  sep split in H3;auto.
  sep split in H3. auto.
  sep split in H3. apply H8.
  sep split in H3;auto.
  sep split in H3. eauto.
  unfolds; auto.
  auto.
  auto.
  destruct H1.
  apply astar_l_afalse_elim  in H1.
  auto.
  sep split in H1.
  rewrite Int.eq_true in H5.
  destruct H5; tryfalse.

  (*当前中断不为1*)
  eapply backward_rule1.
  intros.
  sep lifts (13::14::32::nil)%nat in H1.
  apply inv_change_aux in H1.
  exact H1.
  unfold AGVars.
  hoare forward.
  instantiate (1:= Afalse). (*not for sequential composition, so Afalse is enough.*)
  pure intro.
  rename H1 into Hm. rename H2 into Hn.
  rename H3 into Hint_neq_one.
  (*These three facts are true, and not needed for future proof*)
  clear H4 H5 H6. 
  eapply seq_rule.
  (*prove ENTER_CRITICAL*)
  hoare lifts (44::40::17::41::42::43::nil)%nat pre.
  eapply encrit2_rule'.
  intros.
  exact H1.
  apply GoodI_I.  (* GoodI *)
  p_local_go.


  (*prove If OSIntNesting*)
  hoare forward.
  destruct (Int.ltu (Int.repr 0) v'43); auto.
  (*prove --OSIntNesting*)
  pure intro.
  clear H1 H2 H3. 
  hoare forward.
  apply disj_rule.
  pure intro.
  clear H1 H2 H3.

  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8 :: logic_val v'9 :: logic_val v'10 :: nil).
  intros.
  sep lifts (3::4::5::6::7::45::nil)%nat in H1.
  sep lift 2%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.
  Optimize Proof.
  Optimize Heap.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H1.
  unfold Int.zero in H1.
  remember (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero in H1. unfold Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H1. rewrite H0 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. tryfalse.
  unfold is_length in H1.
  destruct v'3; simpl in H1; tryfalse.
  auto.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. unfold Int.zero in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.



  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H4.
  hoare unfold.
  rename H2 into Hidle.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H6;omega.*)
  rename H3 into Hm. rename H4 into Hn.

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H5. rename Hn into H6.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H7.
  rewrite H8.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H9.
  unfold OS_RDY_TBL_SIZE in H8.
  eapply GAarray_imp_length_P in H9.
  rewrite H8.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H11;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  Optimize Proof.
  Optimize Heap.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H11.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.

  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x0) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H33.  
  rewrite H33;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H33;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x0) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.
  rewrite H34;auto.
  destruct H29;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H34.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H35.
  eapply int_unsigned_le_z2nat_lt.
  auto.

  hoare forward;eauto.
  pure intro.
  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H10;auto.

  lets Hhastid:prio_in_rtbl_has_tid H29 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  lia.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  can_change_aop_solver.
  2:apply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  can_change_aop_solver.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H36;eauto.
  instantiate (2:=  (v'48 ↝ {Int.zero})).
  instantiate (3:= ((v'47
  :: v'3
     :: x8
        :: x7
           :: Vint32 i7
              :: Vint32 i6
                 :: Vint32 i5
                    :: Vint32 i4
                       :: Vint32 i3
                          :: 
                          Vint32 i2
                          :: 
                          Vint32 i1 :: nil):: v'16) %list).
  instantiate (3:=v'14).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H37.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  sep lifts (7::1::nil)%nat%list in H37.
  apply read_only_merge_vptr in H37.
  destruct H37.
  clear H38.
  apply read_only_split_vptr in H37.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H36;eauto.
  clear -H32.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H32;auto.
  unfold Int.notbool in H32.
  int auto.
  instantiate (2:=(v'48 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  hoare remember (1::2::19::nil)%nat%list pre.

  apply backward_rule1 with (<|| sched;; END None ||>  **
  (A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) )**  H37).
  intros.
  sep normal.
  auto.
  subst H37.
  eapply frame_rule' with (frm:=
  A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil)).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=(LINV OSLInv (v'48, Int.zero) (logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil))).
  intros.
  sep cancel LINV.
  exact H37.
  intros.
  intros.
  unfold SWINVt.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'4.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.

  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  eapply A_isr_is_prop_elim.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  unfold IntInv.
  sep semiauto;eauto.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel 1%nat 1%nat.
  sep cancel 8%nat 1%nat.
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
  unfold AOSTCBFreeList in H37.
  sep normal.
  sep cancel tcbdllflag.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel assertion.sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H37.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H37.
  eapply Astruct_sll_OS_TCB_dup_false; eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H36.
  eauto.
  
  destruct_s s.
  simpl in H42;subst i11.
  simpl.
  auto.
  Optimize Proof.
  Optimize Heap.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H16.
  clear -H16;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  simpl in H42,H39.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.

  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H36.
  rewrite H36 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s|=AOSTCBList v'12 (Vptr (v'48 ↝ {Int.zero})) v'14 ((
                v'47
                :: v'3
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'48 ↝ {Int.zero}) v'20 ** H38).
  unfold AOSTCBList.
  sep normal.
  clear HeqH38.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H37.
  subst H38.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep lifts (1::37::21::nil)%nat in H39.
  unfold CurTid in H39.
  eapply highest_rdy_eq in H39;eauto.
  clear -Hran.
  remember ( Int.add (Int.shl x (Int.repr 3)) x0 ) as X.
  clear HeqX.
  int auto.

  exists v'20.
  sep auto.
  clear -H14 H16.
  simpl in H16.
  mytac.
  inverts H.
  assert (join (sig (v'48 ↝ {Int.zero}) x2) x1 v'46).
  auto.
  clear H1.
  clear -H H14.
  assert (get (sig (v'48↝ {Int.zero}) x2) (v'48 ↝ {Int.zero}) = Some x2).
  apply map_get_sig.
  eapply join_get_l in H;eauto.
  eapply join_get_r in H14;eauto.
  unfolds;eauto.
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat. 
  simpl; auto.
  intros.
  exact H18.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
    A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
    Aisr (isrupd v'0 v'4 false) **
    Aie false **
    Ais (v'4 :: nil) **
    Acs (false :: nil) **
    Aier (ierupd v'1 v'4 true) ** 
    LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** p_local OSLInv (v'48 ↝ {Int.zero}) (logic_val (V$ 1)
    :: logic_val v'7
       :: logic_val v'8
          :: logic_val v'9
             :: logic_val v'10 :: nil))).
  intros.
  ssplit_apure_in H18.

  unfold SWINVt in H18.
  unfold SWINV in H18.  
  sep normal in H18.
  sep destruct H18.
  sep lifts (2::3::9::7::nil)%nat in H18.
  apply invlth_isr_invlth_isr'_imp in H18.
  unfold aemp_isr_is in H18.
  sep normal in H18.
  eapply A_isr_is_prop_elim'''' in H18.
  sep cancel 1%nat 9%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  rewrite Hempisr; auto.

  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (28::30::25::26::27::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.  
  sep lifts (1::2::21::nil)%nat in H29.
  apply elim_a_isr_is_prop' in H29.
  exact H29.
  rewrite Hempisr.
  unfolds;simpl;auto.
  hoare lifts (4::1::31::6::2::7::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'59 = (v'48 ↝ {Int.zero})).
  sep lifts (33::12::nil)%nat in H29.
  eapply p_local_ostcblist_eq_ct in H29.
  auto.
  subst v'59.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  sep normal.
  sep split.
  apply disj_split.
  right. 
  sep split.
 
  sep cancel 32%nat 3%nat.
  apply disj_split.
  left.
  unfold AOSTCBPrioTbl in H29.
  unfold AGVars in H29.
  sep lift 23%nat in H29.
  sep normal in H29.
  sep destruct H29.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  sep split in H29; eauto. auto.
  sep split in H29. auto.
  sep split in H29. auto.
  sep split in H29. auto.
  sep split in H29. apply H34.
  sep split in H29. apply H33.
  sep split in H29. apply H31.
  unfold isflag. auto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.
  Optimize Proof.
  Optimize Heap.

  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H10;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H29 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  split; lia.
  destruct Hhastid.
  hoare lifts (2::17::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.

  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35;p_local_go.
  subst H35;p_local_go.

  apply absinfer_choice2;auto.
  subst H35;p_local_go.
  subst H35;p_local_go.

  eapply abscsq_rule'.
  apply noabs_oslinv.

  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'48 ↝ {Int.zero}));eauto.
  subst H35; p_local_go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  instantiate (2:=  (v'48 ↝ {Int.zero})).
  instantiate(2:= (v'47
  :: v'3
   :: x8
      :: x7
         :: Vint32 i7
            :: Vint32 i6
               :: Vint32 i5
                  :: Vint32 i4
                     :: Vint32 i3
                        :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16).
   instantiate (2:=v'14).
   instantiate (2:=v'12).
   subst H35.
   unfold p_local in H36.
   unfold CurTid in H36.
   sep normal in H36.
   sep destruct H36.
   unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList. 
  sep cancel 39%nat 9%nat.
  sep split;eauto.
  split;auto.
  go.
  subst H35.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H34;eauto.
  clear -H32.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H32;destruct H32;auto;tryfalse.
  instantiate (2:=(v'48 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'4:: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq_end;auto.
  subst H35; p_local_go.
  subst H35; p_local_go.
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** Aie false ** Ais (v'4::nil) ** Acs (false::nil) ** Aisr empisr ** Aier (ierupd v'1 v'4 true) **   LV os_code_defs.x @ Int32u |-> is_length (v'4:: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** p_local OSLInv (v'48 ↝ {Int.zero}) (logic_val (V$ 1)
                                  :: logic_val v'7
                                     :: logic_val v'8
                                        :: logic_val v'9
                                           :: logic_val v'10 :: nil) ).

  intros.
  subst H35.
  sep remember (6::7::8::9::10::nil)%nat in H36.
  assert(s|=AOSTCBList v'12 (Vptr (v'48 ↝ {Int.zero})) v'14 ((
   v'47
   :: v'3
    :: x8
       :: x7
          :: Vint32 i7
             :: Vint32 i6
                :: Vint32 i5
                   :: Vint32 i4
                      :: Vint32 i3
                         :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'48 ↝ {Int.zero}) v'20 ** H35).
  unfold AOSTCBList.
  sep normal.
  clear HeqH35.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H36.
  subst H35.
  unfold OSInv.
  unfold IntInv.
  unfold A_isr_is_prop.
  sep lifts (1::23::24::25::nil)%nat in H37.
  rewrite <- inv_change_aux in H37.
  sep semiauto;eauto.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 3%nat 1 %nat.
  sep cancel 3%nat 1 %nat.
  exact H37.
  simpl;auto.
  rewrite <- Hempisr. auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  simpl in H16.
  clear -H16;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  rewrite H38, H41.
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (30::28::14::26::27::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply elim_a_isr_is_prop' in H35.
  exact H35.
  unfolds;simpl;auto.
  hoare lifts (3::1::6::4::2::5::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'59 = (v'48 ↝ {Int.zero})).
  sep lifts (33::10::nil)%nat in H35.
  eapply p_local_ostcblist_eq_ct in H35.
  auto.
  Optimize Proof.
  Optimize Heap.
  subst v'59.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  right.
  sep normal.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  eauto.
  sep split in H35. eauto. eauto.
  sep split in H35. eauto. 
  sep split in H35. eauto.
  sep split in H35. eauto. 
  sep split in H35. eauto.
  sep split in H35. eauto.
  sep split in H35. eauto.
  sep split in H35. rewrite <- Hempisr in H38. eauto.
  unfolds; auto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.
  intros.
  exact H1.
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  right.
  sep normal.
  sep split.
  apply disj_split.
  left.
  sep lifts (21::22::23::24::nil)%nat in H2.
  eapply inv_change_aux in H2.
  sep normal.
  sep eexists.
  

  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep semiauto;eauto.
  sep split in H2; eauto.
  auto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  auto.
  
  unfolds; auto.
  auto.
  auto.
  (*second checkis*)
  eapply seq_rule.
  hoare lifts (1::3::2::nil)%nat pre.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil)).
  intros.
  sep lifts (1::2::3::4::5::44::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq v'43
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H2.
  unfold Int.zero in H2.
  remember (Int.eq v'43 (Int.repr 0)) as X.
  remember (Int.eq v'44 (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero in H2. unfold Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H2. rewrite H0 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. tryfalse.
  unfold is_length in H2.
  destruct v'3; simpl in H2; tryfalse.
  auto.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. unfold Int.zero in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H5. 
  hoare unfold.
  rename H2 into Hidle.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H7;omega.*)
  rename H3 into Hm. rename H5 into Hn.

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  Optimize Proof.
  Optimize Heap.
  auto.
  rename Hm into H6. rename Hn into H7.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H12;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H12.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.

  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x0) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.  
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H34;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x0) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.
  rewrite H35;auto.
  destruct H30;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.

  hoare forward;eauto.
  pure intro.
  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H11;auto.

  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  lia.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  can_change_aop_solver.
  2:apply absinfer_choice1;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  can_change_aop_solver.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  instantiate (2:=  (v'48 ↝ {Int.zero})).
  instantiate (3:= ((v'47
  :: v'3
     :: x8
        :: x7
           :: Vint32 i7
              :: Vint32 i6
                 :: Vint32 i5
                    :: Vint32 i4
                       :: Vint32 i3
                          :: 
                          Vint32 i2
                          :: 
                          Vint32 i1 :: nil):: v'16) %list).
  instantiate (3:=v'14).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H38.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep lifts (7::1::nil)%nat%list in H38.
  apply read_only_merge_vptr in H38.
  destruct H38.
  clear H39.
  apply read_only_split_vptr in H38.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'48 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  can_change_aop_solver.
  hoare remember (1::2::19::nil)%nat%list pre.

  apply backward_rule1 with (<|| sched;; END None ||>  **
  (A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) )**  H38).
  intros.
  sep normal.
  auto.
  subst H38.
  eapply frame_rule' with (frm:=
  A_dom_lenv ((os_code_defs.x ↝ {Int32u}) :: nil) **
  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil)).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=(LINV OSLInv (v'48, Int.zero) (logic_val (V$ 1)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil))).
  intros.
  sep cancel LINV.
  exact H38.
  intros.
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
  exists v'4.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.

  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  eapply A_isr_is_prop_elim.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  unfold IntInv.
  sep semiauto; eauto.
  sep cancel APthreadAttr.
  sep cancel 1%nat 1%nat.
  sep cancel 8%nat 1%nat.
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
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel assertion.sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false; eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.
  
  destruct_s s.
  simpl in H43;subst i11.
  simpl.
  auto.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  simpl in H43,H40.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.

  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H37.
  rewrite H37 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'12 (Vptr (v'48 ↝ {Int.zero})) v'14 ((
                v'47
                :: v'3
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'48 ↝ {Int.zero}) v'20 ** H39).
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
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep lifts (1::37::21::nil)%nat in H40.
  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  clear -Hran.
  remember ( Int.add (Int.shl x (Int.repr 3)) x0 ) as X.
  clear HeqX.
  int auto.
  Optimize Proof.
  Optimize Heap.

  exists v'20.
  sep auto.
  clear -H15 H17.
  simpl in H17.
  mytac.
  inverts H.
  assert (join (sig (v'48 ↝ {Int.zero}) x2) x1 v'46).
  auto.
  clear H1.
  clear -H H15.
  assert (get (sig (v'48 ↝ {Int.zero}) x2) (v'48 ↝ {Int.zero}) = Some x2).
  apply map_get_sig.
  eapply join_get_l in H;eauto.
  eapply join_get_r in H15;eauto.
  unfolds;eauto.
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat. 
  simpl; auto.
  intros.
  exact H19.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
    A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
    Aisr (isrupd v'0 v'4 false) **
    Aie false **
    Ais (v'4 :: nil) **
    Acs (false :: nil) **
    Aier (ierupd v'1 v'4 true) ** 
    LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** p_local OSLInv (v'48 ↝ {Int.zero}) (logic_val (V$ 1)
    :: logic_val v'7
       :: logic_val v'8
          :: logic_val v'9
             :: logic_val v'10 :: nil))).
  intros.
  ssplit_apure_in H19.

  unfold SWINVt in H19.
  unfold SWINV in H19.  
  sep normal in H19.
  sep destruct H19.
  sep lifts (2::3::9::7::nil)%nat in H19.
  apply invlth_isr_invlth_isr'_imp in H19.
  unfold aemp_isr_is in H19.
  sep normal in H19.
  eapply A_isr_is_prop_elim'''' in H19.
  sep cancel 1%nat 9%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  rewrite Hempisr; auto.

  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (28::30::25::26::27::29::31::nil)%nat pre.
  eapply backward_rule1.
  intros.  
  sep lifts (1::2::21::nil)%nat in H30.
  apply elim_a_isr_is_prop' in H30.
  exact H30.
  rewrite Hempisr.
  unfolds;simpl;auto.
  hoare lifts (4::1::31::6::2::7::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'59 = (v'48 ↝ {Int.zero})).
  sep lifts (33::12::nil)%nat in H30.
  eapply p_local_ostcblist_eq_ct in H30.
  auto.
  subst v'59.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  sep normal.
  sep split.
  sep cancel 33%nat 3%nat.
  apply disj_split.
  right.  
  sep normal. sep split.
  apply disj_split.
  left.
  unfold AOSTCBPrioTbl in H30.
  unfold AGVars in H30.
  sep normal in H30.
  sep destruct H30.
  sep normal.
  sep eexists.
  (*unfold AOSRunning in H30.*)
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep semiauto;eauto.
  sep split in H30. eauto.
  eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  sep split in H30. eauto.
  unfolds; eauto.
  rewrite Hempisr;unfolds;simpl;auto.
  auto.

  lets Hinrtbl:unmap_inrtbl H1 H0 H2 H11;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x0).
  split; lia.
  destruct Hhastid.
  hoare lifts (2::17::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.

  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq;auto.
  subst H36;p_local_go.
  subst H36;p_local_go.

  apply absinfer_choice2;auto.
  subst H36;p_local_go.
  subst H36;p_local_go.

  eapply abscsq_rule'.
  apply noabs_oslinv.

  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'48 ↝ {Int.zero}));eauto.
  subst H36; p_local_go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.
  instantiate (2:=  (v'48 ↝ {Int.zero})).
  instantiate(2:= (v'47
  :: v'3
   :: x8
      :: x7
         :: Vint32 i7
            :: Vint32 i6
               :: Vint32 i5
                  :: Vint32 i4
                     :: Vint32 i3
                        :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16).
   instantiate (2:=v'14).
   instantiate (2:=v'12).
   subst H36.
   unfold p_local in H37.
   unfold CurTid in H37.
   sep normal in H37.
   sep destruct H37.
   unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList. 
  sep cancel 39%nat 9%nat.
  sep split;eauto.
  split;auto.
  go.
  subst H36.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq (Int.add (Int.shl x (Int.repr 3)) x0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'48 ↝ {Int.zero})).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  subst H36; p_local_go.
  subst H36; p_local_go.
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** Aie false ** Ais (v'4::nil) ** Acs (false::nil) ** Aisr empisr ** Aier (ierupd v'1 v'4 true) **   LV os_code_defs.x @ Int32u |-> is_length (v'4 :: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** p_local OSLInv (v'48 ↝ {Int.zero}) (logic_val (V$ 1)
                                  :: logic_val v'7
                                     :: logic_val v'8
                                        :: logic_val v'9
                                           :: logic_val v'10 :: nil) ).

  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s|=AOSTCBList v'12 (Vptr (v'48 ↝ {Int.zero})) v'14 ((
   v'47
   :: v'3
    :: x8
       :: x7
          :: Vint32 i7
             :: Vint32 i6
                :: Vint32 i5
                   :: Vint32 i4
                      :: Vint32 i3
                         :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'48 ↝ {Int.zero}) v'20 ** H36).
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
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold IntInv.
  sep lifts (1::23::24::25::nil)%nat in H38.
  rewrite <- inv_change_aux in H38.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 3%nat 1 %nat.
  sep cancel 3%nat 1 %nat.
  exact H38.
  simpl;auto.
  rewrite <- Hempisr. auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  destruct p. (* new add *)
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  rewrite H39, H42.
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  unfold IntInv.
  hoare normal pre.
  pure intro.
  hoare lifts (8::9::10::11::12::13::14::15::16::
  17::18::19::20::21::22::23::24::25::nil)%nat pre.
  hoare lifts (30::28::14::24::26::27::29::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply elim_a_isr_is_prop' in H36.
  exact H36.
  unfolds;simpl;auto.
  hoare lifts (4::1::30::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  assert(v'59 = (v'48 ↝ {Int.zero})).
  sep lifts (33::11::nil)%nat in H36.
  eapply p_local_ostcblist_eq_ct in H36.
  auto.
  subst v'59.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  right.
  sep normal.
  
  sep semiauto;eauto.
  sep cancel p_local.
  left.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep semiauto;eauto.
  
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36; eauto.
  sep split in H36. rewrite <- Hempisr in H39. eauto.
  unfolds; auto.
  rewrite Hempisr;unfolds;simpl;auto.
  eauto.
  intros.
  exact H1.
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.

  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I.
  p_local_go.
  apply ret_rule'.
  intros.
  sep normal.
  do 5 eexists.
  exists v'4.
  exists (Vint32 (Int.repr 1)).
  do 5 eexists.
  sep split.
  3:eauto.
  apply disj_split.
  right.
  sep normal.
  sep split.

  apply disj_split.
  left.
  sep lifts (20::21::22::23::nil)%nat in H3.
  eapply inv_change_aux in H3.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep auto.
  sep split in H3;auto.
  auto.
  Optimize Proof.
  Optimize Heap.
  sep split in H3;auto.
  sep split in H3; eauto.
  auto.
  sep split in H3;auto.
  sep split in H3;auto.
  sep split in H3. auto.
  sep split in H3. apply H8.
  sep split in H3;auto.
  sep split in H3. eauto.
  unfolds; auto.
  auto.
  auto.
  destruct H1.
  apply astar_l_afalse_elim  in H1.
  auto.
  sep split in H1.
  rewrite Int.eq_true in H5.
  destruct H5; tryfalse.

  (*p_local holds 0 *)
  eapply backward_rule1.
  intros.
  sep lift 26%nat in H1.
  apply disj_split in H1.
  exact H1.
  apply disj_rule.
  unfold AGVars.
  (*中断号为1*)
  hoare forward.
  instantiate (1:= Afalse). (*not for sequential composition, so Afalse is enough.*)
  pure intro.
  rename H1 into Hm. rename H2 into Hn.
  (*These three facts are true, and not needed for future proof*)
  clear H4 H5 H6. 
  eapply seq_rule.
  (*prove ENTER_CRITICAL*)
  hoare lifts (42::39::37::38::40::41::nil)%nat pre.
  eapply encrit2_rule'.
  intros.
  sep lifts (3::18::1::4::5::nil)%nat in H1.
  exact H1.
  apply GoodI_I.  (* GoodI *)
  p_local_go.


  (*prove If OSIntNesting*)
  hoare forward.
  destruct (Int.ltu (Int.repr 0) v'43); auto.
  (*prove --OSIntNesting*)
  pure intro.
  clear H1 H2 H3. 
  hoare forward.
  apply disj_rule.
  pure intro.
  clear H1 H2 H3.

  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 0)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil)).
  intros.
  sep lifts (4::3::5::6::7::44::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H1.
  unfold Int.zero in H1.
  remember (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero in H1. unfold Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H1. rewrite H0 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. tryfalse.
  unfold is_length in H1.
  destruct v'3; simpl in H1; tryfalse.
  auto.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. unfold Int.zero in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.



  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H4.
  hoare unfold.
  rename H2 into Hidle.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H6;omega.*)
  rename H3 into Hm. rename H4 into Hn.

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H5. rename Hn into H6.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H7.
  rewrite H8.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  Optimize Proof.
  Optimize Heap.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H9.
  unfold OS_RDY_TBL_SIZE in H8.
  eapply GAarray_imp_length_P in H9.
  rewrite H9.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H11;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare lifts (32::47::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H9.
  destruct H9.
  unfold p_local in H9.
  unfold CurTid in H9.
  sep normal in H9.
  sep destruct H9.
  unfold tcbdllseg in H9.
  sep lifts (4::1::nil)%nat in H9.
  sep split in H9.
  destruct H10;subst.
  apply read_only_merge_vptr in H9.
  destruct H9.
  sep lifts (3::4::5::6::nil)%nat in H9.
  apply task_del_noexists in H9.
  unfolds in H9;false.
  sep lift 35%nat in H9.
  apply disj_split in H9.
  unfold TCBFree_Not_Eq in H9.
  destruct H9.
(*ct is not the head of freelist, false case*)
  sep normal in H9.
  sep destruct H9.
  sep split in H9.
  destruct H10;tryfalse.
  exact H9.
  unfold TCBFree_Eq.
  (*The struct corresponding to ct is from TCBFree_EEq. *)
    unfold p_local,CurTid.
  (*Astruct ct OS_TCB_flag vl, vl is the value of ct, where it comes from?*)
    hoare unfold.
    hoare lift 3%nat pre.
    hoare forward.
    go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H14.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H17.
  apply Zle_bool_imp_le in Hran.
  
  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x1) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia. 
  apply Zle_is_le_bool in H30.  
  rewrite H30;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H30;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x1) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H31.
  rewrite H31;auto.
  destruct H26;auto.
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
  lets Hinrtbl:unmap_inrtbl Hidle H1 H2 H14;auto.

  lets Hhastid:prio_in_rtbl_has_tid H26 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x1).
  split;lia.
  destruct Hhastid.
  hoare lifts (1::29::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  unfold isched.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H34).

  apply absinfer_seq;auto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H34).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H34. can_change_aop_solver.
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H33;eauto.
  subst H34.
  sep cancel tcblist.
  sep cancel 52%nat 1%nat.
  sep lifts (7::8::nil)%nat in H35.
  apply read_only_merge_vptr in H35.
  destruct H35.
  exact H34.
  subst H34.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  sep lifts (6::7::nil)%nat in H35.
  apply read_only_merge_vptr in H35.
  destruct H35.
  sep lifts (8::9::46::1::nil)%nat in H35.
  eapply  highest_ct_dead_neq in H35;eauto.
  rewrite Int.repr_unsigned in H33;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H34).
  apply absinfer_seq;auto.
  subst H34. can_change_aop_solver.
  subst H34. can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H34. can_change_aop_solver.
  subst H34. can_change_aop_solver.
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H34).
   intros.
   sep normal.
   auto.
   subst H34.
   eapply switchdead_rule with (Px:=LINV OSLInv ct  ((logic_val (V$ 0)
   :: logic_val v'7
      :: logic_val v'8
         :: logic_val v'9
            :: logic_val v'10 :: nil)) **  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H34.
  intros.
  unfold SWINVt.
  
  sep normal.
  exists v'50. 
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists 1%nat.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  apply A_isr_is_prop_elim.
  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  unfold IntInv.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 1%nat 1%nat.
  sep cancel 15%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'49.
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
  rewrite H39;simpl;auto.
  rewrite <- Hempisr;auto.
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
  rewrite H39, H36.
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H33.
  rewrite H33 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H34.
  sep split in H34.
  mytac.
  sep lifts (4::5::nil)%nat in H34.
  apply read_only_merge_vptr in H34;destruct H34.
  sep auto.
  auto.
  exists v'20.
  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.
  intros.
  exact H25.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H25;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H29.
  remember(Int.eq
  (Int.add (Int.shl x (Int.repr 3))
     x1) x0) as X.
   destruct X. simpl in H28.
   assert (Int.eq
   (Int.add (Int.shl x (Int.repr 3))
      x1) x0 =false).
   eapply dead_not_ready;eauto.
   eapply prio_not_in_tcbls_nready;eauto.
  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H;inverts H;auto.
  rewrite H31 in HeqX0.
  tryfalse.
  simpl in H29.
  clear -H29;int auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1)
  x0); simpl in H29; tryfalse.
  intros.
  exact H1.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H1;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  left.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 2%nat 5%nat. 
  exact H2.
  sep split in H2; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  unfolds; auto.
  auto.  
  (*OSIntNesting 不大于0*)
  eapply seq_rule.
  hoare lifts (1::7::nil)%nat pre.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 0)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil)).
  intros.
  sep lifts (3::2::4::5::6::43::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (v'43) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (v'43)
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H2.
  unfold Int.zero in H2.
  remember (Int.eq v'43
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero in H2. unfold Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H2. rewrite H0 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. tryfalse.
  unfold is_length in H2.
  destruct v'3; simpl in H2; tryfalse.
  auto.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. unfold Int.zero in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.



  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.

  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  rename Hm into H3. rename Hn into H5.
  hoare unfold.
  rename H2 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H7;omega.*)
  rename H3 into Hm. rename H5 into Hn.
  
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H6. rename Hn into H7.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  Optimize Proof.
  Optimize Heap.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H12;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare lifts (32::47::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H10.
  destruct H10.
  unfold p_local in H10.
  unfold CurTid in H10.
  sep normal in H10.
  sep destruct H10.
  unfold tcbdllseg in H10.
  sep lifts (4::1::nil)%nat in H10.
  sep split in H10.
  destruct H11;subst.
  apply read_only_merge_vptr in H10.
  destruct H10.
  sep lifts (3::4::5::6::nil)%nat in H10.
  apply task_del_noexists in H10.
  unfolds in H10;false.
  sep lift 35%nat in H10.
  apply disj_split in H10.
  unfold TCBFree_Not_Eq in H10.
  destruct H10.
(*ct is not the head of freelist, false case*)
  sep normal in H10.
  sep destruct H10.
  sep split in H10.
  destruct H11;tryfalse.
  exact H10.
  unfold TCBFree_Eq.
  (*The struct corresponding to ct is from TCBFree_EEq. *)
    unfold p_local,CurTid.
  (*Astruct ct OS_TCB_flag vl, vl is the value of ct, where it comes from?*)
    hoare unfold.
    hoare lift 3%nat pre.
    hoare forward.
    go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H15.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H18.
  apply Zle_bool_imp_le in Hran.
  
  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x1) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia. 
  apply Zle_is_le_bool in H31.  
  rewrite H31;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H31;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x1) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H32.
  rewrite H32;auto.
  destruct H27;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H32.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H33.
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
  lets Hinrtbl:unmap_inrtbl Hidle H1 H2 H15;auto.

  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x1).
  split;lia.
  destruct Hhastid.
  hoare lifts (1::29::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  unfold isched.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).

  apply absinfer_seq;auto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H35. can_change_aop_solver.
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H34;eauto.
  subst H35.
  sep cancel tcblist.
  sep cancel 52%nat 1%nat.
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  exact H35.
  subst H35.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  sep lifts (6::7::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  sep lifts (8::9::46::1::nil)%nat in H36.
  eapply  highest_ct_dead_neq in H36;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H35).
  apply absinfer_seq;auto.
  subst H35. can_change_aop_solver.
  subst H35. can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H35. can_change_aop_solver.
  subst H35. can_change_aop_solver.
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H35).
   intros.
   sep normal.
   auto.
   subst H35.
   eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0)
   :: logic_val v'7
      :: logic_val v'8
         :: logic_val v'9
            :: logic_val v'10 :: nil)**  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H35.
  intros.
  unfold SWINVt.
  
  sep normal.
  exists v'50. 
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists 1%nat.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  apply A_isr_is_prop_elim.
  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  unfold IntInv.
  sep semiauto;eauto.
  sep cancel CoreCommuInv.
  sep cancel APthreadAttr.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 1%nat 1%nat.
  sep cancel 15%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'49.
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
  rewrite Int.repr_unsigned in H34;eauto.
  rewrite H40;simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  rewrite H40, H37.
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H34.
  rewrite H34 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H35.
  sep split in H35.
  mytac.
  sep lifts (4::5::nil)%nat in H35.
  apply read_only_merge_vptr in H35;destruct H35.
  sep auto.
  auto.
  exists v'20.
  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.
  intros.
  exact H26.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H30.
  remember(Int.eq
  (Int.add (Int.shl x (Int.repr 3))
     x1) x0) as X.
   destruct X. simpl in H30.
   assert (Int.eq
   (Int.add (Int.shl x (Int.repr 3))
      x1) x0 =false).
   eapply dead_not_ready;eauto.
   eapply prio_not_in_tcbls_nready;eauto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H;inverts H;auto.
  rewrite H32 in HeqX0.
  tryfalse.
  simpl in H30.
  clear -H30;int auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1)
  x0); simpl in H30; tryfalse.
  intros.
  exact H1.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H1;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  left.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 2%nat 5%nat. 
  exact H3.
  sep split in H3; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  unfolds; auto.
  destruct H1.
  apply astar_l_afalse_elim in H1.
  auto.
  sep split in H1.
  rewrite Int.eq_true in H5.
  destruct H5; tryfalse.
  (*中断号不为1*)
  unfold AGVars.
  hoare forward. (*not for sequential composition, so Afalse is enough.*)
  instantiate (1:= Afalse). 
  pure intro.
  rename H1 into Hm. rename H2 into Hn.
  clear H4 H5 H6. 
  eapply seq_rule.
  (*prove ENTER_CRITICAL*)
  hoare lifts (42::39::37::38::40::41::nil)%nat pre.
  eapply encrit2_rule'.
  intros.
  sep lifts (3::18::1::4::5::nil)%nat in H1.
  exact H1.
  apply GoodI_I.  (* GoodI *)
  p_local_go.
  rename H3 into Hint_neq_one.


  (*prove If OSIntNesting*)
  unfold AOSIntNesting. 
  hoare forward.
  destruct (Int.ltu (Int.repr 0) v'43); auto.
  (*prove --OSIntNesting*)
  pure intro.
  
  clear H1 H2 H3. 
  hoare forward.
  apply disj_rule.
  pure intro.
  clear H1 H2 H3.

  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=((logic_val (V$ 0)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil))).
  intros.
  sep lifts (4::3::5::6::7::44::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (Int.sub v'43 (Int.repr 1)) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H1.
  unfold Int.zero in H1.
  remember (Int.eq (Int.sub v'43 (Int.repr 1))
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero in H1. unfold Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H1. rewrite H0 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. tryfalse.
  unfold is_length in H1.
  destruct v'3; simpl in H1; tryfalse.
  auto.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. rewrite H0 in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.
  unfold is_length in H1. simpl in H1.
  unfold Int.zero, Int.one in H1.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H1. unfold Int.zero in H1.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H2 in H1.
  simpl in H1. unfold Int.zero in H1.
  rewrite H in H1. simpl in H1. tryfalse.



  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  
  hoare unfold.
  rename H2 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  
  rtmatch_solve.
  rename Hm into H3. rename Hn into H4.
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H6;omega.*)
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H5. rename Hn into H6.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H7.
  rewrite H8.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H9.
  unfold OS_RDY_TBL_SIZE in H8.
  eapply GAarray_imp_length_P in H9.
  rewrite H9.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  Optimize Proof.
  Optimize Heap.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H11;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H10.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare lifts (32::47::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H9.
  destruct H9.
  unfold p_local in H9.
  unfold CurTid in H9.
  sep normal in H9.
  sep destruct H9.
  unfold tcbdllseg in H9.
  sep lifts (4::1::nil)%nat in H9.
  sep split in H9.
  destruct H10;subst.
  apply read_only_merge_vptr in H9.
  destruct H9.
  sep lifts (3::4::5::6::nil)%nat in H9.
  apply task_del_noexists in H9.
  unfolds in H9;false.
  sep lift 35%nat in H9.
  apply disj_split in H9.
  unfold TCBFree_Not_Eq in H9.
  destruct H9.
(*ct is not the head of freelist, false case*)
  sep normal in H9.
  sep destruct H9.
  sep split in H9.
  destruct H10;tryfalse.
  exact H9.
  unfold TCBFree_Eq.
  (*The struct corresponding to ct is from TCBFree_EEq. *)
    unfold p_local,CurTid.
  (*Astruct ct OS_TCB_flag vl, vl is the value of ct, where it comes from?*)
    hoare unfold.
    hoare lift 3%nat pre.
    hoare forward.
    go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H14.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H17.
  apply Zle_bool_imp_le in Hran.
  
  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x1) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia. 
  apply Zle_is_le_bool in H30.  
  rewrite H30;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H30;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x1) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H31.
  rewrite H31;auto.
  destruct H26;auto.
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
  lets Hinrtbl:unmap_inrtbl Hidle H1 H2 H14;auto.

  lets Hhastid:prio_in_rtbl_has_tid H26 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x1).
  split;lia.
  destruct Hhastid.
  hoare lifts (1::29::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  unfold isched.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H34).

  apply absinfer_seq;auto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H34.
  can_change_aop_solver.
  subst H34.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H34).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H34. can_change_aop_solver.
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H33;eauto.
  subst H34.
  sep cancel tcblist.
  sep cancel 52%nat 1%nat.
  sep lifts (7::8::nil)%nat in H35.
  apply read_only_merge_vptr in H35.
  destruct H35.
  exact H34.
  subst H34.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  sep lifts (6::7::nil)%nat in H35.
  apply read_only_merge_vptr in H35.
  destruct H35.
  sep lifts (8::9::46::1::nil)%nat in H35.
  eapply  highest_ct_dead_neq in H35;eauto.
  rewrite Int.repr_unsigned in H33;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H34).
  apply absinfer_seq;auto.
  subst H34. can_change_aop_solver.
  subst H34. can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H34. can_change_aop_solver.
  subst H34. can_change_aop_solver.
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H34).
   intros.
   sep normal.
   auto.
   subst H34.
   eapply switchdead_rule with (Px:=LINV OSLInv ct   (logic_val (V$ 0)
   :: logic_val v'7
      :: logic_val v'8
         :: logic_val v'9
            :: logic_val v'10 :: nil) **  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H34.
  intros.
  unfold SWINVt.
  
  sep normal.
  exists v'51. 
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'4.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  apply A_isr_is_prop_elim.
  unfold OSInv.
  unfold AGVars.
  unfold IntInv.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 1%nat 1%nat.
  sep cancel 15%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'50.
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
  rewrite H39;simpl;auto.
  rewrite <- Hempisr;auto.
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
  rewrite H39, H36.
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H33.
  rewrite H33 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H34.
  sep split in H34.
  mytac.
  sep lifts (4::5::nil)%nat in H34.
  apply read_only_merge_vptr in H34;destruct H34.
  sep auto.
  auto.
  exists v'20.
  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.
  intros.
  exact H25.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H25;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H29.
  remember(Int.eq
  (Int.add (Int.shl x (Int.repr 3))
     x1) x0) as X.
   destruct X. simpl in H29.
   assert (Int.eq
   (Int.add (Int.shl x (Int.repr 3))
      x1) x0 =false).
   eapply dead_not_ready;eauto.
   eapply prio_not_in_tcbls_nready;eauto.
  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H;inverts H;auto.
  rewrite H31 in HeqX0.
  tryfalse.
  simpl in H29.
  clear -H29;int auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1)
  x0); simpl in H29; tryfalse.
  intros.
  exact H1.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H1;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 2%nat 5%nat. 
  exact H2.
  sep split in H2; eauto.
  auto.
  Optimize Proof.
  Optimize Heap.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  sep split in H2; eauto.
  unfolds; auto.
  (*OSIntNesting 不大于0*)
  eapply seq_rule.
  hoare lifts (1::7::nil)%nat pre.
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 0)
  :: logic_val v'7
     :: logic_val v'8
        :: logic_val v'9
           :: logic_val v'10 :: nil)).
  intros.
  sep lifts (3::2::4::5::6::43::nil)%nat in H1.
  exact H1.
  apply GoodI_I.
  p_local_go.
  intros.
  sep auto.

  (*prove If(OSIntNesting == 0 && 
  OSLockNesting == 0) && (x == 1)*)
  hoare_forward_stmts_nsepauto.
  destruct (Int.eq v'43 (Int.repr 0));
  auto.
  unfold Int.zero.
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  destruct (Int.eq (v'43) (Int.repr 0));
  destruct(Int.eq v'44 (Int.repr 0)); auto.
  unfold is_length.
  destruct v'3;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'3;simpl;auto.

  unfold is_length.
  destruct v'3; 
  destruct (Int.eq (v'43)
  (Int.repr 0)); destruct (Int.eq v'44
  (Int.repr 0)); simpl; auto.

  pure intro.
  assert(v'3 = nil).
  clear -H2.
  unfold Int.zero in H2.
  remember (Int.eq v'43
  (Int.repr 0)) as X.
  remember (Int.eq v'44
  (Int.repr 0)) as Y.
  destruct X. destruct Y. destruct v'3.
  auto.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero in H2. unfold Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H in H2. rewrite H0 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. 
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. tryfalse.
  unfold is_length in H2.
  destruct v'3; simpl in H2; tryfalse.
  auto.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.

  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.

  destruct v'3. auto.
  destruct Y.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. rewrite H0 in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.
  unfold is_length in H2. simpl in H2.
  unfold Int.zero, Int.one in H2.
  assert(Int.ltu (Int.repr 0) (Int.repr 0) = false) by auto.
  assert(Int.ltu (Int.repr 0) (Int.repr 1) = true ) by auto.
  rewrite H in H2. unfold Int.zero in H2.
  assert(Int.eq (Int.repr 0) (Int.repr 1) = false) by auto.
  rewrite H1 in H2.
  simpl in H2. unfold Int.zero in H2.
  rewrite H in H2. simpl in H2. tryfalse.



  instantiate (1:= Afalse).
  clear H1 H2 H3.
  subst v'3.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*prove OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′]*)
  hoare unfold.
  rename H2 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.
  rename Hm into H3. rename Hn into H5.

  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H7;omega.*)
  

  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H2.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z. (*to prove x is within the range*)
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H3.
  apply Zle_is_le_bool.
  lia.
  auto.
  rename Hm into H6. rename Hn into H7.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H3.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.*)
    
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H3.
  omega.

  apply Zle_bool_imp_le in H3.
  omega.*)

  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  apply Zle_bool_imp_le in H3.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  Optimize Proof.
  Optimize Heap.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.
  (*apply Zle_bool_imp_le in H12;omega.*)
  (*right*)
  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare lifts (32::47::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H10.
  destruct H10.
  unfold p_local in H10.
  unfold CurTid in H10.
  sep normal in H10.
  sep destruct H10.
  unfold tcbdllseg in H10.
  sep lifts (4::1::nil)%nat in H10.
  sep split in H10.
  destruct H11;subst.
  apply read_only_merge_vptr in H10.
  destruct H10.
  sep lifts (3::4::5::6::nil)%nat in H10.
  apply task_del_noexists in H10.
  unfolds in H10;false.
  sep lift 35%nat in H10.
  apply disj_split in H10.
  unfold TCBFree_Not_Eq in H10.
  destruct H10.
(*ct is not the head of freelist, false case*)
  sep normal in H10.
  sep destruct H10.
  sep split in H10.
  destruct H11;tryfalse.
  exact H10.
  unfold TCBFree_Eq.
  (*The struct corresponding to ct is from TCBFree_EEq. *)
    unfold p_local,CurTid.
  (*Astruct ct OS_TCB_flag vl, vl is the value of ct, where it comes from?*)
    hoare unfold.
    hoare lift 3%nat pre.
    hoare forward.
    go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  (*proof If(OSPrioHighRdy′ !=ₑ OSPrioCur′)*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H15.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H3 H18.
  apply Zle_bool_imp_le in Hran.
  
  hoare_forward_stmts_nsepauto.
  assert (Int.unsigned
  (Int.add (Int.shl x (Int.repr 3)) x1) <=
Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia. 
  apply Zle_is_le_bool in H31.  
  rewrite H31;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H31;auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1) x0);simpl;auto.

  hoare forward.
  assert (  Int.unsigned
    (Int.add (Int.shl x (Int.repr 3)) x1) <=
  Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H32.
  rewrite H32;auto.
  destruct H27;auto.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H32.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H33.
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
  lets Hinrtbl:unmap_inrtbl Hidle H1 H2 H15;auto.

  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range (Int.add (Int.shl x (Int.repr 3)) x1).
  split;lia.
  destruct Hhastid.
  hoare lifts (1::29::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  unfold isched.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).

  apply absinfer_seq;auto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H35.
  can_change_aop_solver.
  subst H35.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H35. can_change_aop_solver.
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H34;eauto.
  subst H35.
  sep cancel tcblist.
  sep cancel 52%nat 1%nat.
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  exact H35.
  subst H35.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  sep lifts (6::7::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  sep lifts (8::9::46::1::nil)%nat in H36.
  eapply  highest_ct_dead_neq in H36;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H35).
  apply absinfer_seq;auto.
  subst H35. can_change_aop_solver.
  subst H35. can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H35. can_change_aop_solver.
  subst H35. can_change_aop_solver.
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H35).
   intros.
   sep normal.
   auto.
   subst H35.
   eapply switchdead_rule with (Px:=LINV OSLInv ct (logic_val (V$ 0)
   :: logic_val v'7
      :: logic_val v'8
         :: logic_val v'9
            :: logic_val v'10 :: nil) **  LV os_code_defs.x @ Int32u |-> is_length (1%nat :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H35.
  intros.
  unfold SWINVt.
  
  sep normal.
  exists v'51. 
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'4.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  unfold aemp_isr_is.
  sep normal.
  sep lifts (2::3::nil)%nat.
  apply A_isr_is_prop_elim.
  unfold OSInv.
  unfold AGVars.
  unfold IntInv.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel 1%nat 1%nat.
  sep cancel 15%nat 1%nat.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'50.
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
  rewrite Int.repr_unsigned in H34;eauto.
  rewrite H40;simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  rewrite H40, H37.
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H34.
  rewrite H34 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H35.
  sep split in H35.
  mytac.
  sep lifts (4::5::nil)%nat in H35.
  apply read_only_merge_vptr in H35;destruct H35.
  sep auto.
  auto.
  exists v'20.
  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.
  intros.
  exact H26.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H30.
  remember(Int.eq
  (Int.add (Int.shl x (Int.repr 3))
     x1) x0) as X.
   destruct X. simpl in H30.
   assert (Int.eq
   (Int.add (Int.shl x (Int.repr 3))
      x1) x0 =false).
   eapply dead_not_ready;eauto.
   eapply prio_not_in_tcbls_nready;eauto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H;inverts H;auto.
  rewrite H32 in HeqX0.
  tryfalse.
  simpl in H30.
  clear -H30;int auto.
  destruct (Int.eq
  (Int.add (Int.shl x (Int.repr 3)) x1)
  x0); simpl in H30; tryfalse.
  intros.
  exact H1.
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H1;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  p_local_go.
  p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  right.
  sep split.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  sep cancel APthreadAttr.
  sep cancel CoreCommuInv.
  sep cancel CapabilityInv.
  sep cancel PartitionInv.
  sep cancel 2%nat 5%nat. 
  exact H3.
  sep split in H3; eauto.
  auto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  sep split in H3; eauto.
  unfolds; auto.
  destruct H1.
  apply astar_l_afalse_elim in H1.
  auto.
  sep split in H1.
  rewrite Int.eq_true in H5.
  destruct H5; tryfalse.


  (*ie = true sub goal*)
  eapply backward_rule1.
  intros.
  sep split in H.
  apply astar_l_afalse_elim in H.
  exact H.
  apply pfalse_rule.
Qed.

