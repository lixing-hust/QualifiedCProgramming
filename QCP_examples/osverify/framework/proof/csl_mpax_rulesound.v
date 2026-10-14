Require Import sound_include.
Require Import Lia.
Require Import symbolic_lemmas.
Require Import math_sol.
Require Import join_lib.
Require Import memory_prop.
Require Import perm_map_lemmas_part1.
Require Import perm_map_lemmas_part3.
Require Import int_auto.
Require Import csl_mpax_pure.

Lemma csl_msmc_getSMSMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 e3 n m q aop pa t index sms mpaxl mpaxh vl strheap,
            can_change_aop P' ->
            (Z.of_nat n <= Int.max_unsigned)%Z ->
            m = Vint32 index ->
            (0 <= Int.unsigned index < 8)%Z ->
            rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
            rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
            SmsMod.get sms index = Some (mpaxl, mpaxh) ->
            P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                       Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SMSMPAXL == Vptr q ->
            P ==> PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                        Aabsdata sms_mpaxid (ossms_mpax sms) ** 
                        Astruct q MSMC_SMSMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                        [| Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) /\ struct_type_vallist_match MSMC_SMSMPAXL vl |] ** P' ->
            (EX vl' strheap' , 
                     PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                     Aabsdata sms_mpaxid (ossms_mpax sms) ** 
                     Astruct q MSMC_SMSMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') ** 
                     [| vl' = get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) |] **
                      [| strheap' = Set_struct strheap q MSMC_SMSMPAXL vl' /\ struct_type_vallist_match MSMC_SMSMPAXL vl' |] ** P') ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_msmc_getSMSMPAXL n m q);; aop ||> ** P)
              (sprim (scsl_msmc_getSMSMPAXL e1 e2 e3))  
              (<|| aop ||>  ** 
                EX vl' strheap', 
                     PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                     Aabsdata sms_mpaxid (ossms_mpax sms) ** 
                     Astruct q MSMC_SMSMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') **
                     [| vl' = get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) |] **
                     [| strheap' = Set_struct strheap q MSMC_SMSMPAXL vl' /\ struct_type_vallist_match MSMC_SMSMPAXL vl' |] ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange Hmatch1 Hmatch2 Hsms HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct Hsat as [Hsat1  Hsat2].
   destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1. 
  simpl in H. subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H27; 
  try (destruct v; destruct H27 as (Heq&H27); inverts Heq); tryfalse).
  destruct (Int.unsigned i0 <=? Byte.max_unsigned)%Z eqn:eq0;tryfalse.
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  unfolds in H30. subst x2.
  apply join_lib.join_emp_eq in H2. subst x3.
  apply join_lib.join_emp_eq in H5. subst x6.
  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds.
      do 4 eexists; eauto.

  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt. unfold not. intros. apply H1. clear H1.
     destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as ?.
     apply joinm2_mem_join in Hjm1 as ?.
     destruct H1. simpl in H1,H6. destruct H4 as [? [_ ?]]. subst G2 E2.
     unfold getmem in H4. simpl in H4.
     lets HH : store_exist_join H3 H0 H4.
     apply join_lib.join_emp. auto.
     destruct HH. destruct q.

     simpl in H13. simpljoin.

     do 5 rewrite Int.add_assoc in *.
     change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in m3.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in m2.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in m1.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in m0.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in m.

     lets Hm5 : m5.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_raddr))) (M3:= x3) in Hm5.
     2:{ join auto. }
     destruct Hm5 as (x3' & Hm5).
     lets Hm4 : m4.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_sr))) (M3:= x10) in Hm4.
     2:{ join auto. }
     destruct Hm4 as (x10' & Hm4).
     lets Hm3: m3.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_sw))) (M3:= x22) in Hm3.
     2:{ join auto. }
     destruct Hm3 as (x22' & Hm3).
     lets Hm2 : m2.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_sx))) (M3:= x31) in Hm2.
     2:{ join auto. }
     destruct Hm2 as (x31' & Hm2).
     lets Hm1 : m1.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_ur))) (M3:= x37) in Hm1.
     2:{ join auto. }
     destruct Hm1 as (x37' & Hm1).
     lets Hm0 : m0.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_uw))) (M3:= x43) in Hm0.
     2:{ join auto. }
     destruct Hm0 as (x43' & Hm0).
     lets Hm : m.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl smsl_ux))) (M3:= x49) in Hm.
     2:{ join auto. }
     destruct Hm as (x49' & Hm).

    assert (Hmx: exists mx mx1 mx2 mx3 mx4 mx5 mx6,
                 join x10 x3 mx1 /\ join x22 mx1 mx2 /\ join x31 mx2 mx3 /\
                 join x37 mx3 mx4 /\ join x43 mx4 mx5 /\ join x49 mx5 mx6 /\
                 join mx mx6 M2).
    { do 7 eexists.
      splits. join auto.
      instantiate (1:= (merge_list (x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x49 :: x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x12 :: x :: x1 :: nil))). join auto.
    }
   destruct Hmx as ( mx & mx1 & mx2 & mx3 & mx4 & mx5 & mx6 & Hmx).
   destruct Hmx as (Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj6 & Hj ).

  assert (Hd1: disjoint x10' x3').
  { eapply disj_store_disj; eauto.
    eapply disjoint_sym.
    eapply disj_store_disj; eauto.
    eapply join_disj. eapply join_comm. eauto.
  }
  lets Hj1': Hd1. destruct Hj1' as (mx1' & Hj1').

  assert (Hd2: disjoint x22' mx1').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx2 mx1 = minus mx2 mx1').
    { eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]].
    }
    lets Hmin: Hj2.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj2': Hd2. destruct Hj2' as (mx2' & Hj2').

  assert (Hd3: disjoint x31' mx2').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx3 mx2 = minus mx3 mx2').
    { do 2 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj3.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj3': Hd3. destruct Hj3' as (mx3' & Hj3').

  assert (Hd4: disjoint x37' mx3').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx4 mx3 = minus mx4 mx3').
    { do 3 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj4.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj4': Hd4. destruct Hj4' as (mx4' & Hj4').

  assert (Hd5: disjoint x43' mx4').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx5 mx4 = minus mx5 mx4').
    { do 4 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj5.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj5': Hd5. destruct Hj5' as (mx5' & Hj5').

  assert (Hd6: disjoint x49' mx5').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx6 mx5 = minus mx6 mx5').
    { do 5 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj6.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj6': Hd6. destruct Hj6' as (mx6' & Hj6').

  assert (Hd: disjoint mx mx6').
  { 
    assert (Heq: minus M2 mx6 = minus M2 mx6').
    { do 6 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj': Hd. destruct Hj' as (M2' & Hj').

     do 2 eexists. unfold nilcont in *.
     eapply csl_msmc_getSMSMPAXL_step; auto.
     - erewrite evaltype_irrev_mem; eauto.
     - erewrite evaltype_irrev_mem; eauto.
     - erewrite evaltype_irrev_mem; eauto.
     - lets Hnew: evalval_mono' H4 H.  eauto. 
     - lets Hnew: evalval_mono H4 H2. rewrite Hnew.  eauto.
     - lets Hnew: evalval_mono H4 H5. rewrite Hnew.  eauto.
     - congruence.
     - congruence.
     - congruence.
     - instantiate (1 := mpaxl).
       eapply load_local with (m1:= M); eauto.
       eapply load_local; eauto.
       rewrite Int.unsigned_repr in H3.
       eapply mapstoval_load; eauto.
       clear -H31 H32.
       change Int.max_unsigned with 4294967295%Z. auto with zarith.
     - rewrite Z.add_0_r.
       unfold mapstoval, opsem.mapstoval in *.
       eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - splits; eauto. join auto.
     - rewrite Z.add_0_r. eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - splits; eauto. unfold merge_list. rewrite jl_merge_emp.
       join auto.
  +   simpl substaskst in *. 
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
      lets Hev3: H5.
      lets Hlem: evalval_mono_joinmem.
      specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
      simpl get_smem in Hlem.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H2.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H1, H4.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.
      rewrite Hev3' in H30.
      rewrite H29 in Hev2'.
      rewrite H28 in Hev1'.
      inverts H30; inverts Hev2'; inverts Hev1'.
      assert (Heq: x2 = mpaxl).
      { lets Hl1: mapstoval_load Hmatch1 H3.
        eapply lmachLib.load_mem_mono with (M' := x6) in Hl1.
        2 : { unfold Maps.sub. 
              eapply perm_map_lemmas_part2.mem_sub_join_sub with (m2 := x5); eauto.
              eapply join_comm; eauto.
              eapply perm_map_lemmas_part2.mem_sub_join_sub; try eapply join_comm; eauto.
              unfolds; eexists; join auto.
       }
       rewrite Int.unsigned_repr in Hl1.
       rewrite H37 in Hl1.
       inverts Hl1.
       auto.
       clear -H32. int auto.
       }
       subst x2.

        assert (Hmx: minus x6 x11 = minus x6 mx6).
         { sep lifts (7::6::5::4::3::2::1::8::nil)%nat in H13.

           simpl in H13. simpljoin.
           do 5 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H85.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in H80.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in H75.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in H70.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in H63.

           rewrite Z.add_0_r in *.
           lets Hm1: mapstoval_minus_eq_emp_alt H95 H38.
           destruct Hm1 as (Hm1 & Hf1).
           simpl; auto.
           lets Hm2: mapstoval_minus_eq_emp_alt H90 H39.
           destruct Hm2 as (Hm2 & Hf2).
           simpl; auto.
           lets Hm3: mapstoval_minus_eq_emp_alt H85 H40.
           destruct Hm3 as (Hm3 & Hf3).
           simpl; auto.
           lets Hm4: mapstoval_minus_eq_emp_alt H80 H41.
           destruct Hm4 as (Hm4 & Hf4).
           simpl; auto.
           lets Hm5: mapstoval_minus_eq_emp_alt H75 H42.
           destruct Hm5 as (Hm5 & Hf5).
           simpl; auto.
           lets Hm6: mapstoval_minus_eq_emp_alt H70 H43.
           destruct Hm6 as (Hm6 & Hf6).
           simpl; auto.
           lets Hm7: mapstoval_minus_eq_emp_alt H63 H44.
           destruct Hm7 as (Hm7 & Hf7).
           simpl; auto.
           eapply map_join_merge' in H45, H57, H58, H59, H60, H61, H62.
           eapply map_join_merge' in H4, H67, H72, H77, H82, H87, H92.
           subst.
           rewrite jl_merge_emp.
           repeat try (apply minus_merge); eauto;
           try solve [eapply minus_same_emp'; eauto].
          }
          lets Hmx1: H62. eapply join_comm in Hmx1.
           eapply join_eq_minus in Hmx1.

          assert (Hmx2:  merge x12 (merge x (merge Ms Mf)) = minus x6 x11).
          { eapply join_eq_minus. 
            eapply join_comm.
            repeat try (eapply join_merge23';eauto).
            eapply join_comm; eauto.
          }
        assert (Hmx3: merge (merge (merge Mf Ms) x) x12  = minus x6 x11).
        { eapply join_eq_minus.
           repeat try (eapply join_join_join_merge; try solve [eapply join_comm; eauto]).
           auto.
          }

          assert (Hsub1: Maps.sub (merge Ms Mf) mx).
          {  rewrite Hmx in Hmx2; rewrite <- Hmx1 in Hmx2.
            rewrite <- Hmx2.
            eapply sub_trans.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            instantiate (1:= x).
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            instantiate (1:= x5).
            eapply perm_map_lemmas_part2.join_sub_sub_merge.
            eapply join_comm; eauto.
            unfolds. eexists. join auto.
            unfolds. eexists. join auto.
            eapply disjoint_sym.
            unfolds. eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            eapply mem_join_disjoint_disjoint.
            eapply join_comm; eauto.
            eapply map_join_merge' in H10.
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            eapply sub_refl.
            unfolds. eexists; eauto.
            subst.
            eapply map_join_merge' in H0. subst.
            eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'; eauto.
            eapply disjoint_sym.
            unfolds. eexists. join auto.
          }
          assert (Hj1:disjoint Ms Mf).
          { eapply join_join_disj_r; eauto.
          }

          assert (Hsub2: Maps.sub Ms mx).
          { eapply sub_trans; eauto.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'.
            eapply sub_refl. auto.
          }
          assert (Hsub3: Maps.sub Mf mx).
          { 
            eapply sub_trans.
            2 : eapply Hsub1.
            eapply join_sub_r.
            eapply join_merge_disj; eauto.
          }
          eapply eq_sym in Hmx1.

  (* disjoint *)
  assert (Hd1: disjoint Mf x /\ disjoint Mf x0 /\ disjoint Mf x12).
            { splits.
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_l; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
                }
              -{ eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
             }

             assert (Hd2 : disjoint Ms x /\ disjoint Ms x0 /\ disjoint Ms x12).
              { splits.
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_l; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                  }
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
                -{ eapply disj_trans_sub with (m2 := x0).
                   eapply join_sub_r; eauto.
                   eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
              }

             destruct Hd1 as (Hd1'&Hd2'&Hd3').
             destruct Hd2 as (Hd4'&Hd5'&Hd6').

             assert (Hd3 : disjoint x x12).
             { eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply my_join_disj; eauto.
             }
           assert (Histrue: 
                        forall (a : HalfPermMap.A) (b0 : bool) (v : HalfPermMap.C),
                                x a = Some (b0, v) -> b0 = true).
            {  lets Heq: mapstoval_minus_eq_emp_alt H3 H3.
                destruct Heq; auto.
                introv Hs.
                specialize H4 with (x:= a).
                rewrite Hs in *.
                destruct H4 as [(v1 & v2 & Heq & _) | (Heq & _)]; inverts Heq.
                auto.
             }

             assert (Hdm1: disjoint (merge Mf Ms) x).
              { eapply disjoint_merge_imp; eauto. }

            assert (Hc: merge Ms Mf = merge Mf Ms).
             {  eapply disjoint_merge_sym; eauto. }

            assert (Hd4 : disjoint (merge Mf Ms) x12).
             { lets Hj1': H66.
               lets Hj2': H64.
               assert(Hj':join x17 (merge Ms Mf) x6).
               eapply join_merge23; eauto.
               eapply my_join_disj in Hj'.
               rewrite Hc in Hj'.
               eapply disjoint_sym in Hj'.
               eapply disj_trans_sub with (m2:= x0).
               eapply join_sub_r; eauto.
               eapply disj_trans_sub with (m2 := x17).
               eapply join_sub_r; eauto.
               auto.
             }

            assert (Hd5 : disjoint (merge (merge Mf Ms) x) x12).
             { eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'.
                2:{ eapply join_comm. eapply join_merge_disj; eauto. }
                eapply disjoint_sym.
                eapply disjoint_merge_imp.
                auto.
                eapply disjoint_sym; eauto.
                eapply disjoint_sym; eauto.
                auto.
             }
  (* end of disjoint *)

          assert (Hsub4: Maps.sub x mx).
          {
            rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'; eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
          }
          assert (Hsub5: Maps.sub x12 mx).
          { rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
           }

          assert (Hmeq: minus (minus M' Ms) Mf = minus M' (merge Ms Mf)).
        { eapply perm_map_lemmas_part2.mem_join_minus.
           eapply join_comm.
           eapply join_join_join_merge.
           2:{ eapply join_sub_minus.
                 eapply join_join_sub_minus.
                 2:{ eapply join_comm. 
                       eapply join_merge_disj; eauto. }
               eapply sub_sem'; eauto.
              eapply sub_trans; eauto.
             unfold Maps.sub. eexists. 
              eapply join_comm; eauto.
            }
           eapply join_sub_minus.
           eapply sub_trans; eauto.
           unfold Maps.sub. eexists. 
           eapply join_comm; eauto.
         }

      eexists. exists n. exists (Vint32 index). exists aop.
      exists OO.
      exists (set OO evstructheapid 
               (evstructheap (Set_struct strheap (b, y) MSMC_SMSMPAXL (get_mpax_struct mpaxl 
                 (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil))))).
      exists (x3, x4, ( minus (minus M' Ms) Mf), x7, x8, x10).
      eexists Ms.
      exists (set O evstructheapid
     (evstructheap
        (Set_struct strheap (b, y) MSMC_SMSMPAXL
           (get_mpax_struct mpaxl
              (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil))))).
      exists Os.
      exists (b, y).
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         
         lets Hsg: H17.
         eapply OSAbstMod.join_sig_get in Hsg.
         eexists (evstructheap strheap).
          
         eapply OSAbstMod.join_get_r in Hsg.
         2: eauto.
         eapply OSAbstMod.join_get_r in Hsg; eauto.
         
       -  unfolds.
          eexists.
          splits; unfold joinmem; do 7 eexists; splits;eauto.
          2 : {eapply join_join_minus.
               eapply join_comm; eauto. 
               subst mx. rewrite <- Hmx.
               lets Hcp: H64.
               eapply join_comm in Hcp; eapply join_eq_minus in Hcp; subst.
               eapply mem_join_sub_join_minus_minus.
               join auto. unfolds; eauto.
                }

          eapply join_comm.
          eapply mem_sub_sub_disjoint_join_minus1 with (m1 := Ms); eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply old.Unnamed_thm.
      -  eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      -  unfold satp. intros.
         apply HPlinv.
         unfold emposabst in H26.
         subst.
         eapply join_emp_eq in H22.
         subst.

         exists ( get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)).
         exists (Set_struct strheap (b, y) MSMC_SMSMPAXL
       (get_mpax_struct mpaxl
          (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_smsmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

  (* end of disjoint *) 
      (* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {
              assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
             {   rewrite Hmeq.
                 eapply perm_map_lemmas_part2.mem_join_minus.
                 eapply join_join_join_merge.
                 eapply join_join_join_merge.
                 eauto.
                 rewrite <- Hmx. rewrite <- Hmx3.
                 eapply join_comm. eapply join_merge_disj.
                 2: { eapply join_comm.
                      rewrite Hc.
                      eapply join_merge_disj; eauto.
                    }
                 auto.
               }
              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }
       (* start prove changed struct MSMC_SMSMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
      (* end of prove changed struct MSMC_SMSMPAXL *)


(*last goal: <_ msim*)
      - constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv.
           unfold emposabst in H26.
           subst.
           eapply join_emp_eq in H22.
           subst.

(* (o,O,aop)|=(CurLINV pa t)) *)
        { exists ( get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)).
         exists (Set_struct strheap (b, y) MSMC_SMSMPAXL
       (get_mpax_struct mpaxl
          (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_smsmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
             }

              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }


(* start prove changed struct MSMC_SMSMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
(* end of prove changed struct MSMC_SMSMPAXL *)
      }


(* (o,O,aop)|=lift (<||aop||> ** (...)) *)
    { unfold lift.
      sep lift 2%nat.
      sep normal.

      unfold emposabst in H26.
      subst.
      eapply join_emp_eq in H22.
      subst.
(* (o,O,aop)|=(CurLINV pa t)) *)
       exists ( get_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)).
       exists (Set_struct strheap (b, y) MSMC_SMSMPAXL
     (get_mpax_struct mpaxl
        (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil))).
      sep split; eauto.
      2 : { split; auto. 
            apply get_mpax_struct_smsmpaxl_match. }

       rewrite Hmeq.
       sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
       sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
       simpl.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       eapply join_comm.
       eapply map_join_set_none.
       eapply join_comm; eauto.
       eapply get_a_sig_a'.
       introv Hf; try false.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       rewrite <- set_sig with (b:= (evstructheap strheap) ).
       eapply map_join_set_none.
       join auto.
      
(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
       rewrite <- ml_eq.
       eapply merge_sem_none3; eauto.
       eapply get_join_none; eauto.
       rewrite OSAbstMod.map_get_sig; eauto.
       eapply get_join_none; try  eapply join_comm; eauto.
       eapply OSAbstMod.join_sig_get; eauto.

       do 6 eexists. splits; eauto.
       2: { eapply old.Unnamed_thm.
          }
       
       2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
       {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
            }
            rewrite <- Heq.
            eapply join_comm. eapply join_merge_disj.
            eapply disjoint_merge_imp.
            2: eapply disjoint_sym; eauto.
            { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
            { eapply disjoint_sym.
               eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
              auto.
        }
        (* end of join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

       do 6 eexists. splits; eauto.
       3: { eapply change_aop_rule; eauto. }
       2: { rewrite <- ml_eq.
               eapply join_join_merge; eauto.
               eapply join_comm; eauto.
          }
       { instantiate (1:= mx6'). 
         eapply join_emp_eq in H15, H20; subst.
         eapply join_comm.
         eapply join_merge_disj.
         eapply disjoint_sym.
         eapply mem_sub_disj; eauto.
         eapply disjoint_sym.
         unfolds; eauto.
       }


(* start prove changed struct MSMC_SMSMPAXL *)
       { subst.
         simpl Astruct.

         do 4 rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
         change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

         sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
         simpl.
(* Aemp *)
         exists (empmem). do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
         exists M7'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
         exists M6'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
         exists M5'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
         exists M4'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
         exists M3'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
         exists M2'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
         rewrite Z.add_0_r in *.
         eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
         unfold emposabst.
         simpl in H13.
         simpljoin.
         join auto.
       }
(* end of prove changed struct MSMC_SMSMPAXL *)
     }

    ++ intros. 
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso. 
       apply Hhf. 
       cbv. eauto.

       Unshelve.
       exact Vnull.
Qed.


Lemma csl_msmc_getSESMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 e3 n m q aop pa t index ses mpaxl mpaxh vl strheap,
                  can_change_aop P' ->
                  (Z.of_nat n <= Int.max_unsigned)%Z ->
                  m = Vint32 index ->
                  (0 <= Int.unsigned index < 8)%Z ->
                  rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
                  rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
                  SesMod.get ses index = Some (mpaxl, mpaxh) ->
                  P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                             Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SESMPAXL == Vptr q ->
                  P ==> PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                              Aabsdata ses_mpaxid (osses_mpax ses) ** 
                              Astruct q MSMC_SESMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                              [| Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) /\ struct_type_vallist_match MSMC_SESMPAXL vl |] ** P' ->
                  (EX vl' strheap' , 
                           PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                           Aabsdata ses_mpaxid (osses_mpax ses) ** 
                           Astruct q MSMC_SESMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') ** 
                           [| vl' = get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) |] **
                            [| strheap' = Set_struct strheap q MSMC_SESMPAXL vl' /\ struct_type_vallist_match MSMC_SESMPAXL vl' |] ** P') ==> CurLINV pa t ->
                  RuleSem Spec sd pa I r ri
                    (<|| (csl_msmc_getSESMPAXL n m q);; aop ||> ** P)
                    (sprim (scsl_msmc_getSESMPAXL e1 e2 e3))  
                    (<|| aop ||>  ** 
                      EX vl' strheap', 
                           PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                           Aabsdata ses_mpaxid (osses_mpax ses) ** 
                           Astruct q MSMC_SESMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') **
                           [| vl' = get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) |] **
                            [| strheap' = Set_struct strheap q MSMC_SESMPAXL vl' /\ struct_type_vallist_match MSMC_SESMPAXL vl' |] ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange Hmatch1 Hmatch2 Hses HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct Hsat as [Hsat1  Hsat2].
   destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1. 
  simpl in H. subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H27; 
  try (destruct v; destruct H27 as (Heq&H27); inverts Heq); tryfalse).
  destruct (Int.unsigned i0 <=? Byte.max_unsigned)%Z eqn:eq0;tryfalse.
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  unfolds in H30. subst x2.
  apply join_lib.join_emp_eq in H2. subst x3.
  apply join_lib.join_emp_eq in H5. subst x6.
  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds.
      do 4 eexists; eauto.

  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt. unfold not. intros. apply H1. clear H1.
     destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as ?.
     apply joinm2_mem_join in Hjm1 as ?.
     destruct H1. simpl in H1,H6. destruct H4 as [? [_ ?]]. subst G2 E2.
     unfold getmem in H4. simpl in H4.
     lets HH : store_exist_join H3 H0 H4.
     apply join_lib.join_emp. auto.
     destruct HH. destruct q.

     simpl in H13. simpljoin.

     do 5 rewrite Int.add_assoc in *.
     change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in m3.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in m2.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in m1.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in m0.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in m.

     lets Hm5 : m5.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_raddr))) (M3:= x3) in Hm5.
     2:{ join auto. }
     destruct Hm5 as (x3' & Hm5).
     lets Hm4 : m4.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_sr))) (M3:= x10) in Hm4.
     2:{ join auto. }
     destruct Hm4 as (x10' & Hm4).
     lets Hm3: m3.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_sw))) (M3:= x22) in Hm3.
     2:{ join auto. }
     destruct Hm3 as (x22' & Hm3).
     lets Hm2 : m2.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_sx))) (M3:= x31) in Hm2.
     2:{ join auto. }
     destruct Hm2 as (x31' & Hm2).
     lets Hm1 : m1.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_ur))) (M3:= x37) in Hm1.
     2:{ join auto. }
     destruct Hm1 as (x37' & Hm1).
     lets Hm0 : m0.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_uw))) (M3:= x43) in Hm0.
     2:{ join auto. }
     destruct Hm0 as (x43' & Hm0).
     lets Hm : m.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl sesl_ux))) (M3:= x49) in Hm.
     2:{ join auto. }
     destruct Hm as (x49' & Hm).

    assert (Hmx: exists mx mx1 mx2 mx3 mx4 mx5 mx6,
                 join x10 x3 mx1 /\ join x22 mx1 mx2 /\ join x31 mx2 mx3 /\
                 join x37 mx3 mx4 /\ join x43 mx4 mx5 /\ join x49 mx5 mx6 /\
                 join mx mx6 M2).
    { do 7 eexists.
      splits. join auto.
      instantiate (1:= (merge_list (x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x49 :: x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x12 :: x :: x1 :: nil))). join auto.
    }
   destruct Hmx as ( mx & mx1 & mx2 & mx3 & mx4 & mx5 & mx6 & Hmx).
   destruct Hmx as (Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj6 & Hj ).

  assert (Hd1: disjoint x10' x3').
  { eapply disj_store_disj; eauto.
    eapply disjoint_sym.
    eapply disj_store_disj; eauto.
    eapply join_disj. eapply join_comm. eauto.
  }
  lets Hj1': Hd1. destruct Hj1' as (mx1' & Hj1').

  assert (Hd2: disjoint x22' mx1').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx2 mx1 = minus mx2 mx1').
    { eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]].
    }
    lets Hmin: Hj2.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj2': Hd2. destruct Hj2' as (mx2' & Hj2').

  assert (Hd3: disjoint x31' mx2').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx3 mx2 = minus mx3 mx2').
    { do 2 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj3.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj3': Hd3. destruct Hj3' as (mx3' & Hj3').

  assert (Hd4: disjoint x37' mx3').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx4 mx3 = minus mx4 mx3').
    { do 3 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj4.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj4': Hd4. destruct Hj4' as (mx4' & Hj4').

  assert (Hd5: disjoint x43' mx4').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx5 mx4 = minus mx5 mx4').
    { do 4 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj5.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj5': Hd5. destruct Hj5' as (mx5' & Hj5').

  assert (Hd6: disjoint x49' mx5').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx6 mx5 = minus mx6 mx5').
    { do 5 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj6.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj6': Hd6. destruct Hj6' as (mx6' & Hj6').

  assert (Hd: disjoint mx mx6').
  { 
    assert (Heq: minus M2 mx6 = minus M2 mx6').
    { do 6 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj': Hd. destruct Hj' as (M2' & Hj').

     do 2 eexists. unfold nilcont in *.
     eapply csl_msmc_getSESMPAXL_step; auto.
     - erewrite evaltype_irrev_mem; eauto.
     - erewrite evaltype_irrev_mem; eauto.
     - erewrite evaltype_irrev_mem; eauto.
     - lets Hnew: evalval_mono' H4 H.  eauto. 
     - lets Hnew: evalval_mono H4 H2. rewrite Hnew.  eauto.
     - lets Hnew: evalval_mono H4 H5. rewrite Hnew.  eauto.
     - congruence.
     - congruence.
     - congruence.
     - instantiate (1 := mpaxl).
       eapply load_local with (m1:= M); eauto.
       eapply load_local; eauto.
       rewrite Int.unsigned_repr in H3.
       eapply mapstoval_load; eauto.
       clear -H31 H32.
       change Int.max_unsigned with 4294967295%Z. auto with zarith.
     - rewrite Z.add_0_r.
       unfold mapstoval, opsem.mapstoval in *.
       eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - splits; eauto. join auto.
     - rewrite Z.add_0_r. eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - splits; eauto. unfold merge_list. rewrite jl_merge_emp.
       join auto.
  +   simpl substaskst in *. 
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
      lets Hev3: H5.
      lets Hlem: evalval_mono_joinmem.
      specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
      simpl get_smem in Hlem.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H2.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H1, H4.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.
      rewrite Hev3' in H30.
      rewrite H29 in Hev2'.
      rewrite H28 in Hev1'.
      inverts H30; inverts Hev2'; inverts Hev1'.
      assert (Heq: x2 = mpaxl).
      { lets Hl1: mapstoval_load Hmatch1 H3.
        eapply lmachLib.load_mem_mono with (M' := x6) in Hl1.
        2 : { unfold Maps.sub. 
              eapply perm_map_lemmas_part2.mem_sub_join_sub with (m2 := x5); eauto.
              eapply join_comm; eauto.
              eapply perm_map_lemmas_part2.mem_sub_join_sub; try eapply join_comm; eauto.
              unfolds; eexists; join auto.
       }
       rewrite Int.unsigned_repr in Hl1.
       rewrite H37 in Hl1.
       inverts Hl1.
       auto.
       clear -H32. int auto.
       }
       subst x2.

        assert (Hmx: minus x6 x11 = minus x6 mx6).
         { sep lifts (7::6::5::4::3::2::1::8::nil)%nat in H13.

           simpl in H13. simpljoin.
           do 5 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H85.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in H80.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in H75.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in H70.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in H63.

           rewrite Z.add_0_r in *.
           lets Hm1: mapstoval_minus_eq_emp_alt H95 H38.
           destruct Hm1 as (Hm1 & Hf1).
           simpl; auto.
           lets Hm2: mapstoval_minus_eq_emp_alt H90 H39.
           destruct Hm2 as (Hm2 & Hf2).
           simpl; auto.
           lets Hm3: mapstoval_minus_eq_emp_alt H85 H40.
           destruct Hm3 as (Hm3 & Hf3).
           simpl; auto.
           lets Hm4: mapstoval_minus_eq_emp_alt H80 H41.
           destruct Hm4 as (Hm4 & Hf4).
           simpl; auto.
           lets Hm5: mapstoval_minus_eq_emp_alt H75 H42.
           destruct Hm5 as (Hm5 & Hf5).
           simpl; auto.
           lets Hm6: mapstoval_minus_eq_emp_alt H70 H43.
           destruct Hm6 as (Hm6 & Hf6).
           simpl; auto.
           lets Hm7: mapstoval_minus_eq_emp_alt H63 H44.
           destruct Hm7 as (Hm7 & Hf7).
           simpl; auto.
           eapply map_join_merge' in H45, H57, H58, H59, H60, H61, H62.
           eapply map_join_merge' in H4, H67, H72, H77, H82, H87, H92.
           subst.
           rewrite jl_merge_emp.
           repeat try (apply minus_merge); eauto;
           try solve [eapply minus_same_emp'; eauto].
          }
          lets Hmx1: H62. eapply join_comm in Hmx1.
           eapply join_eq_minus in Hmx1.

          assert (Hmx2:  merge x12 (merge x (merge Ms Mf)) = minus x6 x11).
          { eapply join_eq_minus. 
            eapply join_comm.
            repeat try (eapply join_merge23';eauto).
            eapply join_comm; eauto.
          }
        assert (Hmx3: merge (merge (merge Mf Ms) x) x12  = minus x6 x11).
        { eapply join_eq_minus.
           repeat try (eapply join_join_join_merge; try solve [eapply join_comm; eauto]).
           auto.
          }

          assert (Hsub1: Maps.sub (merge Ms Mf) mx).
          {  rewrite Hmx in Hmx2; rewrite <- Hmx1 in Hmx2.
            rewrite <- Hmx2.
            eapply sub_trans.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            instantiate (1:= x).
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            instantiate (1:= x5).
            eapply perm_map_lemmas_part2.join_sub_sub_merge.
            eapply join_comm; eauto.
            unfolds. eexists. join auto.
            unfolds. eexists. join auto.
            eapply disjoint_sym.
            unfolds. eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            eapply mem_join_disjoint_disjoint.
            eapply join_comm; eauto.
            eapply map_join_merge' in H10.
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            eapply sub_refl.
            unfolds. eexists; eauto.
            subst.
            eapply map_join_merge' in H0. subst.
            eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'; eauto.
            eapply disjoint_sym.
            unfolds. eexists. join auto.
          }
          assert (Hj1:disjoint Ms Mf).
          { eapply join_join_disj_r; eauto.
          }

          assert (Hsub2: Maps.sub Ms mx).
          { eapply sub_trans; eauto.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'.
            eapply sub_refl. auto.
          }
          assert (Hsub3: Maps.sub Mf mx).
          { 
            eapply sub_trans.
            2 : eapply Hsub1.
            eapply join_sub_r.
            eapply join_merge_disj; eauto.
          }
          eapply eq_sym in Hmx1.

  (* disjoint *)
  assert (Hd1: disjoint Mf x /\ disjoint Mf x0 /\ disjoint Mf x12).
            { splits.
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_l; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
                }
              -{ eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
             }

             assert (Hd2 : disjoint Ms x /\ disjoint Ms x0 /\ disjoint Ms x12).
              { splits.
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_l; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                  }
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
                -{ eapply disj_trans_sub with (m2 := x0).
                   eapply join_sub_r; eauto.
                   eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
              }

             destruct Hd1 as (Hd1'&Hd2'&Hd3').
             destruct Hd2 as (Hd4'&Hd5'&Hd6').

             assert (Hd3 : disjoint x x12).
             { eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply my_join_disj; eauto.
             }
           assert (Histrue: 
                        forall (a : HalfPermMap.A) (b0 : bool) (v : HalfPermMap.C),
                                x a = Some (b0, v) -> b0 = true).
            {  lets Heq: mapstoval_minus_eq_emp_alt H3 H3.
                destruct Heq; auto.
                introv Hs.
                specialize H4 with (x:= a).
                rewrite Hs in *.
                destruct H4 as [(v1 & v2 & Heq & _) | (Heq & _)]; inverts Heq.
                auto.
             }

             assert (Hdm1: disjoint (merge Mf Ms) x).
              { eapply disjoint_merge_imp; eauto. }

            assert (Hc: merge Ms Mf = merge Mf Ms).
             {  eapply disjoint_merge_sym; eauto. }

            assert (Hd4 : disjoint (merge Mf Ms) x12).
             { lets Hj1': H66.
               lets Hj2': H64.
               assert(Hj':join x17 (merge Ms Mf) x6).
               eapply join_merge23; eauto.
               eapply my_join_disj in Hj'.
               rewrite Hc in Hj'.
               eapply disjoint_sym in Hj'.
               eapply disj_trans_sub with (m2:= x0).
               eapply join_sub_r; eauto.
               eapply disj_trans_sub with (m2 := x17).
               eapply join_sub_r; eauto.
               auto.
             }

            assert (Hd5 : disjoint (merge (merge Mf Ms) x) x12).
             { eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'.
                2:{ eapply join_comm. eapply join_merge_disj; eauto. }
                eapply disjoint_sym.
                eapply disjoint_merge_imp.
                auto.
                eapply disjoint_sym; eauto.
                eapply disjoint_sym; eauto.
                auto.
             }
  (* end of disjoint *)

          assert (Hsub4: Maps.sub x mx).
          {
            rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'; eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
          }
          assert (Hsub5: Maps.sub x12 mx).
          { rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
           }

          assert (Hmeq: minus (minus M' Ms) Mf = minus M' (merge Ms Mf)).
        { eapply perm_map_lemmas_part2.mem_join_minus.
           eapply join_comm.
           eapply join_join_join_merge.
           2:{ eapply join_sub_minus.
                 eapply join_join_sub_minus.
                 2:{ eapply join_comm. 
                       eapply join_merge_disj; eauto. }
               eapply sub_sem'; eauto.
              eapply sub_trans; eauto.
             unfold Maps.sub. eexists. 
              eapply join_comm; eauto.
            }
           eapply join_sub_minus.
           eapply sub_trans; eauto.
           unfold Maps.sub. eexists. 
           eapply join_comm; eauto.
         }

      eexists. exists n. exists (Vint32 index). exists aop.
      exists OO.
      exists (set OO evstructheapid 
               (evstructheap (Set_struct strheap (b, y) MSMC_SESMPAXL (get_mpax_struct mpaxl 
                 (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))))).
      exists (x3, x4, ( minus (minus M' Ms) Mf), x7, x8, x10).
      eexists Ms.
      exists (set O evstructheapid
     (evstructheap
        (Set_struct strheap (b, y) MSMC_SESMPAXL
           (get_mpax_struct mpaxl
              (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))))).
      exists Os.
      exists (b, y).
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         
         lets Hsg: H17.
         eapply OSAbstMod.join_sig_get in Hsg.
         eexists (evstructheap strheap).
          
         eapply OSAbstMod.join_get_r in Hsg.
         2: eauto.
         eapply OSAbstMod.join_get_r in Hsg; eauto.
         
       -  unfolds.
          eexists.
          splits; unfold joinmem; do 7 eexists; splits;eauto.
          2 : {eapply join_join_minus.
               eapply join_comm; eauto. 
               subst mx. rewrite <- Hmx.
               lets Hcp: H64.
               eapply join_comm in Hcp; eapply join_eq_minus in Hcp; subst.
               eapply mem_join_sub_join_minus_minus.
               join auto. unfolds; eauto.
                }

          eapply join_comm.
          eapply mem_sub_sub_disjoint_join_minus1 with (m1 := Ms); eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply old.Unnamed_thm.
      -  eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      -  unfold satp. intros.
         apply HPlinv.
         unfold emposabst in H26.
         subst.
         eapply join_emp_eq in H22.
         subst.

         exists ( get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)).
         exists (Set_struct strheap (b, y) MSMC_SESMPAXL
       (get_mpax_struct mpaxl
          (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_sesmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

  (* end of disjoint *) 
      (* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {
              assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
             {   rewrite Hmeq.
                 eapply perm_map_lemmas_part2.mem_join_minus.
                 eapply join_join_join_merge.
                 eapply join_join_join_merge.
                 eauto.
                 rewrite <- Hmx. rewrite <- Hmx3.
                 eapply join_comm. eapply join_merge_disj.
                 2: { eapply join_comm.
                      rewrite Hc.
                      eapply join_merge_disj; eauto.
                    }
                 auto.
               }
              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }
       (* start prove changed struct MSMC_SESMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
      (* end of prove changed struct MSMC_SESMPAXL *)


(*last goal: <_ msim*)
      - constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv.
           unfold emposabst in H26.
           subst.
           eapply join_emp_eq in H22.
           subst.

(* (o,O,aop)|=(CurLINV pa t)) *)
        { exists ( get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)).
         exists (Set_struct strheap (b, y) MSMC_SESMPAXL
       (get_mpax_struct mpaxl
          (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_sesmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
             }

              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }


(* start prove changed struct MSMC_SESMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
(* end of prove changed struct MSMC_SMSMPAXL *)
      }


(* (o,O,aop)|=lift (<||aop||> ** (...)) *)
    { unfold lift.
      sep lift 2%nat.
      sep normal.

      unfold emposabst in H26.
      subst.
      eapply join_emp_eq in H22.
      subst.
(* (o,O,aop)|=(CurLINV pa t)) *)
       exists ( get_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)).
       exists (Set_struct strheap (b, y) MSMC_SESMPAXL
     (get_mpax_struct mpaxl
        (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil))).
      sep split; eauto.
      2 : { split; auto. 
            apply get_mpax_struct_sesmpaxl_match. }

       rewrite Hmeq.
       sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
       sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
       simpl.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       eapply join_comm.
       eapply map_join_set_none.
       eapply join_comm; eauto.
       eapply get_a_sig_a'.
       introv Hf; try false.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       rewrite <- set_sig with (b:= (evstructheap strheap) ).
       eapply map_join_set_none.
       join auto.
      
(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
       rewrite <- ml_eq.
       eapply merge_sem_none3; eauto.
       eapply get_join_none; eauto.
       rewrite OSAbstMod.map_get_sig; eauto.
       eapply get_join_none; try  eapply join_comm; eauto.
       eapply OSAbstMod.join_sig_get; eauto.

       do 6 eexists. splits; eauto.
       2: { eapply old.Unnamed_thm.
          }
       
       2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
       {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
            }
            rewrite <- Heq.
            eapply join_comm. eapply join_merge_disj.
            eapply disjoint_merge_imp.
            2: eapply disjoint_sym; eauto.
            { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
            { eapply disjoint_sym.
               eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
              auto.
        }
        (* end of join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

       do 6 eexists. splits; eauto.
       3: { eapply change_aop_rule; eauto. }
       2: { rewrite <- ml_eq.
               eapply join_join_merge; eauto.
               eapply join_comm; eauto.
          }
       { instantiate (1:= mx6'). 
         eapply join_emp_eq in H15, H20; subst.
         eapply join_comm.
         eapply join_merge_disj.
         eapply disjoint_sym.
         eapply mem_sub_disj; eauto.
         eapply disjoint_sym.
         unfolds; eauto.
       }


(* start prove changed struct MSMC_SMSMPAXL *)
       { subst.
         simpl Astruct.

         do 4 rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
         change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

         sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
         simpl.
(* Aemp *)
         exists (empmem). do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
         exists M7'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
         exists M6'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
         exists M5'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
         exists M4'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
         exists M3'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
         exists M2'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
         rewrite Z.add_0_r in *.
         eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
         unfold emposabst.
         simpl in H13.
         simpljoin.
         join auto.
       }
(* end of prove changed struct MSMC_SESMPAXL *)
     }

    ++ intros. 
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso. 
       apply Hhf. 
       cbv. eauto.

       Unshelve.
       exact Vnull.
Qed.


Lemma csl_xmc_getXMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 n q aop pa t index xmc mpaxl mpaxh vl strheap,
                  can_change_aop P' ->
                  n = Vint32 index ->
                  (0 <= Int.unsigned index < 16)%Z ->
                  rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
                  rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
                  XmcMod.get xmc index = Some (mpaxl, mpaxh) ->
                  P ==> Rv e1 @ Tint32 ==  n //\\ Rv e2 @ Tptr XMC_XMPAXL == Vptr q ->
                  P ==> PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                              Aabsdata xmpaxid (osxmpax xmc) ** 
                              Astruct q XMC_XMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                              [| Get_struct strheap q = Some (q, XMC_XMPAXL, vl) /\ struct_type_vallist_match XMC_XMPAXL vl |] ** P' ->
                  (EX vl' strheap' , 
                           PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                           Aabsdata xmpaxid (osxmpax xmc) ** 
                           Astruct q XMC_XMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') ** 
                           [| vl' = get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) |] **
                            [| strheap' = Set_struct strheap q XMC_XMPAXL vl' /\ struct_type_vallist_match XMC_XMPAXL vl' |] ** P') ==> CurLINV pa t ->
                  RuleSem Spec sd pa I r ri
                    (<|| (csl_xmc_getXMPAXL n q);; aop ||> ** P)
                    (sprim (scsl_xmc_getXMPAXL e1 e2))  
                    (<|| aop ||>  ** 
                      EX vl' strheap', 
                           PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                           Aabsdata xmpaxid (osxmpax xmc) ** 
                           Astruct q XMC_XMPAXL vl' ** Aabsdata evstructheapid (evstructheap strheap') **
                           [| vl' = get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) |] **
                            [| strheap' = Set_struct strheap q XMC_XMPAXL vl' /\ struct_type_vallist_match XMC_XMPAXL vl' |] ** P' ) t.
Proof.
  introv Haop Hindex Hrange Hmatch1 Hmatch2 Hxmc HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct Hsat as [Hsat1  Hsat2].
   destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1. 
  simpl in H. subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H27; 
  try (destruct v; destruct H27 as (Heq&H27); inverts Heq); tryfalse).
  destruct (Int.unsigned i0 <=? Byte.max_unsigned)%Z eqn:eq0;tryfalse.
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  unfolds in H30. subst x2.
  apply join_lib.join_emp_eq in H2. subst x3.
  apply join_lib.join_emp_eq in H5. subst x6.
  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds.
      do 4 eexists; eauto.

  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt. unfold not. intros. apply H1. clear H1.
     destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as ?.
     apply joinm2_mem_join in Hjm1 as ?.
     destruct H1. simpl in H1,H6. destruct H4 as [? [_ ?]]. subst G2 E2.
     unfold getmem in H4. simpl in H4.
     lets HH : store_exist_join H3 H0 H4.
     apply join_lib.join_emp. auto.
     destruct HH. destruct q.

     simpl in H13. simpljoin.

     do 5 rewrite Int.add_assoc in *.
     change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in m3.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in m2.
     change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in m1.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in m0.
     change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                   (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in m.

     lets Hm5 : m5.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_raddr))) (M3:= x3) in Hm5.
     2:{ join auto. }
     destruct Hm5 as (x3' & Hm5).
     lets Hm4 : m4.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_sr))) (M3:= x10) in Hm4.
     2:{ join auto. }
     destruct Hm4 as (x10' & Hm4).
     lets Hm3: m3.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_sw))) (M3:= x22) in Hm3.
     2:{ join auto. }
     destruct Hm3 as (x22' & Hm3).
     lets Hm2 : m2.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_sx))) (M3:= x31) in Hm2.
     2:{ join auto. }
     destruct Hm2 as (x31' & Hm2).
     lets Hm1 : m1.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_ur))) (M3:= x37) in Hm1.
     2:{ join auto. }
     destruct Hm1 as (x37' & Hm1).
     lets Hm0 : m0.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_uw))) (M3:= x43) in Hm0.
     2:{ join auto. }
     destruct Hm0 as (x43' & Hm0).
     lets Hm : m.
     eapply store_exist_join' with (y := (Vint32 (get_mpax mpaxl xmc_ux))) (M3:= x49) in Hm.
     2:{ join auto. }
     destruct Hm as (x49' & Hm).

    assert (Hmx: exists mx mx1 mx2 mx3 mx4 mx5 mx6,
                 join x10 x3 mx1 /\ join x22 mx1 mx2 /\ join x31 mx2 mx3 /\
                 join x37 mx3 mx4 /\ join x43 mx4 mx5 /\ join x49 mx5 mx6 /\
                 join mx mx6 M2).
    { do 7 eexists.
      splits. join auto.
      instantiate (1:= (merge_list (x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x49 :: x43 :: x37 :: x31 :: x22 :: x10 :: x3 :: nil))). join auto.
      instantiate (1:= (merge_list (x12 :: x :: x1 :: nil))). join auto.
    }
   destruct Hmx as ( mx & mx1 & mx2 & mx3 & mx4 & mx5 & mx6 & Hmx).
   destruct Hmx as (Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj6 & Hj ).

  assert (Hd1: disjoint x10' x3').
  { eapply disj_store_disj; eauto.
    eapply disjoint_sym.
    eapply disj_store_disj; eauto.
    eapply join_disj. eapply join_comm. eauto.
  }
  lets Hj1': Hd1. destruct Hj1' as (mx1' & Hj1').

  assert (Hd2: disjoint x22' mx1').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx2 mx1 = minus mx2 mx1').
    { eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]].
    }
    lets Hmin: Hj2.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj2': Hd2. destruct Hj2' as (mx2' & Hj2').

  assert (Hd3: disjoint x31' mx2').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx3 mx2 = minus mx3 mx2').
    { do 2 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj3.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj3': Hd3. destruct Hj3' as (mx3' & Hj3').

  assert (Hd4: disjoint x37' mx3').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx4 mx3 = minus mx4 mx3').
    { do 3 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj4.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj4': Hd4. destruct Hj4' as (mx4' & Hj4').

  assert (Hd5: disjoint x43' mx4').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx5 mx4 = minus mx5 mx4').
    { do 4 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj5.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj5': Hd5. destruct Hj5' as (mx5' & Hj5').

  assert (Hd6: disjoint x49' mx5').
  { eapply disj_store_disj; eauto.
    assert (Heq: minus mx6 mx5 = minus mx6 mx5').
    { do 5 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj6.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj6': Hd6. destruct Hj6' as (mx6' & Hj6').

  assert (Hd: disjoint mx mx6').
  { 
    assert (Heq: minus M2 mx6 = minus M2 mx6').
    { do 6 try (eapply minus_merge_alt; try solve [eapply map_join_merge'; eauto];
      try solve [eapply store_sub_minus_eq; eauto;
                 try solve [eapply join_sub_r; try join auto]]).
    }
    lets Hmin: Hj.
    eapply join_eq_minus in Hmin.
    subst. rewrite Heq.
    eapply mem_disjoint_minus.
  }
  lets Hj': Hd. destruct Hj' as (M2' & Hj').

     do 2 eexists. unfold nilcont in *.
     eapply csl_xmc_getXMPAXL_step; auto.
     - erewrite evaltype_irrev_mem; eauto.
     - erewrite evaltype_irrev_mem; eauto.
     - lets Hnew: evalval_mono' H4 H.  eauto. 
     - lets Hnew: evalval_mono H4 H2. rewrite Hnew.  eauto.
     - congruence.
     - congruence.
     - instantiate (1 := mpaxl).
       eapply load_local with (m1:= M); eauto.
       eapply load_local; eauto.
       rewrite Int.unsigned_repr in H3.
       eapply mapstoval_load; eauto.
       clear -H31 H32.
       change Int.max_unsigned with 4294967295%Z. auto with zarith.
     - rewrite Z.add_0_r.
       unfold mapstoval, opsem.mapstoval in *.
       eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
        eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - unfold mapstoval, opsem.mapstoval in *.
         eauto.
     - splits; eauto. join auto.
     - rewrite Z.add_0_r. eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - eauto.
     - splits; eauto. unfold merge_list. rewrite jl_merge_emp.
       join auto.
  +   simpl substaskst in *. 
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
      lets Hev2: H2.
      lets Hlem: evalval_mono_joinmem.
      specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
      simpl get_smem in Hlem.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H1, H4.
      simp join.
      simpl get_smem in Hev2 , Hev2', Hev1 , Hev1'.
      rewrite Hev2' in H21.
      rewrite H19 in Hev1'.
      inverts H21; inverts Hev2'; inverts Hev1'.
      assert (Heq: x2 = mpaxl).
      { lets Hl1: mapstoval_load Hmatch1 H3.
        eapply lmachLib.load_mem_mono with (M' := x6) in Hl1.
        2 : { unfold Maps.sub. 
              eapply perm_map_lemmas_part2.mem_sub_join_sub with (m2 := x5); eauto.
              eapply join_comm; eauto.
              eapply perm_map_lemmas_part2.mem_sub_join_sub; try eapply join_comm; eauto.
              unfolds; eexists; join auto.
       }
       rewrite Int.unsigned_repr in Hl1.
       rewrite H29 in Hl1.
       inverts Hl1.
       auto.
       clear -H32. int auto.
       }
       subst x2.

        assert (Hmx: minus x6 x11 = minus x6 mx6).
         { sep lifts (7::6::5::4::3::2::1::8::nil)%nat in H13.

           simpl in H13. simpljoin.
           do 5 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in H80.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6)  in H75.
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))) with (Int.repr 7) in H70.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1)  (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.repr 1))))) with (Int.repr 8) in H65.
           change (Int.add (Int.repr 4)  (Int.add (Int.repr 1) (Int.add (Int.repr 1)
                         (Int.add (Int.repr 1) (Int.add (Int.repr 1) (Int.repr 1)))))) with (Int.repr 9) in H59.

           rewrite Z.add_0_r in *.
           lets Hm1: mapstoval_minus_eq_emp_alt H90 H30.
           destruct Hm1 as (Hm1 & Hf1).
           simpl; auto.
           lets Hm2: mapstoval_minus_eq_emp_alt H85 H33.
           destruct Hm2 as (Hm2 & Hf2).
           simpl; auto.
           lets Hm3: mapstoval_minus_eq_emp_alt H80 H34.
           destruct Hm3 as (Hm3 & Hf3).
           simpl; auto.
           lets Hm4: mapstoval_minus_eq_emp_alt H75 H35.
           destruct Hm4 as (Hm4 & Hf4).
           simpl; auto.
           lets Hm5: mapstoval_minus_eq_emp_alt H70 H36.
           destruct Hm5 as (Hm5 & Hf5).
           simpl; auto.
           lets Hm6: mapstoval_minus_eq_emp_alt H65 H37.
           destruct Hm6 as (Hm6 & Hf6).
           simpl; auto.
           lets Hm7: mapstoval_minus_eq_emp_alt H59 H38.
           destruct Hm7 as (Hm7 & Hf7).
           simpl; auto.
           eapply map_join_merge' in H39, H51, H52, H53, H54, H55, H56.
           eapply map_join_merge' in H13, H62, H67, H72, H77, H82, H87.
           subst.
           rewrite jl_merge_emp.
           repeat try (apply minus_merge); eauto;
           try solve [eapply minus_same_emp'; eauto].
          }
          lets Hmx1: H56. eapply join_comm in Hmx1.
           eapply join_eq_minus in Hmx1.

          assert (Hmx2:  merge x12 (merge x (merge Ms Mf)) = minus x6 x11).
          { eapply join_eq_minus. 
            eapply join_comm.
            repeat try (eapply join_merge23';eauto).
            eapply join_comm; eauto.
          }
        assert (Hmx3: merge (merge (merge Mf Ms) x) x12  = minus x6 x11).
        { eapply join_eq_minus.
           repeat try (eapply join_join_join_merge; try solve [eapply join_comm; eauto]).
           auto.
          }

          assert (Hsub1: Maps.sub (merge Ms Mf) mx).
          {  rewrite Hmx in Hmx2; rewrite <- Hmx1 in Hmx2.
            rewrite <- Hmx2.
            eapply sub_trans.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            instantiate (1:= x).
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            instantiate (1:= x5).
            eapply perm_map_lemmas_part2.join_sub_sub_merge.
            eapply join_comm; eauto.
            unfolds. eexists. join auto.
            unfolds. eexists. join auto.
            eapply disjoint_sym.
            unfolds. eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r.
            eapply mem_join_disjoint_disjoint.
            eapply join_comm; eauto.
            eapply map_join_merge' in H10.
            eapply disjoint_sym.
            eapply mem_sub_merge_disjoint_merge_disjont.
            eapply sub_refl.
            unfolds. eexists; eauto.
            subst.
            eapply map_join_merge' in H0. subst.
            eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'; eauto.
            eapply disjoint_sym.
            unfolds. eexists. join auto.
          }
          assert (Hj1:disjoint Ms Mf).
          { eapply join_join_disj_r; eauto.
          }

          assert (Hsub2: Maps.sub Ms mx).
          { eapply sub_trans; eauto.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'.
            eapply sub_refl. auto.
          }
          assert (Hsub3: Maps.sub Mf mx).
          { 
            eapply sub_trans.
            2 : eapply Hsub1.
            eapply join_sub_r.
            eapply join_merge_disj; eauto.
          }
          eapply eq_sym in Hmx1.

  (* disjoint *)
  assert (Hd1: disjoint Mf x /\ disjoint Mf x0 /\ disjoint Mf x12).
            { splits.
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_l; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
              -{ eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
                }
              -{ eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x17).
                 eapply join_sub_r; eauto.
                 eapply disj_trans_sub with (m2 := x5).
                 eapply join_sub_l; eauto.
                 eapply disjoint_sym.
                 eapply my_join_disj; eauto.
               }
             }

             assert (Hd2 : disjoint Ms x /\ disjoint Ms x0 /\ disjoint Ms x12).
              { splits.
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_l; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                  }
                -{ eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
                -{ eapply disj_trans_sub with (m2 := x0).
                   eapply join_sub_r; eauto.
                   eapply disj_trans_sub with (m2 := x17).
                   eapply join_sub_r; eauto.
                   eapply disjoint_sym.
                   eapply my_join_disj; eauto.
                }
              }

             destruct Hd1 as (Hd1'&Hd2'&Hd3').
             destruct Hd2 as (Hd4'&Hd5'&Hd6').

             assert (Hd3 : disjoint x x12).
             { eapply disj_trans_sub with (m2 := x0).
                 eapply join_sub_r; eauto.
                 eapply my_join_disj; eauto.
             }
           assert (Histrue: 
                        forall (a : HalfPermMap.A) (b0 : bool) (v : HalfPermMap.C),
                                x a = Some (b0, v) -> b0 = true).
            {  lets Heq: mapstoval_minus_eq_emp_alt H3 H3.
                destruct Heq; auto.
                introv Hs.
                specialize H21 with (x:= a).
                rewrite Hs in *.
                destruct H21 as [(v1 & v2 & Heq & _) | (Heq & _)]; inverts Heq.
                auto.
             }

             assert (Hdm1: disjoint (merge Mf Ms) x).
              { eapply disjoint_merge_imp; eauto. }

            assert (Hc: merge Ms Mf = merge Mf Ms).
             {  eapply disjoint_merge_sym; eauto. }

            assert (Hd4 : disjoint (merge Mf Ms) x12).
             { lets Hj1': H60.
               lets Hj2': H58.
               assert(Hj':join x17 (merge Ms Mf) x6).
               eapply join_merge23; eauto.
               eapply my_join_disj in Hj'.
               rewrite Hc in Hj'.
               eapply disjoint_sym in Hj'.
               eapply disj_trans_sub with (m2:= x0).
               eapply join_sub_r; eauto.
               eapply disj_trans_sub with (m2 := x17).
               eapply join_sub_r; eauto.
               auto.
             }

            assert (Hd5 : disjoint (merge (merge Mf Ms) x) x12).
             { eapply perm_map_lemmas_part2.mem_disj_join_disjmerge'.
                2:{ eapply join_comm. eapply join_merge_disj; eauto. }
                eapply disjoint_sym.
                eapply disjoint_merge_imp.
                auto.
                eapply disjoint_sym; eauto.
                eapply disjoint_sym; eauto.
                auto.
             }
  (* end of disjoint *)

          assert (Hsub4: Maps.sub x mx).
          {
            rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part2.mem_sub_disjoint_sub_merge'; eauto.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
          }
          assert (Hsub5: Maps.sub x12 mx).
          { rewrite Hmx in Hmx3; rewrite Hmx1 in Hmx3.
            rewrite <- Hmx3.
            eapply perm_map_lemmas_part4.disjoint_sub_merge_r; eauto.
           }

          assert (Hmeq: minus (minus M' Ms) Mf = minus M' (merge Ms Mf)).
        { eapply perm_map_lemmas_part2.mem_join_minus.
           eapply join_comm.
           eapply join_join_join_merge.
           2:{ eapply join_sub_minus.
                 eapply join_join_sub_minus.
                 2:{ eapply join_comm. 
                       eapply join_merge_disj; eauto. }
               eapply sub_sem'; eauto.
              eapply sub_trans; eauto.
             unfold Maps.sub. eexists. 
              eapply join_comm; eauto.
            }
           eapply join_sub_minus.
           eapply sub_trans; eauto.
           unfold Maps.sub. eexists. 
           eapply join_comm; eauto.
         }

      eexists. exists (Vint32 index). exists aop.
      exists OO.
      exists (set OO evstructheapid 
               (evstructheap (Set_struct strheap (b, y) XMC_XMPAXL (get_mpax_struct mpaxl 
                 (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil))))).
      exists (x3, x4, ( minus (minus M' Ms) Mf), x7, x8, x10).
      eexists Ms.
      exists (set O evstructheapid
     (evstructheap
        (Set_struct strheap (b, y) XMC_XMPAXL (get_mpax_struct mpaxl 
                 (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil))))).
      exists Os.
      exists (b, y).
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         
         lets Hsg: H17.
         eapply OSAbstMod.join_sig_get in Hsg.
         eexists (evstructheap strheap).
          
         eapply OSAbstMod.join_get_r in Hsg.
         2: eauto.
         eapply OSAbstMod.join_get_r in Hsg; eauto.
         
       -  unfolds.
          eexists.
          splits; unfold joinmem; do 7 eexists; splits;eauto.
          2 : {eapply join_join_minus.
               eapply join_comm; eauto. 
               subst mx. rewrite <- Hmx.
               lets Hcp: H58.
               eapply join_comm in Hcp; eapply join_eq_minus in Hcp; subst.
               eapply mem_join_sub_join_minus_minus.
               join auto. unfolds; eauto.
                }

          eapply join_comm.
          eapply mem_sub_sub_disjoint_join_minus1 with (m1 := Ms); eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply sub_trans; eauto.
          eapply join_sub_r; eauto.
          eapply old.Unnamed_thm.
      -  eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      -  unfold satp. intros.
         apply HPlinv.
         unfold emposabst in H26.
         subst.
         eapply join_emp_eq in H22.
         subst.

         exists ( get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)).
         exists (Set_struct strheap (b, y) XMC_XMPAXL (get_mpax_struct mpaxl 
                 (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_xmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

  (* end of disjoint *) 
      (* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {
              assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
             {   rewrite Hmeq.
                 eapply perm_map_lemmas_part2.mem_join_minus.
                 eapply join_join_join_merge.
                 eapply join_join_join_merge.
                 eauto.
                 rewrite <- Hmx. rewrite <- Hmx3.
                 eapply join_comm. eapply join_merge_disj.
                 2: { eapply join_comm.
                      rewrite Hc.
                      eapply join_merge_disj; eauto.
                    }
                 auto.
               }
              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }
       (* start prove changed struct XMC_XMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
      (* end of prove changed struct XMC_XMPAXL *)


(*last goal: <_ msim*)
      - constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv.
           unfold emposabst in H26.
           subst.
           eapply join_emp_eq in H22.
           subst.

(* (o,O,aop)|=(CurLINV pa t)) *)
        { exists ( get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)).
         exists (Set_struct strheap (b, y) XMC_XMPAXL
       (get_mpax_struct mpaxl
          (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil))).
        sep split; eauto.
        2 : { split; auto. 
              apply get_mpax_struct_xmpaxl_match. }

         rewrite Hmeq.
         sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
         simpl.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         rewrite <- set_sig with (b:= (evstructheap strheap) ).
         eapply map_join_set_none.
         join auto.

(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
         rewrite <- ml_eq.
         eapply merge_sem_none3; eauto.
         eapply get_join_none; eauto.
         rewrite OSAbstMod.map_get_sig; eauto.
         eapply get_join_none; try  eapply join_comm; eauto.
         eapply OSAbstMod.join_sig_get; eauto.

         do 6 eexists. splits; eauto.
         2: {  eapply old.Unnamed_thm.
            }
         2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
         {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
             }

              rewrite <- Heq.
              eapply join_comm. eapply join_merge_disj.
              eapply disjoint_merge_imp.
              2: eapply disjoint_sym; eauto.
              { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
              { eapply disjoint_sym.
                 eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
                 unfolds; eauto.
               }
                auto.
          }
          (* end of  join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

         do 6 eexists. splits; eauto.
         3: { eapply change_aop_rule; eauto. }
         2: { rewrite <- ml_eq.
                 eapply join_join_merge; eauto.
                 eapply join_comm; eauto.
            }
         { instantiate (1:= mx6'). 
           eapply join_emp_eq in H15, H20; subst.
           eapply join_comm.
           eapply join_merge_disj.
           eapply disjoint_sym.
           eapply mem_sub_disj; eauto.
           eapply disjoint_sym.
           unfolds; eauto.
         }


(* start prove changed struct XMC_XMPAXL *)
         { subst.
           simpl Astruct.

           do 4 rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
           change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
           change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
           rewrite Int.add_assoc in *.
           change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

           sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
           simpl.
(* Aemp *)
           exists (empmem). do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           eapply old.Unnamed_thm.
           unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
           exists M7'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
           exists M6'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
           exists M5'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
           exists M4'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
           exists M3'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
           exists M2'.
           do 5 eexists.
           splits; eauto.
           eapply old.Unnamed_thm.
           unfold emposabst. split; auto.
           eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
           rewrite Z.add_0_r in *.
           eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
           unfold emposabst.
           simpl in H13.
           simpljoin.
           join auto.
         }
(* end of prove changed struct XMC_XMPAXL *)
      }


(* (o,O,aop)|=lift (<||aop||> ** (...)) *)
    { unfold lift.
      sep lift 2%nat.
      sep normal.

      unfold emposabst in H26.
      subst.
      eapply join_emp_eq in H22.
      subst.
(* (o,O,aop)|=(CurLINV pa t)) *)
       exists ( get_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)).
       exists (Set_struct strheap (b, y) XMC_XMPAXL
     (get_mpax_struct mpaxl
        (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil))).
      sep split; eauto.
      2 : { split; auto. 
            apply get_mpax_struct_xmpaxl_match. }

       rewrite Hmeq.
       sep lifts (2 :: 4 :: 1 :: 5 :: 3 :: nil)%nat.
       sep remember (1 :: 2 :: 3 :: 4 :: nil)%nat.
       simpl.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       eapply join_comm.
       eapply map_join_set_none.
       eapply join_comm; eauto.
       eapply get_a_sig_a'.
       introv Hf; try false.
       do 6 eexists. splits; eauto.
       eapply old.Unnamed_thm.
       rewrite <- set_sig with (b:= (evstructheap strheap) ).
       eapply map_join_set_none.
       join auto.
      
(*get (merge_list (x21 :: x14 :: nil)) evstructheapid = None*)
       rewrite <- ml_eq.
       eapply merge_sem_none3; eauto.
       eapply get_join_none; eauto.
       rewrite OSAbstMod.map_get_sig; eauto.
       eapply get_join_none; try  eapply join_comm; eauto.
       eapply OSAbstMod.join_sig_get; eauto.

       do 6 eexists. splits; eauto.
       2: { eapply old.Unnamed_thm.
          }
       
       2:{ splits; eauto. unfolds. auto. } 

(* start goal: join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)
       {  assert (Heq: merge (merge mx6' x12) x = (minus (minus M' Ms) Mf)).
            {  rewrite Hmeq.
               eapply perm_map_lemmas_part2.mem_join_minus.
               eapply join_join_join_merge.
               eapply join_join_join_merge.
               eauto.
               rewrite <- Hmx. rewrite <- Hmx3.
               eapply join_comm. eapply join_merge_disj.
               2: { eapply join_comm.
                    rewrite Hc.
                    eapply join_merge_disj; eauto.
                  }
               auto.
            }
            rewrite <- Heq.
            eapply join_comm. eapply join_merge_disj.
            eapply disjoint_merge_imp.
            2: eapply disjoint_sym; eauto.
            { eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
            { eapply disjoint_sym.
               eapply disj_trans_sub with (m2:=(minus x6 mx6)); auto.
               unfolds; eauto.
             }
              auto.
        }
        (* end of join x (merge mx6' x12) (minus (minus M' Ms) Mf) *)

       do 6 eexists. splits; eauto.
       3: { eapply change_aop_rule; eauto. }
       2: { rewrite <- ml_eq.
               eapply join_join_merge; eauto.
               eapply join_comm; eauto.
          }
       { instantiate (1:= mx6'). 
         eapply join_emp_eq in H15, H20; subst.
         eapply join_comm.
         eapply join_merge_disj.
         eapply disjoint_sym.
         eapply mem_sub_disj; eauto.
         eapply disjoint_sym.
         unfolds; eauto.
       }


(* start prove changed struct MSMC_SMSMPAXL *)
       { subst.
         simpl Astruct.

         do 4 rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5).
         change (Int.add (Int.repr 4) (Int.add (Int.repr 1) (Int.repr 1))) with (Int.repr 6).
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8).
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9).

         sep lifts (8 :: 7 :: 6 :: 5 :: 4 :: 3 :: 2 :: 1 :: nil)%nat.
         simpl.
(* Aemp *)
         exists (empmem). do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         unfold emposabst. auto.
(*mapstoval (b, y+9) Tint8 true (Vint32 (get_part mpaxl 31 0)) M0*)
         exists M7'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+8) Tint8 true (Vint32 (get_part mpaxl 30 1)) M0*)
         exists M6'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+7) Tint8 true (Vint32 (get_part mpaxl 29 2)) M0*)
         exists M5'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+6) Tint8 true (Vint32 (get_part mpaxl 28 3)) M0*)
         exists M4'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+5) Tint8 true (Vint32 (get_part mpaxl 27 4)) M0*)
         exists M3'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y+4) Tint8 true (Vint32 (get_part mpaxl 26 5)) M0*)
         exists M2'.
         do 5 eexists.
         splits; eauto.
         eapply old.Unnamed_thm.
         unfold emposabst. split; auto.
         eapply mapstoval_store_changeval; eauto.
(*mapstoval (b, y) Tint32 true (Vint32 (get_part mpaxl 0 8)) M0*)
         rewrite Z.add_0_r in *.
         eapply mapstoval_store_changeval; eauto.
(* emposabst x14 *)
         unfold emposabst.
         simpl in H13.
         simpljoin.
         join auto.
       }
(* end of prove changed struct XMC_XMPAXL *)
     }

    ++ intros. 
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso. 
       apply Hhf. 
       cbv. eauto.

       Unshelve.
       exact Vnull.
Qed.

Lemma csl_msmc_setSMSMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 e3 
          n m q aop pa t index sms 
           mpaxl mpaxh vl strheap,
            can_change_aop P' ->
            (Z.of_nat n <= Int.max_unsigned)%Z ->
            m = Vint32 index ->
            (0 <= Int.unsigned index < 8)%Z ->
            rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
            rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
            SmsMod.get sms index = Some (mpaxl, mpaxh) ->
            P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                       Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SMSMPAXL == Vptr q ->
            P ==> Astruct q MSMC_SMSMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                        [| Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) /\ struct_type_vallist_match MSMC_SMSMPAXL vl |] ** 
                        PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                        Aabsdata sms_mpaxid (ossms_mpax sms) ** P' ->
            ( EX sms' mpaxl',
                     Astruct q MSMC_SMSMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) /\ struct_type_vallist_match MSMC_SMSMPAXL vl |] **
                     PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) vl |] **
                     [| sms' = SmsMod.set sms index (mpaxl', mpaxh) |] ** Aabsdata sms_mpaxid (ossms_mpax sms') ** P' ) ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_msmc_setSMSMPAXL n m q);; aop ||> ** P)
              (sprim (scsl_msmc_setSMSMPAXL e1 e2 e3))  
              (<|| aop ||>  ** 
                EX sms' mpaxl', 
                     Astruct q MSMC_SMSMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, MSMC_SMSMPAXL, vl) /\ struct_type_vallist_match MSMC_SMSMPAXL vl |] **
                     PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (smsl_raddr :: smsl_sr :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil) vl |] **
                     [| sms' = SmsMod.set sms index (mpaxl', mpaxh) |]  ** Aabsdata sms_mpaxid (ossms_mpax sms') ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange
         Hmatch1 Hmatch2 Hsms HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  destruct (Int.unsigned i6 <=? Byte.max_unsigned)%Z eqn:eq6;tryfalse.

   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   Ltac destruct_rename dest_h name_m name_hj name_ho name_hmp :=
   destruct dest_h as [name_m [ ? [ ? [ ? [ ? [ ? dest_h]]]]]];
   destruct dest_h as (? & name_hj & ? & name_ho & (name_hmp & ?) & dest_h).
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   destruct_rename Heq mx3 Hj3 Ho3 Hmap3.
   destruct_rename Heq mx4 Hj4 Ho4 Hmap4.
   destruct_rename Heq mx5 Hj5 Ho5 Hmap5.
   destruct_rename Heq mx6 Hj6 Ho6 Hmap6.
   destruct_rename Heq mx7 Hj7 Ho7 Hmap7.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&Hf&_).
    exfalso. apply Hf. unfolds.
    do 4 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H11 as [? [_ ?]].
    unfold getmem in H11.
    simpl in H10, H11. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H11.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_msmc_setSMSMPAXL_step with
                     (x:= mpaxl) (x1:= i0) (x2:= i1) (x3:= i2) (x4:= i3) (x5:= i4) (x6:= i5) (x7:= i6); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - erewrite Hst; eauto.

   +
      simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev3: H2.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H10, H11.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H23 in Hev3'.
      rewrite H21 in Hev2'.
      rewrite H20 in Hev1'.
      inverts Hev3'; inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxl = Vint32 x3 /\
                                 Vint32 i0 = Vint32 x4  /\ Vint32 i1 = Vint32 x5 /\ Vint32 i2 = Vint32 x6 /\
                                 Vint32 i3 = Vint32 x7  /\ Vint32 i4 = Vint32 x8 /\ Vint32 i5 = Vint32 x11 /\
                                 Vint32 i6 = Vint32 x12).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6 & Heq7 & Heq8).
       eapply eq_sym in Heq1, Heq2, Heq3, Heq4, Heq5, Heq6, Heq7, Heq8; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3; inverts Heq4; inverts Heq5; inverts Heq6; inverts Heq7; inverts Heq8.

      lets Hst_mpaxl : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxl as (m' & Hst_mpaxl).
      lets Hst_mpaxl0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxl0 as (m0 & Hst_mpaxl0).
      lets Hst_mpaxl1 : store_exist_join H18 H15 H0 (map_join_emp x25).
      destruct Hst_mpaxl1 as (m1 & Hst_mpaxl1).
      lets Hst_mpaxl2 : store_exist_join  H18 H15 H0 H37.
      destruct Hst_mpaxl2 as (m2 & Hst_mpaxl2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxl Hst_mpaxl0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxl0 Hst_mpaxl1.
      lets Hjnew1: join_store_join (join_comm H37) Hst_mpaxl1 Hst_mpaxl2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H14) Hst_mpaxl2 H39.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x13, x14, m1, x19, x20, x21,
                          set O sms_mpaxid
                            (ossms_mpax
                               (SmsMod.set sms index
                                  (set_mpax_struct mpaxl
                                     (smsl_raddr
                                      :: smsl_sr
                                         :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1
                                         :: Vint32 i2
                                            :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil),
                                  mpaxh))), aop0)
                          |= EX (sms' : SmsMod.map) (mpaxl' : int32),
                             Astruct (b, i) MSMC_SMSMPAXL
                               (Vint32 i0
                                :: Vint32 i1
                                   :: Vint32 i2
                                      :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, MSMC_SMSMPAXL,
                                 Vint32 i0
                                 :: Vint32 i1
                                    :: Vint32 i2
                                       :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) /\
                               struct_type_vallist_match MSMC_SMSMPAXL
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             PV (sms_mpax_block, Int.repr (Int.unsigned index * 8)) @ Tint32
                             |-> Vint32 mpaxl' **
                             [|mpaxl' =
                               set_mpax_struct mpaxl
                                 (smsl_raddr
                                  :: smsl_sr
                                     :: smsl_sw :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             [|sms' = SmsMod.set sms index (mpaxl', mpaxh)|] **
                             Aabsdata sms_mpaxid (ossms_mpax sms') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1,eq2, eq3, eq4, eq5, eq6. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H10.
         simpl Astruct.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 5 eexists.
      exists (set OO sms_mpaxid
                                   (ossms_mpax
                                      (SmsMod.set sms index
                                         (set_mpax_struct mpaxl
                                            (smsl_raddr
                                             :: smsl_sr
                                                :: smsl_sw
                                                   :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      exists (x13, x14, m1, x19, x20, x21).
      exists Ms.
      exists (set O sms_mpaxid
                                   (ossms_mpax
                                      (SmsMod.set sms index
                                         (set_mpax_struct mpaxl
                                            (smsl_raddr
                                             :: smsl_sr
                                                :: smsl_sw
                                                   :: smsl_sx :: smsl_ur :: smsl_uw :: smsl_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      do 2  eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.


Lemma csl_msmc_setSESMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 e3 
          n m q aop pa t index ses 
           mpaxl mpaxh vl strheap,
            can_change_aop P' ->
            (Z.of_nat n <= Int.max_unsigned)%Z ->
            m = Vint32 index ->
            (0 <= Int.unsigned index < 8)%Z ->
            rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
            rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
            SesMod.get ses index = Some (mpaxl, mpaxh) ->
            P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                       Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SESMPAXL == Vptr q ->
            P ==> Astruct q MSMC_SESMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                        [| Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) /\ struct_type_vallist_match MSMC_SESMPAXL vl |] ** 
                        PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                        Aabsdata ses_mpaxid (osses_mpax ses) ** P' ->
            ( EX ses' mpaxl',
                     Astruct q MSMC_SESMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) /\ struct_type_vallist_match MSMC_SESMPAXL vl |] **
                     PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) vl |] **
                     [| ses' = SesMod.set ses index (mpaxl', mpaxh) |] ** Aabsdata ses_mpaxid (osses_mpax ses') ** P' ) ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_msmc_setSESMPAXL n m q);; aop ||> ** P)
              (sprim (scsl_msmc_setSESMPAXL e1 e2 e3))  
              (<|| aop ||>  ** 
                EX ses' mpaxl', 
                     Astruct q MSMC_SESMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, MSMC_SESMPAXL, vl) /\ struct_type_vallist_match MSMC_SESMPAXL vl |] **
                     PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (sesl_raddr :: sesl_sr :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil) vl |] **
                     [| ses' = SesMod.set ses index (mpaxl', mpaxh) |]  ** Aabsdata ses_mpaxid (osses_mpax ses') ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange
         Hmatch1 Hmatch2 Hses HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  destruct (Int.unsigned i6 <=? Byte.max_unsigned)%Z eqn:eq6;tryfalse.

   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   destruct_rename Heq mx3 Hj3 Ho3 Hmap3.
   destruct_rename Heq mx4 Hj4 Ho4 Hmap4.
   destruct_rename Heq mx5 Hj5 Ho5 Hmap5.
   destruct_rename Heq mx6 Hj6 Ho6 Hmap6.
   destruct_rename Heq mx7 Hj7 Ho7 Hmap7.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
    exfalso. apply Hf. unfolds.
    do 4 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H11 as [? [_ ?]].
    unfold getmem in H11.
    simpl in H10, H11. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H11.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_msmc_setSESMPAXL_step with
                     (x:= mpaxl) (x1:= i0) (x2:= i1) (x3:= i2) (x4:= i3) (x5:= i4) (x6:= i5) (x7:= i6); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - erewrite Hst; eauto.

   +
      simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev3: H2.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H10, H11.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H23 in Hev3'.
      rewrite H21 in Hev2'.
      rewrite H20 in Hev1'.
      inverts Hev3'; inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxl = Vint32 x3 /\
                                 Vint32 i0 = Vint32 x4  /\ Vint32 i1 = Vint32 x5 /\ Vint32 i2 = Vint32 x6 /\
                                 Vint32 i3 = Vint32 x7  /\ Vint32 i4 = Vint32 x8 /\ Vint32 i5 = Vint32 x11 /\
                                 Vint32 i6 = Vint32 x12).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6 & Heq7 & Heq8).
       eapply eq_sym in Heq1, Heq2, Heq3, Heq4, Heq5, Heq6, Heq7, Heq8; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3; inverts Heq4; inverts Heq5; inverts Heq6; inverts Heq7; inverts Heq8.

      lets Hst_mpaxl : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxl as (m' & Hst_mpaxl).
      lets Hst_mpaxl0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxl0 as (m0 & Hst_mpaxl0).
      lets Hst_mpaxl1 : store_exist_join H18 H15 H0 (map_join_emp x25).
      destruct Hst_mpaxl1 as (m1 & Hst_mpaxl1).
      lets Hst_mpaxl2 : store_exist_join  H18 H15 H0 H37.
      destruct Hst_mpaxl2 as (m2 & Hst_mpaxl2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxl Hst_mpaxl0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxl0 Hst_mpaxl1.
      lets Hjnew1: join_store_join (join_comm H37) Hst_mpaxl1 Hst_mpaxl2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H14) Hst_mpaxl2 H39.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x13, x14, m1, x19, x20, x21,
                          set O ses_mpaxid
                            (osses_mpax
                               (SesMod.set ses index
                                  (set_mpax_struct mpaxl
                                     (sesl_raddr
                                      :: sesl_sr
                                         :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1
                                         :: Vint32 i2
                                            :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil),
                                  mpaxh))), aop0)
                          |= EX (ses' : SesMod.map) (mpaxl' : int32),
                             Astruct (b, i) MSMC_SESMPAXL
                               (Vint32 i0
                                :: Vint32 i1
                                   :: Vint32 i2
                                      :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, MSMC_SESMPAXL,
                                 Vint32 i0
                                 :: Vint32 i1
                                    :: Vint32 i2
                                       :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) /\
                               struct_type_vallist_match MSMC_SESMPAXL
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             PV (ses_mpax_block, Int.repr (Int.unsigned index * 8)) @ Tint32
                             |-> Vint32 mpaxl' **
                             [|mpaxl' =
                               set_mpax_struct mpaxl
                                 (sesl_raddr
                                  :: sesl_sr
                                     :: sesl_sw :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             [|ses' = SesMod.set ses index (mpaxl', mpaxh)|] **
                             Aabsdata ses_mpaxid (osses_mpax ses') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1,eq2, eq3, eq4, eq5, eq6. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H10.
         simpl Astruct.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 5 eexists.
      exists (set OO ses_mpaxid
                                   (osses_mpax
                                      (SesMod.set ses index
                                         (set_mpax_struct mpaxl
                                            (sesl_raddr
                                             :: sesl_sr
                                                :: sesl_sw
                                                   :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      exists (x13, x14, m1, x19, x20, x21).
      exists Ms.
      exists (set O ses_mpaxid
                                   (osses_mpax
                                      (SesMod.set ses index
                                         (set_mpax_struct mpaxl
                                            (sesl_raddr
                                             :: sesl_sr
                                                :: sesl_sw
                                                   :: sesl_sx :: sesl_ur :: sesl_uw :: sesl_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      do 2  eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.

Lemma csl_xmc_setXMPAXL_rule_sound:
  forall Spec sd I r ri  P P' e1 e2 
          n q aop pa t index xmc 
           mpaxl mpaxh vl strheap,
            can_change_aop P' ->
            n = Vint32 index ->
            (0 <= Int.unsigned index < 16)%Z ->
            rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
            rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
            XmcMod.get xmc index = Some (mpaxl, mpaxh) ->
            P ==> Rv e1 @ Tint32 ==  n //\\ Rv e2 @ Tptr XMC_XMPAXL == Vptr q ->
            P ==> Astruct q XMC_XMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                        [| Get_struct strheap q = Some (q, XMC_XMPAXL, vl) /\ struct_type_vallist_match XMC_XMPAXL vl |] ** 
                        PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl)  ** 
                        Aabsdata xmpaxid (osxmpax xmc) ** P' ->
            ( EX xmc' mpaxl',
                     Astruct q XMC_XMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, XMC_XMPAXL, vl) /\ struct_type_vallist_match XMC_XMPAXL vl |] **
                     PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) vl |] **
                     [| xmc' = XmcMod.set xmc index (mpaxl', mpaxh) |] ** Aabsdata xmpaxid (osxmpax xmc') ** P' ) ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_xmc_setXMPAXL n q);; aop ||> ** P)
              (sprim (scsl_xmc_setXMPAXL e1 e2))  
              (<|| aop ||>  ** 
                EX xmc' mpaxl', 
                     Astruct q XMC_XMPAXL vl ** Aabsdata evstructheapid (evstructheap strheap) **
                     [| Get_struct strheap q = Some (q, XMC_XMPAXL, vl) /\ struct_type_vallist_match XMC_XMPAXL vl |] **
                     PV (xmpax_block, (Int.repr ((Int.unsigned index)*8)%Z)) @ Tint32 |-> (Vint32 mpaxl')  ** 
                     [| mpaxl' = set_mpax_struct mpaxl (xmc_raddr :: xmc_sr :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil) vl |] **
                     [| xmc' = XmcMod.set xmc index (mpaxl', mpaxh) |]  ** Aabsdata xmpaxid (osxmpax xmc') ** P' ) t.
Proof.
  introv Haop Hindex Hrange
         Hmatch1 Hmatch2 Hxmc HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 8 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.
  destruct (Int.unsigned i2 <=? Byte.max_unsigned)%Z eqn:eq2;tryfalse.
  destruct (Int.unsigned i3 <=? Byte.max_unsigned)%Z eqn:eq3;tryfalse.
  destruct (Int.unsigned i4 <=? Byte.max_unsigned)%Z eqn:eq4;tryfalse.
  destruct (Int.unsigned i5 <=? Byte.max_unsigned)%Z eqn:eq5;tryfalse.
  destruct (Int.unsigned i6 <=? Byte.max_unsigned)%Z eqn:eq6;tryfalse.

   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
   rewrite Int.add_assoc in *.
   change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   destruct_rename Heq mx3 Hj3 Ho3 Hmap3.
   destruct_rename Heq mx4 Hj4 Ho4 Hmap4.
   destruct_rename Heq mx5 Hj5 Ho5 Hmap5.
   destruct_rename Heq mx6 Hj6 Ho6 Hmap6.
   destruct_rename Heq mx7 Hj7 Ho7 Hmap7.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
    exfalso. apply Hf. unfolds.
    do 3 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H8 as [? [_ ?]].
    unfold getmem in H8.
    simpl in H6, H8. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H8.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_xmc_setXMPAXL_step with
                     (x:= mpaxl) (x1:= i0) (x2:= i1) (x3:= i2) (x4:= i3) (x5:= i4) (x6:= i5) (x7:= i6); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - join auto.
     - erewrite Hst; eauto.

   +
      simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H6, H8.
      simp join.
      simpl get_smem in Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H16 in Hev2'.
      rewrite H14 in Hev1'.
      inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxl = Vint32 x3 /\
                                 Vint32 i0 = Vint32 x4  /\ Vint32 i1 = Vint32 x5 /\ Vint32 i2 = Vint32 x6 /\
                                 Vint32 i3 = Vint32 x7  /\ Vint32 i4 = Vint32 x8 /\ Vint32 i5 = Vint32 x11 /\
                                 Vint32 i6 = Vint32 x12).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1;  try rewrite eq2;  try rewrite eq3;
                               try rewrite eq4;  try rewrite eq5;  try rewrite eq6; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3 & Heq4 & Heq5 & Heq6 & Heq7 & Heq8).
       eapply eq_sym in Heq1, Heq2, Heq3, Heq4, Heq5, Heq6, Heq7, Heq8; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3; inverts Heq4; inverts Heq5; inverts Heq6; inverts Heq7; inverts Heq8.

      lets Hst_mpaxl : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxl as (m' & Hst_mpaxl).
      lets Hst_mpaxl0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxl0 as (m0 & Hst_mpaxl0).
      lets Hst_mpaxl1 : store_exist_join H18 H15 H0 (map_join_emp x25).
      destruct Hst_mpaxl1 as (m1 & Hst_mpaxl1).
      lets Hst_mpaxl2 : store_exist_join  H18 H15 H0 H31.
      destruct Hst_mpaxl2 as (m2 & Hst_mpaxl2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxl Hst_mpaxl0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxl0 Hst_mpaxl1.
      lets Hjnew1: join_store_join (join_comm H31) Hst_mpaxl1 Hst_mpaxl2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H10) Hst_mpaxl2 H33.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x13, x14, m1, x19, x20, x21,
                          set O xmpaxid
                            (osxmpax
                               (XmcMod.set xmc index
                                  (set_mpax_struct mpaxl
                                     (xmc_raddr
                                      :: xmc_sr
                                         :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1
                                         :: Vint32 i2
                                            :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil),
                                  mpaxh))), aop0)
                          |= EX (xmc' : XmcMod.map) (mpaxl' : int32),
                             Astruct (b, i) XMC_XMPAXL
                               (Vint32 i0
                                :: Vint32 i1
                                   :: Vint32 i2
                                      :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, XMC_XMPAXL,
                                 Vint32 i0
                                 :: Vint32 i1
                                    :: Vint32 i2
                                       :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil) /\
                               struct_type_vallist_match XMC_XMPAXL
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             PV (xmpax_block, Int.repr (Int.unsigned index * 8)) @ Tint32
                             |-> Vint32 mpaxl' **
                             [|mpaxl' =
                               set_mpax_struct mpaxl
                                 (xmc_raddr
                                  :: xmc_sr
                                     :: xmc_sw :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1
                                     :: Vint32 i2
                                        :: Vint32 i3 :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil)|] **
                             [|xmc' = XmcMod.set xmc index (mpaxl', mpaxh)|] **
                             Aabsdata xmpaxid (osxmpax xmc') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1,eq2, eq3, eq4, eq5, eq6. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H6.
         simpl Astruct.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 4) (Int.repr 1)) with (Int.repr 5) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 5) (Int.repr 1)) with (Int.repr 6) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 6) (Int.repr 1)) with (Int.repr 7) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 7) (Int.repr 1)) with (Int.repr 8) in *.
         rewrite Int.add_assoc in *.
         change (Int.add (Int.repr 8) (Int.repr 1)) with (Int.repr 9) in *.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 4 eexists.
      exists (set OO xmpaxid
                                   (osxmpax
                                      (XmcMod.set xmc index
                                         (set_mpax_struct mpaxl
                                            (xmc_raddr
                                             :: xmc_sr
                                                :: xmc_sw
                                                   :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      exists (x13, x14, m1, x19, x20, x21).
      exists Ms.
      exists (set O xmpaxid
                                   (osxmpax
                                      (XmcMod.set xmc index
                                         (set_mpax_struct mpaxl
                                            (xmc_raddr
                                             :: xmc_sr
                                                :: xmc_sw
                                                   :: xmc_sx :: xmc_ur :: xmc_uw :: xmc_ux :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1
                                        :: Vint32 i2
                                           :: Vint32 i3
                                              :: Vint32 i4 :: Vint32 i5 :: Vint32 i6 :: nil), mpaxh)))).
      do 2 eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.

Lemma csl_msmc_setSMSMPAXH_rule_sound:
        forall Spec sd I r ri  P P' e1 e2 e3 n m q aop pa t index sms mpaxl mpaxh vl strheap,
                  can_change_aop P' ->
                  (Z.of_nat n <= Int.max_unsigned)%Z ->
                  m = Vint32 index ->
                  (0 <= Int.unsigned index < 8)%Z ->
                  rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
                  rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
                  SmsMod.get sms index = Some (mpaxl, mpaxh) ->
                  P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                             Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SMSMPAXH == Vptr q ->
                  P ==> Astruct q MSMC_SMSMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                              [| Get_struct strheap q = Some (q, MSMC_SMSMPAXH, vl) /\ struct_type_vallist_match MSMC_SMSMPAXH vl |] ** 
                              PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh)  ** 
                              Aabsdata sms_mpaxid (ossms_mpax sms) ** P' ->
                  ( EX sms' mpaxh',
                           Astruct q MSMC_SMSMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                           [| Get_struct strheap q = Some (q, MSMC_SMSMPAXH, vl) /\ struct_type_vallist_match MSMC_SMSMPAXH vl |] **
                           PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                           [| mpaxh' = set_mpax_struct mpaxh (smsh_baddr :: smsh_segsize :: nil) vl |] **
                           [| sms' = SmsMod.set sms index (mpaxl, mpaxh') |] ** Aabsdata sms_mpaxid (ossms_mpax sms') ** P' ) ==> CurLINV pa t ->
                  RuleSem Spec sd pa I r ri
                    (<|| (csl_msmc_setSMSMPAXH n m q);; aop ||> ** P)
                    (sprim (scsl_msmc_setSMSMPAXH e1 e2 e3))  
                    (<|| aop ||>  ** 
                      EX sms' mpaxh', 
                           Astruct q MSMC_SMSMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                           [| Get_struct strheap q = Some (q, MSMC_SMSMPAXH, vl) /\ struct_type_vallist_match MSMC_SMSMPAXH vl |] **
                           PV (sms_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                           [| mpaxh' = set_mpax_struct mpaxh (smsh_baddr :: smsh_segsize :: nil) vl |]  **
                           [| sms' = SmsMod.set sms index (mpaxl, mpaxh') |] ** Aabsdata sms_mpaxid (ossms_mpax sms') ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange
         Hmatch1 Hmatch2 Hsms HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 3 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
    exfalso. apply Hf. unfolds.
    do 4 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H11 as [? [_ ?]].
    unfold getmem in H11.
    simpl in H10, H11. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H11.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_msmc_setSMSMPAXH_step with
                     (x:= mpaxh) (x1:= i0) (x2:= i1); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - erewrite Hst; eauto.

   +  simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev3: H2.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H10, H11.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H23 in Hev3'.
      rewrite H21 in Hev2'.
      rewrite H20 in Hev1'.
      inverts Hev3'; inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxh = Vint32 x2 /\
                                 Vint32 i0 = Vint32 x3  /\ Vint32 i1 = Vint32 x4).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3).
       eapply eq_sym in Heq1, Heq2, Heq3; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3.

      lets Hst_mpaxh : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxh as (m' & Hst_mpaxh).
      lets Hst_mpaxh0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxh0 as (m0 & Hst_mpaxh0).
      lets Hst_mpaxh1 : store_exist_join H18 H15 H0 (map_join_emp x15).
      destruct Hst_mpaxh1 as (m1 & Hst_mpaxh1).
      lets Hst_mpaxh2 : store_exist_join  H18 H15 H0 H32.
      destruct Hst_mpaxh2 as (m2 & Hst_mpaxh2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxh Hst_mpaxh0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxh0 Hst_mpaxh1.
      lets Hjnew1: join_store_join (join_comm H32) Hst_mpaxh1 Hst_mpaxh2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H14) Hst_mpaxh2 H34.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x5, x6, m1, x10, x11, x12,
                          set O sms_mpaxid
                            (ossms_mpax
                               (SmsMod.set sms index
                                  (mpaxl, set_mpax_struct mpaxh
                                     (smsh_baddr
                                      :: smsh_segsize :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1 :: nil)))), aop0)
                          |= EX (sms' : SmsMod.map) (mpaxh' : int32),
                             Astruct (b, i) MSMC_SMSMPAXH
                               (Vint32 i0
                                :: Vint32 i1 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, MSMC_SMSMPAXH,
                                 Vint32 i0
                                 :: Vint32 i1 :: nil) /\
                               struct_type_vallist_match MSMC_SMSMPAXH
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             PV (sms_mpax_block, Int.repr (Int.unsigned index * 8 + 4)) @ Tint32
                             |-> Vint32 mpaxh' **
                             [|mpaxh' =
                               set_mpax_struct mpaxh
                                 (smsh_baddr ::
                                   smsh_segsize :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             [|sms' = SmsMod.set sms index (mpaxl, mpaxh')|] **
                             Aabsdata sms_mpaxid (ossms_mpax sms') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H10.
         simpl Astruct.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 5 eexists.
      exists (set OO sms_mpaxid
                                   (ossms_mpax
                                      (SmsMod.set sms index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (smsh_baddr
                                             :: smsh_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      exists (x5, x6, m1, x10, x11, x12).
      exists Ms.
      exists (set O sms_mpaxid
                                   (ossms_mpax
                                      (SmsMod.set sms index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (smsh_baddr
                                             :: smsh_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      do 2 eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.

Lemma csl_msmc_setSESMPAXH_rule_sound:
        forall Spec sd I r ri  P P' e1 e2 e3 n m q aop pa t index ses mpaxl mpaxh vl strheap,
                can_change_aop P' ->
                (Z.of_nat n <= Int.max_unsigned)%Z ->
                m = Vint32 index ->
                (0 <= Int.unsigned index < 8)%Z ->
                rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
                rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
                SesMod.get ses index = Some (mpaxl, mpaxh) ->
                P ==> Rv e1 @ Tint32 == Vint32 ((Int.repr (Z.of_nat n))) //\\
                           Rv e2 @ Tint32 ==  m //\\ Rv e3 @ Tptr MSMC_SESMPAXH == Vptr q ->
                P ==> Astruct q MSMC_SESMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                            [| Get_struct strheap q = Some (q, MSMC_SESMPAXH, vl) /\ struct_type_vallist_match MSMC_SESMPAXH vl |] ** 
                            PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh)  ** 
                            Aabsdata ses_mpaxid (osses_mpax ses) ** P' ->
                ( EX ses' mpaxh',
                         Astruct q MSMC_SESMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                         [| Get_struct strheap q = Some (q, MSMC_SESMPAXH, vl) /\ struct_type_vallist_match MSMC_SESMPAXH vl |] **
                         PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                         [| mpaxh' = set_mpax_struct mpaxh (sesh_baddr :: sesh_segsize :: nil) vl |] **
                         [| ses' = SesMod.set ses index (mpaxl, mpaxh') |] ** Aabsdata ses_mpaxid (osses_mpax ses') ** P' ) ==> CurLINV pa t ->
                RuleSem Spec sd pa I r ri
                  (<|| (csl_msmc_setSESMPAXH n m q);; aop ||> ** P)
                  (sprim (scsl_msmc_setSESMPAXH e1 e2 e3))  
                  (<|| aop ||>  ** 
                    EX ses' mpaxh', 
                         Astruct q MSMC_SESMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                         [| Get_struct strheap q = Some (q, MSMC_SESMPAXH, vl) /\ struct_type_vallist_match MSMC_SESMPAXH vl |] **
                         PV (ses_mpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                         [| mpaxh' = set_mpax_struct mpaxh (sesh_baddr :: sesh_segsize :: nil) vl |]  **
                         [| ses' = SesMod.set ses index (mpaxl, mpaxh') |] ** Aabsdata ses_mpaxid (osses_mpax ses') ** P' ) t.
Proof.
  introv Haop Hnrange Hindex Hrange
         Hmatch1 Hmatch2 Hses HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 3 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf&_).
    exfalso. apply Hf. unfolds.
    do 4 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H11 as [? [_ ?]].
    unfold getmem in H11.
    simpl in H10, H11. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H11.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_msmc_setSESMPAXH_step with
                     (x:= mpaxh) (x1:= i0) (x2:= i1); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - erewrite Hst; eauto.

   +  simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev3: H2.
      eapply Hlem in Hev3; eauto.
      lets Hev3': Hev3.
      eapply evalval_mono_joinmem in Hev3'; eauto.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H10, H11.
      simp join.
      simpl get_smem in Hev3 , Hev3', Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H23 in Hev3'.
      rewrite H21 in Hev2'.
      rewrite H20 in Hev1'.
      inverts Hev3'; inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxh = Vint32 x2 /\
                                 Vint32 i0 = Vint32 x3  /\ Vint32 i1 = Vint32 x4).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3).
       eapply eq_sym in Heq1, Heq2, Heq3; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3.

      lets Hst_mpaxh : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxh as (m' & Hst_mpaxh).
      lets Hst_mpaxh0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxh0 as (m0 & Hst_mpaxh0).
      lets Hst_mpaxh1 : store_exist_join H18 H15 H0 (map_join_emp x15).
      destruct Hst_mpaxh1 as (m1 & Hst_mpaxh1).
      lets Hst_mpaxh2 : store_exist_join  H18 H15 H0 H32.
      destruct Hst_mpaxh2 as (m2 & Hst_mpaxh2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxh Hst_mpaxh0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxh0 Hst_mpaxh1.
      lets Hjnew1: join_store_join (join_comm H32) Hst_mpaxh1 Hst_mpaxh2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H14) Hst_mpaxh2 H34.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x5, x6, m1, x10, x11, x12,
                          set O ses_mpaxid
                            (osses_mpax
                               (SesMod.set ses index
                                  (mpaxl, set_mpax_struct mpaxh
                                     (sesh_baddr
                                      :: sesh_segsize :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1 :: nil)))), aop0)
                          |= EX (ses' : SesMod.map) (mpaxh' : int32),
                             Astruct (b, i) MSMC_SESMPAXH
                               (Vint32 i0
                                :: Vint32 i1 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, MSMC_SESMPAXH,
                                 Vint32 i0
                                 :: Vint32 i1 :: nil) /\
                               struct_type_vallist_match MSMC_SESMPAXH
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             PV (ses_mpax_block, Int.repr (Int.unsigned index * 8 + 4)) @ Tint32
                             |-> Vint32 mpaxh' **
                             [|mpaxh' =
                               set_mpax_struct mpaxh
                                 (sesh_baddr ::
                                   sesh_segsize :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             [|ses' = SesMod.set ses index (mpaxl, mpaxh')|] **
                             Aabsdata ses_mpaxid (osses_mpax ses') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H10.
         simpl Astruct.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 5 eexists.
      exists (set OO ses_mpaxid
                                   (osses_mpax
                                      (SesMod.set ses index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (sesh_baddr
                                             :: sesh_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      exists (x5, x6, m1, x10, x11, x12).
      exists Ms.
      exists (set O ses_mpaxid
                                   (osses_mpax
                                      (SesMod.set ses index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (sesh_baddr
                                             :: sesh_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      do 2 eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.

Lemma csl_xmc_setXMPAXH_rule_sound:
        forall Spec sd I r ri  P P' e1 e2 n q aop pa t index xmc mpaxl mpaxh vl strheap,
                  can_change_aop P' ->
                  n = Vint32 index ->
                  (0 <= Int.unsigned index < 16)%Z ->
                  rule_type_val_match Tint32 (Vint32 mpaxl) = true ->
                  rule_type_val_match Tint32 (Vint32 mpaxh) = true ->
                  XmcMod.get xmc index = Some (mpaxl, mpaxh) ->
                  P ==> Rv e1 @ Tint32 ==  n //\\ Rv e2 @ Tptr XMC_XMPAXH == Vptr q ->
                  P ==> Astruct q XMC_XMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                              [| Get_struct strheap q = Some (q, XMC_XMPAXH, vl) /\ struct_type_vallist_match XMC_XMPAXH vl |] ** 
                              PV (xmpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh)  ** 
                              Aabsdata xmpaxid (osxmpax xmc) ** P' ->
                  ( EX xmc' mpaxh',
                           Astruct q XMC_XMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                           [| Get_struct strheap q = Some (q, XMC_XMPAXH, vl) /\ struct_type_vallist_match XMC_XMPAXH vl |] **
                           PV (xmpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                           [| mpaxh' = set_mpax_struct mpaxh (xmc_baddr :: xmc_segsize :: nil) vl |] **
                           [| xmc' = XmcMod.set xmc index (mpaxl, mpaxh') |] ** Aabsdata xmpaxid (osxmpax xmc') ** P' ) ==> CurLINV pa t ->
                  RuleSem Spec sd pa I r ri
                    (<|| (csl_xmc_setXMPAXH n q);; aop ||> ** P)
                    (sprim (scsl_xmc_setXMPAXH e1 e2))  
                    (<|| aop ||>  ** 
                      EX xmc' mpaxh', 
                           Astruct q XMC_XMPAXH vl ** Aabsdata evstructheapid (evstructheap strheap) **
                           [| Get_struct strheap q = Some (q, XMC_XMPAXH, vl) /\ struct_type_vallist_match XMC_XMPAXH vl |] **
                           PV (xmpax_block, (Int.repr ((Int.unsigned index)*8 + 4)%Z)) @ Tint32 |-> (Vint32 mpaxh')  ** 
                           [| mpaxh' = set_mpax_struct mpaxh (xmc_baddr :: xmc_segsize :: nil) vl |]  **
                           [| xmc' = XmcMod.set xmc index (mpaxl, mpaxh') |] ** Aabsdata xmpaxid (osxmpax xmc') ** P' ) t.
Proof.
  introv Haop Hindex Hrange
         Hmatch1 Hmatch2 Hsms HPeval HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct q as (b & i).
  destruct Hrange as (Hrgn1 & Hrgn2).
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  do 3 (destruct vl; simpl in H29; 
  try (destruct v; destruct H29 as (Heq&H29); inverts Heq); tryfalse).
  destruct (Int.unsigned i1 <=? Byte.max_unsigned)%Z eqn:eq1;tryfalse.

   rewrite Int.unsigned_repr in *; eauto.
   2:{ clear -Hrgn1 Hrgn2.
          change Int.max_unsigned with 4294967295%Z. auto with zarith. }

   rename H3 into Heq.
   simpl in Heq.
   unfold emposabst in *.
   destruct_rename Heq mx1 Hj1 Ho1 Hmap1.
   destruct_rename Heq mx2 Hj2 Ho2 Hmap2.
   simpljoin.
   repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).

  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.

  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
    destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf & _).
    exfalso. apply Hf. unfolds.
    do 4 eexists; eauto.

  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt, not.
    introv Hf.
    apply Hf. clear Hf.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H8 as [? [_ ?]].
    unfold getmem in H8.
    simpl in H6, H8. simpljoin.

     lets HH : store_exist_join H18 H15 H0 H8.
     destruct HH as (M2' & Hst).

     do 2 eexists.
     eapply csl_xmc_setXMPAXH_step with
                     (x:= mpaxh) (x1:= i0) (x2:= i1); auto;
      try solve [erewrite evaltype_irrev_mem; eauto];
      try solve [eapply evalval_mono'; eauto];
      try solve [ congruence];
      try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end).
     - join auto.
     - join auto.
     - rewrite Z.add_0_r. eauto.
     - join auto.
     - erewrite Hst; eauto.

   +  simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
       lets Hlem: evalval_mono_joinmem.
       specialize Hlem with (o1:= (G, E, M, irr, ierr, aux)).
       simpl get_smem in Hlem.
      lets Hev2: H1.
      eapply Hlem in Hev2; eauto.
      lets Hev2': Hev2.
      eapply evalval_mono_joinmem in Hev2'; eauto.
      lets Hev1: H.
      eapply Hlem in Hev1; eauto.
      lets Hev1': Hev1.
      eapply evalval_mono_joinmem in Hev1'; eauto.

      invertstep tryfalse.
      unfold joinmem in H6, H8.
      simp join.
      simpl get_smem in Hev2 , Hev2', Hev1 , Hev1'.

      rewrite H16 in Hev2'.
      rewrite H14 in Hev1'.
      inverts Hev2'; inverts Hev1'.
      rewrite Z.add_0_r in *.
      assert (Heqv: Vint32 mpaxh = Vint32 x2 /\
                                 Vint32 i0 = Vint32 x3  /\ Vint32 i1 = Vint32 x4).
      { splits; eapply lmachLib.load_mem_deter; eauto;
         try (match goal with
       | |- load _ _ _ = _ =>
              (match goal with
                | H : mapstoval _ _ _ (Vint32 ?v) ?mx |- load _ _ _ = Some (Vint32 ?v)
                    => eapply load_local with (m1:= mx);
                          [eauto
                            | eapply mapstoval_load; eauto;
                               try unfold rule_type_val_match; 
                               try rewrite eq1; eauto  ]
                  end)
       end);
            try solve [unfold Maps.sub; eexists; join auto].
            unfold Maps.sub; join auto.
       }
       destruct Heqv as (Heq1 & Heq2 & Heq3).
       eapply eq_sym in Heq1, Heq2, Heq3; eauto.
       inverts Heq1; inverts Heq2; inverts Heq3.

      lets Hst_mpaxh : store_exist_join' H18 (map_join_emp x17).
      destruct Hst_mpaxh as (m' & Hst_mpaxh).
      lets Hst_mpaxh0 : store_exist_join'  H18 H15.
      destruct Hst_mpaxh0 as (m0 & Hst_mpaxh0).
      lets Hst_mpaxh1 : store_exist_join H18 H15 H0 (map_join_emp x15).
      destruct Hst_mpaxh1 as (m1 & Hst_mpaxh1).
      lets Hst_mpaxh2 : store_exist_join  H18 H15 H0 H26.
      destruct Hst_mpaxh2 as (m2 & Hst_mpaxh2).
      lets Hjnew: join_store_join (join_comm H15) Hst_mpaxh Hst_mpaxh0.
      eapply join_comm in Hjnew.
      lets Hjnew0: join_store_join H0 Hst_mpaxh0 Hst_mpaxh1.
      lets Hjnew1: join_store_join (join_comm H26) Hst_mpaxh1 Hst_mpaxh2.
      eapply join_comm in Hjnew1.
      lets Hjnew2: join_store_join (join_comm H10) Hst_mpaxh2 H28.
      eapply join_comm in Hjnew2.
      lets Heq: Hjnew. eapply join_merge in Heq.
      lets Heq0: Hjnew. eapply join_merge in Heq0.
      lets Heq1: Hjnew1. eapply join_merge in Heq1.
      lets Heq2: Hjnew2. eapply join_merge in Heq2.

      assert (HPlinv_pre:
                       forall aop0,
                          (x5, x6, m1, x10, x11, x12,
                          set O xmpaxid
                            (osxmpax
                               (XmcMod.set xmc index
                                  (mpaxl, set_mpax_struct mpaxh
                                     (xmc_baddr
                                      :: xmc_segsize :: nil)
                                     (Vint32 i0
                                      :: Vint32 i1 :: nil)))), aop0)
                          |= EX (xmc' : XmcMod.map) (mpaxh' : int32),
                             Astruct (b, i) XMC_XMPAXH
                               (Vint32 i0
                                :: Vint32 i1 :: nil) **
                             Aabsdata evstructheapid (evstructheap strheap) **
                             [|Get_struct strheap (b, i) =
                               Some
                                 (b, i, XMC_XMPAXH,
                                 Vint32 i0
                                 :: Vint32 i1 :: nil) /\
                               struct_type_vallist_match XMC_XMPAXH
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             PV (xmpax_block, Int.repr (Int.unsigned index * 8 + 4)) @ Tint32
                             |-> Vint32 mpaxh' **
                             [|mpaxh' =
                               set_mpax_struct mpaxh
                                 (xmc_baddr ::
                                   xmc_segsize :: nil)
                                 (Vint32 i0
                                  :: Vint32 i1 :: nil)|] **
                             [|xmc' = XmcMod.set xmc index (mpaxl, mpaxh')|] **
                             Aabsdata xmpaxid (osxmpax xmc') ** P').
     { intros. 
        sep eexists.
         sep split; eauto.
         2 : { split; auto.
                  simpl. rewrite eq1. splits; auto. }

         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H6.
         simpl Astruct.
         simpl sat.
         unfold emposabst.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         do 6 eexists. splits; eauto.
         eapply join_comm.
         eapply old.Unnamed_thm.
         eapply old.Unnamed_thm.
         exists m'. do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         split; auto.
         rewrite Int.unsigned_repr in *; eauto.
        2:{
             clear -Hrgn1 Hrgn2.
             change Int.max_unsigned with 4294967295%Z. auto with zarith.
        }
         eapply mapstoval_store_changeval; eauto.
         eapply change_aop_rule; eauto.
     }

      do 4 eexists.
      exists (set OO xmpaxid
                                   (osxmpax
                                      (XmcMod.set xmc index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (xmc_baddr
                                             :: xmc_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      exists (x5, x6, m1, x10, x11, x12).
      exists Ms.
      exists (set O xmpaxid
                                   (osxmpax
                                      (XmcMod.set xmc index
                                         (mpaxl, set_mpax_struct mpaxh
                                            (xmc_baddr
                                             :: xmc_segsize :: nil)
                                    (Vint32 i0
                                     :: Vint32 i1 :: nil))))).
      do 2 eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply join_lib.join_sig_get; eauto. join auto.
         apply join_lib.join_set_l; auto.
         apply OSAbstMod.get_indom.
         eexists.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
      - unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.


Lemma csl_xmc_clearFault_rule_sound:
  forall Spec sd I r ri  P P' aop pa t vfar vfsr,
            can_change_aop P' ->
            P ==> PV xmpfar_addr @ Tint32 |-> (Vint32 vfar)  ** Aabsdata xmpfarid (xmpfar vfar) **
                               PV xmpfsr_addr @ Tint32 |-> (Vint32 vfsr)  ** Aabsdata xmpfsrid (xmpfsr vfsr) ** P' ->
            (EX vfsr',
                           [| vfsr' = set_part (set_part vfsr 26%nat 0%nat Int.zero) 23%nat 8%nat Int.zero |] **
                           PV xmpfar_addr @ Tint32 |-> (Vint32 Int.zero)  ** Aabsdata xmpfarid (xmpfar Int.zero) **
                           PV xmpfsr_addr @ Tint32 |-> (Vint32 vfsr')  ** Aabsdata xmpfsrid (xmpfsr vfsr') ** P') ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_xmc_clearFault);; aop ||> ** P)
              (sprim (scsl_xmc_clearFault))
              (<|| aop ||>  ** 
                EX vfsr',
                           [| vfsr' = set_part (set_part vfsr 26%nat 0%nat Int.zero) 23%nat 8%nat Int.zero |] **
                           PV xmpfar_addr @ Tint32 |-> (Vint32 Int.zero)  ** Aabsdata xmpfarid (xmpfar Int.zero) **
                           PV xmpfsr_addr @ Tint32 |-> (Vint32 vfsr')  ** Aabsdata xmpfsrid (xmpfsr vfsr') ** P') t.
Proof.
  introv Haop HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  unfold emposabst in *; subst.
  repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
       destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf & _).
      exfalso. apply Hf. unfolds.
      eexists; eauto.
  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt, not.
      intros. apply H. clear H.

      destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
      apply joinm2_env_eq in Hjm1 as ?.
      apply joinm2_mem_join in Hjm1 as ?.
      unfold getmem in *. simpl in H, H1.
      simp join.

      match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2, Hj2: join ?M2 _ ?M5 |- _ =>
       lets Hs0: store_exist_join Hm  (map_join_emp M1) ((map_join_emp M1)) ;
                 try (eapply join_comm;  apply map_join_emp);
          destruct Hs0 as (? & Hs0);
        lets Hs: store_exist_join Hm Hj1 (map_join_emp M2); try (eapply join_comm;  apply map_join_emp);
        destruct Hs as (? & Hs);
        lets Hj0: join_store Hj1 Hs0 Hs;
        lets Hs': store_exist_join Hm Hj1 (join_comm Hj2) (map_join_emp M5); 
        destruct Hs' as (? & Hs');
        lets Hj: join_store Hj2 Hs Hs' end.

       match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2 |- _ =>
       lets Hs1: store_exist_join Hm Hj1 Hj0 Hj; destruct Hs1 as (? & ?) end.

      do 2 eexists.
      eapply csl_xmc_clearFault_step; eauto.
      eapply load_local; eauto.
      eapply load_local; eauto.
      eapply mapstoval_load; eauto.
      apply join_lib.join_comm in H0.
      eapply load_local; eauto.
      eapply load_local; eauto.
      eapply load_local; eauto.
      eapply mapstoval_load; eauto.
 +  simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
      invertstep tryfalse.
      unfold joinmem in *.
      simp join.
      assert (Heq: Vint32 vfsr = Vint32 vfsr0).
      { eapply lmachLib.load_mem_deter; eauto.
         eapply mapstoval_load; eauto.
         unfolds. eexists. join auto.
       }
      inverts Heq.

      match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2, Hj2: join ?M2 _ ?M5, Hj3: join ?M5 _ ?M7 |- _ =>
       lets Hs0: store_exist_join Hm  (map_join_emp M1) ((map_join_emp M1)) ;
                 try (eapply join_comm;  apply map_join_emp);
          destruct Hs0 as (m0 & Hs0);
        lets Hs: store_exist_join Hm Hj1 (map_join_emp M2); try (eapply join_comm;  apply map_join_emp);
        destruct Hs as (m1 & Hs);
        lets Hj0: join_store Hj1 Hs0 Hs;
        lets Hs': store_exist_join Hm Hj1 (join_comm Hj2) (map_join_emp M5); 
        destruct Hs' as (m2 & Hs');
        lets Hj: join_store Hj2 Hs Hs';
        lets Hs'': store_exist_join Hm Hj1 (join_comm Hj2) Hj3; 
        destruct Hs'' as (m3 & Hs'');
        lets Hj': join_store Hj3 Hs' Hs'' end.

       match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2 |- _ =>
       lets Hs0': store_exist_join' Hm (map_join_emp M1); destruct Hs0' as (? & Hs0');
       lets Hs0'': store_exist_join' Hm Hj1; destruct Hs0'' as (? & Hs0'');
       lets Hs1: store_exist_join Hm Hj1 Hj0 (map_join_emp m1) end.
       destruct Hs1 as (? & Hs1).
       lets Hjnew0': join_store Hs0' Hs0''; eauto.
       lets Hjnew0'': join_store (join_comm Hj0) Hs0'' Hs1; eauto.

       match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2 |- _ =>
       lets Hs2: store_exist_join Hm Hj1 Hj0 Hj; destruct Hs2 as (? & Hs2) end.
       lets Hs3: join_store_general (join_comm Hj') Hs2.
       destruct Hs3 as (m4 & Hs3).
       lets Hjnew0: join_store Hj Hs1 Hs2.
       lets Hjnew1: join_store Hj' Hs2 Hs3.
       match goal with
       Hs: store _ ?m (?b, _) _ = _, Hs': store _ ?m (?b, _) _ = _ |- _ =>
       lets Hjnew: join_store (map_join_emp m) Hs Hs';
       eapply map_join_emp' in Hjnew; subst end.
      match goal with
       Hs: store _ ?m (?b, _) _ = _, Hs': store _ ?m (?b, _) _ = _ |- _ =>
       lets Hjnew: join_store (map_join_emp m) Hs Hs';
       eapply map_join_emp' in Hjnew; subst end.

       assert (HPlinv_pre:
                       forall aop0,
                          (x2, x3, x13, x6, x7, x8,
                            set (set O xmpfarid (xmpfar Int.zero)) xmpfsrid
                              (xmpfsr (set_part (set_part vfsr0 26 0 Int.zero) 23 8 Int.zero)), aop0)
                            |= EX vfsr' : int32,
                               [|vfsr' = set_part (set_part vfsr0 26 0 Int.zero) 23 8 Int.zero|] **
                               PV xmpfar_addr @ Tint32 |-> Vint32 Int.zero **
                               Aabsdata xmpfarid (xmpfar Int.zero) **
                               PV xmpfsr_addr @ Tint32 |-> Vint32 vfsr' **
                               Aabsdata xmpfsrid (xmpfsr vfsr') ** P').
      { intros.
         sep eexists.
         sep split; eauto.
         sep lifts (2 :: 4 :: 1 :: 3 :: nil)%nat.
         sep remember (1 :: 2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         eapply join_comm.
         eapply map_join_set_none.
         eapply join_comm; eauto.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         eapply get_a_sig_a'.
         introv Hf; try false.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H.
         simpl sat.
         unfold emposabst.
         exists m0; do 5 eexists.
         splits; eauto.
         3:{ split; auto.
                eapply mapstoval_store_changeval; eauto. }
         apply join_comm; eauto.
         eapply old.Unnamed_thm.
         exists x1. do 5 eexists. splits; eauto.
         2:{ split; auto.
                eapply mapstoval_store_changeval; eauto. }
         eapply old.Unnamed_thm.
         eapply change_aop_rule; eauto.
      }

       do 3 eexists.
      exists (set (set OO xmpfarid (xmpfar Int.zero))
                           xmpfsrid (xmpfsr (set_part (set_part vfsr0 26 0 Int.zero) 23 8 Int.zero))).
      do 2 eexists.
      exists (set (set O xmpfarid (xmpfar Int.zero))
                           xmpfsrid (xmpfsr (set_part (set_part vfsr0 26 0 Int.zero) 23 8 Int.zero))).
      eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply join_lib.join_sig_get; eauto.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
         apply join_lib.join_set_l; auto.
         apply join_lib.join_set_l; auto.
         unfolds; eexists.
         eapply OSAbstMod.join_sig_get; eauto.
         unfolds; eexists.
         rewrite map_get_set'; auto.
         eapply OSAbstMod.join_get_r; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
         introv Hf; tryfalse.
      -  unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.


Lemma csl_cgem_clearMDMAError_rule_sound:
  forall Spec sd I r ri  P P' aop pa t verr,
            can_change_aop P' ->
            P ==> PV mdmaerr_addr @ Tint32 |-> (Vint32 verr)  ** Aabsdata mdmaerrid (mdmaerr verr) ** P' ->
            (EX verr',
                           [| verr' = set_part (set_part (set_part verr 29%nat 0%nat Int.zero) 20%nat 8%nat Int.zero) 0%nat 29%nat Int.zero |] **
                           PV mdmaerr_addr @ Tint32 |-> (Vint32 verr')  ** Aabsdata mdmaerrid (mdmaerr verr') ** P') ==> CurLINV pa t ->
            RuleSem Spec sd pa I r ri
              (<|| (csl_cgem_clearMDMAError);; aop ||> ** P)
              (sprim (scsl_cgem_clearMDMAError))
              (<|| aop ||>  ** 
                EX verr',
                           [| verr' = set_part (set_part (set_part verr 29%nat 0%nat Int.zero) 20%nat 8%nat Int.zero) 0%nat 29%nat Int.zero |] **
                           PV mdmaerr_addr @ Tint32 |-> (Vint32 verr')  ** Aabsdata mdmaerrid (mdmaerr verr') ** P') t.
Proof.
  introv Haop HPaddr HPlinv.
  unfolds.
  introv Hsat.
  destruct Hsat as [Hsat1 Hsat2].
  destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1.
  simpl in H.
  subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  unfold emposabst in *; subst.
  repeat try (match goal with
                      | H : join empenv _ _ |- _ => apply join_lib.join_emp_eq in H; subst
                      | H : join _ empenv ?mx |- _ => apply join_lib.join_comm in H; apply join_lib.join_emp_eq in H; subst mx
                      end).
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
       destruct Hlostep as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_ &_&_& Hf).
      exfalso. apply Hf. unfolds.
      eexists; eauto.
  + introv Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt, not.
      intros. apply H. clear H.

      destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
      apply joinm2_env_eq in Hjm1 as ?.
      apply joinm2_mem_join in Hjm1 as ?.
      unfold getmem in *. simpl in H, H1.
      simp join.

      match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2, Hj2: join ?M2 _ ?M5 |- _ =>
       lets Hs0: store_exist_join Hm  (map_join_emp M1) ((map_join_emp M1)) ;
                 try (eapply join_comm;  apply map_join_emp);
          destruct Hs0 as (? & Hs0);
        lets Hs: store_exist_join Hm Hj1 (map_join_emp M2); try (eapply join_comm;  apply map_join_emp);
        destruct Hs as (? & Hs);
        lets Hj0: join_store Hj1 Hs0 Hs;
        lets Hs': store_exist_join Hm Hj1 (join_comm Hj2) (map_join_emp M5); 
        destruct Hs' as (? & Hs');
        lets Hj: join_store Hj2 Hs Hs' end.

       (* match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2 |- _ =>
       lets Hs1: store_exist_join Hm Hj1 Hj0 Hj; destruct Hs1 as (? & ?) end. *)

      do 2 eexists.
      eapply csl_cgem_clearMDMAError_step; eauto.
      eapply load_local; eauto.
      eapply load_local; eauto.
      eapply mapstoval_load; eauto.
 +  simpl substaskst in *.
      introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
       unfold joinm2 in Hjm1.
       simpljoin.
      invertstep tryfalse.
      unfold joinmem in *.
      simp join.
      assert (Heq: Vint32 verr = Vint32 verr0).
      { eapply lmachLib.load_mem_deter; eauto.
         eapply mapstoval_load; eauto.
         unfolds. eexists. join auto.
       }
      inverts Heq.

      match goal with
       Hm: mapstoval (?b , _) _ _ _ ?M1, Hj1: join ?M1 _ ?M2, Hj2: join ?M2 _ ?M5, Hj3: join ?M5 _ ?M7 |- _ =>
       lets Hs0: store_exist_join Hm  (map_join_emp M1) ((map_join_emp M1)) ;
                 try (eapply join_comm;  apply map_join_emp);
          destruct Hs0 as (m0 & Hs0);
        lets Hs: store_exist_join Hm Hj1 (map_join_emp M2); try (eapply join_comm;  apply map_join_emp);
        destruct Hs as (m1 & Hs);
        lets Hj0: join_store Hj1 Hs0 Hs;
        lets Hs': store_exist_join Hm Hj1 (join_comm Hj2) (map_join_emp M5); 
        destruct Hs' as (m2 & Hs');
        lets Hj: join_store Hj2 Hs Hs';
        lets Hs'': store_exist_join Hm Hj1 (join_comm Hj2) Hj3; 
        destruct Hs'' as (m3 & Hs'');
        lets Hj': join_store Hj3 Hs' Hs'' end.

       match goal with
       Hs: store _ ?m (?b, _) _ = _, Hs': store _ ?m (?b, _) _ = _ |- _ =>
       lets Hjnew: join_store (map_join_emp m) Hs Hs';
       eapply map_join_emp' in Hjnew; subst end.
      match goal with
       Hs: store _ ?m (?b, _) _ = _, Hs': store _ ?m (?b, _) _ = _ |- _ =>
       lets Hjnew: join_store (map_join_emp m) Hs Hs';
       eapply map_join_emp' in Hjnew; subst end.

       assert (HPlinv_pre:
                       forall aop0,
                          (x2, x3, m1, x6, x7, x8,
                          set O mdmaerrid
                            (mdmaerr
                               (set_part (set_part (set_part verr0 29 0 Int.zero) 20 8 Int.zero) 0 29
                                  Int.zero)), aop0)
                          |= EX verr' : int32,
                             [|verr' =
                               set_part (set_part (set_part verr0 29 0 Int.zero) 20 8 Int.zero) 0 29
                                 Int.zero|] **
                             PV mdmaerr_addr @ Tint32 |-> Vint32 verr' **
                             Aabsdata mdmaerrid (mdmaerr verr') ** P').
      { intros.
         sep eexists.
         sep split; eauto.
         sep remember (2 :: nil)%nat.
         simpl.
         exists (empenv: mem). do 5 eexists. splits; eauto.
         eapply old.Unnamed_thm.
         erewrite <- set_sig .
         eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none.
         2:{ eapply join_comm.  eapply old.Unnamed_thm. }
         unfold disjoint; eauto.
         subst H.
         simpl sat.
         unfold emposabst.
         exists m0; do 5 eexists.
         splits; eauto.
         2:{ split; auto.
                eapply mapstoval_store_changeval; eauto. }
         eapply old.Unnamed_thm.
         eapply change_aop_rule; eauto.
      }

       do 3 eexists.
      exists (set OO mdmaerrid (mdmaerr (set_part (set_part (set_part verr0 29 0 Int.zero) 20 8 Int.zero) 0 29 Int.zero))).
      do 2 eexists.
      exists (set O mdmaerrid (mdmaerr (set_part (set_part (set_part verr0 29 0 Int.zero) 20 8 Int.zero) 0 29 Int.zero))).
      eexists.
      splits; eauto.
       - constructor.
       - econstructor; eauto.
         eapply OSAbstMod.join_sig_get; eauto.
         apply join_lib.join_set_l; auto.
         unfolds; eexists.
         eapply OSAbstMod.join_sig_get; eauto.
      -  unfold joinm2, joinmem.
         eexists; split; do 7 eexists; splits; eauto.
      - eapply map_join_set_none; eauto.
         eapply osabst_disjoint_join_sig_get_none; eauto.
         unfold disjoint.
         eexists; join auto.
      - unfold satp. intros.
         apply HPlinv; eauto.
      - (*last goal: <_ msim*)
         constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros. subst. inverts Hhf.
           exists aop. exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv; eauto.
       (* _ |=lift (<||aop||> ** (...)) *)
        { unfold lift.
          sep lift 2%nat.
          sep normal.
          clear -HPlinv_pre Haop.
          specialize HPlinv_pre with (aop0 := aop).
          sep auto.
         }
     ++ intros.
       destruct Hhf as [ _ Hhf ].
       destruct Hhf as (_&Hhf&_).
       unfolds in Hhf.
       exfalso.
       apply Hhf.
       cbv. eauto.
Qed.


