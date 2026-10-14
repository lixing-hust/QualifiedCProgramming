Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.
Require Import ev_aux_code.
Require Import ifun_spec.
Require Import include_frm.
Require Import os_inv.
Require Import ucos_frmaop.
Require Import abs_step.
Require Import init_spec.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward. (*change*)
Require Import math_auto.
Require Import sem_lab.
Require Import symbolic_lemmas.
Require Import gjb_common.
Require Import abs_op.
Require Import include_frm.
Require Import NPeano.
Require Import ucos_pauto.
Require Import os_inv.
Require Import abs_infer_abt.
Require Import seplog_trm_tacs.
Require Import evt_spec_defs.
Require Import ifun_spec.
Require Import partition_xml_init.
Require Import abs_op_partition_ext.
Require Import ifun_spec.

Require Import hoare_assign_tac_ext.
Require Import hoare_forward_tac_ext.
Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

(*----------------------------------------------------------------*)
(* internal function spec                                         *)
(*----------------------------------------------------------------*)
Open Scope Z_scope.
Open Scope int_scope.
Require Import List.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma struct_array_member_rv':
  forall decls s e1 te1 e2 te2 b o t n m vl v k t' id sid P, 
    s |= Rv e1 @ te1 == Vptr (b, o) ->
    s |= Rv e2 @ te2 == Vint32 m ->
    (te1 = Tarray t n \/ te1 = t ∗) -> 
    (te2 = Int8u \/ te2 = Int16u \/ te2 = Int32u) ->
    s |= Astruct (b, o +ᵢ  $ Z.of_nat (Z.to_nat (Int.unsigned m) * typelen t)) t vl ** P -> 
    t = Tstruct sid decls -> 
    good_decllist decls = true -> 
    Int.ltu m Int.zero = false -> 
    Int.unsigned m <= Int.max_signed -> 
    Int.min_signed <= Z.of_nat (szstruct decls) <= Int.max_signed -> 
    struct_type_vallist_match t vl -> 
    ftype id decls = Some t' ->
    (~(exists t'' n, t' = Tarray t'' n) /\ ~(exists sid' ds', t' = Tstruct sid' ds')
    /\ ~(exists sid' ds', t' = Tunion sid' ds')) ->  
    (id_nth id decls) = Some k ->
    nth_val' k vl = v -> 
    s |= Rv efield (e1[e2]) id @ t' == v. 
Proof. 
  introv He1 He2 Hte1 Hte2 Hastruct Ht Hgdecls Hmgez. 
  introv Hmle Hszrgn.
  introv Hmt Hidtp Ht' Hoff Hv. 
  subst t.
  unfold Astruct in Hastruct.
  assert (Hnth: nth_id k decls = Some id).
  { apply id_nth_eq; auto. }
  pose proof (nth_id_exists_off _ _ Hnth).
  destruct H as (off & Hfdoff).
  gen Hv.
  destruct Hastruct. simpljoin1.
  introv Hv.
  rename H8 into Hastruct.
  erewrite struct_asrt_eq with (id:=id) (dls:=decls) (v:=v) (t:=t') (n:=k) in Hastruct;
    eauto.
  2: {
    subst v. apply nth_val_imp_nth_val'_2.
    assert (k < len_decllist decls)%nat.
    { eapply id_nth_lt_len; eauto. }
    erewrite <- astruct_dls_vl_len; eauto.
  }
  destruct s as [[[[[[[]]]]]]].
  destruct Hastruct. 
  gen Hv.
  simpljoin1. change_smo_hyps.
  destruct H11.
  simp_mem_abst.
  simpl in H.
  destruct He1.  destruct He2. mytac. intro Hv.
  simpl in H11. simpl in H13. simpl in H14. simpl in H15.
  assert (Hrtpvmt: rule_type_val_match t' v = true).
  { eapply struct_rule_type_vll_mt; eauto. }
  simpl_sat_goal.
  change (getsmem (e, e0, m0, i, i0, l, o0, a)) with (e, e0, m0).
  simpl.
  rewrite H13.
  destruct Hte1 as [Hte1' | Hte1']; subst te1; 
  rewrite H15; 
  destruct Hte2 as [Hte2' | [Hte2' | Hte2']]; subst te2;
  try (
      rewrite Hidtp; 
      rewrite H11; 
      rewrite H14; 
      unfold getoff;  
      simpl; rewrite H13; rewrite H15;
      rewrite Hfdoff; 
      splits; auto;
      [
        eapply mapstoval_load in H; auto;
        simpl; rewrite Int.repr_unsigned;
        rewrite <- mul_sz_decls; auto;
        assert (Hsub: Maps.sub x1 m0) by (join_to_sub; eapply sub_trans; eauto);
        eapply lmachLib.load_mem_mono; eauto
      |
        eapply rule_type_val_match_nvundef; eauto]).
Qed.

Lemma struct_type_vallist_match_elim_14 :
  forall x1 t1 x2 t2 x3 t3 x4 t4 x5 t5 x6 t6 x7 t7 x8 t8 x9 t9 x10 t10 x11 t11 x12 t12 x13 t13 x14 t14 v,  
    struct_type_vallist_match'(dcons x14 t14 (dcons x13 t13 (dcons x12 t12 (dcons x11 t11(dcons x10 t10 (dcons x9 t9 (dcons x8 t8 (dcons x7 t7 (dcons x6 t6 (dcons x5 t5 (dcons x4 t4 (dcons x3 t3 (dcons x2 t2 (dcons x1 t1 dnil)))))))))))))) v -> 
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
      exists v11 v12 v13 v14,
        v =v14::v13::v12::v11::v10::v9::v8::v7::v6::v5::v4::v3::v2::v1::nil.
Proof.
  intros;  simpl.
  destruct v; simpl struct_type_vallist_match' in H; tryfalse.
  destruct t14;simp join;
  match goal with
    | H : context[struct_type_vallist_match'] |- _ => 
      apply struct_type_vallist_match_elim_13 in H;auto;simp join
  end; 
  do 14 eexists;  eauto; repeat (splits; auto).
Qed.

Lemma ucons_length :
forall vl,
  struct_type_vallist_match ucos_conf_t vl -> 
  (13 < length vl)%nat.
Proof.
  introv Hstr.
  simpl in Hstr.
  eapply struct_type_vallist_match_elim_14 in Hstr.
  destruct Hstr as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 &
                    v10 & v11 & v12 & v13 & v14 & Hstr); subst.
  simpl; auto with zarith.
Qed.

Ltac conv_max_unsigned' :=
  try change Int.max_unsigned with 4294967295 in *;
  try change Int.max_signed with 2147483647 in *;
  try change Int.min_signed with (Z.opp 2147483648) in *.

Ltac unfold_part_defs :=
try unfold CORENUM in *;
try unfold DSCHEDULE_SIZE in *;
try unfold DOMAIN_SIZE in *;
try unfold PARTITION_NUM in *;
try unfold PORT_NUMS in *;
try unfold PTHREAD_STACK_MIN in *;
try change (Z.to_nat (2 * 4096 / 4)) with 2048%nat.

Ltac solve_part_int_rgn :=
conv_max_unsigned';
unfold_part_defs;
auto with zarith.

Lemma cnum_le:
forall cnum,
            Int.unsigned cnum < CORENUM ->
            Int.unsigned cnum <= Int.max_signed.
solve_part_int_rgn.
Qed.

Lemma cnum_le':
forall cnum,
            Z.of_nat cnum < CORENUM ->
            Z.of_nat cnum <= Int.max_signed.
solve_part_int_rgn.
Qed.

Lemma cpu_conf_t_min_max:
     (Int.min_signed <= 910 <= Int.max_signed)%Z.
solve_part_int_rgn.
Qed.


Ltac sep_get_rv_array_struct_conf :=
let Hsat := fresh in
let Hf := fresh in
let Heq := fresh in
match goal with
| |- ?P ==> Rv efield ((efield (ederef ?gident) ?id1)[?ident ′]) ?id2 @ ?tp1 == _ =>
      introv Hsat;
      eapply struct_array_member_rv';
      [ try symbolic_execution; eauto
      | try symbolic_execution
      | auto
      | auto
      | try (match goal with
                  Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                     match find_ptrstruct_by_block P' pb with
                       | some ?n => sep lifts (( n) :: nil) in Hsat
                       end
                  end);
         try sep cancel Astruct; eauto
      | match goal with
        | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
        end; auto
      | simpl; auto
      | try apply int_ltu_zero_eq_false
      | try (apply cnum_le; auto); try (apply cnum_le'; auto)
      | simpl; try apply cpu_conf_t_min_max
      | auto
      | simpl; auto
      | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
      | unfold id_nth; simpl; auto
      | auto ]
| Hsat:?s |= ?P
  |- ?s |= Rv efield ((efield (ederef ?gident) ?id1)[?ident ′]) ?id2 @ ?tp1 == _ =>
              eapply struct_array_member_rv';
              [ try symbolic_execution; eauto
              | try symbolic_execution
              | auto
              | auto
              | try (match goal with
                          Hsat: _ |= ?P' |- _ |= Astruct (?pb, ?pi) _ _ ** _ =>
                             match find_ptrstruct_by_block P' pb with
                               | some ?n => sep lifts (( n) :: nil) in Hsat
                               end
                          end);
                 try sep cancel Astruct; eauto
              | match goal with
                | |- ?tp = STRUCT _ ­{ _ }­ => try unfold tp
                end; auto
              | simpl; auto
              | try apply int_ltu_zero_eq_false
              | try (apply cnum_le; auto); try (apply cnum_le'; auto)
              | simpl; try apply cpu_conf_t_min_max
              | auto
              | simpl; auto
              | splits; intro Hf; destruct Hf as (t''_0, (n_0, Hf)); inv Hf
              | unfold id_nth; simpl; auto
              | auto ]
end.

Lemma typematch_size:
forall i,
  Int.unsigned i <= 255->
  rule_type_val_match char_t (Vint32 i) = true.
Proof.
  intros.
  unfolds.
  rewrite byte_max_unsigned_val.
  eapply leb_bytemax_true_intro in H.
  rewrite byte_max_unsigned_val in H.
  rewrite H. eauto.
Qed.

Set Nested Proofs Allowed.

Lemma good_frm_AKsDomain :
  forall vl,  GoodFrm (AKsDomain vl).
Proof.
  intros.
  unfold AKsDomain.
  good_frm_sovler.
Qed.

Lemma good_frm_AOSPortAttrTbl' :
  forall vl,  GoodFrm (AOSPortAttrTbl' vl).
Proof.
  intros.
  unfold AOSPortAttrTbl'.
  good_frm_sovler.
Qed.


Lemma intunsign_z:
forall x,
  0<= x < 8 ->
  0 <= Int.unsigned ($ x) < 8.
Proof.
intros.
destruct H.
destruct x.
split.
mauto.
mauto.
mauto.
mauto.
Qed.

Lemma initConf_proof:
    forall vl p r logicl ct, 
      Some p =  
      BuildPreI os_internal initConf vl logicl initConfPre ct->
      Some r =
      BuildRetI os_internal initConf vl logicl initConfPost ct->
      exists t d1 d2 s,
        os_internal initConf = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec. tryfalse.
  subst logicl.
  (* sysEndian′ =ₑ  ′0;ₛ --------------------------- *)
  hoare forward.
  (* confEndian′ =ₑ ′0;ₛ--------------------------- *)
  hoare forward.
  (* conf′ =ₑ 〈ucos_conf_t∗〉 eptrconst BOOT_DATA_ADDRESS;ₛ--------------------------- *)
  hoare forward.
  eapply assign_rule_lvar.
   
  split. intros.
  sep_lifts_trms_in H0 (Aisr,Ais,A_isr_is_prop).
  eapply a_isr_is_prop_split in H0.
  sep_lifts_trms_in H0 (uconf).
  sep auto. intros. 
  unfold A_isr_is_prop.
  destruct_s s.
  sep normal.
  sep auto.

  intros.
  eapply cast_rv_tptr.
  3:{ apply assign_type_match_true; simpl; auto. }
  3:{ intros.
      sep auto. }
  simpl.
  destruct s as [[[[[[[]]]]]]].
  simpl; split; eauto.
  eauto.
  (* flag′ =ₑ ′1;ₛ---------------------------*)
  hoare forward.
  (* n1 ′ =ₑ conf ′ .. magicf;ₛ--------------------------- *)
  unfold AucosConf.
  destruct v'11.
  do 5 destruct p.
  destruct v'10.
  do 12 destruct p.
  hoare unfold.
  unfold BOOT_DATA_ADDRESS in *.
  unfold node.
  unfold Astruct.
  unfold ucos_conf_t.
  hoare unfold.
  simpl.
  hoare_lifts_trms_pre (flag ,uconf). 
  hoare remember (1 ::2 :: 17 :: nil)%nat pre.
  eapply backward_rule1 with (p := 
        (
         <|| v'12 ||>  **
         LV uconf @ ucos_conf_t ∗|-> Vptr (2147483648%positive, Int.zero) **
         LV flag @ long |-> (V$ 1) ** H0 ) \\//
        (
         <|| v'12 ||>  **
         LV uconf @ ucos_conf_t ∗|-> Vptr (2147483648%positive, Int.zero) **
         [|val_inj
         (bop_eval
            (val_inj
               (bop_eval
                  (val_inj
                     (bop_eval (Vint32 i6) (V$ 305419896) long long
                        oeq))
                  (val_inj
                     (bop_eval (Vint32 i4) (V$ 305419896) long long
                        oeq)) long long oand))
            (val_inj
               (bop_eval
                  (val_inj
                     (bop_eval (Vint32 i6) (V$ 2018910994) long long
                        oeq))
                  (val_inj
                     (bop_eval (Vint32 i4) (V$ 2018910994) long long
                        oeq)) long long oand)) long long oor) = Vint32 Int.one |]**
         LV flag @ long |-> (V$ 0) ** H0) 
  ).
  intros.
  left.
  sep cancel flag.
  sep cancel uconf. eauto.
  eapply seq_rule.
  eapply while_rule.
  intros.

  destruct H5.
  symbolic_execution.
  symbolic_execution.
  eapply backward_rule1 with (p :=
       (
         <|| v'12 ||>  **
         LV uconf @ ucos_conf_t ∗|-> Vptr (2147483648%positive, Int.zero) **
         LV flag @ long |-> (V$ 1) ** H0 )).
  intros.
  destruct H5.
  destruct H5. eauto.
  false.
  destruct_s s.
  sep remember (4::nil)%nat in H5.
  simpl in H5.
  simpljoin1.
  apply mapstoval_load in H22.
  2: auto.
  destruct (load long m4 (x18, 0)) eqn : eq1.
  pose proof (load_mono long (x18, Int.unsigned Int.zero) H13 H22). (*?????*)
  rewrite H22 in H0.
  change (Int.unsigned Int.zero) with 0 in H0.
  rewrite H0 in eq1.
  inverts eq1.
  simpl in H6.
  rewrite H21 in H6.
  destruct H6.
  destruct H5.
  rewrite H5 in H0.
  inverts H0.
  simpl in H6.
  change ($0) with (Int.zero) in H6.
  assert (Int.eq Int.zero Int.zero = true).
  {
    eapply eq_zero_zero.
  }
  rewrite H0 in H6.
  tryfalse.
  simpl in H6.
  rewrite H21 in H6.
  destruct H6.
  destruct H0.
  rewrite eq1 in H0.
  inverts H0. 
  (* If (((n1′ ==ₑ ′0x12345678)&&ₑ(n2′ ==ₑ ′0x12345678)) ||ₑ ((n1′   ==ₑ ′0x78562312)&&ₑ(n2′   ==ₑ ′0x78562312))){
           flag′ =ₑ ′0
  }*)
  hoare normal pre. 
  hoare_ex_intro.
  eapply forward_rule2.
  eapply ift_rule''.
  intros.
  eapply bop_rv;eauto.
  eapply bop_rv;eauto.
  eapply bop_rv;eauto.
  instantiate(2:= long).
  eapply struct_member_rv;eauto.
  instantiate(2:= (Vint32 i6
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: Vint32 i4 :: nil)).
  instantiate(2:= (⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t;
        noPartitions @ char_t; noCommChannels @ char_t; noPorts @
        char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
        area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
        Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t;
        portRdyTbl @ Tarray char_t ∘ 8; portTbl @
        Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟)).
  instantiate(2:=UCOS_CONF ).
  instantiate(2:=BOOT_DATA_ADDRESS).
  instantiate(2:= true).
  sep_lifts_trms_in H5 (uconf).
  unfold Astruct.
  unfold Astruct'.
  unfold BOOT_DATA_ADDRESS.
  unfold area_conf_t.
  sep auto.
  eauto.
  eauto.
  instantiate(1:=O); eauto.
  simpl. mauto.
  unfolds. unfolds. unfold area_conf_t.
  splits;eauto.

  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  
  eapply const_rv.
  eauto.
  simpl.
  destruct (Int.eq i6 ($ 305419896))  eqn:eq .
  simpl. eauto.
  simpl. eauto.
  unfolds.
  unfolds. eauto.
  eapply bop_rv;eauto.
  instantiate(2:= long).
  eapply struct_member_rv; eauto.
  instantiate(2:= (Vint32 i6
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: Vint32 i4 :: nil)).
  instantiate(2:= (⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t;
        noPartitions @ char_t; noCommChannels @ char_t; noPorts @
        char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
        area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
        Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t;
        portRdyTbl @ Tarray char_t ∘ 8; portTbl @
        Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟)).
  instantiate(2:=UCOS_CONF ).

  instantiate(2:=BOOT_DATA_ADDRESS).
  instantiate(2:= true).
  sep_lifts_trms_in H5 (uconf).
  unfold Astruct.
  unfold Astruct'.
  unfold BOOT_DATA_ADDRESS.
  unfold area_conf_t.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  eauto.
  eauto.
  instantiate(1:=S(S(S(S(S(S(S(S(S(S(S(S(S(O)))))))))))))); eauto.
  simpl.
  mauto.
  unfolds. unfolds. unfold area_conf_t.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  
  eapply const_rv.
  unfold val_inj.
  unfold nth_val'.
  unfold bop_eval.
  unfold val_eq.
  assert (Heq: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
  { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  destruct Heq; rewrite H6; auto.
  unfolds bop_type, cmp_int_type; eauto.
  simpl.
  assert (Heq1: Int.eq i6 ($ 305419896) = true \/ Int.eq i6 ($ 305419896) = false).
  { assert (Hran: i6 = ($ 305419896) \/ i6 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq2: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
  { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
  rewrite Heq1, Heq2; auto.
  unfold bop_type, bop_int_type; eauto.
  eapply bop_rv;eauto.
  eapply bop_rv;eauto.
  instantiate(2:= long).
  eapply struct_member_rv; eauto.
  instantiate(2:= (Vint32 i6
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: Vint32 i4 :: nil)).
  instantiate(2:= (⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t;
        noPartitions @ char_t; noCommChannels @ char_t; noPorts @
        char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
        area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
        Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t;
        portRdyTbl @ Tarray char_t ∘ 8; portTbl @
        Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟)).
  instantiate(2:=UCOS_CONF ).

  instantiate(2:=BOOT_DATA_ADDRESS).
  instantiate(2:= true).
  sep_lifts_trms_in H5 (uconf).
  unfold Astruct.
  unfold Astruct'.
  unfold BOOT_DATA_ADDRESS.
  unfold area_conf_t.
  sep auto.
  eauto.
  eauto.
  instantiate(1:=O); eauto.

  simpl.
  mauto.
  unfolds. unfolds. unfold area_conf_t.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.


  eapply const_rv.
  simpl.
  destruct (Int.eq i6 ($ 2018910994))  eqn:eq .
  simpl. eauto.
  simpl. eauto.
  unfolds.
  unfolds. eauto.
  eapply bop_rv;eauto.
  instantiate(2:= long).
  eapply struct_member_rv; eauto.
  instantiate(2:= (Vint32 i6
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: Vint32 i4 :: nil)).
  instantiate(2:= (⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t;
        noPartitions @ char_t; noCommChannels @ char_t; noPorts @
        char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
        area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
        Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t;
        portRdyTbl @ Tarray char_t ∘ 8; portTbl @
        Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟)).
  instantiate(2:=UCOS_CONF ).


  instantiate(2:=BOOT_DATA_ADDRESS).
  instantiate(2:= true).
  sep_lifts_trms_in H5 (uconf).
  unfold Astruct.
  unfold Astruct'.
  unfold BOOT_DATA_ADDRESS.
  unfold area_conf_t.
  sep auto.
  eauto.
  eauto.
  instantiate(1:=S(S(S(S(S(S(S(S(S(S(S(S(S(O)))))))))))))); eauto.
  simpl. mauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.

  eapply const_rv.
  simpl.
  
  assert (Heq: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
  { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  destruct Heq; rewrite H6; auto.
  unfolds bop_type, cmp_int_type; eauto.
  simpl.
  
  assert (Heq1: Int.eq i6 ($ 2018910994) = true \/ Int.eq i6 ($ 2018910994) = false).
  { assert (Hran: i6 = ($ 2018910994) \/ i6 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  } 
  assert (Heq2: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
  { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
  rewrite Heq1, Heq2; auto.
  unfolds bop_type, bop_int_type; eauto.
  simpl.

  assert (Heq1: Int.eq i6 ($ 305419896) = true \/ Int.eq i6 ($ 305419896) = false).
  { assert (Hran: i6 = ($ 305419896) \/ i6 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq2: Int.eq i6 ($ 2018910994) = true \/ Int.eq i6 ($ 2018910994) = false).
  { assert (Hran: i6 = ($ 2018910994) \/ i6 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq3: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
  { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq4: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
  { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
  destruct Heq3 as [Heq3 | Heq3]; destruct Heq4 as [Heq4 | Heq4];
  rewrite Heq1, Heq2, Heq3, Heq4; auto.
  unfolds bop_type, bop_int_type; eauto.
  hoare forward.
  pure_auto.
  destruct H5 as[H5|H5].
  right.
  simpljoin.
  sep auto.
  Optimize Proof.
  Optimize Heap.
  simpl. 

 assert (Heq1: Int.eq i6 ($ 305419896) = true \/ Int.eq i6 ($ 305419896) = false).
  { assert (Hran: i6 = ($ 305419896) \/ i6 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq2: Int.eq i6 ($ 2018910994) = true \/ Int.eq i6 ($ 2018910994) = false).
  { assert (Hran: i6 = ($ 2018910994) \/ i6 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq3: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
  { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  assert (Heq4: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
  { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
    destruct Hran; subst; auto.
    right; eapply Int.eq_false; auto.
  }
  simpl in H6;
  destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
  destruct Heq3 as [Heq3 | Heq3]; destruct Heq4 as [Heq4 | Heq4];
  rewrite Heq1, Heq2, Heq3, Heq4 in *;
  simpl in H6;
  try eapply semacc_int_eq_true in Heq1, Heq2;
  try eapply semacc_int_eq_true in Heq3, Heq4;
  try rewrite Heq1 in Heq2;
  try rewrite Heq3 in Heq4;
  simpl;
  change (Int.ltu Int.zero Int.one) with true in * ;
  change (Int.ltu Int.zero Int.zero) with false in * ;
  simpl; simpl in H6;
  change (Int.ltu Int.zero Int.one) with true in * ;
  change (Int.ltu Int.zero Int.zero) with false in * ;
  simpl; simpl in H6; destruct H6; tryfalse; auto.
  left.
  simpljoin.
  sep auto.
  apply disj_conj_distrib_pre.
  apply disj_rule.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  intros.
  instantiate (1:= (V$ 1)).
  instantiate (1:= long).
  symbolic execution. pauto.
  hoare_split_pure_all.
  destruct H5; tryfalse.
  eapply backward_rule1.
  eapply sep_aconj_r_aisfalse_to_astar.
  instantiate (1:= (V$ 0)).
  instantiate (1:= long).
  intros.
  symbolic execution;pauto.
  hoare_split_pure_all.
  destruct H6;tryfalse.

  hoare unfold.
  hoare forward.
  sep remember(27::nil)%nat in H0.
  sep auto.
  clear. pure_auto.
  
  eapply good_frm_AKsDomain.

  unfold retpost. 
  introv Hsat.
  inverts Hsat.
  sep pauto.
  sep pauto.
  introv Hsat. 
  sep destruct Hsat.
  destruct Hsat as [Hsat | Hsat].
  sep destruct Hsat.
  eexists.
  sep cancel p_local.
  simpl.
  eauto.
  sep destruct Hsat.
  eexists.
  sep cancel p_local.
  simpl.
  eauto.
  introv Hsat.
  sep destruct Hsat.
  eexists.
  sep cancel p_local.
  simpl.
  eauto.
  hoare unfold.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_split in Hsat.
  destruct Hsat as [Hsat|Hsat].
  eapply adisj_intro.
  left.
  eauto.
  right.
  eauto.
  hoare forward.
  hoare unfold.
  (*If (y ′ ==ₑ ′ 1){sysEndian ′ =ₑ ′ 1};ₛ*)
  (*case y = 0*)
  1:{
    hoare forward.
    hoare unfold.
    change (Int.eq ($ 0) ($ 1)) with false in H6.
    simpl in H6.
    tryfalse.
    hoare forward.
    hoare unfold.
    change (Int.eq ($ 0) ($ 1)) with false in H6.
    simpl in H6.
    tryfalse.
  (*base ′ =ₑ 〈 (char_t) ∗ 〉 (&ₐ conf′→ magicf ′);ₛ*)
    hoare forward.
    hoare unfold.
    hoare forward.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split.
    introv Hsat.
    sep remember (34::nil)%nat in Hsat.
    sep auto.
    intros.
    sep auto.
    intros.
    eapply cast_rv_tptr.
    eapply struct_offset_rv.
    eapply addrof_deref_rv.
    symbolic execution; pauto.

    instantiate(2:=UCOS_CONF).
    instantiate(1:=⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t; noPartitions @ char_t;
     noCommChannels @ char_t; noPorts @ char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
     area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
     Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t; portRdyTbl @ 
     Tarray char_t ∘ 8; portTbl @ Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟).
    eauto.
    instantiate(1:= $ 0).
    eauto.
    instantiate(1:= long).
    eauto.
    eauto.
    eauto.
    eapply assign_type_match_true.
    eauto.
    intros.
    sep auto.
    change (fst BOOT_DATA_ADDRESS, snd BOOT_DATA_ADDRESS +ᵢ  $ 0) with (2147483648%positive, Int.zero).
    inverts H12.
    lets Hval: H5.
    simpl in Hval, H5.
    assert (Heq1: Int.eq i6 ($ 305419896) = true \/ Int.eq i6 ($ 305419896) = false).
    { assert (Hran: i6 = ($ 305419896) \/ i6 <> ($ 305419896)) by tauto.
      destruct Hran; subst; auto.
       right; eapply Int.eq_false; auto.
    }
    assert (Heq2: Int.eq i6 ($ 2018910994) = true \/ Int.eq i6 ($ 2018910994) = false).
    { assert (Hran: i6 = ($ 2018910994) \/ i6 <> ($ 2018910994)) by tauto.
      destruct Hran; subst; auto.
      right; eapply Int.eq_false; auto.
    }
    assert (Heq3: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
    { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
      destruct Hran; subst; auto.
      right; eapply Int.eq_false; auto.
    }
    assert (Heq4: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
    { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
      destruct Hran; subst; auto.
      right; eapply Int.eq_false; auto.
    }
    destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
    destruct Heq3 as [Heq3 | Heq3]; destruct Heq4 as [Heq4 | Heq4];
    rewrite Heq1, Heq2, Heq3, Heq4 in *;
    simpl in Hval;
    try eapply semacc_int_eq_true in Heq1, Heq2;
    try eapply semacc_int_eq_true in Heq3, Heq4;
    try rewrite Heq1 in Heq2;
    try rewrite Heq3 in Heq4;
    simpl;
    change (Int.ltu Int.zero Int.one) with true in * ;
    change (Int.ltu Int.zero Int.zero) with false in * ;
    simpl; simpl in Hval;
    change (Int.ltu Int.zero Int.one) with true in * ;
    change (Int.ltu Int.zero Int.zero) with false in *;
    simpl; simpl in Hval; tryfalse; auto.
  (*Int.eq i ($ 305419896) = true /\ Int.eq i0 ($ 305419896) = true*)
    1:{
      change (fst (2147483648%positive, Int.zero), snd (2147483648%positive, Int.zero) +ᵢ  $ 0) with (2147483648%positive, Int.zero) in *.
      pose proof(semacc_int_eq_true( i6 ) ($ 305419896) Heq1);
      pose proof(semacc_int_eq_true( i4 ) ($ 305419896) Heq3); subst.
      hoare forward.
      eapply ift_rule_general.
      intros.
      eexists.
      eapply bop_rv; eauto.
      eapply deref_rv.
      eapply lvar_rv.
      sep auto.
  Optimize Proof.
  Optimize Heap.
      eauto.
      change (Int.zero +ᵢ  $ 0) with Int.zero.
      instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 86) ** 
                       PV (2147483648%positive, $2) @ char_t |-> (V$ 52) **
                       PV (2147483648%positive, $3) @ char_t |-> (V$ 18) **
                        <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
        char_t |-> Vint32 i2 **
        PV (2147483648%positive,
           (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
               +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  
            $ 7088) +ᵢ  $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
                 +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
              $ 416) +ᵢ  $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long
        |-> (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV confEndian @ char_t |-> (V$ 0) **
        LV sysEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).
      instantiate(2:= true).
      unfold Aptrmapsto at 1 2 3 4.
      sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
      sep remember(12::nil)%nat in H6.
      destruct_s s.
      unfold Aptrmapsto in H6.
      simpl in H6.
      simpl.
      simpljoin.
      unfold mapstoval in H17.
      simpljoin.
      simpl in H12.
      simpljoin.
      do 6 eexists.
      split.
      eauto.
      split.
      2:split.
      3:split.
      4:split.
      4:split.
      2:eauto.
      2:eauto.
      3:eauto.

      instantiate(2:= x7).
      join auto.
      unfolds.
      eexists.
      split.
      instantiate(2:= V$ 120).
      eauto.
      simpl.
      do 2 eexists.
      split.
      instantiate(2:= x7).
      instantiate(1:= empenv).
      join auto.  
      split.
      2:eauto.
      unfold ptomval in *.
      simpl.
      simpl.
      assert (Hby: Byte.repr (Int.unsigned ($ 305419896)) = Byte.repr (Int.unsigned ($ 120))).
      {
        try repeat rewrite Int.unsigned_repr.
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        eapply Byte.eqm_samerepr.
        unfold Byte.eqm, Byte.eqmod, Byte.modulus.
        unfold Byte.wordsize, Wordsize_8.wordsize.
        unfold two_power_nat, shift_nat, nat_rect.
        exists 1193046; auto. }
  rewrite H12.
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  eauto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256) = Byte.repr (Int.unsigned ($ 86))).
    {
      try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 4660; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists; split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256) = Byte.repr (Int.unsigned ($ 52))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 18; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 18))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  eauto.
  sep pauto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 120) (V$ 18) char_t long oeq) with (Some (Vint32 Int.zero)).
  eauto.
  simpl; eauto.
  intros.
  destruct H6.
  eapply H6.
  hoare forward.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  intros.
  eapply bop_rv.
  eapply deref_rv.
  eapply lvar_rv.
  sep auto.
  eauto.
  instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 86) ** 
                   PV (2147483648%positive, $2) @ char_t |-> (V$ 52) **
                   PV (2147483648%positive, $3) @ char_t |-> (V$ 18) **
                    <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
        char_t |-> Vint32 i2 **
        PV (2147483648%positive,
           (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
               +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  
            $ 7088) +ᵢ  $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
                 +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
              $ 416) +ᵢ  $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long
        |-> (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV confEndian @ char_t |-> (V$ 0) **
        LV sysEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).
  instantiate(2:= true).
  unfold Aptrmapsto at 1 2 3 4.
  sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
  sep remember(12::nil)%nat in H6.
  destruct_s s.
  unfold Aptrmapsto in H6.
  simpl in H6.
  simpl.
  simpljoin.
  unfold mapstoval in H17.
  simpljoin.
  simpl in H12.
  simpljoin.
  do 6 eexists.
  split.
  eauto.
  split.
  2:split.
  3:split.
  4:split.
  4:split.
  2:eauto.
  2:eauto.
  3:eauto.
  instantiate(2:= x7).
  join auto.
  unfolds.
  eexists.
  split.
  instantiate(2:= V$ 120).
  eauto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x7).
  instantiate(1:= empenv).
  join auto.  
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896)) = Byte.repr (Int.unsigned ($ 120))).
  {
    try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 1193046; auto. }
  rewrite H12.
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  eauto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256) = Byte.repr (Int.unsigned ($ 86))).
    {
      try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 4660; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists; split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256) = Byte.repr (Int.unsigned ($ 52))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 18; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 18))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  sep pauto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 120) (V$ 18) char_t long oeq) with (Some (Vint32 Int.zero)).
  instantiate(1:= Vint32 Int.zero).
  eauto.
  eauto.
  simpl.
  eauto.
  hoare unfold.
  tryfalse.
  instantiate(1:=  <|| v'26 ||>  **
  LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
  APortTbl (2147483648%positive, Int.zero) l m **
  LV sysEndian @ char_t |-> (V$ 0) **
  Aisr v'11 **
  Aie v'22 **
  Ais v'23 **
  Acs v'24 **
  Aier v'25 **
  p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
  LV y @ char_t |-> (V$ 0) **
  A_dom_lenv
    ((sysEndian, char_t)
     :: (confEndian, char_t)
        :: (y, char_t)
           :: (base, (char_t) ∗)
              :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
  LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
  LV flag @ long |-> (V$ 0) **
  PV (2147483648%positive, Int.zero) @ long |-> (V$ 305419896) **
  PV (2147483648%positive, Int.zero) @ long |-> (V$ 305419896) **
  PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
  PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
  |-> Vint32 i3 **
  PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
  char_t |-> Vint32 i2 **
  PV (2147483648%positive,
     (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
  |-> Vint32 i1 **
  PV (2147483648%positive,
     ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
  |-> Vint32 i0 **
  PV (2147483648%positive,
     (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
         $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
     $ 416) @ char_t |-> Vint32 i **
  PV (2147483648%positive,
     ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ
          $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  $ 1) +ᵢ  
      $ 8) +ᵢ  $ 320) @ long |-> (V$ 305419896) **
  AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
  AAllArea (2147483648%positive, Int.zero) v0 a **
  ACPUs (2147483648%positive, Int.zero) l1 m2 **
  AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
  LV confEndian @ char_t |-> (V$ 0) **
  Adomain2index' v'14 **
  AKsDomain v'15 **
  APartID2Dom v'16 **
  APortnumcur **
  APartArea' v'17 **
  AKsDSchdlen v'18 **
  AKsDomSchedule' v'19 ** AOSPortAttrTbl' v'20 ** ACorepartnum' v'21 **
  [|Vint32 Int.zero <> Vint32 Int.zero /\
    Vint32 Int.zero <> Vnull /\ Vint32 Int.zero <> Vundef|]).
  hoare forward.
  hoare unfold.
  tryfalse.
  
  eapply backward_rule1.
  intros.
(*   Search A_isr_is_prop.
  Search ([|_|]). *)
  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV confEndian @ char_t |-> (V$ 0) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 305419896) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV sysEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 ).
(*   eapply a_isr_is_prop_split in Ht.
  sep_lifts_trms_in H0 (uconf).
  sep auto. intros.  *)
  unfold A_isr_is_prop.
  destruct_s s.
  sep normal.
  sep auto.
  Optimize Proof.
  Optimize Heap.
(*if sys=conf*)
  hoare forward.
  hoare unfold.
  
  hoare forward.

  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H14 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 0) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 0) **
   LV y @ char_t |-> (V$ 0) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 305419896
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 305419896 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.

  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).

  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 305419896
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 305419896 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
}
{
    pose proof(semacc_int_eq_true( i6 ) ($ 2018910994) Heq2);
    pose proof(semacc_int_eq_true( i4 ) ($ 2018910994) Heq4); subst.
    hoare forward.
    eapply ift_rule_general.
    intros.
    eexists.
    eapply bop_rv.
    eapply deref_rv.
    eapply lvar_rv.
    sep auto.
    eauto.
    instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 35) ** 
                     PV (2147483648%positive, $2) @ char_t |-> (V$ 86) **
                     PV (2147483648%positive, $3) @ char_t |-> (V$ 120) **
                      <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 0) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
    instantiate(2:= true).
    unfold Aptrmapsto at 1 2 3 4.
    sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
    sep remember(12::nil)%nat in H6.
    destruct_s s.
    unfold Aptrmapsto in H6.
    simpl in H6.
    simpl.
    simpljoin.
    unfold mapstoval in H17.
    simpljoin.
    simpl in H12.
    simpljoin.
    do 6 eexists.
    split.
    eauto.
    split.
    2:split.
    3:split.
    4:split.
    4:split.
    2:eauto.
    2:eauto.
    3:eauto.
    instantiate(2:= x7).
    join auto.
    unfolds.
    eexists.
    split.
    instantiate(2:= V$ 18).
    eauto.
    simpl.
    do 2 eexists.
    split.
    instantiate(2:= x7).
    instantiate(1:= empenv).
    join auto.  
    split.
    2:eauto.
    unfold ptomval in *.
    simpl.
    subst x7.
    simpl.
    assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)) = Byte.repr (Int.unsigned ($ 18))).
    { try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 7886371; auto. }
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)/ 256) = Byte.repr (Int.unsigned ($ 35))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 30806; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256) = Byte.repr (Int.unsigned ($ 86))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 120; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 120))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  subst.
  eauto.
  sep auto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 18) (V$ 18) char_t long oeq) with (Some (Vint32 Int.one)).
  instantiate(1:= Vint32 Int.one).
  eauto.
  eauto.
  simpl.
  eauto.
  intros.
  destruct H6.
  eapply H6.
  hoare forward.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  intros.
  eapply bop_rv.
  eapply deref_rv.
  eapply lvar_rv.
  sep auto.
  eauto.
  instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 35) ** 
                   PV (2147483648%positive, $2) @ char_t |-> (V$ 86) **
                   PV (2147483648%positive, $3) @ char_t |-> (V$ 120) **
                    <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 0) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
    instantiate(2:= true).
    unfold Aptrmapsto at 1 2 3 4.
    sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
    sep remember(12::nil)%nat in H6.
    destruct_s s.
    unfold Aptrmapsto in H6.
    simpl in H6.
    simpl.
    simpljoin.
    unfold mapstoval in H17.
    simpljoin.
    simpl in H12.
    simpljoin.
    do 6 eexists.
    split.
    eauto.
    split.
    2:split.
    3:split.
    4:split.
    4:split.
    2:eauto.
    2:eauto.
    3:eauto.
    instantiate(2:= x7).
    join auto.
    unfolds.
    eexists.
    split.
    instantiate(2:= V$ 18).
    eauto.
    simpl.
    do 2 eexists.
    split.
    instantiate(2:= x7).
    instantiate(1:= empenv).
    join auto.  
    split.
    2:eauto.
    unfold ptomval in *.
    simpl.
    subst x7.
    simpl.
    assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)) = Byte.repr (Int.unsigned ($ 18))).
    { try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 7886371; auto. }
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)/ 256) = Byte.repr (Int.unsigned ($ 35))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 30806; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256) = Byte.repr (Int.unsigned ($ 86))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 120; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 120))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  subst.
  eauto.
  sep auto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 18) (V$ 18) char_t long oeq) with (Some (Vint32 Int.one)).
  instantiate(1:= Vint32 Int.one).
  eauto.
  eauto.
  simpl.
  eauto.
  intros.
  hoare forward.
  hoare forward.
  eapply backward_rule1.
  intros.

  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 0) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 2018910994) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 1) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        [|val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vint32 Int.one /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vnull /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vundef|]).

  unfold A_isr_is_prop.
  destruct_s s.
  sep normal. 
  sep auto.
  Optimize Proof.
  Optimize Heap.
  
(*if sys=conf*)
  hoare forward.
  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H6 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 1) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 0) **
   LV y @ char_t |-> (V$ 0) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.

  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).

  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.

  eapply backward_rule1.
  intros.

  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 0) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 0) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 2018910994) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        [|val_inj
            (if Int.eq ($ 0) ($ 0)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
          val_inj
            (if Int.eq ($ 0) ($ 0)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vnull /\
          val_inj
            (if Int.eq ($ 0) ($ 0)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vundef|]).

  unfold A_isr_is_prop.
  destruct_s s.
  sep normal. 
  sep auto.
  Optimize Proof.
  Optimize Heap.
(*if sys=conf*)
  hoare forward.
  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H6 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 0) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 0) **
   LV y @ char_t |-> (V$ 0) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.
  splits;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).

  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto. split.
  eapply typematch_size;eauto.
  split;eauto.
}
}

   hoare unfold.
    (*If (y ′ ==ₑ ′ 1){sysEndian ′ =ₑ ′ 1};ₛ*)
    (*case y = 1*)
    1:{
    hoare forward. 
    hoare forward.
    hoare forward.
    2:{
    hoare unfold.
    change (Int.eq ($ 1) ($ 1))with (true) in H6.
    simpl in H6.
    destruct H6.
    tryfalse.
    tryfalse.
    }

  (*base ′ =ₑ 〈 (char_t) ∗ 〉 (&ₐ conf′→ magicf ′);ₛ*)
    hoare forward.
    hoare unfold.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split.
    introv Hsat.
    sep remember (34::nil)%nat in Hsat.
    sep auto.
    intros.
    sep auto.
    intros.
    eapply cast_rv_tptr.
    eapply struct_offset_rv.
    eapply addrof_deref_rv.
    symbolic execution; pauto.
    sep auto.
    instantiate(2:=UCOS_CONF).
    instantiate(1:=⌞ magicf @ long; fileVersion @ long ; coreNums @ char_t; noPartitions @ char_t;
     noCommChannels @ char_t; noPorts @ char_t; IntrDomainMux @ Tarray char_t ∘ 11; allArea @
     area_conf_t; cpus @ Tarray cpu_conf_t ∘ CORENUM; channelTbl @
     Tarray channel_conf_t ∘ CHANNEL_NUMS; portRdyGrp @ char_t; portRdyTbl @ 
     Tarray char_t ∘ 8; portTbl @ Tarray port_conf_t ∘ PORT_NUMS; magicl @ long ⌟).
    eauto.
    instantiate(1:= $ 0).
    eauto.
    instantiate(1:= long).
    eauto.
    eauto.
    eauto.
    eapply assign_type_match_true.
    eauto.
    intros.
    sep auto.
  Optimize Proof.
  Optimize Heap.
    change (fst BOOT_DATA_ADDRESS, snd BOOT_DATA_ADDRESS +ᵢ  $ 0) with (2147483648%positive, Int.zero).
    inverts H12.
    lets Hval: H5.
    simpl in Hval, H5.
    assert (Heq1: Int.eq i6 ($ 305419896) = true \/ Int.eq i6 ($ 305419896) = false).
    { assert (Hran: i6 = ($ 305419896) \/ i6 <> ($ 305419896)) by tauto.
      destruct Hran; subst; auto.
      right; eapply Int.eq_false; auto. 
    }
    assert (Heq2: Int.eq i6 ($ 2018910994) = true \/ Int.eq i6 ($ 2018910994) = false).
    { assert (Hran: i6 = ($ 2018910994) \/ i6 <> ($ 2018910994)) by tauto.
      destruct Hran; subst; auto.
       right; eapply Int.eq_false; auto. 
    }
    assert (Heq3: Int.eq i4 ($ 305419896) = true \/ Int.eq i4 ($ 305419896) = false).
    { assert (Hran: i4 = ($ 305419896) \/ i4 <> ($ 305419896)) by tauto.
      destruct Hran; subst; auto.
       right; eapply Int.eq_false; auto. 
    }
    assert (Heq4: Int.eq i4 ($ 2018910994) = true \/ Int.eq i4 ($ 2018910994) = false).
    { assert (Hran: i4 = ($ 2018910994) \/ i4 <> ($ 2018910994)) by tauto.
      destruct Hran; subst; auto.
       right; eapply Int.eq_false; auto. 
    }
    destruct Heq1 as [Heq1 | Heq1]; destruct Heq2 as [Heq2 | Heq2];
    destruct Heq3 as [Heq3 | Heq3]; destruct Heq4 as [Heq4 | Heq4];
    rewrite Heq1, Heq2, Heq3, Heq4 in *;
    simpl in Hval;
    try eapply semacc_int_eq_true in Heq1, Heq2;
    try eapply semacc_int_eq_true in Heq3, Heq4;
    try rewrite Heq1 in Heq2;
    try rewrite Heq3 in Heq4;
    simpl;
    change (Int.ltu Int.zero Int.one) with true in * ;
    change (Int.ltu Int.zero Int.zero) with false in * ;
    simpl; simpl in Hval;
    change (Int.ltu Int.zero Int.one) with true in * ;
    change (Int.ltu Int.zero Int.zero) with false in *;
    simpl; simpl in Hval; tryfalse; auto.
  (*Int.eq i ($ 305419896) = true /\ Int.eq i0 ($ 305419896) = true*)
    1:{
      change (fst (2147483648%positive, Int.zero), snd (2147483648%positive, Int.zero) +ᵢ  $ 0) with (2147483648%positive, Int.zero) in *.
      pose proof(semacc_int_eq_true( i6 ) ($ 305419896) Heq1);
      pose proof(semacc_int_eq_true( i4 ) ($ 305419896) Heq3); subst.
      hoare forward.
      eapply ift_rule_general.
      intros.
      eexists.
      eapply bop_rv; eauto.
      eapply deref_rv.
      eapply lvar_rv.
      sep auto.
      eauto.
      change (Int.zero +ᵢ  $ 0) with Int.zero.
      instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 86) ** 
                       PV (2147483648%positive, $2) @ char_t |-> (V$ 52) **
                       PV (2147483648%positive, $3) @ char_t |-> (V$ 18) **
                        <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
      instantiate(2:= true).
      unfold Aptrmapsto at 1 2 3 4.
      sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
      sep remember(13::nil)%nat in H6.
      destruct_s s.
      unfold Aptrmapsto in H6.
      simpl in H6.
      simpl.
      simpljoin.
      unfold mapstoval in H17.
      simpljoin.
      simpl in H12.
      simpljoin.
      do 6 eexists.
      split.
      eauto.
      split.
      2:split.
      3:split.
      4:split.
      4:split.
      2:eauto.
      2:eauto.
      3:eauto.
      instantiate(2:= x7).
      join auto.
      unfolds.
      eexists.
      split.
      instantiate(2:= V$ 120).
      eauto.
      simpl.
      do 2 eexists.
      split.
      instantiate(2:= x7).
      instantiate(1:= empenv).
      join auto.  
      split.
      2:eauto.
      unfold ptomval in *.
      simpl.
      simpl.
      assert (Hby: Byte.repr (Int.unsigned ($ 305419896)) = Byte.repr (Int.unsigned ($ 120))).
      {
        try repeat rewrite Int.unsigned_repr.
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        eapply Byte.eqm_samerepr.
        unfold Byte.eqm, Byte.eqmod, Byte.modulus.
        unfold Byte.wordsize, Wordsize_8.wordsize.
        unfold two_power_nat, shift_nat, nat_rect.
        exists 1193046; auto. }
  rewrite H12.
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  eauto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256) = Byte.repr (Int.unsigned ($ 86))).
    {
      try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 4660; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists; split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256) = Byte.repr (Int.unsigned ($ 52))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 18; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 18))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  eauto.
  sep auto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 120) (V$ 18) char_t long oeq) with (Some (Vint32 Int.zero)).
  eauto.
  simpl; eauto.
  intros.
  destruct H6.
  eapply H6.
  hoare forward.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  intros.
  eapply bop_rv.
  eapply deref_rv.
  eapply lvar_rv.
  sep auto.
  eauto.
  instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 86) ** 
                   PV (2147483648%positive, $2) @ char_t |-> (V$ 52) **
                   PV (2147483648%positive, $3) @ char_t |-> (V$ 18) **
                    <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
  instantiate(2:= true).
  unfold Aptrmapsto at 1 2 3 4.
  sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
  sep remember(13::nil)%nat in H6.
  destruct_s s.
  unfold Aptrmapsto in H6.
  simpl in H6.
  simpl.
  simpljoin.
  unfold mapstoval in H17.
  simpljoin.
  simpl in H12.
  simpljoin.
  do 6 eexists.
  split.
  eauto.
  split.
  2:split.
  3:split.
  4:split.
  4:split.
  2:eauto.
  2:eauto.
  3:eauto.
      instantiate(2:= x7).
      join auto.
      unfolds.
      eexists.
      split.
      instantiate(2:= V$ 120).
      eauto.
      simpl.
      do 2 eexists.
      split.
      instantiate(2:= x7).
      instantiate(1:= empenv).
      join auto.  
      split.
      2:eauto.
      unfold ptomval in *.
      simpl.
      simpl.
      assert (Hby: Byte.repr (Int.unsigned ($ 305419896)) = Byte.repr (Int.unsigned ($ 120))).
      {
        try repeat rewrite Int.unsigned_repr.
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        2:{ change Int.max_unsigned with (65536*65536-1);
            auto with zarith. }
        eapply Byte.eqm_samerepr.
        unfold Byte.eqm, Byte.eqmod, Byte.modulus.
        unfold Byte.wordsize, Wordsize_8.wordsize.
        unfold two_power_nat, shift_nat, nat_rect.
        exists 1193046; auto. }
  rewrite H12.
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  eauto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256) = Byte.repr (Int.unsigned ($ 86))).
    {
      try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 4660; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists; split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256) = Byte.repr (Int.unsigned ($ 52))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 18; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 305419896) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 18))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  subst.
  sep auto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 120) (V$ 18) char_t long oeq) with (Some (Vint32 Int.zero)).
  instantiate(1:= Vint32 Int.zero).
  eauto.
  eauto.
  simpl.
  eauto.
  hoare unfold.
  tryfalse.
  instantiate(1:=  <|| v'26 ||>  **
  LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
  APortTbl (2147483648%positive, Int.zero) l m **
  LV sysEndian @ char_t |-> (V$ 1) **
  Aisr v'11 **
  Aie v'22 **
  Ais v'23 **
  Acs v'24 **
  Aier v'25 **
  p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
  LV y @ char_t |-> (V$ 1) **
  A_dom_lenv
    ((sysEndian, char_t)
     :: (confEndian, char_t)
        :: (y, char_t)
           :: (base, (char_t) ∗)
              :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
  LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
  LV flag @ long |-> (V$ 0) **
PV (2147483648%positive, Int.zero) @ long |-> (V$ 305419896) **
  PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
  PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t |-> Vint32 i3 **
  PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
  |-> Vint32 i2 **
  PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
  char_t |-> Vint32 i1 **
  PV (2147483648%positive,
     ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
  |-> Vint32 i0 **
  PV (2147483648%positive,
     (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
        $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) @ char_t |-> 
  Vint32 i **
  PV (2147483648%positive,
     ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ
          $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  $ 1) +ᵢ  
      $ 8) +ᵢ  $ 320) @ long |-> (V$ 305419896) **
  AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
  AAllArea (2147483648%positive, Int.zero) v0 a **
  ACPUs (2147483648%positive, Int.zero) l1 m2 **
  AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
  LV confEndian @ char_t |-> (V$ 0) **
  Adomain2index' v'14 **
  AKsDomain v'15 **
  APartID2Dom v'16 **
  APortnumcur **
  APartArea' v'17 **
  AKsDSchdlen v'18 **
  AKsDomSchedule' v'19 ** AOSPortAttrTbl' v'20 ** ACorepartnum' v'21 **
  [|Vint32 Int.zero <> Vint32 Int.zero /\
    Vint32 Int.zero <> Vnull /\ Vint32 Int.zero <> Vundef|]).
  hoare forward.
  hoare unfold.
  tryfalse.

  eapply backward_rule1.
  intros.

  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 305419896) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 305419896) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        [|val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vint32 Int.one /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vnull /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vundef|]).

  unfold A_isr_is_prop.
  destruct_s s.
  sep normal.
  sep auto.
  Optimize Proof.
  Optimize Heap.
(*if sys=conf*)
  hoare forward.
  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H6 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 0) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 1) **
   LV y @ char_t |-> (V$ 1) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 305419896
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 305419896 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.

  split;eauto.
  simpl.
  splits;eauto.

  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).

  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 305419896
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2 :: x3 :: V$ 305419896 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
}
  
{
    pose proof(semacc_int_eq_true( i6 ) ($ 2018910994) Heq2);
    pose proof(semacc_int_eq_true( i4 ) ($ 2018910994) Heq4); subst.
    hoare forward.
    eapply ift_rule_general.
    intros.
    eexists.
    eapply bop_rv.
    eapply deref_rv.
    eapply lvar_rv.
    sep auto.
    eauto.
    instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 35) ** 
                     PV (2147483648%positive, $2) @ char_t |-> (V$ 86) **
                     PV (2147483648%positive, $3) @ char_t |-> (V$ 120) **
                      <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @ char_t
        |-> Vint32 i2 **
        PV (2147483648%positive, (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ
               $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  
           $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
    instantiate(2:= true).
    unfold Aptrmapsto at 1 2 3 4.
    sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
    sep remember(13::nil)%nat in H6.
    destruct_s s.
    unfold Aptrmapsto in H6.
    simpl in H6.
    simpl.
    simpljoin.
    unfold mapstoval in H17.
    simpljoin.
    simpl in H12.
    simpljoin.
    do 6 eexists.
    split.
    eauto.
    split.
    2:split.
    3:split.
    4:split.
    4:split.
    2:eauto.
    2:eauto.
    3:eauto.
    instantiate(2:= x7).
    join auto.
    unfolds.
    eexists.
    split.
    instantiate(2:= V$ 18).
    eauto.
    simpl.
    do 2 eexists.
    split.
    instantiate(2:= x7).
    instantiate(1:= empenv).
    join auto.  
    split.
    2:eauto.
    unfold ptomval in *.
    simpl.
    subst x7.
    simpl.
    assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)) = Byte.repr (Int.unsigned ($ 18))).
    { try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 7886371; auto. }
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)/ 256) = Byte.repr (Int.unsigned ($ 35))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 30806; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256) = Byte.repr (Int.unsigned ($ 86))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 120; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 120))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  subst.
  eauto.
  sep auto.
  eauto.
  symbolic execution.

  change (bop_eval (V$ 18) (V$ 18) char_t long oeq) with (Some (Vint32 Int.one)).
  instantiate(1:= Vint32 Int.one).
  eauto.
  eauto.
  simpl.
  eauto.
  intros.
  destruct H6.
  eapply H6.
  hoare forward.
  eapply backward_rule1.
  eapply sep_aconj_r_aistrue_to_astar.
  intros.
  eapply bop_rv.
  eapply deref_rv.
  eapply lvar_rv.
  sep auto.
  eauto.
  instantiate(1:=  PV(2147483648%positive, $1) @ char_t |->  (V$ 35) ** 
                   PV (2147483648%positive, $2) @ char_t |-> (V$ 86) **
                   PV (2147483648%positive, $3) @ char_t |-> (V$ 120) **
                    <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aisr v'11 **
        Aie v'22 **
        Ais v'23 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
        char_t |-> Vint32 i2 **
        PV (2147483648%positive,
           (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
               +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  
            $ 7088) +ᵢ  $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 ** ACorepartnum' v'21).
  instantiate(2:= true).
  unfold Aptrmapsto at 1 2 3 4.
  sep remember (1 :: 2 :: 3 :: 4 ::nil)%nat .
  sep remember(13::nil)%nat in H6.
  destruct_s s.
  unfold Aptrmapsto in H6.
  simpl in H6.
  simpl.
  simpljoin.
  unfold mapstoval in H17.
  simpljoin.
  simpl in H12.
  simpljoin.
  do 6 eexists.
  split.
  eauto.
  split.
  2:split.
  3:split.
  4:split.
  4:split.
  2:eauto.
  2:eauto.
  3:eauto.
    instantiate(2:= x7).
    join auto.
    unfolds.
    eexists.
    split.
    instantiate(2:= V$ 18).
    eauto.
    simpl.
    do 2 eexists.
    split.
    instantiate(2:= x7).
    instantiate(1:= empenv).
    join auto.  
    split.
    2:eauto.
    unfold ptomval in *.
    simpl.
    subst x7.
    simpl.
    assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)) = Byte.repr (Int.unsigned ($ 18))).
    { try repeat rewrite Int.unsigned_repr.
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      2:{ change Int.max_unsigned with (65536*65536-1);
          auto with zarith. }
      eapply Byte.eqm_samerepr.
      unfold Byte.eqm, Byte.eqmod, Byte.modulus.
      unfold Byte.wordsize, Wordsize_8.wordsize.
      unfold two_power_nat, shift_nat, nat_rect.
      exists 7886371; auto. }
  rewrite Hby.
  eauto.
  do 6 eexists.
  split.
  2:split.
  eauto.
  instantiate(2:= x11).
  instantiate(1:=(merge_list (x13 :: x15  :: x4 :: nil))).
  join auto.
  split.
  eauto.
  split.
  instantiate(2:=empenv).
  instantiate(1:= x9).
  join auto.  
  split.
  2: do 6 eexists.
  2:split.
  2:eauto.
  2:split.
  3:split.
  3:eauto.
  3:split.
  3:instantiate(2:= empenv).
  3:instantiate(1:= x9).
  3:join auto.
  3:split.
  4:do 6 eexists.
  4:split.
  split.
  2:join auto.
  3:split.
  2:instantiate(2:= x13).
  2:instantiate(1:=merge_list ( x15 :: x4 :: nil)).
  2:join auto.
  3:join auto.
  3:eauto.
  3:split.
  4:split.
  5:split.
  6:split.
  4:eauto.
  3:instantiate(2:= x15).
  3:instantiate(1:=x4).
  3:join auto.
  3:instantiate(2:= empenv).
  3:instantiate(1:=x9).
  3:join auto.
  3:split.
  4:join auto.
  unfolds.
  eexists.
  split.
  auto.
  Optimize Proof.
  Optimize Heap.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x11).
  instantiate(1:=empenv).
  join auto.
  split.
  auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x11.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994)/ 256) = Byte.repr (Int.unsigned ($ 35))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 30806; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  2:split.
  instantiate(2:= x13).
  instantiate(1:=empenv).
  join auto.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x13.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256) = Byte.repr (Int.unsigned ($ 86))).
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 120; auto. }
  rewrite Hby.
  eauto.
  unfolds.
  eexists.
  split.
  auto.
  simpl.
  do 2 eexists.
  split.
  instantiate(2:= x15).
  instantiate(1:= empenv).
  join auto.
  split.
  2:eauto.
  unfold ptomval in *.
  simpl.
  subst x15.
  simpl.
  assert (Hby: Byte.repr (Int.unsigned ($ 2018910994) / 256 / 256 / 256) = Byte.repr (Int.unsigned ($ 120))).  
  { try repeat rewrite Int.unsigned_repr.
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    2:{ change Int.max_unsigned with (65536*65536-1);
        auto with zarith. }
    eapply Byte.eqm_samerepr.
    unfold Byte.eqm, Byte.eqmod, Byte.modulus.
    unfold Byte.wordsize, Wordsize_8.wordsize.
    unfold two_power_nat, shift_nat, nat_rect.
    exists 0; auto. }
  rewrite Hby.
  eauto.
  subst.
  eauto.
  sep auto.
  eauto.
  symbolic execution.
  change (bop_eval (V$ 18) (V$ 18) char_t long oeq) with (Some (Vint32 Int.one)).
  instantiate(1:= Vint32 Int.one).
  eauto.
  eauto.
  simpl.
  eauto.
  intros.
  hoare forward.
  hoare forward.
  eapply backward_rule1.
  intros.

  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 2018910994) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
        char_t |-> Vint32 i2 **
        PV (2147483648%positive,
           (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
               +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  
            $ 7088) +ᵢ  $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 1) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        [|val_inj
            (if Int.eq ($ 1) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vint32 Int.zero /\
          val_inj
            (if Int.eq ($ 1) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vnull /\
          val_inj
            (if Int.eq ($ 1) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vundef|]).

  unfold A_isr_is_prop.
  destruct_s s.
  sep normal.
  sep auto.
  Optimize Proof.
  Optimize Heap.
(*if sys=conf*)
  hoare forward.
  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H6 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 1) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 1) **
   LV y @ char_t |-> (V$ 1) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2
                                         :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).

  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2
                                         :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply backward_rule1.
  intros.
  lets Ht:astar_l_apure_intro.
  specializes Ht.
  eapply H6.
  eapply H3.
  sep remember(2::3::4::5::6::7::8::9::10::11::12::13::14::15::16::17::18::19::20::21::22::23::24::25::26::27::28::29::30::31::32::33::34::35::36::37::nil)%nat in Ht.
  subst H12.
  sep_lifts_trms_in Ht (Aisr,Ais).
  instantiate(1:= Aisr v'11 **
        Ais v'23 **
        A_isr_is_prop**
         <|| v'26 ||>  **
        LV base @ (char_t) ∗
        |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
        APortTbl (2147483648%positive, Int.zero) l m **
        LV sysEndian @ char_t |-> (V$ 1) **
        Aie v'22 **
        Acs v'24 **
        Aier v'25 **
        p_local OSLInv ct (logic_val (V$ 1) :: v'27) **
        LV y @ char_t |-> (V$ 1) **
        A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil) **
        LV uconf @ ucos_conf_t ∗
        |-> Vptr (2147483648%positive, Int.zero) **
        LV flag @ long |-> (V$ 0) **
        PV (2147483648%positive, Int.zero) @ long |-> (V$ 2018910994) **
        PV (2147483648%positive, Int.zero +ᵢ  $ 4) @ long |-> Vint32 i5 **
        PV (2147483648%positive, (Int.zero +ᵢ  $ 4) +ᵢ  $ 4) @ char_t
        |-> Vint32 i3 **
        PV (2147483648%positive, ((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) @
        char_t |-> Vint32 i2 **
        PV (2147483648%positive,
           (((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) @ char_t
        |-> Vint32 i1 **
        PV (2147483648%positive,
           ((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) @
        char_t |-> Vint32 i0 **
        PV (2147483648%positive,
           (((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1)
               +ᵢ  $ 1) +ᵢ  $ 11) +ᵢ  $ 16) +ᵢ  
            $ 7088) +ᵢ  $ 416) @ char_t |-> Vint32 i **
        PV (2147483648%positive,
           ((((((((((((Int.zero +ᵢ  $ 4) +ᵢ  $ 4) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 1) +ᵢ  $ 11)
                +ᵢ  $ 16) +ᵢ  $ 7088) +ᵢ  $ 416) +ᵢ  
             $ 1) +ᵢ  $ 8) +ᵢ  $ 320) @ long |-> 
        (V$ 2018910994) **
        AIntrDomainMux (2147483648%positive, Int.zero) v2 m3 **
        AAllArea (2147483648%positive, Int.zero) v0 a **
        ACPUs (2147483648%positive, Int.zero) l1 m2 **
        AChannelTbl (2147483648%positive, Int.zero) l0 m1 **
        LV confEndian @ char_t |-> (V$ 0) **
        Adomain2index' v'14 **
        AKsDomain v'15 **
        APartID2Dom v'16 **
        APortnumcur **
        APartArea' v'17 **
        AKsDSchdlen v'18 **
        AKsDomSchedule' v'19 **
        AOSPortAttrTbl' v'20 **
        ACorepartnum' v'21 **
        [|val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vint32 Int.one /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vnull /\
          val_inj
            (if Int.eq ($ 0) ($ 1)
             then Some (Vint32 Int.one)
             else Some (Vint32 Int.zero)) <> Vundef|]).

  unfold A_isr_is_prop.
  destruct_s s.
  sep normal. 
  sep auto.
  Optimize Proof.
  Optimize Heap.
(*if sys=conf*)
  hoare forward.
  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(4:=v'27).
  sep_lifts_trms_in H6 (p_local,Adomain2index',AKsDomain,APartID2Dom,APartArea,AKsDSchdlen,AKsDomSchedule',AOSPortAttrTbl',ACorepartnum'). 
  instantiate(1:= LV confEndian @ char_t |-> (V$ 0) **
   LV base @ (char_t) ∗ |-> Vptr (2147483648%positive, Int.zero +ᵢ  $ 0) **
   LV sysEndian @ char_t |-> (V$ 1) **
   LV y @ char_t |-> (V$ 1) **
   LV uconf @ ucos_conf_t ∗ |-> Vptr (2147483648%positive, Int.zero) **
   LV flag @ long |-> (V$ 0)**A_dom_lenv
          ((sysEndian, char_t)
           :: (confEndian, char_t)
              :: (y, char_t)
                 :: (base, (char_t) ∗)
                    :: (flag, long) :: (uconf, ucos_conf_t ∗) :: nil)).

  sep auto.
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2
                                         :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).
  unfold AucosConf.
  unfold BOOT_DATA_ADDRESS.
  sep pauto.
  sep auto.
  unfold node.
  sep pauto.
  unfold Astruct.
  unfold Astruct'.
  unfold ucos_conf_t.
  unfold area_conf_t.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  instantiate(1:= $DNUM ).
  assert(0 <= Int.unsigned ($ DNUM) <8).
  eapply intunsign_z.
  split;eauto. eauto.
  simpl. eauto.
  pure_auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x11)).
  sep auto.
  introv Hsat.
  sep pauto.
  instantiate(1:= (logic_val (V$ 1) :: x10)).
  sep auto.

  hoare forward.
  unfold initDnumPost.
  unfold initDnumPost'.
  unfold getasrt.
  hoare forward.
  instantiate(2:=v'56).
  instantiate(2:=v'41).
  instantiate(2:=v'40).
  instantiate(2:=v'54).
  instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)).
  instantiate(2:=v'37).
  instantiate(2:=v'36).
  instantiate(2:=v'32).
  instantiate(1:=v'13).
  unfold AucosConf in H6.
  unfold BOOT_DATA_ADDRESS in H6.
  unfold node in H6.
  unfold ucos_conf_t in H6.
  unfold  Astruct in H6.
  unfold Astruct' in H6.
  instantiate(1:= v'30).
  instantiate(1:= v'29).
  sep auto.

  hoare forward.
  instantiate(2:=v'21).
  instantiate(2:=v'20).
  instantiate(2:=v'19).
  instantiate(2:=v'18).
(*   instantiate(2:=(nth_val' 0 v'44 :: nth_val' 1 v'44 :: nth_val' 2 v'44 :: nil)). *)
  instantiate(2:=v'17).
  instantiate(2:=v'16).
  instantiate(2:=v'15).
  instantiate(2:=v'14).
  instantiate(1:=v'27).
  instantiate(2:=((V$ 2018910994
        :: Vint32 i5
           :: Vint32 i3
              :: Vint32 i2
                 :: Vint32 i1
                    :: Vint32 i0
                       :: x6
                          :: x5
                             :: x
                                :: x0
                                   :: Vint32 i
                                      :: x2
                                         :: x3 :: V$ 2018910994 :: nil),v2,v0,l1,l0,v,l)).
  instantiate(1:=(u5,u6,u4,u3,u2,u1,m3,a,m2,m1,u0,m0,m,u)).

  sep pauto.
  sep auto.
  split;eauto.
  simpl.
  splits;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
  eapply typematch_size;eauto.
Unshelve.
eapply Aemp.
}
}
Qed.
