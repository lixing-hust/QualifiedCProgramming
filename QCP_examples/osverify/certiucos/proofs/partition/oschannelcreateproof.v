Require Import ucos_include.
Require Import Lia.


Require Import aux_pureLib.
Require Import abs_op_corecommu_rules.
Require Import OSTimeTickPure.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.


Open Scope code_scope.

Open Scope int_scope.

Lemma sys_channel_info_count_rv : forall s ptr countv vl ls P,
  struct_type_vallist_match os_ucos_h.channel_semaphore_t vl ->
  symbolic_lemmas.var_notin_dom sys_channel_info ls = true ->
  nth_val 0 vl = Some countv ->
  s  |= GV sys_channel_info @ channel_semaphore_t ∗ |-> Vptr ptr **
        Astruct ptr os_ucos_h.channel_semaphore_t vl ** A_dom_lenv ls ** P ->
  s |= Rv sys_channel_info ′ → count @ (Tint8) == countv.
Proof.
  intros.
  struct_type_vallist_match_elim.
  eapply symbolic_lemmas.struct_member_rv_g''';eauto.
  sep autocancel. apply H2. 
  auto.
  auto.
  auto.
  pauto.
Qed.

Lemma sys_channel_info_freeTbl_rv : forall s ptr countv vl ls P,
  struct_type_vallist_match os_ucos_h.channel_semaphore_t vl ->
  symbolic_lemmas.var_notin_dom sys_channel_info ls = true ->
  nth_val 1 vl = Some countv ->
  s  |= GV sys_channel_info @ channel_semaphore_t ∗ |-> Vptr ptr **
        Astruct ptr os_ucos_h.channel_semaphore_t vl ** A_dom_lenv ls ** P ->
  s |= Rv sys_channel_info ′ → freeTbl @ (Tint8) == countv.
Proof.
  intros.
  struct_type_vallist_match_elim.
  eapply symbolic_lemmas.struct_member_rv_g''';eauto.
  sep autocancel. apply H2. 
  auto.
  auto.
  auto.
  pauto.
Qed.

Lemma channelf_sll_head_isptr_frm : forall l p s P,
  s |= channelf_sll p l OS_Channel OS_Channel_V_OSEventPtr ** P ->
  isptr p.
Proof.
  induction l.
  - intros. cbn in H. simpljoin.
    unfold isptr. tauto. 
  - intros.
    unfold channelf_sll in H; cbn [channelf_sllseg] in H;unfold node in H.
    sep normal in H.
    sep destruct H.
    sep split in H.
    simpljoin1.
    unfold isptr.
    right.
    eexists. eauto.
Qed.

Lemma update_nth_vallist_middle : forall l1 x l2 y,
  update_nth_vallist (length l1) (l1++x::l2) y = l1++y::l2.
Proof.
  induction l1.
  - intros. simpl. auto.
  - intros.
    simpl.
    rewrite IHl1.
    auto.
Qed.

Lemma update_nth_middle: forall {A:Type} (l1: list A) x l2 y,
  ifun_spec.update_nth A (length l1) (l1++x::l2) y = l1++y::l2.
Proof.
  induction l1.
  - intros. simpl. auto.
  - intros.
    simpl.
    rewrite IHl1.
    auto.
Qed.

Lemma nthval'_has_value_ptr : 
  forall l len n t, array_type_vallist_match (Tptr t) l ->
                  length l = len -> 
                  (n < len)%nat ->
                  exists x, nth_val' n l = x /\ true = rule_type_val_match (Tptr t) x.
Proof.
  intro.
  induction l.
  intros.
  simpl in H0.
  rewrite <- H0 in H1.
  inversion H1.

  intros.
  induction n.
  inversion H.
  simpl in H2.
  destruct a; try inversion H2.
  exists Vnull.
  split ; auto.
  exists (Vptr a).
  split; auto.

  simpl nth_val'.
  apply (IHl (pred len)).
  inversion H;  auto.
  simpl in H0.
  lia.
  lia.
Qed.

Lemma struct_type_vallist_match_channel: forall chanvl,
  struct_type_vallist_match os_ucos_h.OS_Channel chanvl ->
  exists i i0 i1 i2 x1 x2 x3 x4, chanvl = Vint32 i2 :: Vint32 i1 :: Vint32 i0 :: Vint32 i :: x1 :: x2 :: x3 :: x4 :: nil/\
  Int.unsigned i <= 255 /\
  Int.unsigned i1 <= 255 /\
  Int.unsigned i2 <= 255 /\
  Int.unsigned i0 <= 255 /\
  isptr x1 /\
  isptr x2 /\
  isptr x3 /\
  isptr x4.
Proof.
  intros.
  struct_type_vallist_match_elim.
  jauto.
Qed.


Lemma OSChannelCreate_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSChannelCreate vl logicl OSChannelCreatePre ct->
      Some r =
      BuildRetI os_internal OSChannelCreate vl logicl OSChannelCreatePost ct->
      exists t d1 d2 s,
        os_internal OSChannelCreate = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  inverts H.
  subst logicl.
  clear H1.
  rename v'7 into s.
  rename v'5 into errptr.
  rename v'6 into errv.
  rename v'10 into syschinfoptr.
  rename v'11 into syschinfovl.
  rename v'8 into chanfptr.
  rename v'9 into chanfl.
  rename v'13 into chanvl.
  rename v'14 into chanl.
  rename v'15 into chandstkportll.
  rename v'2 into flag_v.
  rename v'1 into semaphore_v.
  rename v'0 into resource_get_res_v.
  rename v' into channel_v.
  rename v'3 into channelID_v.
  rename v'4 into chtype_v.
  rename v'17 into chcount.
  rename v'12 into ier.
  rename v'16 into nest.
  rename H0 into Hsyschinfovl_V_count.
  rename H4 into Hchcount_le_CHANNEL_NUMS.
  rename H3 into HchannellID_v_range.
  destruct H5 as (Hchanvl_type_match & Hlen_chanvl_CHANNLE_NUMS).
  unfold OSChannelCreate_aspec.
  simpl spec_code_cons.

  (* channel ′ =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
  resource_get_res ′ =ₑ ′ 0;ₛ
  semaphore ′ =ₑ ′ DEFAULT_CHANNLE_SEMAPHROE;ₛ *)
  hoare forward.
  hoare forward.
  hoare forward.
  hoare name lift Aop errptr pre. 
  (* If (channelID ′ ≥ ′ CHANNEL_NUMS){∗ err ′ =ₑ ′ OS_CHANNEL_ID_INVALID;ₛ
    RETURN channel ′};ₛ *)
  destruct (Int.ltu  channelID_v ($ CHANNEL_NUMS)) eqn:EchnID_v.
  2:{
    (* channelID_v >= CHANNEL_NUMS *)
    hoare forward.
    rewrite byte_max_unsigned_val; pauto.
    destruct (Int.ltu ($ CHANNEL_NUMS) channelID_v); auto.
    rewrite byte_max_unsigned_val; pauto.
    destruct (Int.eq channelID_v ($ CHANNEL_NUMS)); auto.
    destruct (Int.ltu ($ CHANNEL_NUMS) channelID_v); destruct (Int.eq channelID_v ($ CHANNEL_NUMS)); auto.
    - instantiate (1:=Afalse). naive pure intro.
      eapply seq_rule.
      { 
        eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto.
      }
      partition_absrulestac absinfer_choice1.
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      sep split; auto.
      left. sep autocancel.
      sep split; auto.
      reflexivity.
    - apply disj_rule.
      naive pure intro. apply pfalse_rule.
      naive pure intro.
      destruct H.
      destruct (Int.eq_dec channelID_v ($ CHANNEL_NUMS)).
      subst. rewrite Int_ltu_refl in H.
      rewrite Int.eq_true in H.
      simpl in H.
      assert (Int.ltu Int.zero Int.one = true) by reflexivity.
      rewrite H0 in H.
      rewrite orb_true_r in H. discriminate.
      rewrite Int.eq_false in H; auto.
      rewrite gjb_common.int_ltu_prop in H; auto.
      simpl in H.
      assert (Int.ltu Int.zero Int.one = true) by reflexivity.
      rewrite H0 in H. simpl in H. clear - H.
      discriminate. 
      destruct (Int.ltu ($ CHANNEL_NUMS) channelID_v); destruct (Int.eq channelID_v ($ CHANNEL_NUMS)); discriminate.
  }
  eapply seq_rule.
  {
    apply corecommu_rules.ift_zero_rule.
    intros.
    symbolic_execution.
    rewrite byte_max_unsigned_val; pauto.
    destruct (Int.ltu ($ CHANNEL_NUMS) channelID_v); auto.
    rewrite byte_max_unsigned_val; pauto.
    destruct (Int.eq channelID_v ($ CHANNEL_NUMS)); auto.
    rewrite Int.eq_sym.
    rewrite ltu_eq_false; auto.
    assert (Int.ltu ($ CHANNEL_NUMS) channelID_v = false).
    apply Intlt_false_is_Zge.
    apply Intlt_true_is_Zlt in EchnID_v. lia.
    now rewrite H0.
  }

  (* If (OSIntNesting ′ >ₑ ′ 0){∗ err ′ =ₑ ′ OS_ERR_CREATE_ISR;ₛ
  RETURN 〈 OS_Channel ∗ 〉 NULL};ₛ *)
  destruct (Int.ltu Int.zero nest) eqn:Enest.
  {
    hoare forward.
    destruct (Int.ltu ($ 0) nest); auto.
    eapply seq_rule.
    { 
      naive pure intro.
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    partition_absrulestac absinfer_choice1.
    partition_absrulestac absinfer_seq_end.
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros. sep normal. sep eexists.
    sep autocancel.
    sep split; auto.
    left. sep auto.
    reflexivity.
    apply disj_rule.
    naive pure intro. apply pfalse_rule.
    naive pure intro.
    setoid_rewrite Enest in H.
    simpl in H.
    destruct H; discriminate.
  }

  eapply seq_rule.
  {
    apply corecommu_rules.ift_zero_rule.
    intros.
    symbolic_execution.
    now setoid_rewrite Enest.
  }


  (* flag ′ =ᶠ channleCreateCheck (·channelID ′, ch_type ′·);ₛ*)
  eapply seq_rule.
  hoare_calle_lvar_logicl (logic_code ( END None;; s
  ?? cslsemacc (Z.to_nat (Int.unsigned ($ OS_RESOURCE_SEMAPHORE_CHANNEL))) (Vint32 Int.zero);;
     END None;; s
     ?? cslsemacc (Z.to_nat (Int.unsigned ($ OS_RESOURCE_SEMAPHORE_CHANNEL))) (Vint32 Int.one);;
        cslsemrel (Z.to_nat (Int.unsigned ($ OS_RESOURCE_SEMAPHORE_CHANNEL)));; END None;; s)::
  logic_ier ier::nil).
  rewrite byte_max_unsigned_val. pauto.
  rewrite H0. reflexivity.
  go.
  unfold retpost.
  intros. unfold getasrt, channleCreateCheckPost, channleCreateCheckPost' in H.
  sep destruct H.
  sep split in H.
  destruct H1; subst; auto.
  rewrite byte_max_unsigned_val; pauto.
  intros. sep destruct H. sep auto.
  intros. sep destruct H. sep auto.
  unfold getasrt, channleCreateCheckPost, channleCreateCheckPost'.
  naive pure intro.
  invertsr H.
  invertsr H1.

  (* If (flag ′ ==ₑ ′ 0){∗ err ′ =ₑ 〈 char_t 〉 ′ CHECK_ERROR;ₛ
      RETURN 〈 OS_Port ∗ 〉 NULL};ₛ *)
  hoare name lift Aop errptr pre.
  destruct H0.
  2:{
    inverts H.
    partition_absrulestac absinfer_choice1.
    partition_absrulestac absinfer_seq_end.
    eapply seq_rule.
    { 
      eapply corecommu_rules.ift_nonzero_rule.
      intros.
      exists (Int.one).
      sep split.
      symbolic_execution.
      reflexivity.
      instantiate (1:=Afalse).
      eapply seq_rule.
      {
        eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto.
      }
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      unfold AOSUnMapTbl.
      unfold AOSMapTbl.
      sep autocancel.
      sep split; auto.
      left. sep auto.
      do 5 right. left. easy.
      reflexivity.
    }
    apply pfalse_rule.
  }
  inverts H.
  eapply seq_rule.
  {
    apply corecommu_rules.ift_zero_rule.
    intros.
    symbolic_execution.
  }

  partition_absrulestac absinfer_choice2.
  hoare name lift Aop resource_get_res pre.
  eapply seq_rule.
  {
    (*CSLSEMACC (′ OS_RESOURCE_SEMAPHORE_CHANNEL, resource_get_res ′)*)
    eapply cslsemacc_rule'.
    go.
    unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
    rewrite max_unsigned_val.
    rewrite Int.unsigned_repr. lia.
    rewrite max_unsigned_val. lia.
    intros.
    rewrite Int.unsigned_repr.
    rewrite Z2Nat.id.
    unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
    symbolic_execution.
    unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
    unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
    intros. unfold p_local in H. unfold CurLINV. sep auto.
    intros. unfold p_local in H. unfold CurLINV. sep auto.
  }
  apply disj_rule.
  {
    eapply seq_rule.
    {
      eapply corecommu_rules.ift_nonzero_rule.
      intros.
      exists (Int.one).
      sep split.
      symbolic_execution.
      reflexivity.
      hoare name lift Aop errptr pre.
      eapply seq_rule.
      {
        eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto.
      }
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      unfold AOSUnMapTbl.
      unfold AOSMapTbl.
      sep autocancel.
      sep split; auto.
      left. sep auto.
      reflexivity.
    }
    apply pfalse_rule.
  }
  (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {∗ err ′ =ₑ ′ OS_CHANNEL_FAIL_TO_GET;ₛ *)
  eapply seq_rule.
  {
    apply corecommu_rules.ift_zero_rule.
    intros.
    symbolic_execution.
  }

  
  (* If (ch_type ′ ==ₑ ′ OUTCORE &&ₑ efield sys_channel_info ′ count ≥ ′ OS_INTER_CORE_CHANNEL_NUMS)
  {∗ err ′ =ₑ ′ OS_CHANNEL_ERR_SEMAPHORE_NULL;ₛ
  CSLSEMREL (〈 char_t 〉 ′ OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ
  RETURN channel ′};ₛ *)
  unfold node at 3.
  naive pure intro.
  rename v' into syschinfoptrb.
  simpljoin. inverts H.
  rename H0 into Hsyschinfovl_type_match.
  eapply seq_rule.
  {
    eapply ift_rule'.
    intros. 
    symbolic_execution.
    destruct (Int.eq chtype_v ($ OUTCORE)); auto.
    clear - Hsyschinfovl_type_match.
    struct_type_vallist_match_elim. simpl. lia.
    auto.
    struct_type_vallist_match_elim.  
    destruct (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) i0); auto.
    struct_type_vallist_match_elim. simpl. lia.
    auto.
    struct_type_vallist_match_elim.
    simpl.  
    destruct (Int.eq i0 ($ OS_INTER_CORE_CHANNEL_NUMS)); auto.
    struct_type_vallist_match_elim.
    destruct (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) i0); auto.
    simpl. 
    destruct (Int.eq i0 ($ OS_INTER_CORE_CHANNEL_NUMS)); auto.
    simpl. destruct (Int.eq i0 ($ OS_INTER_CORE_CHANNEL_NUMS)); auto.
    struct_type_vallist_match_elim.
    destruct (Int.eq chtype_v ($ OUTCORE)); destruct (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) i0); simpl;
    destruct (Int.eq i0 ($ OS_INTER_CORE_CHANNEL_NUMS)); auto.
    naive pure intro.
    clear H.
    hoare name lift Aop errptr pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    eapply seq_rule.
    {
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H. unfold CurLINV. sep auto.
    }
    partition_absrulestac absinfer_seq_end.
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros. sep normal. sep eexists.
    sep autocancel.
    unfold AOSUnMapTbl.
    unfold AOSMapTbl.
    sep autocancel.
    sep split; auto.
    left.
    sep autocancel.
    unfold node.
    sep normal.
    sep eexists.
    sep autocancel.
    sep split; auto.
    reflexivity.
  }
  naive pure intro.
  apply disj_rule.
  {
    apply pfalse_rule.
  }
  naive pure intro.
  rename H into Hout_cond.
  struct_type_vallist_match_elim.
  inverts Hsyschinfovl_V_count.
  rename i into freetblv.
  rename H into chcount_range.
  rename H0 into freetblv_range.
  simpl in Hout_cond.
  destruct Hout_cond.
  2:{
    destruct (Int.eq chtype_v ($ OUTCORE)); destruct (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) chcount);
    destruct (Int.eq chcount ($ OS_INTER_CORE_CHANNEL_NUMS)); discriminate.
  }
  lets Htmp: nthval'_has_value (length OSUnMapVallist)(Z.to_nat (Int.unsigned freetblv)) OSUnMapVallist_type_vallist_match.
  destruct Htmp; auto.
  simpl. lia.
  destruct H0 as (Hnthval'_OSUnMapVallist_x&Hx_type_match).
  lets Hx_range: math_unmap_range Hnthval'_OSUnMapVallist_x. lia.
  lets Htmp: nthval'_has_value OSMapVallist (length OSMapVallist)(Z.to_nat (Int.unsigned x)).
  destruct Htmp; auto.
  simpl. pauto.
  simpl. lia.
  destruct H0 as (Hnthval'_OSMapVallist_x0&Hx0_type_match).
  destruct (Int.eq chtype_v ($ OUTCORE)) eqn: Echtype_Outcore.
  eapply seq_rule.
  {
    eapply ift_rule' with (q:=Afalse).
    intros.
    symbolic_execution.
    rewrite byte_max_unsigned_val. pauto.
    clear - EchnID_v.
    unfold CHANNEL_NUMS in EchnID_v.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    rewrite Hlen_chanvl_CHANNLE_NUMS.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlen_chanvl_CHANNLE_NUMS.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    lets Htmp: nthval'_has_value_ptr (Z.to_nat (Int.unsigned channelID_v)) Hchanvl_type_match Hlen_chanvl_CHANNLE_NUMS.
    destruct Htmp.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    destruct H1.
    destruct x1; try discriminate.
    now rewrite H1.
    rewrite H1. simpl. destruct a; auto.
    naive pure intro.
    rename H into Hcond1.
    assert (nth_error  chanvl (Z.to_nat (Int.unsigned channelID_v)) = Some Vnull).
    {
      simpljoin.
      destruct (nth_val' (Z.to_nat (Int.unsigned channelID_v))) eqn:E; simpl in H, H0, H1; try congruence.
      2:{
          destruct a. simpl in H. congruence.
      }
      clear H H0 H1.
      apply nth_val_nth_error.
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2. congruence.
      rewrite Hlen_chanvl_CHANNLE_NUMS.
      unfold CHANNEL_NUMS in *. simpl.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      lia. rewrite max_unsigned_val. lia.
    }
    clear H0. rename H into Hcond2.
    unfold AOSChannelFreeList at 3.
    
    (* channel ′ =ₑ OSChannelFreeList ′;ₛ *)
    hoare normal pre.
    hoare_assert_pure (isptr chanfptr).
    {
       eapply channelf_sll_head_isptr_frm with (s:=s0).
       sep autocancel. apply H.
    }
    naive pure intro.
    rename H into Hchanfptr_isptr.
    hoare forward.
    clear - Hchanfptr_isptr.
    pauto.
    unfold isptr in Hchanfptr_isptr.
    destruct Hchanfptr_isptr.
    {
      subst.
      (* err ′ =ₑ ′ OS_CHANNEL_DEPLETED *)
      eapply seq_rule.
      {
        eapply if_zero_rule.
        intros.
        symbolic_execution.
        hoare name lift Aop errptr pre.
        eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto.
      }
      (* CSLSEMREL (〈 char_t 〉 ′ OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ *)
      eapply seq_rule.
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H. unfold CurLINV. sep auto.

      (* RETURN channel ′ *)
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      unfold AOSUnMapTbl.
      unfold AOSMapTbl.
      sep autocancel.
      sep split; auto.
      left.
      sep autocancel.
      unfold node.
      sep normal.
      sep eexists.
      sep autocancel.
      unfold AOSChannelFreeList.
      sep normal.
      sep eexists.
      sep split; auto.
      sep autocancel.
      tauto.
      splits; auto.
      pauto.
      reflexivity.
    }
    destruct H. subst chanfptr.
    rename x1 into chanfptr.
    destruct chanfl.
    {
      unfold channelf_sll.
      cbn [channelf_sllseg].
      naive pure intro.
      discriminate H. 
    }
    rename v into chanfvl.
    unfold channelf_sll.
    cbn [channelf_sllseg].
    naive pure intro.
    rename v' into chanfptr'. 
    rename H into Hchanfvl_V_OSEventPtr.
    rename H0 into Hchanfl_V_channelID.
    rename H1 into Hchanfl_V_srcnum.
    rename H2 into Hchanfl_V_dstnum.
    rename H3 into Hchanfl_V_sem.
    rename H4 into Hchanfl_V_dsthead.
    rename H5 into Hchanfl_V_dsttail.
    clear H6.

    unfold node.
    naive pure intro.
    destruct H as (Htmp&Hchanfl_type_match).
    rename v' into chanfptrb.
    inverts Htmp.
    apply struct_type_vallist_match_channel in Hchanfl_type_match.
    simpljoin.
    inverts Hchanfl_V_dsttail.
    inverts Hchanfl_V_dsthead.
    inverts Hchanfl_V_sem.
    inverts Hchanfl_V_dstnum.
    inverts Hchanfl_V_srcnum.
    inverts Hchanfl_V_channelID.
    inverts Hchanfvl_V_OSEventPtr.
    clear H0 H1 H2 H3 H4 H5.
    rename H6 into Hx6_isptr.
    rename H7 into Hchanfptr'_isptr.
    
    eapply seq_rule.
    {
      apply if_one_rule.
      intros.
      symbolic_execution.
      hoare forward.
      clear - Hx6_isptr Hchanfptr'_isptr.
      pauto.
      clear - Hchanfptr'_isptr.
      pauto.
      
      (* OSChannelIDTbl ′[ channelID ′] =ₑ channel ′;ₛ *)
      hoare forward.
      rewrite byte_max_unsigned_val. pauto.
      unfold CHANNEL_NUMS in *.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      simpl.
      lia. rewrite max_unsigned_val. lia.
      rewrite Hlen_chanvl_CHANNLE_NUMS.
      unfold CHANNEL_NUMS in *.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      simpl. 
      lia. rewrite max_unsigned_val. lia.
      
      (* If( ch_type ′ ==ₑ ′ OUTCORE) *)
      eapply seq_rule.
      {
        apply corecommu_rules.ift_nonzero_rule.
        intros.
        exists Int.one.
        sep split.
        symbolic_execution.
        now rewrite Echtype_Outcore.
        reflexivity.
       
        (* semaphore ′ =ₑ OSUnMapTbl ′[sys_channel_info ′ → freeTbl];ₛ*)
        hoare forward.
        pauto.
        eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match.
        2: apply OSUnMapVallist_type_vallist_match.
        simpl. lia.
        
        (* sys_channel_info ′ → freeTbl &= ∼ OSMapTbl ′ [semaphore ′];ₛ *)
       
        rewrite Hnthval'_OSUnMapVallist_x.
        hoare forward.
        pauto.
        rewrite Hnthval'_OSMapVallist_x0.
        congruence.
        rewrite Hnthval'_OSMapVallist_x0.
        auto.
        rewrite Hnthval'_OSMapVallist_x0.
        auto.
        rewrite Hnthval'_OSMapVallist_x0.
        simpl negint.
        simpl val_inj.
        

        (* ++ sys_channel_info ′ → count; *)
        hoare forward.
        simpl.
        clear - chcount_range freetblv_range.
        rewrite byte_max_unsigned_val.
        lets Hfreetbl': Int.and_le freetblv (Int.not x0).
        assert (Int.unsigned (freetblv&ᵢInt.not x0) <=255) as freetbl'_range by lia.
        clear Hfreetbl'.
        pauto.
        
        (* channel ′ → semaphore =ₑ  semaphore ′ *)
        hoare name lift ( Astruct (chanfptrb, Int.zero)) pre.
        hoare evar lift channel pre.
        hoare abs lift pre.
        eapply assign_rule_struct_aop; try reflexivity.
        auto. auto.
        intros.
        auto.
        symbolic_execution.
        now apply assign_type_match_true.
        simpl. lia.
        intros. sep auto.
      }
      (* channel ′ → channelID =ₑ
                                                 channelID ′;ₛ
      channel ′ → OSEventPtr =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
      channel ′ → srcPort =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → dstPortsHead =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → dstPortsTail =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → srcPortsNum =ₑ ′ 0;ₛ
      channel ′ → dstPortsNum =ₑ ′ 0;ₛ *)
      hoare forward.
      pauto.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare name lift Aop errptr pre.
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    (* CSLSEMREL (〈 char_t 〉 ′ OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ *)
    eapply seq_rule.
    {
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H. unfold CurLINV. sep auto.
    }
    partition_absrulestac absinfer_seq_end.
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros.
    sep name lift ChannelNode in H.
    lets Htmp: ChannelNode_getsome_Vnull_frm Hcond2 H. clear H.
    sep destruct Htmp.
    sep normal.
    sep eexists.
    sep autocancel.
    unfold AOSUnMapTbl.
    unfold AOSMapTbl.
    sep autocancel.
    sep split.
    2,3: reflexivity.
    right.
    sep normal.
    sep eexists.
    sep split in Htmp.
    unfold AOSChannelFreeList.
    unfold channelf_sll.
    sep normal.
    sep autocancel.
    sep cancel 4%nat 2%nat.
    instantiate (1:= (Vint32 channelID_v
    :: V$ 0 :: V$ 0 :: Vint32 x :: Vnull :: Vnull :: Vnull :: Vnull :: nil)).
    rewrite H.
    rewrite H0.
    rewrite H1.
    simpljoin.
    rewrite <- H2 at 1.
    rewrite update_nth_val_midlle.
    rewrite <- H3 at 1.
    rewrite update_nth_vallist_middle.
    rewrite <- H4 at 1.
    rewrite update_nth_middle.
    sep name lift ChannelNode.
    eapply ChannelNode_compose.
    rewrite H2. setoid_rewrite H3. congruence.
    rewrite H2. setoid_rewrite H4. congruence.
    reflexivity.
    reflexivity.
    simpl.
    rewrite byte_max_unsigned_val.
    assert (Int.unsigned x <= 255) by lia.
    pauto.
    rewrite Int.unsigned_repr.
    2: clear; rewrite max_unsigned_val; lia.
    unfold Coqlib.nat_of_Z.
    simpl Z.to_nat.
    cbn [Channel_dstkport_get].
    sep autocancel.
    sep split; auto.
    2: reflexivity.
    assert (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) chcount = false).
    {
      clear - Hchcount_le_CHANNEL_NUMS.
      apply Intlt_false_is_Zge.
      rewrite Int.unsigned_repr. lia.
      unfold OS_INTER_CORE_CHANNEL_NUMS.
      rewrite max_unsigned_val.
      lia.
    }
    rewrite H in Hcond1.
    simpl in Hcond1.
    destruct (Int.eq chcount ($ OS_INTER_CORE_CHANNEL_NUMS)) eqn:E'.
    {
      simpl in Hcond1.
      assert (Int.ltu Int.zero Int.zero=false) by reflexivity.
      rewrite H0 in Hcond1.
      simpl in Hcond1.
      assert (Int.ltu Int.zero Int.one = true) by reflexivity.
      rewrite H1 in Hcond1.
      simpl in Hcond1.
      rewrite H1 in Hcond1.
      discriminate.
    }
    apply sem_lab.semacc_int_eq_false in E'.
    destruct (Z.eq_dec (Int.unsigned chcount) OS_INTER_CORE_CHANNEL_NUMS).
    rewrite <- e in E'.
    rewrite Int.repr_unsigned in E'. congruence.
    assert (Int.unsigned chcount < OS_INTER_CORE_CHANNEL_NUMS) by lia.
    clear - H0 chcount_range.
    rewrite Int.add_unsigned.
    rewrite Int.unsigned_repr.
    rewrite Int.unsigned_repr.
    lia.
    rewrite max_unsigned_val. lia.
    rewrite max_unsigned_val.
    rewrite Int.unsigned_repr. unfold OS_INTER_CORE_CHANNEL_NUMS in H0. split; try lia.
    pose proof Int.unsigned_range chcount. lia.
    rewrite max_unsigned_val. lia.
    splits; auto.
    simpl.
    rewrite byte_max_unsigned_val.
    pose proof Int.and_le freetblv (Int.not x0).
    assert (Int.unsigned (freetblv&ᵢInt.not x0) <= 255) by lia.
    clear - H0 Hchcount_le_CHANNEL_NUMS.
    assert (Int.unsigned (chcount +ᵢ  $ 1) <= 255).
    {
      unfold OS_INTER_CORE_CHANNEL_NUMS in Hchcount_le_CHANNEL_NUMS.
      rewrite Int.add_unsigned.
      rewrite Int.unsigned_repr.
      rewrite Int.unsigned_repr.
      lia.
      rewrite max_unsigned_val. lia.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr.
      pose proof Int.unsigned_range chcount. lia.
      rewrite max_unsigned_val. lia.
    }
    pauto.
  }
  {
    apply disj_rule.
    apply pfalse_rule.
    naive pure intro.
    hoare abs lift pre.
    eapply seq_rule.
    {
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H1. unfold CurLINV. sep auto.
    }
    partition_absrulestac absinfer_seq_end.
    hoare name lift Aop errptr pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros. sep normal. sep eexists.
    sep autocancel.
    unfold AOSUnMapTbl.
    unfold AOSMapTbl.
    sep autocancel.
    sep split; auto.
    left.
    sep autocancel.
    unfold node.
    sep normal.
    sep eexists.
    sep autocancel.
    sep split; auto.
    tauto.
    splits; auto. pauto.
    reflexivity.
  }
  eapply seq_rule.
  {
    eapply ift_rule' with (q:=Afalse).
    intros.
    symbolic_execution.
    rewrite byte_max_unsigned_val. pauto.
    clear - EchnID_v.
    unfold CHANNEL_NUMS in EchnID_v.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    rewrite Hlen_chanvl_CHANNLE_NUMS.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match; eauto.
    rewrite Hlen_chanvl_CHANNLE_NUMS.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    lets Htmp: nthval'_has_value_ptr (Z.to_nat (Int.unsigned channelID_v)) Hchanvl_type_match Hlen_chanvl_CHANNLE_NUMS.
    destruct Htmp.
    unfold CHANNEL_NUMS in *. simpl.
    apply Intlt_true_is_Zlt in EchnID_v.
    rewrite Int.unsigned_repr in EchnID_v.
    lia. rewrite max_unsigned_val. lia.
    destruct H1.
    destruct x1; try discriminate.
    now rewrite H1.
    rewrite H1. simpl. destruct a; auto.
    naive pure intro.
    rename H into Hcond1.
    assert (nth_error  chanvl (Z.to_nat (Int.unsigned channelID_v)) = Some Vnull).
    {
      simpljoin.
      destruct (nth_val' (Z.to_nat (Int.unsigned channelID_v))) eqn:E; simpl in H, H0, H1; try congruence.
      2:{
          destruct a. simpl in H. congruence.
      }
      clear H H0 H1.
      apply nth_val_nth_error.
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2. congruence.
      rewrite Hlen_chanvl_CHANNLE_NUMS.
      unfold CHANNEL_NUMS in *. simpl.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      lia. rewrite max_unsigned_val. lia.
    }
    clear H0. rename H into Hcond2.
    unfold AOSChannelFreeList at 3.
    
    (* channel ′ =ₑ OSChannelFreeList ′;ₛ *)
    hoare normal pre.
    hoare_assert_pure (isptr chanfptr).
    {
       eapply channelf_sll_head_isptr_frm with (s:=s0).
       sep autocancel. apply H.
    }
    naive pure intro.
    rename H into Hchanfptr_isptr.
    hoare forward.
    clear - Hchanfptr_isptr.
    pauto.
    unfold isptr in Hchanfptr_isptr.
    destruct Hchanfptr_isptr.
    {
      subst.
      (* err ′ =ₑ ′ OS_CHANNEL_DEPLETED *)
      eapply seq_rule.
      {
        eapply if_zero_rule.
        intros.
        symbolic_execution.
        hoare name lift Aop errptr pre.
        eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto.
      }
      (* CSLSEMREL (〈 char_t 〉 ′ OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ *)
      eapply seq_rule.
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H. unfold CurLINV. sep auto.

      (* RETURN channel ′ *)
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      unfold AOSUnMapTbl.
      unfold AOSMapTbl.
      sep autocancel.
      sep split; auto.
      left.
      sep autocancel.
      unfold node.
      sep normal.
      sep eexists.
      sep autocancel.
      unfold AOSChannelFreeList.
      sep normal.
      sep eexists.
      sep split; auto.
      sep autocancel.
      tauto.
      splits; auto.
      pauto.
      reflexivity.
    }
    destruct H. subst chanfptr.
    rename x1 into chanfptr.
    destruct chanfl.
    {
      unfold channelf_sll.
      cbn [channelf_sllseg].
      naive pure intro.
      discriminate H. 
    }
    rename v into chanfvl.
    unfold channelf_sll.
    cbn [channelf_sllseg].
    naive pure intro.
    rename v' into chanfptr'. 
    rename H into Hchanfvl_V_OSEventPtr.
    rename H0 into Hchanfl_V_channelID.
    rename H1 into Hchanfl_V_srcnum.
    rename H2 into Hchanfl_V_dstnum.
    rename H3 into Hchanfl_V_sem.
    rename H4 into Hchanfl_V_dsthead.
    rename H5 into Hchanfl_V_dsttail.
    clear H6.

    unfold node.
    naive pure intro.
    destruct H as (Htmp&Hchanfl_type_match).
    rename v' into chanfptrb.
    inverts Htmp.
    apply struct_type_vallist_match_channel in Hchanfl_type_match.
    simpljoin.
    inverts Hchanfl_V_dsttail.
    inverts Hchanfl_V_dsthead.
    inverts Hchanfl_V_sem.
    inverts Hchanfl_V_dstnum.
    inverts Hchanfl_V_srcnum.
    inverts Hchanfl_V_channelID.
    inverts Hchanfvl_V_OSEventPtr.
    clear H0 H1 H2 H3 H4 H5.
    rename H6 into Hx6_isptr.
    rename H7 into Hchanfptr'_isptr.
    
    eapply seq_rule.
    {
      apply if_one_rule.
      intros.
      symbolic_execution.
      hoare forward.
      clear - Hx6_isptr Hchanfptr'_isptr.
      pauto.
      clear - Hchanfptr'_isptr.
      pauto.
      
      (* OSChannelIDTbl ′[ channelID ′] =ₑ channel ′;ₛ *)
      hoare forward.
      rewrite byte_max_unsigned_val. pauto.
      unfold CHANNEL_NUMS in *.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      simpl.
      lia. rewrite max_unsigned_val. lia.
      rewrite Hlen_chanvl_CHANNLE_NUMS.
      unfold CHANNEL_NUMS in *.
      apply Intlt_true_is_Zlt in EchnID_v.
      rewrite Int.unsigned_repr in EchnID_v.
      simpl. 
      lia. rewrite max_unsigned_val. lia.
      
      (* If( ch_type ′ ==ₑ ′ OUTCORE) *)
      eapply seq_rule.
      {
        apply corecommu_rules.ift_zero_rule.
        intros.
        symbolic_execution.
        now rewrite Echtype_Outcore.
      }
      (* channel ′ → channelID =ₑ
                                                 channelID ′;ₛ
      channel ′ → OSEventPtr =ₑ 〈 OS_Channel ∗ 〉 NULL;ₛ
      channel ′ → srcPort =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → dstPortsHead =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → dstPortsTail =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
      channel ′ → srcPortsNum =ₑ ′ 0;ₛ
      channel ′ → dstPortsNum =ₑ ′ 0;ₛ *)
      hoare forward.
      pauto.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare forward.
      hoare name lift Aop errptr pre.
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    (* CSLSEMREL (〈 char_t 〉 ′ OS_RESOURCE_SEMAPHORE_CHANNEL);ₛ *)
    eapply seq_rule.
    {
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H. unfold CurLINV. sep auto.
    }
    partition_absrulestac absinfer_seq_end.
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros.
    sep name lift ChannelNode in H.
    lets Htmp: ChannelNode_getsome_Vnull_frm Hcond2 H. clear H.
    sep destruct Htmp.
    sep normal.
    sep eexists.
    sep autocancel.
    unfold AOSUnMapTbl.
    unfold AOSMapTbl.
    sep autocancel.
    sep split.
    2,3: reflexivity.
    right.
    sep normal.
    sep eexists.
    sep split in Htmp.
    unfold AOSChannelFreeList.
    unfold channelf_sll.
    sep normal.
    sep autocancel.
    sep cancel 4%nat 2%nat.
    instantiate (1:= (Vint32 channelID_v
    :: V$ 0
       :: V$ 0
          :: V$ DEFAULT_CHANNLE_SEMAPHROE :: Vnull :: Vnull :: Vnull :: Vnull :: nil)).
    rewrite H.
    rewrite H0.
    rewrite H1.
    simpljoin.
    rewrite <- H2 at 1.
    rewrite update_nth_val_midlle.
    rewrite <- H3 at 1.
    rewrite update_nth_vallist_middle.
    rewrite <- H4 at 1.
    rewrite update_nth_middle.
    sep name lift ChannelNode.
    eapply ChannelNode_compose.
    rewrite H2. setoid_rewrite H3. congruence.
    rewrite H2. setoid_rewrite H4. congruence.
    reflexivity.
    reflexivity.
    simpl.
    rewrite byte_max_unsigned_val.
    assert (Int.unsigned x <= 255) by lia.
    pauto.
    rewrite Int.unsigned_repr.
    2: clear; rewrite max_unsigned_val; lia.
    unfold Coqlib.nat_of_Z.
    simpl Z.to_nat.
    cbn [Channel_dstkport_get].
    sep autocancel.
    sep split; auto.
    2: reflexivity.
    assert (Int.ltu ($ OS_INTER_CORE_CHANNEL_NUMS) chcount = false).
    {
      clear - Hchcount_le_CHANNEL_NUMS.
      apply Intlt_false_is_Zge.
      rewrite Int.unsigned_repr. lia.
      unfold OS_INTER_CORE_CHANNEL_NUMS.
      rewrite max_unsigned_val.
      lia.
    }
    auto.
    splits; auto.
    pauto.
  }
  {
    apply disj_rule.
    apply pfalse_rule.
    naive pure intro.
    hoare abs lift pre.
    eapply seq_rule.
    {
      eapply cslsemrel_rule.
      go.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      rewrite max_unsigned_val.
      rewrite Int.unsigned_repr. lia.
      rewrite max_unsigned_val. lia.
      intros.
      rewrite Int.unsigned_repr.
      rewrite Z2Nat.id.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL.
      symbolic_execution.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. lia.
      unfold OS_RESOURCE_SEMAPHORE_CHANNEL. rewrite max_unsigned_val. lia.
      intros. unfold p_local in H1. unfold CurLINV. sep auto.
    }
    partition_absrulestac absinfer_seq_end.
    hoare name lift Aop errptr pre.
    eapply seq_rule.
    {
      eapply assign_rule_general.
      symbolic_execution. reflexivity.
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto.
    }
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros. sep normal. sep eexists.
    sep autocancel.
    unfold AOSUnMapTbl.
    unfold AOSMapTbl.
    sep autocancel.
    sep split; auto.
    left.
    sep autocancel.
    unfold node.
    sep normal.
    sep eexists.
    sep autocancel.
    sep split; auto.
    tauto.
    splits; auto. pauto.
    reflexivity.
  }
Qed.