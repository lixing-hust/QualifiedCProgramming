Require Import ucos_include.
Require Import Lia.

Require Import aux_pureLib.

Require Import abs_op_corecommu_rules.
Require Import corecommu_sep_added.
Require Import corecommu_tactics.
Require Import partition_rules.
Require Import partition_seprules.
Require Import partition_absrules.
Require Import partition_symrules.
Require Import partition_tactics.
Require Import corecommu_rules.

Open Scope code_scope.

Open Scope int_scope.

Ltac hoare_ex_intro ::=
  repeat match goal with
    | |- {| _, _, _, _, _, _ |} |- _  {{ EX _, _ }} _ {{ _ }} =>
      apply ex_intro_rule; intros 
  end.

Lemma kportf_sll_head_isptr_frm : forall l p s P,
  s |= kportf_sll p l OS_K_Port OS_K_Port_V_OSEventPtr ** P ->
  isptr p.
Proof.
  induction l.
  - intros. cbn in H. simpljoin.
    unfold isptr. tauto. 
  - intros.
    unfold kportf_sll in H; cbn [kportf_sllseg] in H;unfold node in H.
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

Lemma struct_type_vallist_match_kport: forall kport,
  struct_type_vallist_match os_ucos_h.OS_K_Port kport ->
  exists i i0 i1 i2 x1 x2 x3, kport = Vint32 i2 :: Vint32 i1 :: x1 :: x2 :: Vint32 i0 :: Vint32 i :: x3 :: nil/\
  Int.unsigned i <= 255 /\
  Int.unsigned i1 <= 255 /\
  Int.unsigned i2 <= 255 /\
  Int.unsigned i0 <= 255 /\
  isptr x1 /\
  isptr x2 /\
  isptr x3.
Proof.
  unfold OS_K_Port.
  intros.
  struct_type_vallist_match_elim.
  jauto.
Qed.

Lemma OSKernelPortCreate_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSKernelPortCreate vl logicl OSKernelPortCreatePre ct->
      Some r =
      BuildRetI os_internal OSKernelPortCreate vl logicl OSKernelPortCreatePost ct->
      exists t d1 d2 s,
        os_internal OSKernelPortCreate = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  simpljoin1.
  inverts H.

  rename v'2 into dmportp.
  rename v'3 into portid.
  rename v'4 into errptr.
  rename v'5 into errv.
  rename v'6 into aop.
  rename v'7 into er.
  rename v'8 into nest.
  rename v'9 into kportp.
  rename v'10 into kportfl.
  rename v'11 into dportp.
  rename v'12 into dportl.
  rename v'13 into dportmsgll.
  rename v'14 into dpptrl.
  rename v'15 into cportp.
  rename v'16 into kportpl.
  rename v'17 into kportl.
  rename v'18 into dmport.
  rename v'19 into dmevetype.
  rename H0 into Hppl.
  rename H2 into Harkpl.
  rename H5 into Hkplen.
  rename H6 into Htydmp.
  rename H4 into Hcisp.
  rename H8 into Hdisp.

  unfold OSKernelPortCreate_aspec, spec_code_cons.

  (* port ′ =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ
  resource_get_res ′ =ₑ 〈 char_t 〉 ′ 0;ₛ *)
  hoare forward.
  hoare forward.

  (* If (portId ′ ≥ ′ PORT_NUMS)
    {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
    RETURN 〈 OS_K_Port ∗ 〉 NULL};ₛ *)
  destruct (Int.ltu portid ($ PORT_NUMS)) eqn:Hportid.
  2:{ hoare forward.
      pauto. pauto. pauto.
      { hoare normal pre; pure intro.
        clear H H0 H2.
        instantiate(1:=Afalse).
        eapply seq_rule.
        { eapply assign_rule_general.
          symbolic_execution.
          { split. intros Hs.
            sep name lift errv in Hs.
            apply Hs. sep pauto. }
          symbolic_execution.
          now apply assign_type_match_true.
          intros. sep auto. }
        partition_absrulestac absinfer_choice1.
        partition_absrulestac absinfer_seq_end.
        eapply rete_rule'.
        { intros. symbolic_execution. }
        intros. sep normal. sep eexists.
        sep autocancel.
        sep split; auto.
        left. sep autocancel.
        sep split; auto.
        reflexivity. }
      hoare forward. naive pure intro.
      exfalso. clear - H Hportid.
      destruct H.
      destruct (Int.eq_dec portid ($ PORT_NUMS)).
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
      destruct (Int.ltu ($ PORT_NUMS) portid);
      destruct (Int.eq portid ($ PORT_NUMS));
      discriminate. }
  
  hoare forward.
  1,2,3: pauto.
  { hoare normal pre; pure intro.
    instantiate (1:=Afalse).
    exfalso. clear - Hportid H.
    destruct (Int.eq_dec portid ($ PORT_NUMS)).
    subst. discriminate.
    rewrite Int.eq_false in H; auto.
    destruct (Int.ltu ($ PORT_NUMS) portid) eqn: ?;
    simpl in H;
    assert (Int.ltu Int.zero Int.one = true) by reflexivity;
    assert (Int.ltu Int.zero Int.zero = false) by reflexivity;
    try rewrite H0 in H; rewrite H1 in H;
    simpl in H; tryfalse. clear H0 H1.
    apply Intlt_true_is_Zlt in Hportid.
    apply Intlt_true_is_Zlt in Heqb. lia. }
  hoare forward. naive pure intro. clear H.

  (* If (OSIntNesting ′ >ₑ ′ 0)
  {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_ERR_CREATE_ISR;ₛ
  RETURN 〈 OS_K_Port ∗ 〉 NULL};ₛ *)
  destruct (Int.ltu Int.zero nest) eqn:Hnest.
  { hoare forward. pauto.
    eapply seq_rule.
    { naive pure intro.
      eapply assign_rule_general.
      symbolic_execution.
      { split. intros Hs.
        sep name lift errv in Hs.
        apply Hs. sep pauto. }
      symbolic_execution.
      now apply assign_type_match_true.
      intros. sep auto. }
    partition_absrulestac absinfer_choice1.
    partition_absrulestac absinfer_seq_end.
    eapply rete_rule'.
    { intros. symbolic_execution. }
    intros. sep normal. sep eexists.
    sep autocancel.
    sep split; auto.
    left. sep auto.
    reflexivity.
    hoare forward.
    naive pure intro.
    setoid_rewrite Hnest in H.
    simpl in H.
    destruct H; discriminate. }
  eapply seq_rule.
  { apply corecommu_rules.ift_zero_rule.
    intros. symbolic_execution.
    now setoid_rewrite Hnest. }
  
  (* corPort_ptr ′ =ₑ OSDomainPortPtrList ′;ₛ *)
  unfold AOSDomainPortPtrList.
  hoare normal pre; pure intro.
  hoare forward.
  { clear - Hppl.
    destruct dportl; destruct dpptrl;
    simpl in Hppl; tryfalse; simpljoin1. }
  
  (* WHILE (corPort_ptr ′ !=ₑ 〈 OS_Port ∗ 〉 NULL)
    {If (corPort_ptr ′ ==ₑ dmPort ′)
    {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
    RETURN 〈 OS_K_Port ∗ 〉 NULL};ₛ
    corPort_ptr ′ =ₑ corPort_ptr ′ .. nextPort};ₛ *)
  eapply seq_rule.
  { hoare remember (1::2::nil)%nat pre.
    eapply backward_rule1.
    { instantiate (1:=
        EX corpp,
        ( [| corpp = Vnull |] **
          [| forall n, nth_error dpptrl n <> Some dmportp |]
          \\//
          EX n portp,
          [| nth_error dpptrl n = Some portp |] **
          [| corpp = Vptr portp |] **
          [| forall m, (m < n)%nat ->
              nth_error dpptrl m <> Some dmportp |] ) **
        <|| END None;; aop
        ?? Semacc_err (V$ OS_RESOURCE_SEMAPHORE_PORT);; END None;; aop
          ?? Semacc_succ (V$ OS_RESOURCE_SEMAPHORE_PORT);;
              Semrelease (V$ OS_RESOURCE_SEMAPHORE_PORT);; END None;; aop ||>  **
        LV corPort_ptr @ OS_Port ∗ |-> corpp ** H ).
      intros. sep normal. sep eexists. sep autocancel.
      destruct dportl; destruct dpptrl;
      simpl in Hppl; tryfalse.
      { subst dportp. left. sep pauto.
        intros. rewrite nth_error_nil. auto. }
      { destruct Hppl as [Hppl0 [hd [Hppl1 Hppl2]]].
        subst dportp. right.
        sep normal. exists 0%nat a. sep pauto.
        intros. inversion H. } }
    subst H.
    eapply while_rule.
    { intros ? Hs.
      sep normal in Hs. sep destruct Hs.
      apply disj_split in Hs. destruct Hs.
      { symbolic execution. }
      { symbolic execution.
        { destruct x1; pauto. }
        { destruct x1; pauto. } } }
      naive pure intro.
      rename v'2 into corpp.
      eapply aconj_aistrue_rule.
      { intros ? Hs.
        sep normal in Hs. sep destruct Hs.
        apply disj_split in Hs.
        instantiate (1:=val_inj (notint (val_inj (val_eq corpp Vnull)))).
        destruct Hs.
        { symbolic execution. }
        { symbolic execution.
          { destruct x0; pauto. }
          { destruct x0; pauto. } } }
      hoare normal pre; pure intro.
      eapply backward_rule1.
      { intros ? Hs.
        eapply disj_split in Hs; apply Hs. }
        eapply disj_rule.
        { hoare normal pre; pure intro.
          exfalso. clear - H. pauto. }
        hoare normal pre; pure intro.
        rename v'3 into corp. rename v'2 into n.
        
        (* If (corPort_ptr ′ ==ₑ dmPort ′)
          {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_INVALID;ₛ
          RETURN 〈 OS_K_Port ∗ 〉 NULL};ₛ *)
        hoare forward.
        { destruct corp; destruct dmportp; pauto. }
        { instantiate (1:=Afalse).
          hoare normal pre; pure intro.
          eapply seq_rule.
          { eapply assign_rule_general.
            symbolic_execution.
            { split. intros Hs.
              sep name lift errv in Hs.
              apply Hs. sep pauto. }
            symbolic_execution.
            now apply assign_type_match_true.
            intros. sep auto. }
          partition_absrulestac absinfer_choice1.
          partition_absrulestac absinfer_seq_end.
          eapply rete_rule'.
          { intros. symbolic_execution. }
          intros. sep normal. sep eexists.
          sep autocancel.
          sep split; auto.
          left. sep autocancel.
          sep split; auto.
          reflexivity. }
        hoare forward.
        hoare normal pre; pure intro.
        assert (corp = dmportp \/ corp <> dmportp) by tauto.
        destruct H7.
        { subst corp. exfalso. clear - H5.
          destruct dmportp. rewrite peq_true in H5.
          rewrite Int.eq_true in H5. simpl in H5.
          destruct H5; inverts H. }
        clear H5.
        apply nth_error_split in H4.
        destruct H4 as [dpptrl1 [dpptrl2 [? ?]]].
        subst n dpptrl.
        hoare name lift dmportp_sll pre.
        hoare remember (1::nil)%nat pre.
        eapply backward_rule1.
        { instantiate ( 1:=[| length dportl = length dportmsgll |] **
                        dmportp_sll dportp dportl dportmsgll OS_Port_V_nextPort ** H4 ).
          intros * Hs. sep cancel H4. clear - Hs.
          revert dportl dportmsgll dportp s Hs.
          induction dportl; destruct dportmsgll;
          unfold dmportp_sll; cbn [dmportp_sllseg]; intros; sep pauto.
          { exfalso. eapply sep_exist_Afalse in Hs. auto. }
          { exfalso. eapply sep_exist_Afalse in Hs. auto. }
          sep name lift dmportp_sllseg in Hs.
          eapply astar_mono in Hs.
          2:{ instantiate (1:=[| length dportl = length dportmsgll |] **
                              dmportp_sll x dportl dportmsgll OS_Port_V_nextPort).
              intros. eapply IHdportl. unfold dmportp_sll. auto. }
          2: eauto.
          sep normal in Hs. sep split in Hs.
          simpl; lia. }
        subst H4. naive pure intro. rename H4 into Hlen_dp.
        assert (exists dportl1 port dportl2,
                dportl = dportl1 ++ port :: dportl2 /\
                length dpptrl1 = length dportl1).
        { clear - Hppl.
          revert dpptrl1 corp dpptrl2 dportl dportp Hppl.
          induction dpptrl1; simpl; intros.
          { destruct dportl;
            cbn [RL_PortPtrList] in Hppl; tryfalse.
            simpljoin1.
            exists (@nil vallist) v dportl.
            simpl; split; auto. }
          { destruct dportl;
            cbn [RL_PortPtrList] in Hppl; tryfalse.
            simpljoin1.
            specialize (IHdpptrl1 _ _ _ _ H1).
            simpljoin1. exists (v :: x0) x1 x2.
            split; simpl; eauto. } }
        destruct H4 as [dportl1 [port [dportl2 [? ?]]]].
        subst dportl.
        assert (exists dportmsgll1 msgl dportmsgll2,
                dportmsgll = dportmsgll1 ++ msgl :: dportmsgll2 /\
                length dportmsgll1 = length dportl1).
        { clear - Hlen_dp.
          revert dportl1 port dportl2 dportmsgll Hlen_dp.
          induction dportl1; destruct dportmsgll; simpl; intros.
          1,3: lia.
          { exists (@nil (list vallist)) l dportmsgll.
            simpl; auto. }
          assert (length (dportl1 ++ port :: dportl2) = length dportmsgll) by lia.
          specialize (IHdportl1 _ _ _ H). simpljoin1.
          exists (l :: x) x0 x1. simpl; auto. }
        destruct H4 as [dportmsgll1 [msgl [dportmsgll2 [? ?]]]].
        subst dportmsgll.
        eapply backward_rule1.
        { eapply dmportp_sllseg_app'_frm.
          { rewrite <- H5. reflexivity. }
          { lia. }
          2:{ eauto. }
          { eapply nth_error_middle. } }
        cbn [dmportp_sllseg].
        hoare normal pre; pure intro.
        rename v'3 into corp.
        rename v'2 into nxp.
        rename v'4 into qstart.

        (* corPort_ptr ′ =ₑ corPort_ptr ′ .. nextPort *)
        hoare name lift Aop pre.
        eapply forward_rule2.
        { eapply assign_rule_lvar.
          { split.
            { intros Hs.
              sep name lift corPort_ptr in Hs.
              apply Hs. }
            sep pauto. }
          { intros ? Hs.
            eapply corport_nextPort_rv.
            { apply H9. }
            { auto. }
            { sep name lift corPort_ptr in Hs.
              apply Hs. } }
          { apply eq_vptr; eauto. }
          { sep auto. } }
        intros ? Hs.
        sep normal. exists nxp. sep autocancel.
        sep lift 2%nat.
        eapply dmportp_sllseg_app'_frm.
        { rewrite <- H5. reflexivity. }
        { lia. }
        2: eauto.
        { apply nth_error_middle. }
        sep lift 4%nat in Hs.
        sep autocancel.
        cbn [dmportp_sllseg].
        sep normal. exists nxp corp qstart.
        sep pauto.
        assert (RL_PortPtrList (Vptr corp) (port :: dportl2) (corp :: dpptrl2)).
        { eapply RL_PortPtrList_snd; eauto. }
        cbn in H4. destruct H4 as [? [? [? ?]]].
        clear H4. rewrite H12 in H9; inverts H9.
        destruct dpptrl2; destruct dportl2;
        simpl in H13; tryfalse.
        { subst nxp. left. sep pauto. intros.
          assert ((n < length dpptrl1)%nat \/
                  (n = length dpptrl1)%nat \/ 
                  (n > length dpptrl1)%nat) by lia.
          destruct H4; [ |destruct H4].
          { apply H6. auto. }
          { subst n. rewrite nth_error_middle.
            intro. inverts H4. contradiction. }
          assert ((length (dpptrl1 ++ corp :: nil) <= n)%nat).
          { assert (length (dpptrl1 ++ corp :: nil) = S (length dpptrl1)).
            { clear. induction dpptrl1; simpl; eauto. }
            rewrite H9. lia. }
          apply nth_error_None in H9.
          rewrite H9. auto. }
        { destruct H13 as [? [? [? ?]]].
          right. sep normal. exists (S (length dpptrl1)) a.
          sep pauto.
          { intros.
            assert ((m < length dpptrl1)%nat \/
                    (m = length dpptrl1)%nat) by lia.
            destruct H14.
            { apply H6. auto. }
            { subst m. rewrite nth_error_middle.
              intro. inverts H14. contradiction. } }
          { assert (dpptrl1 ++ corp :: a :: dpptrl2 =
                    (dpptrl1 ++ corp :: nil) ++ a :: dpptrl2).
            { clear. induction dpptrl1; simpl; eauto.
              rewrite IHdpptrl1. auto. }
            rewrite H4.
            assert (S (length dpptrl1) = length (dpptrl1 ++ corp :: nil)).
            { clear. induction dpptrl1; simpl; eauto. }
            rewrite H14. apply nth_error_middle. } } }
  naive pure intro. rename v'2 into corp.
  eapply aconj_aisfalse_rule.
  { intros ? Hs.
    apply disj_split in Hs.
    instantiate (1:=val_inj (notint (val_inj (val_eq corp Vnull)))).
    destruct Hs as [Hs|Hs]; sep normal in Hs; sep destruct Hs.
    { symbolic_execution. }
    { symbolic_execution.
      { destruct x0. pauto. }
      { destruct x0. pauto. } } }
  hoare normal pre; pure intro.
  eapply backward_rule1.
  intros ? Hs; eapply disj_split in Hs; apply Hs.
  eapply disj_rule; hoare normal pre; pure intro.
  2:{ exfalso. clear - H.
      unfold val_eq, notint, val_inj in *.
      destruct v'3; simpl in H.
      destruct H; inverts H. }
  clear H. rename H2 into Hpl_dmp.

  partition_absrulestac absinfer_choice2.
  hoare name lift Aop resource_get_res pre.
  (* CSLSEMACC (′ OS_RESOURCE_SEMAPHORE_PORT, resource_get_res ′);ₛ *)
  eapply seq_rule.
  { eapply cslsemacc_rule'.
    go.
    unfold OS_RESOURCE_SEMAPHORE_PORT.
    rewrite max_unsigned_val.
    rewrite Int.unsigned_repr. lia.
    rewrite max_unsigned_val. lia.
    intros.
    rewrite Int.unsigned_repr.
    rewrite Z2Nat.id.
    unfold OS_RESOURCE_SEMAPHORE_PORT.
    symbolic_execution.
    unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
    unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
    intros. unfold p_local in H. unfold CurLINV. sep auto.
    intros. unfold p_local in H. unfold CurLINV. sep auto. }
  apply disj_rule.
  { eapply seq_rule.
    { eapply corecommu_rules.ift_nonzero_rule.
      intros.
      exists (Int.one).
      sep split.
      symbolic_execution.
      reflexivity.
      hoare name lift Aop errptr pre.
      eapply seq_rule.
      { eapply assign_rule_general.
        symbolic_execution. reflexivity.
        symbolic_execution.
        now apply assign_type_match_true.
        intros. sep auto. }
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      intros. sep normal. sep eexists.
      sep autocancel.
      sep split; auto.
      left. sep auto.
      reflexivity. }
    apply pfalse_rule. }
  (* If (resource_get_res ′ ==ₑ 〈 char_t 〉 ′ 0)
    {∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_FAIL_TO_GET;ₛ *)
  eapply seq_rule.
  { apply corecommu_rules.ift_zero_rule.
    intros. symbolic_execution. }
  
  (* If (OSKernelPortIDTbl ′ [portId ′] ==ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
  eapply seq_rule.
  { eapply ift_rule' with (q:=Afalse).
    { symbolic_execution.
      { apply Intlt_true_is_Zlt in Hportid.
        unfold PORT_NUMS in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. }
      { rewrite Hkplen.
        unfold nat_of_Z, PORT_NUMS.
        rewrite Z2Nat.id; [ |mauto].
        apply Intlt_true_is_Zlt in Hportid.
        unfold PORT_NUMS in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. }
      { eapply symbolic_lemmas.array_type_vallist_match_imp_rule_type_val_match; eauto.
        rewrite Hkplen.
        unfold nat_of_Z, PORT_NUMS in *.
        apply Z2Nat.inj_lt.
        apply Int.unsigned_range.
        mauto.
        apply Intlt_true_is_Zlt in Hportid.
        unfold PORT_NUMS in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. }
      lets Htmp: nthval'_has_value_ptr (Z.to_nat (Int.unsigned portid)) Harkpl Hkplen.
      destruct Htmp.
      { unfold nat_of_Z, PORT_NUMS.
        apply Z2Nat.inj_lt.
        apply Int.unsigned_range.
        mauto.
        apply Intlt_true_is_Zlt in Hportid.
        unfold PORT_NUMS in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. }
      destruct H0.
      destruct x; try discriminate.
      now rewrite H0.
      rewrite H0. simpl. destruct a. pauto. }
    naive pure intro.
    rename H into Hcond1.
    assert (nth_error kportpl (Z.to_nat (Int.unsigned portid)) = Some Vnull).
    { simpljoin.
      destruct (nth_val' (Z.to_nat (Int.unsigned portid))) eqn:E;
      simpl in H, H0, H2; try congruence.
      2:{ destruct a. simpl in H. congruence. }
      clear H H0 H2.
      apply nth_val_nth_error.
      rewrite symbolic_lemmas.nth_val_imp_nth_val'_2. congruence.
      rewrite Hkplen.
      unfold nat_of_Z, PORT_NUMS in *.
      apply Z2Nat.inj_lt.
      apply Int.unsigned_range.
      mauto.
      apply Intlt_true_is_Zlt in Hportid.
      unfold PORT_NUMS in Hportid.
      assert (Int.unsigned ($ 64) = 64) by mauto.
      lia. }
    clear Hcond1. rename H into Hcond.
    
    (* port ′ =ₑ OSKernelPortFreeList ′;ₛ  *)
    unfold AOSKernelPortFreeList at 4.
    hoare normal pre.
    hoare_assert_pure (isptr kportp).
    { eapply kportf_sll_head_isptr_frm with (s:=s0).
      sep autocancel. apply H. }
    naive pure intro.
    rename H into Hkportp_isptr.
    hoare forward.
    pauto.
    unfold isptr in Hkportp_isptr.
    destruct Hkportp_isptr.
    { subst. eapply seq_rule.
      { hoare forward.
        instantiate (1:=Afalse).
        hoare normal pre; pure intro.
        exfalso. clear - H. pauto. }
      hoare forward.
      hoare normal pre; pure intro.
      clear H.
      
      (* If (dmPort ′ .. os_code_defs.direction ==ₑ ′ DESTINATION)
      {dmPort ′ .. OSEventPtr =ₑ OSCorePortPtrList ′;ₛ
      OSCorePortPtrList ′ =ₑ dmPort ′};ₛ *)

      assert ((length dmport = 18%nat)%nat).
      { clear - Htydmp.
        destruct dmport; simpl in Htydmp; tryfalse.
        do 18 (destruct Htydmp as [? Htydmp];
        destruct dmport; simpl in Htydmp; tryfalse).
        simpl. auto. }
      rename H into Hdmlen.

      assert (exists dir, nth_val' 4 dmport = Vint32 dir).
      { clear - Htydmp.
        destruct dmport; simpl in Htydmp; tryfalse.
        do 4 (destruct Htydmp as [? Htydmp];
        destruct dmport; simpl in Htydmp; tryfalse).
        simpl. destruct Htydmp.
        destruct v3; tryfalse. eauto. }
      destruct H as [dir Hdmdir].

      assert (exists evp, nth_val' 10 dmport = evp /\ isptr evp).
      { clear - Htydmp.
        destruct dmport; simpl in Htydmp; tryfalse.
        do 10 (destruct Htydmp as [? Htydmp];
        destruct dmport; simpl in Htydmp; tryfalse).
        simpl. destruct Htydmp.
        destruct v9; tryfalse; unfold isptr; eauto. }
      destruct H as [evp [Hdmevp Hevpisp]].

      assert (exists nxp, nth_val' 11 dmport = nxp /\ isptr nxp).
      { clear - Htydmp.
        destruct dmport; simpl in Htydmp; tryfalse.
        do 11 (destruct Htydmp as [? Htydmp];
        destruct dmport; simpl in Htydmp; tryfalse).
        simpl. destruct Htydmp.
        destruct v10; tryfalse; unfold isptr; eauto. }
      destruct H as [nxp [Hdmnxp Hnxpisp]].

      eapply seq_rule.
      { eapply ift_rule'.
        { intros ? Hs. sep_get_port_rv.
          eapply dmPort_direction_rv.
          { eauto. }
          { sep autocancel.
            apply Hs. }
          { rewrite Hdmdir. simpl. pauto. }
          { pauto. } }
        naive pure intro.
        rewrite Hdmdir in H. simpl in H.
        destruct (Int.eq dir ($ DESTINATION)) eqn: Heqdir.
        2:{ simpl in H. destruct H. tryfalse. }
        clear H.
        (* dmPort ′ .. OSEventPtrPort =ₑ OSCorePortPtrList ′;ₛ *)
        eapply seq_rule.
        { eapply port_memeber_asgn' with (n := 10%nat).
          { split.
            { intros Hs. sep autocancel. apply Hs. }
            sep pauto. }
          { symbolic_execution. destruct Hcisp.
            { subst. auto. }
            { destruct H0. subst; auto. } }
          { go. }
          { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
            { rewrite Hdmevp. eauto. } { lia. } }
          { go. } { go. } { go. } { go. }
          { eapply eq_vptr; eauto. }
          { simpl. destruct Hcisp.
            { subst; auto. }
            { destruct H; subst; auto. } }
          { sep auto. } }
        (* OSCorePortPtrList ′ =ₑ dmPort ′ *)
        hoare remember (@nil nat) pre.
        eapply backward_rule1.
        { instantiate (1:=H ** [| Int.eq dir ($ DESTINATION) = true |]).
          sep pauto. }
        subst H. hoare normal pre.
        hoare forward. }
      eapply disj_rule.
      { (* Int.eq dir ($ DESTINATION) = true *)
        naive pure intro. rename H into Heqdir.

        assert (nth_val' 11 ((update_nth_val 10 dmport cportp)) = nxp).
        { apply nth_val_nth_val'_some_eq.
          rewrite nth_upd_neqrev'; auto.
          rewrite <- Hdmnxp.
          apply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
        rename H into Hupnxp.

        (* dmPort ′ .. nextPort =ₑ OSDomainPortPtrList ′;ₛ *)
        eapply seq_rule.
        { eapply port_memeber_asgn' with (n := 11%nat).
          { split.
            { intros Hs. sep autocancel. apply Hs. }
            sep pauto. }
          { symbolic_execution. destruct Hdisp.
            { subst. auto. }
            { destruct H0. subst; auto. } }
          { go. }
          { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
            { rewrite Hupnxp. eauto. }
            { rewrite update_nth_val_len_eq. lia. } }
          { go. } { go. } { go. } { go. }
          { eapply eq_vptr; eauto. }
          { simpl. destruct Hdisp.
            { subst; auto. }
            { destruct H; subst; auto. } }
          { sep auto. } }
        (* OSDomainPortPtrList ′ =ₑ dmPort ′;ₛ *)
        hoare forward.
        (* IF (port ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
        hoare forward.
        { instantiate (1:=Afalse).
          naive pure intro.
          exfalso. pauto. }
        { naive pure intro. clear H.
          (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_DEPLETED *)
          eapply assign_rule_general.
          symbolic_execution.
          { split. intros Hs.
            sep autocancel. apply Hs. sep pauto. }
          symbolic_execution.
          now apply assign_type_match_true.
          sep auto. }
        hoare forward.
        naive pure intro. clear H.
        (* CSLSEMREL (′ OS_RESOURCE_SEMAPHORE_PORT);ₛ *)
        eapply seq_rule.
        { eapply cslsemrel_rule.
          go.
          unfold OS_RESOURCE_SEMAPHORE_PORT.
          rewrite max_unsigned_val.
          rewrite Int.unsigned_repr. lia.
          rewrite max_unsigned_val. lia.
          intros.
          rewrite Int.unsigned_repr.
          rewrite Z2Nat.id.
          unfold OS_RESOURCE_SEMAPHORE_PORT.
          symbolic_execution.
          unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
          unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
          intros ? Hs. unfold p_local in Hs. unfold CurLINV. sep auto. }
        partition_absrulestac absinfer_seq_end.
        eapply rete_rule'.
        { intros. symbolic_execution. }
        { intros. sep normal. sep eexists.
          sep autocancel.
          sep split; auto.
          { right. sep autocancel.
            sep normal. sep split.
            2: eauto. apply disj_split.
            right. sep normal. sep autocancel.
            sep split; auto.
            { left. unfold AOSKernelPortFreeList.
              sep normal. sep pauto. }
            { unfold OS_Port_V_direction.
              rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
              2: lia. rewrite Hdmdir. repeat f_equal.
              apply sem_lab.semacc_int_eq_true. auto. } }
          reflexivity. } }
      { (* Int.eq dir ($ DESTINATION) = false *)
        naive pure intro.
        rewrite Hdmdir in H. simpl in H.
        destruct (Int.eq dir ($ DESTINATION)) eqn: Heqdir.
        { simpl in H. exfalso. destruct H; inverts H. }
        clear H.

        (* dmPort ′ .. nextPort =ₑ OSDomainPortPtrList ′;ₛ *)
        eapply seq_rule.
        { eapply port_memeber_asgn' with (n := 11%nat).
          { split.
            { intros Hs. sep autocancel. apply Hs. }
            sep pauto. }
          { symbolic_execution. destruct Hdisp.
            { subst. auto. }
            { destruct H0. subst; auto. } }
          { go. }
          { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
            { rewrite Hdmnxp. eauto. } { lia. } }
          { go. } { go. } { go. } { go. }
          { eapply eq_vptr; eauto. }
          { simpl. destruct Hdisp.
            { subst; auto. }
            { destruct H; subst; auto. } }
          { sep auto. } }
        (* OSDomainPortPtrList ′ =ₑ dmPort ′;ₛ *)
        hoare forward.
        (* IF (port ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
        hoare forward.
        { instantiate (1:=Afalse).
          naive pure intro.
          exfalso. pauto. }
        { naive pure intro. clear H.
          (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_DEPLETED *)
          eapply assign_rule_general.
          symbolic_execution.
          { split. intros Hs.
            sep autocancel. apply Hs. sep pauto. }
          symbolic_execution.
          now apply assign_type_match_true.
          sep auto. }
        hoare forward.
        naive pure intro. clear H.
        (* CSLSEMREL (′ OS_RESOURCE_SEMAPHORE_PORT);ₛ *)
        eapply seq_rule.
        { eapply cslsemrel_rule.
          go.
          unfold OS_RESOURCE_SEMAPHORE_PORT.
          rewrite max_unsigned_val.
          rewrite Int.unsigned_repr. lia.
          rewrite max_unsigned_val. lia.
          intros.
          rewrite Int.unsigned_repr.
          rewrite Z2Nat.id.
          unfold OS_RESOURCE_SEMAPHORE_PORT.
          symbolic_execution.
          unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
          unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
          intros ? Hs. unfold p_local in Hs. unfold CurLINV. sep auto. }
        partition_absrulestac absinfer_seq_end.
        eapply rete_rule'.
        { intros. symbolic_execution. }
        { intros. sep normal. sep eexists.
          sep autocancel.
          sep split; auto.
          { right. sep autocancel.
            sep normal. sep split.
            2: eauto. apply disj_split.
            left. sep normal. sep autocancel.
            sep split; auto.
            { left. unfold AOSKernelPortFreeList.
              sep normal. sep pauto. }
            { unfold OS_Port_V_direction.
              rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
              2: lia. rewrite Hdmdir.
              intro. inverts H0.
              rewrite Int.eq_true in Heqdir. tryfalse. } }
          reflexivity. } } }
    (* kportp <> Vnull *)
    destruct H as [kporta ?]; subst kportp.
    unfold kportf_sll; destruct kportfl.
    { cbn [kportf_sllseg]. naive pure intro. inverts H. }
    cbn [kportf_sllseg]. naive pure intro.
    rename v into newkp.
    rename v'2 into kevp; clear H2.

    unfold node.
    naive pure intro.
    destruct H2 as (Htmp & Hkpty).
    rename v'2 into kpb.
    inverts Htmp.
    apply struct_type_vallist_match_kport in Hkpty.
    simpljoin.
    inverts H8. inverts H. inverts H7.
    inverts H0. inverts H6. inverts H4.
    inverts H5. clear H9 H10 H11 H12 H13 H14.
    rename H15 into Hispkevp.
    (* If (OSKernelPortFreeList ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
    hoare forward.
    { naive pure intro. clear H.
      hoare forward.
      { pauto. } { pauto. }
      hoare forward.
      { unfold nat_of_Z, PORT_NUMS in *.
        apply Z2Nat.inj_lt.
        apply Int.unsigned_range.
        mauto.
        apply Intlt_true_is_Zlt in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. }
      { rewrite Hkplen.
        unfold nat_of_Z, PORT_NUMS in *.
        apply Z2Nat.inj_lt.
        apply Int.unsigned_range.
        mauto.
        apply Intlt_true_is_Zlt in Hportid.
        assert (Int.unsigned ($ 64) = 64) by mauto.
        lia. } }
    eapply disj_rule.
    2:{ naive pure intro. exfalso.
        destruct H; inverts H. }
    naive pure intro. clear H.
    
    (* If (dmPort ′ .. os_code_defs.direction ==ₑ ′ DESTINATION) *)
    assert ((length dmport = 18%nat)%nat).
    { clear - Htydmp.
      destruct dmport; simpl in Htydmp; tryfalse.
      do 18 (destruct Htydmp as [? Htydmp];
      destruct dmport; simpl in Htydmp; tryfalse).
      simpl. auto. }
    rename H into Hdmlen.

    assert (exists dir, nth_val' 4 dmport = Vint32 dir).
    { clear - Htydmp.
      destruct dmport; simpl in Htydmp; tryfalse.
      do 4 (destruct Htydmp as [? Htydmp];
      destruct dmport; simpl in Htydmp; tryfalse).
      simpl. destruct Htydmp.
      destruct v3; tryfalse. eauto. }
    destruct H as [dir Hdmdir].

    assert (exists evp, nth_val' 10 dmport = evp /\ isptr evp).
    { clear - Htydmp.
      destruct dmport; simpl in Htydmp; tryfalse.
      do 10 (destruct Htydmp as [? Htydmp];
      destruct dmport; simpl in Htydmp; tryfalse).
      simpl. destruct Htydmp.
      destruct v9; tryfalse; unfold isptr; eauto. }
    destruct H as [evp [Hdmevp Hevpisp]].

    assert (exists nxp, nth_val' 11 dmport = nxp /\ isptr nxp).
    { clear - Htydmp.
      destruct dmport; simpl in Htydmp; tryfalse.
      do 11 (destruct Htydmp as [? Htydmp];
      destruct dmport; simpl in Htydmp; tryfalse).
      simpl. destruct Htydmp.
      destruct v10; tryfalse; unfold isptr; eauto. }
    destruct H as [nxp [Hdmnxp Hnxpisp]].

    assert (exists coren, nth_val' 2 dmport = Vint32 coren /\ Int.unsigned coren <= 255).
    { clear - Htydmp.
      destruct dmport; simpl in Htydmp; tryfalse.
      do 2 (destruct Htydmp as [? Htydmp];
      destruct dmport; simpl in Htydmp; tryfalse).
      simpl. destruct Htydmp.
      destruct v1; tryfalse.
      exists i. split; pauto.
      destruct (Int.unsigned i <=? Byte.max_unsigned) eqn: ?; tryfalse.
      apply leb_bytemax_true_elim; auto. }
    destruct H as [coren [Hdmcrn Hcrnrg]].

    eapply seq_rule.
    { eapply ift_rule'.
      { intros ? Hs. sep_get_port_rv.
        eapply dmPort_direction_rv.
        { eauto. }
        { sep autocancel.
          apply Hs. }
        { rewrite Hdmdir. simpl. pauto. }
        { pauto. } }
      naive pure intro.
      rewrite Hdmdir in H. simpl in H.
      destruct (Int.eq dir ($ DESTINATION)) eqn: Heqdir.
      2:{ simpl in H. destruct H. tryfalse. }
      clear H.
      (* dmPort ′ .. OSEventPtrPort =ₑ OSCorePortPtrList ′;ₛ *)
      eapply seq_rule.
      { eapply port_memeber_asgn' with (n := 10%nat).
        { split.
          { intros Hs. sep autocancel. apply Hs. }
          sep pauto. }
        { symbolic_execution. destruct Hcisp.
          { subst. auto. }
          { destruct H0. subst; auto. } }
        { go. }
        { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
          { rewrite Hdmevp. eauto. } { lia. } }
        { go. } { go. } { go. } { go. }
        { eapply eq_vptr; eauto. }
        { simpl. destruct Hcisp.
          { subst; auto. }
          { destruct H; subst; auto. } }
        { sep auto. } }
      (* OSCorePortPtrList ′ =ₑ dmPort ′ *)
      hoare remember (@nil nat) pre.
      eapply backward_rule1.
      { instantiate (1:=H ** [| Int.eq dir ($ DESTINATION) = true |]).
        sep pauto. }
      subst H. hoare normal pre.
      hoare forward. }
    eapply disj_rule.
    { (* Int.eq dir ($ DESTINATION) = true *)
      naive pure intro. rename H into Heqdir.

      assert (nth_val' 11 ((update_nth_val 10 dmport cportp)) = nxp).
      { apply nth_val_nth_val'_some_eq.
        rewrite nth_upd_neqrev'; auto.
        rewrite <- Hdmnxp.
        apply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
      rename H into Hupnxp.

      (* dmPort ′ .. nextPort =ₑ OSDomainPortPtrList ′;ₛ *)
      eapply seq_rule.
      { eapply port_memeber_asgn' with (n := 11%nat).
        { split.
          { intros Hs. sep autocancel. apply Hs. }
          sep pauto. }
        { symbolic_execution. destruct Hdisp.
          { subst. auto. }
          { destruct H0. subst; auto. } }
        { go. }
        { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
          { rewrite Hupnxp. eauto. }
          { rewrite update_nth_val_len_eq. lia. } }
        { go. } { go. } { go. } { go. }
        { eapply eq_vptr; eauto. }
        { simpl. destruct Hdisp.
          { subst; auto. }
          { destruct H; subst; auto. } }
        { sep auto. } }
      (* OSDomainPortPtrList ′ =ₑ dmPort ′;ₛ *)
      hoare forward.

      assert (nth_val' 2 (update_nth_val 11 (update_nth_val 10 dmport cportp) dportp) = Vint32 coren).
      { apply nth_val_nth_val'_some_eq.
        do 2 (rewrite nth_upd_neqrev'; eauto).
        rewrite <- Hdmcrn.
        apply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
      rename H into Hupcoren.

      (* IF (port ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
      hoare forward.
      { naive pure intro. clear H.
        (* port ′ .. portID =ₑ portId ′;ₛ *)
        hoare forward.
        hoare forward.
        hoare forward.
        hoare forward.
        (* port ′ .. coreNum =ₑ dmPort ′ .. coreNum;ₛ *)
        eapply seq_rule.
        { hoare remember (1::nil)%nat pre.
          hoare lift 2%nat pre. subst H.
          eapply assign_rule_struct'.
          5:{ split.
              { intros Hs. sep autocancel. apply Hs. }
              { sep pauto. } }
          9:{ intros.
              eapply port_coreNum_rv_gen'.
              2:{ sep autocancel. apply H. }
              clear - Htydmp Hcisp Hdisp.
              destruct dmport; simpl in *; tryfalse.
              repeat (destruct Htydmp as [? Htydmp]; split; auto;
              destruct dmport; simpl in *; tryfalse).
              destruct Hcisp; [ |destruct H10]; subst; auto.
              destruct Hdisp; [ |destruct H11]; subst; auto. }
          11: sep auto.
          10:{ rewrite Hupcoren. instantiate (1:=4%nat).
              simpl. eauto. }
          6:{ simpl. eauto. }
          all: pauto; go. eapply eq_int; tauto. }
        hoare name lift Aop pre.
        hoare normal pre.
        (* port ′ .. channel =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ *)
        hoare forward.
        (* dmPort ′ .. OSEventType =ₑ ′ OS_EVENT_TYPE_PORT;ₛ *)
        eapply seq_rule.
        { eapply assign_rule_general.
          { intros ? Hs.
            eapply symbolic_lemmas.struct_offset_rv.
            { eapply symbolic_lemmas.addrof_deref_rv.
              symbolic_execution. }
            { unfold OS_Port; eauto. }
            { go. } { go. } }
          { unfold get_off_addr.
            assert (Int.zero = ($ 0)) by (clear; mauto).
            rewrite H; clear H. split.
            { intros Hs. sep autocancel. apply Hs. }
            { sep pauto. } }
          { symbolic_execution. }
          { eapply eq_int; tauto. }
          { sep auto. } }
        assert ((Int.modu ($ OS_EVENT_TYPE_PORT) ($ Byte.modulus)) =
                ($ OS_EVENT_TYPE_PORT)).
        { clear. unfold OS_EVENT_TYPE_PORT. mauto. }
        rewrite H. clear H.
        (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_NO_ERR *)
        eapply assign_rule_general.
        symbolic_execution.
        { split. intros Hs.
          sep autocancel. apply Hs. sep pauto. }
        symbolic_execution.
        now apply assign_type_match_true.
        sep auto. }
      { naive pure intro.
        instantiate (1:=Afalse).
        exfalso. destruct H; inverts H. }
      hoare forward.
      naive pure intro. clear H.
      (* CSLSEMREL (′ OS_RESOURCE_SEMAPHORE_PORT);ₛ *)
      eapply seq_rule.
      { eapply cslsemrel_rule.
        go.
        unfold OS_RESOURCE_SEMAPHORE_PORT.
        rewrite max_unsigned_val.
        rewrite Int.unsigned_repr. lia.
        rewrite max_unsigned_val. lia.
        intros.
        rewrite Int.unsigned_repr.
        rewrite Z2Nat.id.
        unfold OS_RESOURCE_SEMAPHORE_PORT.
        symbolic_execution.
        unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
        unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
        intros ? Hs. unfold p_local in Hs. unfold CurLINV. sep auto. }
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      { intros. sep normal. sep eexists.
        sep autocancel.
        sep split; auto.
        { right. sep autocancel.
          sep normal. sep split.
          2: eauto. apply disj_split.
          right. sep normal. sep autocancel.
          sep split; auto.
          { right. sep normal.
            (* instantiate (1:=portid). *)
            exists kevp kportfl 
            (Vint32 portid :: V$ DEFAULT_CHANELID
             :: Vptr dmportp :: Vnull :: Vint32 coren
             :: V$ DEFAULT_PORTSTATE :: Vnull :: nil) (kpb, $ 0).
            unfold AOSKernelPortFreeList. sep normal.
            sep autocancel.
            unfold get_off_addr.
            (* OS_EVENT_TYPE_PORT *)
            assert (Int.zero = $ 0) by (clear; mauto).
            rename H0 into Hzero.
            rewrite Hzero in H. sep autocancel.
            (* kportf_sll *)
            unfold kportf_sll. sep autocancel.
            (* kportNode_P *)
            sep split.
            2,3,4,5,6,7,8,9,10: go.
            2:{ unfold OS_Port_V_coreNum.
                rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; [ |lia].
                f_equal. auto. }
            sep name lift kportNode_P in H.
            lets Hs: kportNode_getsome_Vnull_frm Hcond H. clear H.
            sep destruct Hs. sep split in Hs. simpljoin1.
            rename x into kportpl1. rename x1 into kportpl2.
            rename x0 into kportl1. rename x2 into kportl2.
            rewrite <- H2 at 1.
            rewrite <- H4 at 1.
            rewrite update_nth_val_midlle.
            rewrite update_nth_vallist_middle.
            eapply kportNode_P_compose.
            { unfold vallist. lia. }
            { simpl; repeat (split; eauto).
              { clear - Hportid.
                rewrite byte_max_unsigned_val.
                unfold PORT_NUMS in Hportid.
                assert (Int.unsigned portid <=? 255 = true).
                2:{ rewrite H. auto. }
                apply Zle_is_le_bool.
                apply Intlt_true_is_Zlt in Hportid.
                assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
                lia. }
              { rewrite byte_max_unsigned_val.
                assert (Int.unsigned coren <=? 255 = true).
                2:{ rewrite H. auto. }
                apply Zle_is_le_bool. auto. } }
            { eauto. }
            sep autocancel.
            unfold Astruct, OS_K_Port in Hs.
            unfold Astruct' in *.
            unfold OS_K_Port_Seg_dls, firstn.
            rewrite <- Hzero in *.
            sep autocancel.
            sep cancel (kpb, Int.zero +ᵢ  $ Z.of_nat (typelen char_t)).
            sep cancel Aemp.
            unfold typelen, fst, snd in *.
            rewrite Int.add_zero_l in *.
            assert (((((($ Z.of_nat 1 +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
            $ Z.of_nat 4) +ᵢ  $ Z.of_nat 1) +ᵢ $ Z.of_nat 1) = ($ 12)) by (clear; mauto).
            rewrite H in Hs. apply Hs. auto. }
          { unfold OS_Port_V_direction.
            rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
            2: lia. rewrite Hdmdir. repeat f_equal.
            apply sem_lab.semacc_int_eq_true. auto. } }
        reflexivity. } }
    { (* Int.eq dir ($ DESTINATION) = false *)
      naive pure intro.
      rewrite Hdmdir in H. simpl in H.
      destruct (Int.eq dir ($ DESTINATION)) eqn: Heqdir.
      { simpl in H. exfalso. destruct H; inverts H. }
      clear H.

      (* dmPort ′ .. nextPort =ₑ OSDomainPortPtrList ′;ₛ *)
      eapply seq_rule.
      { eapply port_memeber_asgn' with (n := 11%nat).
        { split.
          { intros Hs. sep autocancel. apply Hs. }
          sep pauto. }
        { symbolic_execution. destruct Hdisp.
          { subst. auto. }
          { destruct H0. subst; auto. } }
        { go. }
        { rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
          { rewrite Hdmnxp. eauto. } { lia. } }
        { go. } { go. } { go. } { go. }
        { eapply eq_vptr; eauto. }
        { simpl. destruct Hdisp.
          { subst; auto. }
          { destruct H; subst; auto. } }
        { sep auto. } }
      (* OSDomainPortPtrList ′ =ₑ dmPort ′;ₛ *)
      hoare forward.

      assert (nth_val' 2 (update_nth_val 11 dmport dportp) = Vint32 coren).
      { apply nth_val_nth_val'_some_eq.
        rewrite nth_upd_neqrev'; eauto.
        rewrite <- Hdmcrn.
        apply symbolic_lemmas.nth_val_imp_nth_val'_2. lia. }
      rename H into Hupcoren.

      (* IF (port ′ !=ₑ 〈 OS_K_Port ∗ 〉 NULL) *)
      hoare forward.
      { naive pure intro. clear H.
        (* port ′ .. portID =ₑ portId ′;ₛ *)
        hoare forward.
        hoare forward.
        hoare forward.
        hoare forward.
        (* port ′ .. coreNum =ₑ dmPort ′ .. coreNum;ₛ *)
        eapply seq_rule.
        { hoare remember (1::nil)%nat pre.
          hoare lift 2%nat pre. subst H.
          eapply assign_rule_struct'.
          5:{ split.
              { intros Hs. sep autocancel. apply Hs. }
              { sep pauto. } }
          9:{ intros.
              eapply port_coreNum_rv_gen'.
              2:{ sep autocancel. apply H. }
              clear - Htydmp Hcisp Hdisp.
              destruct dmport; simpl in *; tryfalse.
              repeat (destruct Htydmp as [? Htydmp]; split; auto;
              destruct dmport; simpl in *; tryfalse).
              destruct Hdisp; [ |destruct H11]; subst; auto. }
          11: sep auto.
          10:{ rewrite Hupcoren. instantiate (1:=4%nat).
              simpl. eauto. }
          6:{ simpl. eauto. }
          all: pauto; go. eapply eq_int; tauto. }
        hoare name lift Aop pre.
        hoare normal pre.
        (* port ′ .. channel =ₑ 〈 OS_K_Port ∗ 〉 NULL;ₛ *)
        hoare forward.
        (* dmPort ′ .. OSEventType =ₑ ′ OS_EVENT_TYPE_PORT;ₛ *)
        eapply seq_rule.
        { eapply assign_rule_general.
          { intros ? Hs.
            eapply symbolic_lemmas.struct_offset_rv.
            { eapply symbolic_lemmas.addrof_deref_rv.
              symbolic_execution. }
            { unfold OS_Port; eauto. }
            { go. } { go. } }
          { unfold get_off_addr.
            assert (Int.zero = ($ 0)) by (clear; mauto).
            rewrite H; clear H. split.
            { intros Hs. sep autocancel. apply Hs. }
            { sep pauto. } }
          { symbolic_execution. }
          { eapply eq_int; tauto. }
          { sep auto. } }
        assert ((Int.modu ($ OS_EVENT_TYPE_PORT) ($ Byte.modulus)) =
                ($ OS_EVENT_TYPE_PORT)).
        { clear. unfold OS_EVENT_TYPE_PORT. mauto. }
        rewrite H. clear H.
        (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_NO_ERR *)
        eapply assign_rule_general.
        symbolic_execution.
        { split. intros Hs.
          sep autocancel. apply Hs. sep pauto. }
        symbolic_execution.
        now apply assign_type_match_true.
        sep auto. }
      { naive pure intro.
        instantiate (1:=Afalse).
        exfalso. destruct H; inverts H. }
      hoare forward.
      naive pure intro. clear H.

      (* CSLSEMREL (′ OS_RESOURCE_SEMAPHORE_PORT);ₛ *)
      eapply seq_rule.
      { eapply cslsemrel_rule.
        go.
        unfold OS_RESOURCE_SEMAPHORE_PORT.
        rewrite max_unsigned_val.
        rewrite Int.unsigned_repr. lia.
        rewrite max_unsigned_val. lia.
        intros.
        rewrite Int.unsigned_repr.
        rewrite Z2Nat.id.
        unfold OS_RESOURCE_SEMAPHORE_PORT.
        symbolic_execution.
        unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
        unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
        intros ? Hs. unfold p_local in Hs. unfold CurLINV. sep auto. }
      partition_absrulestac absinfer_seq_end.
      eapply rete_rule'.
      { intros. symbolic_execution. }
      { intros. sep normal. sep eexists.
        sep autocancel.
        sep split; auto.
        { right. sep autocancel.
          sep normal. sep split.
          2: eauto. apply disj_split.
          left. sep normal. sep autocancel.
          sep split; auto.
          { right. sep normal.
            (* instantiate (1:=portid). *)
            exists kevp kportfl 
            (Vint32 portid :: V$ DEFAULT_CHANELID
             :: Vptr dmportp :: Vnull :: Vint32 coren
             :: V$ DEFAULT_PORTSTATE :: Vnull :: nil) (kpb, $ 0).
            unfold AOSKernelPortFreeList. sep normal.
            sep autocancel.
            unfold get_off_addr.
            (* OS_EVENT_TYPE_PORT *)
            assert (Int.zero = $ 0) by (clear; mauto).
            rename H0 into Hzero.
            rewrite Hzero in H. sep autocancel.
            (* kportf_sll *)
            unfold kportf_sll. sep autocancel.
            (* kportNode_P *)
            sep split.
            2,3,4,5,6,7,8,9,10: go.
            2:{ unfold OS_Port_V_coreNum.
                rewrite symbolic_lemmas.nth_val_imp_nth_val'_2; [ |lia].
                f_equal. auto. }
            sep name lift kportNode_P in H.
            lets Hs: kportNode_getsome_Vnull_frm Hcond H. clear H.
            sep destruct Hs. sep split in Hs. simpljoin1.
            rename x into kportpl1. rename x1 into kportpl2.
            rename x0 into kportl1. rename x2 into kportl2.
            rewrite <- H2 at 1.
            rewrite <- H4 at 1.
            rewrite update_nth_val_midlle.
            rewrite update_nth_vallist_middle.
            eapply kportNode_P_compose.
            { unfold vallist. lia. }
            { simpl; repeat (split; eauto).
              { clear - Hportid.
                rewrite byte_max_unsigned_val.
                unfold PORT_NUMS in Hportid.
                assert (Int.unsigned portid <=? 255 = true).
                2:{ rewrite H. auto. }
                apply Zle_is_le_bool.
                apply Intlt_true_is_Zlt in Hportid.
                assert (Int.unsigned ($ 64) = 64) by (clear; mauto).
                lia. }
              { rewrite byte_max_unsigned_val.
                assert (Int.unsigned coren <=? 255 = true).
                2:{ rewrite H. auto. }
                apply Zle_is_le_bool. auto. } }
            { eauto. }
            sep autocancel.
            unfold Astruct, OS_K_Port in Hs.
            unfold Astruct' in *.
            unfold OS_K_Port_Seg_dls, firstn.
            rewrite <- Hzero in *.
            sep autocancel.
            sep cancel (kpb, Int.zero +ᵢ  $ Z.of_nat (typelen char_t)).
            sep cancel Aemp.
            unfold typelen, fst, snd in *.
            rewrite Int.add_zero_l in *.
            assert (((((($ Z.of_nat 1 +ᵢ  $ Z.of_nat 1) +ᵢ  $ Z.of_nat 4) +ᵢ
            $ Z.of_nat 4) +ᵢ  $ Z.of_nat 1) +ᵢ $ Z.of_nat 1) = ($ 12)) by (clear; mauto).
            rewrite H in Hs. apply Hs. auto. }
          { unfold OS_Port_V_direction.
            rewrite symbolic_lemmas.nth_val_imp_nth_val'_2.
            2: lia. rewrite Hdmdir.
            intro. inverts H0.
            rewrite Int.eq_true in Heqdir. tryfalse. } }
        reflexivity. } } }
  hoare forward. naive pure intro.
  rename H into Hcond_pid.
  (* CSLSEMREL (′ OS_RESOURCE_SEMAPHORE_PORT);ₛ *)
  eapply seq_rule.
  { eapply cslsemrel_rule.
    go.
    unfold OS_RESOURCE_SEMAPHORE_PORT.
    rewrite max_unsigned_val.
    rewrite Int.unsigned_repr. lia.
    rewrite max_unsigned_val. lia.
    intros.
    rewrite Int.unsigned_repr.
    rewrite Z2Nat.id.
    unfold OS_RESOURCE_SEMAPHORE_PORT.
    symbolic_execution.
    unfold OS_RESOURCE_SEMAPHORE_PORT. lia.
    unfold OS_RESOURCE_SEMAPHORE_PORT. rewrite max_unsigned_val. lia.
    intros ? Hs. unfold p_local in Hs. unfold CurLINV. sep auto. }
  partition_absrulestac absinfer_seq_end.
  (* ∗ err ′ =ₑ 〈 char_t 〉 ′ OS_PORT_ID_EXIST;ₛ *)
  eapply seq_rule.
  { eapply assign_rule_general.
    symbolic_execution.
    { split. intros Hs.
      sep autocancel. apply Hs. sep pauto. }
    symbolic_execution.
    now apply assign_type_match_true.
    sep auto. }
  eapply rete_rule'.
  { intros. symbolic_execution. }
  { intros. sep normal. sep eexists.
    sep autocancel.
    sep split; auto.
    { left. sep pauto. do 3 right. split; eauto.
      instantiate (1:=portid).
      assert (exists x, nth_val' (Z.to_nat (Int.unsigned portid)) kportpl = x /\ 
                        true = rule_type_val_match OS_K_Port ∗ x).
      { eapply nthval'_has_value_ptr; eauto.
        clear - Hportid. apply Intlt_true_is_Zlt in Hportid.
        unfold nat_of_Z. apply symbolic_lemmas.ge0_z_nat_le.
        { apply Int.unsigned_range. }
        rewrite Z2Nat.id. 2: clear; mauto.
        assert (Int.unsigned ($ PORT_NUMS) = PORT_NUMS).
        { clear. unfold PORT_NUMS. mauto. } lia. }
      destruct H0 as [p [? ?]].
      unfold rule_type_val_match in H2.
      destruct p; tryfalse.
      { rewrite H0 in *. exfalso.
        clear - Hcond_pid. simpl in Hcond_pid.
        destruct Hcond_pid; tryfalse. }
      exists a. apply nth_val_nth_error.
      rewrite <- H0.
      apply symbolic_lemmas.nth_val_imp_nth_val'_2.
      rewrite Hkplen.
      clear - Hportid. apply Intlt_true_is_Zlt in Hportid.
      unfold nat_of_Z. apply symbolic_lemmas.ge0_z_nat_le.
      { apply Int.unsigned_range. }
      rewrite Z2Nat.id. 2: clear; mauto.
      assert (Int.unsigned ($ PORT_NUMS) = PORT_NUMS).
      { clear. unfold PORT_NUMS. mauto. } lia. }
    reflexivity. }
Qed.