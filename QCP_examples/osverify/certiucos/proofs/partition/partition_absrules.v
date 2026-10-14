Require Import ucos_include.
Require Import Lia.
Require Import aux_pureLib.

Lemma absinfer_choice1_cons:
forall (p : asrt) (s1 s2 s3: spec_code) sc,
  can_change_aop p ->
  sc ⊢  <|| (s1 ?? s2);;s3 ||>  ** p ⇒  <|| s1;;s3 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; auto.
  eapply absinfer_choice1; auto.
Qed.

Lemma absinfer_choice2_cons:
forall (p : asrt) (s1 s2 s3: spec_code) sc,
  can_change_aop p ->
  sc ⊢  <|| (s1 ?? s2);;s3 ||>  ** p ⇒  <|| s2;;s3 ||>  ** p.
Proof.
  intros.
  eapply absinfer_seq; auto.
  eapply absinfer_choice2; auto.
Qed.

Lemma absinfer_choice1':
    forall p s1 s2 sc,
      can_change_aop p ->
      absinfer sc (<||s1 ?? s2 ||> ** p) (<||s1||> ** p).
Proof.
  intros.
  eapply absinfer_choice1; auto.
Qed.
               
Lemma absinfer_choice2':
    forall p s1 s2 sc,
      can_change_aop p ->
      absinfer sc (<||s1 ?? s2 ||> ** p ) (<||s2||> ** p).
Proof.
  intros.
  eapply absinfer_choice2; auto.
Qed.

Lemma port_indomainport_null_abt:
 forall sch s P,
   can_change_aop P ->
   sch ⊢  <||  ASSERT port_indomainport Vnull ;; s ||> ** P
         ⇒ <|| ABORT ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold port_indomainport.
  auto.
  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma port_indomainport_none_abt:
 forall sch s P dprtls p_v,
   get dprtls p_v = None ->
   can_change_aop P ->
   sch ⊢  <||  ASSERT port_indomainport (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
         ⇒ <|| ABORT ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold port_indomainport.
  unfold not;intros. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H1.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  rewrite H2 in H1. inverts H1.
  unfold absdomainport.B, Port, port_coreNum in H.
  rewrite H3 in H. inversion H. 

  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma port_indomainport_none_abt':
  forall sch s P dprtls p_v p p0 p1 d p2 p3 p4 p5,
    get dprtls p_v = Some (p, p0, p1, d, p2, p3, p4, p5) ->
    p <> Z.to_nat DNUM ->
    can_change_aop P ->
    sch ⊢  <||  ASSERT port_indomainport (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
          ⇒ <|| ABORT ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold port_indomainport.
  unfold not;intros. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H2.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  rewrite H3 in H2. inverts H2.
  unfold absdomainport.B, Port, port_coreNum in H.
  rewrite H4 in H. inversion H. lia. 

  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma valid_port_none_abt:
 forall sch s P dprtls p_v,
   get dprtls p_v = None ->
   can_change_aop P ->
   sch ⊢  <||  ASSERT valid_port (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
         ⇒ <|| ABORT ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold valid_port.
  unfold not;intros.
  destruct H2; [congruence| ]. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H1.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  rewrite H3 in H1. inverts H1.
  setoid_rewrite H in H2. discriminate. 
  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma valid_port_none_abt':
  forall sch s P dprtls p_v p p0 p1 d p2 p3 p4 p5,
    get dprtls p_v = Some (p, p0, p1, d, p2, p3, p4, p5) ->
    p <> Z.to_nat DNUM ->
    can_change_aop P ->
    sch ⊢  <||  ASSERT valid_port (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
          ⇒ <|| ABORT ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold valid_port.
  unfold not;intros. destruct H3; [congruence| ]. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H2.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  rewrite H4 in H2. inverts H2.
  rewrite H in H3. inverts H3. lia. 
  eapply absinfer_seq_abt;  [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma port_indomainport_cont:
 forall sch s P dprtls p_v p0 p1 d p2 p3 p4 p5,
   get dprtls p_v = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) ->
   can_change_aop P ->
   sch ⊢  <||  ASSERT port_indomainport (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
         ⇒ <|| s ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None ) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold port_indomainport.
  unfold not;intros. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H1.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  (* destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?]. *)
  do 8 eexists.
  split;eauto.

  eapply absinfer_seq_end;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma valid_port_cont:
 forall sch s P dprtls p_v p0 p1 d p2 p3 p4 p5,
   get dprtls p_v = Some (Z.to_nat DNUM, p0, p1, d, p2, p3, p4, p5) ->
   can_change_aop P ->
   sch ⊢  <||  ASSERT valid_port (Vptr p_v) ;; s ||> ** Hdomainportl dprtls ** P
         ⇒ <|| s ||>  ** Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None ) (q:= Hdomainportl dprtls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  unfold valid_port.
  unfold not;intros. right. 
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  simpl_sat H1.
  simpljoin1.
  cbn in *. simpljoin1.
  assert (get o osdomainportid = Some (osdomainport dprtls)) by (eapply join_sig_get;eauto).
  (* destruct b as [[[[[[[? ?] ?] ?] ?] ?] ?] ?]. *)
  do 8 eexists.
  split;eauto.
  eapply absinfer_seq_end;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.


Lemma port_unmapped:
  forall sch s P tcbls tid dprtls p_v p st msg sus pcn pd pid pdir pst pintick poutick pt,
    get tcbls tid = Some (p, st, msg, sus) ->
    get dprtls p_v = Some (pcn, pd, pid, pdir, pst, pintick, poutick, pt) ->
    Int.eq (p >>ᵢ $ 3) ($ Z.of_nat pd) = false ->
    can_change_aop P ->
    sch ⊢  <||   err_unmapped (|Vptr p_v :: nil|) ?? s ||> ** 
    HCurTCB tid ** HTCBList tcbls **
    Hdomainportl dprtls  ** P
          ⇒ <|| END (Some (Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED))) ||>  ** HCurTCB tid **
          HTCBList tcbls **
          Hdomainportl dprtls  ** P.
Proof.
  intros.
  infer_solver 0%nat.
Qed.

Lemma portpend_err_dire_end:
  forall sch s1 s P dprtls p_v tm_v msg_v pcn pd pid pst pintick poutick pt,
    get dprtls p_v = Some (pcn, pd, pid, SourceP, pst, pintick, poutick, pt) ->
    can_change_aop P ->
    sch ⊢  <||  s1 ?? portpend_err_dire (|Vptr p_v :: Vint32 tm_v :: msg_v :: nil|) ?? s ||> ** 
    Hdomainportl dprtls  ** P
          ⇒ <|| END (Some (Vint32 (Int.repr OS_PORT_ERR_DIRECTION_TYPE))) ||>  **
          Hdomainportl dprtls  ** P.
Proof.
  infer_solver 1%nat.
Qed.
  
Lemma portpend_err_type_end:
  forall sch s1 s2 s P dprtls p_v tm_v msg_v pcn pd pid nextdst pst pintick poutick o,
    get dprtls p_v = Some (pcn, pd, pid, DestinationP nextdst,  pst, pintick, poutick, SamplePort o) ->
    can_change_aop P ->
    sch ⊢  <||  s1 ?? s2 ?? portpend_err_type  (|Vptr p_v :: Vint32 tm_v :: msg_v :: nil|) ?? s ||> ** 
    Hdomainportl dprtls  ** P
          ⇒ <|| END (Some (Vint32 (Int.repr OS_PORT_ERR_TYPE))) ||>  **
          Hdomainportl dprtls  ** P.
Proof.
  infer_solver 2%nat.
Qed.

Lemma err_msgnull_end:
  forall sch s P z,
    can_change_aop P ->
    sch ⊢  <||   err_msgnull z (|Vnull :: nil|)  ?? s ||>  ** P
          ⇒ <|| END (Some (Vint32 (Int.repr z))) ||> ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma portpend_err_nochannel_end:
  forall sch s1 s2 s3 s4 s P dprtls kportls p_v kp_v pcn pd pid pdir pst pintick poutick pt kpst,
    get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, pt) ->
    get kportls kp_v = Some (pid, Some p_v, None, pcn, kpst)  ->
    can_change_aop P ->
    sch ⊢  <||  s1 ?? s2 ?? s3 ?? s4 ?? err_nochannel (|Vptr p_v :: nil|) ?? s ||> ** 
          Hdomainportl dprtls  ** Hkernelport kportls ** P
          ⇒ <|| END (Some (Vint32 (Int.repr OS_ERR_PORT_NO_CHANNEL))) ||>  **
          Hdomainportl dprtls  ** Hkernelport kportls ** P.
Proof.
  infer_solver 4%nat.
Qed.

(* Definition nodup_dport (kportls :KernelPMod.map) :=
  forall kpv1 kpv2, kpv1 <> kpv2  ->
    match (get kportls kpv1), (get kportls kpv2) with 
    | (Some (_ , Some pv1, _, _, _)), Some (_ , Some pv2, _, _, _) => pv1 <> pv2
    | _,_=>  True
    end. *)

Lemma corecommu_sem_abt :
  forall sch s P dprtls kportls chanls p_v v kp_v pcn pd pid pdir pst pintick poutick pt channaddr kpst
    cid cdn cdstkp csem,
    v <> Vint32 ($ Z.of_nat csem) ->
    get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, pt) ->
    get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
    get chanls channaddr = Some (cid, cdn, cdstkp, OutcoreC csem) ->
    nodup_dport kportls ->
    can_change_aop P ->
    sch ⊢  <||   ASSERT corecommu_ (Vptr p_v) v ;; s ||> ** 
          Hdomainportl dprtls  ** Hkernelport kportls ** Hchannell chanls ** P
          ⇒ <|| ABORT ||>  **
          Hdomainportl dprtls  ** Hkernelport kportls ** Hchannell chanls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dprtls ** Hkernelport kportls ** Hchannell chanls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  unfold corecommu_, not.
  cbn;intros.
  assert (get o osdomainportid = Some (osdomainport dprtls)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportls)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanls)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpljoin1.
  rewrite H11 in *. rewrite H13 in *. rewrite H15 in *.
  inverts H6. inverts H7. inverts H8. inverts H9.
  rewrite H12 in *. inverts H0. 
  assert (x10 <> kp_v \/ x10 = kp_v)  as [ | ] by tauto.
  { eapply H3 in H0. rewrite H14, H1 in *. tryfalse. }
  subst x10.
  rewrite H14 in *. inverts H1.
  rewrite H16 in *. inverts H2.
  tryfalse.
  eapply absinfer_seq_abt;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma corecommu_sem_cont :
  forall sch s P dprtls kportls chanls p_v kp_v pcn pd pid pdir pst pintick poutick pt channaddr kpst
    cid cdn cdstkp csem,
    get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, pt) ->
    get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
    get chanls channaddr = Some (cid, cdn, cdstkp, OutcoreC csem) ->
    can_change_aop P ->
    sch ⊢  <||   ASSERT corecommu_ (Vptr p_v) (Vint32 ($ Z.of_nat csem)) ;; s ||> ** 
          Hdomainportl dprtls  ** Hkernelport kportls ** Hchannell chanls ** P
          ⇒ <|| s ||>  **
          Hdomainportl dprtls  ** Hkernelport kportls ** Hchannell chanls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None ) (q:= Hdomainportl dprtls ** Hkernelport kportls ** Hchannell chanls ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?]. 
  unfold corecommu_.
  assert (get o osdomainportid = Some (osdomainport dprtls)).
  { sep remember (1::nil)%nat in H3. simpl_sat H3.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportls)).
  { sep remember (2::nil)%nat in H3. simpl_sat H3.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanls)).
  { sep remember (3::nil)%nat in H3. simpl_sat H3.
    simpljoin1. eapply join_sig_get;eauto.  }
  do 19 eexists.
  splits;eauto.
  eapply absinfer_seq_end;[can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma samplepost_dstplength_coresem_abt:
  forall sch s P v v0 m dpl pcn pd pid pst pin pout pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  length vsdstcl <> length cdstkp ->
  sch ⊢ <|| ASSERT samplepost_dstplength_coresem
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold samplepost_dstplength_coresem.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  rewrite H6 in H11; inverts H11.
  rewrite H7 in H13; inverts H13.
  rewrite H8 in H15; inverts H15.
  inverts H9.
  rewrite H0 in H12; inverts H12.
  assert (x12 <> kpptr \/ x12 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H14, H1 in *; tryfalse.
  subst; rewrite H1 in H14; inverts H14.
  destruct H4.
  {
    destruct H16; simpljoin1;
    unfold channel_dstport in H2; rewrite H2 in H11;
    inverts H11; auto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma samplepost_dstplength_coresem_abt':
  forall sch s P v v0 m dpl pcn pd pid pst pin pout pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  ~( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\ 
        Forall (fun (v:val) => v = Vnull) vsdstcl /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC) ) ->
  sch ⊢ <|| ASSERT samplepost_dstplength_coresem
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold samplepost_dstplength_coresem.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  rewrite H6 in H11; inverts H11.
  rewrite H7 in H13; inverts H13.
  rewrite H8 in H15; inverts H15.
  inverts H9.
  rewrite H0 in H12; inverts H12.
  assert (x12 <> kpptr \/ x12 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H14, H1 in *; tryfalse.
  subst; rewrite H1 in H14; inverts H14.
  destruct H4.
  {
    destruct H16; simpljoin1;
    unfold channel_dstport in H2; rewrite H2 in H11;
    inverts H11; [left; eexists|right]; splits; eauto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma samplepost_dstplength_coresem_abt'':
  forall sch s P v v0 m dpl pcn pd pid pst pin pout pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  v0 <> Vint32 (Int.repr (Z.of_nat (length cdstkp))) ->
  sch ⊢ <|| ASSERT samplepost_dstplength_coresem
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold samplepost_dstplength_coresem.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  rewrite H6 in H11; inverts H11.
  rewrite H7 in H13; inverts H13.
  rewrite H8 in H15; inverts H15.
  inverts H9.
  rewrite H0 in H12; inverts H12.
  assert (x12 <> kpptr \/ x12 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H14, H1 in *; tryfalse.
  subst; rewrite H1 in H14; inverts H14.
  destruct H4.
  {
    destruct H16; simpljoin1;
    unfold channel_dstport in H2; rewrite H2 in H11;
    inverts H11; auto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma samplepost_dstplength_coresem_abt''':
  forall sch s P v v0 m dpl pcn pd pid pst pin pout pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  ~( forall n, (n < (length cdstkp))%nat -> 
    exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
    exists dstkpaddr dstkpst nextdst,
    nth_error cdstkp n = Some dstkpaddr /\ 
    get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
    get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
    ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ) ->
  sch ⊢ <|| ASSERT samplepost_dstplength_coresem
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold samplepost_dstplength_coresem.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  rewrite H6 in H11; inverts H11.
  rewrite H7 in H13; inverts H13.
  rewrite H8 in H15; inverts H15.
  inverts H9.
  rewrite H0 in H12; inverts H12.
  assert (x12 <> kpptr \/ x12 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H14, H1 in *; tryfalse.
  subst; rewrite H1 in H14; inverts H14.
  destruct H4.
  {
    destruct H16; simpljoin1;
    unfold channel_dstport in H2; rewrite H2 in H11;
    inverts H11; auto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma samplepost_dstplength_coresem_cont:
  forall sch s P v m dpl pcn pd pid pst pin pout pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  (length vsdstcl = length cdstkp)%nat ->
  ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\ 
        Forall (fun (v:val) => v = Vnull) vsdstcl /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC) ) ->
  ( forall n, (n < (length cdstkp))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error cdstkp n = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, SamplePort dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ) ->
  sch ⊢ <|| ASSERT samplepost_dstplength_coresem
        ( Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold samplepost_dstplength_coresem.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H7. simpl_sat H7.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H7. simpl_sat H7.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H7. simpl_sat H7.
    simpljoin1. eapply join_sig_get;eauto.  }
  do 20 eexists; splits; eauto.
  eapply absinfer_seq_end; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma qportpost_port_kport_channel_map_abt:
  forall sch s P v v0 m dpl pcn pd pid pst pin pout sz pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout,  QueuePort sz pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  ~( ((exists csemid, vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\ 
  get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid) ) \/ 
vsem = Vnull /\  get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ) ->
  sch ⊢ <|| ASSERT qportpost_port_kport_channel_map
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold qportpost_port_kport_channel_map.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1. inverts H9.
  rewrite H6 in H10; inverts H10.
  rewrite H7 in H12; inverts H12.
  rewrite H8 in H14; inverts H14.
  rewrite H0 in H11; inverts H11.
  assert (x13 <> kpptr \/ x13 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H13, H1 in *; tryfalse.
  subst; rewrite H1 in H13; inverts H13.
  destruct H4.
  {
    destruct H15; simpljoin1.
    setoid_rewrite H2 in H9. inverts H9.
    left. eexists; eauto. right.
    setoid_rewrite H2 in H9. inverts H9. tauto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma qportpost_port_kport_channel_map_abt':
  forall sch s P v v0 m dpl pcn pd pid pst pin pout sz pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  v0 <> Vint32 (Int.repr (Z.of_nat (length cdstkp))) ->
  sch ⊢ <|| ASSERT qportpost_port_kport_channel_map
        ( Vptr v :: Vptr m :: v0 :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold qportpost_port_kport_channel_map.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  rewrite H6 in H10; inverts H10.
  rewrite H7 in H12; inverts H12.
  rewrite H8 in H14; inverts H14.
  inverts H9.
  rewrite H0 in H11; inverts H11.
  assert (x13 <> kpptr \/ x13 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H13, H1 in *; tryfalse.
  subst; rewrite H1 in H13; inverts H13.
  destruct H4.
  {
    destruct H15; simpljoin1.
    rewrite H2 in H9; inverts H9. reflexivity.
    unfold channel_dstport in H2. rewrite H2 in H9.
    inverts H9; auto.
  }
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma qportpost_port_kport_channel_map_cont:
  forall sch s P v m dpl pcn pd pid pst pin pout sz pm kportl kpptr kpst channaddr chanl vsem vsdstcl cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  ( ((exists csemid, vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\ 
  get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
  vsem = Vnull /\  get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ) ->
  sch ⊢ <|| ASSERT qportpost_port_kport_channel_map
        ( Vptr v :: Vptr m :: Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold qportpost_port_kport_channel_map.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  do 21 eexists; splits; eauto.
  eapply absinfer_seq_end; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma qportpost_msg_in_heapl_abt: forall sch s P v vl m cHeapl cHeape cHeapt dportls kportls chanls,
  can_change_aop P ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg)/\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| ASSERT qportpost_msg_in_heapl (v :: Vptr m :: vl);; s ||>  **
  Hdomainportl dportls **
  Hkernelport kportls **
  Hchannell chanls ** 
  HCoreHeap cHeapl cHeape cHeapt ** P 
  ⇒
  <|| ABORT ||>  **
  Hdomainportl dportls **
  Hkernelport kportls **
  Hchannell chanls **
  HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (s1' := ABORT ) (q:=  Hdomainportl dportls ** Hkernelport kportls ** Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto| ].
    intros. unfold not. intros. 
    unfold qportpost_msg_in_heapl in H2. simpljoin.
    inverts H2. apply H0.
    do 2 eexists. splits;eauto.
    assert (s0 |= HCoreHeap cHeapl cHeape cHeapt ** Hdomainportl dportls **
    Hkernelport kportls ** Hchannell chanls **P) by sep auto.
    destruct s0. destruct r.
    apply absdata_elim in H2.
    setoid_rewrite H2 in H3. inverts H3.
    eauto.
  }
  apply absinfer_seq_abt; can_change_aop_solver.
  auto.
Qed.

Lemma qportpost_msg_in_heapl_abt': forall sch s P v vl m cHeapl cHeape cHeapt dportls,
  can_change_aop P ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg)/\ (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| ASSERT qportpost_msg_in_heapl (v :: Vptr m :: vl);; s ||>  **
  Hdomainportl dportls **
  HCoreHeap cHeapl cHeape cHeapt ** P 
  ⇒
  <|| ABORT ||>  **
  Hdomainportl dportls **
  HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (s1' := ABORT ) (q:=  Hdomainportl dportls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto| ].
    intros. unfold not. intros. 
    unfold qportpost_msg_in_heapl in H2. simpljoin.
    inverts H2. apply H0.
    do 2 eexists. splits;eauto.
    assert (s0 |= HCoreHeap cHeapl cHeape cHeapt ** Hdomainportl dportls **P) by sep auto.
    destruct s0. destruct r.
    apply absdata_elim in H2.
    setoid_rewrite H2 in H3. inverts H3.
    eauto.
  }
  apply absinfer_seq_abt; can_change_aop_solver.
  auto.
Qed.

Lemma qportpost_msg_in_heapl_cont: forall sch msg mlen s P v m vl  cHeapl cHeape cHeapt dportls kportls chanls,
  can_change_aop P ->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z  ->
  sch
  ⊢ <|| ASSERT qportpost_msg_in_heapl (v :: Vptr m :: vl);; s ||>  **
    Hdomainportl dportls **
    Hkernelport kportls **
    Hchannell chanls ** 
    HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl dportls **
    Hkernelport kportls **
    Hchannell chanls **
    HCoreHeap cHeapl cHeape cHeapt ** P. 
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (q:=  Hdomainportl dportls ** Hkernelport kportls ** Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto| ].
    intros.
    assert (s0 |= HCoreHeap cHeapl cHeape cHeapt ** Hdomainportl dportls **
    Hkernelport kportls ** Hchannell chanls **P) by sep auto.
    destruct s0. destruct r.
    apply absdata_elim in H3.
    unfold qportpost_msg_in_heapl. do 3 eexists. splits; eauto.
    do 3 eexists. splits; eauto.
  }
  apply absinfer_seq_end; can_change_aop_solver. auto.
Qed.

Lemma qportpost_msg_in_heapl_cont': forall sch msg mlen s P v m vl  cHeapl cHeape cHeapt dportls,
  can_change_aop P ->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z  ->
  sch
  ⊢ <|| ASSERT qportpost_msg_in_heapl (v :: Vptr m :: vl);; s ||>  **
    Hdomainportl dportls **
    HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl dportls **
    HCoreHeap cHeapl cHeape cHeapt ** P. 
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (q:=  Hdomainportl dportls **  HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto| ].
    intros.
    assert (s0 |= HCoreHeap cHeapl cHeape cHeapt ** Hdomainportl dportls **P) by sep auto.
    destruct s0. destruct r.
    apply absdata_elim in H3.
    unfold qportpost_msg_in_heapl. do 3 eexists. splits; eauto.
    do 3 eexists. splits; eauto.
  }
  apply absinfer_seq_end; can_change_aop_solver. auto.
Qed.

Lemma qportpost_store_one_OutCore_cont: forall sch sz pm msg s P v m csemid vsdstcl dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cHeapl cHeape cHeapt mlen,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, nil, OutcoreC csemid)->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ->
  sch
  ⊢ <|| qportpost_store_one 
      (|Vptr v :: Vptr m :: 
        V$ 0 :: 
        V$ Z.of_nat csemid :: vsdstcl|);; s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl (set dpl v (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ (msg :: nil)))) ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= Hdomainportl
    (set dpl v
       (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ msg :: nil))) **
  Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dpl v
    (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ msg :: nil))))).
    unfold qportpost_store_one.
    do 17 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    do 3 eexists; splits; eauto.
    { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    do 2 eexists; splits; eauto.
    absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.


Lemma qportpost_store_one_InCore_cont: forall sch sz pm msg s P v vsdstcl m dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cHeapl cHeape cHeapt mlen,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, nil, IncoreC)->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ->
  sch
  ⊢ <|| qportpost_store_one 
      (|Vptr v :: Vptr m :: 
        V$ 0 :: 
        Vnull :: vsdstcl|);; s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl (set dpl v (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ (msg :: nil)))) ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= Hdomainportl
    (set dpl v
       (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ msg :: nil))) **
  Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dpl v
    (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz (pm ++ msg :: nil))))).
    unfold qportpost_store_one.
    do 17 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    do 3 eexists; splits; eauto.
    { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
    do 2 eexists; splits; eauto.
    absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.


Lemma qportpost_dstplength_coresem_Outcore_abt:
  forall sch s P v  m dpl pcn pd pid pst pin pout sz pm kportl kpptr kpst channaddr chanl vsdstcl vlen vsem cid cdn cdstkp ct,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, ct) ->
  nodup_dport kportl ->
  ~ (length vsdstcl = length cdstkp /\ Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
  ( forall n, (n < (length cdstkp))%nat -> 
    exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstsz dstpm,
    exists dstkpaddr dstkpst nextdst,
    nth_error cdstkp n = Some dstkpaddr /\ 
    get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
    get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
    ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ) ) ->
  sch ⊢ <|| ASSERT qportpost_dstplength_coresem_Outcore
        ( Vptr v :: Vptr m :: vlen :: vsem :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| ABORT ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_abt;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold qportpost_dstplength_coresem_Outcore.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  simpl; intro; simpljoin1.
  symmetry in H9. inverts H9.
  rewrite H6 in H10; symmetry in H10; inverts H10.
  rewrite H0 in H11; symmetry in H11. inverts H11.
  rewrite H7 in H12; symmetry in H12; inverts H12.
  rewrite H8 in H14; symmetry in H14; inverts H14.
  assert (x15 <> kpptr \/ x15 = kpptr) as [ | ] by tauto.
  eapply H3 in H9. rewrite H13, H1 in *; tryfalse.
  subst.
  rewrite H1 in H13; symmetry in H13; inverts H13.
  rewrite H2 in H15; symmetry in H15; inverts H15.
  apply H4; splits; eauto; try tauto.
  eapply absinfer_seq_abt; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.


Lemma qportpost_dstplength_coresem_Outcore_cont:
  forall sch s P v m dpl pcn pd pid pst pin pout sz pm kportl kpptr kpst channaddr chanl vlen vsem csemid vsdstcl cid cdn cdstkp,
  can_change_aop P ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, QueuePort sz pm) ->
  get kportl kpptr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid) ->
  nodup_dport kportl ->
  (
    length vsdstcl = length cdstkp /\
    Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
    ( forall n, (n < (length cdstkp))%nat -> 
        exists dstpaddr dstpcn dstpd dstpid dstpst dstpin dstpout dstsz dstpm,
        exists dstkpaddr dstkpst nextdst,
        nth_error cdstkp n = Some dstkpaddr /\ 
        get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) /\ 
        get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) /\
        ((Z.of_nat dstpcn) <> DNUM -> nth_error vsdstcl n = Some (Vint32 (Int.repr (Z.of_nat dstpcn)))))
  )%nat ->

  sch ⊢ <|| ASSERT qportpost_dstplength_coresem_Outcore
        ( Vptr v :: Vptr m :: vlen :: vsem  :: vsdstcl);; s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P
      ⇒ <|| s ||> **
        Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** P);[can_change_aop_solver.. ].
  eapply absinfer_assert_cont;[can_change_aop_solver | can_change_aop_solver | auto | ].
  intros.
  destruct s0 as [[[[[[[? ? ] ? ] ? ] ? ] ? ] ?] ?].
  unfold qportpost_dstplength_coresem_Outcore.
  assert (get o osdomainportid = Some (osdomainport dpl)).
  { sep remember (1::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oskportid = Some (oskport kportl)).
  { sep remember (2::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  assert (get o oschannelid = Some (oschannel chanl)).
  { sep remember (3::nil)%nat in H5. simpl_sat H5.
    simpljoin1. eapply join_sig_get;eauto.  }
  do 23 eexists; splits; eauto; try tauto.
  eapply absinfer_seq_end; [can_change_aop_solver | can_change_aop_solver | auto].
Qed.

Lemma qportpost_send_one_OutCore_cont: forall sch  msg s P v n m csemid vsdstcl dpl pcn pid kportl kpaddr kpst channaddr chanl cid cdn cHeapl cHeape cHeapt mlen
  dstkpaddr dstpid dstpaddr dstpcn dstkpst dstpst dstpin dstpout dstsz dstpm cdstkp dstpd nextdst,
  can_change_aop P ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ->
  nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr ->
  get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) ->
  get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) ->
  ((Z.of_nat dstpcn) <> DNUM ->
          nth_error vsdstcl ((length cdstkp) - n)%nat =
              Some (Vint32 (Int.repr (Z.of_nat dstpcn)))) ->
  sch
  ⊢ <|| qportpost_send_one_Outcore n
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
        V$ Z.of_nat csemid :: vsdstcl|);; s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))) ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= Hdomainportl
    (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))) **
  Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))))).
    unfold qportpost_send_one_Outcore.
    do 15 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (3::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    do 3 eexists; splits; eauto.
    { sep remember (4::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    do 2 eexists; splits; eauto.
    do 13 eexists. splits; eauto.
    absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma Ecb_set_a_set_a : forall T a val1 val2, EcbMod.set (EcbMod.set T a val1) a val2 = EcbMod.set T a val2.
Proof.
  intros.
  apply EcbMod.extensionality.
  intro.
  destruct (tidspec.beq a a0) eqn:eq1.
  rewrite EcbMod.set_a_get_a.
  rewrite EcbMod.set_a_get_a.
  auto.
  auto.
  auto.
  rewrite EcbMod.set_a_get_a'.
  rewrite EcbMod.set_a_get_a'.
  rewrite EcbMod.set_a_get_a'.
  auto.
  auto.
  auto.
  auto.
Qed.

Lemma qportpost_send_one_InCore_porttskrdy_abt: forall sch s P v n m vsdstcl dpl pcn pid kportl kpaddr kpst channaddr chanl cid cdn 
  dstkpaddr dstpid dstpaddr dstpcn dstkpst tcbls ecbls wt t p st tskm  cdstkp,
  can_change_aop P ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, IncoreC)->
  nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr ->
  get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) ->
  get ecbls dstpaddr = Some (absport, wt) ->
  wt <> nil ->
  GetHWait tcbls wt  t ->
  get tcbls t = Some (p,st,tskm,true) ->
  sch
  ⊢ <|| qportpost_send_one_Incore_porttskrdy n
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
        Vnull :: vsdstcl|);; s ||>  **
    HTCBList tcbls ** HECBList ecbls ** Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** P 
    ⇒
    <|| ABORT ||>  **
    HTCBList tcbls ** HECBList ecbls ** Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT). can_change_aop_solver.
  3:{
    eapply absinfer_seq_abt.
    3: eauto.
    can_change_aop_solver.
    can_change_aop_solver.
  }
  can_change_aop_solver.
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds.
  do 14 eexists; splits; eauto.
  { sep remember (3::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (4::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (5::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
  do 5 eexists; splits; eauto.
  do 2 eexists; splits; eauto.
  { sep remember (2::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
  do 6 eexists; splits; eauto.
  { sep remember (1::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
  instantiate (1:= empabst).
  apply map_join_emp.   
  repeat hmstep_call_consturctor.
  sep auto.
Qed.

Lemma qportpost_send_one_InCore_porttskrdy_cont: forall sch s P v n m vsdstcl dpl pcn pid kportl kpaddr kpst channaddr chanl cid cdn 
  dstkpaddr dstpid dstpaddr dstpcn dstkpst tcbls ecbls wt t p st tskm cdstkp,
  can_change_aop P ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, IncoreC)->
  nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr ->
  get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) ->
  get ecbls dstpaddr = Some (absport, wt) ->
  wt <> nil ->
  GetHWait tcbls wt  t ->
  get tcbls t = Some (p,st,tskm,false) ->
  sch
  ⊢ <|| qportpost_send_one_Incore_porttskrdy n
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
        Vnull :: vsdstcl|);; s ||>  **
    HTCBList tcbls ** HECBList ecbls ** Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** P 
    ⇒
    <|| s ||>  **
    HTCBList  (set tcbls t (p, rdy, Vptr OS_PARTITION_MESSAGE_COME_ptr, false)) **
    HECBList (set ecbls dstpaddr (absport, (remove_tid t wt))) **
    Hdomainportl dpl ** Hkernelport kportl ** 
    Hchannell chanl ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    3: eauto.
    can_change_aop_solver.
    can_change_aop_solver.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= (set (set O abtcblsid (abstcblist (set tcbls t (p, rdy, Vptr OS_PARTITION_MESSAGE_COME_ptr, false))))) 
                              absecblsid (absecblist (set ecbls dstpaddr (absport, (remove_tid t wt))))).
    unfold qportpost_send_one_Incore_porttskrdy.
    do 14 eexists; splits; eauto.
    { sep remember (3::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (4::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (5::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    do 5 eexists; splits; eauto.
    do 2 eexists; splits; eauto.
    { sep remember (2::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    do 6 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H8. simpl in H8. simpljoin1. eapply join_sig_get;eauto. }
    right.
    do 2 eexists; splits; eauto.
    rewrite Ecb_set_a_set_a. reflexivity.
    absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma qportpost_send_one_InCore_cont: forall sch  msg s P v n m  vsdstcl dpl pcn pid kportl kpaddr kpst channaddr chanl cid cdn cHeapl cHeape cHeapt mlen
  dstkpaddr dstpid dstpaddr dstpcn dstkpst dstpst dstpin dstpout dstsz dstpm cdstkp dstpd nextdst,
  can_change_aop P ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  get chanl channaddr = Some (cid, cdn, cdstkp, IncoreC)->
  Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ->
  nth_error cdstkp ((length cdstkp) - n)%nat = Some dstkpaddr ->
  get kportl dstkpaddr = Some (dstpid, Some dstpaddr, Some channaddr, dstpcn, dstkpst) ->
  get dpl dstpaddr = Some (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz dstpm) ->
  sch
  ⊢ <|| qportpost_send_one_Incore n
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
        Vnull :: vsdstcl|);; s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| s ||>  **
    Hdomainportl (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))) ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= Hdomainportl
    (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))) **
  Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dpl dstpaddr (dstpcn, dstpd, dstpid, DestinationP nextdst, dstpst, dstpin, dstpout, QueuePort dstsz (dstpm ++ (msg :: nil)))))).
    unfold qportpost_send_one_Incore.
    do 14 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H7. simpl in H7. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H7. simpl in H7. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (3::nil)%nat in H7. simpl in H7. simpljoin1. eapply join_sig_get;eauto. }
    do 3 eexists; splits; eauto.
    { sep remember (4::nil)%nat in H7. simpl in H7. simpljoin1. eapply join_sig_get;eauto. }
    do 2 eexists; splits; eauto.
    do 13 eexists. splits; eauto.
    absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma qportpend_notnil_abt' : forall sch P dprtls kportls chanls p_v tm_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cHeapl cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
~ In_heapl_addrval cHeapl msg_p (S (length msg)) ->
can_change_aop P ->
sch ⊢  <|| qportpend_notnil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|)||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P
      ⇒ <|| ABORT ||>  **
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds. 
  do 23 eexists.
  splits;try eauto. instantiate (1:= O). 
  { sep remember (1::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  left. auto. 
  instantiate (1:= empabst). 
  apply map_join_emp.
  instantiate (1:= O).
  repeat hmstep_call_consturctor.
  destruct s as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H4. simpl_sat_goal.
  simpljoin.
  repeat progress  (do 6 eexists;
  splits ; try eauto).
  simpl. auto.
  eapply change_aop_rule; eauto. 
Qed.

Lemma qportpend_notnil_cont' : forall sch P dprtls kportls chanls p_v tm_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cheapl1 msgn msglen msgvl ml2 cheapl2 cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
In_heapl_addrval (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) msg_p (S (length msg)) ->
length (msglen :: msgvl) = S (length msg) ->
can_change_aop P ->
sch ⊢  <|| qportpend_notnil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls **
      HCoreHeap (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) cHeape cHeapt ** P
      ⇒ <|| END (Some (Vint32 (Int.repr  OS_NO_ERR))) ||>  **
      Hdomainportl (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl)))  ** 
      Hkernelport kportls ** 
      Hchannell chanls ** 
      HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_prim ;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step.
  instantiate (2:=  (Some (Vint32 (Int.repr  OS_NO_ERR)))).
  instantiate (2:= O).
  unfolds. 
  do 23 eexists.
  splits;try eauto.
  { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  right.
  exists (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) 
         (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl))).
  splits;eauto.
  { unfold update_heapl_addrval.
    exists cheapl1 msgn (msglen :: msgvl) ml2 cheapl2.
    splits;eauto. }
  eapply eqdomO_trans.
  2: eapply abst_get_set_eqdom.
  eapply abst_get_set_eqdom.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  unfold eqtls;auto.
  eapply get_set_neq;auto.
  { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  cbn;auto.
  eapply tidsame_trans.
  2: eapply tidsame_set;auto.
  eapply tidsame_set;auto.

  join auto.
  join auto.

  repeat hmstep_call_consturctor.
  destruct s as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H5. simpl_sat_goal.
  simpljoin1.


  do 6 eexists;splits ; try eauto.
  instantiate (2:= empenv).
  join auto.
  cbn. unfold emposabst. auto.

  assert (indom x21 oscoreheapid).
  {  eapply get_indom.
  eexists.
  eapply join_sig_get;eauto. }

  do 4 eexists.
  exists (set x9 oscoreheapid
  (oscoreheap
     (cheapl1 ++
      (msg_p, msgn,
      (V$ Z.of_nat (length msg) :: msg) ++
      ml2) :: cheapl2, cHeape, cHeapt))).
  eexists. splits;eauto.
  eapply abs_join_sig_set_join.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  eapply join_in_r;eauto.

  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  
  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.

  unfold gettaskst, emptaskst in *. subst.

  do 6 eexists;splits ; try eauto.
  join auto.
  eapply join_sig_set;eauto.

  eapply change_aop_rule; eauto. 
Qed.


Lemma qportpend_notnil_abt : forall sch s P dprtls kportls chanls p_v tm_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cHeapl cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
~ In_heapl_addrval cHeapl msg_p (S (length msg)) ->
can_change_aop P ->
sch ⊢  <|| qportpend_notnil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P
      ⇒ <|| ABORT ||>  **
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dprtls ** Hkernelport kportls ** Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply qportpend_notnil_abt';eauto. } 

  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma qportpend_notnil_cont : forall sch s P dprtls kportls chanls p_v tm_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cheapl1 msgn msglen msgvl ml2 cheapl2 cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
In_heapl_addrval (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) msg_p (S (length msg)) ->
length (msglen :: msgvl) = S (length msg) ->
can_change_aop P ->
sch ⊢  <|| qportpend_notnil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls **
      HCoreHeap (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) cHeape cHeapt ** P
      ⇒ <|| s ||>  **
      Hdomainportl (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl)))  ** 
      Hkernelport kportls ** 
      Hchannell chanls ** 
      HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := END (Some (Vint32 (Int.repr  OS_NO_ERR)))) 
  (q:= Hdomainportl (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl)))  ** 
  Hkernelport kportls ** 
  Hchannell chanls ** 
  HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply qportpend_notnil_cont';eauto.
  }

  apply absinfer_seq_end;can_change_aop_solver.
  sep auto.
Qed.

Lemma qportpend_nil_cont : forall sch s0 s1  P dprtls tm_v msg_p p_v pcn pd pid pdir pst pintick poutick 
sz,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz nil) ->
can_change_aop P ->
sch ⊢  <|| s0 ?? qportpend_nil (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; s1 ||> ** 
      Hdomainportl dprtls  ** P
      ⇒ <|| s1 ||>  **
      Hdomainportl dprtls  **  P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= Hdomainportl dprtls ** P);
  can_change_aop_solver.
  intros. sep auto.
  eapply absinfer_trans.
  2: eapply absinfer_seq_end with (p:= Hdomainportl dprtls ** P);
  can_change_aop_solver.
  eapply absinfer_seq;can_change_aop_solver.
  instantiate (1:= None).
  infer_solver 0%nat.
  intros. sep auto.
Qed.

Lemma qportpend_idle_err_abt: forall sch s P tid tcbls tm_v msg_p p_v st m sus,
get tcbls tid = Some (Int.repr OS_IDLE_PRIO, st, m, sus) ->
can_change_aop P ->
sch ⊢  <||  qportpend_idle_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ??  s  ||> ** 
      HTCBList tcbls **
      HCurTCB  tid ** P
      ⇒ <|| ABORT ||>  **
      HTCBList tcbls **
      HCurTCB  tid ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice1 with (q:= HTCBList tcbls ** HCurTCB tid ** P);can_change_aop_solver. 
  sep auto.
  eapply absinfer_abt;can_change_aop_solver.
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds.
  do 3 eexists. splits;eauto. do 5 eexists. splits;eauto. 
  sep remember (2::nil)%nat in H1.
  simpl_sat H1. simpljoin1.  eapply join_sig_get; eauto.
  sep remember (1::nil)%nat in H1.
  simpl_sat H1. simpljoin1.  eapply join_sig_get; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  sep auto.
Qed.

Lemma qportpend_not_ready_err_abt: forall sch s0 s P tid tcbls tm_v msg_p p_v pri st m sus,
get tcbls tid = Some (pri, st, m, sus) ->
(~ (st = rdy /\ sus = false)) ->
can_change_aop P ->
sch ⊢  <||  s0 ?? qportpend_not_ready_err (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ??  s  ||> ** 
      HTCBList tcbls **
      HCurTCB  tid ** P
      ⇒ <|| ABORT ||>  **
      HTCBList tcbls **
      HCurTCB  tid ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= HTCBList tcbls ** HCurTCB tid ** P);can_change_aop_solver. 
  sep auto.
  eapply absinfer_trans.
  eapply absinfer_choice1 with (q:= HTCBList tcbls ** HCurTCB tid ** P);can_change_aop_solver. 
  sep auto.
  eapply absinfer_abt;can_change_aop_solver.
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds.
  do 3 eexists. splits;eauto. do 6 eexists. splits;eauto. 
  sep remember (2::nil)%nat in H2.
  simpl_sat H2. simpljoin1.  eapply join_sig_get; eauto.
  sep remember (1::nil)%nat in H2.
  simpl_sat H2. simpljoin1.  eapply join_sig_get; eauto.
  apply map_join_emp.
  repeat hmstep_call_consturctor.
  sep auto.
Qed.


Lemma qportpend_block_cont: forall sch s s0 s1 P tid tcbls ecbls dportls tm_v msg_p p_v 
  pri st m sus wt 
  pcn pd pid pdir pst pintick poutick sz t_opt,
get tcbls tid = Some (pri,st,m,sus) ->
get ecbls p_v = Some (absport, wt) ->
get dportls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz nil) ->
((t_opt = Some tm_v /\ tm_v <> Int.zero) \/ (t_opt = None /\ tm_v = Int.zero))  ->
can_change_aop P ->
sch ⊢  <||  s0 ?? s1 ?? qportpend_block (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; s  ||> ** 
      HTCBList tcbls **
      HECBList ecbls **
      HCurTCB  tid **
      Hdomainportl dportls ** P
      ⇒ <|| s ||>  **
      HTCBList (set tcbls tid (pri, wait (os_stat_port p_v) t_opt, m,sus)) **
      HECBList (set ecbls p_v (absport, tid :: wt)) **
      HCurTCB  tid **
      Hdomainportl dportls ** P.
Proof.
  intros. 
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= HTCBList tcbls ** HECBList ecbls ** HCurTCB tid ** Hdomainportl dportls ** P);can_change_aop_solver.
  sep auto.
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= HTCBList tcbls ** HECBList ecbls ** HCurTCB tid ** Hdomainportl dportls ** P);can_change_aop_solver.
  sep auto.
  eapply absinfer_trans.
  2: eapply absinfer_seq_end with (p:= HTCBList
  (set tcbls tid (pri, wait (os_stat_port p_v) t_opt, m, sus)) **
HECBList (set ecbls p_v (absport, tid :: wt)) **
HCurTCB tid ** Hdomainportl dportls ** P);
  can_change_aop_solver.
  eapply absinfer_seq;can_change_aop_solver.
  instantiate (1:= None).
  infer_solver 0%nat.
  intros. sep auto.
Qed.


Lemma qportpend_block_timeout_end: forall sch s0 P tid tcbls ecbls dportls tm_v msg_p p_v 
  pri st sus wt 
  pcn pd pid pdir pst pintick poutick sz pm,
get tcbls tid = Some (pri,st,Vnull,sus) ->
get ecbls p_v = Some (absport, wt) ->
get dportls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz pm) ->
can_change_aop P ->
sch ⊢  <||  s0 ?? qportpend_block_timeout (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|) ||> ** 
      HTCBList tcbls **
      HECBList ecbls **
      HCurTCB  tid **
      Hdomainportl dportls ** P
      ⇒ <|| END (Some (Vint32 (Int.repr OS_TIMEOUT))) ||>  **
      HTCBList (set tcbls tid (pri, rdy, Vnull, false)) **
      HECBList (set ecbls p_v (absport, (remove_tid tid wt))) **
      HCurTCB  tid **
      Hdomainportl dportls ** P.
Proof.
  intros. 
  eapply absinfer_trans.
  eapply absinfer_choice2 with (q:= HTCBList tcbls ** HECBList ecbls ** HCurTCB tid ** Hdomainportl dportls ** P);can_change_aop_solver.
  sep auto.
  eapply absinfer_prim ;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step.
  instantiate (2:=  (Some (Vint32 (Int.repr OS_TIMEOUT)))).
  instantiate (2:= O).
  unfolds. 
  do 13 eexists.
  splits;try eauto.
  { sep remember (4::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  do 7 eexists.
  splits;try eauto.
  { sep remember (3::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (1::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (2::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  split;eauto.
  eapply eqdomO_trans.
  2:eapply abst_get_set_eqdom.
  eapply abst_get_set_eqdom.
  { sep remember (1::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  unfold eqtls;auto. 
  eapply tls_get_set_indom;eauto.
  erewrite get_set_neq;eauto.
  { sep remember (2::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
  unfold eqtls;auto. 
  eapply tidsame_trans.
  2: eapply tidsame_set;eauto.
  eapply tidsame_set;eauto.

  join auto.
  join auto.

  repeat hmstep_call_consturctor.
  destruct s as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H3. simpl_sat_goal.
  simpljoin1.


  do 6 eexists;splits ; try eauto.
  instantiate (2:= empenv).
  join auto.
  cbn. unfold emposabst. auto.


  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.
  eapply join_sig_set;eauto.
  unfold indom. eexists. eapply join_sig_get;eauto.


  do 6 eexists;splits ; try eauto.
  eapply join_sig_set;eauto.

  exists empmem.
  do 5 eexists;splits ; try eauto.
  join auto. split;auto. cbn. auto.

  do 6 eexists;splits ; try eauto.

  eapply change_aop_rule; eauto. 
Qed.

Lemma qportpend_aftersch_cont :
  forall qid P tcbls curtid sch  p st m s sus,
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
     (st = rdy /\ m  = (Vptr OS_PARTITION_MESSAGE_COME_ptr)  /\ sus = false \/
     st = wait (os_stat_port qid) (Some Int.zero) /\ m = Vnull /\ sus = false) ->
    absinfer sch
      (<||  qportpend_after_sched (|Vptr qid :: nil|) ;; s ||> **
           HTCBList tcbls **  HCurTCB curtid ** P)
      (<|| s ||> **
           HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma qportpend_aftersch_abt :
  forall qid P tcbls curtid sch  p st m s sus,
    can_change_aop P ->
     TcbMod.get tcbls curtid = Some (p, st, m, sus) ->
     ~ (st = rdy /\ m  = (Vptr OS_PARTITION_MESSAGE_COME_ptr)  /\ sus = false \/
     st = wait (os_stat_port qid) (Some Int.zero) /\ m = Vnull /\ sus = false) ->
    absinfer sch
      (<||  qportpend_after_sched (|Vptr qid :: nil|) ;; s ||> **
           HTCBList tcbls **  HCurTCB curtid ** P)
      (<|| ABORT ||> **
           HTCBList tcbls ** HCurTCB curtid ** P).
Proof.
  intros.
  assert (Hc: can_change_aop ( HTCBList tcbls ** HCurTCB curtid ** P)) .
  can_change_aop_solver.
  eapply absinfer_trans.
  2: eapply absinfer_seq_abt;eauto.
  eapply absinfer_seq;eauto.
  eapply absinfer_abt; try eauto.
  unfolds; intros;
  eexists; exgamma;
  (first [ splits ; 
           [ try simpl_subst_gamma;
             try hmstep_call_consturctor; try eapply spec_prim_step_abt; 
             [ unfolds; repeat eexists; subst;
               try (eapply absdata_elim; eauto with abst_solver_base); try eauto 
             | try apply map_join_emp 
             |  repeat hmstep_call_consturctor
             | .. ]
           | sep remember (1 :: nil)%nat; simpl in *; simpljoin ;
           do 6 eexists ; splits ; try eauto ; eapply change_aop_rule; eauto]
         | idtac] ).
  sep lift (2)%nat in H2.
  eauto.
Qed.

Lemma qportpend_block_get_cont :
  forall p_v tm_v msg_p  P tcbls curtid sch  p m s sus,
    can_change_aop P ->
    TcbMod.get tcbls curtid = Some (p, rdy, m, sus) ->
    m <> Vnull -> 
    absinfer sch
      (<||  qportpend_block_get (|Vptr p_v :: Vint32 tm_v :: Vptr msg_p :: nil|);; s ||> **
           HTCBList tcbls **  HCurTCB curtid ** P)
      (<|| s ||> **
           HTCBList (set tcbls curtid (p, rdy, Vnull, sus) )  ** HCurTCB curtid ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma samplepost_sendmemcpy_one_abt: forall sch msg n P v m vsem vsdstc dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cdstkp cHeapl cHeape cHeapt,
  can_change_aop P ->
  length cdstkp = length vsdstc ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort (Some msg)) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstc /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  
        Forall (fun (v:val) => v = Vnull) vsdstc /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
      (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| samplepost_sendmemcpy_one n 
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
          vsem :: vsdstc|) ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| ABORT ||>  **
    Hdomainportl dpl ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds. 
  do 20 eexists.
  splits;try eauto. instantiate (1:= O). 
  sep remember (1::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
  sep remember (2::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
  sep remember (3::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
  splits; eauto.
  do 3 eexists; splits; eauto.
  sep remember (4::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
  instantiate (1:= empabst). 
  apply map_join_emp.
  instantiate (1:= O).
  repeat hmstep_call_consturctor.
  destruct s as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H5. simpl_sat_goal.
  simpljoin.
  repeat progress (do 6 eexists; splits; try eauto).
  simpl. auto.
  eapply change_aop_rule; eauto.
Qed.

Lemma samplepost_sendmemcpy_one_abt_s: forall sch msg s n P v m vsem vsdstc dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cdstkp cHeapl cHeape cHeapt,
  can_change_aop P ->
  length cdstkp = length vsdstc ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort (Some msg)) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstc /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  
        Forall (fun (v:val) => v = Vnull) vsdstc /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
      (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| samplepost_sendmemcpy_one n 
      (|Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
          vsem :: vsdstc|);; s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| ABORT ||>  **
    Hdomainportl dpl ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
    unfolds;intros.
    eexists;exgamma.
    splits.
    simpl_subst_gamma.
    hmstep_call_consturctor.
    eapply spec_prim_step_abt.
    instantiate (1:=  None).
    unfolds. 
    do 20 eexists.
    splits;try eauto. instantiate (1:= O). 
    sep remember (1::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
    sep remember (2::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
    sep remember (3::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
    splits; eauto.
    do 3 eexists; splits; eauto.
    sep remember (4::nil)%nat in H5; simpl in H5; simpljoin1; eapply join_sig_get; eauto.
    instantiate (1:= empabst). 
    apply map_join_emp.
    instantiate (1:= O).
    repeat hmstep_call_consturctor.
    destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
    simpl_sat H5. simpl_sat_goal.
    simpljoin.
    repeat progress (do 6 eexists; splits; try eauto).
    simpl. auto.
    eapply change_aop_rule; eauto.
  }
  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma samplepost_sendmemcpy_aux_Outcore_abt: forall sch msg s n P v m vsem vsdstc dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cdstkp cHeapl cHeape cHeapt,
  can_change_aop P ->
  length cdstkp = length vsdstc ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort (Some msg)) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstc /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  
        Forall (fun (v:val) => v = Vnull) vsdstc /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
      (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| spec_code_cons (samplepost_sendmemcpy_aux_Outcore (S n) 
      (Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
          vsem :: vsdstc)) s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| ABORT ||>  **
    Hdomainportl dpl ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  cbn [samplepost_sendmemcpy_aux_Outcore].
  cbn [spec_code_cons].
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply samplepost_sendmemcpy_one_abt; eauto.
  }
  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma samplepost_sendmemcpy_aux_Incore_abt: forall sch msg s n P v m vsem vsdstc dpl pcn pd pid pst pin pout kportl kpaddr kpst channaddr chanl cid cdn cdstkp cHeapl cHeape cHeapt,
  can_change_aop P ->
  length cdstkp = length vsdstc ->
  get dpl v = Some (pcn, pd, pid, SourceP, pst, pin, pout, SamplePort (Some msg)) ->
  get kportl kpaddr = Some (pid, Some v, Some channaddr, pcn, kpst) ->
  ( ( exists csemid,
          vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
          Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstc /\
          get chanl channaddr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
        vsem = Vnull /\  
        Forall (fun (v:val) => v = Vnull) vsdstc /\  
        get chanl channaddr = Some  (cid, cdn, cdstkp, IncoreC)) ->
  ~ ( exists mlen msg,
      Get_heapl_addrval cHeapl m (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: msg) /\
      (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ) ->
  sch
  ⊢ <|| spec_code_cons (samplepost_sendmemcpy_aux_Incore (S n) 
      (Vptr v :: Vptr m :: 
        Vint32 (Int.repr (Z.of_nat (length cdstkp))) :: 
          vsem :: vsdstc)) s ||>  **
    Hdomainportl dpl ** Hkernelport kportl **
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P 
    ⇒
    <|| ABORT ||>  **
    Hdomainportl dpl ** Hkernelport kportl ** 
    Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  cbn [samplepost_sendmemcpy_aux_Incore].
  cbn [spec_code_cons].
  eapply absinfer_trans.
  {
    eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dpl ** Hkernelport kportl ** Hchannell chanl ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
    eapply samplepost_sendmemcpy_one_abt; eauto.
  }
  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma samplepost_sendmemcpy_one_cont:
  forall sch s P pptr msgptr vsem vsdstcl pin mlen ori_msg_vl
        dstkportpl dstkportpl1 dstkportp dstkportpl2 dstportp
        dportls kportls chanls cHeapl cHeape cHeapt tm
        v'38 v'39 v'40 v'41 v'42 v'43 v'44 v'45 v'46 v'47 v'48 v'49
        v'31 v'32 v'33 v'34 v'35 v'36 v'37 nextdst,
  can_change_aop P ->
  dstkportpl = dstkportpl1 ++ dstkportp :: dstkportpl2 ->
  (length dstkportpl = length vsdstcl)%nat ->
  get dportls pptr = Some (v'38, v'39, v'40, SourceP, v'41,
      Z.to_nat (Int.unsigned pin), v'42, SamplePort (Some v'43)) ->
  get kportls v'44 = Some (v'40, Some pptr, Some v'45, v'38, v'46) ->
  ( ( exists csemid,
        vsem = Vint32 (Int.repr (Z.of_nat csemid)) /\
        Forall (fun (v:val) => exists vdst, v = Vint32 vdst) vsdstcl /\
        get chanls v'45 = Some (v'47, v'48, dstkportpl, OutcoreC csemid) ) \/ 
      vsem = Vnull /\  
      Forall (fun (v:val) => v = Vnull) vsdstcl /\  
      get chanls v'45 = Some (v'47, v'48, dstkportpl, IncoreC)  ) ->
  Get_heapl_addrval cHeapl msgptr
    (Z.to_nat (Int.unsigned mlen + 1)) (Vint32 mlen :: ori_msg_vl) ->
  (Int.unsigned mlen <= CHANNEL_CACHE_SZIE)%Z ->
  get kportls dstkportp =
      Some (v'33, Some dstportp, Some v'45, v'31, v'49) ->
  get dportls dstportp = Some (v'31, v'32, v'33,
    DestinationP nextdst, v'34, v'35, v'36, SamplePort v'37) ->
  (Z.of_nat v'31 <> DNUM ->
    nth_error vsdstcl (length dstkportpl1) = Some (V$ Z.of_nat v'31)) ->
  sch ⊢ <||samplepost_sendmemcpy_one (S (length dstkportpl2))
            (|Vptr pptr :: Vptr msgptr :: 
                V$ Z.of_nat (length dstkportpl) :: 
                  vsem :: vsdstcl|) ;; s ||> **
        Hdomainportl dportls **
        Hkernelport kportls **
        Hchannell chanls **
        HCoreHeap cHeapl cHeape cHeapt ** 
        HTime tm ** P
      ⇒ <|| s ||> **
        Hdomainportl (set dportls dstportp (v'31, v'32, v'33, DestinationP nextdst, v'34, Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm), SamplePort (Some ori_msg_vl))) **
        Hkernelport kportls **
        Hchannell chanls **
        HCoreHeap cHeapl cHeape cHeapt **
        HTime tm ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= Hdomainportl
                        (set dportls dstportp
                            (v'31, v'32, v'33, DestinationP nextdst, v'34,
                            Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
                            SamplePort (Some ori_msg_vl))) **
                      Hkernelport kportls **
                      Hchannell chanls **
                      HCoreHeap cHeapl cHeape cHeapt **
                      HTime tm ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dportls dstportp
                      (v'31, v'32, v'33, DestinationP nextdst, v'34,
                      Z.to_nat (Int.unsigned pin), Z.to_nat (Int.unsigned tm),
                      SamplePort (Some ori_msg_vl))))).
    unfold samplepost_sendmemcpy_one.
    do 20 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H10. simpl in H10. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H10. simpl in H10. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (3::nil)%nat in H10. simpl in H10. simpljoin1. eapply join_sig_get;eauto. }
    splits; eauto.
    do 3 eexists; splits; eauto.
    { sep remember (4::nil)%nat in H10. simpl in H10. simpljoin1. eapply join_sig_get;eauto. }
    right; do 2 eexists; splits; eauto.
    do 13 eexists; splits; eauto.
    {
      assert (((length dstkportpl - S (length dstkportpl2)) = length dstkportpl1)%nat).
      { subst; rewrite app_length; simpl; lia. }
      rewrite H11; subst.
      rewrite nth_error_app2; auto.
      assert ((length dstkportpl1 - length dstkportpl1 = 0)%nat) by lia.
      rewrite H0; simpl; auto.
    }
    { sep remember (5::nil)%nat in H10. simpl in H10. simpljoin1. eapply join_sig_get;eauto. }
    {
      assert (((length dstkportpl - S (length dstkportpl2)) = length dstkportpl1)%nat).
      { subst; rewrite app_length; simpl; lia. }
      rewrite H11; subst; auto.
    }
    1,2: try absinfer_side_condition_solver.
    1,2: apply map_join_emp. 
  }
  repeat simpl_absdata_sep; sep auto.
Qed.

Lemma portflush_succ_cont:
  forall sch s P pptr dportls kportls
         pcn pd pid pdir pst pin pout pt kpptr chan kpst pt',
  can_change_aop P ->
  get dportls pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
  get kportls kpptr = Some (pid, Some pptr, chan, pcn, kpst) ->
  (* ((exists csemid,
      get chanls chanptr = Some (cid, cdn, cdstkp, OutcoreC csemid)) \/ 
    get chanls chanptr = Some  (cid, cdn, cdstkp, IncoreC)) -> *)
  ((exists msg, pt = SamplePort msg /\ pt' = SamplePort (Some (@nil val))) \/
  (exists sz msg, pt = QueuePort sz msg /\ pt' = QueuePort sz (nil))) ->
  sch ⊢ <|| portflush_succ (|Vptr pptr :: nil|);; s ||> **
        Hdomainportl dportls **
        Hkernelport kportls ** P
      ⇒ <|| s ||> **
        Hdomainportl (set dportls pptr (pcn, pd, pid, pdir, pst, pin, pout, pt')) **
        Hkernelport kportls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    3: eauto.
    can_change_aop_solver.
    can_change_aop_solver.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    instantiate (1:= set O osdomainportid (osdomainport (set dportls pptr
                                          (pcn, pd, pid, pdir, pst, pin, pout, pt')))).
    unfold portflush_succ.
    do 14 eexists; splits; eauto.
    { sep remember (1::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H3. simpl in H3. simpljoin1. eapply join_sig_get;eauto. }
    1,2: try absinfer_side_condition_solver.
    1,2: apply map_join_emp. 
  }
  repeat simpl_absdata_sep; sep auto.
Qed.
Lemma err_portnull_absinfer:
  forall (P : asrt) (sch : ossched),
    can_change_aop P ->
    sch ⊢  <|| err_portnull (|Vnull :: nil|) ||>  ** P ⇒  <|| END Some (V$ OS_PORT_ERR_NULL) ||>  ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_unmapped_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt tcbl tid pri st msg sus,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    get tcbl tid = Some (pri, st, msg, sus) ->
    Int.eq (pri >>ᵢ $ 3) ($ Z.of_nat pd) = false ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_unmapped (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** 
      HCurTCB tid ** 
      HTCBList tcbl ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_PARTITION_UNMAPPED) ||> **
      Hdomainportl dpl ** 
      HCurTCB tid ** 
      HTCBList tcbl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_msgnull_absinfer:
  forall (P : asrt) (sch : ossched),
    can_change_aop P ->
    sch ⊢ 
      <|| err_msgnull OS_ERR_POST_NULL_PTR (|Vnull :: nil|) ||> ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_POST_NULL_PTR) ||> ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_porttype_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    (pdir <> SourceP \/ (exists sz ml, pt = QueuePort sz ml)) ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_porttype (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** P
    ⇒ 
      <|| END Some (V$ OS_PORT_ERR_TYPE) ||> **
      Hdomainportl dpl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_porttype_queue_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    (pdir <> SourceP \/ (exists ml, pt = SamplePort ml)) ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_porttype_queue (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** P
    ⇒ 
      <|| END Some (V$ OS_PORT_ERR_TYPE) ||> **
      Hdomainportl dpl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma err_nochannel_absinfer:
  forall (P : asrt) (sch : ossched) pptr dpl pcn pd pid pdir pst pin pout pt kportl kpaddr kpst,
    get dpl pptr = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
    get kportl kpaddr = Some (pid, Some pptr, None, pcn, kpst) ->
    can_change_aop P ->
    sch ⊢ 
      <|| err_nochannel (|Vptr pptr :: nil|) ||> **
      Hdomainportl dpl ** Hkernelport kportl ** P
    ⇒ 
      <|| END Some (V$ OS_ERR_PORT_NO_CHANNEL) ||> **
      Hdomainportl dpl ** Hkernelport kportl ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma portacc_err_dire_end:
  forall sch s P dprtls p_v pcn pd pid pst pintick poutick pt,
    get dprtls p_v = Some (pcn, pd, pid, SourceP, pst, pintick, poutick, pt) ->
    can_change_aop P ->
    sch ⊢  <||  portacc_err_dire (|Vptr p_v :: nil|) ;; s ||> ** 
          Hdomainportl dprtls  ** P
          ⇒ <|| s ||>  **
          Hdomainportl dprtls  ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma portacc_err_msgnull_end:
  forall sch s P,
    can_change_aop P ->
    sch ⊢  <||  portacc_err_msgnull (|Vnull :: nil|) ;; s ||> ** P
          ⇒ <|| s ||> ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma portacc_err_nochannel_end:
  forall sch s P dprtls kportls p_v kp_v pcn pd pid pdir pst pintick poutick pt kpst,
    get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, pt) ->
    get kportls kp_v = Some (pid, Some p_v, None, pcn, kpst)  ->
    can_change_aop P ->
    sch ⊢  <|| portacc_err_nochannel (|Vptr p_v :: nil|) ;; s ||> ** 
          Hdomainportl dprtls  ** Hkernelport kportls ** P
          ⇒ <|| s ||>  **
          Hdomainportl dprtls  ** Hkernelport kportls ** P.
Proof.
  infer_solver 0%nat.
Qed.

Lemma portacc_queue_notnil_abt : forall sch s P dprtls kportls chanls p_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cHeapl cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
~ In_heapl_addrval cHeapl msg_p (S (length msg)) ->
can_change_aop P ->
sch ⊢  <|| portacc_queue_notnil (|Vptr p_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P
      ⇒ <|| ABORT ||>  **
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dprtls ** Hkernelport kportls ** Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds. 
  do 22 eexists.
  splits;try eauto. instantiate (1:= O). 
  { sep remember (1::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  left. auto. 
  instantiate (1:= empabst). 
  apply map_join_emp.
  instantiate (1:= O).
  repeat hmstep_call_consturctor.
  destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H4. simpl_sat_goal.
  simpljoin.
  repeat progress  (do 6 eexists;
  splits ; try eauto).
  simpl. auto.
  eapply change_aop_rule; eauto. } 

  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma portacc_queue_notnil_cont : forall sch s P dprtls kportls chanls p_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
sz msg msgl channaddr kpst cid cdn cdstkp ctype cheapl1 msgn msglen msgvl ml2 cheapl2 cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msg :: msgl)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
In_heapl_addrval (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) msg_p (S (length msg)) ->
length (msglen :: msgvl) = S (length msg) ->
can_change_aop P ->
sch ⊢  <|| portacc_queue_notnil (|Vptr p_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls **
      HCoreHeap (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) cHeape cHeapt ** P
      ⇒ <|| s ||>  **
      Hdomainportl (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl)))  ** 
      Hkernelport kportls ** 
      Hchannell chanls ** 
      HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := END None) 
  (q:= Hdomainportl (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl)))  ** 
  Hkernelport kportls ** 
  Hchannell chanls ** 
  HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply absinfer_prim ;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step.
  instantiate (2:= None).
  instantiate (2:= O).
  unfolds. 
  do 22 eexists.
  splits;try eauto.
  { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  right.
  exists (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) 
         (set dprtls p_v (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz (msgl))).
  splits;eauto.
  { unfold update_heapl_addrval.
    exists cheapl1 msgn (msglen :: msgvl) ml2 cheapl2.
    splits;eauto. }
  eapply eqdomO_trans.
  2: eapply abst_get_set_eqdom.
  eapply abst_get_set_eqdom.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  unfold eqtls;auto.
  eapply get_set_neq;auto.
  { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  cbn;auto.
  eapply tidsame_trans.
  2: eapply tidsame_set;auto.
  eapply tidsame_set;auto.

  join auto.
  join auto.

  repeat hmstep_call_consturctor.
  destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H5. simpl_sat_goal.
  simpljoin1.


  do 6 eexists;splits ; try eauto.
  instantiate (2:= empenv).
  join auto.
  cbn. unfold emposabst. auto.

  assert (indom x21 oscoreheapid).
  {  eapply get_indom.
  eexists.
  eapply join_sig_get;eauto. }

  do 4 eexists.
  exists (set x9 oscoreheapid
  (oscoreheap
     (cheapl1 ++
      (msg_p, msgn,
      (V$ Z.of_nat (length msg) :: msg) ++
      ml2) :: cheapl2, cHeape, cHeapt))).
  eexists. splits;eauto.
  eapply abs_join_sig_set_join.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  eapply join_in_r;eauto.

  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  
  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.

  unfold gettaskst, emptaskst in *. subst.

  do 6 eexists;splits ; try eauto.
  join auto.
  eapply join_sig_set;eauto.

  eapply change_aop_rule; eauto. }

  apply absinfer_seq_end;can_change_aop_solver.
  sep auto.
Qed.

Lemma portacc_queue_nil_cont : forall sch s P dprtls p_v msg_p pcn pd pid pdir pst pintick poutick sz,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, QueuePort sz nil) ->
can_change_aop P ->
sch ⊢  <|| portacc_queue_nil (|Vptr p_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls ** P
      ⇒ <|| s ||>  **
      Hdomainportl dprtls ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := END None) 
  (q:= Hdomainportl dprtls  ** P);[can_change_aop_solver.. ].
  eapply absinfer_prim ;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step.
  instantiate (2:= None).
  instantiate (2:= O).
  unfolds. 
  do 11 eexists.
  splits;try eauto.
  { sep remember (1::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
  eapply eqdom_same.
  eapply eqtid_same.
  join auto.
  join auto.

  repeat hmstep_call_consturctor.

  destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H1. simpl_sat_goal.
  simpljoin.


  repeat progress (do 6 eexists;splits ; try eauto).
  simpl; auto.
  eapply change_aop_rule; eauto. }

  apply absinfer_seq_end;can_change_aop_solver.
  sep auto.
Qed.

Lemma portacc_sample_abt : forall sch s P dprtls kportls chanls p_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
msg channaddr kpst cid cdn cdstkp ctype cHeapl cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, SamplePort (Some msg)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
~ In_heapl_addrval cHeapl msg_p (S (length msg)) ->
can_change_aop P ->
sch ⊢  <|| portacc_sample (|Vptr p_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P
      ⇒ <|| ABORT ||>  **
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := ABORT ) (q:= Hdomainportl dprtls ** Hkernelport kportls ** Hchannell chanls ** HCoreHeap cHeapl cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds. 
  do 20 eexists.
  splits;try eauto. instantiate (1:= O). 
  { sep remember (1::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H4. simpl in H4. simpljoin1. eapply join_sig_get;eauto. }
  left. auto. 
  instantiate (1:= empabst). 
  apply map_join_emp.
  instantiate (1:= O).
  repeat hmstep_call_consturctor.
  destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H4. simpl_sat_goal.
  simpljoin.
  repeat progress  (do 6 eexists;
  splits ; try eauto).
  simpl. auto.
  eapply change_aop_rule; eauto. } 

  apply absinfer_seq_abt;can_change_aop_solver.
  sep auto.
Qed.

Lemma portacc_sample_cont : forall sch s P dprtls kportls chanls p_v msg_p kp_v pcn pd pid pdir pst pintick poutick 
 msg channaddr kpst cid cdn cdstkp ctype cheapl1 msgn msglen msgvl ml2 cheapl2 cHeape cHeapt,
get dprtls p_v = Some (pcn, pd, pid, pdir,  pst, pintick, poutick, SamplePort (Some msg)) ->
get kportls kp_v = Some (pid, Some p_v, Some channaddr, pcn, kpst)  ->
get chanls channaddr = Some (cid, cdn, cdstkp, ctype) ->
In_heapl_addrval (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) msg_p (S (length msg)) ->
length (msglen :: msgvl) = S (length msg) ->
can_change_aop P ->
sch ⊢  <|| portacc_sample (|Vptr p_v :: Vptr msg_p :: nil|);; s ||> ** 
      Hdomainportl dprtls  ** Hkernelport kportls ** 
      Hchannell chanls **
      HCoreHeap (cheapl1 ++ (msg_p, msgn, (msglen :: msgvl) ++ ml2) :: cheapl2) cHeape cHeapt ** P
      ⇒ <|| s ||>  **
      Hdomainportl dprtls  ** 
      Hkernelport kportls ** 
      Hchannell chanls ** 
      HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P.
Proof.
  intros.
  eapply absinfer_trans.
  { eapply absinfer_seq with (s1' := END None) 
  (q:= Hdomainportl dprtls  ** 
  Hkernelport kportls ** 
  Hchannell chanls ** 
  HCoreHeap (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2) cHeape cHeapt ** P);[can_change_aop_solver.. ].
  eapply absinfer_prim ;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step.
  instantiate (2:= None).
  instantiate (2:= O).
  unfolds. 
  do 20 eexists.
  splits;try eauto.
  { sep remember (1::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (3::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  do 3 eexists.
  split.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  right.
  exists (cheapl1 ++ (msg_p, msgn, ((Vint32 ($ Z.of_nat (length msg))) :: msg) ++ ml2) :: cheapl2).
  splits;eauto.
  { unfold update_heapl_addrval.
    exists cheapl1 msgn (msglen :: msgvl) ml2 cheapl2.
    splits;eauto. }
  eapply eqdomO_trans.
  2: eapply abst_get_set_eqdom.
  eapply eqdom_same.
  { sep remember (4::nil)%nat in H5. simpl in H5. simpljoin1. eapply join_sig_get;eauto. }
  unfold eqtls;auto.
  eapply tidsame_trans.
  2: eapply tidsame_set;auto.
  eapply eqtid_same;auto.

  join auto.
  join auto.

  repeat hmstep_call_consturctor.
  destruct s0 as [[[[[? ? ] ? ] ? ] ?] ?].
  simpl_sat H5. simpl_sat_goal.
  simpljoin1.


  do 6 eexists;splits ; try eauto.
  instantiate (2:= empenv).
  join auto.
  cbn. unfold emposabst. auto.

  assert (indom x21 oscoreheapid).
  {  eapply get_indom.
  eexists.
  eapply join_sig_get;eauto. }

  do 6 eexists; splits; try eauto.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  eapply join_in_r;eauto.

  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.
  eapply join_in_r;eauto.
  
  do 6 eexists;splits ; try eauto.
  eapply join_set_r;eauto.

  unfold gettaskst, emptaskst in *. subst.

  do 6 eexists;splits ; try eauto.
  join auto.
  eapply join_sig_set;eauto.

  eapply change_aop_rule; eauto. }

  apply absinfer_seq_end;can_change_aop_solver.
  sep auto.
Qed.

Lemma ASSERT_err_msg_abt : forall errv m s sch P ,
  errv <> (Vint32 m) ->
  can_change_aop P ->
  sch ⊢  <|| ASSERT err_msg errv m ;; s ||> ** P ⇒ <|| ABORT ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  2: eapply absinfer_seq_abt with (p:= P);[can_change_aop_solver | can_change_aop_solver | sep auto].
  eapply absinfer_seq;can_change_aop_solver.
  eapply absinfer_assert_abt;can_change_aop_solver.
  sep auto.
  intros.
  unfold err_msg, not. intros.
  destruct errv;tryfalse.
Qed. 


Lemma ASSERT_err_msg_cont : forall errv m s sch P ,
  errv = (Vint32 m) ->
  can_change_aop P ->
  sch ⊢  <|| ASSERT err_msg errv m ;; s ||> ** P ⇒ <|| s ||>  ** P.
Proof.
  intros.
  eapply absinfer_trans.
  2: eapply absinfer_seq_end with (p:= P);[can_change_aop_solver | can_change_aop_solver | sep auto].
  eapply absinfer_seq;can_change_aop_solver.
  eapply absinfer_assert_cont;can_change_aop_solver.
  sep auto.
  intros.
  unfold err_msg. subst. auto.
Qed. 

Lemma receivePortMsg_aspec_abt: forall sch n cportpl P tcbls ecbls tcbls' s,
  can_change_aop P ->
  receivePortMsg_tcbls_ecbls (firstn n cportpl) ecbls tcbls tcbls' false ->
  sch
  ⊢ <|| receivePortMsg_aspec (|nil|);; s ||>  **
    HTCBList tcbls ** HECBList ecbls ** Hcoreportpl cportpl ** P 
    ⇒
    <|| ABORT ||>  **
    HTCBList tcbls ** HECBList ecbls **  Hcoreportpl cportpl ** P .
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := ABORT). can_change_aop_solver.
  3:{
    eapply absinfer_seq_abt.
    3: eauto.
    can_change_aop_solver.
    can_change_aop_solver.
  }
  can_change_aop_solver.
  eapply absinfer_abt;[can_change_aop_solver | can_change_aop_solver | auto ].
  unfolds;intros.
  eexists;exgamma.
  splits.
  simpl_subst_gamma.
  hmstep_call_consturctor.
  eapply spec_prim_step_abt.
  instantiate (1:=  None).
  unfolds.
  do 4 eexists; splits; eauto.
  { sep remember (3::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (2::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
  { sep remember (1::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
  instantiate (1:= empabst).
  apply map_join_emp.   
  repeat hmstep_call_consturctor.
  sep auto.
Qed.

Lemma receivePortMsg_tcbls_ecbls_eqdomtls:
  forall cportpl ecbls tcbls tcbls' b,
    receivePortMsg_tcbls_ecbls cportpl ecbls tcbls tcbls' b ->
    eqdomtls tcbls tcbls'.
Proof.
  intros.
  induction H.
  - unfold eqdomtls. intros. tauto.
  - auto.
  - eapply eqdomtls_trans; eauto.
    subst tcbls'.
    unfold eqdomtls. intros.
    unfold indom;split; intros.
    + destruct H3. destruct (addrval_eq_dec tid t'). subst.
      eexists. eapply set_a_get_a.
      eexists. eapply get_set_neq; eauto.
    + destruct H3. destruct (addrval_eq_dec tid t'). subst.
      eexists. eauto.
      eexists. rewrite set_a_get_a' in H3; eauto.
  - auto.
Qed. 

Lemma receivePortMsg_aspec_cont: forall sch cportpl P tcbls ecbls tcbls' s,
  can_change_aop P ->
  receivePortMsg_tcbls_ecbls cportpl ecbls tcbls tcbls' true ->
  sch
  ⊢ <|| receivePortMsg_aspec (|nil|);; s ||>  **
    HTCBList tcbls ** HECBList ecbls ** Hcoreportpl cportpl ** P 
    ⇒
    <|| s ||>  **
    HTCBList tcbls' ** HECBList ecbls **  Hcoreportpl cportpl ** P .
Proof.
  intros.
  eapply absinfer_trans.
  eapply absinfer_seq with (s1' := END None). can_change_aop_solver.
  3:{
    eapply absinfer_seq_end.
    instantiate (1:= HTCBList tcbls' ** HECBList ecbls ** Hcoreportpl cportpl ** P).
    can_change_aop_solver.
    can_change_aop_solver.
    sep auto.
  }
  can_change_aop_solver.
  tri_infer_prim; eexists;exgamma. 
  splits.
  {
    simpl_subst_gamma.
    repeat hmstep_call_consturctor.
    unfold receivePortMsg_aspec.
    do 4 eexists. splits; eauto.
    { sep remember (3::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (2::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
    { sep remember (1::nil)%nat in H1. simpl in H1. simpljoin1. eapply join_sig_get;eauto. }
    2: absinfer_side_condition_solver.
    absinfer_side_condition_solver.
    unfold eqtls.
    eapply receivePortMsg_tcbls_ecbls_eqdomtls; eauto.
    instantiate (1:= empabst).
    all: apply map_join_emp.
  }
  repeat simpl_absdata_sep; sep auto.
Qed.
