Require Import LibTactics.
Require Import base_tac. 
Require Import memory.

Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs.
Require Import buffer_apispecs.
Require Import intspecs.
Require Import osspecs.
Require Import properties.

Require Import data_invs.
Require Import equiv_prop.
Require Import if_assms.
Require Import if_succ_gen.
Require Import if_good_code.

Require Import hasrt_sat_preserve.
Require Import FunctionalExtensionality.

Require Import integrity_lemma.
Set Keyed Unification.
Require Import protect.
Require Import spec_aux_defs.
Require Import if_common_lemmas.
Require Import int_auto.
(* Require Import mqsend_cproof1. *)

Require Import chinfo_back_lemmas. 

Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end].

(* Require Import integrity_proof_send_code. *)
(* Require Import ports_cproof1_common. *)
(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)
Lemma dom_cur_tsk_join_get_l:
forall O0 Of Ox td,
dom_cur_tsk O0 td ->
join O0 Of Ox ->
dom_cur_tsk Ox td.
Proof.
introv Hdom Hj.
unfold dom_cur_tsk in *.
simpljoin.
exists x x0.
splits; auto.
eapply join_get_get_l;eauto.
unfold task_prio_id in *.
simpljoin.
do 5 eexists.
splits; eauto.
eapply join_get_get_l;eauto.
Qed.

(*from ports_cproof1_common*)
Lemma upd_bufmp_get_neq:
  forall bmp d d' ms,
    d <> d' -> 
    upd_bufmp bmp d ms d' = bmp d'.
Proof.
  intros.
  unfolds.
  apply Int.eq_false in H.
  rewrite H.
  auto. 
Qed.

(*end *)

Require Import confidentiality_tactics.
Require Import confidentiality_lemmas. 
Require Import ct_pp_lemmas.

Lemma tpi_frm_extend:
  forall O0 Of O p t, 
    task_prio_id O0 p t ->
    join O0 Of O ->
    task_prio_id O p t.
Proof.
  introv Htpi Hjo.
  unfold task_prio_id in *.
  simpljoin.
  do 5 eexists.
  split; eauto.
  eapply join_get_get_l; eauto. 
Qed. 

Lemma mq_ptr_same_objp: 
  forall O O' idx objp objp' td, 
    kernel_mq_equiv td O O -> 
    get O absmqattrid = get O' absmqattrid ->             
    mq_ptr O idx objp ->
    mq_ptr O' idx objp' ->
    objp = objp'. 
Proof. 
  introv Hkme Hgaeq Hmp Hmp'.
  unfold mq_ptr in *.
  simpljoin.
  match goal with
    Hgaeq: ?t1 = ?t2, H1: ?t1 = _, H2: ?t2 = _ |- _ =>
      rewrite H1 in Hgaeq; rewrite H2 in Hgaeq; inverts Hgaeq
  end.
  l_rew12_inv2 (get x idx).
  match goal with
    H1: _ \/ _, H2: _ \/ _ |- _ => destruct H1; destruct H2; simpljoin; tryfalse
  end.
  congruence. 
Qed. 

Lemma cspceq_cap_equiv:
  forall O O' td, 
    cap_equiv td O O -> 
    get O cspaceid = get O' cspaceid -> 
    kernel_mq_equiv td O O -> 
    get O absmqattrid = get O' absmqattrid -> 
    cap_equiv td O O'. 
Proof.
  introv Hce Hgeq Hkme Hmae.
  assert (Hkme_ := Hkme).
  unfolds.
  unfolds in Hce.
  simpljoin.
  symmetry in Hgeq.
  l_rew12_inv2 (get O cspaceid).
  rewrite H in Hgeq.
  unfolds in Hkme. 
  simpljoin.
  symmetry in Hmae.
  l_rew12_inv2 (get O absmqattrid).
  rewrite H0 in Hmae.

  do 2 eexists.
  split; eauto.
  split; eauto. 
  introv Hd.
  split.
  - intros.
    split; auto.
  - introv Hd'.
    split.
    +
      unfold mq_ptr.
      split.
      * 
        introv Hp.
        simpljoin.
        l_rew12_inv2 (get O absmqattrid).
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
        **
          do 9 eexists. split; eauto.
        **
          do 9 eexists. split; eauto. 
      *
        introv Hp.
        simpljoin.
        l_rew12_inv2 (get O' absmqattrid).
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
        **
          do 9 eexists. split; eauto.
        **
          do 9 eexists. split; eauto. 
    +
      introv Hmp1 Hmp2.
      lets Heq_: mq_ptr_same_objp Hmp1 Hmp2; eauto.
      congruence. 
      subst. 
      tauto.
Qed. 

Lemma local_envs_equiv_pp:
  forall O O' c td, 
    prio_preserved O O' -> 
    local_envs_equiv td c c O O'. 
Proof.
  introv Hpp.
  unfolds.
  introv Hd Htpi Htpi'.
  lets H__: prio_preserved_tpi Htpi' Hpp; eauto.  
  lets Heq: tid_unique Htpi H__; eauto.
  subst. 
  auto.
Qed.

Lemma client_data_equiv_pp: 
  forall O O' td cst, 
    prio_preserved O O' -> 
    client_data_equiv td cst cst O O'. 
Proof.
  introv Hpp.
  unfolds.
  destruct cst.
  destruct p.
  do 6 eexists.
  split; eauto.
  split; eauto.
  splits; eauto.
  eapply local_envs_equiv_pp; eauto. 
Qed. 

Lemma mq_equiv_ecbl_upd: 
  forall kportl cdstkpl dpl els els' tls O O' mq i, 
    get O absecblsid = Some (absecblist els) -> 
    get O' absecblsid = Some (absecblist els') -> 
    prio_preserved O O' -> 
    ecbl_upd kportl cdstkpl dpl els els' tls ->
    mq_equiv i mq mq O O ->
    mq_equiv i mq mq O O'. 
Proof.
  introv Hels Hels' Hpp Heu Hme.
  unfold mq_equiv in *.
  unfold ecbl_upd in Heu.
  simpljoin.
  do 8 eexists.
  split; eauto.
  split; eauto.
  match goal with
    H: _ \/ _ \/ _ |- _ => destruct H as [Hnull | [Hholder | Hptr]]; simpljoin
  end.
  - left; split; auto.
  - right; left. split; auto.
  -
    l_rew12_inv2 (get O absecblsid).
    match goal with
      H1: get ?t1 ?t2 = _, H2: get ?t1 ?t2 = _ |- _ =>
        rewrite H1 in H2; inverts H2
    end.
    right; right.
    match goal with x: tid, H: get _ ?x = _ |- _ => rename x into eid end.
    specialize (Heu eid).
    destruct Heu as [Hupd | Hnupd].
    + simpljoin.
      unfold hwait_prt in *.
      simpljoin.
      l_rew21_inv1 (get O absecblsid).
      match goal with H1: get els _ = _, H2: get els _ = _ |- _ => rewrite H1 in H2; inverts H2 end.
      unfold mq_ed_equiv in *.
      simpljoin.
      tryfalse.
    + simpljoin.
      l_rew21_inv1 (get O absecblsid).
      match goal with
        H1: get els' eid = _, H2: get els eid = _ |- _ =>
          rewrite H2 in H1
      end.
      do 7 eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split.
      * (* mq_ed_equiv *)
        unfold mq_ed_equiv in *.
        simpljoin. 
        do 4 eexists.
        split; eauto.
        split; eauto.
        match goal with H: absmsgq _ _ _ = absmsgq _ _ _ |- _ => inverts H end.
        eapply tidls_equiv_pp_preserve2 with (O1 := O) (O2 := O) (O1' := O) (O2' := O'); eauto. 
        eapply prio_preserved_refl; eauto. 
      *
        eapply tidls_equiv_pp_preserve2 with (O1 := O) (O2 := O) (O1' := O) (O2' := O'); eauto. 
        eapply prio_preserved_refl; eauto. 
Qed. 

             
Lemma has_channel_change_dpl:
  forall dpl dpl' kportl chs td td', 
    dpl_same_addr_to_id dpl dpl' ->
    has_channel dpl kportl chs td td' ->
    has_channel dpl' kportl chs td td'. 
Proof.
  introv Ha Hhc.
  unfolds in Ha. 
  unfold has_channel in *.
  destruct Hhc as
    (a & cid & cdstn & dstpaddrs & tp & asrcdp & spcn & spd & spid & sdir 
     & spst & spin & spout & sptt & asrckp & ao & spcn' & spst' & adstkp & dpid 
     & ao' & ao'' & dpcn' & dpst' & adstdp & kpcn & dpd & ddir & dpst & dpin 
     & dpout & dptt & H'').
  simpljoin.
  assert (Hex: exists pcn pd pst pin pout pt,
             get dpl' asrcdp = Some (pcn, pd, spid, sdir, pst, pin, pout, pt)).
  {
    eapply Ha; eauto.
    do 6 eexists; eauto.
  }
  assert (Hex': exists pcn pd pst pin pout pt,
             get dpl' adstdp = Some (pcn, pd, dpid, ddir, pst, pin, pout, pt)).
  {
    eapply Ha; eauto.
    do 6 eexists; eauto. 
  }
  destruct Hex as (pcn0 & pd0 & pst0 & pin0 & pout0 & pt0 & Hex0).
  destruct Hex' as (pcn0' & pd0' & pst0' & pin0' & pout0' & pt0' & Hex0').
  exists a cid cdstn dstpaddrs tp.
  exists asrcdp pcn0 pd0 spid sdir pst0.
  exists pin0 pout0 pt0.
  exists asrckp ao spcn' spst'.
  exists adstkp dpid ao' ao'' dpcn' dpst'.
  exists adstdp pcn0' pd0' ddir pst0'.
  exists pin0' pout0' pt0'.
  
  repeat eexists; eauto. 
Qed.
    
Definition ex_dstprt_in_dom cdstkpl (kportl: if_language.KernelPMod.map) dpl td := 
  exists a' pid a0 cha pcn' kpst,
    In a' cdstkpl /\
      get kportl a' = Some (pid, Some a0, Some cha, pcn', kpst) /\
      exists a pcn pd pst pin pout n msgl,
        addrval_in_dom a td = true /\ 
          get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, QueuePort n msgl).        


Set Nested Proofs Allowed. 

Lemma nfl_send_to_dom_upd_unchanged:
  forall O (* O' *) cst T pc tps cspc pr td t kportl cdstkpl msg dpl dpl' els els' tls tls' chs
         asrc pcn pd srcpid pst pin pout pt kpa a cha pcn' kpst cid cdstn chtp, 
    good_client_code pc -> 
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst O -> 
    ~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom td) ->
    has_post_cap tps cspc (dom_for_prio pr) -> 
    tps_tst_corr O tps -> 
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t -> 
    prt_indom (Vptr asrc) O pr ->    
    get dpl asrc = Some (pcn, pd, srcpid, SourceP, pst, pin, pout, pt) ->
    get kportl kpa = Some (srcpid, Some a, Some cha, pcn', kpst) ->
    get chs cha = Some (cid, cdstn, cdstkpl, chtp) -> 
    dpl_upd kportl cdstkpl msg dpl dpl' ->
    tcbl_upd kportl cdstkpl dpl els tls tls' ->
    ecbl_upd kportl cdstkpl dpl els els' tls ->
    get O abstcblsid = Some (abstcblist tls) -> 
    get O absecblsid = Some (absecblist els) ->
    get O osdomainportid = Some (osdomainport dpl) ->
    get O oskportid = Some (if_language.oskport kportl) -> 
    get O oschannelid = Some (oschannel chs) -> 
    get O cspaceid = Some (capcspace cspc) -> 
    ((forall pr t, task_prio_id O pr t -> dom_for_prio pr = td -> get tls t = get tls' t)
     /\ (forall a, addrval_in_dom a td = true -> get dpl a = get dpl' a)
     /\ (forall a, 
            addrval_in_dom a td = true ->
            (forall wl, get els a = Some (absport, wl) <-> get els' a = Some (absport, wl)))).
Proof.
  introv Hgcli Hrc Hnfl Hhpc Httc Hgct Htpi.
  introv Hpri Hgdp Hgkp Hgch.
  introv Hdu Htu Heu.
  introv Hgtcbs Hgecbs Hgdpl Hgkpl Hgchs Hgcspc (* Hgtcbs' Hgecbs' Hgdpl' *).
  unfolds in Hpri.
  simpljoin.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
        
  assert (Hor: ex_dstprt_in_dom cdstkpl kportl dpl td
               \/ ~ex_dstprt_in_dom cdstkpl kportl dpl td)
    by tauto.
  destruct Hor as [Hexprt | Hnexprt].
  -
    assert (Hhc: has_channel dpl kportl chs (dom_for_prio pr) td).
    {
      unfolds in Hexprt.
      simpljoin. 
      unfolds.
      exists cha cid cdstn cdstkpl chtp.
      exists x pcn pd srcpid SourceP.
      exists pst pin pout pt.
      exists kpa (Some a) pcn' kpst.
      exists x0.
      repeat eexists; eauto.
    }
    lets H__: reachable_chinfo_back Hgcli Hrc; eauto.
    specializes H__; eauto.
    destruct H__ as (dpl0 & Hccfg & Hds).
    lets H__: has_channel_change_dpl Hds Hhc; eauto. 
    assert (Hfl: flowsTo (TaskDom (dom_for_prio pr)) (TaskDom td)).
    {
      eapply comm_flows; eauto. 
    }
    apply Hnfl in Hfl.
    false.
    
  -
    unfold ex_dstprt_in_dom in Hnexprt.
    splits.
    + (* get tls _ = get tls' _ *)
      introv Htpi_ Hd_.
      unfolds in Htu.
      specialize (Htu t0).
      destruct Htu as [Hupdt | Hgteq].
      *
        destruct Hupdt as (Hwait & Hgteq).
        unfold hwait_prt in Hwait.
        destruct Hwait as (
            wl & a_ & a' & pid & pcn_ & pd_ & pst_ & pin_ & pout_ & n &
              msgl & a0 & cha_ & pcn'_ & kpst_ & Hrem).
        destruct Hrem as (Hin & Hgkp_ & Hgdp_ & Hgecb & Hnnil & Hghw).
        apply Classical_Pred_Type.not_ex_all_not with (n:=a') in Hnexprt.
        apply Classical_Pred_Type.not_ex_all_not with (n:=pid) in Hnexprt.
        do 4 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt]. 
        apply Hf in Hin. false.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].
        apply Hf in Hgkp_. false.
        assert (Hinwl: In t0 wl).
        { eapply gethwait_in; eauto. }
        lets H__: qprt_part_consistent td Hgecbs Hgecb Hinwl; eauto.
        assert (Hex: exists pr, task_prio_id O pr t0 /\ dom_for_prio pr = td).
        { eexists; split; eauto. }
        apply H__ in Hex.
        apply Classical_Pred_Type.not_ex_all_not with (n:=a_) in Hnexprt.
        do 7 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt]. 
        apply Hf in Hex. false.
        eapply Hnexprt in Hgdp_; eauto.
        false.
      *
        simpljoin.
        symmetry.
        auto.
    + (* get dpl _ = get dpl' _ *)
      intros a0 Hd_.
      unfolds in Hdu.
      specialize (Hdu a0).
      destruct Hdu as [Hupd | Hnupd].
      * destruct Hupd as (Hprt & Hprtupd).
        unfolds in Hprt.
        destruct Hprt as (
            a' & pid & pcn_ & pd_ & pst_ & pin_ & pout_ & n & msgl & a1 
              & cha_ & pcn'_ & kpst_ & Hrem).
        destruct Hrem as (Hindsts & Hgkp' & Hgdp' & Hlen).
        apply Classical_Pred_Type.not_ex_all_not with (n:=a') in Hnexprt.
        apply Classical_Pred_Type.not_ex_all_not with (n:=pid) in Hnexprt.        
        do 4 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].         
        apply Hf in Hindsts; false.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].
        apply Hf in Hgkp'; false.
        apply Classical_Pred_Type.not_ex_all_not with (n:=a0) in Hnexprt.
        do 7 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].         
        apply Hf in Hd_. false.
        apply Hnexprt in Hgdp'; false.
      * 
        simpljoin.
        symmetry.
        auto.
    + (* get els _ =_ <-> get els' _ = _ *)
      intros a0 Hd_ wl_.
      unfolds in Heu.
      specialize (Heu a0).
      destruct Heu as [Hupd | Hnupd].
      * destruct Hupd as (t' & wl' & Hprt & Hprtupd). 
        unfolds in Hprt.
        destruct Hprt as (
            a' & pid & pcn_ & pd_ & pst_ & pin_ & pout_ & n & msgl & a1 
              & cha_ & pcn'_ & kpst_ & Hrem).
        destruct Hrem as (Hindsts & Hgkp' & Hgdp' & Hlen).        
        apply Classical_Pred_Type.not_ex_all_not with (n:=a') in Hnexprt.
        apply Classical_Pred_Type.not_ex_all_not with (n:=pid) in Hnexprt.        
        do 4 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].         
        apply Hf in Hindsts; false.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].         
        apply Hf in Hgkp'; false.
        apply Classical_Pred_Type.not_ex_all_not with (n:=a0) in Hnexprt.
        do 7 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
        apply Classical_Prop.not_and_or in Hnexprt.
        destruct Hnexprt as [Hf | Hnexprt].         
        apply Hf in Hd_. false.
        apply Hnexprt in Hgdp'; false.
      *
        destruct Hnupd as (Hnex & Hgeq).
        rewrite Hgeq.
        split; auto.
Qed.         
 
Lemma rc_q_send_to_domain_data_equiv:
  forall pc T cst O v v' O0 O0' Of O' act t pr i, 
    good_client_code pc -> 
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst O -> 
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t ->
    ~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) -> 
    q_send_to_domain (v::nil) O0 act (v', Some O0') ->
    prt_indom v O pr -> 
    join O0 Of O ->
    join O0' Of O' ->
    ctid_equiv i O O -> 
    bufs_equiv i O O -> 
    kernel_data_equiv i O O -> 
    has_prtpost_cap O pr -> 
    data_equiv_tskd i cst cst O O'.
Proof.
  introv Hgcli Hrch Hctid Htpi Hflw Hsd Hpid Hjo Hjo'. 
  introv Hctq Hbusq Hkenl Hhascp. 
  assert (Hsd_ := Hsd).
  inverts Hsd.
  destruct H as (dpl & pcn & pd & srcpid & pst & pin & pout & pt & kportl & kpaddr & a & chaddr &
                   pcn' & kpst & chanl & cid & cdstn & cdstkpl & chtp & ibmp & td & msg0 & msgl &
                   els & els' & tls & tls' & dpl' & Hvl & Hdom & Hgdpl & Hkprt & Hgkpt & Hchanl & Hgchal & 
                   Hibf & Hecb' & Htcb' & Hack & Hibm & Hdpud & Hecbud & Htcbud & Hv & Hact & Hsome).
  inverts Hsome.
  inverts Hvl.
  subst.      
  kvext O0 osdomainportid O.
  kvext O0 oskportid O.
  kvext O0 oschannelid O.
  kvext O0 ibufsid O.
  kvext O0 absecblsid O.
  kvext O0 abtcblsid O.
  assert (Hgceq: get O curtid = get O' curtid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto. 
    repeat rewsimp. auto.
  }
  assert (Hgobeq: get O obufsid = get O' obufsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto. 
    repeat rewsimp. auto.        
  }      
  kvext_h Hjo' ibufsid O'.      
  kvext_h Hjo' abtcblsid O'.
  lets Hpp: q_send_to_domain_prio_preserved Hsd_ Hjo Hjo'; eauto. 
  
  unfolds.
  splits.

  - (* ctid_equiv *)
    destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
    unfolds; intros.
    exists t1 t2.
    splits; try congruence.
    introv Htpi1 Htpi2 Hd.
    eapply Hpreq; eauto.
    eapply prio_preserved_tpi; eauto. 

  - (* bufs_equiv *)
    destruct Hbusq as (Hib & Hob).
    unfolds in Hib; simpljoin.
    unfolds in Hob; simpljoin.
    l_rew21_inv1 (get O obufsid).

    unfolds.
    split.
    + 
      unfolds.
      do 2 eexists.
      split; eauto.
      split; eauto.
      unfold dom_cur_tsk in Hack.
      destruct Hack as (t_ & pr_ & Hct & Htpi_ & Hd_).
      kvext O0 curtid O.
      assert (Hteq: t = t_) by congruence.
      subst t_.
      lets Htpi__: tpi_frm_extend Htpi_; eauto.
      specializes Htpi__; eauto.
      lets H__: prio_unique Htpi Htpi__. subst pr_.
      rewrite upd_bufmp_get_neq; auto.
      { introv Htdeqi. subst. false. apply Hflw. apply flows_to_refl. }
    +
      unfolds; intros.
      do 2 eexists; split; eauto. 

  - (* kernel_data_equiv *)
    destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
    unfolds; splits.
    
    * (*kernel_task_equiv*)
      unfolds in Hkenlt; simpljoin.
      do 2 l_rew12_inv2 (get O abtcblsid). 
      unfolds.
      do 2 eexists; splits; eauto.
      introv Hdp. 
      splits.
      ** 
        unfolds in Hpp. unfold prio_preserved_d in Hpp.
        split; introv Hex.
        ***
          destruct Hex as (t_ & Htpi_).
          specialize (Hpp i pr0 t_ Hdp).
          destruct Hpp as (Ha & Hb).
          exists t_. eapply Ha; eauto. 
        ***
          destruct Hex as (t_ & Htpi_).
          specialize (Hpp i pr0 t_ Hdp).
          destruct Hpp as (Ha & Hb).
          exists t_. eapply Hb; eauto. 
      **
        assert (Htcbud_ := Htcbud).
        unfolds in Htcbud.
        introv Hgt1 Hgt2.
        specialize (Htcbud t2).
        
        unfolds in Hhascp. (*has_prtpost_cap*)
        destruct Hhascp as (cspc & tps & td' & Hcsp & Htpserr & Hdim & Hpcap).
        (* lets Hcflw: comm_flows (dom_for_prio pr) (dom_for_prio pr0) dpl kportl chanl tps. *)
        (* specialize (Hcflw cspc).     *)
        assert(Hhpc: has_post_cap tps cspc (dom_for_prio pr)).
        {
          unfolds in Hpcap.
          simpljoin.
          unfolds.
          do 2 eexists; splits; eauto.
        }        
        lets H__: nfl_send_to_dom_upd_unchanged Hflw Hhpc; eauto. 
        specializes H__; eauto. 
        destruct H__ as (Htt' & _ & _).
        assert (Htpi2: task_prio_id O' pr0 t2).
        { unfolds. do 5 eexists. split; eauto. }
        lets Htpi20: prio_preserved_tpi Htpi2 Hpp; eauto.
        specialize (Htt' pr0 t2).
        specializes Htt'; eauto.
        rewrite Hgt2 in Htt'.
        match goal with H: forall _: priority, _ -> _ |- _ => lets Hteq0: H Hdp end.
        destruct Hteq0 as (Hiff & Ha).
        eapply Ha; eauto.
          
    * (* kernel_mq_equiv *) 
      unfolds.
      unfolds in Hkernlq.
      simpljoin.
      l_rew12_inv2 (get O absmqattrid).
      assert (Hgeq: get O absmqattrid = get O' absmqattrid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.                  
      }
      l_rew12_inv2 (get O absmqattrid).
      do 2 eexists.
      split; eauto.
      split; eauto.
      introv Hd.
      split.
      ** split; auto.
      ** introv Hg1 Hg2.
         rewrite Hg1 in Hg2; inverts Hg2.
         match goal with
           H: forall _, mqidx_in_dom _ _ = _ -> _ |- _ =>
             lets H__: H Hd
         end.
         destruct H__ as (Hiff & Ha).
         specializes Ha; eauto.
         kvext_h Hjo' absecblsid O'.
         eapply mq_equiv_ecbl_upd; eauto.

    * (* ports_equiv *) 
      
      unfolds in Hhascp. (*has_prtpost_cap*)
      destruct Hhascp as (cspc & tps & td' & Hcsp & Htpserr & Hdim & Hpcap).
      lets Hcflw: comm_flows (dom_for_prio pr) i dpl kportl chanl tps.
      specialize (Hcflw cspc).    
      assert(Hhpc: has_post_cap tps cspc (dom_for_prio pr)).
      {
        unfolds in Hpcap.
        simpljoin.
        unfolds.
        do 2 eexists; splits; eauto.
      }

      lets H__: nfl_send_to_dom_upd_unchanged Hflw Hhpc; eauto. 
      specializes H__; eauto. 
      destruct H__ as (_ & Hdpdp' & Helel').
      unfolds.
      kvext_h Hjo' osdomainportid O'.
      kvext_h Hjo' absecblsid O'.
      do 4 eexists.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto. 
      introv Hd.
      split. eapply Hdpdp'; eauto.
      split.
      split; introv Hex.
      {
        destruct Hex as (tls_ & Hgecb).
        specializes Helel'; eauto.
        eapply Helel' in Hgecb.
        eexists; eauto. 
      }
      {
        destruct Hex as (tls_ & Hgecb).
        specializes Helel'; eauto.
        eapply Helel' in Hgecb.
        eexists; eauto. 
      }
      introv Hge Hge'.
      specializes Helel'; eauto.
      eapply Helel' in Hge'; eauto.
      rewrite Hge in Hge'. inverts Hge'.
      eapply tidls_equiv_pp_preserve2 with (O1:=O) (O2:=O) (O1':=O) (O2':=O'); eauto.
      apply tidls_equiv_refl.
      apply prio_preserved_refl.
      * 
     
      (* buffer_equiv *)
      unfolds.
      unfold buffer_equiv in *.
      simpljoin.
      kvext_h Hjo' absecblsid O'.
      do 2 eexists.
      splits;eauto.
      intros.






splits.
split;intros.
simpljoin.
      unfolds in Hecbud.
      specialize (Hecbud eid).
      destruct Hecbud as [Hupd | Hnupd].
       simpljoin.
        unfold hwait_prt in *.
        simpljoin.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        rewrite H18 in H13;inverts H13.
        eauto.
       simpljoin.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        do 2 eexists.
        rewrite H13 in H15.
        eauto.

        simpljoin.
      unfolds in Hecbud.
      specialize (Hecbud eid).
      destruct Hecbud as [Hupd | Hnupd].
       simpljoin.
        unfold hwait_prt in *.
        simpljoin.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        do 2 eexists.
        eauto.

        simpljoin.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        do 2 eexists.
        rewrite H13 in H15.
        eauto.
       
      intros.
      lets Hecbud1: Hecbud.
      unfolds in Hecbud.
      specialize (Hecbud eid).
      destruct Hecbud as [Hupd | Hnupd].
       simpljoin.
        unfold hwait_prt in *.
        simpljoin.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        lets Hbfe: buffer_ecb H12 H3.
        simpljoin.
        rewrite H19 in H7.
        inverts H7.
        simpljoin.
        rewrite H16 in H14.
        rewrite H13 in H14;inverts H14.

        unfolds in Hkernlq.
        simpljoin.
        split.
        l_rew21_inv1 (get O absecblsid).
        l_rew21_inv1 (get O absecblsid).
        unfolds.
        lets Hbfe: buffer_ecb H12 H3.
        simpljoin.
        rewrite H13 in H7;inverts H7.
        do 4 eexists.
        splits;eauto.
        eapply tidls_equiv_pp_preserve2 with (O1:=O) (O2:=O) (O1':=O) (O2':=O'); eauto.
        apply tidls_equiv_refl.
        apply prio_preserved_refl.
        eapply tidls_equiv_pp_preserve2 with (O1:=O) (O2:=O) (O1':=O) (O2':=O'); eauto.
        apply tidls_equiv_refl.
        apply prio_preserved_refl.

    * (* cap_equiv *)
      assert (get O cspaceid = get O' cspaceid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.          
      }
      assert (get O absmqattrid = get O' absmqattrid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.                  
      }    
 
      lets H__: cspceq_cap_equiv O O' Hcapq Hkernlq; eauto.  

  - (*client_data_equiv *)
    eapply client_data_equiv_pp; eauto.

Qed. 

Lemma store_msg_data_equiv_tskd_preserve:
forall i pr O v0 O0 act v O'0 Of O' cst' t,
i <> dom_for_prio pr ->
prt_indom v O pr ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
ctid_equiv i O O ->
bufs_equiv i O O ->
kernel_data_equiv i O O ->
client_data_equiv i cst' cst' O O ->
store_msg (v :: nil) O0 act (v0, Some O'0)->
join O0 Of O ->
join O'0 Of O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
  introv Hi_neq Hasrt Htpi Hctid Hctq Hbusq Hkenl Hdata Hspec.
  introv Hj1 Hj2.
  inverts Hspec.
  destruct H as (dpl & pcn & pd & pid & pst & pin & pout & n &
                               msgl & ibmp & td & m & dpl' & Hvl & Hdom & Hgetdp &
                               Hibf & Hdck & Hibmp & Hdpl' & Hact & Hsome).
  inverts Hsome.

  assert (get O osdomainportid = Some (osdomainport dpl)) as Hdprt.
  eapply join_get_get_l;eauto.
  assert (get O ibufsid = Some (ibufs ibmp)) as Hibfs.
  eapply join_get_get_l;eauto.

  assert (O'=set (set O osdomainportid (osdomainport dpl'))
           ibufsid (ibufs (upd_bufmp ibmp td msgl))).
  eapply join_get_set_eq_2;eauto.
  clear Hibf Hdom.
  remember O as Ox.
  clear HeqOx.
  subst.
  match goal with H: _ :: nil = _ :: nil |- _ => inverts H end.

  assert(Hdmct: dom_cur_tsk Ox td) by (eapply dom_cur_tsk_join_get_l; eauto).
  clear Hdck.
  splits.

  (*ctid_equiv*)
  destruct Hctq as (t1 & t2 & Hct1 & Hct2 & Hpreq).
  unfolds; intros.
  exists t1 t2.
  splits; eauto.
  do 4 try (rewrite set_a_get_a'; try intro; tryfalse).
  eauto.
  
  intros.
  eapply Hpreq; eauto.
  unfold task_prio_id in *.
  simpljoin.
  match goal with
     H: get (set _ _ _) _ = _ |- _ => 
        rewrite set_a_get_a' in H; eauto end; try intro; tryfalse.
  
  (*bufs_equiv*)
  destruct Hbusq as (Hib & Hob).
  unfolds in Hib; simpljoin.
  unfolds in Hob; simpljoin.
  
  unfolds; split.
  unfolds;
  intros.
  do 2 l_rew21_inv1 (get Ox ibufsid).
  exists x0.
  
  exists (upd_bufmp x0 td msgl).
  splits; eauto.
  rewrite set_a_get_a; eauto.
  
  unfolds in Hdmct; simpljoin.
  l_rew21_inv1 (get Ox curtid).
  assert(He: x4 = pr) by (eapply prio_unique; eauto).
  subst.
  rewrite upd_bufmp_get_neq; auto.
  
  (*obufs_equiv*)
  unfolds; intros.
  do 2 eexists; split; eauto;
  do 4 try (rewrite set_a_get_a'; try intro; tryfalse; eauto).
  
  (*kernel_data_equiv*)
  destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
  unfolds; splits.
  
  (*kernel_task_equiv*)
  unfolds in Hkenlt; simpljoin.
  { 
  unfolds.
  do 2 eexists; splits; eauto.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse; eauto).

  intros.
  splits.
  splits; intros;
  match goal with 
  H: exists _, task_prio_id _ _ _ |- _ =>
  destruct H as (t1 & Htkid) end;
  exists t1;
  unfold task_prio_id in *.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse).

  simpljoin.
  do 2 l_rew21_inv1 (get Ox abtcblsid).
  do 5 eexists; splits; eauto.
  simpljoin.
  do 2 try (match goal with
     H: get (set _ _ _) _ = _ |- _ => 
        rewrite set_a_get_a' in H; eauto end; try intro; tryfalse).
  do 5 eexists; splits; eauto.

  intros.
  l_rew21_inv1 (get Ox abtcblsid).
  assert(t1 = t2).
eapply tid_unique; eauto; unfolds; do 5 eexists; splits; eauto.
subst.
rewrite H6 in H5; inverts H5; eauto.
 }
  
  (* kernel_mq_equiv *)
  { 
  unfolds in Hkernlq;simpljoin.
  unfolds.
  do 2 eexists; splits; eauto.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse; eauto).

  intros.
  splits.
  splits; intros; auto. 
  l_rew21_inv1 (get Ox absmqattrid).

  intros.
  (*mq_equiv*)
  unfolds.
  eapply H3 in H4; eauto.
  simpljoin.
  eapply H6 in H; eauto.
  match goal with 
  H: mq_equiv _ _ _ _ _ |- _ =>
  unfolds in H end; simpljoin.
  do 8 eexists; splits; eauto.
  match goal with 
  H: _ \/ _ \/ _ |- _ =>
  destruct H as [Hnull | [ Hhold | Heid]] end; simpljoin.
  left; eauto.
  right; left; eauto.
  l_rew21_inv1 (get Ox absecblsid).
  do 2 right.
  exists x9.
  do 6 eexists; splits; eauto.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse; eauto).

  (*mq_ed_equiv*)
  unfolds.
  match goal with 
  H: mq_ed_equiv _ _ _ _ |- _ =>
  unfolds in H end; simpljoin.
  do 4 eexists; splits; eauto.

  (*tidls_equiv*)
  unfolds.
  unfold tidls_equiv in H8; simpljoin.
  splits; eauto.
  intros.
  splits; intros; simpljoin.
  eexists; splits; eauto;
  unfold task_prio_id in *; simpljoin.
  rewrite set_a_get_a'; try intro; tryfalse; eauto.
  do 5 eexists; eauto.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse; eauto).
  unfold task_prio_id in *.
  simpljoin.
  do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
  eexists; splits; eauto;
  do 5 eexists; eauto.

  (*tidls_equiv_ws*)
  unfold tidls_equiv in *; simpljoin.
  splits; eauto.
  intros.
  splits; intros; unfold task_prio_id in *; simpljoin;
  [do 2 try (rewrite set_a_get_a'; try intro; tryfalse; eauto) | 
  do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse ];
  eexists; splits; eauto;
  do 5 eexists; eauto. }

  (*ports_equiv*)
  unfold ports_equiv in *; simpljoin.
  l_rew21_inv1 (get Ox osdomainportid).
  l_rew21_inv1 (get Ox absecblsid).
  rewrite set_a_get_a'; try intro; tryfalse.
  rewrite set_a_get_a; eauto.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse).
  do 4 eexists; splits; eauto.

  intros.
  casetac a x Heq Hneq;
  subst.
  unfolds in Hasrt; simpljoin.
  match goal with
  H: Vptr _ = Vptr _ |- _ => inverts H end.
  do 2 match goal with 
  H: addrval_in_dom _ _ = _ |- _ => 
  unfolds in H end.
  destruct x3.
  match goal with 
  H: addr_in_dom _ _ = _ |- _ => 
  eapply dom_disj_addrs in H end; eauto; tryfalse. 
  rewrite set_a_get_a'; eauto. 

  splits; eauto.
  splits; intro; eauto.

(* tidls_equiv *)
  intros.
  eapply H5 in H3; eauto.
  unfold tidls_equiv in *.
  destruct H3 as (Hlen & Hsl).
  splits; eauto.
  intros pr0.
  splits; intros Hg.
  eapply Hsl in Hg; eauto.
  destruct Hg as (tk & Hin & Htkid).
  exists tk.
  splits; eauto.
  unfold task_prio_id in *.
  simpljoin.
  do 2 try (rewrite set_a_get_a' ; try intro; tryfalse).
  do 5 eexists; splits; eauto.  

  eapply Hsl.
  simpljoin.
  unfold task_prio_id in *.
  simpljoin.
  do 2 match goal with
    H: get (set _ _ _) _ = _ |- _ => 
      rewrite set_a_get_a' in H end; try intro; tryfalse. 
  eexists; splits; eauto.
  do 5 eexists; splits; eauto.

  (* buffer_equiv *)

  unfold buffer_equiv in *.
rewrite set_a_get_a' ; try intro; tryfalse.
rewrite set_a_get_a' ; try intro; tryfalse.
simpljoin.
do 2 eexists; splits; eauto.
intros e0 Hb.
splits.
split;intros;eauto.
intros.
rewrite H3 in H4;inverts H4.
rewrite H in H1;inverts H1.

lets Hmqed : buffer_ecb Hb H.
simpljoin.
rewrite H3 in H1;inverts H1.
split.
unfolds.
do 4 eexists.
splits;eauto.
(* tidls_equiv *)
unfold tidls_equiv in *.

splits; eauto.
intros pr0.
splits; intros Hg.
simpljoin.
eexists x5.
split;eauto.
unfolds in H4.
simpljoin.
unfolds.
do 5 eexists.
rewrite set_a_get_a'; try intro;tryfalse.
rewrite set_a_get_a'; try intro;tryfalse.
split;eauto.
simpljoin.
eexists x5.
split;eauto.
unfolds in H4.
simpljoin.
rewrite set_a_get_a' in H4; try intro;tryfalse.
rewrite set_a_get_a' in H4; try intro;tryfalse.
unfolds.
do 5 eexists.
split;eauto.
(* tidls_equiv *)
unfold tidls_equiv in *.

splits; eauto.
intros pr0.
splits; intros Hg.
simpljoin.
eexists x5.
split;eauto.
unfolds in H4.
simpljoin.
unfolds.
do 5 eexists.
rewrite set_a_get_a'; try intro;tryfalse.
rewrite set_a_get_a'; try intro;tryfalse.
split;eauto.
simpljoin.
eexists x5.
split;eauto.
unfolds in H4.
simpljoin.
rewrite set_a_get_a' in H4; try intro;tryfalse.
rewrite set_a_get_a' in H4; try intro;tryfalse.
unfolds.
do 5 eexists.
split;eauto.

  (* cap_equiv *)
  unfold cap_equiv in *.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse).
  simpljoin.
  do 2 eexists; splits; eauto.

  intros pr0 Hd.
  lets Hm: H2 Hd.
  l_rew21_inv1 (get Ox cspaceid).
  destruct Hm as (Hcap1 & Hcap2).
  splits; eauto.

  intros idx Hdom.
  lets Hs: Hcap2 Hdom.
  destruct Hs as (Hs1 & Hs2).
  splits.
  splits; intros Hs;
  unfold mq_ptr in *.
  do 2 try (rewrite set_a_get_a'; try intro; tryfalse).
  auto.
  do 2 try (rewrite set_a_get_a' in Hs; try intro; tryfalse).
  auto.

  intros.
  eapply Hs2; eauto.
  unfold mq_ptr in *.
  do 2 try (rewrite set_a_get_a' in H3; try intro; tryfalse).
  auto.

  (* client_data_equiv *)
  unfold client_data_equiv in *.
  simpljoin.
  do 6 eexists; splits; eauto.

  unfold local_envs_equiv in *.
  intros.
  eapply H2; eauto.
  unfold task_prio_id in *.
  do 2 try (rewrite set_a_get_a' in H1; try intro; tryfalse; auto).
Qed.


Lemma qportpost_nabt_spec_step_data_equiv_tskd_preserve :
  forall O cd  n vl sd cd' O' act ke ks t T i pr pc cst',
    good_client_code pc -> 
    good_task_code T ->
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
    ~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
    task_prio_id O pr t ->
    get O curtid = Some (oscurt t) ->
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    qportpost vl <> ABORT -> 
    nth_error (get_all_succs (qportpost vl)) n = Some cd ->
    spec_step sd cd O cd' O' act ->
    i <> dom_for_prio pr ->
    O <> O' ->
    data_equiv_tskd i cst' cst' O O'.
Proof. 
  introv Hgcli Hgdt Hrch Hflw Htpi Hctid Hgett Hnabt Hnth.
  introv Hstep Hi_neq HO_neq.
  lets Hasrt: rch_hasrt_sat Hrch Hgett Htpi.
  remember vl as recv_vl.
  do 3 try (destruct recv_vl; simpl in Hnabt;tryfalse);
  try destruct v0; simpl in Hnabt; tryfalse;
  try destruct recv_vl; simpl in Hnabt; tryfalse.
  clear Hnabt.

  (* n = 0 *)
  destruct n; [ my_succs_solver_same_absdata | idtac].
  (* n = 1 *)
  destruct n; [ my_succs_solver_same_absdata | idtac].
  (* n = 2 *)
  destruct n; [ my_succs_solver_same_absdata | idtac].
  (* n = 3 *)
  destruct n; [ my_succs_solver_same_absdata | idtac].
  (* n = 4 *)
  lets Hgdcd: Hgdt Hgett.
  unfolds in Hgdcd. simpl in Hgdcd.
  destruct Hgdcd as (Hgde' & Hgdks').
  lets H': Hstep.
  protect H'.
  protect Hgde'.
  assert(HO:data_equiv_tskd i cst' cst' O O).
  { eapply data_equiv_tskd_same_preserve; eauto. }
  unfolds in HO.
  destruct HO as (Hctq & Hbusq & Hkenl & Hdata).
  destruct n; [ my_succs_solver_same_absdata | idtac].
  
  simpl in Hasrt.
  - (*q_send_to_domain*)
    destruct Hasrt as (Hprtin & Hhascp).
    lets H__: rc_q_send_to_domain_data_equiv Hrch Hflw; eauto.

  - (*q_send_to_domain*)
    solve_endabt.
    
  - (*store_msg*)
    simpl in Hasrt; simpljoin.
    eapply store_msg_data_equiv_tskd_preserve; eauto.

  - (* store_msg *)
    solve_endabt.

  -
    (* n = 5 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 6 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 7 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 8 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 9 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 10 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse.

Qed.


