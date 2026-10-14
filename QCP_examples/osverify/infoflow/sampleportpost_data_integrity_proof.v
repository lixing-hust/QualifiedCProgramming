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
      exists a pcn pd pst pin pout mopt,
        addrval_in_dom a td = true /\ 
          get dpl a = Some (pcn, pd, pid, DestinationP, pst, pin, pout, SamplePort mopt).

Set Nested Proofs Allowed. 

Lemma rc_sample_send_to_domain_data_equiv:
  forall pc T cst O v v' O0 O0' Of O' act t pr i, 
    good_client_code pc -> 
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst O -> 
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t ->
    ~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) -> 
    sample_send_to_domain (v::nil) O0 act (v', Some O0') ->
    prt_indom v O pr -> 
    join O0 Of O ->
    join O0' Of O' ->
    ctid_equiv i O O -> 
    bufs_equiv i O O -> 
    kernel_data_equiv i O O -> 
    has_prtpost_cap O pr -> 
    i <> dom_for_prio pr ->
    data_equiv_tskd i cst cst O O'.
Proof.
  introv Hgcli Hrch Hctid Htpi Hflw Hsd Hpid Hjo Hjo'. 
  introv Hctq Hbusq Hkenl Hhascp Hi_neq. 
  assert (Hsd_ := Hsd).
  inverts Hsd.
  destruct H as (dpl & pcn & pd & srcpid & pst & pin & pout & pt & kportl & kpaddr & a & chaddr &
                   pcn' & kpst & chanl & cid & cdstn & cdstkpl & chtp & ibmp & td & msg0 & msgl &
                   dpl' & Hvl & Hdom & Hgdpl & Hkprt & Hgkpt & Hchanl & Hgchal & 
                   Hibf & Hack & Hibm & Hsu & Hv & Hact & Hsome).
  inverts Hsome.
  inverts Hvl.
  subst.      
  kvext O0 osdomainportid O.
  kvext O0 oskportid O.
  kvext O0 oschannelid O.
  kvext O0 ibufsid O.
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
  lets Hpp: sample_send_to_domain_prio_preserved Hsd_ Hjo Hjo'; eauto. 
  
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
      { introv Htdeqi. subst. false. }
    +
      unfolds; intros.
      do 2 eexists; split; eauto. 

  - (* kernel_data_equiv *)
    destruct Hkenl as (Hkenlt & Hkernlq & Hportq & Hcapq).
    unfolds; splits.
    
    * (*kernel_task_equiv*)
      unfolds in Hkenlt; simpljoin.
      assert (Hgeq: get O abtcblsid = get O' abtcblsid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.                  
      }
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
        specialize (H8 pr0).
        apply H8 in Hdp.
        destruct Hdp.
        auto.
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
         assert (Hgeq: get O absecblsid = get O' absecblsid).
         {
           lets H_: join_get_same_l Hjo Hjo'; eauto.
           repeat rewsimp. auto.                  
         }
         unfolds in Ha.
         unfolds.
         simpljoin.
         do 8 eexists. splits; eauto.
         destruct H11 as [H11 | [H11 | H11]]; eauto.
         right; right.
         simpljoin.
         do 2 l_rew12_inv2 (get O absecblsid).
         rewrite H13 in H14.
         inverts H14.
         do 7 eexists. splits; eauto.
         unfolds in H15.
         unfolds.
         simpljoin.
         inverts H12.
         do 4 eexists. splits; eauto.
         eapply tidls_equiv_pp_preserve2; eauto. eapply prio_preserved_refl.
         eapply tidls_equiv_pp_preserve2; eauto. eapply prio_preserved_refl.

    * (* ports_equiv *) 
      unfolds in Hportq.
      unfolds.


      kvext_h Hjo' osdomainportid O'.
      simpljoin.
      do 2 l_rew12_inv2 (get O osdomainportid).
      assert (Hgeq: get O absecblsid = get O' absecblsid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.                  
      }
      do 2 l_rew12_inv2 (get O absecblsid).
      do 4 eexists. splits; eauto. 
      intros.
      unfolds in Hsu.
      specialize (Hsu a0).
      destruct Hsu.
      {
      
  assert (Hor: ex_dstprt_in_dom cdstkpl kportl dpl i
               \/ ~ex_dstprt_in_dom cdstkpl kportl dpl i)
    by tauto.
  destruct Hor as [Hexprt | Hnexprt].
  -

    assert (Hhc: has_channel dpl kportl chanl (dom_for_prio pr) i).
    {
      unfolds in Hexprt.
      simpljoin. 
      unfolds.
      exists chaddr cid cdstn cdstkpl chtp.
      exists x pcn pd srcpid SourceP.
      exists pst pin pout pt.
      exists kpaddr (Some a) pcn' kpst.
      exists x0.
      unfolds in Hpid. simpljoin. inverts H19.
      repeat eexists; eauto.
    }
    unfolds in Hhascp. simpljoin.
    lets H__: reachable_chinfo_back Hgcli Hrch; eauto.
    specializes H__; eauto.
    destruct H__ as (dpl0 & Hccfg & Hds).
    lets H__: has_channel_change_dpl Hds Hhc; eauto. 
    assert (Hfl: flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i)).
    {
      eapply comm_flows; eauto. 
    }
    tryfalse.
  -
    unfold ex_dstprt_in_dom in Hnexprt.
    simpljoin.
    apply Classical_Pred_Type.not_ex_all_not with (n:=x0) in Hnexprt.
    apply Classical_Pred_Type.not_ex_all_not with (n:=x5) in Hnexprt.
    do 4 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
    apply Classical_Prop.not_and_or in Hnexprt.
    destruct Hnexprt as [Hf | Hnexprt]. 
    apply Hf in H10. false.
    apply Classical_Prop.not_and_or in Hnexprt.
    destruct Hnexprt as [Hf | Hnexprt].
    apply Hf in H12. false.
    apply Classical_Pred_Type.not_ex_all_not with (n:=a0) in Hnexprt.
    do 6 eapply Classical_Pred_Type.not_ex_all_not in Hnexprt.
    apply Classical_Prop.not_and_or in Hnexprt.
    destruct Hnexprt.
    apply H15 in H. false.
    apply H15 in H13. false.
      }
      {
        simpljoin.
        splits; eauto.
        split; eauto.
        intros.
        unfolds.
        rewrite H13 in H14.
        inverts H14.
        split; eauto.
        intros.
        split.
        intros. 
        simpljoin. eexists. split. eauto.
        eapply prio_preserved_tpi; eauto.
        eapply prio_preserved_sym; eauto.
        intros. 
        simpljoin. eexists. split. eauto.
        eapply prio_preserved_tpi; eauto.
      }
    * 
     
      (* buffer_equiv *)
      unfolds.
      unfold buffer_equiv in *. 
      simpljoin.
      assert (Hgeq: get O absecblsid = get O' absecblsid).
      {
        lets H_: join_get_same_l Hjo Hjo'; eauto.
        repeat rewsimp. auto.
      }
      do 2 l_rew12_inv2 (get O absecblsid). 
      do 2 eexists.
      splits;eauto.
      intros.
      specialize (H7 eid).
      apply H7 in H6.
      simpljoin.
      splits; eauto.
      intros.
      specialize (H8 ed1 ed2 ws1 ws2).
      specializes H8; eauto.
      destruct H8.
      split.
      unfolds in H8.
      unfolds.
      simpljoin.
      do 4 eexists. splits; eauto.
      eapply tidls_equiv_pp_preserve2; eauto. eapply prio_preserved_refl.
      eapply tidls_equiv_pp_preserve2; eauto. eapply prio_preserved_refl.

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

Lemma sampleportpost_nabt_spec_step_data_equiv_tskd_preserve :
  forall O cd  n vl sd cd' O' act ke ks t T i pr pc cst',
    good_client_code pc -> 
    good_task_code T ->
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
    ~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
    task_prio_id O pr t ->
    get O curtid = Some (oscurt t) ->
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    sampleportpost vl <> ABORT -> 
    nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
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
  - (*sample_send_to_domain*)
    destruct Hasrt as (Hprtin & Hhascp).
    lets H__: rc_sample_send_to_domain_data_equiv Hrch Hflw; eauto.

  - (*sample_send_to_domain*)
    solve_endabt.
    
  -
    (* n = 5 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    (* n = 6 *)
    destruct n; [ my_succs_solver_same_absdata | idtac].
    simpl in Hnth; rewrite nth_error_nil in Hnth; tryfalse.
Qed.
