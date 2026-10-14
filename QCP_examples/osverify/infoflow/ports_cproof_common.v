
Require Import FunctionalExtensionality.
Require Import base_tac. 
Require Import memory. 

Require Import math_auto. 
Require Import seplog_lemmas. 

Require Import if_language.
Require Import if_opsem.
Require Import prt_apispecs. 
Require Import osspecs. 
Require Import properties.

Require Import if_assms.
Require Import sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas. 
Require Import spec_aux_defs. 
Require Import confidentiality_tactics.
Require Import confidentiality_lemmas.
Require Import equiv_prop. 

Require Import hasrt_sat_preserve. 

Set Keyed Unification. 

Lemma upd_bufmp_get_eq:
  forall bmp d ms, 
    upd_bufmp bmp d ms d = ms.
Proof.
  intros.
  unfolds.
  int auto.
Qed.

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

Lemma sskp_Oeq: 
  forall vl O act v O',
    spec_skip_step vl O act (v, Some O') -> 
    O = O'. 
Proof.
  introv Hstp.
  unfolds in Hstp.
  simpljoin.
  congruence. 
Qed. 

Lemma sskp_veq:
  forall vl v O O' act, 
    spec_skip_step vl O act (v, Some O') -> 
    v = None. 
Proof.
  introv Hstp.
  unfolds in Hstp.
  simpljoin.
Qed.

Lemma port_indomainport_frm_preserve:      
  forall v O0 Of O, 
    port_indomainport v O0 -> 
    join O0 Of O ->
    port_indomainport v O.
Proof.
  introv Hpi Hjo.
  unfold port_indomainport in *.
  destruct v; tryfalse.
  simpljoin.
  do 8 eexists.
  split; eauto.
  eapply join_get_get_l; eauto. 
Qed.

Lemma prts_equiv_wrongdom_impl:
  forall O1 O2 vprt pr t1 t2,
    ports_equiv (dom_for_prio pr) O1 O2 ->
    (* data_equiv_schd O1 O2 ->  *)
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    has_port vprt O1 pr ->
    has_port vprt O2 pr -> 
    wrong_dom O1 vprt ->
    wrong_dom O2 vprt. 
Proof.
  introv Hpe (* Hsche *) Hg1 Hg2 Htpi1 Htpi2 Hhp1 Hhp2 Hwd.
  unfold wrong_dom in *.
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  (* lets H__: prt_dom_correct H1 H2; eauto. *)
  unfold dom_cur_tsk in *.
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  apply2_rev (task_prio_id O1) (task_prio_id O1) prio_unique.
  unfold has_port in *.
  destruct Hhp1 as [ | Hhp1]; tryfalse.
  destruct Hhp2 as [ | Hhp2]; tryfalse.
  unfold port_indomainport in *.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  do 11 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split. do 2 eexists. split; eauto.
  rewrite H11 in H2. inverts H2.
  match goal with
    |- ?e = false => assert (Hcs: e = true \/ e = false); [destruct e; auto | idtac]
  end.
  destruct Hcs as [Ht | Hf]; auto.
  rewrite <- H3 in *.
  lets H__: prt_dom_correct H10 H12.
  assert (Heq: dom_for_prio pr = $Z.of_nat x22).
  {
    clear -Ht.
    lets H0_: Int.eq_spec (dom_for_prio pr) ($ Z.of_nat x22).
    rewrite Ht in H0_. auto.
  }
  rewrite <- Heq in H__.
  lets Hdeq: H8 H__.
  destruct Hdeq as (Hgeteq & _).
  rewrite H11 in Hgeteq. rewrite H12 in Hgeteq.
  inverts Hgeteq.
  false. 
Qed. 

Lemma has_port_ptr:
  forall v O pr, 
    has_port v O pr ->
    v <> Vnull ->
    exists a, v = Vptr a. 
Proof.
  introv Hhp Hnn.
  unfold has_port in Hhp.
  destruct Hhp as [Hf | Hpi]; tryfalse.
  unfolds in Hpi.
  destruct v; tryfalse.
  eexists; eauto. 
Qed.

Lemma nwrong_dom_dest0:
  forall O prt, 
    ~wrong_dom O prt ->
    forall a dpl pcn pd pid pdir pst pin pout pt pr t,
      prt = Vptr a ->
      get O osdomainportid = Some (osdomainport dpl) ->
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
      get O curtid = Some (oscurt t) ->
      task_prio_id O pr t ->
      Int.eq (dom_for_prio pr) ($ Z.of_nat pd) = true.
Proof.
  introv Hnd Hptr Hdpl Hdp Hct Htpi.
  cut (~ Int.eq (dom_for_prio pr) ($ Z.of_nat pd) = false).
  {
    introv Hn.
    destruct (Int.eq (dom_for_prio pr) ($ Z.of_nat pd)).
    auto. false. 
  }
  introv Hfalse.
  apply Hnd.
  unfold task_prio_id in *.
  simpljoin. 
  unfolds.
  repeat eexists; eauto.
Qed.         

Lemma nwrong_dom_dest:
  forall O prt, 
    ~wrong_dom O prt ->
    forall a dpl pcn pd pid pdir pst pin pout pt pr t,
      prt = Vptr a ->
      get O osdomainportid = Some (osdomainport dpl) ->
      get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) ->
      get O curtid = Some (oscurt t) ->
      task_prio_id O pr t ->
      addrval_in_dom a (dom_for_prio pr) = true. 
Proof.
  introv Hnd Hptr Hdpl Hdp Hct Htpi.
  lets H__: nwrong_dom_dest0.
  specializes H__; eauto.
  assert (Hrw: dom_for_prio pr = $ Z.of_nat pd).
  {
    lets H'__: Int.eq_spec (dom_for_prio pr) ($ Z.of_nat pd). 
    rewrite H__ in H'__. auto. 
  }
  rewrite Hrw.
  eapply prt_dom_correct; eauto.
Qed.

Lemma prts_equiv_wrong_core_impl: 
  forall a O1 O2 vprt t1 t2 pr, 
    ~ wrong_dom O1 vprt ->
    vprt = Vptr a -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    has_port vprt O1 pr ->
    has_port vprt O2 pr -> 
    wrong_core O1 vprt ->
    wrong_core O2 vprt.
Proof.
  introv Hnwd Ha Hpe Hct1 Hct2 Htpi1 Htpi2 Hhp1 Hhp2 Hwc1.
  unfold wrong_core in Hwc1.
  simpljoin.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end. 
  lets H__: nwrong_dom_dest Hnwd. 
  specializes H__; eauto.
  unfold has_port in Hhp2.
  destruct Hhp2 as [ | Hpi2]; tryfalse.
  unfolds in Hpi2.
  simpljoin.
  unfolds.
  do 10 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  unfolds in Hpe.
  simpljoin.
  specialize (H8 x H__).
  destruct H8 as (Heq & _).
  l_rew21_inv1 (get O1 osdomainportid).
  l_rew21_inv1 (get O2 osdomainportid).
  false.
  match goal with H: _ <> _ |- _ => apply H end.
  rewrite H1 in Heq. rewrite H3 in Heq.
  inverts Heq.
  auto. 
Qed.       

Lemma prts_equiv_orcond_impl :
  forall pr O1 O2 vprt t1 t2 a, 
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 -> 
    has_port vprt O1 pr ->
    has_port vprt O2 pr ->
    vprt = Vptr a -> 
    (not_port O1 vprt \/ wrong_core O1 vprt \/ wrong_dom O1 vprt) ->
    (not_port O2 vprt \/ wrong_core O2 vprt \/ wrong_dom O2 vprt). 
Proof.
  introv Hpe Hct1 Hct2 Htpi1 Htpi2 Hhp1 Hhp2 Hptr Hor1.
  assert (Hor: wrong_dom O1 vprt \/ ~wrong_dom O1 vprt).
  { tauto. }
  destruct Hor as [Hwd | Hnwd].
  - right; right.
    eapply prts_equiv_wrongdom_impl; eauto. 
  - destruct Hor1 as  [Hnp1 | [Hwc1 | Hwd1]].
    unfold has_port in Hhp1.
    unfold not_port in Hnp1.
    simpljoin.
    destruct Hhp1 as [Hff | Hid].
    + tryfalse.
    + match goal with H: Vptr _ = Vptr _ |- _ => inverts H end. 
      unfold port_indomainport in Hid.
      simpljoin.
      lets H__: prt_ecb_consistent.
      specializes H__; eauto. 
      match goal with H: context [osdomainport ?x] |- _ => rename x into dpl end.
      assert (Hex: exists dp, get dpl x = Some dp).
      { eexists; eauto. }
      eapply H__ in Hex.
      apply H1 in Hex. inverts Hex.
    + right; left.
      eapply prts_equiv_wrong_core_impl; eauto.
    + false. 
Qed.

Lemma ncond_dest_wd: 
  forall O v, 
    ~ (not_port O v \/ wrong_core O v \/ wrong_dom O v) ->
    ~wrong_dom O v. 
Proof.
  introv Hno.
  intuition.
Qed.   

Lemma nwd_prt_indom: 
  forall O v t pr, 
    ~ (not_port O v \/ wrong_core O v \/ wrong_dom O v) ->
    has_port v O pr ->
    v <> Vnull -> 
    get O curtid = Some (oscurt t) ->
    task_prio_id O pr t -> 
    prt_indom v O pr. 
Proof.
  introv Hnor Hhp Hnn Hct Htpi.
  apply ncond_dest_wd in Hnor.
  lets H__: has_port_ptr.
  specializes H__; eauto.
  destruct H__ as (a & Hv).
  destruct Hhp as [Hf | H_]; tryfalse.
  unfolds in H_.
  destruct v; tryfalse.
  simpljoin.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end.
  lets H__: nwrong_dom_dest.
  specializes H__; eauto.
  unfolds.
  eexists. split; eauto. 
Qed.

Lemma cheq_no_chan_impl:
  forall O1 O2 v pr,
    prt_indom v O1 pr -> 
    obsr_equiv_chnd O1 O2 ->
    ports_equiv (dom_for_prio pr) O1 O2 ->
    no_channel O1 v ->
    no_channel O2 v.  
Proof. 
  introv Hnwd Hoe Hpe (* Hgc1 Htpi1 *) Hnc1.
  unfold no_channel in *.
  simpljoin.
  unfolds in Hnwd.
  destruct Hnwd as (a & Hptreq & Hid).
  inverts Hptreq. 
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: forall _, _ -> _ |- _ => lets H'__: H Hid
  end.
  destruct H'__ as (Hpeq & _).
  match goal with H1: ?t1 = _, H2: ?t2 = _ |- _ => rewrite H1 in H2 end.
  symmetry in Hpeq.
  unfold obsr_equiv_chnd in Hoe.
  destruct Hoe as ((Hnnch & Hcheq) & (Hnnkp & Hkpeq)).
  match goal with
    H1: get O1 oskportid = _, H2: get O1 oskportid = _ |- _ =>
      rewrite H1 in H2
  end.
  do 13 eexists. 
  split; eauto.
Qed.    

Lemma cheq_intercore_impl: 
  forall O1 O2 v pr, 
    prt_indom v O1 pr -> 
    ports_equiv (dom_for_prio pr) O1 O2 ->
    obsr_equiv_chnd O1 O2 -> 
    (exists a, v = Vptr a /\ is_intercore O1 a) ->
    (exists a, v = Vptr a /\ is_intercore O2 a).  
Proof.
  introv Hpi Hpe Hoe Hex.
  destruct Hex as (a & Hptr & Hic).
  subst.
  eexists.
  split; eauto.
  unfolds in Hpi.
  destruct Hpi as (a_ & Hpt & Hid).
  inverts Hpt.
  unfolds in Hpe.
  simpljoin.
  match goal with
    H: forall _, _->_ |- _ => lets H__: H Hid
  end.
  destruct H__ as (Hgeq & Ha).
  unfolds in Hic.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: ?t = _, H': ?t' = _ |- _ => unify t t'; rewrite H in H'
  end.
  unfolds in Hoe.
  simpljoin.
  l_rew21_inv1 (get O1 oskportid). 
  l_rew21_inv1 (get O1 oschannelid).
  unfold is_intercore.
  do 18 eexists.
  split; eauto.
Qed.

Lemma prt_indom_preserve:
  forall O O' v pr,
    prt_indom v O pr ->
    prt_indom v O' pr.
Proof.
  introv Hpi.
  unfold prt_indom in *.
  simpljoin.
  eexists.
  split; eauto.
Qed. 

Lemma ceq_nnocap_hascap: 
  forall pr O1 O2 t1, 
    cap_equiv (dom_for_prio pr) O1 O2 ->
    task_prio_id O1 pr t1 ->
    get O1 curtid = Some (oscurt t1) -> 
    ~has_no_cap_prtpost O1 ->
    has_prtpost_cap O1 pr. 
Proof.
  introv Hce Htpi Hgct Hnncp.
  unfolds in Htpi.
  unfolds in Hce. 
  simpljoin.      
  unfolds.
  match goal with H: get O1 abstcblsid = Some (abstcblist ?x) |- _ => rename x into tls end.
  eexists.
  exists (fun tid => match get tls tid with Some (_, _, _, _, p0) => Some p0 | _ => None end).
  exists (dom_for_prio pr).
  splits.
  - eauto. 
  - unfolds.
    eexists.
    split. eauto. 
    split.
    + introv Hgt.
      rewrite Hgt.
      auto.
    + introv Hgp.
      destruct (get tls t) eqn: E; tryfalse.
      repeat match type of Hgp with
               context [let (_, _):=?x in _] => destruct x
             end.
      inverts Hgp.
      do 4 eexists; eauto. 
  - auto.
  - (* has_post_cap *)
    unfolds.
    exists t1.
    exists pr.
    match goal with H: get tls _ = _ |- _ => rewrite H end.
    splits; eauto.
    unfold has_no_cap_prtpost in Hnncp.
    do 7 eapply Classical_Pred_Type.not_ex_all_not in Hnncp.
    eapply Classical_Prop.not_and_or in Hnncp.
    destruct Hnncp as [Hf | H']; [ false; eapply Hf; eauto | idtac ].
    eapply Classical_Prop.not_and_or in H'.
    destruct H' as [Hf | H']; [ false; eapply Hf; eauto | idtac ].
    eapply Classical_Prop.not_and_or in H'.
    destruct H' as [Hf | H']; [ false; eapply Hf; eauto | idtac ].
    eapply Classical_Prop.not_and_or in H'.
    destruct H' as [Hf | H']; [ false; eapply Hf; eauto | idtac ].
    apply Classical_Prop.NNPP in H'.
    auto.
Qed.

Lemma cpe_no_prtpost_cap_impl:   
  forall pr t1 t2 O1 O2, 
    cap_equiv (dom_for_prio pr) O1 O2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    has_no_cap_prtpost O1 ->
    has_no_cap_prtpost O2.
Proof.
  introv Hce Hct1 Hct2 Htpi1 Htpi2 Hncp.
  unfold cap_equiv in Hce.
  unfold has_no_cap_prtpost in *.
  destruct Hce as (cspc1 & cspc2 & Hg1 & Hg2 & Hall).
  specialize (Hall pr (eq_refl)).
  destruct Hall as (Hcpiff & _).
  simpljoin.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O1 cspaceid).
  unfold task_prio_id in *.
  simpljoin.
  l_rew21_inv1 (get O1 abstcblsid).
  rewrite H1 in H7. inverts H7.
  do 7 eexists. 
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  introv Hhcp. apply H3. clear -Hhcp Hcpiff.
  eapply Hcpiff; eauto. 
Qed. 

Lemma prte_prtid_invalid_impl: 
  forall O1 O2 vprt pr t1, 
    ~wrong_dom O1 vprt ->
    ports_equiv (dom_for_prio pr) O1 O2 -> 
    get O1 curtid = Some (oscurt t1) ->
    task_prio_id O1 pr t1 ->
    (exists a dpl pcn pd pid pdir pst pin pout pt,
        get O1 osdomainportid = Some (osdomainport dpl) /\
          vprt = Vptr a /\
          get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
          Z.of_nat pid >= PORT_NUMS) -> 
    (exists a dpl pcn pd pid pdir pst pin pout pt,
        get O2 osdomainportid = Some (osdomainport dpl) /\
          vprt = Vptr a /\
          get dpl a = Some (pcn, pd, pid, pdir, pst, pin, pout, pt) /\
          Z.of_nat pid >= PORT_NUMS). 
Proof.
  introv Hnwd Hpe Hgc1 Htpi1 Hex.
  simpljoin.
  eapply nwrong_dom_dest in Hnwd; eauto.
  unfolds in Hpe.
  simpljoin.
  l_rew21_inv1 (get O1 osdomainportid).
  match goal with
    H: forall _, _ -> _ |- _ => lets H__: H Hnwd
  end.
  destruct H__ as (Hprteq & _).
  match goal with
    H1: ?t1 = Some _, H2: ?t1' = _ |- _ => unify t1 t1'; rewrite H1 in H2
  end.
  do 10 eexists.
  split; eauto.
Qed.    

Lemma dom_cur_tsk_dom_eq:
  forall O10 O20 pr O1 O2 t1 t2 x1 x2 Of1 Of2, 
    dom_cur_tsk O10 x1 ->
    dom_cur_tsk O20 x2 ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    task_prio_id O1 pr t1 ->
    task_prio_id O2 pr t2 ->
    get O1 curtid = Some (oscurt t1) ->
    get O2 curtid = Some (oscurt t2) ->
    x1 = x2 /\ x1 = dom_for_prio pr.
Proof.
  introv Hdc1 Hdc2 Hjo1 Hjo2 Htpi1 Htpi2 Hgt1 Hgt2.
  unfold dom_cur_tsk in *.
  simpljoin.
  kvext O10 curtid O1.
  kvext O20 curtid O2.
  l_rew21_inv1 (get O1 curtid).
  l_rew21_inv1 (get O2 curtid).
  unfold task_prio_id in *.
  simpljoin.
  kvext O10 abstcblsid O1.
  l_rew21_inv1 (get O1 abstcblsid).
  kvext O20 abstcblsid O2.
  l_rew21_inv1 (get O2 abstcblsid).
  match goal with H1: ?t = _, H2: ?t = _ |- _ => rewrite H1 in H2; inverts H2; clear H1 H2 end.
  match goal with H1: ?t = _, H2: ?t = _ |- _ => rewrite H1 in H2; inverts H2; clear H1 H2 end.
  split; auto.
Qed. 

Lemma bufs_equiv_ibmp_eq:
  forall td O1 O2 O10 O20 x1 x2 Of1 Of2, 
    bufs_equiv td O1 O2 -> 
    get O10 ibufsid = Some (ibufs x1) ->
    get O20 ibufsid = Some (ibufs x2) ->
    join O10 Of1 O1 ->
    join O20 Of2 O2 -> 
    x1 td = x2 td.
Proof.
  introv Hbe Hgib1 Hgib2 Hjo1 Hjo2.
  unfold bufs_equiv in *.
  destruct Hbe as (Hibe & Hobe).
  unfolds in Hibe.
  simpljoin.
  kvext O10 ibufsid O1.
  kvext O20 ibufsid O2.
  l_rew21_inv1 (get O1 ibufsid).
  l_rew21_inv1 (get O2 ibufsid).
  auto.
Qed. 
