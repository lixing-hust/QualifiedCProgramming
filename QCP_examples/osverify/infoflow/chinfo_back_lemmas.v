
Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import seplog_lemmas.

Require Import if_language.
Require Import if_opsem.
Require Import spec_aux_defs.
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

Require Import confidentiality_tactics.

Require Import if_common_lemmas.
Require Import ct_pp_lemmas. 
Require Import integrity_lemma.

Require Import FunctionalExtensionality.
Require Import int_auto.
Require Import protect.

Set Keyed Unification.

Lemma tps_tst_corr_pp_back:
  forall O O' tps, 
    tps_tst_corr O' tps ->
    prio_preserved O O' ->
    dom_impl O' O -> 
    tps_tst_corr O tps. 
Proof.
  introv Httc Hpp Hdi.
  unfold tps_tst_corr in *.
  simpljoin.
  unfolds in Hdi.
  specialize (Hdi abstcblsid).
  rewrite H in Hdi.
  destruct Hdi as (tls & Hgtls).
  exists tls.
  split; eauto.
  split.
  - introv Hgt.
    unfolds in Hpp.
    unfold prio_preserved_d in Hpp.
    specialize (Hpp (dom_for_prio p0) p0 t (eq_refl _)).
    assert (Htpi: task_prio_id O p0 t).
    { unfolds. do 5 eexists; split; eauto. }
    apply Hpp in Htpi.
    unfolds in Htpi. simpljoin.
    l_rew21_inv1 (get O' abtcblsid).
    eapply H0; eauto. 
  - introv Hgts.
    lets H__: H1 Hgts; eauto.
    simpljoin.
    unfolds in Hpp.
    unfold prio_preserved_d in Hpp.
    specialize (Hpp (dom_for_prio p0) p0 t (eq_refl _)).
    assert (Htpi: task_prio_id O' p0 t).
    { unfolds. do 5 eexists; split; eauto. }
    apply Hpp in Htpi.
    unfolds in Htpi. simpljoin.
    l_rew21_inv1 (get O abtcblsid).
    do 4 eexists; eauto.
Qed. 

Definition dpl_same_addr_to_id (dpl dpl': DomainPortMod.map) :=
  forall a sid dir,
        ((exists pcn pd pst pin pout pt,
             get dpl a = Some (pcn, pd, sid, dir, pst, pin, pout, pt)) <->
           (exists pcn pd pst pin pout pt,
               get dpl' a = Some (pcn, pd, sid, dir, pst, pin, pout, pt))).

Lemma dpl_same_addr_to_id_refl: 
  forall dpl, 
    dpl_same_addr_to_id dpl dpl. 
Proof.
  intros.
  unfolds.
  intros.
  split; auto.
Qed.   


Lemma qpost_exwt_succ_chinfo_back:
  forall v1 v2 i O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpost_exwt_succ_body (v1 :: v2 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpost_exwt_succ_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma qtimedpost_nowt_succ_chinfo_back:
  forall v1 v2 i O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpost_nowt_succ_body (v1 :: v2 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpost_nowt_succ_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgte: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp. auto.
  }
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed. 

Lemma qtimedpost_ovf_block_chinfo_back:
  forall v1 v2 i O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qtimedpost_ovf_block_body (v1 :: v2 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qtimedpost_ovf_block_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed. 

Lemma qtimedpost_timeout_err_chinfo_back:
  forall v1 v2 i O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qtimedpost_timeout_err_body (v1 :: v2 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qtimedpost_timeout_err_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma qpost_nowt_succ_chinfo_back:
  forall v1 v2 i O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpost_nowt_succ_body (v1 :: v2 :: Vint32 i :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpost_nowt_succ_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma qpend_get_no_pwl_succ_chinfo_back:
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_get_no_pwl_succ_body (v1 :: v2 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof. 
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_nopwl_succ_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma qpend_get_ex_pwl_before_sched_chinfo_back:
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_get_ex_pwl_before_sched_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_get_expwl_before_sched_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma qpend_block_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_block_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_block_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.

Lemma qpend_assm_stat_chinfo_back: 
  forall v1 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_assm_stat (v1 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_assm_stat_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.

Lemma qpend_block_get_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_block_get_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_block_get_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.

Lemma qpend_to_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qpend_to_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qpend_to_body_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.

Lemma qacc_succ_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qacc_succ_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: aqcc_succ_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end.
  match goal with H: Some _ = _ |- _ => inverts H end.
  assert (Hgde: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence. 
  - 
    eapply tps_tst_corr_pp_back; eauto. 
  -
    rewrite Hgde. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.


(*************************************************************)
  
Lemma eqdomO0_sym:
  forall O1 O2, 
    eqdomO0 O1 O2 ->
    eqdomO0 O2 O1.
Proof.
  introv Heq.
  unfold eqdomO0 in *.
  simpljoin.
  split; auto. 
Qed.
  
Lemma eqdom0_frm_domimpl:
  forall O10 O20 Of O1 O2,
    eqdomO0 O10 O20 ->
    join O10 Of O1 ->
    join O20 Of O2 ->
    dom_impl O1 O2.
Proof.
  introv Heqd Hjo1 Hjo2.
  unfolds in Heqd.
  destruct Heqd as (Himpl1 & Himpl2).
  unfold dom_impl in Himpl1.
  unfold dom_impl.
  intros.
  specialize (Himpl1 x).
  destruct (get O1 x) eqn: E.
  2: {
    assert (E0: get O10 x = None).
    { eapply join_get_none_rev1; eauto. }  
    rewrite E0 in Himpl1.
    assert (E0': get Of x = None).
    { clear Hjo2. eapply join_get_none_rev2; eauto. }
    assert (get O2 x = get Of x).
    eapply map_join_get_none; eauto.
    congruence. 
  }
  destruct a; 
    try (
        match type of E with
          get _ _ = Some ?e => 
            assert (Hor: get O10 x = Some e \/ get Of x = Some e)
            by (eapply join_get_or; eauto)
        end; 
        destruct Hor as [Hget1 | Hget2];
        [
          rewrite Hget1 in Himpl1;
          destruct Himpl1 as (y & Hget20); 
          eexists;
          eapply join_get_get_l; eauto |
          eexists;
          eapply join_get_get_r; eauto
      ]).
Qed.

Lemma eqdom0_frm_domimpl_back:
  forall O10 O20 Of O1 O2, 
    eqdomO O10 O20 ->
    join O10 Of O1 -> 
    join O20 Of O2 ->
    dom_impl O2 O1. 
Proof.
  introv Heq Hjo Hjo'.
  unfolds in Heq.
  simpljoin.
  eapply eqdomO0_sym in H; eauto.
  eapply eqdom0_frm_domimpl; eauto.
Qed.   

(****************************************************************)

Ltac des_vl_absprog := 
  match goal with
    Hsp: context[spec_step] |- _ =>
      match goal with
        vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
          destruct vl; inverts H; tryfalse
      | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
          apply abt_succs_contra in H; subst; inverts Hsp
      | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
          destruct v; simpl in H;  
          try (apply abt_succs_contra in H; subst; inverts Hsp)   
      end
  end.

Ltac symexe_ :=
  match goal with
    H: spec_step _ _ _ _ _ _ |- _ => inverts H
  | H: nabt (set _ _ (curs (hapi_code (ABORT)), _)) |- _ =>
      apply nabt_abt_false in H; solve [false]
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto)
  | H: _ /\ (ABORT <> ABORT) |- _ =>
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto
  (* | H: _ |- prio_preserved ?O1 ?O2 => *)
  (*     unify O1 O2; apply prio_preserved_refl; symexe0 *)
  | act: action, H: ?f _ ?O ?act (_, Some ?O'), H1: join _ _ ?O1, H2: join _ _ ?O2 |- _ =>
      (assert (O = O') by eauto with oeq_lemmas; subst); 
      (assert (O1 = O2) by join auto; subst)
  | H: tps_tst_corr ?O ?tps |- tps_tst_corr ?O ?tps /\ _ /\ _ /\ _ /\ _ => 
      splits;
      [eauto | eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto | eauto | eauto | eauto]
  | _ => idtac
  end.

Ltac symexe0 :=
  match goal with
    H: spec_step _ _ _ _ _ _ |- _ => inverts H; symexe0
  | H: nabt (set _ _ (curs (hapi_code (ABORT)), _)) |- _ =>
      apply nabt_abt_false in H; solve [false]; symexe0
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto); symexe0
  | H: _ /\ (ABORT <> ABORT) |- _ =>
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto; symexe0
  (* | H: _ |- prio_preserved ?O1 ?O2 => *)
  (*     unify O1 O2; apply prio_preserved_refl; symexe0 *)
  | H: tps_tst_corr ?O ?tps |- tps_tst_corr ?O ?tps /\ _ /\ _ /\ _ /\ _ => 
      splits;
      [eauto | eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto | eauto | eauto | eauto]
  | act: action, H: ?f _ ?O ?act (_, Some ?O'), H1: join _ _ ?O1, H2: join _ _ ?O2 |- _ =>
      (assert (O = O') by eauto with oeq_lemmas; subst); 
      (assert (O1 = O2) by join auto; subst); symexe0
  | _ => idtac
  end.

Ltac symexe i :=
  destruct i;
  [match goal with
     H: context[nth_error] |- _ => simpl in H; inverts H; symexe0
   end
  | idtac]. 

Set Printing Depth 1000.

Lemma mqsend_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (mqsend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold mqsend in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.  
  symexe n.  
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qtimedpost_nowt_succ_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpost_exwt_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qtimedpost_ovf_block_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n. 
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qtimedpost_timeout_err_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. } 
  symexe n.
  eapply qpost_nowt_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. } 
  eapply qpost_exwt_succ_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  symexe n.
  simpl in H0.
  rewrite nth_error_nil in H0.
  false.

  Unshelve.
  trivial.  

Qed. 

Lemma mqrecv_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (mqreceive vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold mqreceive in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_get_no_pwl_succ_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. } 
  eapply qpend_get_ex_pwl_before_sched_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_block_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }  
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_assm_stat_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  eapply qpend_block_get_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_to_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  eapply qacc_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  simpl in H0.
  rewrite nth_error_nil in H0.
  false.

  Unshelve.
  trivial. 

Qed.

Lemma mqtimedrecv_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (mqtimedreceive vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold mqtimedreceive in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_get_no_pwl_succ_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. } 
  eapply qpend_get_ex_pwl_before_sched_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_block_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }  
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_assm_stat_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  eapply qpend_block_get_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_to_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  eapply qacc_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  simpl in H0.
  rewrite nth_error_nil in H0.
  false.

  Unshelve.
  trivial. 

Qed.


Lemma dpl_upd_same_addr_to_pid: 
  forall kpm das m dpl dpl', 
    dpl_upd kpm das m dpl dpl' ->
    dpl_same_addr_to_id dpl' dpl. 
Proof.
  introv Hdu.
  unfolds.
  unfolds in Hdu.
  intros.
  specialize (Hdu a).
  destruct Hdu as [Hupd | Hnupd].
  - simpljoin.
    split.
    + 
      introv Hgd'.
      simpljoin.
      match goal with
        H1: get dpl' _ = _, H2: get dpl' _ = _ |- _ =>
          rewrite H1 in H2; inverts H2
      end.
      do 6 eexists. eauto.
    +
      introv Hgd.
      simpljoin.
      match goal with
        H1: get dpl _ = _, H2: get dpl _ = _ |- _ =>
          rewrite H1 in H2; inverts H2
      end.
      do 6 eexists. eauto.
  - destruct Hnupd as (_ & Heq).
    rewrite Heq.
    split; auto.
Qed.

Lemma q_send_to_domain_chinfo_back: 
  forall v O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    q_send_to_domain (v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hqs Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: q_send_to_domain_prio_preserved Hqs; eauto.
  specializes Hpp; eauto. 
  inverts Hqs.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' osdomainportid O'.
  kvext O0 osdomainportid O.
  l_rew21_inv1 (get O' osdomainportid). 
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - eexists.
    split; eauto.
    eapply dpl_upd_same_addr_to_pid; eauto. 
Qed. 

Lemma store_msg_chinfo_back: 
  forall v O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    store_msg (v :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.  
  introv Hsm Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: store_msg_prio_preserved Hsm; eauto.
  specializes Hpp; eauto. 
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' osdomainportid O'.
  kvext O0 osdomainportid O.
  l_rew21_inv1 (get O' osdomainportid). 
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - eexists.
    split; eauto.
    unfolds.
    intros.
    casetac x a Ht Hf.
    + subst. rewrite set_a_get_a.
      split; introv Hex.
      simpljoin.
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      do 6 eexists; eauto.
      simpljoin.
      match goal with 
        H1: get _ a = _, H2: get _ a = _ |- _ => rewrite H1 in H2; inverts H2 
      end.
      do 6 eexists; eauto.
    + rewrite set_a_get_a'; eauto.
      split; eauto.
Qed.        


Lemma qportpend_notnil_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qportpend_notnil_body (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hsm Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qportpend_notnil_prio_preserved Hsm; eauto.
  specializes Hpp; eauto. 
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' osdomainportid O'.
  kvext O0 osdomainportid O.
  l_rew21_inv1 (get O' osdomainportid). 
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - eexists.
    split; eauto.
    unfolds.
    intros.
    casetac x a Ht Hf.
    + subst. rewrite set_a_get_a.
      split; introv Hex.
      simpljoin.
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      do 6 eexists; eauto.
      simpljoin.
      match goal with 
        H1: get _ a = _, H2: get _ a = _ |- _ => rewrite H1 in H2; inverts H2 
      end.
      do 6 eexists; eauto.
    + rewrite set_a_get_a'; eauto.
      split; eauto.
Qed.

Lemma qportpend_block_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qportpend_block (v1 :: v2 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hsm Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qportpend_block_prio_preserved Hsm; eauto.
  specializes Hpp; eauto. 
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (Hgdpe: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.    
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - 
    rewrite Hgdpe. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.  

Lemma qportpend_block_get_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qportpend_block_get_body (v1 :: v2 :: nil) O0 act (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof. 
  introv Hsm Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qportpend_block_get_prio_preserved Hsm; eauto.
  specializes Hpp; eauto. 
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  kvext_h Hjo' osdomainportid O'.
  kvext O0 osdomainportid O.
  l_rew21_inv1 (get O' osdomainportid). 
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - eexists.
    split; eauto.
    unfolds.
    intros.
    casetac x a Ht Hf.
    + subst. rewrite set_a_get_a.
      split; introv Hex.
      simpljoin.
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      do 6 eexists; eauto.
      simpljoin.
      match goal with 
        H1: get _ a = _, H2: get _ a = _ |- _ => rewrite H1 in H2; inverts H2 
      end.
      do 6 eexists; eauto.
    + rewrite set_a_get_a'; eauto.
      split; eauto.
Qed.

Lemma qportpend_block_timeout_chinfo_back: 
  forall v1 v2 O0 O0' act v' Of O O' tps dpl kportl chs cspc, 
    qportpend_block_timeout (v1 :: v2 :: nil) O0 act (v', Some O0') -> 
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc). 
Proof.
  introv Hsm Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: qportpend_block_to_prio_preserved Hsm; eauto.
  specializes Hpp; eauto. 
  inverts Hsm.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  match goal with H: _ :: _ = _ |- _ => inverts H end.
  assert (Hgdpe: get O osdomainportid = get O' osdomainportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.    
  }
  assert (Hgke: get O oskportid = get O' oskportid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgche: get O oschannelid = get O' oschannelid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hgcpe: get O cspaceid = get O' cspaceid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  splits; try congruence.
  - eapply tps_tst_corr_pp_back; eauto.
  - 
    rewrite Hgdpe. eexists; split; eauto.
    eapply dpl_same_addr_to_id_refl; eauto.    
Qed.   

Lemma qportpost_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (qportpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold qportpost in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply q_send_to_domain_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply store_msg_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  simpl in H0.  
  rewrite nth_error_nil in H0.
  false. 

Qed. 

Lemma qportpend_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (qportpend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold qportpend in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qportpend_notnil_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.  
  symexe n.
  eapply qportpend_block_chinfo_back; eauto. 
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  eapply qportpend_block_get_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qportpend_block_timeout_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  simpl in H0.
  rewrite nth_error_nil in H0.
  false. 
Qed. 

Require Import sched_lemma. 
Lemma tlsused_tls'_prio_preserved_:
  forall tls tls' els els' O O', 
    intspecs.tickstep' tls els tls' els' tls ->
    get O abstcblsid = Some (abstcblist tls) ->
    get O' abstcblsid = Some (abstcblist tls') -> 
    prio_preserved O O'. 
Proof.
  introv Hstep Hg Hg'.
  unfolds.
  intros.
  unfolds.
  introv Hd.
  lets H__: tlsused_tls'_prio_preserved t Hstep; eauto.
  assert (Hiff: 
           forall p0 : priority,
             (exists p st msg0 sus, get tls' t = Some (p, st, msg0, sus, p0)) <->
               (exists p st msg0 sus, get tls t = Some (p, st, msg0, sus, p0))
         ).
  {
    destruct H__ as [Hn | Hnn]; simpljoin.
    auto.
    intros. specialize (H0 p0).
    symmetry.
    auto.
  }
  
  specialize (Hiff pr).
  destruct Hiff as (Hg'g & Hgg').
  split.
  + 
    introv Htpi.
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O abtcblsid).
    specializes Hgg'; eauto.
    simpljoin. 
    do 5 eexists.
    split; eauto.
  +
    introv Htpi'.
    unfold task_prio_id in *.
    simpljoin.
    l_rew21_inv1 (get O' abtcblsid).
    specializes Hg'g; eauto. 
    simpljoin.
    do 5 eexists.
    split; eauto.
Qed.     

Lemma tickisr_spec_step_chninfo_preserve: 
  forall n cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs tickisr) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold tickisr in Hnth.

  symexe n.
  {
    unfold tickisr_spec in *.
    simpljoin. 
    split.
    - 
      unfold tickstep in *.
      kvext O0 abtcblsid O.      
      match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end; 
      match goal with H: Some _ = Some _ |- _ => inverts H end.
      + 
        match goal with
          H: join (set _ _ _) Of O' |- _ => kvext_h H abtcblsid O'
        end.
        match goal with
          H: context [tickstep'] |- _ =>
            lets H__: tlsused_tls'_prio_preserved_ H; eauto
        end.
        specializes H__; eauto.
        eapply tps_tst_corr_pp_back with (O:=O) (O':=O'); eauto.
        eapply eqdom0_frm_domimpl_back; eauto. 
      +
        match goal with
          H: join (set _ _ _) Of O' |- _ => kvext_h H abtcblsid O'
        end.
        match goal with
          H: context [tickstep'] |- _ =>
            lets H__: tlsused_tls'_prio_preserved_ H; eauto
        end.
        specializes H__; eauto. 
        eapply tps_tst_corr_pp_back with (O:=O) (O':=O'); eauto.
        eapply eqdom0_frm_domimpl_back; eauto. 
    -
      match goal with H: join _ _ _, H': join _ _ _ |- _ => rename H into Hjo; rename H' into Hjo' end.
      assert (Hdpe: get O osdomainportid = get O' osdomainportid).
      {
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end;
        match goal with H: Some _ = Some _ |- _ => inverts H end;         
        lets H__: join_get_same_l osdomainportid Hjo Hjo'; eauto; 
        repeat rewsimp; eauto. 
      }
      assert (get O oskportid = get O' oskportid).
      {
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end;
        match goal with H: Some _ = Some _ |- _ => inverts H end;         
        lets H__: join_get_same_l oskportid Hjo Hjo'; eauto; 
        repeat rewsimp; eauto.       
      }
      assert (get O oschannelid = get O' oschannelid).
      {
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end;
        match goal with H: Some _ = Some _ |- _ => inverts H end;         
        lets H__: join_get_same_l oschannelid Hjo Hjo'; eauto; 
        repeat rewsimp; eauto.       
      }
      assert (get O cspaceid = get O' cspaceid).
      {
        match goal with H: _ \/ _ |- _ => inverts H; simpljoin; tryfalse end;
        match goal with H: Some _ = Some _ |- _ => inverts H end;         
        lets H__: join_get_same_l cspaceid Hjo Hjo'; eauto; 
        repeat rewsimp; eauto.       
      }
      splits; try congruence.
      {
        rewrite Hdpe. eexists; split; eauto.
        eapply dpl_same_addr_to_id_refl; eauto.            
      }      
  }
  symexe n.
  symexe n.
  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 
Qed.


Lemma tps_tst_corr_set_: 
  forall O tps t, 
    tps_tst_corr (set O curtid (oscurt t)) tps ->
    tps_tst_corr O tps.
Proof.
  introv Httc.
  unfold tps_tst_corr in *.
  simpljoin. 
  rewsimp_in H.
  eexists.
  split; eauto. 
Qed.     

Lemma bufferpost_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (bufferpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.

  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold bufferpost in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qtimedpost_nowt_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpost_exwt_succ_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.  
  symexe n.
  symexe n.

  simpl in H0.
  false. 
Qed.  

Lemma bufferaccept_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (bufferaccept vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold bufferaccept in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qacc_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  simpl in H0.
  false. 
Qed.  

Lemma bufferpend_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (bufferpend vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold bufferpend in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_get_no_pwl_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_get_ex_pwl_before_sched_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_block_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply qpend_assm_stat_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  eapply qpend_block_get_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  eapply qpend_to_chinfo_back;eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }
  symexe n.
  symexe n.
  symexe n.
  simpl in H0.
  false. 
Qed.  

Lemma sample_send_to_domain_succ_chinfo_back:
  forall v v1 O0 O0' act  Of O O' tps dpl kportl chs cspc, 
    sample_send_to_domain (v :: nil) O0 act (v1, Some O0')->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: sample_send_to_domain_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  unfolds in H9.
  eapply join_get_set_eq_2 in Hjo';eauto.
  inverts Hjo'. clear H10.
  splits.
  unfolds.
  unfolds in Httc.
  try repeat(rewrite set_a_get_a' in Httc;[idtac|introv Hfalse;tryfalse]).
  eauto.
  eapply join_get_get_l in H0;eauto.
  eexists. split. eauto.
  unfolds.
  intros.
  specialize(H9 a).
  destruct H9.
  simpljoin.
  rewrite set_a_get_a' in Hgdp;[idtac|introv Hf;tryfalse].
  rewrite set_a_get_a in Hgdp.  inverts Hgdp.
  
  split.
  introv Hdpl.
  simpljoin. rewrite H13 in H12.
  inverts H12. do 6 eexists. eauto.
  introv Hdpl.
  simpljoin. rewrite H13 in H11. inverts H11.
  do 6 eexists. eauto.
  
  simpljoin.
  rewrite set_a_get_a' in Hgdp;[idtac|introv Hf;tryfalse].
  rewrite set_a_get_a in Hgdp.  inverts Hgdp.
  split.
  introv Hdpl.
  simpljoin. rewrite <-H10.
  do 6 eexists. eauto.
  introv Hdpl.
  simpljoin. rewrite H10.
  do 6 eexists. eauto.

  try repeat(rewrite set_a_get_a' in Hgkp;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgch;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgcp;[idtac|introv Hfalse;tryfalse]).
  eauto.
Qed.

Lemma sampleportpost_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (sampleportpost vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold sampleportpost in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply sample_send_to_domain_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }

  symexe n.
  symexe n.
  symexe n.
  simpl in *.
  inverts H0.
Qed.

Lemma receive_port_msg_succ_chinfo_back:
  forall v v1 O0 O0' act  Of O O' tps dpl kportl chs cspc, 
    receive_port_msg (v :: nil) O0 act (v1, Some O0')->
    join O0 Of O ->
    join O0' Of O' ->
    dom_impl O' O -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) -> 
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) -> 
    tps_tst_corr O tps /\
      (exists dpl',
          get O osdomainportid = Some (osdomainport dpl') /\ dpl_same_addr_to_id dpl dpl') /\
      get O oskportid = Some (oskport kportl) /\
      get O oschannelid = Some (oschannel chs) /\ get O cspaceid = Some (capcspace cspc).
Proof.
  introv Hqns Hjo Hjo' Hdi Httc Hgdp Hgkp Hgch Hgcp. 
  lets Hpp: receive_port_msg_prio_preserved Hqns; eauto.
  specializes Hpp; eauto. 
  inverts Hqns.
  simpljoin.
  match goal with H: Some _ = _ |- _ => inverts H end.
  destruct H3. simpljoin.
  eapply join_get_set_eq_2 in Hjo';eauto.
  inverts Hjo'. clear H3.
  splits.
  unfolds.
  unfolds in Httc.
  try repeat(rewrite set_a_get_a' in Httc;[idtac|introv Hfalse;tryfalse]).
  eauto.
  eapply join_get_get_l in H0;eauto.
  eexists. split. eauto.
  unfolds.
  intros.
  simpljoin.
  rewrite set_a_get_a' in Hgdp;[idtac|introv Hf;tryfalse].
  rewrite set_a_get_a in Hgdp.  inverts Hgdp.
  
  split.
  introv Hdpl.
  simpljoin. 
  casetac x a Hte Htne.
  subst a.
  rewrite set_a_get_a in H3.
  inverts H3.
  do 6  eexists. eauto.
  rewrite set_a_get_a' in H3;eauto.
  do 6 eexists. eauto.
  introv Hdpl.
  simpljoin. 
  casetac x a Hte Htne.
  subst a.
  rewrite set_a_get_a.
  rewrite H3 in H2. inverts H2.
  do 6  eexists. eauto.
  rewrite set_a_get_a';eauto.
  do 6 eexists. eauto.

  try repeat(rewrite set_a_get_a' in Hgkp;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgch;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgcp;[idtac|introv Hfalse;tryfalse]).
  eauto.

  simpljoin.
  eapply join_get_set_eq_2 in Hjo';eauto.
  inverts Hjo'. clear H3.
  splits.
  unfolds.
  unfolds in Httc.
  try repeat(rewrite set_a_get_a' in Httc;[idtac|introv Hfalse;tryfalse]).
  eauto.
  eapply join_get_get_l in H0;eauto.
  eexists. split. eauto.
  unfolds.
  intros.
  simpljoin.
  rewrite set_a_get_a' in Hgdp;[idtac|introv Hf;tryfalse].
  rewrite set_a_get_a in Hgdp.  inverts Hgdp.
  
  split.
  introv Hdpl. eauto.
  introv Hdpl. eauto.

  try repeat(rewrite set_a_get_a' in Hgkp;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgch;[idtac|introv Hfalse;tryfalse]).
  eauto.
  try repeat(rewrite set_a_get_a' in Hgcp;[idtac|introv Hfalse;tryfalse]).
  eauto.
Qed.

Lemma portacceptapit_spec_step_chninfo_preserve: 
  forall n vl cd O cd' O' act dpl kportl chs cspc tps,
    nth_error (get_all_succs (portaccept vl)) n = Some cd ->
    spec_step get_hprio_d cd O cd' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ). 
Proof.
  introv Hnth Hstep Httc Hgdp Hgkp Hgch Hgcp.
  unfold portaccept in Hnth.
  repeat des_vl_absprog.

  symexe n.
  symexe n.
  symexe n.
  symexe n.
  symexe n.
  eapply receive_port_msg_succ_chinfo_back; eauto.
  { eapply eqdom0_frm_domimpl_back; eauto. }

  symexe n.
  symexe n.
  symexe n.
  simpl in *.
  inverts H0.
Qed.

Lemma hpstep_chninfo_preserve:
  forall pc T cst O T' cst' O' act tps dpl kportl chs cspc, 
    good_task_code T ->
    hpstep ((pc, (api_spec, int_spec, get_hprio_d))) T cst O T' cst' O' act ->
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ).     
Proof.
  introv Hgt Hsp Httc Hgdp' Hgkp' Hch' Hgspc'.
  inverts Hsp.
  - (* htstep *)
    match goal with H: get T _ = Some _ |- _ => rename H into HgC end.
    match goal with H: context[htstep] |- _ => rename H into Hsp end.
    lets H__: Hgt HgC; eauto. 
    destruct C as (c & ke & ks).
    inverts Hsp.
    + (* cstep *)
      splits;
        [eauto | eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto | eauto | eauto | eauto].
    + (* hapistep *)
      match goal with H: context [hapistep] |- _ => rename H into Hastp end.
      inverts Hastp.
      * (* hapienter_step *)
        splits; eauto.
        {
          eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto. 
        }
      * (* hidapi_step *)
        match goal with H: context [spec_step] |- _ => rename H into Hsptp end.
        match goal with H: (_, _) = _ |- _ => inverts H end.
        unfolds in H__. 
        destruct H__ as (Hgeval & Hgks).
        simpl in Hgeval.
        unfolds in Hgeval.
        destruct Hgeval as [Hgapi | [Hgintr | [Hend | Habt]]].
        ** (* good api stmt *)
          destruct Hgapi as (fid & ac & ft & vl & Haf & Hin).
          unfolds in Haf.
          simpl in Haf.
          destruct (Zeq_bool mq_send fid) eqn: Ems; inverts Haf.
          {
            eapply In_nth_error in Hin; eauto.
            destruct Hin as (n & Hnth).
            eapply mqsend_spec_step_chninfo_preserve; eauto.            
          }
          {
            destruct (Zeq_bool mq_recv fid) eqn: Emr; 
              try match goal with H: Some _ = Some _ |- _ => inverts H end.
            {
              eapply In_nth_error in Hin; eauto.
              destruct Hin as (n & Hnth).
              eapply mqrecv_spec_step_chninfo_preserve; eauto.              
            }
            destruct (Zeq_bool mq_timedrecv fid) eqn: Etmr; 
              try match goal with H: Some _ = Some _ |- _ => inverts H end.
            {
              eapply In_nth_error in Hin; eauto.
              destruct Hin as (n & Hnth).
              eapply mqtimedrecv_spec_step_chninfo_preserve; eauto.              
            }
            {
              destruct (Zeq_bool q_port_post fid) eqn: Eqpst;
                try match goal with H: Some _ = Some _ |- _ => inverts H end.
              {
                eapply In_nth_error in Hin; eauto.
                destruct Hin as (n & Hnth).
                eapply qportpost_spec_step_chninfo_preserve; eauto.                              
              }
              {
                destruct (Zeq_bool q_port_pend fid) eqn: Eqprt;
                  try match goal with H: Some _ = Some _ |- _ => inverts H end.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth).
                  eapply qportpend_spec_step_chninfo_preserve; eauto.   
                }
                destruct (Zeq_bool sample_port_post fid) eqn: Eqspp;
                  try match goal with H: Some _ = Some _ |- _ => inverts H end.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth).
                  eapply sampleportpost_spec_step_chninfo_preserve; eauto.   
            
                }
                destruct (Zeq_bool port_accept fid) eqn: Eqpa.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth). inverts H2.
                  eapply portacceptapit_spec_step_chninfo_preserve; eauto.   
                }
                destruct (Zeq_bool buffer_post fid) eqn: Ebfprt;
                  try match goal with H: Some _ = Some _ |- _ => inverts H end.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth).
                  eapply bufferpost_spec_step_chninfo_preserve; eauto.   
                }
                destruct (Zeq_bool buffer_accept fid) eqn: Ebfacpt;
                  try match goal with H: Some _ = Some _ |- _ => inverts H end.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth).
                  eapply bufferaccept_spec_step_chninfo_preserve; eauto.   
                }
                destruct (Zeq_bool buffer_pend fid) eqn: Ebfpend;
                  try match goal with H: Some _ = Some _ |- _ => inverts H end.
                {
                  eapply In_nth_error in Hin; eauto.
                  destruct Hin as (n & Hnth).
                  eapply bufferpend_spec_step_chninfo_preserve; eauto.   
                }
                { tryfalse. }
              }
            }
          }
          
        ** (* good intr stmt *)
          destruct Hgintr as (hid & ic & Hgic & Hin).
          eapply In_nth_error in Hin; eauto.
          destruct Hin as (n & Hnth).          
          unfolds in Hgic.
          simpl in Hgic.
          repeat (destruct hid; simpl in Hgic; tryfalse).
          inverts Hgic.
          eapply tickisr_spec_step_chninfo_preserve; eauto.
        **
          simpljoin.
          inverts Hsptp.
        **
          simpljoin.
          inverts Hsptp.

      * (* hapiexit_step *)
        splits; eauto. 
        eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto.

      * (* hintexit_step *)
        splits; eauto.
        eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto.

  - (* htistep *)
    match goal with H: context [htistep] |- _ => inverts H end.
    splits; eauto. 
    eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto.

  - (* sched step *)
    rewsimp_in Hgspc'.
    rewsimp_in Hch'.
    rewsimp_in Hgkp'.
    rewsimp_in Hgdp'.

    splits; eauto.
    eapply tps_tst_corr_set_; eauto. 
    eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto.
Qed.

Lemma dpl_same_addr_to_id_trans:
  forall dpl1 dpl2 dpl3, 
    dpl_same_addr_to_id dpl1 dpl2 ->
    dpl_same_addr_to_id dpl2 dpl3 ->
    dpl_same_addr_to_id dpl1 dpl3. 
Proof.
  introv Hds12 Hds23.
  unfold dpl_same_addr_to_id in *.
  intros.
  specialize (Hds12 a sid dir).
  specialize (Hds23 a sid dir).
  destruct Hds12 as (Hds12a & Hds12b).
  destruct Hds23 as (Hds23a & Hds23b).
  split.
  - 
    introv Hex.
    apply Hds12a in Hex.
    apply Hds23a in Hex.
    auto.
  -
    introv Hex.
    apply Hds23b in Hex.
    apply Hds12b in Hex.
    auto.
Qed.                
  
Lemma hpstepokstar_chninfo_preserve: 
  forall pc T cst O T' cst' O' tps dpl kportl chs cspc, 
    hpstepokstar ((pc, (api_spec, int_spec, get_hprio_d))) T cst O T' cst' O' ->
    good_client_code pc ->
    good_task_code T ->                         
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    (
      tps_tst_corr O tps
      /\ (exists dpl',
             get O osdomainportid = Some (osdomainport dpl') /\
               dpl_same_addr_to_id dpl dpl')
      /\ get O oskportid = Some (oskport kportl)
      /\ get O oschannelid = Some (oschannel chs)
      /\ get O cspaceid = Some (capcspace cspc)
    ).     
Proof.  
  introv Hsps.
  remember (pc, (api_spec, int_spec, get_hprio_d)) as sys.
  induction Hsps.
  -
    intros.
    splits; eauto. 
    eexists; splits; eauto; eapply dpl_same_addr_to_id_refl; eauto.
  -
    introv Hgcd Hgtc Httc'' Hdpl'' Hkpl'' Hchn'' Hcspc''.
    specializes IHHsps; eauto.
    rewrite Heqsys in *. 
    eapply hpstep_goodcode_h; eauto. 
    clear Hdpl'' Hkpl'' Hchn'' Hcspc'' Httc''.
    destructs IHHsps.
    match goal with H: context [hpstep_ok] |- _ => inverts H end.
    simpljoin.
    lets H__: hpstep_chninfo_preserve.
    specializes H__; eauto.
    simpljoin.
    splits; eauto. 
    eexists. split; eauto.
    eapply dpl_same_addr_to_id_trans; eauto. 
Qed.

Set Keyed Unification.

Lemma tps_tst_corr_eq:
  forall O tps1 tps2, 
    tps_tst_corr O tps1 ->
    tps_tst_corr O tps2 ->
    tps1 = tps2. 
Proof.
  introv Httc1 Httc2.
  unfold tps_tst_corr in *.
  simpljoin.
  l_rew21_inv1 (get O abtcblsid).
  apply functional_extensionality.
  intro t.
  destruct (tps1 t) eqn: E1.
  - eapply H4 in E1; eauto.
    simpljoin.
    eapply H1 in H0; eauto. 
  - destruct (get x0 t) eqn: E'.
    + specialize (H3 t).
      rewrite E' in H3.
      rewrite E1 in H3.
      destruct p. destruct p. destruct p. destruct p.
      specializes H3; eauto.
      inverts H3.
    + destruct (tps2 t) eqn: E2.
      * specialize (H2 t).
        eapply H2 in E2.
        simpljoin.
        rewrite E' in H0. inverts H0.
      * auto.
Qed.           

Lemma init_tsk_st_impl_ttc: 
  forall O tps, 
    init_tsk_st O tps ->
    tps_tst_corr O tps. 
Proof.
  introv Hits.
  unfolds in Hits.
  unfolds.
  simpljoin.
  eexists.
  split; eauto.
  split.
  - 
    introv Hg.
    lets H__: H0 Hg; eauto.
    simpljoin.
    auto.
  -
    auto.
Qed. 
      
Lemma reachable_chinfo_back: 
  forall pc T' cst' O' tps dpl kportl chs cspc, 
    good_client_code pc -> 
    reachable (pc, (api_spec, int_spec, get_hprio_d)) T' cst' O' -> 
    tps_tst_corr O' tps -> 
    get O' osdomainportid = Some (osdomainport dpl) ->
    get O' oskportid = Some (oskport kportl) -> 
    get O' oschannelid = Some (oschannel chs) -> 
    get O' cspaceid = Some (capcspace cspc) ->
    exists dpl',
      ccfg = (tps, cspc, dpl', kportl, chs) 
      /\ dpl_same_addr_to_id dpl dpl'. 
Proof.
  introv Hgcc Hrc Httc' Hdpl' Hkpl' Hchn' Hcspc'.
  unfolds in Hrc.
  destruct Hrc as (pu & spc & Heq & Hex).
  destruct Hex as (T0 & cst0 & O0 & Hinit & Hsps).
  inverts Heq.
  unfolds in Hinit.
  destruct Hinit as (Hitsk & Hist).
  unfolds in Hist.
  destruct Hist as (tps_ & dpl_ & kpl_ & chs_ & cspc_ & Hrem).
  simpljoin.
  lets Hgtsk: init_good_tasks Hitsk; eauto.
  specializes Hgtsk; eauto.  
  lets H__: hpstepokstar_chninfo_preserve Hsps; eauto.
  specializes H__; eauto.
  simpljoin.
  match goal with
    H: context[init_tsk_st] |- _ => 
      lets Httc0: init_tsk_st_impl_ttc H; eauto 
  end.
  apply2_rev (tps_tst_corr O0) (tps_tst_corr O0) tps_tst_corr_eq.
  unfold init_prt_st in *.
  simpljoin.
  unfold get in H8. unfold AMap in H8.
  l_rew12_inv2 (OSAbstMod.get O0 osdomainportid).
  unfold get in H9. unfold AMap in H9.
  l_rew12_inv2 (OSAbstMod.get O0 oskportid).
  unfold get in H10. unfold AMap in H10.
  l_rew12_inv2 (OSAbstMod.get O0 oschannelid).
  match goal with
    H: context[init_cap_st] |- _ => unfolds in H; inverts H
  end.
  simpljoin. 
  l_rew21_inv1 (get O0 cspaceid).
  eexists.
  split; eauto.
Qed.   
