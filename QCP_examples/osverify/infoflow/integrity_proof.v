Require Import LibTactics.
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs.
Require Import prt_apispecs.
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
Require Import mqsend_codeequiv_integrity_proof.
Require Import mqsend_dataequiv_integrity_proof.
Require Import qportpost_data_integrity_proof.
Require Import qportpost_codeequiv_integrity_proof.
Require Import mqrecv_codeequiv_integrity_proof.
Require Import mqrecv_dataequiv_integrity_proof.
Require Import portpend_dataequiv_integrity_proof.
Require Import qportpend_codeequiv_integrity_proof.
Require Import mqtmrecv_codeequiv_integrity_proof.
Require Import mqtmrecv_dataequiv_integrity_proof.

Require Import bufferaccept_dataequiv_integrity_proof.
Require Import bufferPost_dataequiv_integrity_proof.
Require Import bufferPend_codeequiv_integrity_proof.
Require Import bufferaccept_codeequiv_integrity_proof.
Require Import bufferPost_codeequiv_integrity_proof.
Require Import bufferPend_dataequiv_integrity_proof.

Require Import samplePortPost_codeequiv_integrity_proof.
Require Import sampleportpost_data_integrity_proof.
Require Import portAccept_codeequiv_integrity_proof.
Require Import portAccept_data_equiv_integrity_proof.

Require Import sem_prop.
Require Import sem_prop_2.
Require Import api_intr_succs_prop.
(* \\\\\\\\\\\\\\\\\\\\\\\\\\\\\ *)

Lemma api_spec_step_code_equiv_tskd'_preserve :
forall O pr t T cd ke ks fid acode ft vl sd cd' O' act i,
good_task_code T ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
api_spec fid = Some (acode, ft) ->
In cd (get_all_succs (acode vl)) ->
spec_step sd cd O cd' O' act ->
cd' <> ABORT ->
i <> dom_for_prio pr ->
O <> O' ->
code_equiv_tskd' i T (set T t (curs (hapi_code cd'), (ke, ks))) O O'.
Proof.
introv HgdT Htpi Hctid Hgett Hapi Hcd Hstep Hnabt' Hi_neq HO_neq.
lets Hnth: In_nth_error cd Hcd.
destruct Hnth as (n & Hnth).
unfolds in Hapi.
simpl in Hapi.
destruct (Zeq_bool mq_send fid) eqn: eq1;
try destruct (Zeq_bool mq_recv fid) eqn: eq2;
try destruct (Zeq_bool q_port_post fid) eqn: eq3;
try destruct (Zeq_bool q_port_pend fid) eqn: eq4;
try destruct (Zeq_bool sample_port_post fid) eqn: eq4_;
try destruct (Zeq_bool port_accept fid) eqn: eq4__; 
try destruct (Zeq_bool mq_timedrecv fid) eqn: eq5;
try destruct (Zeq_bool buffer_post fid) eqn: eq6;
try destruct (Zeq_bool buffer_accept fid) eqn: eq7;
try destruct (Zeq_bool buffer_pend fid) eqn: eq8;
try inverts Hapi;
tryfalse;
try rewrite <- Zeq_is_eq_bool in eq1;
try rewrite <- Zeq_is_eq_bool in eq2;
try rewrite <- Zeq_is_eq_bool in eq3;
try rewrite <- Zeq_is_eq_bool in eq4;
try rewrite <- Zeq_is_eq_bool in eq4_;
try rewrite <- Zeq_is_eq_bool in eq4__;
try rewrite <- Zeq_is_eq_bool in eq5;
try rewrite <- Zeq_is_eq_bool in eq6;
try rewrite <- Zeq_is_eq_bool in eq7;
try rewrite <- Zeq_is_eq_bool in eq8;
  unfold mq_send, mq_recv, mq_timedrecv, 
  q_port_pend, q_port_post, sample_port_post, port_accept, 
  buffer_post, buffer_accept, buffer_pend in *;
  subst;
  tryfalse.
- (* mqsend *)
      assert (Habt: mqsend vl = ABORT \/ mqsend vl <> ABORT) by tauto.
      destruct Habt as [Habt | Hnabt].
      rewrite Habt in *.
      unfold get_all_succs in Hnth.
      simpl in Hnth.
      re_err_contra n; simpl in Hnth; tryfalse.
      inverts Hnth; inverts Hstep.
      rewrite nth_error_nil in Hnth; tryfalse.
      remember vl as send_vl.
      do 11 try (destruct send_vl; simpl in Hnabt;tryfalse); 
      try destruct v; simpl in Hnabt; tryfalse;
      try destruct v1; simpl in Hnabt; tryfalse;
      try destruct v3; simpl in Hnabt; tryfalse;
      try destruct v6; simpl in Hnabt; tryfalse;
      try destruct v7; simpl in Hnabt; tryfalse;
      try destruct v5; simpl in Hnabt; tryfalse.
     eapply mqsend_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
     simpl; auto.
- (* mqreceive *)
    assert (Habt: mqreceive vl = ABORT \/ mqreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as recv_vl.
    do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
    try destruct v; simpl in Hnabt; tryfalse;
    try destruct v1; simpl in Hnabt; tryfalse;
    try destruct v3; simpl in Hnabt; tryfalse;
    try destruct v5; simpl in Hnabt; tryfalse;
    try destruct v7; simpl in Hnabt; tryfalse.
    eapply mqrecv_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto.
- (* qportpost *)
    assert (Habt: qportpost vl = ABORT \/ qportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse.
    eapply qppost_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto.
- (* qportpend *)
    assert (Habt: qportpend vl = ABORT \/ qportpend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v1; simpl in Hnabt; tryfalse.
    eapply qppen_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto.
- (* sampleportpost *)
    assert (Habt: sampleportpost vl = ABORT \/ sampleportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse.
    eapply sampleportpost_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto.
- (* portaccept *)
    assert (Habt: portaccept vl = ABORT \/ portaccept vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse.
    eapply portaccept_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto. 
- (* mq_timedrecv *)
    assert (Habt: mqtimedreceive vl = ABORT \/ mqtimedreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as recv_vl.
  do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
  try destruct v; simpl in Hnabt; tryfalse;
  try destruct v1; simpl in Hnabt; tryfalse;
  try destruct v3; simpl in Hnabt; tryfalse;
  try destruct v4; simpl in Hnabt; tryfalse;
  try destruct v6; simpl in Hnabt; tryfalse.
    eapply mqtmrecv_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
    simpl; auto.
  - (* bufferpost*)
  assert (Habt: buffer_apispecs.bufferpost vl = ABORT \/ buffer_apispecs.bufferpost vl <> ABORT) by tauto.
  destruct Habt as [Habt | Hnabt].
  rewrite Habt in *.
  unfold get_all_succs in Hnth.
  simpl in Hnth.
  re_err_contra n; simpl in Hnth; tryfalse.
  inverts Hnth; inverts Hstep.
  rewrite nth_error_nil in Hnth; tryfalse.
  remember vl as recv_vl.
  do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
  try destruct v1; simpl in Hnabt; tryfalse.
  eapply bufpost_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
 - (* bufferaccept*)
 assert (Habt: buffer_apispecs.bufferaccept vl = ABORT \/ buffer_apispecs.bufferaccept vl <> ABORT) by tauto.
 destruct Habt as [Habt | Hnabt].
 rewrite Habt in *.
 unfold get_all_succs in Hnth.
 simpl in Hnth.
 re_err_contra n; simpl in Hnth; tryfalse.
 inverts Hnth; inverts Hstep.
 rewrite nth_error_nil in Hnth; tryfalse.
 remember vl as recv_vl.
 eapply bufferaccept_nabt_spec_step_code_equiv_tskd'_preserve; eauto. 
 - (* bufferpend*)
 assert (Habt: buffer_apispecs.bufferpend vl = ABORT \/ buffer_apispecs.bufferpend vl <> ABORT) by tauto.
 destruct Habt as [Habt | Hnabt].
 rewrite Habt in *.
 unfold get_all_succs in Hnth.
 simpl in Hnth.
 re_err_contra n; simpl in Hnth; tryfalse.
 inverts Hnth; inverts Hstep.
 rewrite nth_error_nil in Hnth; tryfalse.
 remember vl as recv_vl.
 eapply bufferpend_nabt_spec_step_code_equiv_tskd'_preserve; eauto.
Qed.

Lemma api_spec_step_data_equiv_tskd_preserve :
forall O pr t T cd ke ks fid acode ft vl sd cd' O' act i cst' pc,
good_client_code pc -> 
good_task_code T ->
reachable (pc, (api_spec, int_spec, get_hprio_d)) T cst' O ->
~ flowsTo (TaskDom (dom_for_prio pr)) (TaskDom i) ->
task_prio_id O pr t ->
get O curtid = Some (oscurt t) ->
get T t = Some (curs (hapi_code cd), (ke, ks)) ->
api_spec fid = Some (acode, ft) ->
In cd (get_all_succs (acode vl)) ->
spec_step sd cd O cd' O' act ->
i <> dom_for_prio pr ->
O <> O' ->
data_equiv_tskd i cst' cst' O O'.
Proof.
introv Hgcli Hgdt Hrch Hflw Htpi Hctid Hgett Hapi Hcd Hstep.
introv Hi_neq HO_neq.
lets Hnth: In_nth_error cd Hcd.
destruct Hnth as (n & Hnth).
unfolds in Hapi. 
simpl in Hapi. 
destruct (Zeq_bool mq_send fid) eqn: eq1;
try destruct (Zeq_bool mq_recv fid) eqn: eq2;
try destruct (Zeq_bool q_port_post fid) eqn: eq3;
try destruct (Zeq_bool q_port_pend fid) eqn: eq4;
try destruct (Zeq_bool sample_port_post fid) eqn: eq4_; 
try destruct (Zeq_bool port_accept fid) eqn: eq4__; 
try destruct (Zeq_bool mq_timedrecv fid) eqn: eq5;
try destruct (Zeq_bool buffer_post fid) eqn: eq6;
try destruct (Zeq_bool buffer_accept fid) eqn: eq7;
try destruct (Zeq_bool buffer_pend fid) eqn: eq8;
try inverts Hapi;
tryfalse;
try rewrite <- Zeq_is_eq_bool in eq1;
try rewrite <- Zeq_is_eq_bool in eq2;
try rewrite <- Zeq_is_eq_bool in eq3;
try rewrite <- Zeq_is_eq_bool in eq4;
try rewrite <- Zeq_is_eq_bool in eq4_;
try rewrite <- Zeq_is_eq_bool in eq4__;
try rewrite <- Zeq_is_eq_bool in eq5;
try rewrite <- Zeq_is_eq_bool in eq6;
try rewrite <- Zeq_is_eq_bool in eq7;
try rewrite <- Zeq_is_eq_bool in eq8;
unfold mq_send, mq_recv, mq_timedrecv, 
  q_port_pend, q_port_pend, sample_port_post, port_accept, 
  buffer_post, buffer_accept, buffer_pend in *;
subst;
tryfalse.

- (* mqsend *)
    assert (Habt: mqsend vl = ABORT \/ mqsend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as send_vl.
    do 11 try (destruct send_vl; simpl in Hnabt;tryfalse); 
    try destruct v; simpl in Hnabt; tryfalse;
    try destruct v1; simpl in Hnabt; tryfalse;
    try destruct v3; simpl in Hnabt; tryfalse;
    try destruct v6; simpl in Hnabt; tryfalse;
    try destruct v7; simpl in Hnabt; tryfalse;
    try destruct v5; simpl in Hnabt; tryfalse.
    eapply mqsend_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (*mqreceive*)
    assert (Habt: mqreceive vl = ABORT \/ mqreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as recv_vl.
    do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
    try destruct v; simpl in Hnabt; tryfalse;
    try destruct v1; simpl in Hnabt; tryfalse;
    try destruct v3; simpl in Hnabt; tryfalse;
    try destruct v5; simpl in Hnabt; tryfalse;
    try destruct v7; simpl in Hnabt; tryfalse.
    eapply mqrecv_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (*qportpost*)
    assert (Habt: qportpost vl = ABORT \/ qportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qportpost.
    do 3 try (destruct qportpost; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse;
    try destruct qportpost; simpl in Hnabt; tryfalse.
    eapply qportpost_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (*qportpend*)
    assert (Habt: qportpend vl = ABORT \/ qportpend vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v1; simpl in Hnabt; tryfalse.
    eapply qportpend_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (* sampleportpost *)
    assert (Habt: sampleportpost vl = ABORT \/ sampleportpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse.
    eapply sampleportpost_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (* portaccept *)
    assert (Habt: portaccept vl = ABORT \/ portaccept vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as qp_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v0; simpl in Hnabt; tryfalse.
    eapply portaccept_nabt_spec_step_data_equiv_tskd_preserve; eauto.
    simpl; eauto.
- (* mq_timedrecv *)
    assert (Habt: mqtimedreceive vl = ABORT \/ mqtimedreceive vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as recv_vl.
    do 11 try (destruct recv_vl; simpl in Hnabt;tryfalse);
    try destruct v; simpl in Hnabt; tryfalse;
    try destruct v1; simpl in Hnabt; tryfalse;
    try destruct v3; simpl in Hnabt; tryfalse;
    try destruct v4; simpl in Hnabt; tryfalse;
    try destruct v6; simpl in Hnabt; tryfalse.
    eapply mqtmrecv_nabt_spec_step_data_equiv_tskd_preserve; eauto. 
    simpl; auto.
    - (* bufferpost*)
    assert (Habt: buffer_apispecs.bufferpost vl = ABORT \/ buffer_apispecs.bufferpost vl <> ABORT) by tauto.
    destruct Habt as [Habt | Hnabt].
    rewrite Habt in *.
    unfold get_all_succs in Hnth.
    simpl in Hnth.
    re_err_contra n; simpl in Hnth; tryfalse.
    inverts Hnth; inverts Hstep.
    rewrite nth_error_nil in Hnth; tryfalse.
    remember vl as recv_vl.
    do 11 try (destruct qp_vl; simpl in Hnabt;tryfalse);
    try destruct v1; simpl in Hnabt; tryfalse.
    eapply bufferpost_nabt_spec_step_data_equiv_tskd_preserve; eauto. 
   - (* bufferaccept*)
   assert (Habt: buffer_apispecs.bufferaccept vl = ABORT \/ buffer_apispecs.bufferaccept vl <> ABORT) by tauto.
   destruct Habt as [Habt | Hnabt].
   rewrite Habt in *.
   unfold get_all_succs in Hnth.
   simpl in Hnth.
   re_err_contra n; simpl in Hnth; tryfalse.
   inverts Hnth; inverts Hstep.
   rewrite nth_error_nil in Hnth; tryfalse.
   remember vl as recv_vl.
   eapply bufferaccept_nabt_spec_step_data_equiv_tskd_preserve; eauto. 
   - (* bufferpend*)
   assert (Habt: buffer_apispecs.bufferpend vl = ABORT \/ buffer_apispecs.bufferpend vl <> ABORT) by tauto.
   destruct Habt as [Habt | Hnabt].
   rewrite Habt in *.
   unfold get_all_succs in Hnth.
   simpl in Hnth.
   re_err_contra n; simpl in Hnth; tryfalse.
   inverts Hnth; inverts Hstep.
   rewrite nth_error_nil in Hnth; tryfalse.
   remember vl as recv_vl.
   eapply bufferpend_nabt_spec_step_data_equiv_tskd_preserve; eauto.
Qed.

Lemma GoodStmt_noabs: 
  forall s, GoodStmt_h s -> stmt_noabs s.
Proof.
  inductions s; 
    introv HGS;
    try (simpl; auto).
  - 
    simpl in HGS.
    simpljoin.
    split; eauto.
  -
    simpl in HGS.
    simpljoin.
    split; eauto.
Qed. 

Lemma good_client_code_impl_noabs:
  forall cliprogs, 
    good_client_code cliprogs ->
    pu_noabs cliprogs.
Proof.
  introv Hgcc.
  unfolds in Hgcc.
  unfolds.
  introv Hcf.
  lets H__: Hgcc Hcf.
  apply GoodStmt_noabs; auto. 
Qed. 
  
Lemma nintr_absintcont_none: 
  forall O T t cd ke ks, 
    get O curtid = Some (oscurt t) ->
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    ~ in_intr T O ->
    absintcont ks = None.
Proof.
  introv Hgct Hgt Hnintr.
  unfolds in Hnintr.
  unfold in_intr in Hnintr.
  destruct (absintcont ks) eqn: E.
  - false.
    eapply Hnintr.
    unfold code_cur_task.
    rewrite Hgct.
    rewrite Hgt.
    do 3 eexists.
    split; eauto.
    rewrite E.
    introv Hf; false.
  - auto.
Qed. 

Theorem integrity_u_holds: 
  forall cliprogs,
    good_client_code cliprogs ->
    integrity_u (cliprogs, (api_spec, int_spec, get_hprio_d)).  
Proof. 
  introv Hgclt.
  unfold integrity_u. 
  introv Heq Hrch Hstep Hnfl. 
  inverts Heq.

  - (* show obsr. eq. for task domain *) 
    inverts Hstep.
    2: { (* the step is taken by Sched domain --- impossible *) 
      false.
      apply Hnfl.
      apply sched_flows_to_all.
    }

    (* the step is taken by task domain *) 
    match goal with H: hpstep _ _ _ _ _ _ _ _ |- _ => rename H into Hstep end.
    inverts Hstep.

    + (* htstep *) 
      match goal with
        H1: get O curtid = _, H2: get O curtid = _  |- _ => 
          rename H1 into Hctid; rewrite Hctid in H2; inverts H2
      end.
      rename t0 into t.
      match goal with
        H1: task_prio_id _ _ _, H2: task_prio_id _ _ _ |- _ =>
          lets H_: prio_unique H2 H1; subst; rename H1 into Htpi; clear H2
      end.
      match goal with
        H: htstep _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Htskstep
      end.
      inverts Htskstep; 
        try (match goal with H: (_, _) = (_, _) |- _ => inverts H end). 
      * (* cstep *)
        rename O' into O.
        unfolds.
        split.
        2: { (* data_equiv_tskd *) 
          unfold data_equiv_tskd.
          split. eapply ctid_equiv_refl; eauto.          
          split. apply reachable_get_bufsid in Hrch.
          destruct Hrch as (x & y & Hgetx & Hgety).
          eapply bufs_equiv_refl; eauto.
          split. apply reachable_get_knldataid in Hrch.
          simpljoin. eapply kernel_data_equiv_refl; eauto.
          eapply client_data_equiv_local_upd_preserve; eauto.
          eapply cstep_dom_intact; eauto. 
          introv Hf. subst td.
          false. apply Hnfl. apply flows_to_refl.
        }
        (* code_equiv_tskd *)
        eapply code_equiv_tskd_local_upd_preserve; eauto. 
      * (* hapistep *)
        (* rename hypothesis *)
        match goal with
        | H: _ = TauAct \/ _  |- _ => rename H into Hact
        end.
        match goal with
        | H: ~ in_intr _ _  |- _ => rename H into Hintr
        end.
        match goal with
        | H: nabt _  |- _ => rename H into Hnabt
        end.
        match goal with
        | H: get T _ = _  |- _ => rename H into Hgetc
        end.
        match goal with
        | H: hapistep _ _ _ _ _ _ |- _ => rename H into Hapistep
        end.
        inverts Hapistep;
          try (match goal with H: (_, _) = (_, _) |- _ => inverts H end).
        (* hapienter_step *)
        rename O' into O.
        rename cst' into cst.
        unfolds.
        split.
        eapply code_equiv_tskd_local_upd_preserve; eauto.
        eapply data_equiv_tskd_same_preserve; eauto.
        (* hidapi_step *)
        match goal with
        | H: spec_step _ _ _ _ _ _ |- _ => rename H into Hsstep
        end.
        simpl in Hsstep.
        assert (Hnabt': cd' <> ABORT).
        { unfold nabt in Hnabt.
          specialize (Hnabt t).
          rewrite set_a_get_a in Hnabt.
          specialize (Hnabt _ _ _ (eq_refl _)).
          introv Hf.
          subst.
          eapply Hnabt; eauto.
        }
        assert (Hi_neq: td <> dom_for_prio pr).
        { introv Hf.
          subst td.
          eapply Hnfl.
          apply flows_to_refl.
        }
        casetac O O' Heq HO_neq.
        subst.
        unfolds; split.
        eapply code_equiv_tskd_local_upd_preserve; eauto.
        eapply data_equiv_tskd_same_preserve; eauto.
        (* change absdata *)
        lets Hgtsk: reachable_good_tasks Hgclt Hrch.
        lets Hgtsk': Hgtsk Hgetc.
        simpl in Hgtsk'.
        destruct Hgtsk' as (Hstmt & Hks).
        destruct Hstmt as [Hapi | [Hint | [Hend | Habt]]];
          [ | | simpljoin; inverts Hsstep | subst; inverts Hsstep].
        (* api_spec *)
        destruct Hapi as (fid & acode & ft & vl & Hapi & Hcd).
        unfolds.
        split.
        eapply api_spec_step_code_equiv_tskd'_preserve; eauto.
        eapply api_spec_step_data_equiv_tskd_preserve; eauto.

        (* int_spec  *)
        simpljoin.
        unfolds in Hintr.
        lets Hpu: good_client_code_impl_noabs Hgclt. 
        lets H__: reachable_ks_noint_apicode Hpu Hrch.
        lets H_: H__ Hgetc; eauto. 
        lets Hnintr: nintr_absintcont_none Hctid Hgetc; eauto.
        specializes Hnintr; eauto.
        simpl in H_.
        destruct H_ as (Hnaapi & _).
        unfolds in Hnaapi.
        specializes Hnaapi; eauto. 
        destruct Hnaapi as [Hcd | [Hat | Hend]].
        
        lets Hgtc: reachable_good_tasks Hgclt Hrch; eauto.    
        simpljoin. 
        split.
        eapply api_spec_step_code_equiv_tskd'_preserve;eauto.
        eapply api_spec_step_data_equiv_tskd_preserve; eauto.
        subst cd.
        match goal with H: context [spec_step] |- _ => inverts H end.
        simpljoin.
        match goal with H: context [spec_step] |- _ => inverts H end.
        unfolds.
        split.
        eapply code_equiv_tskd_local_upd_preserve; eauto.
        eapply data_equiv_tskd_same_preserve; eauto.

        unfolds.
        split.
        eapply code_equiv_tskd_local_upd_preserve; eauto.
        eapply data_equiv_tskd_same_preserve; eauto.
    +
      match goal with 
        H: _ \/ _ \/ _ |- _ => 
          destruct H as [Hf | [Hf | Hf]]; simpljoin; false
      end.
    +
      match goal with 
        H: _ \/ _ \/ _ |- _ => 
          destruct H as [Hf | [Hf | Hf]]; simpljoin; false
      end.
Qed.
