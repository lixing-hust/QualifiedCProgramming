
Require Import sem_sys. 
Require Import sem_init.
Require Import sem_invs. 

Require Import init_inv_satisfied.
Require Import step_inv_preserved.
Require Import good_code.
Require Import sem_destroy_preserves_inv.

Require Import rc_no_subabs.
(* Require Import rc_kevt_nonest. *)
Require Import rc_nknl_nkevt.
Require Import rc_int_code. 
Require Import asrt_sat_apis.
Require Import asrt_sat.

Require Import sem_tacs. 

Require Import join_lib.

Definition pool_no_pend_on_del T O (laust: LAuxStMod.map) := 
  forall t cd ke ks,
    get T t = Some (curs (hapi_code cd), (ke, ks)) ->
    no_pend_on_deletion cd O laust. 

Axiom no_task_pending_on_sem_to_be_deleted: 
  forall T O aust, pool_no_pend_on_del T O aust. 

Lemma dtinv_set_curt_preserved: 
  forall O aust t, 
    dtinv O aust ->
    dtinv (set O curtid (oscurt t)) aust. 
Proof.
  introv Hdt.
  unfold dtinv in *.
  simpljoin.
  do 4 eexists; splits; eauto; 
  rewrite set_a_get_a'; eauto; 
  introv Hf; inverts Hf.
Qed.       
                    
Lemma dtinv_hpstepok_preserve:
  forall pu T cst O aust T' cst' O' aust', 
    (* good_client_code pu -> *)
    pool_int_code T -> 
    pool_hasrt_sat T aust -> 
    hpstep_ok (pu, os_spec') T cst O aust T' cst' O' aust' ->  
    pool_no_pend_on_del T O aust -> 
    good_task_code T ->  
    dtinv O aust ->
    dtinv O' aust'. 
Proof.
  introv (* Hgcc  *)Hatc Hhs Hhp Hpn Hgtc Hdt.
  inverts Hhp.
  inverts H.
  -
    match goal with H: context[htstep] |- _ => inverts H end.
    +
      match goal with H: (_, _) = _ |- _ => inverts H end.
      assert (Hseq: set aust t lau' = aust).
      { eapply get_set_same; eauto. }
      congruence.
    +
      match goal with H: (_, _) = _ |- _ => inverts H end.
      match goal with H: context[hapistep] |- _ => inverts H end.
      * (* hapienter_step *) 
        assert (Hseq: set aust t lau' = aust).
        { eapply get_set_same; eauto. }
        congruence.
      * (* hidapi_step *)
        unfolds in Hatc.
        match goal with
          H: get T t = _ |- _ => lets H__: Hatc H; eauto
        end.
        simpl in H__.
        assert (Hnone: absintcont ks = None).
        {
          casetac (absintcont ks) (None: option stmtcont) Ht Hf.
          - auto.
          - destruct H__ as (H__ & Hcont).
            specializes H__; eauto.
            destruct H__ as (iid & isr & His & _).
            unfolds in His. unfold int_spec_list in His.
            simpl in His. tryfalse. 
        }
        clear H__.
        assert (Hhsat: head_asrt_sat cd lau).
        {
          match goal with
            H: get T t = _ |- _ => lets H__: Hhs H; eauto
          end.
          specializes H__; eauto.
          unfolds in H__.
          destruct H__ as (c0 & ke0 & ks0 & Heq & Himpl & Hcont).
          inverts Heq.  
          specializes Himpl; eauto.
          destruct Himpl as (Hsat & Hnml).
          specializes Hsat; eauto. 
        }
        specializes Hgtc; eauto.
        simpl in Hgtc.
        destruct Hgtc as (Hga & _).
        unfolds in Hga.
        destruct Hga as [Ha | [He | Habt]].
        **
          destruct Ha as (fid & ac & ft & vl & Hac & Hin).
          unfolds in Hac.
          unfold api_spec_list' in Hac.
          simpl in Hac.
          destruct (Zeq_bool sem_trywait fid) eqn: eq1;
            try destruct (Zeq_bool sem_wait fid) eqn: eq2;
            try destruct (Zeq_bool sem_timedwait fid) eqn: eq3; 
            try destruct (Zeq_bool sem_signal fid) eqn: eq4;
            try destruct (Zeq_bool sem_init fid) eqn: eq5;
            try destruct (Zeq_bool sem_init_bin fid) eqn: eq6; 
            try destruct (Zeq_bool sem_destroy fid) eqn: eq7;
            try inverts Hac;
            tryfalse; 
            try rewrite <- Zeq_is_eq_bool in eq1;
            try rewrite <- Zeq_is_eq_bool in eq2;
            try rewrite <- Zeq_is_eq_bool in eq3;
            try rewrite <- Zeq_is_eq_bool in eq4;
            try rewrite <- Zeq_is_eq_bool in eq5;
            try rewrite <- Zeq_is_eq_bool in eq6;
            try rewrite <- Zeq_is_eq_bool in eq7; 
            subst;
            tryfalse.           
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_trywait_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_wait_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_timedwait_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_signal_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_init_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_initbin_preserves_inv; eauto.
          ***
            eapply In_nth_error in Hin; eauto.
            destruct Hin.
            eapply sem_destroy_preserves_inv; eauto.

        **
          simpljoin.
          match goal with H: context[spec_step] |- _ => inverts H end.
        **
          subst.
          match goal with H: context[spec_step] |- _ => inverts H end.
          
      * (* hapi_exit_step *)
        assert (Hseq: set aust t lau' = aust).
        { eapply get_set_same; eauto. }
        congruence.
        
      * (* hint_exit_step *)
        assert (Hseq: set aust t lau' = aust).
        { eapply get_set_same; eauto. }
        congruence.
        
  -
    match goal with H: (_, _) = _ |- _ => inverts H end.
    match goal with H: context[htistep] |- _ => inverts H end.
    unfolds in H.
    unfold int_spec_list in *.
    simpl in H.
    tryfalse.

  -
    eapply dtinv_set_curt_preserved; eauto. 
    
Qed.

Lemma dtinv_hpstepokstar_preserve:
  forall pu T cst O aust T' cst' O' aust', 
    good_client_code pu ->
    pool_nknl_nkevt T->
    task_pool_no_sub_abs T->
    (* pool_kevt_no_nest T ->       *)
    pool_int_code T -> 
    pool_hasrt_sat T aust -> 
    hpstepokstar (pu, os_spec') T cst O aust T' cst' O' aust' ->  
    good_task_code T ->  
    dtinv O aust ->
    dtinv O' aust'. 
Proof.
  introv Hgcc Hpnn Hpns (* Hknn *) Hatc Hhs Hsteps.
  remember (pu, os_spec') as hp.
  induction Hsteps; introv Hgtc Hdt.
  -
    auto.
  -
    match goal with
      H: context[hpstep_ok] |- _ => assert (Hsp:=H); inverts H
    end.
    unfold os_spec' in *. 
    lets IH: IHHsteps Heqhp; eauto; subst p.
    eapply nknl_nkevt_hpstep_preserve; eauto.
    eapply noabs_preserve_hpstep; eauto.
    { eapply good_client_code_impl_noabs; eauto. }
    eapply pool_int_code_hpstep_preserve; eauto.
    eapply hsat_preserve_hpstep; eauto.
    
    lets Hdti': dtinv_hpstepok_preserve Hsp; eauto. 
    lets Haxm: no_task_pending_on_sem_to_be_deleted T O aust.
    specializes Hdti'; eauto.
    eapply IH; eauto.
    eapply hpstep_goodcode_h; eauto. 
Qed. 

Theorem reachable_dtinv_sat:
  forall cliprogs T cst O aust,
    good_client_code cliprogs ->
    reachable (cliprogs, os_spec') T cst O aust ->
    dtinv O aust. 
Proof.
  introv Hgc Hr.
  destruct Hr as (pu & spc & Heq & Hr).
  inverts Heq.
  destruct Hr as (T0 & cst0 & O0 & aust0 & Hini & Hsp).
  assert (Hdtinv0: dtinv O0 aust0).
  { eapply init_inv; eauto. }
  assert (Hrc: reachable (pu, os_spec') T0 cst0 O0 aust0).
  {
    unfolds.
    do 2 eexists.
    splits; eauto.
    do 4 eexists.
    split; eauto.
    constructors.
  }
  
  eapply dtinv_hpstepokstar_preserve; eauto.
  eapply reachable_nknl_nkevt; eauto.
  {
    eapply reachable_no_sub_abs; eauto.
    eapply good_client_code_impl_noabs; eauto.
  }
  {
    eapply reachable_apicode_type_c; eauto.
    eapply good_client_code_impl_noabs; eauto.
  }
  eapply reachable_hasrt_sat; eauto.
  {
    unfolds in Hini. simpljoin.
    eapply init_good_tasks; eauto.
  }
Qed.


