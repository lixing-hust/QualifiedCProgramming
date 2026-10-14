
Require Import memory.
Require Import sem_language.
Require Import sem_init.
Require Import sem_invs.
Require Import sem_sys.
Require Import succ_gen.

Require Import join_lib.
Require Import seplog_lemmas.

Require Import sem_tacs. 
Require Import sem_lemmas.

Require Import math_auto.

Require Import assms.

Require Import steq_inv_preserve. 

Set Keyed Unification. 


Lemma sem_post_exwt_succ_cond_ge_preserve:
  forall O els eid ni ns1 na1 ns0 na0 wl gau n t, 
    cond_pv1 gau els ->
    get O absecblsid = Some (absecblist els) -> 
    get els eid = Some (abssem n, wl) ->
    get gau eid = Some {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |} -> 
    cond_pv1
      (set gau eid {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := S ns0; nacq0 := na0 |}) 
      (set els eid (abssem n, remove_tid t wl)).  
Proof.
  introv Hcge Hgels Hgsem Hgau.
  match goal with
    H: cond_pv1 ?gau ?els |- cond_pv1 ?gau'_ ?els'_ => 
      eapply cond_ge_preserve0 with (gau:=gau) (els:=els) (gau':=gau'_) (els':=els'_); eauto 
  end.
  - 
    introv Hget.
    casetac eid eid0 Ht Hf.
    + subst. rewrite set_a_get_a in Hget. inverts Hget.
      eexists; eauto.  
    + rewrite set_a_get_a' in Hget; eauto.
  -
    introv Hga.
    casetac eid eid0 Ht Hf.
    +
      subst. rewrite set_a_get_a.
      eexists. split. eauto. 
      rewrite Hgau in Hga. inverts Hga.
      simpl.
      splits; auto.
    +
      rewrite set_a_get_a'; eauto.
Qed.               

Lemma gethwait_in:
  forall x ws t, 
    GetHWait x ws t -> In t ws. 
Proof.
  intros.
  unfolds in H.
  simpljoin.
  auto.  
Qed.   

Lemma join_sig_get_r_res: 
  forall a t (tls tls': TcbMod.map) p st m sus, 
    join (sig a (p, st, m, sus)) tls' tls ->
    t <> a ->
    get tls' t = get tls t.
Proof.
  intros.
  destruct (get tls t) eqn: E.
  - eapply join_get_or in E; eauto.
    destruct E as [Hf | Ht].
    + rewrite get_a_sig_a' in Hf. false.
      auto.
    + auto. 
  - eapply join_get_none_rev2; eauto. 
Qed.

Lemma sem_post_exwt_succ_n_wait_rdy_eq_S: 
  forall ts tls t p eid0 ot m sus laump lau, 
    get tls t = Some (p, wait (os_stat_sem eid0) ot, m, sus) -> 
    get laump t = Some lau ->
    tskpt lau = PtPend (Vptr eid0) -> 
    atids_valid tls ts -> 
    n_wait_rdy eid0 ts (set tls t (p, rdy, Vnull, sus)) laump =
      S (n_wait_rdy eid0 ts tls laump). 
Proof.
  induction ts.
  -
    introv Hgtls Hgl Htl Hav.
    unfolds in Hav.
    destruct Hav as (_ & Ha).
    specialize (Ha t).
    unfolds in Ha.
    destruct Ha as (Hf & _).
    false. eapply in_nil. eapply Hf.
    introv Hnone.
    rewrite Hnone in Hgtls.
    false. 
  -
    introv Hgtls Hgl Htl Hav.
    lets Hdc: atids_valid_decomp Hav; eauto.
    destruct Hdc as (p_ & st_ & m_ & sus_ & Hgtls_ & Hex).
    destruct Hex as (tls' & Hjo & Hav').
    do 2 rewrite n_wait_rdy_prop. 
    rewrite Hgtls_.
    assert (Hne: forall t, In t ts -> t <> a).
    {
      unfolds in Hav.
      destruct Hav as (Hds & Hav).
      lets Hf_: distinct_in_contr Hds; eauto.
      introv Hin.
      introv Heq. subst. false.                     
    }
    casetac t a Ht Hf.
    + subst. 
      rewrite set_a_get_a.
      rewrite Hgl.
      destruct st_ eqn: Est_.
      {
        rewrite Hgtls in Hgtls_.
        inverts Hgtls_.
      }
      {
        destruct lau eqn: Elau.
        simpl in Htl. subst tskpt.
        rewrite Hgtls in Hgtls_.
        inverts Hgtls_.
        rewrite beq_tid_true.
        apply eq_S.
        assert (Haeq': forall t, In t ts -> get (set tls a (p_, rdy, Vnull, sus_)) t = get tls t).
        {
          introv Hin.
          eapply Hne in Hin; eauto.
          rewrite set_a_get_a'; eauto.
        }
        eapply n_wait_rdy_change_tls; eauto.
        {
          introv Hin. eapply Hne in Hin; eauto.
          rewrite set_a_get_a'; eauto. 
        }
      }
    +
      assert (Hg': get tls' t = Some (p, wait (os_stat_sem eid0) ot, m, sus)).
      {
        match goal with
          Hgtls: get tls t = Some ?e, Hjo: join ?tls0 tls' tls |- get tls' t = Some ?e' => 
            assert (Hor: get tls0 t = Some e \/ get tls' t = Some e)
        end.
        eapply join_get_or; eauto.
        destruct Hor as [Hgll | Hgrr].
        -  rewrite get_a_sig_a' in Hgll; eauto.
           false.
        - auto.
      }                  
      assert (Hrw1:
               n_wait_rdy eid0 ts (set tls t (p, rdy, Vnull, sus)) laump =
                 n_wait_rdy eid0 ts (set tls' t (p, rdy, Vnull, sus)) laump).
      {
        eapply n_wait_rdy_change_tls; eauto.
        {
          introv Hin.
          casetac t t0 Ht_ Hf_.
          - subst. do 2 rewrite set_a_get_a. auto.
          - do 2 (rewrite set_a_get_a'; eauto).  
            eapply Hne in Hin; eauto.
            eapply join_sig_get_r_res; eauto. 
        }                    
      }
      rewrite Hrw1.
      assert (Hrw2: n_wait_rdy eid0 ts tls laump = n_wait_rdy eid0 ts tls' laump).
      {
        eapply n_wait_rdy_change_tls; eauto.
        introv Hin.
        eapply Hne in Hin; eauto.
        eapply join_sig_get_r_res; eauto. 
      }
      rewrite Hrw2.
      
      rewrite set_a_get_a'; eauto.
      rewrite Hgtls_.
      destruct st_ eqn: Est_.
      destruct (get laump a) eqn: Egl.
      destruct l.
      destruct tskpt. 
      destruct vp eqn: Evp.
      {
        eapply IHts; eauto.
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      destruct (beq_tid eid0 a0) eqn: Ebeq.
      {
        apply eq_S. 
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto.  
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      {
        eapply IHts; eauto. 
      }
      
Qed. 

Lemma sem_post_exwt_succ_cond_aux_preserve: 
  forall O (els: EcbMod.map) (tls: TcbMod.map) ts gau laump n (p: priority) (sus:susstatus)
         t wl ni ns1 na1 ns0 na0 (st: taskstatus) (m:msg) eid, 
    cond_pv0 els tls ts gau laump ->
    get O abstcblsid = Some (abstcblist tls) ->
    get O absecblsid = Some (absecblist els) -> 
    wait_progpt els laump -> 
    get els eid = Some (abssem n, wl) -> 
    get tls t = Some (p, st, m, sus) ->
    GetHWait tls wl t -> 
    get gau eid = Some {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=ns0; nacq0:=na0|} -> 
    atids_valid tls ts -> 
    cond_pv0
      (set els eid (abssem n, remove_tid t wl))
      (set tls t (p, rdy, Vnull, sus))
      ts
      (set gau eid {| ninit:=ni; nsig1:=ns1; nacq1:=na1; nsig0:=S ns0; nacq0:=na0 |})
      laump. 
Proof.
  introv Hca Hgtls Hgels Hwp Hge Hgt Hgw Hgg Hav.
  unfold cond_pv0 in *.
  introv Hge_.
  lets Hinwl: gethwait_in Hgw; eauto.          
  lets H0_: sem_tst_est_ Hgtls Hgels; eauto.
  specializes H0_; eauto.
  destruct H0_ as (p_ & ot_ & m_ & sus_ & Hg).
  rewrite Hg in Hgt. 
  inverts Hgt.
  
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hge_.
    inverts Hge_.
    lets Heq: Hca Hge; eauto.
    destruct Heq as (ga & Hgga & Heq).
    rewrite Hgg in Hgga. inverts Hgga.
    simpl in Heq.
    rewrite set_a_get_a.
    eexists.
    split; eauto.
    simpl.        
    unfolds in Hwp.
    lets Hpt: Hwp Hge Hinwl; eauto.
    simpljoin. 
    erewrite sem_post_exwt_succ_n_wait_rdy_eq_S; eauto.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hge_; eauto.
    lets H__: Hca Hge_; eauto.
    destruct H__ as (ga_ & Hgg_ & Heq_).
    eexists.
    split; eauto.
    unfolds in Hwp.
    apply gethwait_in in Hgw.
    lets Hpt: Hwp Hge Hgw; eauto.
    destruct Hpt as (lau_ & Hgl_ & Hpt_).
    match goal with
      Heq_: _ = (_ + ?e1)%nat |- _ = (_ + ?e2)%nat =>
        assert (e1 = e2)
    end.
    {
      eapply n_wait_rdy_lem; eauto.
      introv Hin0.
      casetac t t0 Htt Hff.
      - subst. rewrite set_a_get_a.
        rewrite Hg.
        rewrite Hgl_.
        destruct lau_ eqn: El_.
        simpl in Hpt_. subst tskpt.
        destruct (beq_tid eid0 eid) eqn: E'.
        eapply beq_tid_true_eq in E'; eauto; subst.
        auto. 
      - rewrite set_a_get_a'; eauto. 
    }
    congruence. 

Qed. 

Lemma sem_post_exwt_succ_wait_progpt_preserve:
  forall els eid n wl laump t, 
    get els eid = Some (abssem n, wl) -> 
    wait_progpt els laump ->
    wait_progpt (set els eid (abssem n, remove_tid t wl)) laump. 
Proof.
  introv Hge Hwp.
  unfold wait_progpt in *.
  introv Hg Hin.
  casetac eid eid0 Ht Hf.
  - subst. rewrite set_a_get_a in Hg.
    inverts Hg.
    lets H__: Hwp Hge; eauto.
    eapply in_remove_tid in Hin; eauto.
  - rewrite set_a_get_a' in Hg; eauto.
Qed.             

Lemma dtinv_sem_post_exwt_succ_preserve:
  forall v1 v2 v' O0 O0' Of O O' laump, 
    sem_post_ex_wt_succ (v1 :: v2 :: nil) O0 (v', Some O0') ->
    join O0 Of O ->
    join O0' Of O' ->
    dtinv O laump ->
    dtinv O' laump.
Proof.
  introv Hsp Hjo Hjo' Hdti.
  inverts Hsp.
  simpljoin.
  inv_some.
  inv_lst.
  unfolds.
  unfolds in Hdti.
  simpljoin.
  kvext O0 abstcblsid O.
  l_rew21 (get O abstcblsid).
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  kvext_h Hjo' abstcblsid O'.
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  assert (get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O atidlsid).
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  splits.
  - (* atids_valid *) 
    eapply atids_valid_set_tcb_preserve; eauto.
  - (* cond_pv1 *)
    eapply sem_post_exwt_succ_cond_ge_preserve; eauto.
  - (* cond_pv0 *)             
    eapply sem_post_exwt_succ_cond_aux_preserve; eauto. 
  - (* wait_progpt *)            
    eapply sem_post_exwt_succ_wait_progpt_preserve; eauto.
  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false.
      apply Hnex. do 2 eexists; eauto.
    + introv Hg.
      rewrite set_a_get_a' in Hnex; eauto.
Qed.

Lemma cond_ge_sem_post_succ_put_preserve:
  forall gau els eid ni ns1 na1 ns0 na0 n wl, 
    get gau eid = Some {| ninit := ni; nsig1 := ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |} ->
    get els eid = Some (abssem n, wl) -> 
    Int.ltu n ($ 65535) = true -> 
    cond_pv1 gau els ->
    cond_pv1
      (set gau eid {| ninit := ni; nsig1 := S ns1; nacq1 := na1; nsig0 := ns0; nacq0 := na0 |})
      (set els eid (abssem (n +ᵢ  Int.one), wl)).
Proof.
  introv Hgg Hge Hlt Hcg.
  unfold cond_pv1 in *.
  lets H__: Hcg Hge; eauto.
  simpljoin.
  introv Hg.
  casetac eid eid0 Ht Hf.
  -
    subst. rewrite set_a_get_a in Hg. inverts Hg.
    split; auto.
    clear -Hlt.
    int auto.
    int auto.
    rewrite set_a_get_a. 
    eexists.
    split; eauto.
    simpl ninit. simpl nsig1. simpl nacq1.
    rewrite Nat2Z.inj_succ.
    rewrite H0 in Hgg.
    inverts Hgg.
    simpl in H1.
    int auto.
    int auto. 
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hg; eauto.
Qed.

Lemma dtinv_sem_post_put_succ_preserve:
  forall v1 v2 v' O0 O0' Of O O' laump, 
    sem_post_put_sem_in_succ (v1 :: v2 :: nil) O0 (v', Some O0') ->   
    join O0 Of O ->
    join O0' Of O' ->
    dtinv O laump ->
    dtinv O' laump.
Proof. 
  introv Hsp Hjo Hjo' Hdti.
  inverts Hsp.
  simpljoin.
  rem_dis.
  inv_some.
  inv_lst.
  unfold dtinv in *.
  simpljoin.
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  assert (Hgaeq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O atidlsid).
  assert (Hgteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  l_rew21 (get O abstcblsid).
  do 4 eexists.
  split; eauto.
  split; eauto. 
  split; eauto.
  split; eauto.
  splits.
  - (* atids_valid *)
    auto.
    
  - (* cond_pv1 *)
    eapply cond_ge_sem_post_succ_put_preserve; eauto. 
    
  - (* cond_pv0 *)
    eapply cond_aux_same_laust_preserve; eauto. 

  - (* wait_progpt *)
    eapply wait_progpt_same_laust_preserve; eauto.

  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex.
    casetac x eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false.
      apply Hnex. do 2 eexists; eauto.
    + rewrite set_a_get_a' in Hnex; eauto. 

Qed. 

    
(* for debugging *) 
Ltac symexe_ :=
  match goal with
    H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; idtac "inverts a step"
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; idtac "inverts an atomic op"
  | H: ~(get ?O _ = get ?O _ /\ _ /\ _ /\ _ /\  ?lau = ?lau) |- _ => false; apply H; splits; auto; idtac "solve_steq"
  | H: _ :: _ = _ :: _ |- _ => inverts H; idtac "inverts equality of lists"
  | H: _ \/ _ /\ Some _ = None |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ /\ None = Some _ \/ _ |- _=> inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ /\ Some _ = None \/ _ |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: _ \/ _ /\ None = Some _ |- _ => inverts H; simpljoin; tryfalse; idtac "rem_dis"
  | H: Some _ = Some _ |- _ => inverts H; idtac "inv_some"
  | H: Some _ = None |- _ => inverts H; idtac "Some _ = None" 
  | H: None = Some _ |- _ => inverts H; idtac "None = Some _"
  | H: join ?O0 ?Of ?O, H': join ?O0 ?Of ?O' |- _ =>
      assert (O = O') by (join auto); subst; idtac "same O"
  | _ => idtac
  end.

Ltac symexe0 :=
  match goal with
    H: spec_step _ _ _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; symexe0
  | H: ~(get ?O _ = get ?O _ /\ _ /\ _ /\ _ /\ ?lau = ?lau) |- _ => false; apply H; splits; auto; symexe0
  | H: _ :: _ = _ :: _ |- _ => inverts H; symexe0
  | H: _ \/ _ /\ Some _ = None |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: _ /\ None = Some _ \/ _ |- _=> inverts H; simpljoin; tryfalse; symexe0
  | H: _ /\ Some _ = None \/ _ |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: _ \/ _ /\ None = Some _ |- _ => inverts H; simpljoin; tryfalse; symexe0
  | H: Some _ = Some _ |- _ => inverts H; symexe0
  | H: Some _ = None |- _ => inverts H; symexe0
  | H: None = Some _ |- _ => inverts H; symexe0
  | H: join ?O0 ?Of ?O, H': join ?O0 ?Of ?O' |- _ =>
      assert (O = O') by (join auto); subst; symexe0  
  | _ => idtac
  end.

Ltac symexe k :=
  destruct k; [
      match goal with
        H: context [nth_error] |- _ => 
          simpl in H;
          inverts H;
          symexe0        
      end |
      idtac
    ].

Ltac solve_endabt :=
  simpljoin; solve
               [ tryfalse
               | false;
                 match goal with
                   H: ~(exists _, END _ = END _) |- _ => apply H; eexists; eauto 
                 | H: ABORT <> ABORT |- _ => apply H; auto
                 end]. 


Set Printing Depth 1000.

Lemma sem_signal_preserves_inv_: 
  forall k vl cd cd' sc O O' lau lau' t (laump laump': LAuxStMod.map), 
    nth_error (get_all_succs (semsignal vl)) k = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    ~(get O abstcblsid = get O' abstcblsid /\
        get O absecblsid = get O' absecblsid /\
        get O gauxstid = get O' gauxstid /\
        get O atidlsid = get O' atidlsid /\ 
        lau = lau') -> 
    get O curtid = Some (oscurt t) -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Hnth Hstep Hneq Hct Hlau Hlau' Hsatinv.
  repeat (destruct vl; 
          [simpl in Hnth; 
           apply abt_succs_contra in Hnth;
           subst; 
           inverts Hstep | idtac]).
  destruct vl.  
  2: {
    simpl in Hnth. apply abt_succs_contra in Hnth; subst.
    inverts Hstep.
  }

  symexe k. 
  symexe k.
  symexe k.
  symexe k.
  symexe k. 
  symexe k.
  symexe k. 
  symexe k. 
  symexe k. 
  symexe k.
  symexe k. 
  symexe k.
  symexe k.
  symexe k. 
  symexe k. 
  symexe k.   
  symexe k.   
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.

  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    invstep0.
    invstep0.
    solve_steq.
    invstep0.
    invstep0. 
    {
      assert (Hseq: set laump t lau' = laump).
      { eapply get_set_same; eauto. }
      rewrite Hseq in Hlau'. subst.  
      eapply dtinv_sem_post_exwt_succ_preserve; eauto. 
    }
    solve_endabt.
    invstep0; solve_endabt. 
  }
  
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.

  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.    
    {
      assert (Hseq: set laump t lau' = laump).
      { eapply get_set_same; eauto. }
      rewrite Hseq in Hlau'. subst.  
      eapply dtinv_sem_post_put_succ_preserve; eauto.
    }
    invstep0.
    solve_steq.
    invstep0; solve_endabt. 
  }

  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.

  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    invstep0.
    invstep0.
    solve_steq.
    invstep0.
    invstep0. 
    {
      assert (Hseq: set laump t lau' = laump).
      { eapply get_set_same; eauto. }
      rewrite Hseq in Hlau'. subst.  
      eapply dtinv_sem_post_exwt_succ_preserve; eauto.       
    }
    solve_endabt.
    invstep0; solve_endabt. 
  }
  
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  symexe k.
  
  destruct k.
  {
    simpl in Hnth; inverts Hnth.
    invstep0.
    invstep0.
    {
      assert (Hseq: set laump t lau' = laump).
      { eapply get_set_same; eauto. }
      rewrite Hseq in Hlau'. subst.  
      eapply dtinv_sem_post_put_succ_preserve; eauto.
    }
    invstep0.
    solve_steq.
    invstep0; solve_endabt. 
  }

  symexe k.
  symexe k.
  symexe k.
  simpl in Hnth.
  rewrite nth_error_nil in Hnth.
  false. 
Qed. 

 
  
  

