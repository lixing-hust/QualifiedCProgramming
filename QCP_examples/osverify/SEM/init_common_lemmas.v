
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

Set Keyed Unification. 

Lemma dtinv_seminit_set_placeholder_preserve:
  forall O O0 O0' Of O' laump v1 v2, 
    dtinv O laump ->
    join O0 Of O ->
    seminit_set_placeholder (v1 :: nil) O0 (v2, Some O0') ->
    join O0' Of O' -> 
    dtinv O' laump. 
Proof.
  introv Hdti Hjo Hssp Hjo'.
  inverts Hssp.
  simpljoin.
  inv_lst.
  unfold dtinv in *.
  simpljoin.
  inv_some.
  assert (Hteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Htideq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Heeq: get O absecblsid = get O' absecblsid). 
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.
  }
  assert (Hauxeq: get O gauxstid = get O' gauxstid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto.          
  }
  rewrite <- Hteq.
  rewrite <- Htideq.
  rewrite <- Heeq.
  rewrite <- Hauxeq.
  do 4 eexists. 
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto. 
Qed. 



Lemma npt_zero_wait_rdy:
  forall ts eid0 tls laump, 
    atids_valid tls ts -> 
    (forall t : tid, In t ts -> get laump t <> Some {| tskpt := PtPend (Vptr eid0) |} ) ->
    n_wait_rdy eid0 ts tls laump = 0%nat.
Proof.
  induction ts.
  - intros.
    unfolds. simpl. auto.
  - introv Hav Ha.
    erewrite n_wait_rdy_prop; eauto.
    lets H__: atids_valid_decomp Hav; eauto.
    destruct H__ as (p & st & m & sus & Hgta & Hex).
    destruct Hex as (tls' & Hjo & Hav').
    assert (Hrw: get tls a = Some (p, st, m, sus)).
    {
      join auto.
    }
    rewrite Hrw.
    assert (Hagr: forall t, In t ts -> get tls' t = get tls t).
    {
      unfolds in Hav'. destruct Hav' as (Hds & Ha').
      introv Hin.
      eapply Ha' in Hin; eauto.
      assert (Hex: exists tcb, get tls' t = Some tcb).
      {
        destruct (get tls' t) eqn: E.
        eexists; eauto.
        false. 
      }
      destruct Hex as (tcb & Hgt').
      assert (Hgtcb: get tls t = Some tcb).
      {
        eapply join_get_get_r; eauto. 
      }
      congruence. 
    }
    destruct st.
    +
      assert (Ha_ := Ha).
      specializes Ha; eauto.
      instantiate (1:=a).
      simpl. left; auto.
      destruct (get laump a) eqn: E.
      * destruct l.
        **
          destruct tskpt.
          ***
            destruct vp.
            {
              lets H__: n_wait_rdy_change_tls Hagr; eauto.
              erewrite H__.
              eapply IHts; eauto.
              introv Hin.
              eapply Ha_; eauto.
              simpl. right; auto.
            }
            {
              lets H__: n_wait_rdy_change_tls Hagr; eauto.
              erewrite H__.
              eapply IHts; eauto.
              introv Hin.
              eapply Ha_; eauto.
              simpl. right; auto.                      
            }
            {
              lets H__: n_wait_rdy_change_tls Hagr; eauto.
              erewrite H__.
              eapply IHts; eauto.
              introv Hin.
              eapply Ha_; eauto.
              simpl. right; auto.                      
            }
            destruct (beq_tid eid0 a0)  eqn: E'.
            ****
              eapply beq_tid_true_eq in E'; eauto. 
              subst.
              false.
            ****
              casetac eid0 a0 Htt Hff.
              *****
                subst.
              rewrite beq_tid_true in E'. false.
              *****
                lets H__: n_wait_rdy_change_tls Hagr; eauto.
              erewrite H__.
              eapply IHts; eauto.
              introv Hin.
              eapply Ha_; eauto.
              simpl. right; auto.                      
          ***
            lets H__: n_wait_rdy_change_tls Hagr; eauto.
            erewrite H__.
            eapply IHts; eauto.
            introv Hin.
            eapply Ha_; eauto.
            simpl. right; auto.                      
      *
        lets H__: n_wait_rdy_change_tls Hagr; eauto.
        erewrite H__.
        eapply IHts; eauto.
        introv Hin.
        eapply Ha_; eauto.
        simpl. right; auto.                      
    +
      lets H__: n_wait_rdy_change_tls Hagr; eauto.
      erewrite H__.
      eapply IHts; eauto.
      introv Hin.
      eapply Ha; eauto.
      simpl. right; auto.                      
Qed.

Lemma cond_ge_semcre_ecb_activate_preserve: 
  forall gaump els eid n,
    cond_pv1 gaump els ->
    get els eid = None -> 
    (Int.unsigned n <=? Int16.max_unsigned) = true -> 
    cond_pv1 (set gaump eid (gau_init n)) (set els eid (abssem n, nil)).
Proof.
  introv Hcg Hge Hrgn.
  unfold cond_pv1 in *.
  introv Hg'.
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hg'.
    inverts Hg'.
    rewrite set_a_get_a.
    split.
    + unfolds Int.ltu.
      destruct (zlt (Int.unsigned n0) (Int.unsigned ($ 65536))) eqn: E.
      auto.
      assert (Hf: Int.unsigned n0 <= Int16.max_unsigned).
      {
        int auto.
      }
      false.
      change (Int16.max_unsigned) with (65535) in Hf.
      change (Int.unsigned ($ 65536)) with 65536 in g.
      auto with zarith.
    +
      unfolds gau_init.
      eexists.
      split; eauto.
      simpl.
      auto with zarith.
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hg'; eauto.
Qed. 

Lemma cond_aux_semcre_ecb_activate_preserve:
  forall els tls ts gaump laump eid n, 
    cond_pv0 els tls ts gaump laump ->
    atids_valid tls ts -> 
    none_progpt els laump ts -> 
    get els eid = None -> 
    cond_pv0 (set els eid (abssem n, nil)) tls ts (set gaump eid (gau_init n)) laump. 
Proof.
  introv Hca Hav Hnp Hge.
  unfold cond_pv0 in *.
  introv Hg.
  casetac eid eid0 Ht Hf.
  - subst.
    rewrite set_a_get_a in Hg.
    inverts Hg. 
    rewrite set_a_get_a.
    eexists.
    split; eauto.
    simpl.
    unfolds in Hnp.
    assert (Hnpt: forall t : tid, In t ts -> get laump t <> Some {| tskpt := PtPend (Vptr eid0) |}).
    {
      eapply Hnp; eauto.
      introv Hex. simpljoin.
      rewrite H in Hge. inverts Hge.
    }                   
    
    erewrite npt_zero_wait_rdy; eauto. 
  -
    rewrite set_a_get_a'; eauto.
    rewrite set_a_get_a' in Hg; eauto. 
Qed.                  

Lemma dtinv_semcre_ecb_activate_preserve:
  forall laump O0 O0' Of O O' v0 v1 v2 , 
    dtinv O laump ->
    join O0 Of O ->
    semcre_ecb_activate (v0 :: v1 :: nil) O0 (v2, Some O0') ->
    join O0' Of O' ->
    dtinv O' laump.
Proof.
  introv Hdti Hjo Hsea Hjo'.
  unfold dtinv in *.
  simpljoin.
  inverts Hsea.
  simpljoin.
  inv_lst.
  inv_some.
  kvext_h Hjo' absecblsid O'.
  kvext_h Hjo' gauxstid O'.
  assert (Hteq: get O abstcblsid = get O' abstcblsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  assert (Htieq: get O atidlsid = get O' atidlsid).
  {
    lets H__: join_get_same_l Hjo Hjo'; eauto.
    repeat rewsimp; auto. 
  }
  rewrite <- Hteq. 
  rewrite <- Htieq.
  kvext O0 gauxstid O.
  l_rew21 (get O gauxstid).
  kvext O0 absecblsid O.
  l_rew21 (get O absecblsid).
  do 4 eexists.
  split; eauto.
  split; eauto.
  split; eauto.
  split; eauto.
  splits.
  - (* atids_valid *)
    auto.
  - (* cond_pv1 *)
    eapply cond_ge_semcre_ecb_activate_preserve; eauto.
  -  (* cond_pv0 *)
    eapply cond_aux_semcre_ecb_activate_preserve; eauto.    
  - (* wait_progpt *)
    unfold wait_progpt in *.
    introv Hg.
    casetac x4 eid Ht_ Hf_.
    +  subst. rewrite set_a_get_a in Hg.
       inverts Hg.
       introv Hf.
       simpl in Hf.
       false.
    + rewrite set_a_get_a' in Hg; eauto.      
  - (* none_progpt *)
    unfold none_progpt in *.
    introv Hnex. 
    casetac x4 eid Ht Hf.
    + subst.
      rewrite set_a_get_a in Hnex.
      false.
      eapply Hnex; eauto.
    + rewrite set_a_get_a' in Hnex; eauto.
Qed.

Lemma seminit_set_ecb_ptr_geq:
  forall O O0 O0' Of O' v1 v2 v3, 
    seminit_set_ecb_ptr (v1 :: v2 :: nil) O0 (v3, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid). 
Proof.
  introv Hss Hjo Hjo'.
  inverts Hss.
  simpljoin.
  inv_lst.
  inv_some.
  splits.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
Qed.

Lemma seminit_set_type_geq:
  forall O O0 O0' Of O' v1 v2,  
    seminit_set_type (v1 :: nil) O0 (v2, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid). 
Proof.
  introv Hss Hjo Hjo'.
  inverts Hss.
  simpljoin.
  inv_lst.
  inv_some.
  splits.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
Qed.

Lemma seminit_set_type_bin_geq:
  forall O O0 O0' Of O' v1 v2,  
    seminit_set_type_bin (v1 :: nil) O0 (v2, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid). 
Proof.
  introv Hss Hjo Hjo'.
  inverts Hss.
  simpljoin.
  inv_lst.
  inv_some.
  splits.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
Qed.

Lemma seminit_set_sem_geq:
  forall O O0 O0' Of O' v1 v2 v3,  
    seminit_set_sem (v1 :: v2 :: nil) O0 (v3, Some O0') -> 
    join O0 Of O ->
    join O0' Of O' -> 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid). 
Proof.
  introv Hss Hjo Hjo'.
  inverts Hss.
  simpljoin.
  inv_lst.
  rem_dis.
  inv_some.
  splits.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
  - lets H__: join_get_same_l Hjo Hjo'; eauto.
    rewsimp. auto.
Qed.
