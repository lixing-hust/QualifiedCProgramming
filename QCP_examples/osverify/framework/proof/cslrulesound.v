Require Import sound_include.
Require Import Lia.

Lemma cslsemacc_rule_sound:
 forall  Spec sd  I r ri p e1 e2 v1 l n aop0 aop1 pa t x,
 can_change_aop p ->
 (Z.of_nat n <= Int.max_unsigned)%Z ->
  e2 = evar x ->
 (p ** PV l @ Tint8 |-> v1) ==> Rv e1 @ Tint8 == Vint32 ((Int.repr (Z.of_nat n))) //\\ Lv e2 @ Tint8 == l ->
 (p ** PV l @ Tint8 |-> Vint32 Int.zero)  ==> CurLINV pa t ->
 (p ** PV l @ Tint8 |-> Vint32 Int.one)  ==> CurLINV pa t ->
 RuleSem Spec sd pa I r ri
  (<|| cslsemacc n (Vint32 Int.zero) ;; aop0 ?? cslsemacc n (Vint32 Int.one) ;; aop1 ||> ** p ** PV l @ Tint8 |-> v1)
  (sprim (scsl_semaccdir e1 e2))
  ( (<|| aop0 ||>  ** p ** PV l @ Tint8 |-> Vint32 Int.zero) \\//  (<|| aop1 ||>  ** p ** PV l @ Tint8 |-> Vint32 Int.one) ) t.
Proof.
  introv Haop Hx Hm HPeval HPlinv0 HPlinv1.
  unfolds. 
  introv Hsat.
  destruct Hsat as (Hsat1 & Hsat2).
  sep split in Hsat1.
  lets Hs : HPeval Hsat1.
  simpl in H.
  subst aop.
  destruct Hs as (Havl & Heval).
  simpl in Havl.
  simpl in Heval.
  destruct Havl as (Ha & Ht & Ht1).
  destruct Heval as (He & Htt).
  destruct o as [[[[[ge le] M] ir] er] aux].
  simpl in Ha, Ht, He, Htt.
  simpl in Hsat1.
  simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
    unfold loststepabt. unfold not. intros. apply H. clear H.
    destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
    apply joinm2_env_eq in Hjm1 as ?.
    apply joinm2_mem_join in Hjm1 as ?.
    destruct H. simpl in H,H6. destruct H1 as [? [_ ?]]. subst G2 E2.
    unfold getmem, get_mem in H1. simpl in H1. 
    lets He2: evaladdr_val_eq Htt He.
    apply join_lib.join_comm in H0.
    lets HH : store_exist_join (Vint32 Int.zero) H4 H0 H1.
    apply join_lib.join_emp. auto.
    destruct HH as [? HH].
    do 2 eexists. unfold nilcont in *.  
    eapply cslsemaccdir_step with (v2:=Vint32 Int.zero); eauto.
    - erewrite evaltype_mono; eauto.
    - erewrite evalval_mono; eauto.
 + simpl substaskst in *. inverts Hfalse.
  introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
  invertstep tryfalse.
  unfolds in Hjm1. unfold joinmem in Hjm1.
  simp join.
  pose proof map_join_assoc'' H16 H14 as [? ?].
  apply join_lib.join_comm in H.
  lets He2: evaladdr_val_eq Htt He.
  lets Haeql : evalval_mono H He2. clear H.
  rewrite He2, H10 in Haeql.
  inverts Haeql.
  apply join_lib.join_comm in H0.
  destruct l.
  assert (i = Int.zero).
  { simpl in H10.
    destruct (get x6 x2) as [[? ?] | ].
    inverts H10. auto.
    destruct (get x5 x2) as [[? ?] | ].
    inverts H10. auto.
    inverts H10. }
  subst i.
  cbn [addrval_to_addr] in *.
  rewrite Int.unsigned_zero in H13.
  lets Hres: store_join_map_join_int8 H14 H16 H0 H4 H13.
  simp join.
  destruct H12; subst v2.
  - eexists. exists n. exists (Vint32 Int.zero). exists aop0.
    exists OO.
    exists (x5, x6, x15, x9, x10, x11).
    exists Ms.
    exists O.
    exists Os.
    splits; eauto.
    {
      econstructor; [ | constructor 1].
      constructor.
    }
    unfolds. exists (x5, x6, x13, x9, x10, x11).  
    splits; unfold joinmem; do 7 eexists; splits; eauto.
    unfold satp. intros.
    apply HPlinv0.
    simpl. exists x0. exists x12. exists x15 O. exists OSAbstMod.emp O.
    splits; auto.
    join auto.
    apply OSAbstMod.map_join_emp.
    unfold emposabst in H5. subst x4.
    apply map_join_emp' in H2. subst x3.
    eapply change_aop_rule; eauto.
    easy.
    constructors; trysimplsall; introv Hhf ;tryfalse.
    ++ intros. invertstep idtac.
    ++ intros. inverts Hhf. exists aop0. do 3 eexists. unfold lift. splits; eauto.
      * constructor.
      * unfold satp. intros. apply HPlinv0. simpl. do 6 eexists.
        splits; auto.
        4: apply H15.
        apply join_lib.join_comm in H9. apply H9.
        apply OSAbstMod.map_join_emp.
        unfold emposabst in H5. subst x4.
        apply map_join_emp' in H2. subst x3.
        eapply change_aop_rule; eauto.
        easy.  
      * left. simpl. do 6 eexists. splits; auto.
        3: splits; eauto.
        apply join_lib.join_emp. auto.
        apply join_lib.join_comm. apply H2. 
        unfold emposabst in H5. subst x4.
        apply map_join_emp' in H2. subst x3.
        do 6 eexists. splits; auto.
        4: apply H15.
        apply join_lib.join_comm in H9. apply H9.
        apply OSAbstMod.map_join_emp.
        eapply change_aop_rule; eauto.
        easy.
    ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
            exfalso. apply Hhf. cbv. eauto.
  - eexists. exists n. exists (Vint32 Int.one). exists aop1.
    exists OO.
    exists (x5, x6, x15, x9, x10, x11).
    exists Ms.
    exists O.
    exists Os.
    splits; eauto.
    {
      econstructor; [ | constructor 1].
      constructor.
    }
    unfolds. exists (x5, x6, x13, x9, x10, x11).  
    splits; unfold joinmem; do 7 eexists; splits; eauto.
    unfold satp. intros.
    apply HPlinv1.
    simpl. exists x0. exists x12. exists x15 O. exists OSAbstMod.emp O.
    splits; auto.
    join auto.
    apply OSAbstMod.map_join_emp.
    unfold emposabst in H5. subst x4.
    apply map_join_emp' in H2. subst x3.
    eapply change_aop_rule; eauto.
    easy.
    constructors; trysimplsall; introv Hhf ;tryfalse.
    ++ intros. invertstep idtac.
    ++ intros. inverts Hhf. exists aop1. do 3 eexists. unfold lift. splits; eauto.
      * constructor.
      * unfold satp. intros. apply HPlinv1. simpl. do 6 eexists.
        splits; auto.
        4: apply H15.
        apply join_lib.join_comm in H9. apply H9.
        apply OSAbstMod.map_join_emp.
        unfold emposabst in H5. subst x4.
        apply map_join_emp' in H2. subst x3.
        eapply change_aop_rule; eauto.
        easy.  
      * right. simpl. do 6 eexists. splits; auto.
        3: splits; eauto.
        apply join_lib.join_emp. auto.
        apply join_lib.join_comm. apply H2. 
        unfold emposabst in H5. subst x4.
        apply map_join_emp' in H2. subst x3.
        do 6 eexists. splits; auto.
        4: apply H15.
        apply join_lib.join_comm in H9. apply H9.
        apply OSAbstMod.map_join_emp.
        eapply change_aop_rule; eauto.
        easy.
    ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
            exfalso. apply Hhf. cbv. eauto.
Qed.

Lemma cslsemrel_rule_sound:
forall  Spec sd  I r ri P e i aop pa t,
  can_change_aop P ->
  (Z.of_nat i <= Int.max_unsigned)%Z ->
  P ==> Rv e @ Tint8 == Vint32 ((Int.repr (Z.of_nat i)))  ->
  P ==> CurLINV pa t ->      
  RuleSem Spec sd pa I r ri ( <|| cslsemrel i;; aop ||>  ** P)
  (sprim (scsl_semrel e)) ( <|| aop ||>  ** P) t.
Proof.
  introv Hnrange Haop HPeval HPlinv Hsat. 
  destruct Hsat as [Hsat1  Hsat2].
  sep split in Hsat1. simpl in H. subst aop0.
  rename Hsat1 into Hsatp.
  rename Hsat2 into Hsatlinv.
  lets Heval: HPeval Hsatp. clear HPeval.
  destruct Heval as [Heval1 Heval2].
  lets Hlinv: HPlinv Hsatp. clear HPlinv.
  destruct o as [[[[[G E] M] irr] ierr] aux].
  inverts Heval1. inverts Heval2.
  simpl getsmem in *.
  constructors; introv Hfalse; tryfalse.
  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt.
      unfolds. intros. apply H2.  clear H2.
   destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as H4.
     apply joinm2_mem_join in Hjm1 as H5.
   destruct H4. simpl in H2,H3. destruct H5 as [? [_ ?]]. subst G2 E2.
   do 2 eexists. unfold nilcont in *.  eapply cslsemrel_step; eauto.
   - simpl. erewrite evaltype_irrev_mem; eauto.
   - lets Hnew: evalval_mono' H4 H0. simpl. eauto. 
 + intros. unfold nilcont in *. inverts Hfalse. simpl get_smem in *. 
    clear H1. 
     eexists. exists i. exists aop. exists OO. exists O. exists Os. exists Ms.
     splits; auto.
     *  constructor. 
     * splits; auto. 
     constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros.  inverts Hhf. exists aop. do 3 eexists. unfold lift. splits; eauto. constructor.
              sep auto.
        ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
               exfalso. apply Hhf. cbv. eauto.
Qed.