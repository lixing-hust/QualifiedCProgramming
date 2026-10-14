Require Import sound_include.
Require Import Lia.

Lemma generateipc_rule_sound:
 forall  Spec sd  I r ri P e1 e2 n m aop pa t,
 (Z.of_nat n <= Int.max_unsigned)%Z ->
 can_change_aop P ->
 P ==> Rv e1 @ Tint8 == Vint32 ((Int.repr (Z.of_nat n))) //\\   
      Rv e2 @ Tint32 == m ->
 P ==> CurLINV pa t ->      
 RuleSem Spec sd pa I r ri
  ( <|| coreint n m;; aop ||>  ** P)
  (sprim (sgenerateipc e1 e2))
  ( <|| aop ||>  ** P) t.
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
     destruct Hlostep as (_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt.
      assert ((exists C' tst',
      loststep p
    (nilcont (sprim (sgenerateipc e1 e2)))
     o2 C' tst')).
   destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as H4.
     apply joinm2_mem_join in Hjm1 as H5.
   destruct H4. simpl in H3,H4. destruct H5 as [? [_ ?]]. subst G2 E2.
   do 2 eexists. unfold nilcont in *. destruct H0. destruct H2. eapply generateipc_step.
   - eauto.
   - simpl. erewrite evaltype_irrev_mem; eauto.
   -  simpl. erewrite evaltype_irrev_mem; eauto.
   - lets Hnew: evalval_mono' H5 H. simpl. eauto. 
   - lets Hnew: evalval_mono' H5 H1. simpl. eauto.
   - auto.
   - auto. 
   - unfold not. intros. apply H4. unfold nilcont. auto. 
 + intros. unfold nilcont in *. inverts Hfalse. simpl get_smem in *. 
     do 8 eexists. splits; eauto; try tauto. splits; eauto.
     constructor.
     * constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros.  inverts Hhf. exists aop. do 3 eexists. unfold lift. splits; eauto. constructor.
              sep auto.
        ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
               exfalso. apply Hhf. cbv. eauto.
 Qed.

Lemma getsem_rule_sound:
 forall  Spec sd  I r ri P e i aop pa t,
 can_change_aop P ->
 (Z.of_nat i <= Int.max_unsigned)%Z ->
 P ==> Rv e @ Tint8 == Vint32 ((Int.repr (Z.of_nat i)))  ->
 P ==> CurLINV pa t ->      
 RuleSem Spec sd pa I r ri
  ( <|| getsem i;; aop ||>  ** P)
  (sprim (sgetsem e))
  ( <|| aop ||>  ** P) t.
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
     destruct Hlostep as (_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt.
      unfolds. intros. apply H2.  clear H2.
   destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as H4.
     apply joinm2_mem_join in Hjm1 as H5.
   destruct H4. simpl in H2,H3. destruct H5 as [? [_ ?]]. subst G2 E2.
   do 2 eexists. unfold nilcont in *.  eapply getsem_step; eauto.
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
 
 Lemma postsem_rule_sound:
 forall  Spec sd  I r ri P e i aop pa t,
 can_change_aop P ->
 (Z.of_nat i <= Int.max_unsigned)%Z ->
 P ==> Rv e @ Tint8 == Vint32 ((Int.repr (Z.of_nat i)))  ->
 P ==> CurLINV pa t ->      
 RuleSem Spec sd pa I r ri
  ( <|| postsem i;; aop ||>  ** P)
  (sprim (spostsem e))
  ( <|| aop ||>  ** P) t.
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
     destruct Hlostep as (_&_&_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt.
      unfolds. intros. apply H2.  clear H2.

   destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as H4.
     apply joinm2_mem_join in Hjm1 as H5.
   destruct H4. simpl in H2,H3. destruct H5 as [? [_ ?]]. subst G2 E2.
   do 2 eexists. unfold nilcont in *.  eapply postsem_step; eauto.
   - simpl. erewrite evaltype_irrev_mem; eauto.
   - lets Hnew: evalval_mono' H4 H0. simpl. eauto. 
 + intros. unfold nilcont in *. inverts Hfalse. simpl get_smem in *. 
    clear H1. 
     eexists. exists i. exists aop. exists OO. exists O. exists Os. exists Ms.
     splits; auto.
     *  constructor. 
     * splits; auto. constructors; trysimplsall; introv Hhf ;tryfalse.
        ++ intros. invertstep idtac.
        ++ intros.  inverts Hhf. exists aop. do 3 eexists. unfold lift. splits; eauto. constructor.
              sep auto.
        ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
               exfalso. apply Hhf. cbv. eauto.
 Qed.        
 
Lemma clearipc_rule_sound:
 forall  Spec sd  I r ri p P e1 e2 n m aop pa t,
 can_change_aop p ->
 (Z.of_nat n <= Int.max_unsigned)%Z ->
 P ==> Rv e1 @ Tint8 == Vint32 ((Int.repr (Z.of_nat n))) //\\   
      Rv e2 @ Tint32 == m ->
   P ==> PV ipcgr_addr @ Tint32 |-> m ** Aabsdata ipcgrid (osipcgr m) ** p ->    
   PV ipcgr_addr @ Tint32 |-> (Vint32 Int.zero) ** Aabsdata ipcgrid (osipcgr (Vint32 Int.zero)) ** p  ==> CurLINV pa t ->
 RuleSem Spec sd pa I r ri
  ( <|| clearipc n m;; aop ||>  ** P)
  (sprim (sclearipc e1 e2))
  ( <|| aop ||>  ** p ** PV ipcgr_addr @ Tint32 |-> (Vint32 Int.zero) ** Aabsdata ipcgrid (osipcgr (Vint32 Int.zero))) t.
Proof.
  introv Haop Hnrange HPeval HPaddr HPlinv.
  unfolds. 
  introv Hsat.
  destruct Hsat as [Hsat1  Hsat2].
   destruct o as [[[[[G E] M] irr] ierr] aux].
  sep split in Hsat1. 
  simpl in H. subst aop0.
  apply HPaddr in Hsat1 as Haddr.
  clear HPaddr.
  simpl in Haddr.
  simp join.
  unfolds in H11. subst x2. 
  apply join_lib.join_emp_eq in H2. subst x3.
  apply join_lib.join_emp_eq in H5. subst x6.
  apply HPeval in Hsat1 as Heval. clear Hsat1.
  simpl in Heval. simp join.
  unfold nilcont.
  constructors; introv Hfalse; tryfalse.
  + introv Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
     destruct Hlostep as (_&_&_&_&_&Hf&_).
     exfalso. apply Hf. unfolds. unfold nilcont.
      do 3 eexists; eauto.
  + introv  Hinv Hjm1 Hjm2 Hjm3 Hnabt.
      unfold loststepabt. unfold not. intros. apply H8. clear H8.
     destruct o2 as [[[[[G2 E2] M2] irr2] ierr2] aux2].
     apply joinm2_env_eq in Hjm1 as ?.
     apply joinm2_mem_join in Hjm1 as ?.
   destruct H8. simpl in H8,H11. destruct H10 as [? [_ ?]]. subst G2 E2.
   unfold getmem in H10. simpl in H10.
  lets HH : store_exist_join (Vint32 Int.zero) H3 H0 H10.
  apply join_lib.join_emp. auto.
   destruct HH.   
   do 2 eexists. unfold nilcont in *.  eapply clearipc_step; auto.
   - erewrite evaltype_irrev_mem; eauto.
   - erewrite evaltype_irrev_mem; eauto.
   - lets Hnew: evalval_mono' H10 H.  eauto. 
   - lets Hnew: evalval_mono H10 H1. rewrite Hnew.  eauto.
   - congruence.
   - auto.
   - eauto. 
 + simpl substaskst in *. 
  introv Hinv Hjm1 Hjm2 Hstep Hnabt. 
  invertstep tryfalse.
  unfolds in Hjm1. unfold joinmem in Hjm1.
  assert (addrval_to_addr ipcgr_addr = (ipcgr_block, 0%Z)) as Hipcgr_addr.
  { unfold ipcgr_addr. simpl. rewrite Int.unsigned_zero. easy. }
  rewrite Hipcgr_addr in H17. rewrite Int.unsigned_zero in H3.
  simp join.
  lets Hres: store_join_map_join  H19 H21 H3 H17; eauto.
  simp join.
  eexists. exists n. exists m. exists aop.
  exists OO.
  exists (set OO ipcgrid (osipcgr (Vint32 Int.zero))).
  exists (x2, x3, x11, x6, x7, x8).
  exists Ms.
  exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
  exists Os.
  splits; eauto.
  constructor.
  econstructor; eauto.
  eapply join_lib.join_sig_get; eauto.
  apply join_lib.join_set_l; auto. 
  apply OSAbstMod.get_indom.  exists (osipcgr m). 
  eapply OSAbstMod.join_sig_get; eauto.
 unfolds. exists (x2,x3, x10, x6 ,x7, x8).
 splits; unfold joinmem; do 7 eexists; splits; eauto.
 apply join_lib.join_set_l; auto. 
 apply OSAbstMod.get_indom.  exists (osipcgr m). 
 eapply OSAbstMod.join_sig_get; eauto.
 unfold satp. intros.
 apply HPlinv.
 simpl. exists x1. exists x0. exists x11. exists OSAbstMod.emp.
 exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
 exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
 splits; auto.
 apply join_lib.join_emp.
 auto. split; auto. unfold emposabst. easy.
 exists empmem. exists x0. exists x0.
 exists (sig ipcgrid (osipcgr (Vint32 Int.zero))).
 exists x9.
 exists ( set O ipcgrid (osipcgr (Vint32 Int.zero))).
 splits; auto.
 apply join_lib.join_emp. auto.
 eapply join_lib.join_sig_set; eauto.
 sep auto.
  constructors; trysimplsall; introv Hhf ;tryfalse.
    ++ intros. invertstep idtac.
    ++ intros. subst.  inverts Hhf. exists aop. 
           exists OO0. do 2 eexists; splits; eauto.
           constructor.
           unfold satp.
           intros.
           apply HPlinv.
     simpl. exists x1. exists x0. exists x11. exists OSAbstMod.emp. 
     exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
     exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
     splits; auto.
     apply join_lib.join_emp.
    auto. split; auto. unfold emposabst. easy.
    exists empmem. exists x0. exists x0.
    exists (sig ipcgrid (osipcgr (Vint32 Int.zero))).
    exists x9.
    exists ( set O ipcgrid (osipcgr (Vint32 Int.zero))).
    splits; auto.
    apply join_lib.join_emp. auto.
    eapply join_lib.join_sig_set; eauto.
    sep auto. unfold lift.
    sep lift 2%nat.
    sep lift 4%nat.
    sep lift 4%nat.
    simpl.
    exists x1. exists x0. exists x11. exists OSAbstMod.emp. 
     exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
     exists (set O ipcgrid (osipcgr (Vint32 Int.zero))).
     splits; auto.
     apply join_lib.join_emp.
    auto. split; auto. unfold emposabst. easy.
    exists empmem. exists x0. exists x0.
    exists (sig ipcgrid (osipcgr (Vint32 Int.zero))).
    exists x9.
    exists ( set O ipcgrid (osipcgr (Vint32 Int.zero))).
    splits; auto.
    apply join_lib.join_emp. auto.
    eapply join_lib.join_sig_set; eauto.
   exists x0. exists empmem. exists x0. 
   exists x9. exists OSAbstMod.emp. exists x9.
   splits; auto.
   join auto.
   join auto.
   apply join_lib.join_comm.
   apply join_lib.join_emp. auto.
   sep auto.
   unfolds. auto.
    ++ intros. destruct Hhf as [ _ Hhf ]. destruct Hhf as (_&Hhf&_). unfolds in Hhf.
               exfalso. apply Hhf. cbv. eauto.
Qed.