
Require Import include_frm.
Require Import os_inv.
Require Import inv_prop.
 
Require Import base_tac. 
Require Import seplog_lemmas. 
Require Import seplog_tactics. 
Require Import sep_cancel_ext.
Require Import ucos_pauto.
Require Import ucos_common. 

Require Import ev_aux_code.
Require Import seplog_trm_tacs.

Open Scope code_scope.

Ltac join_to_sub := 
  match goal with
    H: Maps.join ?t1 ?t2 ?t3 |- sub ?t1 ?t => apply join_sub_l in H; auto
  | H: Maps.join ?t1 ?t2 ?t3 |- sub ?t2 ?t => apply join_sub_r in H; auto
  end; 
  repeat ( 
      match goal with
        H1: sub ?t1 ?t2 |- _ => 
          match goal with 
            H2: Maps.join t2 ?t3 ?t |- _ => apply join_sub_l in H2
          | H2: Maps.join ?t3 t2 ?t |- _ => apply join_sub_r in H2
          end
      end).

Lemma err_sllseg_split_first_val:
  forall s hd vl vll' pbls,
    s |= err_sllseg hd Vnull (vl::vll') pbls ->
    exists l errv pbls' vn, 
      hd = Vptr l /\
        get pbls l = Some errv /\
        joinsig l errv pbls' pbls /\ 
        V_errblk_err vl = Some (Vint32 errv) /\ 
        V_errblk_next vl = Some vn /\ 
        s |= node hd vl gjb_err_blk_t ** err_sllseg vn Vnull vll' pbls'.  
Proof.
  introv Hsat.
  unfold err_sllseg in Hsat.
  fold err_sllseg in Hsat.
  destruct s as [[[[[[[]]]]]]].
  destruct Hsat. simpljoin1.
  destruct H4. 
  destruct H. simpljoin1.
  destruct H7.
  destruct H. simpljoin1.
  destruct H10.
  destruct H. simpljoin1.
  destruct H13.
  destruct H. simpljoin1.
  destruct H9. simpljoin1.
  change_smo_hyps.
  simp_mem_abst.
  destruct H6.
  destruct H12.
  destruct H15.
  exists x1. exists x6.
  do 2 eexists.
  splits; eauto.
  simpl in H19. destruct H19. subst x19.
  assert (x22 = empenv). join auto. subst x22.
  assert (x20 = x15) by join auto. subst x20.
  assert (x23 = x18) by join auto. subst x18.
  simpl in H18. destruct H18. subst x14.
  assert (x17 = empenv) by join auto. subst x17. 
  assert (x23 = x13) by join auto. subst x23.
  assert (x15 = x10) by join auto. subst x15.
  simpl in H9. destruct H9. subst x9.
  assert (x12 = empenv) by join auto. subst x12.
  assert (x10 = x5) by join auto. subst x10.
  assert (x13 = x8) by join auto. subst x13.
  simpl in H17. destruct H17. subst x4.
  assert (x5 = x0) by join auto. subst x5.
  assert (x7 = empenv) by join auto. subst x7.
  assert (x8 = x3) by join auto. subst x8.
  remember (node hd vl gjb_err_blk_t) as P.
  remember (err_sllseg x16 Vnull vll' x11) as Q.
  simpl.
  exists x x0. exists m. exists x2 x3. exists o.
  splits; auto.
Qed.

Lemma err_sllseg_first_merge: 
  forall e e0 m1 m2 i i0 l o1 o2 a0 p0 errv0 vl vll vn0 vn pbls, 
    (e, e0, m1, i, i0, l, o1, a0) |= node (Vptr p0) vl gjb_err_blk_t ->
    (e, e0, m2, i, i0, l, o2, a0) |= err_sllseg vn0 vn vll pbls ->
    V_errblk_err vl = Some (Vint32 errv0) -> 
    V_errblk_next vl = Some vn0 ->
    disjoint m1 m2 ->
    disjoint o1 o2 -> 
    disjoint (sig p0 errv0) pbls -> 
    (e, e0, merge m1 m2, i, i0, l, merge o1 o2, a0)
      |= err_sllseg (Vptr p0) vn (vl :: vll) (merge (sig p0 errv0) pbls).
Proof.
  intros.
  unfold err_sllseg. fold err_sllseg.
  simpl_sat_goal.
  exists m1. do 2 eexists. exists o1. do 2 eexists.
  splits; eauto.
  join auto. join auto.
  exists p0. exists (emp:mem). exists m2. eexists.
  exists (emp:osabst). exists o2. eexists.
  splits; eauto.
  join auto. join auto.
  splits; auto. simpl. splits; auto. 
  unfolds. auto.
  exists errv0. exists (emp:mem). exists m2. eexists.
  exists (emp:osabst). exists o2. eexists.
  splits; eauto.
  join auto. join auto.
  split.
  2: { simpl. split; auto. unfolds. auto. }
  split; auto.
  eapply perm_map_lemmas_part3.osabst_get_merge_auto; eauto.
  apply get_a_sig_a.
  exists pbls. exists (emp:mem). exists m2. eexists.
  exists (emp:osabst). exists o2. eexists.
  splits; eauto.
  join auto.
  join auto.
  split.
  2: { simpl. split; auto. unfolds. auto. }
  unfold TcbJoin.
  apply join_merge_disj; auto.
  exists vn0. exists (emp:mem). exists m2. eexists.
  exists (emp:osabst). exists o2. eexists.
  splits; eauto.
  join auto. join auto.
  split; auto. simple. split; auto. unfolds. auto.
Qed.  

Lemma err_list_split: 
  forall pbls smadr errv s, 
    s |= AErrblkList pbls -> 
    get pbls smadr = Some errv ->
    s |= EX p, 
            GV GJB_err_list @ gjb_err_blk_t∗ |-> p ** 
            EX vll1 vll2 vl hd2 pbls1 pbls' pbls2,
              err_sllseg p (Vptr smadr) vll1 pbls1 **
                node (Vptr smadr) vl gjb_err_blk_t **
                err_sllseg hd2 Vnull vll2 pbls2 **
                [| V_errblk_next vl = Some hd2 |] **
                [| V_errblk_err vl = Some (Vint32 errv) |] **
                [| joinsig smadr errv pbls2 pbls' /\ join pbls1 pbls' pbls |]. 
Proof.
  introv Hsat Hget.
  unfold AErrblkList in Hsat.
  apply aexists_elim in Hsat.
  destruct Hsat.
  apply aexists_intro.
  exists x.
  sep cancel 1%nat 1%nat.
  apply aexists_elim in H.
  destruct H as (vll & Hsat).
  gen vll pbls x s. 
  inductions vll.
  - introv Hget Hsat.
    simpl in Hsat. simpljoin1.
    inversion Hget.
  - introv Hget Hsat.
    assert (HsatS := Hsat). 
    apply err_sllseg_split_first_val in HsatS.
    destruct HsatS as (p0 & errv0 & pbls0 & vn0 & H').
    destruct H' as (Hp0 & Hget0 & Hjo & Herr0 & Hnxt0 & Hsat0).
    assert (Hor: smadr = p0 \/ smadr <> p0) by tauto.
    destruct Hor.
    + (* eq *)
      subst.
      apply aexists_intro. exists (nil : list vallist).
      apply aexists_intro. exists vll.
      apply aexists_intro. exists a.
      apply aexists_intro. exists vn0.
      apply aexists_intro. exists (emp: EbMod.map).
      apply aexists_intro. eexists. 
      apply aexists_intro. exists pbls0.
      match goal with H: _ |- _ |= ?P ** ?Q => remember Q as X end.
      unfold err_sllseg.
      sep normal.
      apply astar_l_apure_intro; pure_auto.
      apply astar_l_apure_intro; pure_auto.
      subst X.
      assert (errv = errv0). 
      { unfold get in Hget. unfold get in Hget0. destruct EbMap. congruence. }
      subst.
      sep pauto.
      instantiate (1:=pbls). 
      split; auto. join auto.
    + (* neq *)
      destruct s as [[[[[[[]]]]]]].
      destruct Hsat0.
      simpljoin1.
      simp_mem_abst. change_smo_hyps.
      assert (Hget': get pbls0 smadr = Some errv).
      {
        unfold TcbJoin in Hjo.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
      }
      lets H00: IHvll Hget' H5.
      simpl_sat H00. simpljoin1.
      apply aexists_intro. exists (a::x).
      apply aexists_intro. exists x2.
      apply aexists_intro. exists x5.
      apply aexists_intro. exists x6.
      apply aexists_intro. exists (merge (sig p0 errv0) x7).
      apply aexists_intro. eexists.
      apply aexists_intro. exists x9.
      simpl_sat_goal.
      exists (merge x0 x10). eexists. exists m.
      exists (merge x3 x13). eexists. exists o.
      splits; eauto.
      instantiate (1:=x11). eapply join_join_join_merge; eauto.
      instantiate (1:=x14). eapply join_join_join_merge; eauto.
      assert (disjoint (sig p0 errv0) pbls0).
      { eapply join_disj; eauto. }
      assert (disjoint (sig p0 errv0) x7).
      { 
        apply disjoint_sym in H0.
        lets H00: perm_map_lemmas_part3.osabst_disjoint_join_disjoint_auto H0 H32; eauto.
        apply disjoint_sym. auto.
      }
      eapply err_sllseg_first_merge; eauto.
      assert (sub x10 x1) by join_to_sub.
      eapply disj_trans_sub; eauto.
      eapply join_disj; eauto.
      assert (sub x13 x4) by join_to_sub.
      eapply disj_trans_sub; eauto.
      eapply join_disj; eauto.
      exists x16. eexists. exists x11. exists x19. eexists. exists x14.
      splits; eauto.
      exists x17. eexists. exists x17. exists x20. eexists. exists x20.
      splits; eauto.
      join auto. join auto.
      do 6 eexists.
      splits; eauto.
      join auto. join auto.
      split; auto.
      simpl. split; auto. unfolds. auto.
      do 6 eexists.
      splits; eauto.
      join auto.
      join auto.
      split; auto.
      simpl. split; auto. unfolds. auto.
      split; eauto.
      2: { simpl. split; auto. unfolds. auto. }
      unfold TcbJoin in Hjo.
      generalize dependent Hjo. intro Hjo.
      remember (sig p0 errv0) as xx.
      clear - H32 Hjo.
      apply join_comm. rewrite disjoint_merge_sym.
      eapply joinmemLib.taskst_join_merge_auto1; eauto.
      apply join_comm. eauto.
      apply join_comm; auto.
      assert (sub x7 pbls0) by join_to_sub.
      eapply disj_trans_sub; eauto.
      eapply join_disj; eauto.
Qed.

Lemma err_list_split_frm: 
  forall pbls smadr errv s P, 
    s |= AErrblkList pbls ** P -> 
    get pbls smadr = Some errv ->
    s |= (EX p, 
            GV GJB_err_list @ gjb_err_blk_t∗ |-> p ** 
            EX vll1 vll2 vl hd2 pbls1 pbls' pbls2,
              err_sllseg p (Vptr smadr) vll1 pbls1 **
                node (Vptr smadr) vl gjb_err_blk_t **
                err_sllseg hd2 Vnull vll2 pbls2 **
                [| V_errblk_next vl = Some hd2 |] **
                [| V_errblk_err vl = Some (Vint32 errv) |] **
                [| joinsig smadr errv pbls2 pbls' /\ join pbls1 pbls' pbls |]) ** P.  
Proof. 
  introv Hsat Hget. 
  sep cancel 2%nat 2%nat.
  eapply err_list_split; eauto.
Qed.

Lemma err_sllseg_merge:
  forall vll1 s hd vsem pbls1 vl hd' vll2 pbls2 errv pbls' pbls P,
    s |= err_sllseg hd (Vptr vsem) vll1 pbls1 **
      node (Vptr vsem) vl gjb_err_blk_t **
      err_sllseg hd' Vnull vll2 pbls2 ** 
      [|V_errblk_err vl = Some (Vint32 errv)|] ** 
      [|V_errblk_next vl = Some hd'|] **
      [| joinsig vsem errv pbls2 pbls' |] **
      [| join pbls1 pbls' pbls |] ** 
      P -> 
    get pbls vsem = Some errv -> 
    s |= err_sllseg hd Vnull (vll1 ++ (vl :: vll2)) pbls ** P. 
Proof.
  inductions vll1.
  -
    intros.
    change ((nil ++ vl :: vll2)) with (vl::vll2).
    unfold err_sllseg at 1 in H.
    sep normal in H.
    apply sep_pure_split in H.
    destruct H.
    apply sep_pure_split in H1.
    destruct H1.
    unfold err_sllseg. fold err_sllseg.
    sep normal.
    apply aexists_intro. exists vsem.
    apply aexists_intro. exists errv.
    apply aexists_intro. exists pbls2.
    apply aexists_intro. exists hd'.
    sep pauto.
    assert (pbls' = pbls) by join auto.
    subst.
    auto.
  -
    introv Hsat Hget.
    change (((a :: vll1) ++ vl :: vll2)) with (a :: (vll1 ++ (vl::vll2))).
    unfold err_sllseg. fold err_sllseg.
    unfold err_sllseg at 1 in Hsat.
    fold err_sllseg in Hsat.
    sep normal in Hsat.
    sep normal.
    apply aexists_elim in Hsat. destruct Hsat as (vhd & Hsat).
    apply aexists_elim in Hsat. destruct Hsat as (errv1 & Hsat).
    apply aexists_elim in Hsat. destruct Hsat as (pbls1' & Hsat).
    apply aexists_elim in Hsat. destruct Hsat as (vna & Hsat).
    apply aexists_intro. exists vhd.
    apply aexists_intro. exists errv1.
    apply aexists_intro. exists (merge pbls1' pbls').
    apply aexists_intro. exists vna.
    sep cancel 1%nat 1%nat. 
    sep cancel 5%nat 5%nat.
    sep lifts (2::3::4::nil)%nat in Hsat.
    apply sep_pure_split in Hsat.
    destruct Hsat as (Hjo & Hsat).
    apply sep_pure_split in Hsat.
    destruct Hsat as (Ha & Hsat).
    apply sep_pure_split in Hsat.
    destruct Hsat as (Hhd & Hsat).
    sep lift 7%nat in Hsat.
    apply sep_pure_split in Hsat.
    destruct Hsat as (Hjo0 & Hsat).
    eapply astar_l_apure_intro
      with (P:=join pbls1' pbls' (merge pbls1' pbls')) in Hsat.
    2: {
      simpl in Hjo.
      assert (Hjo': join (sig vhd errv1) pbls1' pbls1) by auto.
      apply join_merge_disj. 
      apply join_comm in Hjo'.
      eapply join_join_disj_l; eauto.
    }
    sep lifts (2::3::4::5::6::7::nil)%nat in Hsat.
    apply IHvll1 in Hsat. 
    sep pauto.
    split; auto.
    clear IHvll1.
    eapply join_get_l; eauto.
    unfold TcbJoin in *.
    remember (sig vhd errv1) as xx.
    eapply join_join_merge23_join; eauto. 
    assert (Hjo': TcbJoin vsem errv pbls2 pbls') 
      by sep pauto.
    unfold TcbJoin in *. 
    assert (disjoint pbls1' pbls').
    { eapply join_join_disj_r; eauto. }
    rewrite perm_map_lemmas_part3.disjoint_merge_comm; eauto. 
    eapply perm_map_lemmas_part3.osabst_get_merge_auto; eauto.
    eapply join_sig_get; eauto. 
Qed.     
