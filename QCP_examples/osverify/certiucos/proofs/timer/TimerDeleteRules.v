Require Import ucos_include.
Require Import Lia.

Require Import join_lib_aux.
Require Import aux_pureLib.
Require Import tmr_rules.
Require Import tmr_sep_rules.
Require Import tmr_assign_rules.
Require Import tmr_tactics.

Open Scope code_scope.

Open Scope int_scope.

Lemma join_eq_trans_permfalse :
  forall (A B T : Type) (MC : PermMap A B T) m1 m1' m2 m3 m3' m4,
    usePerm = false ->
    join m1 m2 m3 ->
    join m1' m2 m3' ->
    join m3' m4 m3 ->
    join m1' m4 m1.
Proof.
  hy.
Qed.


Lemma TMRList_P_user_delete_tmr : 
forall n m utmrl tmrusedl tmrls tmri new_tmri tmr tmrls',
 (n < length utmrl)%nat ->
 length utmrl = length tmrusedl ->
 nth_error utmrl n = Some tmri ->
 V_OSTGCR new_tmri = Some (V$ 0) ->
 join (sig (Z.of_nat (m + n + 8)) tmr) tmrls' tmrls ->
 TMRList_P_user m utmrl tmrusedl tmrls ->
 TMRList_P_user m
  (update_nth_vallist n utmrl new_tmri)
  (update_nth_val n tmrusedl (V$ 0)) tmrls'.
Proof.
  induction n;intros.
  - destruct utmrl;tryfalse.
    destruct tmrusedl;tryfalse.
    simpl in *.
    destruct v0;tryfalse.
    assert ((m + 0 + 8 ) = m + 8 )%nat by lia.
    rewrite H5 in *. clear H5.
    right.
    do 2 (split;auto).
    destruct H4.
    + my_destruct H4.
      assert (x = tmr).
      { assert (get tmrls (Z.of_nat (m + 8)) = Some x).
        { eapply join_sig_get;eauto. }
        assert (get tmrls (Z.of_nat (m + 8)) = Some tmr).
        { eapply join_sig_get;eauto. }
        eapply map_get_unique;eauto. }
      subst x.
      assert (x0 = tmrls').
      { assert (x0 = minus tmrls (sig (Z.of_nat (m + 8)) tmr)).
        { eapply perm_map_lemmas_part1.join_eq_minus.
          apply join_comm;auto. }
        assert (tmrls' = minus tmrls (sig (Z.of_nat (m + 8)) tmr)).
        { eapply perm_map_lemmas_part1.join_eq_minus.
          apply join_comm;auto. }
        rewrite H9,H10. auto. }
      subst x0.
      split;auto.
      eapply join_sig_nindom;eauto.
    + my_destruct H4.
      false.
      apply H6.
      eexists.
      eapply join_sig_get;eauto.
  - destruct utmrl;tryfalse.
    destruct tmrusedl;tryfalse.
    simpl in *.
    destruct v0;tryfalse.
    apply lt_S_n in H.
    apply eq_add_S in H0.
    assert ((m + S n + 8) = (S m + n + 8))%nat by lia.
    rewrite H5 in H3.
    clear H5.
    destruct H4.
    + my_destruct H4.
      left.
      splits;auto.
      assert (get tmrls' (Z.of_nat (m + 8)) = Some x).
      { eapply join_sig_get_neq;eauto.
        eapply join_sig_get;eauto.
        lia. }
      pose proof map_join_get_sig H9 as [? ?].
      do 2 eexists.
      splits;eauto.
      assert (join (sig (Z.of_nat (S m + n + 8)) tmr) x1 x0).
      {  apply join_comm.
         eapply join_eq_trans_permfalse.
         auto.
         apply join_comm;eauto.
         apply join_comm;eauto.
         apply join_comm;eauto. }
      eapply IHn;eauto.
    + my_destruct H4.
      right.
      splits;auto.
      unfold not;intros.
      apply H6.
      destruct H8.
      eexists. eapply join_get_r;eauto.
      eapply IHn;eauto.
Qed.



Lemma RLH_TMRList_P_user_delete_tmr :
forall utmrl tmrusedl tmrls tmrid tmri new_tmri tmr tmrls',
Int.ltu ($ 7) tmrid = true ->
Int.ltu tmrid ($ 16) = true->
length utmrl = 8%nat ->
length tmrusedl = 8%nat -> 
nth_error utmrl (Z.to_nat (Int.unsigned tmrid) - 8) = Some tmri ->
V_OSTGCR new_tmri = Some (V$ 0) ->
join (sig (Int.unsigned tmrid) tmr) tmrls' tmrls ->
RLH_TMRList_P_user utmrl tmrusedl tmrls ->
RLH_TMRList_P_user
  (update_nth_vallist (Z.to_nat (Int.unsigned tmrid) - 8) utmrl new_tmri)
  (update_nth_val (Z.to_nat (Int.unsigned tmrid - 8)) tmrusedl (V$ 0)) tmrls'.
Proof.
  intros.
  assert ((Z.to_nat (Int.unsigned tmrid - 8)) = (Z.to_nat (Int.unsigned tmrid) - 8))%nat by (simpl_intltbool;lia).
  rewrite H7. clear H7.
  assert ((Int.unsigned tmrid) = Z.of_nat ((Z.to_nat (Int.unsigned tmrid) - 8) + 8)) by (simpl_intltbool;lia).
  rewrite H7 in H5. clear H7. 
  unfold RLH_TMRList_P_user in *.
  eapply TMRList_P_user_delete_tmr;eauto.
  simpl_intltbool; lia.
  lia.
Qed.