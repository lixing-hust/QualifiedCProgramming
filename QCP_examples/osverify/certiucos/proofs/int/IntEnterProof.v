Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import ios_int.
Import DeprecatedTactic.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.

Lemma OSIntEnterInt_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSIntEnter
                  vl logicl OSIntEnterIntPre ct->
      Some r =
      BuildRetI os_internal OSIntEnter vl logicl OSIntEnterIntPost ct->
      exists t d1 d2 s,
      os_internal OSIntEnter = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}.
Proof.
  init spec.
  pure intro.
  unfolds in H2. destruct H2.
  subst v'3.

  eapply backward_rule1.
  intros.
  sep lift 20%nat in H0.
  apply disj_split in H0.
  exact H0.
  apply disj_rule.

  pure intro.
  unfold AGVars.
  pure intro.
  rename H0 into Hx. rename H2 into Hy.
  hoare forward.
  pure intro.
  clear H0 H2 H3.
  hoare forward.
  destruct (Int.ltu v'37 (Int.repr 255)); auto.
  hoare forward.
  apply ret_rule'.

  intros.
  destruct H0.
  sep normal in H0. 
  sep destruct H0.
  sep split in H0.
  clear H2.
  destruct H0.
  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.
  sep normal. 
  sep eexists.
  sep lift  36%nat.
  apply disj_split.
  left.
  sep auto; eauto.
  unfolds; auto.
  auto. auto.

  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.

  sep normal. 
  sep eexists.
  sep lift  36%nat.
  apply disj_split.
  left.
  sep auto; eauto.
  unfolds; auto.
  sep split in H0.
  rewrite Int.eq_true in H2.
  destruct H2; tryfalse.
  unfold AGVars.
  pure intro.
  rename H0 into Hx. rename H2 into Hy.
  hoare forward.
  pure intro.
  clear H0 H2 H3 H4.
  hoare forward.
  destruct (Int.ltu v'38 (Int.repr 255)); auto.
  pure intro.
  clear H0 H2 H3.
  hoare forward.
  apply ret_rule'.

  intros.
  destruct H0.
  sep normal in H0. 
  sep destruct H0.
  sep split in H0.
  clear H2.
  destruct H0.
  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.
  sep normal. 
  sep eexists.
  sep lift  36%nat.
  apply disj_split.
  right.
  sep auto; eauto.
  unfolds; auto.

  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.

  sep normal. 
  sep eexists.
  sep lift  36%nat.
  apply disj_split.
  right.
  sep auto; eauto.
  unfolds; auto.
  sep split in H0.
  rewrite Int.eq_true in H2.
  destruct H2; tryfalse.

  pure intro.
  unfold AGVars.
  pure intro.
  rename H0 into Hx. rename H2 into Hy.
  hoare forward.
  pure intro.
  clear H0 H2 H3.
  hoare forward.
  destruct (Int.ltu v'38 (Int.repr 255)); auto.
  pure intro.
  clear H0 H2 H3.
  hoare forward.
  apply ret_rule'.

  intros.
  destruct H0.
  sep normal in H0. 
  sep destruct H0.
  sep split in H0.
  clear H2.
  destruct H0.
  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.
  sep lift 34%nat in H2.
  apply disj_split in H2. 
  destruct H2.
  sep normal. 
  sep eexists.
  sep lift 36%nat.
  apply disj_split.
  left.
  sep auto; eauto.
  unfolds; auto.


  sep normal. 
  sep eexists.
  sep lift 36%nat.
  apply disj_split.
  right.
  sep auto; eauto.
  unfolds; auto.


  sep normal in H0.
  sep lift 39%nat in H0.
  apply sep_pure_split in H0.
  destruct H0.
  clear H0.

  sep lift 32%nat in H2.
  apply disj_split in H2. 
  destruct H2.
  sep normal. 
  sep eexists.
  sep lift 36%nat.
  apply disj_split.
  left.
  sep auto; eauto.
  unfolds; auto.


  sep normal. 
  sep eexists.
  sep lift 36%nat.
  apply disj_split.
  right.
  sep auto; eauto.
  unfolds; auto.
  sep split in H0.
  rewrite Int.eq_true in H2.
  destruct H2; tryfalse.
Qed.