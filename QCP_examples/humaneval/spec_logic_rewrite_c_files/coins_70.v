Load "../spec/70".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_70_pre_z (lst : list Z) : Prop :=
  problem_70_pre lst.

Definition problem_70_spec_z (lst output : list Z) : Prop :=
  problem_70_spec lst output.

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition strange_output_safe_70 (lst : list Z) : Prop :=
  Forall (fun x => INT_MIN <= x <= INT_MAX) lst.

Definition pair_at_70 (l : list Z) (i : nat) : list Z :=
  [nth i l 0; nth (length l - S i) l 0].

Definition strange_pairs_prefix_nat_70 (l : list Z) (n : nat) : list Z :=
  concat (map (pair_at_70 l) (seq 0 n)).

Definition strange_pairs_prefix_70 (l : list Z) (n : Z) : list Z :=
  strange_pairs_prefix_nat_70 l (Z.to_nat n).

Definition strange_output_70 (l : list Z) : list Z :=
  let n := length l in
  let half := Nat.div2 n in
  let prefix := strange_pairs_prefix_nat_70 l half in
  if Nat.even n then prefix else prefix ++ [nth half l 0].

Definition strange_output_prefix_70 (l : list Z) (n : Z) : list Z :=
  firstn (Z.to_nat n) (strange_output_70 l).

Lemma seq_snoc_70 : forall start len,
  seq start (S len) = seq start len ++ [(start + len)%nat].
Proof.
  intros start len; revert start.
  induction len; intros start; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - change (S start :: seq (S (S start)) len) with
      (seq (S start) (S len)).
    rewrite IHlen.
    replace (start + S len)%nat with (S start + len)%nat by lia.
    reflexivity.
Qed.

Lemma strange_pairs_prefix_nat_snoc_70 : forall l n,
  strange_pairs_prefix_nat_70 l (S n) =
  strange_pairs_prefix_nat_70 l n ++ pair_at_70 l n.
Proof.
  intros l n.
  unfold strange_pairs_prefix_nat_70.
  rewrite seq_snoc_70.
  rewrite map_app, concat_app.
  cbn.
  reflexivity.
Qed.

Lemma length_strange_pairs_prefix_nat_70 : forall l n,
  length (strange_pairs_prefix_nat_70 l n) = (2 * n)%nat.
Proof.
  intros l n.
  induction n as [| n IH].
  - reflexivity.
  - rewrite strange_pairs_prefix_nat_snoc_70, app_length, IH.
    unfold pair_at_70.
    cbn [length].
    lia.
Qed.

Lemma firstn_pairs_prefix_nat_70 : forall l p q,
  (p <= q)%nat ->
  firstn (2 * p) (strange_pairs_prefix_nat_70 l q) =
  strange_pairs_prefix_nat_70 l p.
Proof.
  intros l p q Hle.
  revert p Hle.
  induction q as [| q IH]; intros p Hle.
  - assert (p = 0%nat) by lia.
    subst; reflexivity.
  - destruct (Nat.eq_dec p (S q)) as [Heq | Hneq].
    + subst p.
      rewrite firstn_all2.
      * reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + assert (Hleq : (p <= q)%nat) by lia.
      rewrite strange_pairs_prefix_nat_snoc_70.
      rewrite firstn_app.
      rewrite length_strange_pairs_prefix_nat_70.
      replace (2 * p - 2 * q)%nat with 0%nat by lia.
      rewrite app_nil_r.
      apply IH; exact Hleq.
Qed.

Lemma firstn_pairs_prefix_nat_odd_70 : forall l p q,
  (p < q)%nat ->
  firstn (2 * p + 1) (strange_pairs_prefix_nat_70 l q) =
  strange_pairs_prefix_nat_70 l p ++ [nth p l 0].
Proof.
  intros l p q Hlt.
  revert p Hlt.
  induction q as [| q IH]; intros p Hlt.
  - lia.
  - rewrite strange_pairs_prefix_nat_snoc_70.
    destruct (Nat.eq_dec p q) as [Heq | Hneq].
    + subst p.
      rewrite firstn_app.
      rewrite length_strange_pairs_prefix_nat_70.
      replace (2 * q + 1 - 2 * q)%nat with 1%nat by lia.
      rewrite firstn_all2.
      * unfold pair_at_70. reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + rewrite firstn_app.
      rewrite length_strange_pairs_prefix_nat_70.
      replace (2 * p + 1 - 2 * q)%nat with 0%nat by lia.
      rewrite app_nil_r.
      apply IH; lia.
Qed.

Lemma nth_error_pairs_prefix_even_70 : forall l p q,
  (p < q)%nat ->
  nth_error (strange_pairs_prefix_nat_70 l q) (2 * p) =
  Some (nth p l 0).
Proof.
  intros l p q Hlt.
  revert p Hlt.
  induction q as [| q IH]; intros p Hlt.
  - lia.
  - rewrite strange_pairs_prefix_nat_snoc_70.
    destruct (Nat.eq_dec p q) as [Heq | Hneq].
    + subst p.
      rewrite nth_error_app2.
      * rewrite length_strange_pairs_prefix_nat_70.
        replace (2 * q - 2 * q)%nat with 0%nat by lia.
        reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + rewrite nth_error_app1.
      * apply IH; lia.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
Qed.

Lemma nth_error_pairs_prefix_odd_70 : forall l p q,
  (p < q)%nat ->
  nth_error (strange_pairs_prefix_nat_70 l q) (2 * p + 1) =
  Some (nth (length l - S p) l 0).
Proof.
  intros l p q Hlt.
  revert p Hlt.
  induction q as [| q IH]; intros p Hlt.
  - lia.
  - rewrite strange_pairs_prefix_nat_snoc_70.
    destruct (Nat.eq_dec p q) as [Heq | Hneq].
    + subst p.
      rewrite nth_error_app2.
      * rewrite length_strange_pairs_prefix_nat_70.
        replace (2 * q + 1 - 2 * q)%nat with 1%nat by lia.
        reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + rewrite nth_error_app1.
      * apply IH; lia.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
Qed.

Lemma Zlength_strange_pairs_prefix_70 : forall l n,
  0 <= n ->
  n <= Z.of_nat (Nat.div2 (length l)) ->
  Zlength (strange_pairs_prefix_70 l n) = 2 * n.
Proof.
  intros l n Hn _.
  unfold strange_pairs_prefix_70.
  rewrite Zlength_correct.
  rewrite length_strange_pairs_prefix_nat_70.
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma Zlength_strange_pairs_prefix_any_70 : forall l n,
  0 <= n ->
  Zlength (strange_pairs_prefix_70 l n) = 2 * n.
Proof.
  intros l n Hn.
  unfold strange_pairs_prefix_70.
  rewrite Zlength_correct.
  rewrite length_strange_pairs_prefix_nat_70.
  rewrite Nat2Z.inj_mul.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma sublist_snoc_Znth_70 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  reflexivity.
Qed.

Lemma sublist_full_eq_70 : forall (l l' : list Z) n,
  n = Zlength l ->
  n = Zlength l' ->
  sublist 0 n l = l' ->
  l = l'.
Proof.
  intros l l' n Hlen _ Hsub.
  rewrite (sublist_self l n Hlen) in Hsub.
  exact Hsub.
Qed.

Lemma strange_pairs_prefix_zero_70 : forall l,
  strange_pairs_prefix_70 l 0 = nil.
Proof.
  reflexivity.
Qed.

Lemma strange_pairs_prefix_step_70 : forall l n left right,
  n = Zlength l ->
  0 <= left ->
  left < right ->
  right = n - 1 - left ->
  strange_pairs_prefix_70 l (left + 1) =
    strange_pairs_prefix_70 l left ++ [Znth left l 0] ++ [Znth right l 0].
Proof.
  intros l n left right Hn Hleft Hlt Hright.
  unfold strange_pairs_prefix_70.
  replace (Z.to_nat (left + 1)) with (S (Z.to_nat left)).
  2:{ replace (left + 1) with (Z.succ left) by lia.
      symmetry; apply Z2Nat.inj_succ; lia. }
  rewrite strange_pairs_prefix_nat_snoc_70.
  unfold pair_at_70, Znth.
  replace (length l - S (Z.to_nat left))%nat with (Z.to_nat right).
  2:{
    assert (Hleft_len : (S (Z.to_nat left) <= length l)%nat).
    { apply Nat2Z.inj_le.
      rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
      rewrite <- Zlength_correct, <- Hn.
      lia. }
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_sub by exact Hleft_len.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    rewrite Z2Nat.id.
    - rewrite <- Zlength_correct.
      rewrite <- Hn.
      lia.
    - lia.
  }
  reflexivity.
Qed.

Lemma strange_pairs_prefix_step_len_70 : forall l n left right k,
  n = Zlength l ->
  0 <= left ->
  left < right ->
  right = n - 1 - left ->
  k = 2 * left + 1 ->
  k + 1 = Zlength (strange_pairs_prefix_70 l (left + 1)).
Proof.
  intros l n left right k Hn Hleft Hlt Hright Hk.
  rewrite Zlength_strange_pairs_prefix_any_70 by lia.
  rewrite Hk.
  lia.
Qed.

Lemma length_eq_even_nat_70 : forall (l : list Z) m,
  0 <= m ->
  Zlength l = 2 * m ->
  length l = (2 * Z.to_nat m)%nat.
Proof.
  intros l m Hm Hlen.
  apply Nat2Z.inj.
  rewrite Zlength_correct in Hlen.
  rewrite Hlen.
  rewrite Nat2Z.inj_mul, Z2Nat.id by lia.
  lia.
Qed.

Lemma length_eq_odd_nat_70 : forall (l : list Z) m,
  0 <= m ->
  Zlength l = 2 * m + 1 ->
  length l = (2 * Z.to_nat m + 1)%nat.
Proof.
  intros l m Hm Hlen.
  apply Nat2Z.inj.
  rewrite Zlength_correct in Hlen.
  rewrite Hlen.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id by lia.
  lia.
Qed.

Lemma strange_output_even_70 : forall (l : list Z) m,
  0 <= m ->
  Zlength l = 2 * m ->
  strange_output_70 l = strange_pairs_prefix_70 l m.
Proof.
  intros l m Hm Hlen.
  unfold strange_output_70, strange_pairs_prefix_70.
  rewrite (length_eq_even_nat_70 l m Hm Hlen).
  rewrite Nat.div2_double, Nat.even_even.
  reflexivity.
Qed.

Lemma strange_output_odd_70 : forall (l : list Z) m,
  0 <= m ->
  Zlength l = 2 * m + 1 ->
  strange_output_70 l = strange_pairs_prefix_70 l m ++ [Znth m l 0].
Proof.
  intros l m Hm Hlen.
  unfold strange_output_70, strange_pairs_prefix_70, Znth.
  rewrite (length_eq_odd_nat_70 l m Hm Hlen).
  rewrite Nat.div2_odd', Nat.even_odd.
  reflexivity.
Qed.

Lemma strange_output_no_middle_70 : forall l n left right k,
  n = Zlength l ->
  right = n - 1 - left ->
  left >= right ->
  left <> right ->
  k = 2 * left ->
  k <= n ->
  k = Zlength (strange_pairs_prefix_70 l left) ->
  k = n /\
  strange_output_prefix_70 l n = strange_output_70 l /\
  strange_pairs_prefix_70 l left = strange_output_70 l.
Proof.
  intros l n left right k Hn Hright Hge Hneq Hk Hkle Hlen.
  assert (Hgt : left > right) by lia.
  assert (Hkn : k = n) by lia.
  assert (Hleft_nonneg : 0 <= left).
  { pose proof (Zlength_nonneg (strange_pairs_prefix_70 l left)).
    lia. }
  assert (Hlen_even : Zlength l = 2 * left) by lia.
  assert (Hout : strange_output_70 l = strange_pairs_prefix_70 l left).
  { apply strange_output_even_70; lia. }
  split; [exact Hkn|].
  split.
  - unfold strange_output_prefix_70.
    rewrite Hout.
    rewrite firstn_all2.
    + reflexivity.
    + apply Nat2Z.inj_le.
      rewrite <- Zlength_correct.
      rewrite Z2Nat.id by (rewrite Hn; apply Zlength_nonneg).
      rewrite <- Hlen.
      lia.
  - symmetry; exact Hout.
Qed.

Lemma strange_output_middle_70 : forall l n left right k,
  n = Zlength l ->
  right = n - 1 - left ->
  left >= right ->
  left = right ->
  k = 2 * left ->
  k = Zlength (strange_pairs_prefix_70 l left) ->
  k + 1 = n /\
  strange_output_prefix_70 l n = strange_output_70 l /\
  strange_pairs_prefix_70 l left ++ [Znth left l 0] = strange_output_70 l.
Proof.
  intros l n left right k Hn Hright Hge Heq Hk Hlen.
  assert (Hkn : k + 1 = n) by lia.
  assert (Hleft_nonneg : 0 <= left).
  { pose proof (Zlength_nonneg (strange_pairs_prefix_70 l left)).
    lia. }
  assert (Hlen_odd : Zlength l = 2 * left + 1) by lia.
  assert (Hout : strange_output_70 l =
                 strange_pairs_prefix_70 l left ++ [Znth left l 0]).
  { apply strange_output_odd_70; lia. }
  split; [exact Hkn|].
  split.
  - unfold strange_output_prefix_70.
    rewrite Hout.
    rewrite firstn_all2.
    + reflexivity.
    + apply Nat2Z.inj_le.
      rewrite <- Zlength_correct.
      rewrite Z2Nat.id by (rewrite Hn; apply Zlength_nonneg).
      rewrite Zlength_app.
      change (Zlength [Znth left l 0]) with 1.
      rewrite <- Hlen.
      lia.
  - symmetry; exact Hout.
Qed.

Lemma Zlength_strange_output_70 : forall l,
  Zlength (strange_output_70 l) = Zlength l.
Proof.
  intros l.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    rewrite Zlength_correct.
    rewrite length_strange_pairs_prefix_nat_70.
    rewrite Hm, Nat.div2_double.
    rewrite Zlength_correct, Hm.
    lia.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    rewrite Zlength_app.
    change (Zlength [nth (Nat.div2 (length l)) l 0]) with 1.
    rewrite Zlength_correct.
    rewrite length_strange_pairs_prefix_nat_70.
    rewrite Hm, Nat.div2_odd'.
    rewrite Zlength_correct, Hm.
    lia.
Qed.

Lemma strange_output_prefix_full_70 : forall l,
  strange_output_prefix_70 l (Zlength l) = strange_output_70 l.
Proof.
  intros l.
  unfold strange_output_prefix_70.
  rewrite firstn_all2.
  - reflexivity.
  - apply Nat2Z.inj_le.
    rewrite <- Zlength_correct.
    rewrite Zlength_strange_output_70.
    rewrite Z2Nat.id by apply Zlength_nonneg.
    lia.
Qed.

Lemma length_strange_output_nat_70 : forall l,
  length (strange_output_70 l) = length l.
Proof.
  intros l.
  apply Nat2Z.inj.
  repeat rewrite <- Zlength_correct.
  apply Zlength_strange_output_70.
Qed.

Lemma firstn_strange_output_even_nat_70 : forall l p,
  (2 * p <= length l)%nat ->
  firstn (2 * p) (strange_output_70 l) =
  strange_pairs_prefix_nat_70 l p.
Proof.
  intros l p Hle.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    rewrite Hm, Nat.div2_double in *.
    apply firstn_pairs_prefix_nat_70; lia.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    rewrite Hm, Nat.div2_odd' in *.
    rewrite firstn_app.
    rewrite length_strange_pairs_prefix_nat_70.
    replace (2 * p - 2 * m)%nat with 0%nat by lia.
    rewrite app_nil_r.
    apply firstn_pairs_prefix_nat_70; lia.
Qed.

Lemma firstn_strange_output_odd_nat_70 : forall l p,
  (2 * p + 1 <= length l)%nat ->
  firstn (2 * p + 1) (strange_output_70 l) =
  strange_pairs_prefix_nat_70 l p ++ [nth p l 0].
Proof.
  intros l p Hle.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    rewrite Hm, Nat.div2_double in *.
    apply firstn_pairs_prefix_nat_odd_70; lia.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    rewrite Hm, Nat.div2_odd' in *.
    destruct (Nat.eq_dec p m) as [Heq | Hneq].
    + subst p.
      rewrite firstn_app.
      rewrite length_strange_pairs_prefix_nat_70.
      replace (2 * m + 1 - 2 * m)%nat with 1%nat by lia.
      rewrite firstn_all2.
      * reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + rewrite firstn_app.
      rewrite length_strange_pairs_prefix_nat_70.
      replace (2 * p + 1 - 2 * m)%nat with 0%nat by lia.
      rewrite app_nil_r.
      apply firstn_pairs_prefix_nat_odd_70; lia.
Qed.

Lemma nth_error_strange_output_even_nat_70 : forall l p,
  (2 * p < length l)%nat ->
  nth_error (strange_output_70 l) (2 * p) = Some (nth p l 0).
Proof.
  intros l p Hlt.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    rewrite Hm, Nat.div2_double in *.
    apply nth_error_pairs_prefix_even_70; lia.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    rewrite Hm, Nat.div2_odd' in *.
    destruct (Nat.eq_dec p m) as [Heq | Hneq].
    + subst p.
      rewrite nth_error_app2.
      * rewrite length_strange_pairs_prefix_nat_70.
        replace (2 * m - 2 * m)%nat with 0%nat by lia.
        reflexivity.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
    + rewrite nth_error_app1.
      * apply nth_error_pairs_prefix_even_70; lia.
      * rewrite length_strange_pairs_prefix_nat_70.
        lia.
Qed.

Lemma nth_error_strange_output_odd_nat_70 : forall l p,
  (2 * p + 1 < length l)%nat ->
  nth_error (strange_output_70 l) (2 * p + 1) =
  Some (nth (length l - S p) l 0).
Proof.
  intros l p Hlt.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    assert (Hdiv : Nat.div2 (length l) = m).
    { rewrite Hm. apply Nat.div2_double. }
    rewrite Hdiv.
    apply nth_error_pairs_prefix_odd_70.
    rewrite Hm in Hlt; lia.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    assert (Hdiv : Nat.div2 (length l) = m).
    { rewrite Hm. apply Nat.div2_odd'. }
    rewrite Hdiv.
    rewrite nth_error_app1.
    + apply nth_error_pairs_prefix_odd_70.
      rewrite Hm in Hlt; lia.
    + rewrite length_strange_pairs_prefix_nat_70.
      rewrite Hm in Hlt; lia.
Qed.

Lemma sorted_nth_le_70 : forall l i j,
  Sorted Z.le l ->
  (i <= j < length l)%nat ->
  nth i l 0 <= nth j l 0.
Proof.
  intros l i j Hs Hij.
  apply Sorted_StronglySorted in Hs.
  2:{ unfold Relations_1.Transitive; intros; lia. }
  revert i j Hij.
  induction Hs as [| a l Hss IH Hall]; intros i j Hij.
  - destruct i; destruct j; simpl; try lia;
      destruct Hij as [_ Hlt]; inversion Hlt.
  - destruct i as [| i], j as [| j].
    + simpl; lia.
    + simpl.
      eapply Forall_forall; eauto.
      apply nth_In.
      apply Nat.succ_lt_mono.
      exact (proj2 Hij).
    + destruct Hij as [Hle _].
      inversion Hle.
    + simpl.
      apply IH.
      split.
      * apply Nat.succ_le_mono.
        exact (proj1 Hij).
      * apply Nat.succ_lt_mono.
        exact (proj2 Hij).
Qed.

Lemma sorted_Znth_le_70 : forall l i j,
  Sorted Z.le l ->
  0 <= i ->
  i <= j ->
  j < Zlength l ->
  Znth i l 0 <= Znth j l 0.
Proof.
  intros l i j Hs Hi Hij Hj.
  unfold Znth.
  apply sorted_nth_le_70; [exact Hs|].
  split.
  - apply Z2Nat.inj_le; lia.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    exact Hj.
Qed.

Lemma permutation_count_z_70 : forall l1 l2 x,
  Permutation l1 l2 ->
  count_z x l1 = count_z x l2.
Proof.
  intros l1 l2 x Hperm.
  apply (Permutation_count_occ Z.eq_dec).
  exact Hperm.
Qed.

Lemma permutation_available_input_70 : forall l1 l2 out x i,
  Permutation l1 l2 ->
  available_after_prefix l1 out x i ->
  available_after_prefix l2 out x i.
Proof.
  intros l1 l2 out x i Hperm Havail.
  unfold available_after_prefix in *.
  rewrite <- (permutation_count_z_70 l1 l2 x Hperm).
  exact Havail.
Qed.

Lemma sublist_take_ends_perm_70 : forall (l : list Z) p n,
  n = Zlength l ->
  0 <= p ->
  2 * p + 2 <= n ->
  Permutation
    ([Znth p l 0; Znth (n - 1 - p) l 0] ++
       sublist (p + 1) (n - 1 - p) l)
    (sublist p (n - p) l).
Proof.
  intros l p n Hn Hp Hroom.
  rewrite (sublist_split p (n - p) (p + 1) l) by lia.
  rewrite (sublist_single 0 p l) by lia.
  rewrite (sublist_split (p + 1) (n - p) (n - 1 - p) l) by lia.
  replace (n - p) with (n - 1 - p + 1) by lia.
  rewrite (sublist_single 0 (n - 1 - p) l) by lia.
  simpl.
  apply perm_skip.
  apply Permutation_cons_append.
Qed.

Lemma strange_pairs_prefix_nat_remaining_perm_70 : forall (l : list Z) p,
  (2 * p <= length l)%nat ->
  Permutation
    (strange_pairs_prefix_nat_70 l p ++
       sublist (Z.of_nat p) (Zlength l - Z.of_nat p) l)
    l.
Proof.
  intros l p.
  induction p as [| p IH]; intros Hroom.
  - simpl.
    rewrite Z.sub_0_r.
    rewrite (sublist_self l (Zlength l) eq_refl).
    reflexivity.
  - rewrite strange_pairs_prefix_nat_snoc_70.
    transitivity
      (strange_pairs_prefix_nat_70 l p ++
         sublist (Z.of_nat p) (Zlength l - Z.of_nat p) l).
    + rewrite <- app_assoc.
      apply Permutation_app_head.
      unfold pair_at_70.
      replace (nth p l 0) with (Znth (Z.of_nat p) l 0).
      2:{ unfold Znth. rewrite Nat2Z.id. reflexivity. }
      replace (nth (length l - S p) l 0)
        with (Znth (Zlength l - 1 - Z.of_nat p) l 0).
      2:{ unfold Znth.
          rewrite Zlength_correct.
          replace (Z.to_nat (Z.of_nat (length l) - 1 - Z.of_nat p))
            with (length l - S p)%nat by lia.
          reflexivity. }
      replace (Z.of_nat (S p)) with (Z.of_nat p + 1) by lia.
      replace (Zlength l - (Z.of_nat p + 1))
        with (Zlength l - 1 - Z.of_nat p) by lia.
      apply (sublist_take_ends_perm_70 l (Z.of_nat p) (Zlength l)).
      * reflexivity.
      * lia.
      * rewrite Zlength_correct.
        lia.
    + apply IH.
      lia.
Qed.

Lemma strange_pairs_prefix_remaining_perm_70 : forall (l : list Z) p,
  0 <= p ->
  2 * p <= Zlength l ->
  Permutation
    (strange_pairs_prefix_70 l p ++ sublist p (Zlength l - p) l)
    l.
Proof.
  intros l p Hp Hroom.
  assert (Hp_eq : p = Z.of_nat (Z.to_nat p)).
  { rewrite Z2Nat.id; lia. }
  unfold strange_pairs_prefix_70.
  rewrite Hp_eq.
  rewrite Nat2Z.id.
  apply strange_pairs_prefix_nat_remaining_perm_70.
  apply Nat2Z.inj_le.
  rewrite Nat2Z.inj_mul, Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma strange_output_perm_70 : forall (l : list Z),
  Permutation (strange_output_70 l) l.
Proof.
  intros l.
  unfold strange_output_70.
  destruct (Nat.even (length l)) eqn:Heven.
  - apply Nat.even_spec in Heven as [m Hm].
    rewrite Hm, Nat.div2_double.
    pose proof (strange_pairs_prefix_nat_remaining_perm_70 l m) as Hperm.
    assert (Hroom : (2 * m <= length l)%nat) by lia.
    specialize (Hperm Hroom).
    replace (Zlength l - Z.of_nat m) with (Z.of_nat m) in Hperm.
    2:{ rewrite Zlength_correct, Hm. lia. }
    rewrite Zsublist_nil in Hperm by lia.
    rewrite app_nil_r in Hperm.
    exact Hperm.
  - assert (Hodd : Nat.odd (length l) = true).
    { rewrite <- Nat.negb_even, Heven. reflexivity. }
    apply Nat.odd_spec in Hodd as [m Hm].
    rewrite Hm, Nat.div2_odd'.
    pose proof (strange_pairs_prefix_nat_remaining_perm_70 l m) as Hperm.
    assert (Hroom : (2 * m <= length l)%nat) by lia.
    specialize (Hperm Hroom).
    replace (Zlength l - Z.of_nat m) with (Z.of_nat m + 1) in Hperm.
    2:{ rewrite Zlength_correct, Hm. lia. }
    rewrite (sublist_single 0 (Z.of_nat m) l) in Hperm.
    + unfold Znth in Hperm.
      rewrite Nat2Z.id in Hperm.
      exact Hperm.
    + rewrite Zlength_correct, Hm.
      lia.
Qed.

Lemma available_in_remaining_70 : forall l out rem x i,
  Permutation (firstn i out ++ rem) l ->
  available_after_prefix l out x i ->
  In x rem.
Proof.
  intros l out rem x i Hperm Havail.
  unfold available_after_prefix, count_z in *.
  apply (proj2 (count_occ_In Z.eq_dec rem x)).
  assert (Hcount :
    count_occ Z.eq_dec l x =
    (count_occ Z.eq_dec (firstn i out) x + count_occ Z.eq_dec rem x)%nat).
  { rewrite <- (proj1 (Permutation_count_occ Z.eq_dec (firstn i out ++ rem) l) Hperm x).
    rewrite count_occ_app.
    reflexivity. }
  lia.
Qed.

Lemma in_remaining_available_70 : forall l out rem x i,
  Permutation (firstn i out ++ rem) l ->
  In x rem ->
  available_after_prefix l out x i.
Proof.
  intros l out rem x i Hperm Hin.
  unfold available_after_prefix, count_z.
  assert (Hcount :
    count_occ Z.eq_dec l x =
    (count_occ Z.eq_dec (firstn i out) x + count_occ Z.eq_dec rem x)%nat).
  { rewrite <- (proj1 (Permutation_count_occ Z.eq_dec (firstn i out ++ rem) l) Hperm x).
    rewrite count_occ_app.
    reflexivity. }
  apply (proj1 (count_occ_In Z.eq_dec rem x)) in Hin.
  rewrite Hcount.
  lia.
Qed.

Lemma in_sublist_Znth_70 : forall (l : list Z) lo hi x,
  0 <= lo <= hi ->
  hi <= Zlength l ->
  In x (sublist lo hi l) ->
  exists k, lo <= k < hi /\ x = Znth k l 0.
Proof.
  intros l lo hi x Hlohi Hhi Hin.
  apply In_nth_error in Hin as [idx Hnth].
  exists (lo + Z.of_nat idx).
  assert (Hidx : (idx < length (sublist lo hi l))%nat).
  { apply nth_error_Some.
    rewrite Hnth.
    discriminate. }
  split.
  - rewrite sublist_length in Hidx by lia.
    apply Nat2Z.inj_lt in Hidx.
    rewrite Z2Nat.id in Hidx by lia.
    lia.
  - apply nth_error_nth with (d := 0) in Hnth.
    rewrite <- Hnth.
    replace (nth idx (sublist lo hi l) 0) with
      (Znth (Z.of_nat idx) (sublist lo hi l) 0).
    2:{ unfold Znth. rewrite Nat2Z.id. reflexivity. }
    assert (HidxZ : 0 <= Z.of_nat idx < hi - lo).
    { rewrite sublist_length in Hidx by lia.
      apply Nat2Z.inj_lt in Hidx.
      rewrite Z2Nat.id in Hidx by lia.
      lia. }
    rewrite Znth_sublist by lia.
    replace (Z.of_nat idx + lo) with (lo + Z.of_nat idx) by lia.
    reflexivity.
Qed.

Lemma sorted_sublist_min_70 : forall l lo hi y,
  Sorted Z.le l ->
  0 <= lo < hi ->
  hi <= Zlength l ->
  In y (sublist lo hi l) ->
  Znth lo l 0 <= y.
Proof.
  intros l lo hi y Hsorted Hlohi Hhi Hin.
  destruct (in_sublist_Znth_70 l lo hi y) as [k [[Hlok Hkhi] Hy]];
    try lia; try exact Hin.
  rewrite Hy.
  eapply sorted_Znth_le_70; eauto; lia.
Qed.

Lemma sorted_sublist_max_70 : forall l lo hi y,
  Sorted Z.le l ->
  0 <= lo < hi ->
  hi <= Zlength l ->
  In y (sublist lo hi l) ->
  y <= Znth (hi - 1) l 0.
Proof.
  intros l lo hi y Hsorted Hlohi Hhi Hin.
  destruct (in_sublist_Znth_70 l lo hi y) as [k [[Hlok Hkhi] Hy]];
    try lia; try exact Hin.
  rewrite Hy.
  eapply sorted_Znth_le_70; eauto; lia.
Qed.

Lemma Znth_in_sublist_70 : forall (l : list Z) lo hi k,
  0 <= lo <= k ->
  k < hi ->
  hi <= Zlength l ->
  In (Znth k l 0) (sublist lo hi l).
Proof.
  intros l lo hi k Hlok Hkhi Hhi.
  rewrite (sublist_split lo hi k l) by lia.
  apply in_or_app. right.
  rewrite (sublist_split k hi (k + 1) l) by lia.
  rewrite (sublist_single 0 k l) by lia.
  simpl; auto.
Qed.

Lemma strange_pairs_prefix_nat_left_remaining_perm_70 : forall (l : list Z) p,
  (2 * p + 1 <= length l)%nat ->
  Permutation
    ((strange_pairs_prefix_nat_70 l p ++ [nth p l 0]) ++
       sublist (Z.of_nat p + 1) (Zlength l - Z.of_nat p) l)
    l.
Proof.
  intros l p Hroom.
  transitivity
    (strange_pairs_prefix_nat_70 l p ++
       sublist (Z.of_nat p) (Zlength l - Z.of_nat p) l).
  - rewrite <- app_assoc.
    apply Permutation_app_head.
    replace (nth p l 0) with (Znth (Z.of_nat p) l 0).
    2:{ unfold Znth. rewrite Nat2Z.id. reflexivity. }
    rewrite (sublist_split (Z.of_nat p) (Zlength l - Z.of_nat p)
               (Z.of_nat p + 1) l)
      by (try rewrite Zlength_correct; lia).
    rewrite (sublist_single 0 (Z.of_nat p) l)
      by (try rewrite Zlength_correct; lia).
    reflexivity.
  - apply strange_pairs_prefix_nat_remaining_perm_70.
    lia.
Qed.

Lemma sorted_strange_output_spec_70 : forall input sorted_l,
  problem_70_pre_z input ->
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  problem_70_spec_z input (strange_output_70 sorted_l).
Proof.
  intros input sorted_l Hpre Hsorted Hperm.
  unfold problem_70_spec_z.
  unfold problem_70_pre_z in Hpre.
  unfold problem_70_spec.
  split.
  - transitivity sorted_l.
    + apply strange_output_perm_70.
    + symmetry; exact Hperm.
  - intros i v Hnth.
    unfold strange_extremal_at.
    assert (Hsorted0 : Sorted Z.le sorted_l).
    { unfold sorted_int_list_by in Hsorted. simpl in Hsorted. exact Hsorted. }
    assert (Hi_lt_out : (i < length (strange_output_70 sorted_l))%nat).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    rewrite length_strange_output_nat_70 in Hi_lt_out.
    destruct (Nat.even i) eqn:Heven.
    + apply Nat.even_spec in Heven as [p Hi].
      subst i.
      assert (Hlt : (2 * p < length sorted_l)%nat) by exact Hi_lt_out.
      pose proof (nth_error_strange_output_even_nat_70 sorted_l p Hlt) as Hv.
      rewrite Hnth in Hv.
      inversion Hv; subst v; clear Hv.
      set (rem := sublist (Z.of_nat p) (Zlength sorted_l - Z.of_nat p) sorted_l).
      assert (Hfirst :
        firstn (2 * p) (strange_output_70 sorted_l) =
        strange_pairs_prefix_nat_70 sorted_l p).
      { apply firstn_strange_output_even_nat_70. lia. }
      assert (Hremperm :
        Permutation (firstn (2 * p) (strange_output_70 sorted_l) ++ rem) sorted_l).
      { rewrite Hfirst. unfold rem.
        apply strange_pairs_prefix_nat_remaining_perm_70. lia. }
      replace (nth p sorted_l 0) with (Znth (Z.of_nat p) sorted_l 0).
      2:{ unfold Znth. rewrite Nat2Z.id. reflexivity. }
      split.
      * apply (permutation_available_input_70 sorted_l input
                 (strange_output_70 sorted_l)
                 (Znth (Z.of_nat p) sorted_l 0) (2 * p)).
        -- symmetry; exact Hperm.
        -- eapply in_remaining_available_70.
           ++ exact Hremperm.
           ++ unfold rem.
              apply Znth_in_sublist_70; rewrite ?Zlength_correct; lia.
      * split.
        -- intros _ y Hy.
           assert (Hys :
             available_after_prefix sorted_l (strange_output_70 sorted_l) y (2 * p)).
           { eapply permutation_available_input_70; [exact Hperm|exact Hy]. }
           pose proof
             (available_in_remaining_70 sorted_l (strange_output_70 sorted_l)
                rem y (2 * p) Hremperm Hys) as Hyin.
           unfold rem in Hyin.
           eapply sorted_sublist_min_70; eauto; rewrite ?Zlength_correct; lia.
        -- intros Hodd y Hy.
           exfalso.
           apply Nat.odd_spec in Hodd as [q Hq].
           lia.
    + assert (Hoddtrue : Nat.odd i = true).
      { rewrite <- Nat.negb_even, Heven. reflexivity. }
      apply Nat.odd_spec in Hoddtrue as [p Hi].
      subst i.
      assert (Hlt : (2 * p + 1 < length sorted_l)%nat) by exact Hi_lt_out.
      pose proof (nth_error_strange_output_odd_nat_70 sorted_l p Hlt) as Hv.
      rewrite Hnth in Hv.
      inversion Hv; subst v; clear Hv.
      set (rem :=
        sublist (Z.of_nat p + 1) (Zlength sorted_l - Z.of_nat p) sorted_l).
      assert (Hfirst :
        firstn (2 * p + 1) (strange_output_70 sorted_l) =
        strange_pairs_prefix_nat_70 sorted_l p ++ [nth p sorted_l 0]).
      { apply firstn_strange_output_odd_nat_70. lia. }
      assert (Hremperm :
        Permutation (firstn (2 * p + 1) (strange_output_70 sorted_l) ++ rem)
          sorted_l).
      { rewrite Hfirst. unfold rem.
        apply strange_pairs_prefix_nat_left_remaining_perm_70. lia. }
      replace (nth (length sorted_l - S p) sorted_l 0)
        with (Znth (Zlength sorted_l - 1 - Z.of_nat p) sorted_l 0).
      2:{ unfold Znth.
          rewrite Zlength_correct.
          replace (Z.to_nat (Z.of_nat (length sorted_l) - 1 - Z.of_nat p))
            with (length sorted_l - S p)%nat by lia.
          reflexivity. }
      split.
      * apply (permutation_available_input_70 sorted_l input
                 (strange_output_70 sorted_l)
                 (Znth (Zlength sorted_l - 1 - Z.of_nat p) sorted_l 0)
                 (2 * p + 1)).
        -- symmetry; exact Hperm.
        -- eapply in_remaining_available_70.
           ++ exact Hremperm.
           ++ unfold rem.
              apply Znth_in_sublist_70; rewrite ?Zlength_correct; lia.
      * split.
        -- intros Hev y Hy.
           exfalso.
           discriminate.
        -- intros _ y Hy.
           assert (Hys :
             available_after_prefix sorted_l (strange_output_70 sorted_l) y
               (2 * p + 1)).
           { eapply permutation_available_input_70; [exact Hperm|exact Hy]. }
           pose proof
             (available_in_remaining_70 sorted_l (strange_output_70 sorted_l)
                rem y (2 * p + 1) Hremperm Hys) as Hyin.
           unfold rem in Hyin.
           replace (Zlength sorted_l - 1 - Z.of_nat p)
             with ((Zlength sorted_l - Z.of_nat p) - 1) by lia.
           eapply sorted_sublist_max_70; eauto; rewrite ?Zlength_correct; lia.
Qed.
