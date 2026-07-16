Load "../spec/61".
Load "../StringClaude/string_bridge".

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition string_length (s : list Z) : Z :=
  Zlength s.

Definition problem_61_pre_z (brackets : list Z) : Prop :=
  problem_61_pre (string_of_list_z brackets).

Definition problem_61_spec_z (brackets : list Z) (output : bool) : Prop :=
  problem_61_spec (string_of_list_z brackets) output.

Definition ascii_delta_61 (c : ascii) : Z :=
  if ascii_dec c "("%char then 1
  else if ascii_dec c ")"%char then -1
  else 0.

Fixpoint ascii_balance_61 (l : list ascii) : Z :=
  match l with
  | [] => 0
  | c :: rest => ascii_delta_61 c + ascii_balance_61 rest
  end.

Definition ascii_prefix_nonnegative_61 (l : list ascii) : Prop :=
  forall n, (n <= List.length l)%nat ->
    0 <= ascii_balance_61 (firstn n l).

Lemma ascii_delta_open_61 : ascii_delta_61 "("%char = 1.
Proof. reflexivity. Qed.

Lemma ascii_delta_close_61 : ascii_delta_61 ")"%char = -1.
Proof. reflexivity. Qed.

Lemma ascii_balance_app_61 : forall l1 l2,
  ascii_balance_61 (l1 ++ l2) =
  ascii_balance_61 l1 + ascii_balance_61 l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2; simpl; [lia|].
  rewrite IH; lia.
Qed.

Lemma balanced_parentheses_balance_zero_61 : forall l,
  balanced_parentheses l -> ascii_balance_61 l = 0.
Proof.
  intros l Hbal.
  induction Hbal as [|inner Hinner IH|left right Hleft IHl Hright IHr].
  - reflexivity.
  - simpl. rewrite ascii_balance_app_61. simpl.
    rewrite IH. reflexivity.
  - rewrite ascii_balance_app_61, IHl, IHr. lia.
Qed.

Lemma balanced_parentheses_prefix_nonnegative_61 : forall l,
  balanced_parentheses l -> ascii_prefix_nonnegative_61 l.
Proof.
  intros l Hbal.
  unfold ascii_prefix_nonnegative_61.
  induction Hbal as [|inner Hinner IH|left right Hleft IHl Hright IHr].
  - intros [|n] Hn; [reflexivity|simpl in Hn; lia].
  - unfold ascii_prefix_nonnegative_61 in IH.
    intros [|n] Hn; [reflexivity|].
    simpl firstn. simpl List.length in Hn.
    destruct (Nat.le_gt_cases n (List.length inner)) as [Hinside|Hfull].
    + rewrite firstn_app.
      replace (n - List.length inner)%nat with 0%nat by lia.
      simpl. rewrite app_nil_r.
      change (0 <= ascii_delta_61 "("%char +
        ascii_balance_61 (firstn n inner)).
      rewrite ascii_delta_open_61.
      pose proof (IH n Hinside) as Hpref. lia.
    + assert (n = S (List.length inner)).
      { rewrite length_app in Hn. simpl in Hn. lia. }
      subst n.
      replace (S (List.length inner)) with
        (List.length (inner ++ [")"%char]))
        by (rewrite app_length; simpl; lia).
      rewrite firstn_all.
      rewrite (balanced_parentheses_balance_zero_61 _
        (balanced_wrap inner Hinner)). lia.
  - unfold ascii_prefix_nonnegative_61 in IHl, IHr.
    intros n Hn.
    rewrite firstn_app, ascii_balance_app_61.
    destruct (Nat.le_gt_cases n (List.length left)) as [Hinleft|Hinright].
    + replace (n - List.length left)%nat with 0%nat by lia.
      rewrite firstn_O. simpl ascii_balance_61. rewrite Z.add_0_r.
      exact (IHl n Hinleft).
    + rewrite firstn_all2 by lia.
      specialize (IHr (n - List.length left)%nat ltac:(rewrite app_length in Hn; lia)).
      rewrite (balanced_parentheses_balance_zero_61 left Hleft). lia.
Qed.

Inductive bracket_prefix_shape_61 : list Z -> nat -> Prop :=
  | bracket_shape_balanced_61 : forall l,
      balanced_parentheses (map ascii_of_z l) ->
      bracket_prefix_shape_61 l O
  | bracket_shape_open_context_61 : forall prefix inner depth,
      bracket_prefix_shape_61 prefix depth ->
      balanced_parentheses (map ascii_of_z inner) ->
      bracket_prefix_shape_61 (prefix ++ 40 :: inner) (S depth).

Lemma ascii_of_z_open_61 : ascii_of_z 40 = "("%char.
Proof. reflexivity. Qed.

Lemma ascii_of_z_close_61 : ascii_of_z 41 = ")"%char.
Proof. reflexivity. Qed.

Lemma bracket_shape_append_balanced_61 : forall prefix depth suffix,
  bracket_prefix_shape_61 prefix depth ->
  balanced_parentheses (map ascii_of_z suffix) ->
  bracket_prefix_shape_61 (prefix ++ suffix) depth.
Proof.
  intros prefix depth suffix Hshape Hsuffix.
  induction Hshape as [l Hl|p inner n Hp IH Hinner].
  - apply bracket_shape_balanced_61.
    rewrite map_app. now apply balanced_concat.
  - replace ((p ++ 40 :: inner) ++ suffix)
      with (p ++ 40 :: (inner ++ suffix))
      by (rewrite <- app_assoc; reflexivity).
    apply bracket_shape_open_context_61; [exact Hp|].
    rewrite map_app. now apply balanced_concat.
Qed.

Lemma bracket_shape_append_open_61 : forall prefix depth,
  bracket_prefix_shape_61 prefix depth ->
  bracket_prefix_shape_61 (prefix ++ [40]) (S depth).
Proof.
  intros prefix depth Hshape.
  change (bracket_prefix_shape_61 (prefix ++ 40 :: []) (S depth)).
  apply bracket_shape_open_context_61; [exact Hshape|].
  constructor.
Qed.

Lemma bracket_shape_append_close_61 : forall prefix depth,
  bracket_prefix_shape_61 prefix (S depth) ->
  bracket_prefix_shape_61 (prefix ++ [41]) depth.
Proof.
  intros prefix depth Hshape.
  inversion Hshape as [|p inner depth' Hp Hinner]; subst.
  replace ((p ++ 40 :: inner) ++ [41])
    with (p ++ (40 :: inner ++ [41]))
    by (rewrite <- app_assoc; reflexivity).
  apply bracket_shape_append_balanced_61; [exact Hp|].
  change (balanced_parentheses
    (ascii_of_z 40 :: map ascii_of_z (inner ++ [41]))).
  rewrite map_app. simpl.
  rewrite ascii_of_z_open_61, ascii_of_z_close_61.
  now apply balanced_wrap.
Qed.

Lemma bracket_shape_balance_61 : forall prefix depth,
  bracket_prefix_shape_61 prefix depth ->
  ascii_balance_61 (map ascii_of_z prefix) = Z.of_nat depth.
Proof.
  intros prefix depth Hshape.
  induction Hshape as [l Hl|p inner n Hp IH Hinner].
  - rewrite (balanced_parentheses_balance_zero_61 _ Hl). reflexivity.
  - rewrite map_app, ascii_balance_app_61. simpl.
    rewrite ascii_of_z_open_61, ascii_delta_open_61, IH.
    rewrite (balanced_parentheses_balance_zero_61 _ Hinner).
    lia.
Qed.

Lemma bracket_shape_zero_balanced_61 : forall prefix,
  bracket_prefix_shape_61 prefix O ->
  balanced_parentheses (map ascii_of_z prefix).
Proof.
  intros prefix Hshape. inversion Hshape; subst; assumption.
Qed.

Definition bracket_state_61 (s : list Z) (i level : Z) : Prop :=
  0 <= i <= Zlength s /\
  exists depth,
    level = Z.of_nat depth /\
    bracket_prefix_shape_61 (sublist 0 i s) depth.

Lemma bracket_state_initial_61 : forall s,
  bracket_state_61 s 0 0.
Proof.
  intros s. split; [unfold Zlength; rewrite Zlength_correct; lia|].
  exists O. split; [reflexivity|].
  change (bracket_prefix_shape_61 [] O).
  apply bracket_shape_balanced_61. constructor.
Qed.

Lemma bracket_state_open_61 : forall s i level,
  bracket_state_61 s i level ->
  i < Zlength s ->
  Znth i s 0 = 40 ->
  bracket_state_61 s (i + 1) (level + 1).
Proof.
  intros s i level [Hbounds [depth [Hlevel Hshape]]] Hi Hchar.
  split; [lia|]. exists (S depth). split; [lia|].
  rewrite (helper_sublist_snoc_Z s i 0) by lia.
  rewrite Hchar. now apply bracket_shape_append_open_61.
Qed.

Lemma bracket_state_close_61 : forall s i level,
  bracket_state_61 s i level ->
  i < Zlength s ->
  Znth i s 0 = 41 ->
  0 < level ->
  bracket_state_61 s (i + 1) (level - 1).
Proof.
  intros s i level [Hbounds [depth [Hlevel Hshape]]] Hi Hchar Hpos.
  destruct depth as [|depth]; simpl in Hlevel; [lia|].
  split; [lia|]. exists depth. split; [lia|].
  rewrite (helper_sublist_snoc_Z s i 0) by lia.
  rewrite Hchar. now apply bracket_shape_append_close_61.
Qed.

Lemma problem_61_pre_z_char_61 : forall s i,
  problem_61_pre_z s ->
  all_ascii s ->
  0 <= i < Zlength s ->
  Znth i s 0 = 40 \/ Znth i s 0 = 41.
Proof.
  intros s i Hpre Hascii Hi.
  unfold problem_61_pre_z, problem_61_pre in Hpre.
  rewrite list_ascii_of_string_string_of_list_z in Hpre.
  apply Forall_forall with (x := ascii_of_z (Znth i s 0)) in Hpre.
  - specialize (Hascii i Hi).
    destruct Hpre as [Hopen|Hclose].
    + left. apply (f_equal nat_of_ascii) in Hopen.
      rewrite nat_of_ascii_ascii_of_z in Hopen by lia.
      change (Z.to_nat (Znth i s 0) = 40%nat) in Hopen.
      apply (f_equal Z.of_nat) in Hopen.
      rewrite Z2Nat.id in Hopen by lia. exact Hopen.
    + right. apply (f_equal nat_of_ascii) in Hclose.
      rewrite nat_of_ascii_ascii_of_z in Hclose by lia.
      change (Z.to_nat (Znth i s 0) = 41%nat) in Hclose.
      apply (f_equal Z.of_nat) in Hclose.
      rewrite Z2Nat.id in Hclose by lia. exact Hclose.
  - apply in_map. unfold Znth. apply nth_In.
    rewrite Zlength_correct in Hi. lia.
Qed.

Lemma bracket_state_early_close_false_61 : forall s i,
  bracket_state_61 s i 0 ->
  i < Zlength s ->
  Znth i s 0 = 41 ->
  problem_61_spec_z s false.
Proof.
  intros s i [Hbounds [depth [Hlevel Hshape]]] Hi Hchar.
  destruct depth as [|depth]; simpl in Hlevel; [|lia].
  unfold problem_61_spec_z, problem_61_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  split; [discriminate|].
  intros Hbalanced.
  pose proof (balanced_parentheses_prefix_nonnegative_61 _ Hbalanced) as Hprefix.
  assert (Hnat :
    (Z.to_nat (i + 1) <= List.length (map ascii_of_z s))%nat).
  {
    rewrite length_map. apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia.
  }
  specialize (Hprefix (Z.to_nat (i + 1)) Hnat).
  assert (Hnext :
    ascii_balance_61 (map ascii_of_z (sublist 0 (i + 1) s)) = -1).
  {
    rewrite (helper_sublist_snoc_Z s i 0) by lia.
    rewrite Hchar, map_app, ascii_balance_app_61. simpl.
    rewrite ascii_of_z_close_61, ascii_delta_close_61.
    rewrite (bracket_shape_balance_61 _ O Hshape). lia.
  }
  unfold sublist in Hnext. simpl in Hnext.
  rewrite <- firstn_map in Hnext.
  rewrite Hnext in Hprefix. lia.
Qed.

Lemma bracket_state_final_true_61 : forall s,
  bracket_state_61 s (Zlength s) 0 ->
  problem_61_spec_z s true.
Proof.
  intros s [_ [depth [Hlevel Hshape]]].
  destruct depth as [|depth]; simpl in Hlevel; [|lia].
  rewrite sublist_self in Hshape by reflexivity.
  unfold problem_61_spec_z, problem_61_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  split; [intros _; now apply bracket_shape_zero_balanced_61|reflexivity].
Qed.

Lemma bracket_state_final_false_61 : forall s level,
  bracket_state_61 s (Zlength s) level ->
  level <> 0 ->
  problem_61_spec_z s false.
Proof.
  intros s level [_ [depth [Hlevel Hshape]]] Hnonzero.
  rewrite sublist_self in Hshape by reflexivity.
  unfold problem_61_spec_z, problem_61_spec.
  rewrite list_ascii_of_string_string_of_list_z.
  split; [discriminate|].
  intros Hbalanced.
  pose proof (balanced_parentheses_balance_zero_61 _ Hbalanced) as Hzero.
  pose proof (bracket_shape_balance_61 _ depth Hshape) as Hdepth.
  destruct depth; simpl in Hlevel; lia.
Qed.
