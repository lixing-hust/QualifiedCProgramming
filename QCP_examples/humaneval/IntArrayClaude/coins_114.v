Load "../spec/114".

Definition list_sum_Z_114 := list_sum.
Lemma list_sum_Z_114_unfold : forall l,
  list_sum_Z_114 l = fold_left Z.add l 0.
Proof. reflexivity. Qed.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From AUXLib Require Import List_lemma ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition LLONG_MIN : Z := -9223372036854775808.
Definition LLONG_MAX : Z := 9223372036854775807.

Definition problem_114_pre_z (nums : list Z) : Prop :=
  problem_114_pre nums.

Fixpoint min_suffix_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev := min_suffix_prefix_nat n' nums in
      let x := Znth (Z.of_nat n') nums 0 in
      if Z.ltb prev 0 then prev + x else x
  end.

Definition min_suffix_prefix (i : Z) (nums : list Z) : Z :=
  min_suffix_prefix_nat (Z.to_nat i) nums.

Fixpoint min_subarray_prefix_nat (n : nat) (nums : list Z) : Z :=
  match n with
  | O => 0
  | S O => Znth 0 nums 0
  | S n' =>
      let prev_min := min_subarray_prefix_nat n' nums in
      let cur := min_suffix_prefix_nat (S n') nums in
      if Z.ltb cur prev_min then cur else prev_min
  end.

Definition min_subarray_prefix (i : Z) (nums : list Z) : Z :=
  min_subarray_prefix_nat (Z.to_nat i) nums.

Definition problem_114_spec_z (nums : list Z) (result : Z) : Prop :=
  problem_114_spec nums result.

Definition zsum_114 (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition suffix_min_spec (nums : list Z) (result : Z) : Prop :=
  (exists suffix prefix,
      suffix <> [] /\
      nums = prefix ++ suffix /\
      zsum_114 suffix = result) /\
  (forall suffix prefix,
      suffix <> [] ->
      nums = prefix ++ suffix ->
      result <= zsum_114 suffix).

Definition subarray_min_spec_114 (nums : list Z) (result : Z) : Prop :=
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    zsum_114 sub_array = result) /\
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    result <= zsum_114 sub_array).

Definition list_int64_range (nums : list Z) : Prop :=
  forall i, 0 <= i < Zlength nums -> LLONG_MIN <= Znth i nums 0 <= LLONG_MAX.

Definition kadane_int64_range (nums : list Z) : Prop :=
  list_int64_range nums /\
  (forall i,
      1 <= i < Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums + Znth i nums 0 <= LLONG_MAX) /\
  (forall i,
      1 <= i <= Zlength nums ->
      LLONG_MIN <= min_suffix_prefix i nums <= LLONG_MAX /\
      LLONG_MIN <= min_subarray_prefix i nums <= LLONG_MAX).

Lemma min_suffix_prefix_1 : forall nums,
  min_suffix_prefix 1 nums = Znth 0 nums 0.
Proof.
  reflexivity.
Qed.

Lemma min_subarray_prefix_1 : forall nums,
  min_subarray_prefix 1 nums = Znth 0 nums 0.
Proof.
  reflexivity.
Qed.

Lemma min_suffix_prefix_step_lt : forall nums i,
  1 <= i ->
  min_suffix_prefix i nums < 0 ->
  min_suffix_prefix (i + 1) nums =
    min_suffix_prefix i nums + Znth i nums 0.
Proof.
  intros nums i Hi Hlt.
  unfold min_suffix_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  replace (Z.of_nat (S n)) with i by lia.
  change match n with
         | O => Znth 0 nums 0
         | S _ =>
             if min_suffix_prefix_nat n nums <? 0
             then min_suffix_prefix_nat n nums + Znth (Z.of_nat n) nums 0
             else Znth (Z.of_nat n) nums 0
         end with (min_suffix_prefix_nat (S n) nums).
  assert ((min_suffix_prefix_nat (S n) nums <? 0) = true) as Htrue.
  { apply Z.ltb_lt. unfold min_suffix_prefix in Hlt.
    replace (Z.to_nat i) with (S n) in Hlt by lia. exact Hlt. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma min_suffix_prefix_step_ge : forall nums i,
  1 <= i ->
  min_suffix_prefix i nums >= 0 ->
  min_suffix_prefix (i + 1) nums = Znth i nums 0.
Proof.
  intros nums i Hi Hge.
  unfold min_suffix_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  simpl.
  change (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat (S n)).
  replace (Z.of_nat (S n)) with i by lia.
  change match n with
         | O => Znth 0 nums 0
         | S _ =>
             if min_suffix_prefix_nat n nums <? 0
             then min_suffix_prefix_nat n nums + Znth (Z.of_nat n) nums 0
             else Znth (Z.of_nat n) nums 0
         end with (min_suffix_prefix_nat (S n) nums).
  assert ((min_suffix_prefix_nat (S n) nums <? 0) = false) as Hfalse.
  { apply Z.ltb_ge. unfold min_suffix_prefix in Hge.
    replace (Z.to_nat i) with (S n) in Hge by lia. lia. }
  rewrite Hfalse.
  reflexivity.
Qed.

Lemma min_subarray_prefix_nat_step_lt : forall nums n cur,
  cur = min_suffix_prefix_nat (S (S n)) nums ->
  cur < min_subarray_prefix_nat (S n) nums ->
  min_subarray_prefix_nat (S (S n)) nums = cur.
Proof.
  intros nums n cur Hcur Hlt.
  cbn [min_subarray_prefix_nat].
  rewrite <- Hcur.
  set (prev :=
    match n with
    | O => Znth 0 nums 0
    | S _ =>
        if min_suffix_prefix_nat (S n) nums <? min_subarray_prefix_nat n nums
        then min_suffix_prefix_nat (S n) nums
        else min_subarray_prefix_nat n nums
    end).
  change (min_subarray_prefix_nat (S n) nums) with prev in Hlt.
  assert ((cur <? prev) = true) as Htrue.
  { apply Z.ltb_lt. exact Hlt. }
  rewrite Htrue.
  reflexivity.
Qed.

Lemma min_subarray_prefix_nat_step_ge : forall nums n cur,
  cur = min_suffix_prefix_nat (S (S n)) nums ->
  cur >= min_subarray_prefix_nat (S n) nums ->
  min_subarray_prefix_nat (S (S n)) nums = min_subarray_prefix_nat (S n) nums.
Proof.
  intros nums n cur Hcur Hge.
  cbn [min_subarray_prefix_nat].
  rewrite <- Hcur.
  set (prev :=
    match n with
    | O => Znth 0 nums 0
    | S _ =>
        if min_suffix_prefix_nat (S n) nums <? min_subarray_prefix_nat n nums
        then min_suffix_prefix_nat (S n) nums
        else min_subarray_prefix_nat n nums
    end).
  change (min_subarray_prefix_nat (S n) nums) with prev in Hge.
  assert ((cur <? prev) = false) as Hfalse.
  { apply Z.ltb_ge. lia. }
  rewrite Hfalse.
  reflexivity.
Qed.

Lemma min_subarray_prefix_step_lt : forall nums i cur,
  1 <= i ->
  cur = min_suffix_prefix (i + 1) nums ->
  cur < min_subarray_prefix i nums ->
  min_subarray_prefix (i + 1) nums = cur.
Proof.
  intros nums i cur Hi Hcur Hlt.
  unfold min_subarray_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  apply (min_subarray_prefix_nat_step_lt nums n cur).
  - replace (Z.of_nat (S n)) with i by lia.
    unfold min_suffix_prefix in Hcur.
    replace (Z.to_nat (i + 1)) with (S (S n)) in Hcur by lia.
    exact Hcur.
  - unfold min_subarray_prefix in Hlt.
    replace (Z.to_nat i) with (S n) in Hlt by lia.
    exact Hlt.
Qed.

Lemma min_subarray_prefix_step_ge : forall nums i cur,
  1 <= i ->
  cur = min_suffix_prefix (i + 1) nums ->
  cur >= min_subarray_prefix i nums ->
  min_subarray_prefix (i + 1) nums = min_subarray_prefix i nums.
Proof.
  intros nums i cur Hi Hcur Hge.
  unfold min_subarray_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [|n] eqn:Hi_nat; [lia |].
  apply (min_subarray_prefix_nat_step_ge nums n cur).
  - replace (Z.of_nat (S n)) with i by lia.
    unfold min_suffix_prefix in Hcur.
    replace (Z.to_nat (i + 1)) with (S (S n)) in Hcur by lia.
    exact Hcur.
  - unfold min_subarray_prefix in Hge.
    replace (Z.to_nat i) with (S n) in Hge by lia.
    lia.
Qed.

Lemma list_sum_acc_114 : forall l acc,
  fold_left Z.add l acc = acc + zsum_114 l.
Proof.
  induction l as [|x xs IH]; intros acc.
  - unfold zsum_114. simpl. lia.
  - simpl.
    rewrite (IH (acc + x)).
    unfold zsum_114 at 2. simpl.
    replace (0 + x) with x by lia.
    rewrite (IH x).
    lia.
Qed.

Lemma list_sum_app_114 : forall l1 l2,
  zsum_114 (l1 ++ l2) = zsum_114 l1 + zsum_114 l2.
Proof.
  intros l1 l2.
  unfold zsum_114 at 1.
  rewrite fold_left_app.
  rewrite list_sum_acc_114.
  reflexivity.
Qed.

Lemma list_sum_singleton_114 : forall x,
  zsum_114 [x] = x.
Proof.
  intros x. reflexivity.
Qed.

Lemma suffix_of_snoc_decomp_114 : forall (p : list Z) (x : Z) (prefix suffix : list Z),
  suffix <> [] ->
  p ++ [x] = prefix ++ suffix ->
  suffix = [x] \/
  exists suffix_p,
    suffix = suffix_p ++ [x] /\
    suffix_p <> [] /\
    p = prefix ++ suffix_p.
Proof.
  intros p x prefix suffix Hnonempty Heq.
  destruct (exists_last Hnonempty) as [suffix_p [last Hsuffix]].
  subst suffix.
  rewrite app_assoc in Heq.
  pose proof (app_inj_tail p (prefix ++ suffix_p) x last Heq) as [Hp Hlast].
  subst last.
  destruct suffix_p as [|h t].
  - left. reflexivity.
  - right.
    exists (h :: t).
    repeat split; try discriminate; assumption.
Qed.

Lemma subarray_of_snoc_decomp_114 : forall (p : list Z) (x : Z)
  (prefix sub suffix : list Z),
  suffix <> [] ->
  p ++ [x] = prefix ++ sub ++ suffix ->
  exists suffix_p, p = prefix ++ sub ++ suffix_p.
Proof.
  intros p x prefix sub suffix Hnonempty Heq.
  destruct (exists_last Hnonempty) as [suffix_p [last Hsuffix]].
  subst suffix.
  repeat rewrite app_assoc in Heq.
  pose proof (app_inj_tail p ((prefix ++ sub) ++ suffix_p) x last Heq) as [Hp _].
  exists suffix_p.
  rewrite app_assoc.
  exact Hp.
Qed.

Lemma suffix_min_spec_singleton_114 : forall x,
  suffix_min_spec [x] x.
Proof.
  intros x.
  unfold suffix_min_spec.
  split.
  - exists [x], [].
    repeat split; try discriminate; reflexivity.
  - intros suffix prefix Hnonempty Heq.
    destruct (suffix_of_snoc_decomp_114 [] x prefix suffix Hnonempty Heq)
      as [Hsuf | [suffix_p [_ [Hsp_nonempty Hp]]]].
    + subst suffix. rewrite list_sum_singleton_114. lia.
    + destruct prefix; simpl in Hp.
      * subst suffix_p. contradiction.
      * discriminate.
Qed.

Lemma subarray_min_spec_singleton_114 : forall x,
  subarray_min_spec_114 [x] x.
Proof.
  intros x.
  unfold subarray_min_spec_114.
  split.
  - exists [x].
    split; [discriminate|].
    split.
    + exists [], []. reflexivity.
    + reflexivity.
  - intros sub Hnonempty [pre [suf Heq]].
    destruct suf as [|s sh].
    + rewrite app_nil_r in Heq.
      destruct (suffix_of_snoc_decomp_114 [] x pre sub Hnonempty Heq)
        as [Hsub | [sub_p [_ [Hsubp_nonempty Hp]]]].
      * subst sub. rewrite list_sum_singleton_114. lia.
      * destruct pre; simpl in Hp.
        -- subst sub_p. contradiction.
        -- discriminate.
    + assert (Hsuf_nonempty : s :: sh <> []) by discriminate.
      destruct (subarray_of_snoc_decomp_114 [] x pre sub (s :: sh)
                  Hsuf_nonempty Heq) as [suffix_p Hp].
      destruct pre; simpl in Hp.
      * destruct sub; simpl in Hp; [contradiction|discriminate].
      * discriminate.
Qed.

Lemma suffix_min_spec_snoc_114 : forall p x prev cur,
  suffix_min_spec p prev ->
  cur = (if prev <? 0 then prev + x else x) ->
  suffix_min_spec (p ++ [x]) cur.
Proof.
  intros p x prev cur [[old_suffix [old_prefix [Hold_nonempty [Hold_eq Hold_sum]]]]
                       Hold_min] Hcur.
  unfold suffix_min_spec.
  split.
  - destruct (prev <? 0) eqn:Hlt.
    + assert (Hlt_prop : prev < 0) by (apply Z.ltb_lt; exact Hlt).
      exists (old_suffix ++ [x]), old_prefix.
      repeat split.
      * intros Hnil. apply app_eq_nil in Hnil as [_ Hbad]. discriminate.
      * rewrite Hold_eq. rewrite app_assoc. reflexivity.
      * rewrite list_sum_app_114, Hold_sum, list_sum_singleton_114.
        subst cur. reflexivity.
    + exists [x], p.
      split; [discriminate|].
      split; [reflexivity|].
      subst cur. reflexivity.
  - intros suffix prefix Hsuffix_nonempty Heq.
    subst cur.
    destruct (prev <? 0) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      destruct (suffix_of_snoc_decomp_114 p x prefix suffix Hsuffix_nonempty Heq)
        as [Hsuf | [suffix_p [Hsuf [Hsp_nonempty Hp]]]].
      * subst suffix. rewrite list_sum_singleton_114. lia.
      * subst suffix.
        rewrite list_sum_app_114, list_sum_singleton_114.
        pose proof (Hold_min suffix_p prefix Hsp_nonempty Hp).
        lia.
    + apply Z.ltb_ge in Hlt.
      destruct (suffix_of_snoc_decomp_114 p x prefix suffix Hsuffix_nonempty Heq)
        as [Hsuf | [suffix_p [Hsuf [Hsp_nonempty Hp]]]].
      * subst suffix. rewrite list_sum_singleton_114. lia.
      * subst suffix.
        rewrite list_sum_app_114, list_sum_singleton_114.
        pose proof (Hold_min suffix_p prefix Hsp_nonempty Hp).
        lia.
Qed.

Lemma subarray_min_spec_snoc_114 : forall p x prev_min cur_suffix result,
  subarray_min_spec_114 p prev_min ->
  suffix_min_spec (p ++ [x]) cur_suffix ->
  result = (if cur_suffix <? prev_min then cur_suffix else prev_min) ->
  subarray_min_spec_114 (p ++ [x]) result.
Proof.
  intros p x prev_min cur_suffix result Hprev Hsuffix Hresult.
  destruct Hprev as [Hprev_exists Hprev_min].
  destruct Hsuffix as [Hsuffix_exists Hsuffix_min].
  unfold subarray_min_spec_114.
  split.
  - destruct (cur_suffix <? prev_min) eqn:Hlt.
    + destruct Hsuffix_exists as [suffix [prefix [Hnonempty [Heq Hsum]]]].
      exists suffix.
      repeat split; try assumption.
      * exists prefix, []. rewrite app_nil_r. exact Heq.
      * subst result. exact Hsum.
    + destruct Hprev_exists as [sub [Hnonempty [[prefix [suffix Heq]] Hsum]]].
      exists sub.
      repeat split; try assumption.
      * exists prefix, (suffix ++ [x]).
        rewrite Heq. repeat rewrite app_assoc. reflexivity.
      * subst result. exact Hsum.
  - intros sub Hsub_nonempty [prefix [suffix Heq]].
    subst result.
    destruct (cur_suffix <? prev_min) eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      destruct suffix as [|s st].
      * rewrite app_nil_r in Heq.
        pose proof (Hsuffix_min sub prefix Hsub_nonempty Heq).
        lia.
      * assert (Hsuf_nonempty : s :: st <> []) by discriminate.
        destruct (subarray_of_snoc_decomp_114 p x prefix sub (s :: st)
                    Hsuf_nonempty Heq) as [suffix_p Hp].
        pose proof (Hprev_min sub Hsub_nonempty (ex_intro _ prefix (ex_intro _ suffix_p Hp))).
        lia.
    + apply Z.ltb_ge in Hlt.
      destruct suffix as [|s st].
      * rewrite app_nil_r in Heq.
        pose proof (Hsuffix_min sub prefix Hsub_nonempty Heq).
        lia.
      * assert (Hsuf_nonempty : s :: st <> []) by discriminate.
        destruct (subarray_of_snoc_decomp_114 p x prefix sub (s :: st)
                    Hsuf_nonempty Heq) as [suffix_p Hp].
        pose proof (Hprev_min sub Hsub_nonempty (ex_intro _ prefix (ex_intro _ suffix_p Hp))).
        lia.
Qed.

Lemma sublist_snoc_Znth_114 : forall nums i,
  0 <= i < Zlength nums ->
  sublist 0 (i + 1) nums = sublist 0 i nums ++ [Znth i nums 0].
Proof.
  intros nums i Hi.
  rewrite (sublist_split 0 (i + 1) i nums).
  - replace (sublist i (i + 1) nums) with [Znth i nums 0].
    + reflexivity.
    + symmetry. apply sublist_single.
      rewrite <- Zlength_correct. lia.
  - lia.
  - rewrite <- Zlength_correct. lia.
Qed.

Lemma min_prefix_specs_nat_114 : forall n nums,
  (0 < n)%nat ->
  Z.of_nat n <= Zlength nums ->
  suffix_min_spec (sublist 0 (Z.of_nat n) nums)
    (min_suffix_prefix_nat n nums) /\
  subarray_min_spec_114 (sublist 0 (Z.of_nat n) nums)
    (min_subarray_prefix_nat n nums).
Proof.
  induction n as [|n IH]; intros nums Hpos Hlen; [lia|].
  destruct n as [|n].
  - change (Z.of_nat 1) with 1 in *.
    replace (sublist 0 1 nums) with [Znth 0 nums 0].
    2:{ symmetry. apply sublist_single.
        rewrite <- Zlength_correct; lia. }
    split.
    + apply suffix_min_spec_singleton_114.
    + apply subarray_min_spec_singleton_114.
  - assert (Hprev_len : Z.of_nat (S n) <= Zlength nums) by lia.
    specialize (IH nums ltac:(lia) Hprev_len) as [IHsuffix IHsub].
    change (min_suffix_prefix_nat (S (S n)) nums) with
      (let prev := min_suffix_prefix_nat (S n) nums in
       let x := Znth (Z.of_nat (S n)) nums 0 in
       if prev <? 0 then prev + x else x).
    change (min_subarray_prefix_nat (S (S n)) nums) with
      (let prev_min := min_subarray_prefix_nat (S n) nums in
       let cur := min_suffix_prefix_nat (S (S n)) nums in
       if cur <? prev_min then cur else prev_min).
    set (p := sublist 0 (Z.of_nat (S n)) nums).
    set (x := Znth (Z.of_nat (S n)) nums 0).
    assert (Hnext:
      sublist 0 (Z.of_nat (S (S n))) nums = p ++ [x]).
    {
      subst p x.
      replace (Z.of_nat (S (S n))) with (Z.of_nat (S n) + 1) by lia.
      apply sublist_snoc_Znth_114.
      lia.
    }
    rewrite Hnext.
    set (prev := min_suffix_prefix_nat (S n) nums).
    set (cur := if prev <? 0 then prev + x else x).
    assert (Hcur_suffix : suffix_min_spec (p ++ [x]) cur).
    {
      subst cur prev p x.
      apply suffix_min_spec_snoc_114 with
        (prev := min_suffix_prefix_nat (S n) nums);
        try assumption.
      reflexivity.
    }
    split.
    + exact Hcur_suffix.
    + subst cur prev.
      apply subarray_min_spec_snoc_114 with
        (prev_min := min_subarray_prefix_nat (S n) nums)
        (cur_suffix := min_suffix_prefix_nat (S (S n)) nums).
      * subst p. exact IHsub.
      * exact Hcur_suffix.
      * reflexivity.
Qed.

Lemma subarray_min_spec_to_problem_114_spec : forall nums result,
  subarray_min_spec_114 nums result ->
  problem_114_spec nums result.
Proof.
  intros nums result [Hexists Hmin].
  unfold problem_114_spec.
  split.
  - destruct Hexists as [sub_array [Hnonempty [Hsplit Hsum]]].
    exists sub_array.
    split; [assumption|].
    split; [assumption|].
    rewrite list_sum_Z_114_unfold.
    unfold zsum_114 in Hsum.
    exact Hsum.
  - intros sub_array Hnonempty Hsplit.
    rewrite list_sum_Z_114_unfold.
    apply Hmin; assumption.
Qed.

Lemma min_subarray_prefix_correct_114 : forall nums,
  problem_114_pre_z nums ->
  problem_114_spec nums (min_subarray_prefix (Zlength nums) nums).
Proof.
  intros nums Hpre.
  unfold problem_114_pre_z, problem_114_pre in Hpre.
  assert (Hlen_pos : 0 < Zlength nums).
  {
    rewrite Zlength_correct.
    destruct nums; simpl in *; try contradiction; lia.
  }
  pose proof (min_prefix_specs_nat_114 (Z.to_nat (Zlength nums)) nums) as Hspec.
  assert (Hnat_pos : (0 < Z.to_nat (Zlength nums))%nat) by lia.
  assert (Hnat_len : Z.of_nat (Z.to_nat (Zlength nums)) <= Zlength nums) by lia.
  specialize (Hspec Hnat_pos Hnat_len) as [_ Hsub].
  unfold min_subarray_prefix.
  replace (Z.of_nat (Z.to_nat (Zlength nums))) with (Zlength nums) in Hsub by lia.
  rewrite sublist_self in Hsub by lia.
  apply subarray_min_spec_to_problem_114_spec.
  exact Hsub.
Qed.

Lemma problem_114_spec_z_of_min_subarray_prefix : forall nums result,
  problem_114_pre_z nums ->
  result = min_subarray_prefix (Zlength nums) nums ->
  problem_114_spec_z nums result.
Proof.
  intros nums result Hpre Hresult.
  subst result.
  unfold problem_114_spec_z.
  apply min_subarray_prefix_correct_114.
  exact Hpre.
Qed.
