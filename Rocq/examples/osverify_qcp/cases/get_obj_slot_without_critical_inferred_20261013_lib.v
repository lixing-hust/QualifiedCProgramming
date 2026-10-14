Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
From compcert.lib Require Import Integers.
Import ListNotations.
Import naive_C_Rules.
Definition gos_heap : Type := naive_C_Rules.model.
Local Open Scope string_scope.
Open Scope Z_scope.

(* The finite list is exactly the observed object-pointer prefix, beginning
   at source constant OBJ_POSITION = 17. It does not model unread slots. *)
Definition gos_nth (xs : list Z) (i : Z) : Z :=
  nth (Z.to_nat (i - 17)) xs 0.
Definition gos_limit (xs : list Z) : Z := 17 + Z.of_nat (List.length xs).
Definition gos_no_match (xs : list Z) (f upto : Z) : Prop :=
  forall j, 17 <= j < upto -> gos_nth xs j <> f.
Definition gos_first_match (xs : list Z) (e f r : Z) : Prop :=
  17 <= r < e /\ r < 255 /\ gos_limit xs = r + 1 /\
  gos_nth xs r = f /\ gos_no_match xs f r.
Definition gos_exhausted (xs : list Z) (e f : Z) : Prop :=
  (e <= 17 /\ xs = []) \/
  (17 < e <= 255 /\ gos_limit xs = e /\ gos_no_match xs f e).
Definition gos_search_result (xs : list Z) (e f r : Z) : Prop :=
  gos_first_match xs e f r \/ (r = 0 /\ gos_exhausted xs e f).
Definition gos_result (prio p e f : Z) (xs : list Z) (r : Z) : Prop :=
  (63 <= prio /\ r = 42) \/
  (prio < 63 /\ p = 0 /\ r = 0) \/
  (prio < 63 /\ p <> 0 /\ gos_search_result xs e f r).
Definition gos_safe_observation (xs : list Z) (e f : Z) : Prop :=
  gos_exhausted xs e f \/ exists r, gos_first_match xs e f r.

(* The initial snapshot remains literal model equality.  The post-state is
   compared at the concrete byte level: raw Z representatives modulo 256
   denote the same physical byte.  Permission/initialization and generic
   logical state are preserved, not quotiented away. *)
Definition gos_exact (h : gos_heap) : Assertion := fun m => m = h.
Definition gos_cell_equiv (x y : mem_var) : Prop :=
  match x, y with
  | Noperm, Noperm => True
  | Noninit, Noninit => True
  | value b, value c => Byte.eqm b c
  | _, _ => False
  end.
Definition gos_heap_equiv (m h : gos_heap) : Prop :=
  (forall a, gos_cell_equiv (ConAssertion.s_mem m a) (ConAssertion.s_mem h a)) /\
  ConAssertion.s_STS m = ConAssertion.s_STS h /\
  ConAssertion.s_token m = ConAssertion.s_token h.
Definition gos_preserved (h : gos_heap) : Assertion :=
  fun m => gos_heap_equiv m h.
Definition gos_read_uint (h : gos_heap) (a v : Z) : Prop :=
  (store_uint a v ** TT)%sac h.
Definition gos_read_ptr (h : gos_heap) (a v : Z) : Prop :=
  (store_ptr a v ** TT)%sac h.
Definition gos_restore_uint (h : gos_heap) (a v : Z) : Assertion :=
  (store_uint a v -* gos_preserved h)%sac.
Definition gos_restore_ptr (h : gos_heap) (a v : Z) : Assertion :=
  (store_ptr a v -* gos_preserved h)%sac.

Definition gos_object_addr (p i : Z) : Z :=
  let slots_base : Z := &(p # "cspace" ->ₛ "cnode" .ₛ "slots") in
  let slot_base : Z := slots_base + i * sizeof("slot") in
  &(slot_base # "slot" ->ₛ "capability" .ₛ "cap_content" .ₛ "object" .ₛ "object_t").
Definition gos_objects (h : gos_heap) (p : Z) (xs : list Z) : Prop :=
  forall j, 17 <= j < gos_limit xs ->
    gos_read_ptr h (gos_object_addr p j) (gos_nth xs j).

(* The two base addresses are the declared global arrays. A valid-priority
   invocation observes the bound first even on the null-pointer path.
   Conjunctions here are ordinary propositions about ONE heap: equal read
   addresses are permitted if their typed values are consistent. *)
Definition gos_input (h : gos_heap) (prio bp tp p e f : Z) (xs : list Z) : Prop :=
  0 <= prio <= 255 /\
  (63 <= prio \/
   (prio < 63 /\ 0 <= e <= 4294967295 /\
    gos_read_uint h (bp + 4 * prio) e /\
    gos_read_ptr h (tp + ptr_size_Z * prio) p /\
    ((p = 0 /\ xs = []) \/
     (p <> 0 /\ gos_safe_observation xs e f /\ gos_objects h p xs)))).

Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality Coq.Logic.PropExtensionality Coq.micromega.Lia.
Lemma gos_frontier_bound__search_step : forall xs e f i,
  gos_safe_observation xs e f -> gos_no_match xs f i ->
  17 <= i -> i < e -> i < gos_limit xs.
Proof.
  intros xs e f i Hsafe Hnone Hlo Hlt.
  destruct Hsafe as [[[He Hnil] | [He [Hlim Hdone]]] | [r Hr]].
  - lia.
  - lia.
  - destruct Hr as [Hr [H255 [Hlim [Hhit Hbefore]]]].
    destruct (Z_lt_ge_dec r i) as [Hri | Hri].
    + exfalso. apply (Hnone r); [lia | exact Hhit].
    + lia.
Qed.
Lemma gos_cell_refl__read_extract : forall x, gos_cell_equiv x x.
Proof. destruct x; simpl; auto using Byte.eqm_refl. Qed.
Lemma gos_cell_sym__read_extract : forall x y, gos_cell_equiv x y -> gos_cell_equiv y x.
Proof. destruct x,y; simpl; auto using Byte.eqm_sym. Qed.
Lemma gos_cell_trans__read_extract : forall x y z,
 gos_cell_equiv x y -> gos_cell_equiv y z -> gos_cell_equiv x z.
Proof. destruct x,y,z; simpl; intuition eauto using Byte.eqm_trans. Qed.
Lemma gos_equiv_refl__read_extract : forall m, gos_heap_equiv m m.
Proof. intro; repeat split; auto using gos_cell_refl__read_extract. Qed.
Lemma gos_equiv_sym__read_extract : forall m h, gos_heap_equiv m h -> gos_heap_equiv h m.
Proof. intros m h [H [HS HT]]; repeat split; auto using gos_cell_sym__read_extract. Qed.
Lemma gos_equiv_trans__read_extract : forall m h k,
 gos_heap_equiv m h -> gos_heap_equiv h k -> gos_heap_equiv m k.
Proof. intros m h k [H [HS HT]] [J [JS JT]]; repeat split; try congruence.
 intro a; eapply gos_cell_trans__read_extract; eauto. Qed.
Lemma gos_join_equiv__read_extract : forall a b m a' b' m',
 state_join a b m -> state_join a' b' m' ->
 gos_heap_equiv a a' -> gos_heap_equiv b b' -> gos_heap_equiv m m'.
Proof.
 intros a b m a' b' m' [J [T S]] [J' [T' S']] [E [ES ET]] [F [FS FT]].
 split.
 - intro x. specialize (J x); specialize (J' x); specialize (E x); specialize (F x).
   unfold gos_cell_equiv in *.
   destruct J as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
   destruct J' as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[w [? [? ?]]]|[w [? [? ?]]]]]]];
   repeat match goal with H : ?x = _ |- _ => rewrite H in *; clear H end; simpl in *; tauto.
 - split.
   + unfold STS_state_join in *. rewrite ES, FS in S. apply functional_extensionality; intro x; apply propositional_extensionality; specialize (S x); specialize (S' x); tauto.
   + unfold TokenSet_join in *. rewrite ET, FT in T. apply functional_extensionality; intro x; apply propositional_extensionality; destruct T as [T _]; destruct T' as [T' _]; specialize (T x); specialize (T' x); tauto.
Qed.
Lemma gos_split_equiv__read_extract : forall a b h m,
 state_join a b h -> gos_heap_equiv m h ->
 exists a' b', state_join a' b' m /\ gos_heap_equiv a' a /\ gos_heap_equiv b' b.
Proof.
 intros a b h m [J [T S]] [E [ES ET]].
 exists (mk_Lstate (fun x => match s_mem a x with Noperm => Noperm | _ => s_mem m x end) (s_STS a) (s_token a)).
 exists (mk_Lstate (fun x => match s_mem b x with Noperm => Noperm | _ => s_mem m x end) (s_STS b) (s_token b)).
 split.
 - split.
   + intro x; specialize (J x); specialize (E x); simpl.
     destruct J as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
     repeat match goal with H : ?x = _ |- _ => rewrite H in *; clear H end;
     destruct (s_mem m x); simpl in E; try contradiction; simpl; unfold mem_join; eauto 10.
   + simpl; rewrite ES, ET; auto.
 - split; split; try (split; reflexivity); intro x; specialize (J x); specialize (E x); simpl;
   destruct J as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
   repeat match goal with H : ?x = _ |- _ => rewrite H in *; clear H end; simpl; auto.
Qed.
Lemma gos_mstore_transport__read_extract : forall a v m h,
 gos_heap_equiv m h -> mstore a v h -> mstore a v m.
Proof.
 intros a v m h [E [ES ET]] [w [V [M [S T]]]].
 specialize (E a) as Ea; rewrite M in Ea; unfold single_byte_mem, addr_eqb in Ea; rewrite Z.eqb_refl in Ea.
 destruct (s_mem m a) as [| |w'] eqn:W; simpl in Ea; try contradiction.
 exists w'; split.
 - eapply Byte.eqm_trans; [exact V|apply Byte.eqm_sym;exact Ea].
 - split.
   + apply functional_extensionality; intro x. unfold single_byte_mem, addr_eqb.
     destruct (Z.eqb x a) eqn:X.
     * apply Z.eqb_eq in X; subst; exact W.
     * specialize (E x). rewrite M in E. unfold single_byte_mem, addr_eqb in E; rewrite X in E.
       destruct (s_mem m x); simpl in E; tauto.
   + rewrite ES, ET; auto.
Qed.
Lemma gos_sep_transport__read_extract : forall (P Q : Assertion),
 (forall m h, gos_heap_equiv m h -> P h -> P m) ->
 (forall m h, gos_heap_equiv m h -> Q h -> Q m) ->
 forall m h, gos_heap_equiv m h -> (P ** Q)%sac h -> (P ** Q)%sac m.
Proof.
 intros P Q HP HQ m h E [a [b [J [PA QB]]]].
 destruct (gos_split_equiv__read_extract a b h m J E) as [a' [b' [J' [EA EB]]]].
 exists a', b'; split; [exact J'|]; split; [eapply HP|eapply HQ]; eauto.
Qed.
Lemma gos_store4_transport__read_extract : forall a v m h,
 gos_heap_equiv m h -> store_4byte a v h -> store_4byte a v m.
Proof.
 intros a v m h E [v1 [v2 [v3 [v4 [V B]]]]].
 exists v1,v2,v3,v4; split; [exact V|].
 eapply gos_sep_transport__read_extract; [apply gos_mstore_transport__read_extract| |exact E|exact B].
 apply gos_sep_transport__read_extract; [apply gos_mstore_transport__read_extract|].
 apply gos_sep_transport__read_extract; apply gos_mstore_transport__read_extract.
Qed.
Lemma gos_mstore_unique__read_extract : forall a v w m h,
 Byte.eqm v w -> mstore a v m -> mstore a w h -> gos_heap_equiv m h.
Proof.
 intros a v w m h VW [b [VB [M [S T]]]] [c [WC [N [S' T']]]].
 split.
 - intro x; rewrite M,N; unfold single_byte_mem, addr_eqb; destruct (Z.eqb x a); simpl; auto.
   eapply Byte.eqm_trans; [apply Byte.eqm_sym;exact VB|].
   eapply Byte.eqm_trans; [exact VW|exact WC].
 - split; apply functional_extensionality; intro x; apply propositional_extensionality.
   + specialize (S x); specialize (S' x); tauto.
   + specialize (T x); specialize (T' x); tauto.
Qed.
Lemma gos_sep_unique__read_extract : forall (P P' Q Q' : Assertion),
 (forall m h, P m -> P' h -> gos_heap_equiv m h) ->
 (forall m h, Q m -> Q' h -> gos_heap_equiv m h) ->
 forall m h, (P ** Q)%sac m -> (P' ** Q')%sac h -> gos_heap_equiv m h.
Proof.
 intros P P' Q Q' HP HQ m h [a [b [J [PA QB]]]] [a' [b' [J' [PA' QB']]]].
 eapply gos_join_equiv__read_extract; eauto.
Qed.
Lemma gos_merge4_unique__read_extract : forall a b c d a' b' c' d' v,
 merge_int a b c d v -> merge_int a' b' c' d' v ->
 Byte.eqm a a' /\ Byte.eqm b b' /\ Byte.eqm c c' /\ Byte.eqm d d'.
Proof.
 intros a b c d a' b' c' d' v H H'.
 unfold merge_int, CArch.BigEndian.merge_int in *.
 change (v mod 4294967296 = a mod 256 * 16777216 + b mod 256 * 65536 + c mod 256 * 256 + d mod 256) in H.
 change (v mod 4294967296 = a' mod 256 * 16777216 + b' mod 256 * 65536 + c' mod 256 * 256 + d' mod 256) in H'.
 pose proof (Z.mod_pos_bound a 256 ltac:(lia)); pose proof (Z.mod_pos_bound b 256 ltac:(lia));
 pose proof (Z.mod_pos_bound c 256 ltac:(lia)); pose proof (Z.mod_pos_bound d 256 ltac:(lia));
 pose proof (Z.mod_pos_bound a' 256 ltac:(lia)); pose proof (Z.mod_pos_bound b' 256 ltac:(lia));
 pose proof (Z.mod_pos_bound c' 256 ltac:(lia)); pose proof (Z.mod_pos_bound d' 256 ltac:(lia)).
 repeat split; apply eqm_iff_mod_eq; lia.
Qed.
Lemma gos_store4_unique__read_extract : forall a v m h,
 store_4byte a v m -> store_4byte a v h -> gos_heap_equiv m h.
Proof.
 intros a v m h [v1 [v2 [v3 [v4 [V B]]]]] [w1 [w2 [w3 [w4 [W C]]]]].
 destruct (gos_merge4_unique__read_extract _ _ _ _ _ _ _ _ _ V W) as [E1 [E2 [E3 E4]]].
 eapply gos_sep_unique__read_extract; [| |exact B|exact C].
 - intros m' h'; exact (gos_mstore_unique__read_extract a v1 w1 _ _ E1).
 - eapply gos_sep_unique__read_extract.
   + intros m' h'; exact (gos_mstore_unique__read_extract (a+1) v2 w2 _ _ E2).
   + eapply gos_sep_unique__read_extract.
     * intros m' h'; exact (gos_mstore_unique__read_extract (a+2) v3 w3 _ _ E3).
     * intros m' h'; exact (gos_mstore_unique__read_extract (a+3) v4 w4 _ _ E4).
Qed.
Lemma gos_extract__read_extract : forall (P : Assertion),
 (forall m h, gos_heap_equiv m h -> P h -> P m) ->
 (forall m h, P m -> P h -> gos_heap_equiv m h) ->
 forall h, (P ** TT)%sac h -> (gos_preserved h |-- P ** (P -* gos_preserved h))%sac.
Proof.
 intros P HP HU h [a [b [J [PA _]]]] m E.
 destruct (gos_split_equiv__read_extract a b h m J E) as [a' [b' [J' [EA EB]]]].
 assert (PA' : P a') by (eapply HP; eauto).
 exists a',b'; split; [exact J'|]. split; [exact PA'|].
 intros c k K PC.
 eapply gos_equiv_trans__read_extract; [|exact E].
 eapply gos_join_equiv__read_extract with (a:=c) (b:=b') (a':=a') (b':=b').
 - apply join_comm; exact K.
 - exact J'.
 - apply HU; auto.
 - apply gos_equiv_refl__read_extract.
Qed.
Lemma gos_read_uint_extract__read_extract : forall h a v,
 gos_read_uint h a v ->
 (gos_preserved h |-- store_uint a v ** gos_restore_uint h a v)%sac.
Proof.
 intros h a v H; apply gos_extract__read_extract; [| |exact H].
 - intros m k E [V B]; split; [exact V|]. eapply gos_store4_transport__read_extract; eauto.
 - intros m k [_ B] [_ C]; eapply gos_store4_unique__read_extract; eauto.
Qed.
Lemma gos_read_ptr_extract__read_extract : forall h a v,
 gos_read_ptr h a v ->
 (gos_preserved h |-- store_ptr a v ** gos_restore_ptr h a v)%sac.
Proof.
 intros h a v H; apply gos_extract__read_extract; [| |exact H].
 - intros m k E [V B]; split; [exact V|]. change (store_4byte a v m).
   change (store_4byte a v k) in B. eapply gos_store4_transport__read_extract; eauto.
 - intros m k [_ B] [_ C]; change (store_4byte a v m) in B; change (store_4byte a v k) in C.
   eapply gos_store4_unique__read_extract; eauto.
Qed.
