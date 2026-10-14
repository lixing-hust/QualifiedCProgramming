Require Import include_frm.
Require Import base_tac.
Require Import os_inv.
Require Import os_code_defs.
Require Import abs_op.
Require Import sep_auto.
Require Import Maps.

Require Import mem_join_lemmas.
Require Import lemmas_for_inv_prop.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
(* lemmas specific on memory(HalfPermMap) *)


Lemma mem_sub_sig_eq :
  forall l a b p (m:mem),
    sub (sig l (p, a)) m ->
    sub (sig l (p, b)) m ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H, H0.
  eapply mem_join_sig_eq; eauto.
Qed.

Ltac destruct_get :=
  let a := fresh in
  match goal with
  | H : (match ?X with | Some _ => _ | None => _ end) |- _ => destruct X eqn : a; tryfalse; destruct_get
  | _ => idtac
  end.

Lemma osabst_join_sig_eq :
  forall l a b (o:osabst) o1 o2,
    join (sig l a) o1 o ->
    join (sig l b) o2 o ->
    a = b.
Proof.
  intros.
  pose proof H l.
  pose proof H0 l.
  rewrite OSAbstMod.get_sig_some in *.
  destruct_get.
  substs; auto.
Qed.

Lemma osabst_sub_sig_eq :
  forall l a b (o:osabst),
    sub (sig l a) o ->
    sub (sig l b) o ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H, H0.
  eapply osabst_join_sig_eq; eauto.
Qed.

Lemma mem_join_sig_sub_eq :
  forall a b l p m1 m1' m2 m2' (m:mem),
    join (sig l (p, a)) m1 m2 ->
    join (sig l (p, b)) m1' m2' ->
    sub m2 m -> sub m2' m ->
    a = b.
Proof.
  unfold sub; intros.
  destruct H1, H2.
  lets Hx1: HalfPermMap.map_join_assoc H H1.
  lets Hx2: HalfPermMap.map_join_assoc H0 H2.
  destruct Hx1; destruct H3.
  destruct Hx2; destruct H5.
  lets Hx: mem_join_sig_eq H3 H5; auto.
Qed.
(* end *)

(* lemmas on PermMap *)
Lemma join_sub_l {A B T:Type} {MC: PermMap A B T} :
  forall m1 m2 m,
    join m1 m2 m -> sub m1 m.
Proof.
  intros.
  unfold sub.
  eexists; eauto.
Qed.

Lemma join_sub_r {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m,
    join m1 m2 m -> sub m2 m.
Proof.
  intros.
  unfold sub.
  eexists.
  apply map_join_comm in H; eauto.
Qed.

Lemma sub_trans {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m3,
    sub m1 m2 -> sub m2 m3 -> sub m1 m3.
Proof.
  unfold sub; intros.
  geat.
Qed.

Lemma join_unique {A B T: Type} {MC: PermMap A B T} :
  forall m1 m2 m m',
    join m1 m2 m -> join m1 m2 m' -> m = m'.
Proof.
  intros.
  geat.
Qed.

Lemma eq_join_eq {A B T: Type} {MC: PermMap A B T} :
  forall m1 m1' m2 m2' M M',
    join m1 m2 M ->
    join m1' m2' M' ->
    m1 = m1' -> m2 = m2' ->
    M = M'.
Proof.
  intros; substs.
  eapply join_unique; eauto.
Qed.
(* end *)

(*--- auxiliary lemmas ------*)
Lemma sat_sep_conj_elim1 :
  forall e e0 M i ier l O a P Q,
    (e, e0, M, i, ier, l, O, a) |= P ** Q ->
    exists M1 M2 O1 O2, join M1 M2 M /\ join O1 O2 O /\
                        (e, e0, M1, i, ier, l, O1, a) |= P /\
                        (e, e0, M2, i, ier, l, O2, a) |= Q. 
Proof.
  intros.
  simpl in H; simpljoin.
  do 4 eexists; repeat (split; eauto).
Qed.

Lemma isptr_ecbf_sll :
  forall s head eventl t next,
    s |= ecbf_sll head eventl  t next -> isptr head.
Proof.
  intros.
  unfold ecbf_sll in H.
  destruct eventl.
  simpl in H; simpljoin.
  unfolds; auto.
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  destruct_s s.
  simpl in H; simpljoin.
  unfolds; right.
  eauto.
Qed.

Lemma isptr_ecbf_sllseg :
  forall s head eventl t next,
    s |= ecbf_sllseg head Vnull eventl t next -> isptr head.
Proof.
  intros.
  unfold ecbf_sllseg in H.
  destruct eventl.
  simpl in H; simpljoin.
  unfolds; auto.
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  destruct_s s.
  simpl in H; simpljoin.
  unfolds; right.
  eauto.
Qed.

Lemma sll_isptr :
  forall vl s head t next,
    s |= sll head vl t next -> isptr head.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin; unfolds; auto.
  simpl in H; simpljoin.
  unfolds; right; eauto.
Qed.

Lemma qblkf_sll_isptr :
  forall qblkl head t next s,
    s |= qblkf_sll head qblkl t next -> isptr head.
Proof.
  inductions qblkl; intros.
  simpl in H; simpljoin; unfolds; auto.
  simpl in H; simpljoin; unfolds; right; eauto.
Qed.

Lemma evsllseg_isptr :
  forall ectrl head msgql s,
    s |= evsllseg head Vnull ectrl msgql -> isptr head.
Proof.
  inductions ectrl; intros.
  simpl in H; simpljoin; unfolds; auto.
  simpl in H; destruct a; destruct msgql; tryfalse; destruct p; simpl in H; simpljoin.
  unfolds; right; eauto.
Qed.

Lemma qblkfsllseg_head_isptr:
  forall l v1   t  n  P s, s |= qblkf_sllseg
                                    v1 Vnull  l t n  ** P  -> isptr v1. 
Proof.
  inductions l ; intros; simpl in *; tryfalse;  simpljoin; 
   unfolds; simpl; eauto.
Qed.

Lemma qblkfsll_head_isptr : forall v l  t n P s, s |= qblkf_sll
                                                   v l  t n ** P  -> isptr v.
Proof.
  unfold qblkf_sll.
  intros.
  eapply  qblkfsllseg_head_isptr.
  eauto.
Qed.

Lemma ecbfsllseg_head_isptr:
  forall l v1   t  n  P s, s |= ecbf_sllseg
                                    v1 Vnull  l t n  ** P  -> isptr v1. 
Proof.
  inductions l ; intros; simpl in *; tryfalse; simpljoin; 
  unfolds; simpl; eauto.
Qed.

Lemma ecbfsll_head_isptr : forall v l  t n P s, s |= ecbf_sll
                                                   v l  t n ** P  -> isptr v.
Proof.
  unfold ecbf_sll.
  intros.
  eapply ecbfsllseg_head_isptr.
  eauto.
Qed.

Lemma  evsllseg_head_isptr : forall  s head l x P, 
                                s|= evsllseg head Vnull l x ** P  -> 
                                isptr head.
Proof.
  introv Hsat.
  destruct l; simpl evsllseg in *.
  sep split in Hsat.
  simpljoin.
  subst; unfolds; auto.
  destruct x.
  simpl in Hsat; tryfalse.
  sep destruct  Hsat.
  sep split in Hsat.
  simpljoin.
  tryfalse.
  destruct e.
  destruct p.
  unfold AEventNode in Hsat.
  destruct e0. 
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  sep destroy Hsat.
  simpljoin.
  unfolds; auto.
  right.
  eexists; eauto.
Qed.
(* end *)

Require Import join_lib.

(* tactics *)
Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1

    | H: emposabst _ |- _ => unfold emposabst in H; subst; simpl_map1

    | H:join empenv _ _ |- _ => apply map_join_comm in H; apply map_join_emp' in H; subst; simpl_map1
    | H:join _ empenv _
      |- _ =>
      apply map_join_emp' in H; subst; simpl_map1
    | |- join empenv _ _ => apply map_join_comm; apply map_join_emp; simpl_map1
    | |- join _ empenv _ => apply map_join_emp; simpl_map1
    | H:join ?a ?b ?ab |- join ?b ?a ?ab => apply map_join_comm; auto
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | |- join _ ?a ?a => apply map_join_comm; simpl_map1
    | |- join ?a _ ?a => apply map_join_emp; simpl_map1
    | |- empenv = _ => reflexivity; simpl_map1
    | |- _ = empenv => reflexivity; simpl_map1
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Ltac mem_join_sub_solver :=
  match goal with
    | H: join ?m _ ?X |- sub ?m ?M =>
      apply join_sub_l in H; apply sub_trans with (m2:=X); auto; mem_join_sub_solver
    | H: join _ ?m ?X |- sub ?m ?M =>
      apply join_sub_r in H; apply sub_trans with (m2:=X); auto; mem_join_sub_solver
  end.

Ltac elim_sep_conj1 H head_H:= let a := fresh in apply sat_sep_conj_elim1 in H; do 4 destruct H; destruct H as [a H]; let b := fresh in destruct H as [b H]; let c := fresh in destruct H as [head_H H].

Ltac mem_sig_eq_solver M := let Hx:= fresh in
  match goal with
    | |- sig ?l1 (?p, ?v1) = sig ?l2 (?p, ?v2) =>
      assert(sub (sig l1 (p, v1)) M) as _H1 by mem_join_sub_solver;
        assert(sub (sig l2 (p, v2)) M) as _H2 by mem_join_sub_solver;
        lets Hx: mem_sub_sig_eq _H1 _H2; rewrite Hx; auto
  end.

Ltac mem_eq_solver1 M :=
  eapply eq_join_eq; eauto; [mem_sig_eq_solver M |try (mem_eq_solver1 M)]; mem_sig_eq_solver M.

Ltac mem_eq_solver2 :=
  match goal with
  | H1: join ?m1 ?m2 ?M1, H2: join ?m3 ?m4 ?M2 |- ?M1 = ?M2 =>
    eapply eq_join_eq; eauto; mem_eq_solver2
  | _ => idtac
  end.

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Ltac mem_eq_solver' MM :=
  eapply eq_join_eq; eauto;[
    match goal with
      | H: forall M : mem, sub ?m1 M -> sub ?m2 M -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (M:= MM)
    end;  mem_join_sub_solver | try (mem_eq_solver' MM)].

Ltac mem_eq_solver MM := try (mem_eq_solver' MM);
    match goal with
      | H: forall M : mem, sub ?m1 M -> sub ?m2 M -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (M:= MM)
    end;  mem_join_sub_solver.

(*
Ltac osabst_join_sub_solver :=
  match goal with
    | H: OSAbstMod.join ?m _ ?X |- OSAbstMod.sub ?m ?M =>
      apply OSAbstMod.join_sub_l in H; apply OSAbstMod.sub_trans with (m2:=X); auto; osabst_join_sub_solver
    | H: OSAbstMod.join _ ?m ?X |- OSAbstMod.sub ?m ?M =>
      apply OSAbstMod.join_sub_r in H; apply OSAbstMod.sub_trans with (m2:=X); auto; osabst_join_sub_solver
  end.
 *)

Ltac osabst_eq_solver' OO :=
  eapply eq_join_eq; eauto;[
    match goal with
      | H: forall o0 : osabst, sub ?m1 o0 -> sub ?m2 o0 -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (o0:= OO)
    end;  mem_join_sub_solver | try (osabst_eq_solver' OO)].

Ltac osabst_eq_solver OO := try (osabst_eq_solver' OO);
    match goal with
      | H: forall o0 : osabst, sub ?m1 o0 -> sub ?m2 o0 -> ?m1 = ?m2 |- ?m1 = ?m2 => apply H with (o0:=OO)
    end;  mem_join_sub_solver.

Ltac un_eq_event_type_solver :=
  match goal with
    | H1: Some _ = Some _ , H2: Some _ = Some _ |- _ =>
      rewrite H1 in H2; inverts H2
  end.

(* end *)
 
Lemma sat_star: 
  forall s p q,
  s |= p ** q ->
  exists  M1 M2 M o1 o2 o , 
                             M = getmem s /\  join M1 M2 M
                            /\ o = getabst s /\ join o1 o2 o
                           /\ sat (substmo s  M1 o1) p
                           /\ sat (substmo s  M2 o2) q .
Proof.
  intros.
  unfold sat in H. fold sat in H.  eauto.
Qed.






(*lemmas*)
Lemma mapstoval_true_vptr_eq :
  forall l a x x' m m' M,
    mapstoval l (Tptr a) true (Vptr x) m -> mapstoval l (Tptr a) true (Vptr x') m' ->
    sub m M -> sub m' M ->
    x = x' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H1, H2; destruct x, x'; simpl in H3, H4; destruct l; simpljoin1.
  unfold ptomval in *; substs.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (true, Pointer b i 0)) M).
  mem_join_sub_solver.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (true, Pointer b0 i0 0)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H3 H5; inverts Hx.
  split; auto.
  clear H5 H3.
  repeat (eapply eq_join_eq; eauto).
Qed.

Lemma mapstoval_false_vptr_eq :
  forall l a x x' m m' M,
    mapstoval l (Tptr a) false (Vptr x) m -> mapstoval l (Tptr a) false (Vptr x') m' ->
    sub m M -> sub m' M ->
    x = x' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H1, H2; destruct x, x'; simpl in H3, H4; destruct l; simpljoin1.
  unfold ptomval in *; substs.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (false, Pointer b i 0)) M).
  mem_join_sub_solver.
  assert(sub (sig (b1, (o + 1 + 1 + 1)%Z) (false, Pointer b0 i0 0)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H3 H5; inverts Hx.
  split; auto.
  clear H5 H3.
  repeat (eapply eq_join_eq; eauto).
Qed.

Lemma ptomvallist_true_mem_eq :
  forall vl l m m' M,
    sub m M -> sub m' M ->
    ptomvallist l true vl m -> ptomvallist l true vl m' ->
    m = m'.
Proof.
  inductions vl; intros.
  simpl in H1, H2; substs; auto.
  simpl in H1, H2; destruct l; simpljoin1.
  unfold ptomval in H3, H5; substs.
  eapply eq_join_eq; eauto.
  eapply IHvl with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma ptomvallist_false_mem_eq :
  forall vl l m m' M,
    sub m M -> sub m' M ->
    ptomvallist l false vl m -> ptomvallist l false vl m' ->
    m = m'.
Proof.
  inductions vl; intros.
  simpl in H1, H2; substs; auto.
  simpl in H1, H2; destruct l; simpljoin1.
  unfold ptomval in H3, H5; substs.
  eapply eq_join_eq; eauto.
  eapply IHvl with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma mapstoval_true_mem_eq :
  forall l t v v' m m' M,
    sub m M -> sub m' M ->
    mapstoval l t true v m -> mapstoval l t true v' m' -> m = m'.
Proof.
  unfold mapstoval; intros; destruct l; simpljoin1.
  destruct t, v, v'; try (destruct a); try(destruct a0); simpl in H3, H4;
  unfold ptomval in H3, H4; simpljoin1;
  try solve [repeat (eapply eq_join_eq; eauto)];
  try solve [lets Hx: mem_join_sig_sub_eq H1 H2 H H0; tryfalse];
  try solve [lets Hx: mem_sub_sig_eq H H0; tryfalse];
  try solve [mem_eq_solver1 M];
  try solve [eapply ptomvallist_true_mem_eq; eauto].
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
Qed.

Lemma mapstoval_false_mem_eq :
  forall l t v v' m m' M,
    sub m M -> sub m' M ->
    mapstoval l t false v m -> mapstoval l t false v' m' -> m = m'.
Proof. 
  unfold mapstoval; intros; destruct l; simpljoin1.
  destruct t, v, v'; try (destruct a); try(destruct a0); simpl in H3, H4;
  unfold ptomval in H3, H4; simpljoin1;
  try solve [repeat (eapply eq_join_eq; eauto)];
  try solve [lets Hx: mem_join_sig_sub_eq H1 H2 H H0; tryfalse];
  try solve [lets Hx: mem_sub_sig_eq H H0; tryfalse];
  try solve [mem_eq_solver1 M];
  try solve [eapply ptomvallist_false_mem_eq; eauto].
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
  lets Hx: mem_sub_sig_eq H H0; rewrite Hx; auto.
Qed.

Fixpoint struct_atom_val_eq' (vl vl':vallist) (d:decllist) :=
  match vl with
    | nil =>
      match vl' with
        | nil => True
        | _ :: _ => False
      end
    | v1 :: t1 =>
      match vl' with
        | nil => False
        | v2 :: t2 =>
          match d with
            | dnil => False
            | dcons id (Tstruct _ _) td => struct_atom_val_eq' t1 t2 td
            | dcons id (Tunion _ _) td => struct_atom_val_eq' t1 t2 td
            | dcons id (Tarray _ _) td => struct_atom_val_eq' t1 t2 td
            | dcons id _ td => v1 = v2 /\ struct_atom_val_eq' t1 t2 td
          end
      end
  end.

Definition struct_atom_val_eq vl vl' t :=
  match t with
    | Tstruct id dl => struct_atom_val_eq' vl vl' dl
    | _ => False
  end.

Local Open Scope Z_scope.
Lemma ptomvallist_true_sub_vl_eq :
  forall vl1 vl2 l m1 m2 m,
    ptomvallist l true vl1 m1 ->
    ptomvallist l true vl2 m2 ->
    length vl1 = length vl2 ->
    sub m1 m -> sub m2 m ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.
  
  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H6.

  unfold ptomval in H1, H6; substs.
  assert(a = m0).
  unfolds in H2; destruct H2.
  unfolds in H3; destruct H3.
  lets Hx1: HalfPermMap.map_join_assoc H H1.
  lets Hx2: HalfPermMap.map_join_assoc H0 H2.
  simpljoin.
  lets Hx: mem_join_sig_eq H6 H3; auto.
  substs.
  assert(vl1 = vl2).
  assert(sub x0 m).
  unfold sub.
  unfold sub in H2.
  geat.
  assert(sub x2 m).
  unfold sub.
  unfold sub in H3.
  geat.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma ptomvallist_false_sub_vl_eq :
  forall vl1 vl2 l m1 m2 m,
    ptomvallist l false vl1 m1 ->
    ptomvallist l false vl2 m2 ->
    length vl1 = length vl2 ->
    sub m1 m -> sub m2 m ->
    vl1 = vl2.
Proof.
  inductions vl1; intros.
  destruct vl2; auto.
  simpl in H1; inversion H1.
  
  destruct vl2.
  simpl in H1; inversion H1.

  simpl in H1; inverts H1.
  simpl in H; destruct l.

  do 3 destruct H; destruct H1.
  simpl in H0; do 3 destruct H0; destruct H6.

  unfold ptomval in H1, H6; substs.
  assert(a = m0).
  unfolds in H2; destruct H2.
  unfolds in H3; destruct H3.
  lets Hx1: HalfPermMap.map_join_assoc H H1.
  lets Hx2: HalfPermMap.map_join_assoc H0 H2.
  simpljoin.
  lets Hx: mem_join_sig_eq H6 H3; auto.
  substs.
  assert(vl1 = vl2).
  assert(sub x0 m).
  unfold sub.
  unfold sub in H2.
  geat.
  assert(sub x2 m).
  unfold sub.
  unfold sub in H3.
  geat.
  apply IHvl1 with (m1:=x0) (m2:=x2) (m:=m) (l:=(b,o+1)); auto.
  substs; auto.
Qed.

Lemma mapstoval_true_rule_type_val_match_eq :
  forall l t v v' m m' M,
    rule_type_val_match t v = true -> rule_type_val_match t v' = true ->
    mapstoval l t true v m -> mapstoval l t true v' m' ->
    sub m M -> sub m' M ->
    v = v' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H1, H2; simpljoin1.
  destruct t; destruct v; destruct v'; simpl in H, H0; tryfalse;
   simpl encode_val in H5, H6;
  (match goal with
  | |- Vptr _ = Vptr _ /\ _ => try destruct a; try destruct a0
  | |- Vptr _ = _ /\ _ => try destruct a
  | |- _ = Vptr _ /\ _ => try destruct a
  | |- _ => idtac
  end);
  try solve [split; auto; eapply ptomvallist_true_mem_eq; eauto];
  try solve [lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; [simpl; auto | inverts Hx]].

  assert(i = i0).
  simpl in H5, H6; destruct l; unfold ptomval in *; simpljoin1.
  lets Hx: mem_sub_sig_eq H3 H4.

  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.
  apply Zle_is_le_bool in eq1; apply Zle_is_le_bool in eq2.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inverts Hx; substs.
  lets Hx1: byte_repr_int_unsigned_eq eq1 eq2 H1; auto.
  substs.
  split; eauto.
  eapply ptomvallist_true_mem_eq; eauto.
  
  lets Hx: ptomvallist_true_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts Hx; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.

  apply byte_repr_eq in H2.  

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H7; auto.
  do 2 rewrite Int.repr_unsigned in H8; substs.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  lets Hx: ptomvallist_true_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3;
    remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts Hx; substs.
  apply byte_repr_eq in H8.
  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H10; substs.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  
  lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.

  lets Hx: ptomvallist_true_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_true_mem_eq; eauto.
Qed.

Lemma mapstoval_false_rule_type_val_match_eq :
  forall l t v v' m m' M,
    rule_type_val_match t v = true -> rule_type_val_match t v' = true ->
    mapstoval l t false v m -> mapstoval l t false v' m' ->
    sub m M -> sub m' M ->
    v = v' /\ m = m'.
Proof.
  intros.
  unfold mapstoval in H1, H2; simpljoin1.
  destruct t; destruct v; destruct v'; simpl in H, H0; tryfalse;
  simpl encode_val in H5, H6;
    (match goal with
  | |- Vptr _ = Vptr _ /\ _ => try destruct a; try destruct a0
  | |- Vptr _ = _ /\ _ => try destruct a
  | |- _ = Vptr _ /\ _ => try destruct a
  | |- _ => idtac
  end);
  try solve [split; auto; eapply ptomvallist_false_mem_eq; eauto];
  try solve [lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; [simpl; auto | inverts Hx]].

  assert(i = i0).
  simpl in H5, H6; destruct l; unfold ptomval in *; simpljoin1.
  lets Hx: mem_sub_sig_eq H3 H4.

  destruct (Int.unsigned i <=? Byte.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Byte.max_unsigned) eqn : eq2; tryfalse.
  apply Zle_is_le_bool in eq1; apply Zle_is_le_bool in eq2.
  remember(Byte.repr (Int.unsigned i)) as X;
    remember(Byte.repr (Int.unsigned i0)) as Y.
  inverts Hx; substs.
  lets Hx1: byte_repr_int_unsigned_eq eq1 eq2 H1; auto.
  substs.
  split; eauto.
  eapply ptomvallist_false_mem_eq; eauto.
  
  lets Hx: ptomvallist_false_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2.
  inverts Hx; substs.

  destruct (Int.unsigned i <=? Int16.max_unsigned) eqn : eq1; tryfalse.
  destruct (Int.unsigned i0 <=? Int16.max_unsigned) eqn : eq2; tryfalse.
  apply Z.leb_le in eq1.
  apply Z.leb_le in eq2.

  apply byte_repr_eq in H2.  

  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H7; auto.
  do 2 rewrite Int.repr_unsigned in H8; substs.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.
  split.
  apply zero_le_int_unsigned_div_256; auto.
  apply z_le_int16_max_div_256_byte_max; auto.

  lets Hx: ptomvallist_false_sub_vl_eq H6 H5 H3 H4.
  simpl; auto.
  remember (Byte.repr (Int.unsigned i)) as X1;
    remember (Byte.repr (Int.unsigned i / 256)) as X2;
    remember (Byte.repr (Int.unsigned i / 256 / 256)) as X3;
    remember (Byte.repr (Int.unsigned i / 256 / 256 / 256)) as X4;
    remember (Byte.repr (Int.unsigned i0)) as Y1;
    remember (Byte.repr (Int.unsigned i0 / 256)) as Y2;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256)) as Y3;
    remember (Byte.repr (Int.unsigned i0 / 256 / 256 / 256)) as Y4.
  inverts Hx; substs.
  apply byte_repr_eq in H8.
  assert(Int.unsigned i = Int.unsigned i0).
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  eapply div_256_byte_repr_eq; eauto.
  assert(Int.repr (Int.unsigned i) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H10; substs.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  split.
  apply zero_le_int_unsigned_div_256_256_256; auto.
  apply z_le_int_max_div_256_256_256_byte_max; auto.
  apply Int.unsigned_range_2.
  
  lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.

  lets Hx: ptomvallist_false_sub_vl_eq H5 H6 H4 H3; simpl; auto.
  inverts Hx.
  split; auto.
  eapply ptomvallist_false_mem_eq; eauto.
Qed.

Lemma Astruct'_vl_eq :
  forall vl vl' d l e e0 M1 M2 M i ier lo o1 o2 a,
    struct_type_vallist_match' d vl -> struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Astruct' l d vl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq' vl vl' d.
Proof.
  inductions vl; intros.
  destruct vl'; destruct d; simpl in H3, H4; tryfalse; auto.
  
  destruct vl'; destruct d; simpl in H3, H4; tryfalse;
  simpl in H, H0.

  destruct l; destruct t; simpl in H1, H2; simpljoin1;
  try solve [
        assert(sub x M) as _H1 by mem_join_sub_solver;
        assert(sub x5 M) as _H2 by mem_join_sub_solver;
        lets Hx1': mapstoval_true_rule_type_val_match_eq H H0 H14 H8 _H2; lets Hx1 : Hx1' _H1;
        assert(sub x0 M) as _H3 by mem_join_sub_solver;
        assert(sub x6 M) as _H4 by mem_join_sub_solver;
        lets Hx2': IHvl H18 H17 H15 H9 _H4; lets Hx2: Hx2' _H3; simpljoin1;
        simpl; auto;
        simpljoin1
      ];
  try solve [simpl; eapply IHvl; eauto].
Qed.

Lemma node_vl_eq :
  forall vl vl' head t M1 M2 M o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, ier, l, o2, a) |= node head vl' t ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq vl vl' t.
Proof.
  intros.
  unfold node in H, H0.
  destruct H, H0; simpl in H, H0; simpljoin1.
  unfold Astruct in H7, H15.
  destruct t; tryfalse; inverts H6; simpl in H10, H18.
  simpl.
  eapply Astruct'_vl_eq; eauto.
Qed.

Lemma struct_type_vallist_match_os_event : 
forall v,
 struct_type_vallist_match os_ucos_h.OS_EVENT v ->
 exists v1 v2 v3 v4 v5 v6 v7 v8, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; tryfalse;
  do 8 eexists; eauto.
Qed.

Lemma osabst_eq_join_eq :
  forall m1 m1' m2 m2' M M',
    OSAbstMod.join m1 m2 M ->
    OSAbstMod.join m1' m2' M' ->
    m1 = m1' -> m2 = m2' ->
    M = M'.
Proof.
  intros; substs.
  eapply OSAbstMod.join_unique; eauto.
Qed.

Lemma struct_type_vallist_match_os_q : forall v, struct_type_vallist_match os_ucos_h.OS_Q v -> exists v1 v2 v3 v4 v5 v6 v7 v8, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; simpljoin1; tryfalse.
  do 4 eexists; eauto.
Qed.

Lemma struct_type_vallist_match_os_q_freeblk : forall v, struct_type_vallist_match os_ucos_h.OS_Q_FREEBLK v -> exists v1 v2, v = v1 :: v2 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  eauto.
Qed.

Lemma AOSEvent_osevent_eq :
  forall osevent osevent' etbl etbl' petbl petbl' l e e0 M1 M2 M i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSEvent l osevent etbl petbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSEvent l osevent' etbl' petbl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT.
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma AOSQCtr_osq_eq :
  forall osq osq' l e e0 M1 M2 M i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSQCtr l osq ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSQCtr l osq' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq osq osq' os_ucos_h.OS_Q.
Proof.
  unfold AOSQCtr; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
Qed.

Lemma AEventNode_osevent_eq :
  forall v osevent osevent' etbl etbl' petbl petbl' d d' e e0 M1 M2 M i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AEventNode v osevent etbl petbl d ->
    (e, e0, M2, i, ier, lo, o2, a) |= AEventNode v osevent' etbl' petbl' d' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT.
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply AOSEvent_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
Qed.
(*end*)

(* main lemma ?*)
Lemma a_isr_is: inv_isr_prop A_isr_is_prop.
Proof.
  unfold inv_isr_prop;unfold A_isr_is_prop.
  splits;intros;destruct s as [[]]; destruct t as [[[[[]]]]];destruct l as [[]].
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl;simpljoin1.
  do 8 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  split; eauto.
  split; auto.
  unfolds; auto.

  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  unfold isr_is_prop.
  intros.
  apply H9 in H.
  unfold isrupd.
  destruct ( beq_nat i x1 );auto.

  unfolds; auto.
  
  (*-----------------------*)
  unfold isr_is_prop in H;simpl in H;simpljoin1.
  simpl.
  do 8 eexists;splits;simpljoin1.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists;splits; eauto.
  eapply map_join_emp.
  eapply map_join_emp.
  splits; eauto.
  unfolds; auto.

  unfold isr_is_prop.
  intros.
  unfold isrupd.
  remember ( beq_nat i x1) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H9.
  intro.
  destruct H.
  right;auto.
  unfolds; auto.
  
  (*----------------------------*)
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl; eauto.
  do 8 eexists;splits; eauto.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.

  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  unfold isr_is_prop.
  simpl in H0, H1.
  intros.
  
  assert (x1=i\/x1<>i) by tauto.
  destruct H2.
  subst;auto.
  subst x0.
  apply H11.
  intro.
  destruct H.
  simpl in H1.
  destruct H1;tryfalse.
  auto.
  unfolds; auto.
  
  (*----------------------*)
  unfold isr_is_prop in H;simpl in H; simpljoin1.
  simpl;  eauto.
  do 8 eexists;splits; eauto.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  
  do 6 eexists;splits;simpljoin1.
  eapply map_join_emp; eauto.
  eapply map_join_emp; eauto.
  splits; eauto.
  unfolds; auto.
  unfold isr_is_prop.
  intros.
  simpl in H0.
  subst x.
  unfold empisr.
  auto.
  unfolds; auto.
Qed.

(*---- osabst emp lemmas ----*)
Lemma Astruct'_osabst_emp :
  forall vl e e0 M i ier l o a0 lo d,
    (e, e0, M, i, ier, lo, o, a0) |= Astruct' l d vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  destruct d; simpl in H; simpljoin1; tryfalse.
  destruct d; simpl in H; tryfalse.
  destruct t; destruct l; simpl in H; simpljoin1; eapply IHvl; eauto.
Qed.

Lemma Astruct_osabst_emp :
  forall e e0 M i ier l o a lo t vl,
    (e, e0, M, i, ier, lo, o, a) |= Astruct l t vl ->
    o = empabst.
Proof.
  intros.
  unfold Astruct in H; destruct t; tryfalse.
  eapply Astruct'_osabst_emp; eauto.
  eapply Astruct'_osabst_emp; eauto.
Qed.

Lemma node_osabst_emp :
  forall head a t e e0 M i ier l o a0,
    (e, e0, M, i, ier, l, o, a0) |= node head a t ->
    o = empabst.
Proof.
  intros.
  unfold node in H; sep pure.
  eapply Astruct_osabst_emp; eauto.
Qed.

Lemma Aarray'_osabst_emp :
  forall vl l n t e e0 M i ier lo o a0 ,
    (e, e0, M, i, ier, lo, o, a0) |= Aarray' l n t vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  destruct n; simpl in H; simpljoin1; tryfalse.
  destruct n; simpl in H; tryfalse.
  destruct l; simpl in H; simpljoin1.
  eapply IHvl; eauto.
Qed.

Lemma Aarray_osabst_emp :
  forall vl l t e e0 M i ier lo o a0 ,
    (e, e0, M, i, ier, lo, o, a0) |= Aarray l t vl ->
    o = empabst.
Proof.
  intros.
  unfold Aarray in H; destruct t; tryfalse.
  eapply Aarray'_osabst_emp; eauto.
Qed.

Lemma ecbf_sllseg_osabst_emp :
  forall eventl e e0 M i ier l o a head tail t next,
    (e, e0, M, i, ier, l, o, a) |= ecbf_sllseg head tail eventl t next ->
    o = empabst.
Proof.
  inductions eventl; intros.
  simpl in H; simpljoin1.
  
  unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  simpl_sat H; simpljoin1.

  eapply node_osabst_emp in H8; substs.
  eapply Aarray_osabst_emp in H18; eauto; substs.
  eapply Aarray_osabst_emp in H28; eauto; substs. (* new add *)
  
  lets Hx: IHeventl H34; substs. (* change H24 -> H34 *)
  clear - H7 H17 H27. (* add H27 *)
  apply OSAbstMod.extensionality; intros.
  simpljoin1. (* new add *)
Qed.

Lemma ecbf_sll_osabst_emp :
  forall eventl e e0 M i ier l o a head t next,
    (e, e0, M, i, ier, l, o, a) |= ecbf_sll head eventl t next ->
    o = empabst.
Proof.
  intros; unfold ecbf_sll in H.
  apply ecbf_sllseg_osabst_emp in H; auto.
Qed.

Lemma sllseg_osabst_emp :
  forall osql e e0 M i ier l o a head tail t next,
    (e, e0, M, i, ier, l, o, a) |= sllseg head tail osql t next ->
    o = empabst.
Proof.
  inductions osql; intros.
  simpl in H; simpljoin1.
  
  unfold sllseg in H; fold sllseg in H.
  simpl_sat H; simpljoin1.
  
  eapply node_osabst_emp in H13; substs.
  
  lets Hx: IHosql H14; substs.
  clear - H12.
  apply OSAbstMod.extensionality; intros.
  pose proof H12 a.
  rewrite OSAbstMod.emp_sem in H.
  destruct(OSAbstMod.get o a); tryfalse.
  rewrite OSAbstMod.emp_sem; auto.
Qed.

Lemma sll_osabst_emp :
  forall osql e e0 M i ier l o a head t next,
    (e, e0, M, i, ier, l, o, a) |= sll head osql t next ->
    o = empabst.
Proof.
  intros; unfold sll in H.
  apply sllseg_osabst_emp in H; auto.
Qed.

Lemma qblkf_sllseg_osabst_emp :
  forall eventl e e0 M i ier l o a head tail t next,
    (e, e0, M, i, ier, l, o, a) |= qblkf_sllseg head tail eventl t next ->
    o = empabst.
Proof.
  inductions eventl; intros.
  simpl in H; simpljoin1.
  
  unfold qblkf_sllseg in H; fold qblkf_sllseg in H.
  simpl_sat H; simpljoin1.
  
  eapply node_osabst_emp in H8; substs.
  eapply Aarray_osabst_emp in H18; eauto; substs.
  
  lets Hx: IHeventl H19; substs.
  clear - H7 H17.
  apply OSAbstMod.extensionality; intros.
  pose proof H7 a; pose proof H17 a.
  rewrite OSAbstMod.emp_sem in H0, H.
  destruct(OSAbstMod.get x12 a); tryfalse.
  destruct(OSAbstMod.get o a); tryfalse.
  rewrite OSAbstMod.emp_sem; auto.
Qed.

Lemma qblkf_sll_osabst_emp :
  forall eventl e e0 M i ier l o a head t next,
    (e, e0, M, i, ier, l, o, a) |= qblkf_sll head eventl t next ->
    o = empabst.
Proof.
  intros; unfold ecbf_sll in H.
  apply qblkf_sllseg_osabst_emp in H; auto.
Qed.

Lemma AOSQCtr_osabst_emp :
  forall l osq e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AOSQCtr l osq ->
    o = empabst.
Proof.
  unfold AOSQCtr; intros.
  simpl_sat H; simpljoin1.
  eapply node_osabst_emp in H3; auto.
Qed.

Lemma AOSQBlk_osabst_emp :
  forall l osqblk msgtbl e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AOSQBlk l osqblk msgtbl ->
    o = empabst.
Proof.
  unfold AOSQBlk; intros.
  simpl_sat H; simpljoin1.
  eapply node_osabst_emp in H3.
  eapply Aarray_osabst_emp in H9; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H2 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a0); tryfalse.
  auto.
Qed.

Lemma AEventData_osabst_emp :
  forall osevent d e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AEventData osevent d ->
    o = empabst.
Proof.
  unfold AEventData; intros.
  destruct d; try solve [simpl in H; simpljoin1].
  simpl_sat H; simpljoin1.
  unfold AMsgData in H9; simpl_sat H9; simpljoin1.
  eapply AOSQCtr_osabst_emp in H4; eapply AOSQBlk_osabst_emp in H11; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H2 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a0); tryfalse; auto.
Qed.

Lemma AOSEvent_osabst_emp :
  forall l osevent etbl petbl e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AOSEvent l osevent etbl petbl ->
    o = empabst.
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpljoin1.
  eapply node_osabst_emp in H3.
  unfold AOSEventTbl in H8.
  unfold AOSPostEventTbl in H28.
  simpl_sat H8; simpljoin1.
  eapply Aarray_osabst_emp in H8; auto.
  simpl_sat H28; simpljoin1.
  eapply Aarray_osabst_emp in H4; auto.
Qed.

Lemma AEventNode_osabst_emp :
  forall v osevent etbl petbl d e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AEventNode v osevent etbl petbl d ->
    o = empabst.
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpljoin1.
  apply AOSEvent_osabst_emp in H3; apply AEventData_osabst_emp in H4.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H2 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a0); tryfalse; auto.
Qed.

Lemma evsllseg_osabst_emp :
  forall ectrl msgql head tail e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= evsllseg head tail ectrl msgql ->
    o = empabst.
Proof.
  inductions ectrl; intros.
  simpl in H; simpljoin1.
  unfold evsllseg in H; fold evsllseg in H; destruct msgql; tryfalse; destruct a.
  destruct p.
  simpl_sat H; simpljoin1.
  apply AEventNode_osabst_emp in H8.
  eapply IHectrl in H9; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H7 a.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a); tryfalse; auto.
Qed.
(* end *)

(*---- precise lemmas -----*)
Lemma precise'2precise:
 forall M1 M2 o1 o2,
 (forall M: mem, sub M1 M -> sub M2 M -> M1 = M2) /\ 
     (forall o: osabst, sub o1 o ->  sub o2 o -> o1 = o2)
  -> 
  (forall M o, sub M1 M -> sub M2 M -> 
  sub o1 o ->  sub o2 o -> M1 = M2 /\ o1 = o2).
Proof. intros. destruct H. split. eapply H;eauto. eapply H4;eauto. Qed.

Lemma Astruct'_precise' :
  forall vl vl' l d M1 M2 o1 o2 e e0 i ier lo a,
    struct_type_vallist_match' d vl ->
    struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Astruct' l d vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros; inductions vl.
  destruct vl'.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  destruct vl'.
  destruct d; simpl in H1, H2; simpljoin1; auto; tryfalse.
  
  destruct d; simpl in H, H0; tryfalse.
  destruct l.
  destruct t; simpljoin1;
  try solve [lets Hx: IHvl H H0 H1 H2; auto];  
  try solve [
        simpl in H1; simpljoin1; simpl in H2; simpljoin1;
        lets Hx: IHvl H4 H3 H9 H11; simpljoin1; split; intros; [
          assert(sub x M) by mem_join_sub_solver;
          assert(sub x1 M) by
              mem_join_sub_solver;
          lets Hx1:  mapstoval_true_mem_eq H13 H14 H8 H10;
          substs;
          eapply eq_join_eq; eauto;
          mem_eq_solver M |
          apply (H6 o); auto]
      ].
Qed.

Lemma Astruct'_precise : 
forall vl vl' l d M1 M2 o1 o2 e e0 i ier lo a,
    struct_type_vallist_match' d vl ->
    struct_type_vallist_match' d vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Astruct' l d vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Astruct' l d vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros  vl vl' l d M1 M2 o1 o2 e e0 i ier lo a H H0 H1 H2. 
  eapply precise'2precise;eauto. 
  apply (Astruct'_precise' vl vl' l d M1 M2 o1 o2 e e0 i ier lo a);eauto.
Qed.

Lemma Astruct_precise' :
  forall vl vl' l t M1 M2 o1 o2 e e0 i ier lo a,
    struct_type_vallist_match t vl ->
    struct_type_vallist_match t vl' ->
          (e, e0, M1, i, ier, lo, o1, a) |= Astruct l t vl ->
          (e, e0, M2, i, ier, lo, o2, a) |= Astruct l t vl' ->
          (forall M : mem,
             sub M1 M -> sub M2 M -> M1 = M2) /\
          (forall o : osabst,
             sub o1 o -> sub o2 o -> o1 = o2 ).
Proof.
  intros.
  destruct t; simpl in H, H0; tryfalse.
  unfold Astruct in H1, H2.
  lets Hx: Astruct'_precise' H H0 H1 H2; auto.
Qed.

Lemma Astruct_precise :
  forall vl vl' l t M1 M2 o1 o2 e e0 i ier lo a,
    struct_type_vallist_match t vl ->
    struct_type_vallist_match t vl' ->
          (e, e0, M1, i, ier, lo, o1, a) |= Astruct l t vl ->
          (e, e0, M2, i, ier, lo, o2, a) |= Astruct l t vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  destruct t; simpl in H, H0; tryfalse.
  unfold Astruct in H1, H2.
  lets Hx: Astruct'_precise H H0 H1 H2; auto.
  eapply Hx;eauto.
Qed.


Lemma node_precise' :
  forall vl vl' head t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, ier, l, o2, a) |= node head vl' t ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  simpl in H, H0; simpljoin1; inverts H4.    
  lets Hx: Astruct_precise' H16 H8 H13 H5; auto.
Qed.

Lemma node_precise :
  forall vl vl' head t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= node head vl t ->
    (e, e0, M2, i, ier, l, o2, a) |= node head vl' t ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' head t M1 M2 o1 o2 e e0 i ier l a H H0.
  simpl in H, H0; simpljoin1; inverts H4.    
  lets Hx: Astruct_precise H16 H8 H13 H5; auto.
Qed.

Lemma Aarray'_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= Aarray' head n t vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray' head n t vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intro; inductions vl; intros.
  destruct vl'; destruct n; simpl in H, H0; tryfalse.
  simpljoin1; split;  intros; auto.
  
  destruct vl'; destruct n; simpl in H, H0; tryfalse.
  destruct head.
  
  simpl in H, H0; simpljoin1.
  lets Hx: IHvl H11 H5.
  simpljoin1; split; intros.
  eapply eq_join_eq; eauto.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  mem_eq_solver M.
  apply H0 with (o:=o); eauto.
Qed.

Lemma Aarray'_precise :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= Aarray' head n t vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray' head n t vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' head n t M1 M2 o1 o2 e e0 i ier l  a H H0.
  eapply precise'2precise;eauto.
  eapply Aarray'_precise';eauto.
Qed.

Lemma Aarray_precise' :
  forall vl vl' head t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= Aarray head t vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray head t vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).      
Proof.
  intros.
  unfold Aarray in H, H0.
  destruct t; simpl in H, H0; tryfalse.
  eapply Aarray'_precise'; eauto.
Qed.

Lemma Aarray_precise :
  forall vl vl' head t M1 M2 o1 o2 e e0 i ier l  a,
    (e, e0, M1, i, ier, l, o1, a) |= Aarray head t vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray head t vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros vl vl' head t M1 M2 o1 o2 e e0 i ier l  a H H0.
  eapply precise'2precise;eauto.
  eapply Aarray_precise';eauto.
Qed.

Lemma ecbf_sll_precise' :
  forall eventl eventl' head M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= ecbf_sll head eventl os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= ecbf_sll head eventl' os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions eventl; intros.
  simpl in H; simpljoin1.
  destruct eventl'.
  simpl in H0; simpljoin1; auto.
  unfold ecbf_sll in H0; unfold ecbf_sllseg in H0; fold ecbf_sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct eventl'.
  simpl in H0; simpljoin1.
  unfold ecbf_sll in H; unfold ecbf_sllseg in H; fold ecbf_sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold ecbf_sll in H, H0; unfold ecbf_sllseg in H, H0; fold ecbf_sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
 
  lets Hx: node_precise' H9 H12.
  rewrite H14 in H21; inverts H21.
  
  lets Hx1: Aarray_precise' H19 H30. (* H28 -> H30 *)
  rewrite H24 in H37; inverts H37. (* new add *)
  lets Hx1': Aarray_precise' H29 H42. (* new add *)

  unfold ecbf_sll in IHeventl.
  simpljoin1; split; intros.
  
  assert(x = x4 (* /\ x4 = x10 /\ x3 = x9 *)). (* x2 -> x4 *)
  assert(sub x10 M) by mem_join_sub_solver. (* x8 -> x11 *)
  assert(sub x19 M) by mem_join_sub_solver. (* x15 -> x21 *)

  lets Hx: node_vl_eq H9 H12 H17 H20(* H13 H15 *).
  simpl in Hx; unfold V_OSEventListPtr in H3, H4.
(*   unfold V_OSPostEventGrp in H39, H55. (* new add *) *)
  unfold node in H9, H12.
  destruct H9, H12; sep split in H9; sep split in  H12; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8, a = a1::a2::a3::a4::a5::a6::a7::a8::nil).
  { eapply struct_type_vallist_match_os_event in H31; simpljoin1; do 8 eexists; eauto. } (* H22 -> H31 *)
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8, v = v1::v2::v3::v4::v5::v6::v7::v8::nil).
  { eapply struct_type_vallist_match_os_event; eauto; do 8 eexists; eauto. }
  simpljoin1; simpl in Hx; simpl in H3, H4; simpljoin1; inversion H3; inversion H4; 
(*   inversion H39; inversion H55; (* new add *) *)
  substs; auto.
  substs.

  lets Hx2: IHeventl (* H25 H34 *) H35 H48.
  simpljoin1; mem_eq_solver M.
  
  eapply ecbf_sllseg_osabst_emp in (* H25 *) H35.
  eapply ecbf_sllseg_osabst_emp in (* H34 *) H48.
  substs.
  eapply osabst_eq_join_eq; eauto.
  apply (H10 o). (* H2 -> H10 *)
(*   clear - H5 H8. *)
 clear -H8 H13.
  unfold sub in *; geat.
(*   clear - H10 H11. *)
  clear -H11 H15.
  unfold sub in *; geat.

  eapply osabst_eq_join_eq; eauto.
   apply (H2 o).
 clear -H8 H13 H18.
  unfold sub in *; geat.
  clear -H11 H15 H27.
  unfold sub in *; geat.

  eapply osabst_eq_join_eq; eauto.

  apply (H0 o).
 clear -H8 H13 H18 H28.
  unfold sub in *.
  geat.
  clear -H11 H15 H27 H41.
  unfold sub in *.
  geat.
Qed.

Lemma ecbf_sll_precise :
  forall eventl eventl' head M1 M2 o1 o2 e e0 i ier l  a,
    (e, e0, M1, i, ier, l, o1, a) |= ecbf_sll head eventl os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= ecbf_sll head eventl' os_ucos_h.OS_EVENT V_OSEventListPtr ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros eventl eventl' head M1 M2 o1 o2 e e0 i ier l  a H H0.
  eapply precise'2precise;eauto.
  eapply ecbf_sll_precise';eauto.
Qed.

Lemma AOSEventFreeList_precise' :
  forall eventl eventl' fecbh fecbh' M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= AOSEventFreeList fecbh eventl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSEventFreeList fecbh' eventl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEventFreeList; intros.
  simpl in H, H0; simpljoin1.

  rewrite H23 in H9; inverts H9.
  split; intros.
  assert(fecbh = fecbh').

  assert(isptr fecbh) by (eapply isptr_ecbf_sll; eauto).
  assert(isptr fecbh') by (eapply isptr_ecbf_sll; eauto).
  
  destruct fecbh, fecbh'; auto;
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse);
  try(unfolds in H3; destruct H3; simpljoin1; tryfalse).
  unfolds in H24; simpljoin1; simpl in H4; simpljoin1.
  
  unfolds in H10; simpljoin1; simpl in H11; destruct a0; simpl in H11; simpljoin1.
  clear - H4 H11 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H11; substs.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, MNull)) M).
  mem_join_sub_solver.

  lets Hx: mem_sub_sig_eq H2 H4; tryfalse.
  
  unfolds in H10; simpljoin1; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; destruct a0; simpl in H12; simpljoin1.
  
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (sig (x18, Int.unsigned Int.zero) (true, MNull)) M).
  mem_join_sub_solver.
  lets Hx: mem_sub_sig_eq H2 H4; tryfalse.
 
  inverts H2; inverts H3.
  assert(sub x M).
  apply join_sub_l in H1.
  eapply sub_trans; eauto.
  assert(sub x5 M).
  apply join_sub_l in H15.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H10 H24 H2 H3; simpljoin1.
  
  substs.
  
  assert(x = x5).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  lets Hx: ecbf_sll_precise' H19 H5; simpljoin1.
  mem_eq_solver M.
  
  apply ecbf_sll_osabst_emp in H19; apply ecbf_sll_osabst_emp in H5.
  substs; auto.
Qed.

Lemma AOSEventFreeList_precise :
  forall eventl eventl' fecbh fecbh' M1 M2 o1 o2 e e0 i ier l  a,
    (e, e0, M1, i, ier, l, o1, a) |= AOSEventFreeList fecbh eventl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSEventFreeList fecbh' eventl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros eventl eventl' fecbh fecbh' M1 M2 o1 o2 e e0 i ier l  a H H0.
  eapply precise'2precise;eauto.
  eapply AOSEventFreeList_precise';eauto.
Qed.

Lemma osq_sll_precise' :
  forall osql osql' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head osql os_ucos_h.OS_Q V_OSQPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head osql' os_ucos_h.OS_Q V_OSQPtr ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
           sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions osql; intros.
  simpl in H; simpljoin1.
  destruct osql'.
  simpl in H0; simpljoin1; auto.
  unfold sll in H0; unfold sllseg in H0; fold sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct osql'.
  simpl in H0; simpljoin1.
  unfold sll in H; unfold sllseg in H; fold sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold sll in H, H0; unfold sllseg in H, H0; fold sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  lets Hx: node_precise' H14 H19.
  
  unfold sll in IHosql.
  simpljoin1; split; intros.
  assert(x5 = x6).
  assert(sub x12 M) by mem_join_sub_solver.
  assert(sub x17 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H14 H19 H5 H6.
  simpl in Hx; unfold V_OSEventListPtr in H9, H10.
  unfold node in H14, H19.
  destruct H14, H19; sep split in H7; sep split in H8; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8, a = a1::a2::a3::a4::a5::a6::a7::a8::nil).
  eapply struct_type_vallist_match_os_q; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8, v = v1::v2::v3::v4::v5::v6::v7::v8::nil).
  eapply struct_type_vallist_match_os_q; eauto.
  simpljoin1; simpl in Hx; simpl in H9, H10; simpljoin1; inversion H9; inversion H10; substs; auto.
  substs.
  
  lets Hx2: IHosql H15 H20.
  simpljoin1; mem_eq_solver M.
  
  eapply sllseg_osabst_emp in H15.
  eapply sllseg_osabst_emp in H20.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma osq_sll_precise :
  forall osql osql' head e e0 M1 M2 i ier l  o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head osql os_ucos_h.OS_Q V_OSQPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head osql' os_ucos_h.OS_Q V_OSQPtr ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof. 
  intros osql osql' head e e0 M1 M2 i ier l  o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply osq_sll_precise';eauto.
Qed.

Lemma AOSQFreeList_precise' :
  forall osql osql' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSQFreeList osql ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSQFreeList osql' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSQFreeList; intros.
  simpl in H, H0; simpljoin1.
  rewrite H23 in H9; inverts H9.
  split; intros.
  assert(x = x6).
  
  assert(isptr x).
  eapply sll_isptr; eauto.
  assert(isptr x6).
  eapply sll_isptr; eauto.
  destruct x, x6; auto;
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse);
  try(unfolds in H3; destruct H3; simpljoin1; tryfalse).
  unfolds in H10; simpljoin1; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; destruct a0; simpl in H12; simpljoin1.
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub x7 M).
  clear - H15 H.
  unfold sub in *; geat.
  assert(sub x0 M).
  clear - H1 H0.
  unfold sub in *; geat.
  lets Hx: mem_join_sig_sub_eq H10 H3 H2 H4; tryfalse.
  
  unfolds in H10; simpljoin1; simpl in H4; destruct a0; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; simpljoin1.
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub x7 M).
  clear - H15 H.
  unfold sub in *; geat.
  assert(sub x0 M).
  clear - H1 H0.
  unfold sub in *; geat.
  lets Hx: mem_join_sig_sub_eq H10 H3 H2 H4; tryfalse.

  inverts H2; inverts H3.
  assert(sub x0 M).
  apply join_sub_l in H1.
  eapply sub_trans; eauto.
  assert(sub x7 M).
  apply join_sub_l in H15.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H10 H24 H2 H3; simpljoin1.

  substs.
  assert(x0 = x7).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  
  lets Hx: osq_sll_precise' H19 H5; simpljoin1.
  mem_eq_solver M.
  
  apply sll_osabst_emp in H19; apply sll_osabst_emp in H5.
  substs; auto.
Qed.

Lemma AOSQFreeList_precise :
  forall osql osql' e e0 i ier l  a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSQFreeList osql ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSQFreeList osql' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros osql osql' e e0 i ier l  a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSQFreeList_precise';eauto.
Qed.
    
Lemma qblkf_sll_precise' :
  forall qblkl qblkl' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= qblkf_sll head qblkl os_ucos_h.OS_Q_FREEBLK V_nextblk ->
    (e, e0, M2, i, ier, l, o2, a) |= qblkf_sll head qblkl' os_ucos_h.OS_Q_FREEBLK V_nextblk ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions qblkl; intros.
  simpl in H; simpljoin1.
  destruct qblkl'.
  simpl in H0; simpljoin1; auto.
  unfold qblkf_sll in H0; unfold qblkf_sllseg in H0; fold qblkf_sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct qblkl'.
  simpl in H0; simpljoin1.
  unfold qblkf_sll in H; unfold qblkf_sll in H; fold qblkf_sll in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold qblkf_sll in H, H0; unfold qblkf_sllseg in H, H0; fold qblkf_sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  lets Hx: node_precise' H9 H12.
  rewrite H14 in H22; inverts H22.
    
  lets Hx1: Aarray_precise' H19 H27.
  
  unfold qblkf_sll in IHqblkl.
  simpljoin1; split; intros.

  assert(x = x2).
  assert(sub x8 M) by mem_join_sub_solver.
  assert(sub x15 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H9 H12 H13 H15.
  simpl in Hx; unfold V_OSQPtr in H3, H4.
  unfold node in H9, H12.
  destruct H9, H12; sep split in H9; sep split in  H12; simpljoin1.
  assert(exists a1 a2 , a = a1::a2::nil).
  
  eapply struct_type_vallist_match_os_q_freeblk; eauto.
  assert(exists v1 v2, v = v1::v2::nil).
  eapply struct_type_vallist_match_os_q_freeblk; eauto.
  simpljoin1; simpl in Hx; simpl in H3, H4; simpljoin1; inversion H3; inversion H4; substs; auto.
  substs.
    
  lets Hx2: IHqblkl H20 H28.
  simpljoin1; mem_eq_solver M.      
  eapply qblkf_sllseg_osabst_emp in H20.
  eapply qblkf_sllseg_osabst_emp in H28.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma qblkf_sll_precise :
  forall qblkl qblkl' head e e0 M1 M2 i ier l  o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= qblkf_sll head qblkl os_ucos_h.OS_Q_FREEBLK V_nextblk ->
    (e, e0, M2, i, ier, l, o2, a) |= qblkf_sll head qblkl' os_ucos_h.OS_Q_FREEBLK V_nextblk ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros qblkl qblkl' head e e0 M1 M2 i ier l  o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply qblkf_sll_precise';eauto.
Qed.

Lemma AOSQFreeBlk_precise' :
  forall qblkl qblkl' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSQFreeBlk qblkl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSQFreeBlk qblkl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
         sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSQFreeBlk; intros.
  simpl in H, H0; simpljoin1.
  rewrite H23 in H9; inverts H9.
  split; intros.
  assert(x = x6).
  assert(isptr x).
  eapply qblkf_sll_isptr; eauto.
  assert(isptr x6).
  eapply qblkf_sll_isptr; eauto.
  destruct x, x6; auto;
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse);
  try(unfolds in H3; destruct H3; simpljoin1; tryfalse).
  unfolds in H10; simpljoin1; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; destruct a0; simpl in H12; simpljoin1.
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub x7 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H3 H2 H4; tryfalse.
  
  unfolds in H10; simpljoin1; simpl in H4; destruct a0; simpl in H4; simpljoin1.
  unfolds in H24; simpljoin1; simpl in H12; simpljoin1.
  clear - H4 H12 H1 H15 H H0 H3 H10.
  unfold ptomval in H4; unfold ptomval in H12; substs.
  assert(sub x7 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H3 H2 H4; tryfalse.
  
  inverts H2; inverts H3.
  assert(sub x0 M).
  apply join_sub_l in H1.
  eapply sub_trans; eauto.
  assert(sub x7 M).
  apply join_sub_l in H15.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H10 H24 H2 H3; simpljoin1.

  substs.
  assert(x0 = x7).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  
  lets Hx: qblkf_sll_precise' H19 H5; simpljoin1.
  mem_eq_solver M.
    
  apply qblkf_sll_osabst_emp in H19; apply qblkf_sll_osabst_emp in H5.
  substs; auto.
Qed.

Lemma AOSQFreeBlk_precise :
  forall qblkl qblkl' e e0 i ier l  a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSQFreeBlk qblkl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSQFreeBlk qblkl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros qblkl qblkl' e e0 i ier l  a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSQFreeBlk_precise';eauto.
Qed.

Lemma AOSEventTbl_precise' :
  forall l etbl etbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSEventTbl l etbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSEventTbl l etbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEventTbl; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  lets Hx: Aarray_precise' H11 H4; auto.
Qed.

Lemma AOSEventTbl_precise :
  forall l etbl etbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSEventTbl l etbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSEventTbl l etbl' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l etbl etbl' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AOSEventTbl_precise';eauto.
Qed.

Lemma AOSEvent_precise' :
  forall l osevent osevent' etbl etbl' petbl petbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSEvent l osevent etbl petbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSEvent l osevent' etbl' petbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSEvent; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  rewrite H14 in H66; inverts H66.
  rewrite H34 in H86; inverts H86.
  lets Hx1: node_precise' H56 H4.

   lets Hx2: AOSEventTbl_precise' H61 H9.
  
  lets Hx3: AOSEventTbl_precise' H81 H29.
  simpljoin1; split; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AOSEvent_precise :
  forall l osevent osevent' etbl etbl' petbl petbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSEvent l osevent etbl petbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSEvent l osevent' etbl' petbl'->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l osevent osevent' etbl etbl'  petbl petbl' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AOSEvent_precise';eauto.
Qed.

Lemma AOSQCtr_precise' :
  forall l osq osq' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSQCtr l osq ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSQCtr l osq' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSQCtr; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  eapply node_precise'; eauto.
Qed.

Lemma AOSQCtr_precise :
  forall l osq osq' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSQCtr l osq ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSQCtr l osq' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l osq osq' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AOSQCtr_precise';eauto.
Qed.

Lemma AOSQBlk_precise' :
  forall l osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSQBlk l osqblk msgtbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSQBlk l osqblk' msgtbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSQBlk; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  rewrite H21 in H9; inverts H9.
  lets Hx1: node_precise' H16 H4.
  lets Hx2: Aarray_precise' H22 H10.
  simpljoin1; split; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AOSQBlk_precise :
  forall l osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSQBlk l osqblk msgtbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSQBlk l osqblk' msgtbl' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AOSQBlk_precise';eauto.
Qed.

Lemma AMsgData_precise' :
  forall l osq osq' osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AMsgData l osq osqblk msgtbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AMsgData l osq' osqblk' msgtbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
               sub o1 o -> sub o2 o -> o1 = o2).  
Proof.
  unfold AMsgData; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  
  intros.
  simpljoin1; split; intros.
  assert(struct_atom_val_eq osq osq' os_ucos_h.OS_Q /\
         struct_type_vallist_match os_ucos_h.OS_Q osq /\
                 struct_type_vallist_match os_ucos_h.OS_Q osq'
        ).
  split.
  eapply AOSQCtr_osq_eq with (M:=M); eauto; mem_join_sub_solver.
  unfold AOSQCtr in H4, H16; unfold node in H4, H16; simpl_sat H4; simpl_sat H16; simpljoin1.
  split; auto.
  simpljoin1; simpl in H2.
  assert(exists t1 t2 t3 t4 t5 t6 t7 t8, osq = t1::t2::t3::t4::t5::t6::t7::t8::nil).
  eapply struct_type_vallist_match_os_q; eauto.
  assert(exists t1 t2 t3 t4 t5 t6 t7 t8, osq' = t1::t2::t3::t4::t5::t6::t7::t8::nil).
  eapply struct_type_vallist_match_os_q; eauto.
  simpljoin1.
  simpl in H2; simpljoin1; unfold V_qfreeblk in H9, H21; simpl nth_val in H9, H21;
  inverts H9; inverts H21.
  
  lets Hx1: AOSQCtr_precise' H16 H4.
  lets Hx2: AOSQBlk_precise' H22 H10.
  simpljoin1.
  mem_eq_solver M.
  
  eapply AOSQCtr_osabst_emp in H16.
  eapply AOSQCtr_osabst_emp in H4.
  eapply AOSQBlk_osabst_emp in H22.
  eapply AOSQBlk_osabst_emp in H10.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H15 a0; pose proof H3 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a0);
    destruct(OSAbstMod.get o2 a0);
    tryfalse; auto.
Qed.

Lemma AMsgData_precise :
  forall l osq osq' osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AMsgData l osq osqblk msgtbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AMsgData l osq' osqblk' msgtbl' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l osq osq' osqblk osqblk' msgtbl msgtbl' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AMsgData_precise';eauto.
Qed.

Lemma AEventData_precise' :
  forall osevent osevent' d d' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AEventData osevent d ->
    (e, e0, M2, i, ier, lo, o2, a) |= AEventData osevent' d' ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AEventData; intros.
  simpl in H1.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8, osevent = v1::v2::v3::v4::v5::v6::v7::v8::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  assert(exists t1 t2 t3 t4 t5 t6 t7 t8, osevent' = t1::t2::t3::t4::t5::t6::t7::t8::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  simpljoin1.
  simpl in H1; simpljoin1; unfold V_OSEventType in *; simpl nth_val in *. 
  destruct d, d'; simpl_sat H; simpl_sat H0; simpljoin1;
  try solve [un_eq_event_type_solver];
  try solve [simpljoin1; intros; auto].
  unfold V_OSEventPtr, V_OSEventCnt in *; simpl nth_val in *.
  inverts H20; inverts H25; inverts H6; inverts H11.
  eapply AMsgData_precise'; eauto.
Qed.

Lemma AEventData_precise :
  forall osevent osevent' d d' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AEventData osevent d ->
    (e, e0, M2, i, ier, lo, o2, a) |= AEventData osevent' d' ->
    struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent ->
    struct_type_vallist_match os_ucos_h.OS_EVENT osevent' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros osevent osevent' d d' e e0 M1 M2 i ier lo o1 o2 a H H0 H1 H2 H3.
  eapply precise'2precise;eauto.
  eapply AEventData_precise';eauto.
Qed.

Lemma AEventNode_precise' :
  forall l osevent osevent' etbl etbl' petbl petbl' d d' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AEventNode l osevent etbl petbl d ->
    (e, e0, M2, i, ier, lo, o2, a) |= AEventNode l osevent' etbl' petbl' d' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AEventNode; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  
  simpljoin1; split; intros.
  assert(struct_atom_val_eq osevent osevent' os_ucos_h.OS_EVENT /\
         struct_type_vallist_match os_ucos_h.OS_EVENT osevent /\
         struct_type_vallist_match os_ucos_h.OS_EVENT osevent'
        ).
  split.
  eapply AOSEvent_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
  unfold AOSEvent in H9, H4; unfold node in H9, H4.
  simpl_sat H9; simpl_sat H4; simpljoin1; auto.
  simpljoin1.
  
  lets Hx1: AEventData_precise' H10 H5 H2 H7 H11.
  lets Hx2: AOSEvent_precise' H9 H4.
  simpljoin1.
  mem_eq_solver M.
  
  apply AOSEvent_osabst_emp in H9;
    apply AOSEvent_osabst_emp in H4;
    apply AEventData_osabst_emp in H10;
    apply AEventData_osabst_emp in H5.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H3 a0; pose proof H8 a0.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o2 a0);
    destruct(OSAbstMod.get o1 a0);
    tryfalse; auto.
Qed.

Lemma AEventNode_precise :
  forall l osevent osevent' etbl etbl' petbl petbl' d d' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AEventNode l osevent etbl petbl d ->
    (e, e0, M2, i, ier, lo, o2, a) |= AEventNode l osevent' etbl' petbl' d' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l osevent osevent' etbl etbl' petbl petbl' d d' e e0 M1 M2 i ier lo o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply AEventNode_precise';eauto.
Qed.

Lemma evsllseg_precise' :
  forall ectrl ectrl' msgql msgql' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= evsllseg head Vnull ectrl msgql ->
    (e, e0, M2, i, ier, l, o2, a) |= evsllseg head Vnull ectrl' msgql' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions ectrl; intros.
  simpl in H; simpljoin1.
  destruct ectrl'.
  simpl in H0; simpljoin1; auto.
  unfold evsllseg in H0; fold evsllseg in H0; destruct msgql'; tryfalse; destruct e1; destruct p.
  unfold AEventNode in H0; simpl in H0; simpljoin1; tryfalse.
  destruct ectrl'.
  simpl in H0; simpljoin1.
  unfold evsllseg in H; fold evsllseg in H; destruct msgql; tryfalse; destruct a; destruct p.
  unfold AEventNode in H; simpl in H; simpljoin1; tryfalse.
  
  unfold evsllseg in H, H0;  fold evsllseg in H, H0.
  destruct msgql; destruct msgql'; tryfalse; destruct a, e1, p ,p0.
  destruct H, H0;
    simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  simpljoin1; split; intros.
  assert(
      struct_atom_val_eq v1 v3 os_ucos_h.OS_EVENT /\
      struct_type_vallist_match os_ucos_h.OS_EVENT v1 /\
      struct_type_vallist_match os_ucos_h.OS_EVENT v3
    ).
  split.

  eapply AEventNode_osevent_eq with (M:=M); eauto; mem_join_sub_solver.
  split;
    unfold AEventNode in H9, H13; unfold AOSEvent in H9, H13; unfold node in H9, H13;
    simpl_sat H9; simpl_sat H13; simpljoin1; auto.
  simpljoin1.
  simpl in H1.
  assert(exists v1' v2 v3 v4 v5 v6 v7 v8, v1 = v1'::v2::v3::v4::v5::v6::v7::v8::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8, v3 = a1::a2::a3::a4::a5::a6::a7::a8::nil).
  eapply struct_type_vallist_match_os_event; eauto.
  simpljoin1.
  simpl in H1; simpljoin1; unfold V_OSEventListPtr in *; simpl nth_val in *; inverts H3; inverts H4.
  lets Hx1: AEventNode_precise' H9 H13.
  lets Hx2: IHectrl H10 H14.
  simpljoin1.
  mem_eq_solver M.

  apply AEventNode_osabst_emp in H9;
    apply AEventNode_osabst_emp in H13;
    apply evsllseg_osabst_emp in H10;
    apply evsllseg_osabst_emp in H14.
  substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H12 a; pose proof H8 a.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a); destruct(OSAbstMod.get o2 a); tryfalse; auto.
Qed.

Lemma evsllseg_precise :
  forall ectrl ectrl' msgql msgql' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= evsllseg head Vnull ectrl msgql ->
    (e, e0, M2, i, ier, l, o2, a) |= evsllseg head Vnull ectrl' msgql' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ectrl ectrl' msgql msgql' head e e0 M1 M2 i ier l o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply evsllseg_precise';eauto.
Qed.

Lemma AECBList_precise' :
  forall ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AECBList ectrl msgql ecbls tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= AECBList ectrl' msgql' ecbls' tcbls' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AECBList; intros.
  simpl in H, H0; simpljoin1.
  rewrite H16 in H37; inverts H37.
  split; intros.
  assert(x = x6).
  assert(isptr x).
  eapply evsllseg_isptr; eauto.
  assert(isptr x6).
  eapply evsllseg_isptr; eauto.
  destruct x, x6; auto;
  try(unfolds in H1; destruct H1; simpljoin1; tryfalse);
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse).
  unfolds in H17; simpljoin1; simpl in H3; simpljoin1.
  unfolds in H38; simpljoin1; simpl in H13; destruct a0; simpl in H13; simpljoin1.
  clear - H3 H13 H2 H10 H H0 H8 H29.
  unfold ptomval in H3; unfold ptomval in H13; substs.
  assert(sub x27 M) by mem_join_sub_solver.
  assert(sub x13 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H2 H1 H3; tryfalse.
  
  unfolds in H17; simpljoin1; simpl in H3; destruct a0; simpl in H3; simpljoin1.
  unfolds in H38; simpljoin1; simpl in H13; simpljoin1.
  clear - H3 H13 H2 H10 H H0 H8 H29.
  unfold ptomval in H3; unfold ptomval in H13; substs.
  assert(sub x27 M) by mem_join_sub_solver.
  assert(sub x13 M) by mem_join_sub_solver.
  lets Hx: mem_join_sig_sub_eq H10 H2 H1 H3; tryfalse.
  
  inverts H1; inverts H2.
  assert(sub x13 M).
  apply join_sub_l in H8.
  eapply sub_trans; eauto.
  assert(sub x27 M).
  apply join_sub_l in H29.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_true_vptr_eq H17 H38 H1 H2; simpljoin1.
  substs.

  assert(x13 = x27).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  
  
  lets Hx: evsllseg_precise' H33 H12; simpljoin1.
  mem_eq_solver M.

  apply evsllseg_osabst_emp in H33; 
    apply evsllseg_osabst_emp in H12; substs; auto.
Qed.

Lemma AECBList_precise :
  forall ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AECBList ectrl msgql ecbls tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= AECBList ectrl' msgql' ecbls' tcbls' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ectrl ectrl' msgql msgql' ecbls ecbls' tcbls tcbls' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AECBList_precise';eauto.
Qed.

Lemma AOSMapTbl_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSMapTbl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSMapTbl ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSMapTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9, H4; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H9.
  unfold addrval_to_addr in H9; destruct x, x6; inverts H9.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma AOSMapTbl_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSMapTbl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSMapTbl ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSMapTbl_precise';eauto.
Qed.

Lemma AOSUnMapTbl_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSUnMapTbl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSUnMapTbl ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSUnMapTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9, H4; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H9.
  unfold addrval_to_addr in H9; destruct x, x6; inverts H9.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma AOSUnMapTbl_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSUnMapTbl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSUnMapTbl ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSUnMapTbl_precise';eauto.
Qed.

Lemma AOSTCBPrioTbl_precise' :
  forall ptbl ptbl' rtbl rtbl' tcbls tcbls' ptls ptls' vhold vhold' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBPrioTbl ptbl' rtbl' tcbls' ptls' vhold' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSTCBPrioTbl; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H99, H49; simpljoin1. (* change H73,H36 -> H99,H49 *)
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H7. (* change H6 -> H7 *)
  unfold addrval_to_addr in H7; destruct x61, x17; inverts H7. (* change H6 -> H7, x49 -> x61 *)
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H5; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  simpl in H94, H44; simpljoin1. (* change H68,H31 -> H94,H44 *)
  rewrite H4 in H; inverts H.
  simpljoin1; split; intros.
  simpl in H95, H45; simpljoin1. (* change H69,H32 -> H95,H45 *)
  assert(x55 = x11). (* change x6,x0 -> x55, x11 *)
  rewrite <- H7 in H11. (* change H6,H9 -> H7,H11 *)
  unfold addrval_to_addr in H11; destruct vhold, vhold'. (* change H9 -> H11 *)
  inverts H11. (* change H9 -> H11 *)
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i2)).
  rewrite H13; auto. (* change H11 -> H13 *)
  do 2 rewrite Int.repr_unsigned in H8; substs. (* change H3 -> H8 *)
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  lets Hx: Aarray_precise' H100 H50; simpljoin1. (* change H74,H37 -> H100,H50 *)
  eapply eq_join_eq; eauto.
  apply H8 with (M:=M); mem_join_sub_solver. (* change H3 -> H8 *)
  simpl in H81,H31; simpljoin1. (* new add *)
  apply Aarray_osabst_emp in H100; apply Aarray_osabst_emp in H50; substs. (* change H74,H37 -> H100,H50 *)
  simpl in H95, H45; simpljoin1. (* change H69,H32 -> H95,H45 *)
  simpl in H81,H31; simpljoin1. (* new add *)
  lets Hx: osabst_sub_sig_eq H H5. (* new add *)
  rewrite Hx; auto. (* new add *)
Qed.

Lemma AOSTCBPrioTbl_precise :
  forall ptbl ptbl' rtbl rtbl' tcbls tcbls' ptls ptls' vhold vhold' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBPrioTbl ptbl' rtbl' tcbls' ptls' vhold' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros ptbl ptbl' rtbl rtbl' tcbls tcbls' ptls ptls' vhold vhold' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSTCBPrioTbl_precise';eauto.
Qed.
 
Lemma AOSIntNesting_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSIntNesting ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSIntNesting->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSIntNesting; intros.
  simpl in H, H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AOSIntNesting_precise :
forall e e0 i ier l a M1 M2 o1 o2,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIntNesting ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIntNesting ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSIntNesting_precise';eauto.
Qed.

(*
Lemma AOSRunning_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSRunning ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSRunning ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSRunning; intros.
  simpl in H, H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AOSRunning_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSRunning ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSRunning ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSRunning_precise';eauto.
Qed.

Lemma AOSLockNesting_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSLockNesting ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSLockNesting ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSLockNesting; intros.
  simpl in H, H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AOSLockNesting_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSLockNesting ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSLockNesting ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSLockNesting_precise';eauto.
Qed.

Lemma AIntNumCurrent_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 v1 v2,
    (e, e0, M1, i, ier, l, o1, a) |= AIntNumCurrent (Vint32 v1) ->
    (e, e0, M2, i, ier, l, o2, a) |= AIntNumCurrent (Vint32 v2) ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AIntNumCurrent; intros.
  simpl in H, H0; simpljoin1;
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros; auto.
  lets Hx: mapstoval_false_rule_type_val_match_eq H5 H14 H0 H; simpl; auto.
  simpljoin1.
Qed.

Lemma AIntNumCurrent_precise :
  forall e e0 i ier l a M1 M2 o1 o2 v1 v2,
    (e, e0, M1, i, ier, l, o1, a) |= AIntNumCurrent (Vint32 v1) ->
    (e, e0, M2, i, ier, l, o2, a) |= AIntNumCurrent (Vint32 v2) ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 v1 v2 H H0.
  eapply precise'2precise;eauto.
  eapply AIntNumCurrent_precise';eauto.
Qed.
*)

Lemma AOSRdyTblGrp_precise' :
  forall rtbl rtbl' rgrp rgrp' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSRdyTblGrp rtbl rgrp ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSRdyTblGrp rtbl' rgrp' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSRdyTblGrp; unfold AOSRdyTbl; unfold AOSRdyGrp; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.

  simpl in H65, H32; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H2 in H6.
  unfold addrval_to_addr in H6; destruct x54, x29.
  inverts H6.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H5; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  
  simpl in H50, H17; simpljoin1.
  rewrite H21 in H9; inverts H9.
  simpljoin1; split; intros.
  assert(sub x6 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  lets Hx': mapstoval_true_rule_type_val_match_eq H51 H18 H22 H11 H4; lets Hx: Hx' H5; clear Hx'.
  simpljoin1.
  
  lets Hx: Aarray_precise' H33 H66; simpljoin1.
  eapply eq_join_eq; eauto.
  symmetry.
  mem_eq_solver M.
  
  apply Aarray_osabst_emp in H33; apply Aarray_osabst_emp in H66.
  substs; auto.
Qed.

Lemma AOSRdyTblGrp_precise :
  forall rtbl rtbl' rgrp rgrp' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSRdyTblGrp rtbl rgrp ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSRdyTblGrp rtbl' rgrp' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros rtbl rtbl' rgrp rgrp' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSRdyTblGrp_precise';eauto.
Qed.

Lemma AOSTime_precise' :
  forall t t' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTime (Vint32 t) ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTime (Vint32 t') ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSTime; intros.
  simpl in H, H0; simpljoin1;
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros; auto.
  lets Hx: mapstoval_true_rule_type_val_match_eq H5 H14 H0 H; simpl; auto.
  simpljoin1.
Qed.

Lemma AOSTime_precise :
  forall t t' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTime (Vint32 t) ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTime (Vint32 t') ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros t t' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSTime_precise';eauto.
Qed.

Lemma Aabsdata_precise' :
  forall id absdata absdata' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= Aabsdata id absdata ->
    (e, e0, M2, i, ier, l, o2, a) |= Aabsdata id absdata' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros; simpl in H, H0.
  simpljoin1; split; intros; auto.
  lets Hx: osabst_sub_sig_eq H H0.
  substs; auto.
Qed.

Lemma Aabsdata_precise :
  forall id absdata absdata' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= Aabsdata id absdata ->
    (e, e0, M2, i, ier, l, o2, a) |= Aabsdata id absdata' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros id absdata absdata' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply Aabsdata_precise';eauto.
Qed.

Lemma AGVars_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AGVars ->
    (e, e0, M2, i, ier, l, o2, a) |= AGVars ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AGVars; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.

  simpl in H78, H4; simpljoin1.
  rewrite H25 in H7; inverts H7.
  
  simpl in H88, H14; simpljoin1.
  rewrite H24 in H5; inverts H5.

  simpl in H93,  H19; simpljoin1.
  rewrite H22 in H5; inverts H5.

  simpl in H103, H29; simpljoin1.
  rewrite H29 in H5; inverts H5.

  simpl in H108, H34; simpljoin1.
  rewrite H34 in H5; inverts H5.

  simpl in H113, H39; simpljoin1.
  rewrite H39 in H5; inverts H5.

  simpl in H123, H49; simpljoin1.
  rewrite H42 in H5; inverts H5.

  simpl in H118, H44; simpljoin1.
  rewrite H47 in H5; inverts H5.

  simpl in H128, H54; simpljoin1.
  rewrite H49 in H5; inverts H5.

  simpl in H145, H71; simpljoin1.
  rewrite H53 in H5; inverts H5.

  simpl in H133, H59; simpljoin1.
  rewrite H55 in H5; inverts H5.

  simpl in H138, H64; simpljoin1.
  rewrite H59 in H5; inverts H5.

  simpl in H134, H60; simpljoin1.
  rewrite H60 in H5; inverts H5.

  simpljoin1; split; intros.

  (*x32*)
  lets Hx1: mapstoval_true_mem_eq M H9 H27.
  mem_join_sub_solver.
  mem_join_sub_solver.

  (*x20*)
  lets Hx2: mapstoval_true_mem_eq M H7 H30.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx3: mapstoval_true_mem_eq M H10 H32.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx4: mapstoval_true_mem_eq M H12 H35.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx5: mapstoval_true_mem_eq M H13 H37.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx6: mapstoval_true_mem_eq M H19 H54.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx7: mapstoval_true_mem_eq M H20 H61.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx8: mapstoval_true_mem_eq M H14 H40.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx9: mapstoval_true_mem_eq M H17 H48.
  mem_join_sub_solver.
  mem_join_sub_solver.
  
  lets Hx10: mapstoval_true_mem_eq M H15 H45.
  mem_join_sub_solver.
  mem_join_sub_solver.
  
  lets Hx11: mapstoval_true_mem_eq M H18 H50.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx12: mapstoval_true_mem_eq M H8 H57.
  mem_join_sub_solver.
  mem_join_sub_solver.

  lets Hx13: mapstoval_true_mem_eq M H23 H62.
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  repeat (eapply eq_join_eq; eauto).

  auto.
Qed.

Lemma AGVars_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AGVars ->
    (e, e0, M2, i, ier, l, o2, a) |= AGVars ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AGVars_precise';eauto.
Qed.

Lemma A_isr_is_prop_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= A_isr_is_prop ->
    (e, e0, M2, i, ier, l, o2, a) |= A_isr_is_prop ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold A_isr_is_prop; intros.
  simpl in H, H0; simpljoin1; intros; auto.
Qed.

Lemma A_isr_is_prop_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= A_isr_is_prop ->
    (e, e0, M2, i, ier, l, o2, a) |= A_isr_is_prop ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply A_isr_is_prop_precise';eauto.
Qed.

Lemma AOSExchandler_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 exchandler exchandler',
    (e, e0, M1, i, ier, l, o1, a) |= AOSExchandler (Vint32 exchandler) ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSExchandler (Vint32 exchandler') ->
    (forall M : mem,
      sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
      sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSExchandler; intros.
  simpl in H, H0; simpljoin1;
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros; auto.
  lets Hx: mapstoval_true_rule_type_val_match_eq H5 H14 H0 H; simpl; auto.
  simpljoin1.
Qed.

Lemma AOSExchandler_precise :
  forall e e0 i ier l a M1 M2 o1 o2 exchandler exchandler',
    (e, e0, M1, i, ier, l, o1, a) |= AOSExchandler (Vint32 exchandler) ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSExchandler (Vint32 exchandler') ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 exchandler exchandler' H H0.
  eapply precise'2precise;eauto.
  eapply AOSExchandler_precise';eauto.
Qed.

Lemma AOSInthandlerParam_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 inthandlerParam inthandlerParam',
    (e, e0, M1, i, ier, l, o1, a) |= AOSInthandlerParam inthandlerParam ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSInthandlerParam inthandlerParam' ->
    (forall M : mem,
      sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
      sub o1 o -> sub o2 o -> o1 = o2).
Proof.
    unfold AOSInthandlerParam; unfold GAarray; intros.
    simpl_sat H; simpl_sat H0; simpljoin1.
    simpl in H9, H4; simpljoin1.
    rewrite H0 in H; inverts H.
    rewrite <- H2 in H9.
    unfold addrval_to_addr in H9. destruct x6, x. inverts H9.
    assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
    rewrite H3; auto.
    do 2 rewrite Int.repr_unsigned in H; substs.
    eapply Aarray_precise'; eauto.
Qed.

Lemma AOSInthandlerParam_precise :
  forall e e0 i ier l a M1 M2 o1 o2 inthandlerParam inthandlerParam',
    (e, e0, M1, i, ier, l, o1, a) |= AOSInthandlerParam inthandlerParam ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSInthandlerParam inthandlerParam' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 inthandlerParam inthandlerParam' H H0.
  eapply precise'2precise;eauto.
  eapply AOSInthandlerParam_precise';eauto.
Qed.

Lemma AOSInthandler_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 inthandler inthandler',
    (e, e0, M1, i, ier, l, o1, a) |= AOSInthandler inthandler ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSInthandler inthandler' ->
    (forall M : mem,
      sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
      sub o1 o -> sub o2 o -> o1 = o2).
Proof.
    unfold AOSInthandler; unfold GAarray; intros.
    simpl_sat H; simpl_sat H0; simpljoin1.
    simpl in H9, H4; simpljoin1.
    rewrite H0 in H; inverts H.
    rewrite <- H2 in H9.
    unfold addrval_to_addr in H9. destruct x6, x. inverts H9.
    assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
    rewrite H3; auto.
    do 2 rewrite Int.repr_unsigned in H; substs.
    eapply Aarray_precise'; eauto.
Qed.

Lemma AOSInthandler_precise :
  forall e e0 i ier l a M1 M2 o1 o2 inthandler inthandler',
    (e, e0, M1, i, ier, l, o1, a) |= AOSInthandler inthandler ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSInthandler inthandler' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 inthandlerParam inthandlerParam' H H0.
  eapply precise'2precise;eauto.
  eapply AOSInthandler_precise';eauto.
Qed.


Lemma AOSTCBList_vptr :
  forall s p1 p2 tcbl1 tcbcur tcbl2 rtbl ct tcbls,
    s |= AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ->
    (exists x, p1 = Vptr x).
Proof.
  unfold AOSTCBList; intros.
  destruct_s s.
  simpl_sat H; simpljoin1.
  destruct tcbl1.
  simpl in H8; simpljoin1; eauto.
  unfold tcbdllseg in H8; unfold dllseg in H8; fold dllseg in H8.
  simpl_sat H8; simpljoin1.
  unfold node in H29; simpl_sat H29; simpljoin1.
  eauto.
Qed.

Lemma tcbdllseg_compose:
  forall s P h hp t1 tn1 t2 tn2 l1 l2,
    s |= tcbdllseg h hp t1 tn1 l1 ** tcbdllseg tn1 t1 t2 tn2 l2 ** P->
    s |= tcbdllseg h hp t2 tn2 (l1++l2) ** P.
Proof.
  intros.

  generalize s P h hp t1 tn1 t2 tn2 l2 H.
  clear s P h hp t1 tn1 t2 tn2 l2 H.
  induction l1.
  intros.
  unfold tcbdllseg in H.
  unfold dllseg in H.
  fold dllseg in H.
  sep split in H.
  subst.
  simpl; auto.
  intros.
  simpl ( (a::l1) ++l2).

  unfold tcbdllseg in *.
  unfold dllseg in *.
  fold dllseg in *.
  sep normal.
  
  sep auto.
  assert (s
      |= dllseg x h t1 tn1 l1 OS_TCB_flag V_OSTCBPrev V_OSTCBNext **
      dllseg tn1 t1 t2 tn2 l2 OS_TCB_flag V_OSTCBPrev V_OSTCBNext ** Aemp).
  sep auto.
  eapply IHl1 in H3.
  sep auto.
  auto.
Qed.

Lemma struct_type_vallist_match_os_tcb :
  forall v, struct_type_vallist_match os_ucos_h.OS_TCB v ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
            exists v11 v12 v13 v14 v15 v16 v17 v18,
              v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: v12 :: v13 :: v14 :: v15 :: v16 :: v17 :: v18 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_TCB in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; simpljoin1; tryfalse.
  destruct v8; simpljoin1; tryfalse.
  destruct v9; simpljoin1; tryfalse.
  destruct v10; simpljoin1; tryfalse.
  destruct v11; simpljoin1; tryfalse.
  destruct v12; simpljoin1; tryfalse.
  destruct v13; simpljoin1; tryfalse.
  destruct v14; simpljoin1; tryfalse.
  destruct v15; simpljoin1; tryfalse.
  destruct v16; simpljoin1; tryfalse.
  destruct v17; simpljoin1; tryfalse.
  repeat eexists. 
Qed.

Lemma dllseg_osabst_emp :
  forall l head headprev tail tailnext t prev next e e0 M i ier lo o a0,
    (e, e0, M, i, ier, lo, o, a0) |= dllseg head headprev tail tailnext l t prev next -> o = empabst.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  unfold dllseg in H; fold dllseg in H; simpl_sat H; simpljoin1.
  apply node_osabst_emp in H18; substs.
  eapply IHl in H19; substs.
  apply OSAbstMod.extensionality; intros.
  pose proof H17 a1.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o a1); tryfalse; auto.
Qed.

(*current backup is inv_prop_bak3.v*)

Lemma disj_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 P P' Q Q',
    ((e, e0, M1, i, ier, l, o1, a) |= P /\
     (e, e0, M2, i, ier, l, o2, a) |= Q' -> False) ->
    ((e, e0, M1, i, ier, l, o1, a) |= Q /\
     (e, e0, M2, i, ier, l, o2, a) |= P' -> False) ->
    (
      forall e e0 i ier l a M1 M2 o1 o2,
        (e, e0, M1, i, ier, l, o1, a) |= P ->
        (e, e0, M2, i, ier, l, o2, a) |= P' ->
        (forall M : mem,
            sub M1 M -> sub M2 M -> M1 = M2) /\
        (forall o : osabst,
            sub o1 o -> sub o2 o -> o1 = o2)
    ) ->
    (
      forall e e0 i ier l a M1 M2 o1 o2,
        (e, e0, M1, i, ier, l, o1, a) |= Q ->
        (e, e0, M2, i, ier, l, o2, a) |= Q' ->
        (forall M : mem,
            sub M1 M -> sub M2 M -> M1 = M2) /\
        (forall o : osabst,
            sub o1 o -> sub o2 o -> o1 = o2)
    ) ->
    (e, e0, M1, i, ier, l, o1, a) |= P \\// Q ->
    (e, e0, M2, i, ier, l, o2, a) |= P' \\// Q' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  destruct H3; destruct H4.

  eapply H1; eauto.
  false; eapply H; eauto.
  false; eapply H0; eauto.
  eapply H2; eauto.
Qed.

Lemma AOSTCBFreeList'_isptr :
  forall s p l ct tcbls,
    s |= AOSTCBFreeList' p l ct tcbls ->
    isptr p.
Proof.
  intros.
  unfold AOSTCBFreeList' in H.
  destruct_s s.
  simpl_sat H; simpljoin1.
  destruct H4.
  unfold TCBFree_Not_Eq in H.
  simpl_sat H; simpljoin1.
  destruct l.
  simpl in H11; simpljoin1.
  unfolds; auto.
  unfold assertion.sll in H11.
  unfold sllseg in H11; fold sllseg in H11.
  sep split in H11.
  destruct H11.
  simpl_sat H1; simpljoin1.
  unfold node in H16; destruct H16.
  sep split in H1; simpljoin1.
  unfolds; eauto.

  unfold TCBFree_Eq in H.
  sep normal in H.
  sep destruct H.
  (* do 3 destruct H. *)
  sep split in H; simpljoin1.
  unfolds; eauto.
Qed.

Lemma mapstoval_vnull_vptr_mem_sub_false :
  forall l a x m m' M,
    mapstoval l (Tptr a) true Vnull m ->
    mapstoval l (Tptr a) true (Vptr x) m' ->
    sub m M -> sub m' M ->
    False.
Proof.
  intros.
  unfold mapstoval in H, H0; simpljoin1.
  simpl in H3, H4.
  destruct x, l.
  simpljoin1.
  simpl in H3; simpljoin1.
  assert(sub x M).
  mem_join_sub_solver.
  assert(sub x5 M).
  mem_join_sub_solver.
  unfold ptomval in H8, H0.
  substs.
  assert (get M (b0, o) = Some (true, MNull)).
  clear - H14.

  eapply mem_sub_sig_true_get; eauto.
  assert (get M (b0, o) = Some (true, Pointer b i 3)).
  clear - H16.
  eapply mem_sub_sig_true_get; eauto.
  rewrite H0 in H8; tryfalse.
Qed.

Lemma struct_type_vallist_match_os_tcb_flag :
  forall v, struct_type_vallist_match OS_TCB_flag v ->
            exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 :: v11 :: nil.
Proof.
  intros.
  unfold OS_TCB_flag in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  destruct v7; simpljoin1; tryfalse.
  destruct v8; simpljoin1; tryfalse.
  destruct v9; simpljoin1; tryfalse.
  destruct v10; simpljoin1; tryfalse.
  do 11 eexists; eauto.
Qed.

Lemma ostcb_flag_sll_precise' :
  forall lfree lfree' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head lfree OS_TCB_flag V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head lfree' OS_TCB_flag V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions lfree; intros.
  simpl in H; simpljoin1.
  destruct lfree'.
  simpl in H0; simpljoin1; auto.
  unfold sll in H0; unfold sllseg in H0; fold sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct lfree'.
  simpl in H0; simpljoin1.
  unfold sll in H; unfold sllseg in H; fold sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold sll in H, H0; unfold sllseg in H, H0; fold sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  lets Hx: node_precise' H14 H19.
  
  unfold sll in IHlfree.
  simpljoin1; split; intros.
  assert(x5 = x6).
  assert(sub x12 M) by mem_join_sub_solver.
  assert(sub x17 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H14 H19 H5 H6.
  simpl in Hx; unfold V_OSEventListPtr in H9, H10.
  unfold node in H14, H19.
  destruct H14, H19; sep split in H7; sep split in H8; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, exists a11, a = a1::a2::a3::a4::a5::a6::a7::a8::a9::a10::a11::nil).
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  simpljoin1; simpl in Hx; simpl in H9, H10; simpljoin1; inversion H9; inversion H10; substs; auto.
  substs.
  
  lets Hx2: IHlfree H15 H20.
  simpljoin1; mem_eq_solver M.
  
  eapply sllseg_osabst_emp in H15.
  eapply sllseg_osabst_emp in H20.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma ostcb_flag_sll_precise :
  forall lfree lfree' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head lfree OS_TCB_flag V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head lfree' OS_TCB_flag V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros lfree lfree' head e e0 M1 M2 i ier l o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply ostcb_flag_sll_precise';eauto.
Qed.

Fixpoint tcb_linked_list_same_next (vl1 vl2 : list vallist) :=
  match vl1, vl2 with
  | nil, nil => True
  | h1::vl1', h2::vl2' =>
    match (V_OSTCBNext h1), (V_OSTCBNext h2) with
    | (Some a1), (Some a2) => a1 = a2 /\ tcb_linked_list_same_next vl1' vl2'
    | _, _ => False
    end
  | _, _ => False
  end.
Lemma struct_atom_val_eq_V_OSTCBNext_eq :
  forall vl1 vl2 x1 x2,
    struct_atom_val_eq vl1 vl2 OS_TCB_flag ->
    V_OSTCBNext vl1 = Some x1 ->
    V_OSTCBNext vl2 = Some x2 ->
    x1 = x2.
Proof.
  intros.
  destruct vl1;
    unfolds in H0; simpl in H0; tryfalse.
  destruct vl2;
    unfolds in H1; simpl in H1; tryfalse.
  inverts H0; inverts H1.
  simpl in H; simpljoin1.
Qed.

Lemma tcb_linked_list_same_next_intro :
  forall vl vl' p e e0 m i ier l o1 o2 a,
    (e, e0, m, i, ier, l, o1, a) |= assertion.sll p vl OS_TCB_flag V_OSTCBNext ->
    (e, e0, m, i, ier, l, o2, a) |= assertion.sll p vl' OS_TCB_flag V_OSTCBNext ->
    tcb_linked_list_same_next vl vl'.
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl; auto.

  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep split in H; sep split in H0; tryfalse.

  destruct vl'.
  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep split in H; sep split in H0; tryfalse.

  unfold assertion.sll in H, H0.
  unfold sllseg in *; fold sllseg in *.
  sep normal in H; sep normal in H0.
  destruct H, H0.
  sep split in H; sep split in H0.
  unfold tcb_linked_list_same_next; fold tcb_linked_list_same_next.
  rewrite H1, H3.
  simpl_sat H; simpl_sat H0; simpljoin1.
  assert (sub x1 m).
  eapply join_sub_l; eauto.
  assert (sub x7 m).
  eapply join_sub_l; eauto.
  lets Hx: node_vl_eq H8 H13 H H0.
  assert (x = x0).
  clear - H1 H3 Hx.
  symmetry.
  eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.

  substs.
  split; auto.
  lets Hx1: ostcb_flag_sll_precise' H9 H14.
  destruct Hx1.
  assert (sub x2 m).
  eapply join_sub_r; eauto.
  assert (sub x8 m).
  eapply join_sub_r; eauto.
  lets Hx1: H6 H15 H16.
  substs.
  eapply IHvl; eauto.
Qed.
    
Lemma sllfreeflag_precise' :
  forall vl vl' p e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= sllfreeflag p vl ->
    (e, e0, M2, i, ier, l, o2, a) |= sllfreeflag p vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl in H0, H1; simpljoin1.
  split; intros; auto.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H0.
  sep destruct H1; sep split in H1.
  (* do 2 destruct H1; sep split in H1. *)
  substs; tryfalse.

  destruct vl'.
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H1.
  sep destruct H0; sep split in H0.
  (* do 2 destruct H0; sep split in H0. *)
  substs; tryfalse.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep destruct H0. sep destruct H1.
  (* do 2 destruct H0, H1. *)
  sep split in H0; sep split in H1.
  substs; inverts H4.
  
  (* rearrange H1 and H0 *)
  remember H0 as H0'.
  clear HeqH0' H0.
  remember H0' as H0.
  clear HeqH0 H0'.
  
  simpl_sat H0; simpl_sat H1; simpljoin1.

  unfold tcb_linked_list_same_next in H; fold tcb_linked_list_same_next in H.
  rewrite H3 in H.
  rewrite H5 in H.
  simpljoin1.

  lets Hx: IHvl H0 H28 H53.
  (* lets Hx: IHvl H0 H8 H13. *)
  split; intros.
  destruct Hx.
  assert (sub x41 M). 
  (* assert (sub x3 M). *)
  mem_join_sub_solver.
  assert (sub x65 M).
  (* assert (sub x9 M). *)
  mem_join_sub_solver.
  lets Hx1: H4 H10 H13.
  substs.
  assert (x = x16).
  {
    simpl in H32, H7; simpljoin1.
    assert (Hsub1': sub x M).
    mem_join_sub_solver.
    assert (Hsub2': sub x16 M).
    mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.
  assert (x22 = x46).
  {
    simpl in H37, H12; simpljoin1.
    assert (Hsub1': sub x22 M) by mem_join_sub_solver.
    assert (Hsub2': sub x46 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.
  assert (x28 = x52).
  {
    simpl in H42, H17; simpljoin1.
    assert (Hsub1': sub x28 M) by mem_join_sub_solver.
    assert (Hsub2': sub x52 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  substs.
  assert (x34 = x58).
  {
    simpl in H47, H22; simpljoin1.
    assert (Hsub1': sub x34 M) by mem_join_sub_solver.
    assert (Hsub2': sub x58 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  (* clear - H9 H2. *)
  (* eapply join_unique; eauto. *)
  substs.
  assert (x40 = x64).
  {
    simpl in H52, H27; simpljoin1.
    assert (Hsub1': sub x40 M) by mem_join_sub_solver.
    assert (Hsub2': sub x64 M) by mem_join_sub_solver.
    eapply mapstoval_true_mem_eq; eauto.
  }
  mem_eq_solver2.
  
  simpl in H7, H32; simpljoin1.
  simpl in H12, H37; simpljoin1.
  simpl in H17, H42; simpljoin1.
  simpl in H22, H47; simpljoin1.
  simpl in H27, H52; simpljoin1.
  eapply H8; eauto.
  (* simpl in H7, H12; simpljoin1. *)
  (* eapply H10; eauto. *)
Qed.

Lemma sllfreeflag_precise :
  forall vl vl' p e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= sllfreeflag p vl ->
    (e, e0, M2, i, ier, l, o2, a) |= sllfreeflag p vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p e e0 i ier l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply sllfreeflag_precise';eauto.
Qed.

Lemma sllfreeflag_osabst_emp :
  forall vl p e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= sllfreeflag p vl ->
    o = empabst.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin1.

  unfold sllfreeflag in *.
  unfold sllsegfreeflag in H; fold sllsegfreeflag in H.
  sep destruct H.
  sep split in H.
  simpl_sat H; simpljoin1.
  simpl in H5; simpljoin1.
  simpl in H10; simpljoin1.
  simpl in H15; simpljoin1.
  simpl in H20; simpljoin1.
  simpl in H25; simpljoin1.
  eapply IHvl; eauto.
Qed.

Lemma TCBFree_Not_Eq_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 p ct vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= TCBFree_Not_Eq p ct vl ->
    (e, e0, M2, i, ier, l, o2, a) |= TCBFree_Not_Eq p ct vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold TCBFree_Not_Eq in H, H0.
  sep split in H.
  sep split in H0.
  
  simpl_sat H; simpl_sat H0; simpljoin1.
  split; intros.
  assert(x5 = x).
  lets Hx: ostcb_flag_sll_precise' H11 H6.
  destruct Hx.
  apply H4 with (M:=M); mem_join_sub_solver.
  substs.

  lets Hx: tcb_linked_list_same_next_intro H11 H6.
  lets Hx1: sllfreeflag_precise' Hx H12 H7.
  destruct Hx1.
  assert (sub x6 M) by mem_join_sub_solver.
  assert (sub x0 M) by mem_join_sub_solver.
  lets Hx1: H4 H13 H14; substs.
  eapply join_unique; eauto.
  apply sll_osabst_emp in H11.
  apply sll_osabst_emp in H6.
  substs.
  eapply sllfreeflag_osabst_emp in H12. 
  eapply sllfreeflag_osabst_emp in H7.
  substs.
  eapply eq_join_eq; eauto.
Qed.

Lemma TCBFree_Not_Eq_precise :
  forall e e0 i ier l a M1 M2 o1 o2 p ct vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= TCBFree_Not_Eq p ct vl ->
    (e, e0, M2, i, ier, l, o2, a) |= TCBFree_Not_Eq p ct vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 p ct vl vl' H H0.
  eapply precise'2precise;eauto.
  eapply TCBFree_Not_Eq_precise';eauto.
Qed.

Lemma Astruct_vl_eq :
  forall vl vl' t l e e0 M1 M2 M i ier lo o1 o2 a,
    struct_type_vallist_match t vl -> struct_type_vallist_match t vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Astruct l t vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Astruct l t vl' ->
    sub M1 M -> sub M2 M ->
    struct_atom_val_eq vl vl' t.
Proof.
  intros.
  unfold struct_type_vallist_match in H, H0.
  destruct t; tryfalse.
  unfold Astruct in H1, H2.
  eapply Astruct'_vl_eq; eauto.
Qed.

Lemma TCBFree_Eq_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls',
    (e, e0, M1, i, ier, l, o1, a) |= TCBFree_Eq p ct vl tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= TCBFree_Eq p ct vl' tcbls' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold TCBFree_Eq in H, H0.
  do 3 destruct H; sep split in H.
  do 3 destruct H0; sep split in H0.
  simpl_sat H; simpl_sat H0; simpljoin1.

  split; intros.
  assert(x11 = x5).
  lets Hx: Astruct_precise' H48 H8; auto.
  (* lets Hx: Astruct_precise' H28 H8; auto. *)
  destruct Hx.
  eapply H1 with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  
  assert (x1 = x4).
  assert (sub x5 M).
  mem_join_sub_solver.
  lets Hx: Astruct_vl_eq H2 H4 H48 H8 H1.
  (* lets Hx: Astruct_vl_eq H2 H4 H28 H8 H1. *)
  lets Hx1: Hx H1; clear Hx.
  eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.
  substs.

  assert (x29 = x70).
  lets Hx: ostcb_flag_sll_precise' H23 H63.
  destruct Hx.
  eapply H1 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs. 

  assert (x30 = x71).
  lets Hx: tcb_linked_list_same_next_intro H23 H63.
  lets Hx1: sllfreeflag_precise' Hx H24 H64.
  destruct Hx1.
  eapply H1 with (M := M); auto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  
  assert (x58 = x17).
  {
    simpl in H53, H13.
    simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  assert (x80 = x39). 
  {
    simpl in H68, H28; simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.
  assert (x86 = x45).
  {
    simpl in H73, H33; simpljoin1. 
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.    
  }
  substs.
  assert (x92 = x51).
  {
    simpl in H78, H38; simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.    
  }
  substs.
  assert (x93 = x52).
  {
    simpl in H79, H39; simpljoin1.
    eapply mapstoval_false_mem_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.        
  }
  
  mem_eq_solver2.

  apply Astruct_osabst_emp in H8.
  apply Astruct_osabst_emp in H48.

  apply sllfreeflag_osabst_emp in H64.
  apply sllfreeflag_osabst_emp in H24.
  
  apply sll_osabst_emp in H63.
  apply sll_osabst_emp in H23.

  simpl in H53, H13; simpljoin1.
  simpl in H68, H28; simpljoin1.
  simpl in H73, H33; simpljoin1.
  simpl in H78, H38; simpljoin1.
  simpl in H79, H39; simpljoin1.
Qed.


Lemma TCBFree_Eq_precise :
  forall e e0 i ier l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls',
    (e, e0, M1, i, ier, l, o1, a) |= TCBFree_Eq p ct vl tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= TCBFree_Eq p ct vl' tcbls' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 p ct vl vl' tcbls tcbls' H H0.
  eapply precise'2precise;eauto.
  eapply TCBFree_Eq_precise';eauto.
Qed.

Lemma TCBFree_Not_Eq_osabst_emp :
  forall p ct vl e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |=TCBFree_Not_Eq p ct vl ->
    o = empabst.
Proof.
  intros.
  unfold TCBFree_Not_Eq in H.
  sep split in H.
  simpl_sat H; simpljoin1.
  apply sll_osabst_emp in H4.
  apply sllfreeflag_osabst_emp in H5.
  simpljoin1.
Qed.

Lemma TCBFree_Eq_osabst_emp :
  forall p ct vl e e0 M i ier lo o a tcbls,
    (e, e0, M, i, ier, lo, o, a) |= TCBFree_Eq p ct vl tcbls ->
    o = empabst.
Proof.
  intros.
  unfold TCBFree_Eq in H.
  do 3 destruct H.
  sep split in H.
  simpl_sat H; simpljoin1.
  apply sll_osabst_emp in H20.
  apply sllfreeflag_osabst_emp in H21.
  apply Astruct_osabst_emp in H5.
  simpl in H10; simpljoin1.
  simpl in H25; simpljoin1.
  simpl in H30; simpljoin1.
  simpl in H35; simpljoin1.
  simpl in H36; simpljoin1.
Qed.

(*should prove ct = ct' using HCurTCB*)
Lemma AOSTCBFreeList'_precise' :
  forall p p' vl vl' ct e e0 i ier l a M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBFreeList' p' vl' ct tcbls' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  assert(isptr p).
  eapply AOSTCBFreeList'_isptr; eauto.
  assert(isptr p').
  eapply AOSTCBFreeList'_isptr; eauto.
  unfold AOSTCBFreeList' in *.
  simpl_sat H.
  simpl_sat H0.
  simpljoin1.
  split; intros.
  assert (p = p' /\ x5 = x).
  simpl in H11, H6; simpljoin1.
  rewrite H23 in H14; inverts H14.
  destruct p, p';
    unfold isptr in H1, H2; destruct H1, H2; simpljoin1; tryfalse.
  split; auto.
  eapply mapstoval_true_mem_eq; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  false.
  eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  false.
  eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  assert (sub x M) by mem_join_sub_solver.
  assert (sub x5 M) by mem_join_sub_solver.
  lets Hx: mapstoval_true_vptr_eq H15 H24 H4 H5.
  simpljoin1; auto.

  simpljoin1.
  lets Hx: disj_precise' H7 H12.
  intros.
  clear H6 H7 H12 H11.
  unfold TCBFree_Not_Eq, TCBFree_Eq in H4.
  destruct H4; do 3 destruct H6.
  sep split in H4; sep split in H6; simpljoin1.
  tryfalse.

  intros.
  clear H6 H7 H12 H11.
  unfold TCBFree_Not_Eq, TCBFree_Eq in H4.
  destruct H4; do 3 destruct H4.
  sep split in H4; sep split in H6; simpljoin1.
  tryfalse.

  intros.
  eapply TCBFree_Not_Eq_precise'; eauto.

  intros.
  eapply TCBFree_Eq_precise'; eauto.

  destruct Hx.
  assert (x0 = x6).
  eapply H4 with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.

  mem_eq_solver2.

  simpl in H11, H6; simpljoin1.

  assert (o1 = empabst).
  destruct H12.
  
  apply TCBFree_Not_Eq_osabst_emp in H4; auto.
  apply TCBFree_Eq_osabst_emp in H4; auto.

  assert (o2 = empabst).
  destruct H7.
  apply TCBFree_Not_Eq_osabst_emp in H5; auto.
  apply TCBFree_Eq_osabst_emp in H5; auto.

  simpljoin1.
Qed.   

Lemma AOSTCBFreeList'_precise :
  forall p p' vl vl' ct e e0 i ier l a M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBFreeList' p' vl' ct tcbls' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros p p' vl vl' ct e e0 i ier l a M1 M2 o1 o2 tcbls tcbls' H H0.
  eapply precise'2precise;eauto.
  eapply AOSTCBFreeList'_precise';eauto.
Qed.

Lemma AOSTCBFreeList'_pfree_eq :
  forall p p' vl vl' ct ct' e e0 i ier l a M M1 M2 o1 o2 tcbls tcbls',
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBFreeList' p vl ct tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBFreeList' p' vl' ct' tcbls' ->
    sub M1 M -> sub M2 M ->    
    p = p'.
Proof.
  intros.
  lets Hx: AOSTCBFreeList'_isptr H.
  lets Hx1: AOSTCBFreeList'_isptr H0.
    
  unfold AOSTCBFreeList' in *.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H11, H6; simpljoin1.
  rewrite H21 in H11; inverts H11.
  destruct p, p'; auto;
    unfold isptr in *;
    destruct Hx; destruct Hx1; simpljoin1; tryfalse.

  false; eapply mapstoval_vnull_vptr_mem_sub_false with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  false; eapply mapstoval_vnull_vptr_mem_sub_false with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := (Tptr os_ucos_h.OS_TCB) ).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

Lemma dllseg_os_tcb_flag_precise' :
  forall l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= dllseg head headprev tail Vnull l OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, M2, i, ier, lo, o2, a) |= dllseg head headprev' tail' Vnull l' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions l; intros.
  destruct l'.
  simpl in H, H0; simpljoin1; intros; auto.

  simpl in H; simpljoin1.
  unfold dllseg in H0; fold dllseg in H0.
  simpl_sat H0; simpljoin1; tryfalse.
  
  destruct l'.
  simpl in H0; simpljoin1.
  unfold dllseg in H; fold dllseg in H; simpl_sat H; simpljoin1.
  simpl in H18; simpljoin1; tryfalse.
  unfold dllseg in H0, H; fold dllseg in H0, H; simpl_sat H0; simpl_sat H; simpljoin1.

  simpljoin1; split;  intros.
  assert(struct_atom_val_eq a v OS_TCB_flag).
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
  simpl in H1.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, a = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).

  unfold node in H45; simpl_sat H45; simpljoin1.
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  unfold node in H19; simpl_sat H19; simpljoin1.
  eapply struct_type_vallist_match_os_tcb_flag; eauto.
  simpljoin1.

  simpl in H1; simpljoin1.
  unfold V_OSTCBNext in H9, H35; unfold V_OSTCBPrev in H40, H14; unfold nth_val in *.
  inverts H9; inverts H14; inverts H35; inverts H40.

  lets Hx1: IHl H46 H20.
  lets Hx2: node_precise' H45 H19; simpljoin1.
  mem_eq_solver M.

  apply node_osabst_emp in H45;
    apply node_osabst_emp in H19;
    apply dllseg_osabst_emp in H46;
    apply dllseg_osabst_emp in H20;
    substs.

  eapply OSAbstMod.extensionality; intros.
  pose proof H18 a1; pose proof H44 a1.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a1 );
    destruct(OSAbstMod.get o2 a1 );
    tryfalse; auto.
Qed.

Lemma dllseg_os_tcb_flag_precise :
  forall l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= dllseg head headprev tail Vnull l OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, M2, i, ier, lo, o2, a) |= dllseg head headprev' tail' Vnull l' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply dllseg_os_tcb_flag_precise';eauto.
Qed.

Lemma tcbdllseg_precise' :
  forall l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= tcbdllseg head headprev tail Vnull l ->
    (e, e0, M2, i, ier, lo, o2, a) |= tcbdllseg head headprev' tail' Vnull l' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold tcbdllseg; intros.
  eapply dllseg_os_tcb_flag_precise'; eauto.
Qed.

Lemma tcbdllseg_precise :
  forall l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= tcbdllseg head headprev tail Vnull l ->
    (e, e0, M2, i, ier, lo, o2, a) |= tcbdllseg head headprev' tail' Vnull l' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros l l' head headprev headprev' tail tail' e e0 i ier lo a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply tcbdllseg_precise';eauto.
Qed.

Lemma tcbdllseg_osabst_emp :
  forall l head headprev tail tailnext e e0 M i ier lo o a0,
    (e, e0, M, i, ier, lo, o, a0) |= tcbdllseg head headprev tail tailnext l -> o = empabst.
Proof.
  unfold tcbdllseg; intros.
  apply dllseg_osabst_emp in H; auto.
Qed.

Lemma tcb_linked_list_same_next_intro_dllseg :
  forall vl vl' head headprev headprev' tail tail' e e0 m i ier l o1 o2 a,
    (e, e0, m, i, ier, l, o1, a) |= dllseg head headprev tail Vnull vl OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    (e, e0, m, i, ier, l, o2, a) |= dllseg head headprev' tail' Vnull vl' OS_TCB_flag V_OSTCBPrev V_OSTCBNext ->
    tcb_linked_list_same_next vl vl'.
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl; auto.

  unfold dllseg in *; fold dllseg in *.
  sep split in H; sep split in H0; tryfalse.
  
  destruct vl'.
  unfold dllseg in *; fold dllseg in *.
  sep split in H; sep split in H0; tryfalse.
  
  unfold dllseg in *; fold dllseg in *.
  sep normal in H; sep normal in H0.
  destruct H, H0.
  sep split in H; sep split in H0.
  unfold tcb_linked_list_same_next; fold tcb_linked_list_same_next.
  rewrite H1, H4.
  simpl_sat H; simpl_sat H0; simpljoin1.
  assert (sub x1 m).
  eapply join_sub_l; eauto.
  assert (sub x7 m).
  eapply join_sub_l; eauto.
  lets Hx: node_vl_eq H15 H10 H0 H.
  assert (x = x0).
  clear - H1 H4 Hx.
  eapply struct_atom_val_eq_V_OSTCBNext_eq; eauto.

  substs.
  split; auto.

  lets Hx1: dllseg_os_tcb_flag_precise' H11 H16.
  destruct Hx1.
  assert (sub x2 m).
  eapply join_sub_r; eauto.
  assert (sub x8 m).
  eapply join_sub_r; eauto.
  lets Hx1: H8 H17 H18.
  substs. 
  eapply IHvl; eauto.
Qed.

Lemma tcb_linked_list_same_next_intro' :
  forall vl vl' head tail tail' e e0 m i ier l o1 o2 a,
    (e, e0, m, i, ier, l, o1, a) |= tcbdllseg head Vnull tail Vnull vl ->
    (e, e0, m, i, ier, l, o2, a) |= tcbdllseg head Vnull tail' Vnull vl' ->
    tcb_linked_list_same_next vl vl'.
Proof.
  intros.
  eapply tcb_linked_list_same_next_intro_dllseg; eauto.
Qed.

(* new add by CNU *)

Lemma AOSTCBList'_tcbdllseg:
  forall e e0 m i ier l o a head p2 vll1 vll2 rtbl hcurt tcbls pf, 
    (e, e0, m, i, ier, l, o, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    exists tail P,
      (e, e0, m, i, ier, l, o, a) |= tcbdllseg head Vnull tail Vnull (vll1++vll2) ** P.  
Proof.
  introv Hsat.
  unfold AOSTCBList' in *.
  destruct Hsat.
  sep destruct H.
  sep lifts (2::4::nil)%nat in H.
  apply tcbdllseg_compose in H.
  exists x0. eexists.  eauto.
  sep destruct H.
  sep lift 3%nat in H.
  unfold tcblist in H.
  sep normal in H.
  exists x. eexists. eauto.
Qed.

Lemma gvar_ptr_precise' :
  forall m1 m2 m v1 v2 e e0 i ier l o1 o2 a t gvar, 
    isptr v1 ->
    isptr v2 -> 
    (e, e0, m1, i, ier, l, o1, a) |= GV gvar @ (Tptr t) |-> v1 ->  
    (e, e0, m2, i, ier, l, o2, a) |= GV gvar @ (Tptr t) |-> v2 ->
    sub m1 m ->
    sub m2 m -> 
    v1 = v2. 
Proof.
  introv Hptr1 Hptr2 Hv1 Hv2 Hsub1 Hsub2.
  destruct Hv1.
  destruct Hv2.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9. simpl in H4. simpljoin1.
  rewrite H0 in H. inverts H.
  destruct H10. destruct H5.
  simpl in *.
  unfold isptr in *.
  destruct Hptr1; destruct Hptr2.
  congruence.
  destruct H5. subst v1. subst v2.
  exfalso. eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  destruct H4.
  subst v1. subst v2.
  exfalso. eapply mapstoval_vnull_vptr_mem_sub_false; eauto.
  destruct H4. destruct H5.
  subst v1. subst v2.
  lets H00: mapstoval_true_vptr_eq H H2 Hsub1 Hsub2.
  destruct H00.
  congruence.
Qed.

Lemma AOSTCBList'_tcb_list_same_head :
  forall vll1 vll1' vll2 vll2' head head' p2 p2' e e0 m i ier l o1 o2 a
         rtbl rtbl' hcurt hcurt' tcbls tcbls' pf pf',
    (e, e0, m, i, ier, l, o1, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    (e, e0, m, i, ier, l, o2, a) |= AOSTCBList' head' p2' vll1' vll2' rtbl' hcurt' tcbls' pf' ->
    head = head'.
Proof.
  introv Hsat1 Hsat2.
  lets Htcbdllseg1: AOSTCBList'_tcbdllseg Hsat1.
  lets Htcbdllseg2: AOSTCBList'_tcbdllseg Hsat2.
  simpljoin1. 
  apply dllseg_head_isptr in H0. rename H0 into Hptr1.
  apply dllseg_head_isptr in H. rename H into Hptr2.
  destruct Hsat1; destruct Hsat2; 
    (sep destruct H; sep destruct H0; 
     elim_sep_conj1 H H_; elim_sep_conj1 H0 H0_; 
     eapply gvar_ptr_precise'; eauto; 
     [ instantiate (1:=m); eapply join_sub_l; eauto | 
       eapply join_sub_l; eauto]).
Qed.

Lemma AOSTCBList'_tcb_list_same_next_intro':
  forall vll1 vll1' vll2 vll2' head head' p2 p2' e e0 m i ier l o1 o2 a
         rtbl rtbl' hcurt hcurt' tcbls tcbls' pf pf',  
    (e, e0, m, i, ier, l, o1, a) |= AOSTCBList' head p2 vll1 vll2 rtbl hcurt tcbls pf ->
    (e, e0, m, i, ier, l, o2, a) |= AOSTCBList' head' p2' vll1' vll2' rtbl' hcurt' tcbls' pf' -> 
    tcb_linked_list_same_next (vll1 ++ vll2) (vll1' ++ vll2').  
Proof.
  introv Hsat1 Hsat2.
  assert (Hhdeq: head = head').
  {
     eapply AOSTCBList'_tcb_list_same_head; eauto.
  }
  subst head'.
  unfold AOSTCBList' in *.
  destruct Hsat1; destruct Hsat2.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H. sep lifts (2::4::nil)%nat in H0.
    apply tcbdllseg_compose in H.
    apply tcbdllseg_compose in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x7 = x11).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H15 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x11. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H.
    apply tcbdllseg_compose in H.
    sep lift 3%nat in H0.
    unfold tcblist in H0.
    sep split in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x4 = x8).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H13 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x8. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lifts (2::4::nil)%nat in H0.
    apply tcbdllseg_compose in H0.
    sep lift 3%nat in H.
    unfold tcblist in H.
    sep split in H.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x4 = x8).
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H13 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x8. 
    eapply tcb_linked_list_same_next_intro'; eauto.
  -
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    sep lift 3%nat in H.
    unfold tcblist in H. sep split in H.
    sep lift 3%nat in H0.
    unfold tcblist in H0. sep split in H0.
    elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
    assert (x1 = x5). 
    {
      lets H00: tcbdllseg_precise' H_ H0_.
      destruct H00.
      apply H11 with (M:=m).
      eapply join_sub_l; eauto.
      eapply join_sub_l; eauto.
    }
    subst x5.
    eapply tcb_linked_list_same_next_intro'; eauto.
Qed.

(* end of new add *)

Lemma tcbdllseg_isvptr1:
  forall l s p1 tail1 ct p z,
    s |= tcbdllseg p1 z tail1 (Vptr ct) l ** p -> exists x, p1 = Vptr x.
Proof.
  inductions l.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  sep split in H.
  eauto.
  intros.
  unfold tcbdllseg in H; simpl dllseg in H.
  unfold node in H.
  sep normal in H.
  sep destruct  H.
  sep split in H.
  simpljoin1; eauto.
Qed.

Lemma tcblist_isptr :
  forall s head tail vl rtbl tcbls P,
    s |= tcblist head Vnull tail Vnull vl rtbl tcbls ** P ->
    isptr head.
Proof.
  intros.
  destruct_s s.
  destruct vl.
  simpl in H; simpljoin1.
  unfolds; eauto.

  unfold tcblist in H.
  sep split in H.
  unfold tcbdllseg in H.
  sep remember (1::nil)%nat in H.
  eapply dllseg_head_isptr in H; auto.
Qed.

Lemma AOSTCBList'_isptr :
  forall s p1 p2 l1 l2 rtbl hcurt tcbls pf,
    s |= AOSTCBList' p1 p2 l1 l2 rtbl hcurt tcbls pf ->
    isptr p1.
Proof.
  intros.
  unfold AOSTCBList' in H.
  destruct H.
  do 4 destruct H.
  sep split in H; simpljoin1.
  sep remember (2::nil)%nat in H.
  eapply tcbdllseg_isvptr1 in H.
  destruct H; substs; unfolds; eauto.

  destruct H.
  sep split in H; simpljoin1.
  sep remember (3::nil)%nat in H.
  eapply tcblist_isptr; eauto.
Qed.

Lemma dllsegflag_osabst_emp :
  forall vl e e0 M i ier o a0 lo p headprev,
    (e, e0, M, i, ier, lo, o, a0) |= dllsegflag p headprev vl V_OSTCBNext ->
    o = empabst.
Proof.
  inductions vl; intros.
  simpl in H; simpljoin1.

  unfold dllsegflag in H; fold dllsegflag in H.
  do 2 destruct H; sep split in H.
  simpl_sat H; simpljoin1.
  lets Hx: IHvl H6; substs.
  simpl in H5; simpljoin1.
Qed.

Lemma tcbdllflag_osabst_emp :
  forall vl e e0 M i ier o a0 lo p,
    (e, e0, M, i, ier, lo, o, a0) |= tcbdllflag p vl ->
    o = empabst.
Proof.
  intros.
  unfold tcbdllflag in H.
  eapply dllsegflag_osabst_emp; eauto.
Qed.

Lemma dllsegflag_precise' :
  forall vl vl' p headprev headprev' e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= dllsegflag p headprev vl V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= dllsegflag p headprev' vl' V_OSTCBNext ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions vl; intros.
  destruct vl'.
  simpl in H0, H1; simpljoin1.
  split; intros; auto.
  
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep split in H0.
  do 2 destruct H1; sep split in H1.
  substs; tryfalse.
  
  destruct vl'.
  unfold dllsegflag in *; fold dllsegflag in *.
  sep split in H1.
  do 2 destruct H0; sep split in H0.
  substs; tryfalse.
  
  unfold sllfreeflag in *.
  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  do 2 destruct H0, H1.
  sep split in H0; sep split in H1.
  substs; inverts H4.
  
  (* rearrange H1 and H0 *)
  remember H0 as H0'.
  clear HeqH0' H0.
  remember H0' as H0.
  clear HeqH0 H0'.
  
  simpl_sat H0; simpl_sat H1; simpljoin1.

  unfold tcb_linked_list_same_next in H; fold tcb_linked_list_same_next in H.
  rewrite H3 in H.
  rewrite H5 in H.
  simpljoin1.

  lets Hx: IHvl H0 H8 H13.
  split; intros.
  destruct Hx.
  assert (sub x3 M).
  mem_join_sub_solver.
  assert (sub x9 M).
  mem_join_sub_solver.
  lets Hx1: H4 H14 H15.
  substs.
  assert (x = x8).
  simpl in H12, H7; simpljoin1.
  assert (sub x M).
  mem_join_sub_solver.
  assert (sub x8 M).
  mem_join_sub_solver.
  lets Hx: mapstoval_false_mem_eq H6 H11 H7 H12.
  auto.
  substs.
  clear - H9 H2.
  eapply join_unique; eauto.

  simpl in H7, H12; simpljoin1.
  eapply H10; eauto.
Qed.

Lemma dllsegflag_precise :
  forall vl vl' p headprev headprev' e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= dllsegflag p headprev vl V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= dllsegflag p headprev' vl' V_OSTCBNext ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p headprev headprev' e e0 i ier l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply dllsegflag_precise';eauto.
Qed.

Lemma tcbdllflag_precise' :
  forall vl vl' p e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= tcbdllflag p vl ->
    (e, e0, M2, i, ier, l, o2, a) |= tcbdllflag p vl' ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  unfold tcbdllflag in *.
  eapply dllsegflag_precise'; eauto.
Qed.

Lemma tcbdllflag_precise :
  forall vl vl' p e e0 i ier l a M1 M2 o1 o2,
    tcb_linked_list_same_next vl vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= tcbdllflag p vl ->
    (e, e0, M2, i, ier, l, o2, a) |= tcbdllflag p vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' p e e0 i ier l a M1 M2 o1 o2 H H0 H1.
  eapply precise'2precise;eauto.
  eapply tcbdllflag_precise';eauto.
Qed.

(*pfree eq by the above lemma on AOSTCBFreeList*)
(*ct eq can be obtained from HCurTid*)
Lemma AOSTCBList'_precise' :
  forall p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pfree ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBList' p1' p2' tcbl1' (tcbcur' :: tcbl2') rtbl' ct tcbls' pfree ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  eapply disj_precise'; eauto.

  intros.
  destruct H1.
  do 4 destruct H1; sep split in H1.
  destruct H2; sep split in H2.
  simpljoin1; tryfalse.

  intros.
  destruct H1.
  destruct H1; sep split in H1.
  do 4 destruct H2; sep split in H2.
  simpljoin1; tryfalse.

-
  intros.
  do 4 destruct H1; do 4 destruct H2.
  sep split in H1; sep split in H2; simpljoin1.
  
  (* rearrange H1 and H2 *)
  remember H1 as H1'.
  clear HeqH1' H1.
  remember H1' as H1.
  clear HeqH1 H1'.
  
  apply AOSTCBList'_isptr in H.
  apply AOSTCBList'_isptr in H0.
  clear H4 H5 H9 H10 H11 H12 H6 H7; clears.
  sep lifts (2::4::nil)%nat in H2.
  sep lifts (2::4::nil)%nat in H1.
  apply tcbdllseg_compose in H2.
  apply tcbdllseg_compose in H1.
  
  destruct p1, p1'; unfold isptr in H, H0; destruct H; destruct H0; simpljoin1; tryfalse.
  clear H3 H8 H0 H; clears.
  split; intros.
  simpl_sat H2.
  simpl_sat H1.
  simpljoin1.
  simpl in H26; simpljoin1.
  simpl in H11; simpljoin1.
  rewrite H9 in H11; inverts H11.
  
  assert (Vptr a = Vptr a1 /\ x13 = x25).
  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  
  simpljoin1.
  inverts H1.
  simpl in H31; simpl in H16; simpljoin1.
  rewrite H31 in H11; inverts H11.
  assert (x19 = x31).
  eapply mapstoval_false_mem_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  assert (x7 = x).
  lets Hx: tcbdllseg_precise' H21 H6.
  destruct Hx.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.

  substs.
  lets Hx: tcb_linked_list_same_next_intro' H21 H6.
  assert (x32 = x20).
  lets Hx1: tcbdllflag_precise' Hx H32 H17.
  destruct Hx1.
  eapply H1 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  mem_eq_solver2.

  simpl_sat H2; simpl_sat H1; simpljoin1.
  unfold tcbdllseg in *.
  apply dllseg_osabst_emp in H21;
    apply dllseg_osabst_emp in H6.
  simpl in H26, H31, H11, H16; simpljoin1.
  eapply tcbdllflag_osabst_emp in H32;
    eapply tcbdllflag_osabst_emp in H17.
  simpljoin1.

- 
  intros.
  apply AOSTCBList'_isptr in H.
  apply AOSTCBList'_isptr in H0.
  destruct H1, H2.
  unfold TCB_Not_In in *.
  unfold tcblist in *.
  sep split in H1; sep split in H2.
  simpljoin1.
  
  (* rearrange H1 and H2 *)
  remember H1 as H1'.
  clear HeqH1' H1.
  remember H1' as H1.
  clear HeqH1 H1'.
  
  destruct p1, p1'; unfold isptr in H, H0; destruct H; destruct H0; simpljoin1; tryfalse.
  inverts H10.
  clear H H0 H3 H7 H8 H11 H4 H13 H5 H9; clears.
  simpl_sat H2; simpl_sat H1; simpljoin1.
  split; intros.
  
  assert (Vptr a2 = Vptr a1 /\ x8 = x1).
  simpl in H19, H4; simpljoin1.
  rewrite H33 in H12; inverts H12.
  eapply mapstoval_true_rule_type_val_match_eq with (M := M) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin1.
  inverts H2.
  
  assert (x26 = x14).
  simpl in H24, H9; simpljoin1.
  rewrite H33 in H12.
  inverts H12.
  eapply mapstoval_false_mem_eq with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  eauto.
  eauto.
  substs.

  assert (x20 = x32).
  lets Hx: tcbdllseg_precise' H14 H29.
  destruct Hx.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.

  assert (x21 = x33).
  lets Hx: tcb_linked_list_same_next_intro' H14 H29.
  lets Hx1: tcbdllflag_precise' Hx H15 H30.
  destruct Hx1.
  eapply H2 with (M := M).
  mem_join_sub_solver.
  mem_join_sub_solver.
  substs.
  mem_eq_solver2.

  simpl in H19, H24, H4, H9; simpljoin1.
  apply tcbdllseg_osabst_emp in H29;
    apply tcbdllseg_osabst_emp in H14.
  apply tcbdllflag_osabst_emp in H30;
    apply tcbdllflag_osabst_emp in H15.
  simpljoin1.
Qed.

Lemma AOSTCBList'_precise :
  forall p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pfree ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSTCBList' p1' p2' tcbl1' (tcbcur' :: tcbl2') rtbl' ct tcbls' pfree ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct tcbls tcbls' pfree  e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply AOSTCBList'_precise';eauto.
Qed.
(*
Lemma dllseg_ostcb_precise :
  forall l l' head headprev headprev' tail tail' e e0 i ier l o a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= dllseg head headprev tail Vnull l os_ucos_h.OS_TCB V_OSTCBPrev V_OSTCBNext ->
    (e, e0, M2, i, ier, lo, o2, a) |= dllseg head headprev' tail' Vnull l' os_ucos_h.OS_TCB V_OSTCBPrev V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions l; intros.
  destruct l'.
  simpl in H, H0; simpljoin1; intros; auto.

  simpl in H; simpljoin1.
  unfold dllseg in H0; fold dllseg in H0.
  simpl_sat H0; simpljoin1; tryfalse.
  
  destruct l'.
  simpl in H0; simpljoin1.
  unfold dllseg in H; fold dllseg in H; simpl_sat H; simpljoin1.
  simpl in H18; simpljoin1; tryfalse.
  unfold dllseg in H0, H; fold dllseg in H0, H; simpl_sat H0; simpl_sat H; simpljoin1.

  simpljoin1; intros.
  assert(struct_atom_val_eq a v os_ucos_h.OS_TCB).
  eapply node_vl_eq with (M:=M); eauto; mem_join_sub_solver.
  simpl in H1.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, a = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).

  unfold node in H45; simpl_sat H45; simpljoin1.
  eapply struct_type_vallist_match_os_tcb; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  unfold node in H19; simpl_sat H19; simpljoin1.
  eapply struct_type_vallist_match_os_tcb; eauto.
  simpljoin1.

  simpl in H1; simpljoin1.
  unfold OSTCBInvDef.V_OSTCBNext in H9, H35; unfold OSTCBInvDef.V_OSTCBPrev in H40, H14; unfold nth_val in *.
  inverts H9; inverts H14; inverts H35; inverts H40.

  lets Hx1: IHl H46 H20.
  lets Hx2: node_precise H45 H19; simpljoin1.
  mem_eq_solver M.

  apply node_osabst_emp in H45;
    apply node_osabst_emp in H19;
    apply dllseg_osabst_emp in H46;
    apply dllseg_osabst_emp in H20;
    substs.

  eapply OSAbstMod.extensionality; intros.
  pose proof H18 a1; pose proof H44 a1.
  rewrite OSAbstMod.emp_sem in *.
  destruct(OSAbstMod.get o1 a1 );
    destruct(OSAbstMod.get o2 a1 );
    tryfalse; auto.
Qed.

Lemma tcbdllseg_precise :
  forall l l' head headprev headprev' tail tail' e e0 i ier l o a M1 M2 o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= OSTCBInvDef.tcbdllseg head headprev tail Vnull l ->
    (e, e0, M2, i, ier, lo, o2, a) |= OSTCBInvDef.tcbdllseg head headprev' tail' Vnull l' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold OSTCBInvDef.tcbdllseg; intros.
  eapply dllseg_ostcb_precise; eauto.
Qed.

Lemma tcbdllseg_osabst_emp :
  forall l head headprev tail tailnext e e0 M i ier l o o a0,
    (e, e0, M, i, ier, lo, o, a0) |= OSTCBInvDef.tcbdllseg head headprev tail tailnext l -> o = empabst.
Proof.
  unfold OSTCBInvDef.tcbdllseg; intros.
  apply dllseg_osabst_emp in H; auto.
Qed.

Lemma AOSTCBList_precise :
  forall p1 p1' p2 p2' tcbl1 tcbl1' tcbcur tcbcur' tcbl2 tcbl2' rtbl rtbl' ct ct' tcbls tcbls' e e0 i ier l  a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= OSTCBInvDef.AOSTCBList p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ->
    (e, e0, M2, i, ier, l, o2, a) |= OSTCBInvDef.AOSTCBList p1' p2' tcbl1' (tcbcur' :: tcbl2') rtbl' ct' tcbls' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  lets Hx1: AOSTCBList_vptr H.
  lets Hx2:  AOSTCBList_vptr H0.
  simpljoin1.

  unfold OSTCBInvDef.AOSTCBList in *.
  do 4 destruct H0; sep split in H0.
  do 4 destruct H; sep split in H.

  simpljoin1; intros.
  assert(x = x0).
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H29, H14; simpljoin1.
  rewrite H41 in H17; inverts H17.
  eapply mapstoval_vptr_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  
  sep lifts (2::4::nil)%nat in H0.
  sep lifts (2::4::nil)%nat in H.
  apply tcbdllseg_compose in H0.
  apply tcbdllseg_compose in H.

  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H19, H20, H29, H30; simpljoin1.
  rewrite H53 in H35; rewrite H44 in H22; inverts H35; inverts H22.
  assert(x20 = x25).
  eapply mapstoval_mem_eq with (M:=M); eauto; mem_join_sub_solver. 
  assert(x21 = x27).
  eapply mapstoval_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.

  lets Hx: tcbdllseg_precise H24 H14; simpljoin1.
  eapply MemMod_eq_join_eq; eauto.
  eapply H with (M:=M); mem_join_sub_solver.
  eapply MemMod_eq_join_eq; eauto.

  sep lifts (2::4::nil)%nat in H0.
  sep lifts (2::4::nil)%nat in H.
  apply tcbdllseg_compose in H0.
  apply tcbdllseg_compose in H.
  simpl_sat H; simpl_sat H0; simpljoin1.
  
  apply tcbdllseg_osabst_emp in H24.
  apply tcbdllseg_osabst_emp in H14.
  simpl in H29, H30, H19, H20; simpljoin1.
Qed.

Lemma ostcb_sll_precise :
  forall lfree lfree' head e e0 M1 M2 i ier l  o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head lfree os_ucos_h.OS_TCB OSTCBInvDef.V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head lfree' os_ucos_h.OS_TCB OSTCBInvDef.V_OSTCBNext ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions lfree; intros.
  simpl in H; simpljoin1.
  destruct lfree'.
  simpl in H0; simpljoin1; auto.
  unfold sll in H0; unfold sllseg in H0; fold sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct lfree'.
  simpl in H0; simpljoin1.
  unfold sll in H; unfold sllseg in H; fold sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold sll in H, H0; unfold sllseg in H, H0; fold sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  lets Hx: node_precise H14 H19.
  
  unfold sll in IHlfree.
  simpljoin1; intros.
  assert(x5 = x6).
  assert(sub x12 M) by mem_join_sub_solver.
  assert(sub x17 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H14 H19 H5 H6.
  simpl in Hx; unfold V_OSEventListPtr in H9, H10.
  unfold node in H14, H19.
  destruct H14, H19; sep split in H7; sep split in H8; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, exists a11, a = a1::a2::a3::a4::a5::a6::a7::a8::a9::a10::a11::nil).
  eapply struct_type_vallist_match_os_tcb; eauto.
  assert(exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10, exists v11, v = v1::v2::v3::v4::v5::v6::v7::v8::v9::v10::v11::nil).
  eapply struct_type_vallist_match_os_tcb; eauto.
  simpljoin1; simpl in Hx; simpl in H9, H10; simpljoin1; inversion H9; inversion H10; substs; auto.
  substs.
  
  lets Hx2: IHlfree H15 H20.
  simpljoin1; mem_eq_solver M.
  
  eapply sllseg_osabst_emp in H15.
  eapply sllseg_osabst_emp in H20.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma AOSTCBFreeList_precise :
  forall ptfree ptfree' lfree lfree' e e0 i ier l  a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= OSTCBInvDef.AOSTCBFreeList ptfree lfree ->
    (e, e0, M2, i, ier, l, o2, a) |= OSTCBInvDef.AOSTCBFreeList ptfree' lfree' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold OSTCBInvDef.AOSTCBFreeList; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H9, H4; simpljoin1.
  rewrite H19 in H9; inverts H9.
  
  simpljoin1; intros.
  assert(ptfree = ptfree').
  assert(isptr ptfree).
  eapply sll_isptr; eauto.
  assert(isptr ptfree').
  eapply sll_isptr; eauto.
  destruct ptfree, ptfree'; auto;
  try(unfolds in H2; destruct H2; simpljoin1; tryfalse);
  try(unfolds in H3; destruct H3; simpljoin1; tryfalse).
  unfolds in H20; simpljoin1; simpl in H4; simpljoin1.
  unfolds in H11; simpljoin1; simpl in H13; destruct a0; simpl in H13; simpljoin1.
  clear - H4 H13 H3 H11 H1 H6 H H0.
  unfold ptomval in H4; unfold ptomval in H13; substs.
  assert(sub (memory.MemMod.sig (x21, Int.unsigned Int.zero) (Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (memory.MemMod.sig (x21, Int.unsigned Int.zero) MNull) M).
  mem_join_sub_solver.
  unfold sub in H2, H4.
  unfold memory.MemMod.lookup in H2, H4.
  pose proof H2 (x21, Int.unsigned Int.zero) (Pointer b i0 3).
  pose proof H4 (x21, Int.unsigned Int.zero) MNull.
  rewrite memory.MemMod.get_sig_some in H5.
  rewrite memory.MemMod.get_sig_some in H7.
  assert(Some (Pointer b i0 3) = Some (Pointer b i0 3)) by auto.
  assert(Some MNull = Some MNull) by auto.
  apply H5 in H8; apply H7 in H9.
  rewrite H8 in H9; inverts H9.
  
  unfolds in H11; simpljoin1; simpl in H4; destruct a0; simpl in H4;  simpljoin1.
  unfolds in H20; simpljoin1; simpl in H14; simpljoin1.
  clear - H4 H14 H3 H12 H H0 H1 H6.
  unfold ptomval in H4; unfold ptomval in H14; substs.
  assert(sub (memory.MemMod.sig (x21, Int.unsigned Int.zero) (Pointer b i0 3)) M).
  mem_join_sub_solver.
  assert(sub (memory.MemMod.sig (x21, Int.unsigned Int.zero) MNull) M).
  mem_join_sub_solver.
  unfold sub in H2, H4.
  unfold memory.MemMod.lookup in H2, H4.
  pose proof H2 (x21, Int.unsigned Int.zero) (Pointer b i0 3).
  pose proof H4 (x21, Int.unsigned Int.zero) MNull.
  rewrite memory.MemMod.get_sig_some in H5.
  rewrite memory.MemMod.get_sig_some in H7.
  assert(Some (Pointer b i0 3) = Some (Pointer b i0 3)) by auto.
  assert(Some MNull = Some MNull) by auto.
  apply H5 in H8; apply H7 in H9.
  rewrite H8 in H9; inverts H9.

  inverts H2; inverts H3.
  assert(sub x M).
  apply memory.MemMod.join_sub_l in H1.
  eapply sub_trans; eauto.
  assert(sub x5 M).
  apply memory.MemMod.join_sub_l in H6.
  eapply sub_trans; eauto.
  lets Hx: mapstoval_vptr_eq H20 H11 H3 H2; simpljoin1.
  substs.
  
  assert(x = x5).
  eapply mapstoval_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply MemMod_eq_join_eq; eauto.
  
  lets Hx: ostcb_sll_precise H10 H5; simpljoin1.
  mem_eq_solver M.
  
  apply sll_osabst_emp in H10; apply sll_osabst_emp in H5.
  substs; auto.
Qed.
*)

Lemma AOSTCBList'_ct_eq :
  forall p1 p1' p2 p2' l1 l1' l2 l2' rtbl rtbl' ct ct'
    tcbls tcbls' pfree pfree'
    e e0 i ier lo a M1 M2 M o1 o2,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSTCBList' p1 p2 l1 l2 rtbl ct tcbls pfree ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSTCBList' p1' p2' l1' l2' rtbl' ct' tcbls' pfree' ->
    sub M1 M -> sub M2 M ->
    ct = ct'.
Proof.
  intros.
  unfold AOSTCBList' in *.
  destruct H, H0.
  
  do 4 destruct H.
  do 4 destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (3::nil)%nat in H0.
  sep remember (3::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H37 in H23; inverts H23.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  do 4 destruct H.
  destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (2::nil)%nat in H0.
  sep remember (3::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H33 in H19; inverts H19.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  do 4 destruct H0.
  destruct H.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (3::nil)%nat in H0.
  sep remember (2::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H33 in H19; inverts H19.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.

  destruct H.
  destruct H0.
  sep split in H; sep split in H0; simpljoin1.
  sep remember (2::nil)%nat in H0.
  sep remember (2::nil)%nat in H.
  simpl in H0; simpl in H; simpljoin1.
  rewrite H29 in H15; inverts H15.
  eapply mapstoval_false_vptr_eq with (M := M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

Lemma AOSTCBList'_osabst_emp :
  forall e e0 M i ier o a0 lo p1 p2 l1 l2 rtbl hcurt tcbls pf,
    (e, e0, M, i, ier, lo, o, a0) |= AOSTCBList' p1 p2 l1 l2 rtbl hcurt tcbls pf ->
    o = empabst.
Proof.
  intros.
  unfold AOSTCBList' in H.
  destruct H.
  do 4 destruct H.
  sep split in H.
  clear H0 H1 H2 H3 H4.
  sep lifts (2::4::nil)%nat in H.
  eapply tcbdllseg_compose in H.
  simpl_sat H; simpljoin1.
  simpl in H8; simpljoin1.
  apply tcbdllseg_osabst_emp in H3.
  apply tcbdllflag_osabst_emp in H14.
  simpl in H13; simpljoin1.

  destruct H.
  unfold tcblist in H.
  unfold TCB_Not_In in H.
  sep normal in H; sep split in H.
  simpl_sat H; simpljoin1.
  clear H0 H2 H1 H19.
  simpl in H7.
  simpl in H12.
  simpljoin1.
  apply tcbdllseg_osabst_emp in H17.
  apply tcbdllflag_osabst_emp in H18.
  simpljoin1.
Qed.

Lemma AOSTCBFreeList'_osabst_emp :
  forall e e0 M i ier o a0 lo ptfree lfree ct tcbls,
    (e, e0, M, i, ier, lo, o, a0) |= AOSTCBFreeList' ptfree lfree ct tcbls->
    o = empabst.
Proof.
  intros.
  unfold AOSTCBFreeList' in H.
  simpl_sat H.
  simpljoin1.
  destruct H4.
  unfold TCBFree_Not_Eq in H.
  sep split in H.
  clear H1.
  simpl_sat H.
  simpl in H3.
  simpljoin1.
  apply sll_osabst_emp in H6.
  apply sllfreeflag_osabst_emp in H7.
  simpljoin1.

  unfold TCBFree_Eq in H.
  do 3 destruct H.
  sep split in H.
  clear H1 H4.
  simpl_sat H.
  simpl in H3.
  simpljoin1.
  apply Astruct_osabst_emp in H6.
  apply sll_osabst_emp in H21.
  apply sllfreeflag_osabst_emp in H22.
  simpl in H11; simpljoin1.
  simpl in H26; simpljoin1.
  simpl in H31; simpljoin1.
  simpl in H36; simpljoin1.
  simpl in H37; simpljoin1.
Qed.

(* precise lemmas about EvtInv  *)

Require Import os_ucos_h.

Ltac simp_mt hyp :=
  match type of hyp with
    context [?t] =>
    match goal with
      H: ?t = _ |- _ => rewrite H in hyp  
    end
  end.

Lemma llsegevaux_mpeq: 
  forall tcbvl tcbvl' tcblh ctcb locmp locmp' ptrmp ptrmp' e e0 i ier l a M1 M2 o1 o2 M, 
    (e, e0, M1, i, ier, l, o1, a) |= llsegevaux tcblh ctcb tcbvl locmp ptrmp V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= llsegevaux tcblh ctcb tcbvl' locmp' ptrmp' V_OSTCBNext ->  
    tcb_linked_list_same_next tcbvl tcbvl' ->
    sub M1 M ->
    sub M2 M -> 
    locmp = locmp' /\ ptrmp = ptrmp'. 
Proof.
  inductions tcbvl.
  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.
  simpl in Hsat1.
  simpljoin1.
  destruct tcbvl'.
  simpl in Hsat2.
  simpljoin1.
  splits; auto.
  simpl in Hnxt. inverts Hnxt.

  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.  
  destruct tcbvl'.
  simpl in Hnxt. inverts Hnxt.

  unfold llsegevaux in Hsat1, Hsat2.
  fold llsegevaux in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
  inverts H4. (*Vptr _ = Vptr _*)
  simpl in Hnxt.
  simp_mt Hnxt.
  simp_mt Hnxt.
  destruct Hnxt. subst.
  unfold evaux_node in H14, H47.
  sep split in H14. sep split in H47. 
  simpl in H47. simpl in H14. simpljoin1.
  assert (Heq: x1 = x9 /\ x19 = x).
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tint8) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heq. substs. 
  (* simpl in H47. simpl in H22. simpljoin1. *)
  assert (Heq: x2 = x10 /\ x41 = x25). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.    
  }
  destruct Heq. substs.
  (* simpl in H95. simpl in H24. simpljoin1.   *)
  assert (Heq: x3 = x11 /\ x47 = x31). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.    
  }
  destruct Heq. substs.
  (* simpl in H53. simpl in H30. simpljoin1. *)
  assert (Heq: x4 = x12 /\ x48 = x32).
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT) (M:=M); eauto.
    mem_join_sub_solver. mem_join_sub_solver.   
  }
  lets H00: IHtcbvl H58 H25 H0. 
  assert (Heq0: x5 = x13 /\ x6 = x14). 
  {
    apply H00. clear H00.
    instantiate (1:=M). mem_join_sub_solver.
    mem_join_sub_solver.
  }
  destructs Heq0.
  substs.
  clear H00.
  splits. join auto. join auto. 
Qed.

Lemma tcbllsegevaux_mpeq: 
  forall tcbvl tcbvl' tcblh locmp locmp' ptrmp ptrmp' e e0 i ier l a M1 M2 o1 o2 M, 
    (e, e0, M1, i, ier, l, o1, a) |= tcbllsegevaux tcblh tcbvl locmp ptrmp ->
    (e, e0, M2, i, ier, l, o2, a) |= tcbllsegevaux tcblh tcbvl' locmp' ptrmp' ->  
    tcb_linked_list_same_next tcbvl tcbvl' ->
    sub M1 M ->
    sub M2 M -> 
    locmp = locmp' /\ ptrmp = ptrmp'. 
Proof. 
  introv Hsat1 Hsat2 Hnxt Hsub1 Hsub2.
  unfold tcbllsegevaux in *.
  lets H00: llsegevaux_mpeq Hsat1 Hsat2 Hnxt.
  apply H00; eauto.
Qed.

Lemma llsegevaux_osabst_emp:
  forall tcbvl e e0 M i ier l o a tcblh tn locmp ptrmp,
    (e, e0, M, i, ier, l, o, a) |= llsegevaux tcblh tn tcbvl locmp ptrmp V_OSTCBNext -> 
    o = empabst.
Proof.
  inductions tcbvl.
  intros.
  simpl in H. simpljoin1.
  introv Hsat.
  simpl in Hsat. simpljoin1.
  eapply IHtcbvl; eauto.
Qed.

Lemma llsegevaux_precise0:  
  forall tcbvl tcbvl' tcblh tn locmp locmp' ptrmp ptrmp' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= llsegevaux tcblh tn tcbvl locmp ptrmp V_OSTCBNext ->
    (e, e0, M2, i, ier, l, o2, a) |= llsegevaux tcblh tn tcbvl' locmp' ptrmp' V_OSTCBNext ->
    tcb_linked_list_same_next tcbvl tcbvl' ->
    (* (forall t locv, get locmp t = Some locv -> rule_type_val_match Tint8 locv = true) ->  *)
    (* (forall t posv, get posmp t = Some posv -> rule_type_val_match Tint8 posv = true) ->  *)
    (* (forall t ptrv, get ptrmp t = Some ptrv -> rule_type_val_match (Tptr OS_EVENT) ptrv = true) ->  *)
    (* (forall t locv, get locmp' t = Some locv -> rule_type_val_match Tint8 locv = true) ->  *)
    (* (forall t posv, get posmp' t = Some posv -> rule_type_val_match Tint8 posv = true) ->  *)
    (* (forall t ptrv, get ptrmp' t = Some ptrv -> rule_type_val_match (Tptr OS_EVENT) ptrv = true) ->   *)
    (forall M, sub M1 M -> sub M2 M -> M1 = M2). 
Proof.
  inductions tcbvl.
  introv Hsat1 Hsat2 Hnxt.
  simpl in Hsat1. simpljoin1.
  destruct tcbvl'. simpl in Hsat2. simpljoin1. intros. auto.
  simpl in Hnxt. tryfalse.

  introv Hsat1 Hsat2 Hnxt.
  destruct tcbvl'. simpl in Hnxt. tryfalse.
  unfold llsegevaux in *. fold llsegevaux in *.
  sep destruct Hsat1. sep destruct Hsat2.
  sep split in Hsat1. sep split in Hsat2.
  unfold evaux_node in *. sep split in Hsat1. sep split in Hsat2.
  simpl in Hsat1; simpl in Hsat2; simpljoin1.
  match goal with H: Vptr _ = Vptr _ |- _ => inverts H end. 
  simpl in Hnxt.
  simp_mt Hnxt.
  simp_mt Hnxt.
  destruct Hnxt.
  subst.
  introv Hsub1 Hsub2.
  assert (Heqs: x1 = x9 /\ x21 = x15). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tint8); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heqs. subst.
  assert (Heqs: x2 = x10 /\ x45 = x27). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  destruct Heqs. subst.
  assert (Heqs: x3 = x11 /\ x51 = x33). 
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.    
  }
  destruct Heqs; subst.
  assert (Heqs: x4 = x12 /\ x57 = x39).
  {
    eapply mapstoval_false_rule_type_val_match_eq with (t:=Tptr OS_EVENT); eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.        
  }
  destruct Heqs; subst. 
  mem_eq_solver2.
  lets H00: IHtcbvl H60 H36 H3.  
  eapply H00.
  instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
Qed.

Lemma tcbllsegevaux_precise':
  forall tcbvl tcbvl' tcblh locvl locvl' ptrvl ptrvl' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= tcbllsegevaux tcblh tcbvl locvl ptrvl ->
    (e, e0, M2, i, ier, l, o2, a) |= tcbllsegevaux tcblh tcbvl' locvl' ptrvl' ->
    tcb_linked_list_same_next tcbvl tcbvl' ->
    (forall M, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2 Hnxt.
  unfold tcbllsegevaux in *.
  assert (Hemp1: o1 = empabst).
  { eapply llsegevaux_osabst_emp in Hsat1. auto. }
  assert (Hemp2: o2 = empabst).
  { eapply llsegevaux_osabst_emp in Hsat2. auto. }
  subst o1. subst o2.
  split.
  2: {
    intros. auto.
  }
  eapply llsegevaux_precise0; eauto.
Qed.

Lemma HEvExeLoc_mp_eq:
  forall locmp1 locmp2 e e0 M1 M2 i ier l o1 o2 a o,
    (e, e0, M1, i, ier, l, o1, a) |= HEvLoc locmp1 ->
    (e, e0, M2, i, ier, l, o2, a) |= HEvLoc locmp2 ->
    sub o1 o ->
    sub o2 o ->
    locmp1 = locmp2.
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  simpl in Hsat1. simpl in Hsat2.
  destruct Hsat1.
  destruct Hsat2.
  assert (Hget1: get o1 evlocid = Some (evloc locmp1)).
  {
    subst o1. join auto.
  }
  assert(Hget2: get o2 evlocid = Some  (evloc locmp2)).
  {
    subst o2. join auto.
  }
  eapply sub_get_get in Hget1; eauto.
  eapply sub_get_get in Hget2; eauto.
  congruence.
Qed.

Lemma HEvExePtr_mp_eq:
  forall ptrmp1 ptrmp2 e e0 M1 M2 i ier l o1 o2 a o,
    (e, e0, M1, i, ier, l, o1, a) |= HEvPtr ptrmp1 ->
    (e, e0, M2, i, ier, l, o2, a) |= HEvPtr ptrmp2 ->  
    sub o1 o ->
    sub o2 o ->
    ptrmp1 = ptrmp2. 
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  simpl in Hsat1. simpl in Hsat2.
  destruct Hsat1.
  destruct Hsat2.
  assert (Hget1: get o1 evptrid = Some (evptr ptrmp1)).  
  {
    subst o1. join auto.
  }
  assert(Hget2: get o2 evptrid = Some  (evptr ptrmp2)).  
  {
    subst o2. join auto.
  }
  eapply sub_get_get in Hget1; eauto.
  eapply sub_get_get in Hget2; eauto.
  congruence.
Qed.

Require Import seplog_trm_tacs.
Require Import Aarray_new_common.
Require Import Maps.
Require Import ev_aux_code.

(* Ltac change_smo' hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i0, ?ier, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i0, ier, l, o, a) m' o') with (e, e0, m', i0, ier, l, o', a) in hyp
      end).

Ltac change_smo_hyps' :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i0, ?ier, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i0, ier, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in H
      end). *)

(* Ltac simp_mem_abst :=
  repeat (
      match goal with
      | H: context [getmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getmem (t1, t2, t3, t4, t5, t6, t7)) with t3 in H
      | H: context [getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)) with t6 in H
      | H: Maps.join ?t1 empenv ?t2 |- _ => (apply map_join_emp' in H; subst t1)
      | H: Maps.join empenv ?t1 ?t2 |- _ => (apply map_join_emp'' in H; subst t1)
      | H: context [?t = empenv] |- _ => subst t
      end). *)

Lemma err_sllseg_osabst_emp :
  forall vll e e0 M i ier l o a hd tn ebls, 
    (e, e0, M, i, ier, l, o, a) |= err_sllseg hd tn vll ebls ->
    o = empabst. 
Proof.
  inductions vll.
  - introv Hsat.
    simpl in Hsat.
    simpljoin1.
  - introv Hsat.
    unfold err_sllseg in Hsat. fold err_sllseg in Hsat.
    destruct Hsat.
    simpljoin1.
    destruct H4. destruct H. simpljoin1. 
    destruct H7.  destruct H. simpljoin1.
    destruct H10. destruct H. simpljoin1.
    destruct H13. destruct H. simpljoin1.
    change_smo_hyps.
    eapply IHvll in H16; eauto.
    subst x23. simpl in H14. simpl in H11. simpl in H8. simpl in H5. simpl in H2.
    assert (x22 = empenv).
    { destruct H15. simpl in H13. destruct H13. auto. }
    subst x22.
    assert (x18 = empenv) by join auto. subst x18.
    assert (x17 = empenv).
    { destruct H12. simpl in H12. destruct H12. auto. }
    subst x17.
    assert (x13 = empenv) by join auto. subst x13.
    assert (x12 = empenv).
    { destruct H9. simpl in H9. destruct H9. auto. }
    subst x12.
    assert (x8 = empenv) by join auto. subst x8.
    assert (x7 = empenv).
    { destruct H6. simpl in H6. destruct H6. simpl in H13. auto. }
    subst x7.
    assert (x3 = empenv) by join auto. subst x3.
    apply node_osabst_emp in H3. subst x2.
    join auto.
Qed.

Lemma err_sllseg_split_first:
  forall s hd vl vll' ebls,
    s |= err_sllseg hd Vnull (vl::vll') ebls ->
    exists l posv ebls' vn, 
      hd = Vptr l /\
        get ebls l = Some posv /\
        joinsig l posv ebls' ebls /\ 
        V_errblk_next vl = Some vn /\ 
        s |= node hd vl gjb_err_blk_t ** err_sllseg vn Vnull vll' ebls'.  
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

Lemma err_sllseg_head_ptr:
  forall s hd vll pbls,
    s |= err_sllseg hd Vnull vll pbls ->
    (hd = Vnull \/ exists l, hd = Vptr l).
Proof.
  intros.
  unfold pos_sllseg in H.
  destruct vll.
  destruct H. simpljoin1. destruct H3. left. auto.
  destruct H. simpljoin1. destruct H4. destruct H. simpljoin1.
  destruct H6. right. eexists. eauto.
Qed.

Lemma err_sllseg_precise : 
  forall vll1 vll2 ebls1 ebls2 head e e0 M1 M2 i ier l o1 o2 a, 
    (e, e0, M1, i, ier, l, o1, a) |= err_sllseg head Vnull vll1 ebls1 ->
    (e, e0, M2, i, ier, l, o2, a) |= err_sllseg head Vnull vll2 ebls2 ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof. 
  inductions vll1.
  - 
    introv Hsat1 Hsat2.
    simpl in Hsat1.
    simpljoin1.
    split.
    +
      introv Hsub1 Hsub2.
      destruct vll2.
      simpl in Hsat2.
      simpljoin1.
      simpl in Hsat2.
      simpljoin1.
      inv H8.
    + 
      introv Hsub1 Hsub2.
      apply err_sllseg_osabst_emp in Hsat2.
      auto.
  -
    introv Hsat1 Hsat2.
    apply err_sllseg_split_first in Hsat1.
    destruct Hsat1 as (l01 & posv1 & pbls'1 & vn1 & H1').
    destructs H1'.
    destruct vll2.
    + 
      simpl in Hsat2. simpljoin1.
      tryfalse.
    +
      apply err_sllseg_split_first in Hsat2.
      destruct Hsat2 as (l02 & posv2 & ebls'2 & vn2 & H2').
      destructs H2'.
      assert (l01 = l02) by congruence. subst l02.
      destruct H3.
      destruct H8.
      simpljoin1.
      change_smo_hyps.
      simp_mem_abst.

      split.
      *
        introv Hsat1 Hsat2.
        lets Heq1: node_precise' H12 H17. destruct Heq1.
        assert (x0 = x).
        { apply H with (M:=M); mem_join_sub_solver. }
        subst.
        lets Heq1': node_vl_eq H17 H12. 
        instantiate (1:=M) in Heq1'.
        assert (Hveq: struct_atom_val_eq a v gjb_err_blk_t).
        { apply Heq1'; mem_join_sub_solver. }
        unfold struct_atom_val_eq in Hveq.
        unfold gjb_err_blk_t in Hveq.
        unfold struct_atom_val_eq' in Hveq.
        destruct a. unfold V_errblk_next in H2. simpl in H2. inv H2.
        destruct v. unfold V_errblk_next in H7. simpl in H7. inv H7.
        destruct a. unfold V_errblk_next in H2. simpl in H2. inverts H2. 
        destruct v1. unfold V_errblk_next in H7. simpl in H7. inverts H7.
        unfold V_errblk_next in H2. simpl in H2. inverts H2. 
        unfold V_errblk_next in H7. simpl in H7. inverts H7.
        destructs Hveq. subst.
        lets Heq': IHvll1 H18 H13.
        destruct Heq'.
        assert (x6 = x1).
        { apply H2 with (M:=M); mem_join_sub_solver. }
        subst.
        (* M1 = M2 *)
        join auto.
      *
        (* o1 = o2 *)
        apply node_osabst_emp in H17.
        apply node_osabst_emp in H12.
        apply err_sllseg_osabst_emp in H18.
        apply err_sllseg_osabst_emp in H13.
        intros.
        join auto.

Qed.

Lemma AErrblkList_precise:
  forall ebls1 ebls2 e e0 M1 M2 i ier l o1 o2 a, 
    (e, e0, M1, i, ier, l, o1, a) |= AErrblkList ebls1 -> 
    (e, e0, M2, i, ier, l, o2, a) |= AErrblkList ebls2 ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AErrblkList.
  intros.
  destruct  H. destruct H.
  destruct H0. destruct H0.
  simpljoin1.
  change_smo_hyps.
  simp_mem_abst.
  destruct H9. destruct H.
  destruct H4. destruct H0.
  simpljoin1.
  change_smo_hyps.
  simpl in H15. simpl in H9.
  simpljoin1.
  simp_mem_abst.
  assert (x17 = x14) by congruence.
  subst.
  simpl in H16. simpl in H11.
  destruct H16.
  destruct H11.
  destruct H10. destruct H5.
  
  split.
  - 
    introv Hsub1 Hsub2.
    lets: mapstoval_true_mem_eq M H2 H7.
    mem_join_sub_solver.
    mem_join_sub_solver.
    subst.
    assert (Hxptr: x = Vnull \/ (exists l1, x = Vptr l1)).
    { eapply err_sllseg_head_ptr. eauto. }
    assert (Hx1ptr: x1 = Vnull \/ (exists l2, x1 = Vptr l2)).
    { eapply err_sllseg_head_ptr. eauto. }
    assert (x = x1).
    {
      destruct H2. destruct H2.
      destruct H7. destruct H7.
      unfold encode_val in H2. simpl in H2. 
      assert (length x0 = 4%nat).
      { destruct x; try (subst x0; auto). destruct a0. auto. }
      unfold encode_val in H7. simpl in H7.
      assert (length x9 = 4%nat).
      { destruct x1; try (subst x9; auto). destruct a0. auto. }
      lets H00: ptomvallist_true_sub_vl_eq H11 H12.
      rewrite H13 in H00. rewrite H14 in H00.
      specialize (H00 (eq_refl _)).
      assert (H'': x0 = x9).
      {
        apply H00. instantiate (1:=M).
        mem_join_sub_solver. mem_join_sub_solver.
      }
      rewrite <- H2 in H''. rewrite <- H7 in H''.
      destruct Hxptr; destruct Hx1ptr.
      subst. auto.
      destruct H16. subst. destruct x12. inverts H''.
      destruct H15. subst. destruct x12. inverts H''.
      destruct H15. destruct H16. subst.
      destruct x12. destruct x13. inverts H''. auto.
    }
    subst.
    lets H00: err_sllseg_precise H5 H10.
    destruct H00.
    cut (x3 = x8).
    + intros; join auto.
    + apply H11 with (M:=M); mem_join_sub_solver.
  -
    apply err_sllseg_osabst_emp in H10.
    apply err_sllseg_osabst_emp in H5.
    intros.
    join auto.

Qed.

Lemma pos_sllseg_osabst_emp :
  forall vll e e0 M i ier l o a hd tn pbls, 
    (e, e0, M, i, ier, l, o, a) |= pos_sllseg hd tn vll pbls ->
    o = empabst. 
Proof.
  inductions vll.
  - introv Hsat.
    simpl in Hsat.
    simpljoin1.
  - introv Hsat.
    unfold pos_sllseg in Hsat. fold pos_sllseg in Hsat.
    destruct Hsat.
    simpljoin1.
    destruct H4. destruct H. simpljoin1. 
    destruct H7.  destruct H. simpljoin1.
    destruct H10. destruct H. simpljoin1.
    destruct H13. destruct H. simpljoin1.
    change_smo_hyps.
    eapply IHvll in H16; eauto.
    subst x23. simpl in H14. simpl in H11. simpl in H8. simpl in H5. simpl in H2.
    assert (x22 = empenv).
    { destruct H15. simpl in H13. destruct H13. auto. }
    subst x22.
    assert (x18 = empenv) by join auto. subst x18.
    assert (x17 = empenv).
    { destruct H12. simpl in H12. destruct H12. auto. }
    subst x17.
    assert (x13 = empenv) by join auto. subst x13.
    assert (x12 = empenv).
    { destruct H9. simpl in H9. destruct H9. auto. }
    subst x12.
    assert (x8 = empenv) by join auto. subst x8.
    assert (x7 = empenv).
    { destruct H6. simpl in H6. destruct H6. simpl in H13. auto. }
    subst x7.
    assert (x3 = empenv) by join auto. subst x3.
    apply node_osabst_emp in H3. subst x2.
    join auto.
Qed.

Lemma pos_sllseg_split_first:
  forall s hd vl vll' pbls,
    s |= pos_sllseg hd Vnull (vl::vll') pbls ->
    exists l posv pbls' vn, 
      hd = Vptr l /\
        get pbls l = Some posv /\
        joinsig l posv pbls' pbls /\ 
        ev_aux_code.V_posblk_next vl = Some vn /\ 
        s |= node hd vl ev_aux_code.gjb_pos_blk_t ** pos_sllseg vn Vnull vll' pbls'.  
Proof.
  introv Hsat.
  unfold pos_sllseg in Hsat.
  fold pos_sllseg in Hsat.
  destruct s as [[[[[[]]]]]].
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
  destruct p.
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
  remember (node hd vl ev_aux_code.gjb_pos_blk_t) as P.
  remember (pos_sllseg x16 Vnull vll' x11) as Q.
  simpl.
  exists x x0. exists m. exists x2 x3. exists o.
  splits; auto.
Qed.

Lemma pos_sllseg_head_ptr:
  forall s hd vll pbls,
    s |= pos_sllseg hd Vnull vll pbls ->
    (hd = Vnull \/ exists l, hd = Vptr l).
Proof.
  intros.
  unfold pos_sllseg in H.
  destruct vll.
  destruct H. simpljoin1. destruct H3. left. auto.
  destruct H. simpljoin1. destruct H4. destruct H. simpljoin1.
  destruct H6. right. eexists. eauto.
Qed.

Lemma pos_sllseg_precise' : 
  forall vll1 vll2 pbls1 pbls2 head e e0 M1 M2 i ier l o1 o2 a, 
    (e, e0, M1, i, ier, l, o1, a) |= pos_sllseg head Vnull vll1 pbls1 ->
    (e, e0, M2, i, ier, l, o2, a) |= pos_sllseg head Vnull vll2 pbls2 ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof. 
  inductions vll1.
  - 
    introv Hsat1 Hsat2.
    simpl in Hsat1.
    simpljoin1.
    split.
    +
      introv Hsub1 Hsub2.
      destruct vll2.
      simpl in Hsat2.
      simpljoin1.
      simpl in Hsat2.
      simpljoin1.
      inv H8.
    + 
      introv Hsub1 Hsub2.
      apply pos_sllseg_osabst_emp in Hsat2.
      auto.
  -
    introv Hsat1 Hsat2.
    apply pos_sllseg_split_first in Hsat1.
    destruct Hsat1 as (l01 & posv1 & pbls'1 & vn1 & H1').
    destructs H1'.
    destruct vll2.
    + 
      simpl in Hsat2. simpljoin1.
      tryfalse.
    +
      apply pos_sllseg_split_first in Hsat2.
      destruct Hsat2 as (l02 & posv2 & pbls'2 & vn2 & H2').
      destructs H2'.
      assert (l01 = l02) by congruence. subst l02.
      destruct H3.
      destruct H8.
      simpljoin1.
      change_smo_hyps.
      simp_mem_abst.

      split.
      *
        introv Hsat1 Hsat2.
        lets Heq1: node_precise' H12 H17. destruct Heq1.
        assert (x0 = x).
        { apply H with (M:=M); mem_join_sub_solver. }
        subst.
        lets Heq1': node_vl_eq H17 H12. 
        instantiate (1:=M) in Heq1'.
        assert (Hveq: struct_atom_val_eq a v ev_aux_code.gjb_pos_blk_t).
        { apply Heq1'; mem_join_sub_solver. }
        unfold struct_atom_val_eq in Hveq.
        unfold ev_aux_code.gjb_pos_blk_t in Hveq.
        unfold struct_atom_val_eq' in Hveq.
        destruct a. unfold ev_aux_code.V_posblk_next in H2. simpl in H2. inv H2.
        destruct v. unfold ev_aux_code.V_posblk_next in H7. simpl in H7. inv H7.
        destruct a. unfold ev_aux_code.V_posblk_next in H2. simpl in H2. inverts H2. 
        destruct v1. unfold ev_aux_code.V_posblk_next in H7. simpl in H7. inverts H7.
        unfold ev_aux_code.V_posblk_next in H2. simpl in H2. inverts H2. 
        unfold ev_aux_code.V_posblk_next in H7. simpl in H7. inverts H7.
        destructs Hveq. subst.
        lets Heq': IHvll1 H18 H13.
        destruct Heq'.
        assert (x6 = x1).
        { apply H2 with (M:=M); mem_join_sub_solver. }
        subst.
        (* M1 = M2 *)
        join auto.
      *
        (* o1 = o2 *)
        apply node_osabst_emp in H17.
        apply node_osabst_emp in H12.
        apply pos_sllseg_osabst_emp in H18.
        apply pos_sllseg_osabst_emp in H13.
        intros.
        join auto.
Qed.

Lemma APosblkList_precise' :
  forall pbls1 pbls2 e e0 M1 M2 i ier l o1 o2 a, 
    (e, e0, M1, i, ier, l, o1, a) |= APosblkList pbls1 -> 
    (e, e0, M2, i, ier, l, o2, a) |= APosblkList pbls2 ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
        sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APosblkList.
  intros.
  destruct  H. destruct H.
  destruct H0. destruct H0.
  simpljoin1.
  change_smo_hyps.
  simp_mem_abst.
  destruct H9. destruct H.
  destruct H4. destruct H0.
  simpljoin1.
  change_smo_hyps.
  simpl in H15. simpl in H9.
  simpljoin1.
  simp_mem_abst.
  assert (x17 = x14) by congruence.
  subst.
  simpl in H16. simpl in H11.
  destruct H16.
  destruct H11.
  destruct H10. destruct H5.
  
  split.
  - 
    introv Hsub1 Hsub2.
    lets: mapstoval_true_mem_eq M H2 H7.
    mem_join_sub_solver.
    mem_join_sub_solver.
    subst.
    assert (Hxptr: x = Vnull \/ (exists l1, x = Vptr l1)).
    { eapply pos_sllseg_head_ptr. eauto. }
    assert (Hx1ptr: x1 = Vnull \/ (exists l2, x1 = Vptr l2)).
    { eapply pos_sllseg_head_ptr. eauto. }
    assert (x = x1).
    {
      destruct H2. destruct H2.
      destruct H7. destruct H7.
      unfold encode_val in H2. simpl in H2. 
      assert (length x0 = 4%nat).
      { destruct x; try (subst x0; auto). destruct a0. auto. }
      unfold encode_val in H7. simpl in H7.
      assert (length x9 = 4%nat).
      { destruct x1; try (subst x9; auto). destruct a0. auto. }
      lets H00: ptomvallist_true_sub_vl_eq H11 H12.
      rewrite H13 in H00. rewrite H14 in H00.
      specialize (H00 (eq_refl _)).
      assert (H'': x0 = x9).
      {
        apply H00. instantiate (1:=M).
        mem_join_sub_solver. mem_join_sub_solver.
      }
      rewrite <- H2 in H''. rewrite <- H7 in H''.
      destruct Hxptr; destruct Hx1ptr.
      subst. auto.
      destruct H16. subst. destruct x12. inverts H''.
      destruct H15. subst. destruct x12. inverts H''.
      destruct H15. destruct H16. subst.
      destruct x12. destruct x13. inverts H''. auto.
    }
    subst.
    lets H00: pos_sllseg_precise' H5 H10.
    destruct H00.
    cut (x3 = x8).
    + intros; join auto.
    + apply H11 with (M:=M); mem_join_sub_solver.
  -
    apply pos_sllseg_osabst_emp in H10.
    apply pos_sllseg_osabst_emp in H5.
    intros.
    join auto.
Qed.

Lemma Hpbls_precise':
  forall pbls pbls' e e0 M1 M2 i ier l o1 o2 a, 
  (e, e0, M1, i, ier, l, o1, a) |= Hpbls pbls ->
  (e, e0, M2, i, ier, l, o2, a) |= Hpbls pbls' -> 
  (forall M : mem, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H0, H2.
  split.
  intros. congruence.
  intros.
  lets H00: osabst_sub_sig_eq H H1.
  congruence.
Qed.

Lemma HSEMInfo_precise':
  forall embls embls' e e0 M1 M2 i ier l o1 o2 a,  
  (e, e0, M1, i, ier, l, o1, a) |= HSEMInfo embls ->
  (e, e0, M2, i, ier, l, o2, a) |= HSEMInfo embls' -> 
  (forall M : mem, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H0, H2.
  split.
  intros. congruence.
  intros.
  lets H00: osabst_sub_sig_eq H H1.
  congruence.
Qed.

Lemma HMuxInfo_precise': 
  forall embls embls' e e0 M1 M2 i ier l o1 o2 a,  
  (e, e0, M1, i, ier, l, o1, a) |= HMuxInfo embls ->
  (e, e0, M2, i, ier, l, o2, a) |= HMuxInfo embls' ->  
  (forall M : mem, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H0, H2.
  split.
  intros. congruence.
  intros.
  lets H00: osabst_sub_sig_eq H H1.
  congruence.
Qed.

Lemma HQAttr_precise':
  forall embls embls' e e0 M1 M2 i ier l o1 o2 a,  
  (e, e0, M1, i, ier, l, o1, a) |= HQAttr embls ->
  (e, e0, M2, i, ier, l, o2, a) |= HQAttr embls' ->   
  (forall M : mem, sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst, sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  introv Hsat1 Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H0, H2.
  split.
  intros. congruence.
  intros.
  lets H00: osabst_sub_sig_eq H H1.
  congruence.
Qed.

Lemma Aarray_new'_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,
    new_array_type_vallist_match t vl ->
    new_array_type_vallist_match t vl' ->
      (e, e0, M1, i, ier, l, o1, a) |= Aarray_new' head n t vl ->
      (e, e0, M2, i, ier, l, o2, a) |= Aarray_new' head n t vl' ->
      (forall M : mem,
         sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
         sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intro. inductions vl; intros. rename H into HX1. rename H0 into HX2. rename H1 into H. rename H2 into H0.
  destruct vl'; destruct n;simpl in H, H0; tryfalse.
  simpljoin1. split; intros; auto.
  rename H into HX1. rename H0 into HX2. rename H1 into H. rename H2 into H0.

  destruct vl';destruct n; tryfalse.
  simpl in H, H0.
  destruct t; destruct v;destruct a; tryfalse; try(destruct a) ;try(destruct v0);tryfalse;
  destruct head;  simpl in H, H0; simpl in HX1, HX2; simpljoin1;
  try (
          lets Hx: IHvl H17 H14 H11 H5;
          simpljoin1; split; intros;
          [ eapply eq_join_eq; eauto;
              [ eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver
                | mem_eq_solver M]
            | apply H0 with (o:=o); eauto]);
   try (
             lets Hx: IHvl H12 H10 H5; auto;
             simpljoin1; split; intros;
            [ eapply eq_join_eq; eauto; 
                [ eapply Aarray'_precise'; [ eapply H9 | eapply H4 | idtac | idtac];
                      [ lets Hx1: IHvl H12 H10 H5; auto;
                        assert (Hsub: sub x5 M1) by (unfold sub; exists x6; apply H6);
                        apply sub_trans with (m2:=M1); [ apply Hsub |  apply H2 ]
                       | assert (Hsub: sub x M2) by (unfold sub; exists x0; apply H1);
                         apply sub_trans with (m2:=M2); [ apply Hsub | apply H7]]
                | mem_eq_solver M]
          | eapply eq_join_eq;eauto;
              [ eapply Aarray'_precise'; [ eapply H9 | eapply H4 | idtac | idtac];
                   [ assert (Hsub: sub x8 o1) by (unfold sub; exists x9; apply H8);
                     apply sub_trans with (m2:=o1); [ apply Hsub | apply H2]
                    | assert (Hsub: sub x2 o2) by (unfold sub; exists x3; apply H3);
                      apply sub_trans with (m2:=o2); [apply Hsub | apply H7]]
              | osabst_eq_solver o]]);
    try ( 
             lets Hx: IHvl H12 H10 H5; auto;
             simpljoin1; split; intros;
            [ eapply eq_join_eq; eauto; 
                [ eapply Astruct'_precise'; [idtac | idtac | eapply H9 | eapply H4 | idtac | idtac];
                   [ simpl; destruct d; tryfalse;auto | simpl; destruct d; tryfalse;auto | idtac | idtac];
                      [ lets Hx1: IHvl H12 H10 H5; auto;
                        assert (Hsub: sub x5 M1) by (unfold sub; exists x6; apply H6);
                        apply sub_trans with (m2:=M1); [ apply Hsub |  apply H2 ]
                       | assert (Hsub: sub x M2) by (unfold sub; exists x0; apply H1);
                         apply sub_trans with (m2:=M2); [ apply Hsub | apply H7]]
                | mem_eq_solver M]
          | eapply eq_join_eq;eauto;
              [ eapply Astruct'_precise'; [idtac | idtac | eapply H9 | eapply H4 | idtac | idtac];
                 [ simpl; destruct d; tryfalse;auto | simpl; destruct d; tryfalse;auto | idtac | idtac];
                   [ assert (Hsub: sub x8 o1) by (unfold sub; exists x9; apply H8);
                     apply sub_trans with (m2:=o1); [ apply Hsub | apply H2]
                    | assert (Hsub: sub x2 o2) by (unfold sub; exists x3; apply H3);
                      apply sub_trans with (m2:=o2); [apply Hsub | apply H7]]
              | osabst_eq_solver o]]);
                try (
                  lets Hx: IHvl H12 H10 H5; auto;
                  simpljoin1; split; intros;
                [ eapply eq_join_eq; eauto; 
                    [ eapply Astruct'_precise'; [idtac | idtac | eapply H9 | eapply H4 | idtac | idtac];
                        [ simpl; destruct d; tryfalse;auto | simpl; destruct d; tryfalse;auto | idtac | idtac];
                          [ lets Hx1: IHvl H12 H10 H5; auto;
                            assert (Hsub: sub x5 M1) by (unfold sub; exists x6; apply H6);
                            apply sub_trans with (m2:=M1); [ apply Hsub |  apply H2 ]
                            | assert (Hsub: sub x M2) by (unfold sub; exists x0; apply H1);
                              apply sub_trans with (m2:=M2); [ apply Hsub | apply H7]]
                    | mem_eq_solver M]
              | eapply eq_join_eq;eauto;
                  [ eapply Astruct'_precise'; [idtac | idtac | eapply H9 | eapply H4 | idtac | idtac];
                      [ simpl; destruct d; tryfalse;auto | simpl; destruct d; tryfalse;auto | idtac | idtac];
                        [ assert (Hsub: sub x8 o1) by (unfold sub; exists x9; apply H8);
                          apply sub_trans with (m2:=o1); [ apply Hsub | apply H2]
                        | assert (Hsub: sub x2 o2) by (unfold sub; exists x3; apply H3);
                          apply sub_trans with (m2:=o2); [apply Hsub | apply H7]]
                  | osabst_eq_solver o]]).
    
Qed.

Lemma Aarray_new_precise' :
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,
    new_array_type_vallist_match t vl ->
    new_array_type_vallist_match t vl' ->
      (e, e0, M1, i, ier, l, o1, a) |= Aarray_new head (Tarray t n) vl ->
      (e, e0, M2, i, ier, l, o2, a) |= Aarray_new head (Tarray t n) vl' ->
      (forall M : mem,
         sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
         sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   intros.
  unfold Aarray_new in H1, H2.
  destruct t; tryfalse;
  try (eapply Aarray_new'_precise'; [apply H | apply H0| apply H1 | apply H2]).
Qed.

Lemma Aarray_new'_osabst_emp :
  forall vl head n t e e0 M i ier lo o a ,
    (e, e0, M, i, ier, lo, o, a) |= Aarray_new' head n t vl -> 
    o = empabst.
Proof.

  inductions vl; intros.
  destruct n; simpl in H; simpljoin1; tryfalse.
  destruct n; tryfalse.
  simpl in H;tryfalse.
  destruct t. destruct a; tryfalse.
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse.
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.
  destruct a; tryfalse. 
  destruct a; tryfalse.
  destruct head.
  simpl in H; simpljoin1; eapply IHvl; eauto.

  destruct head.
  simpl in H; simpljoin1. lets Hx: IHvl H4.
  apply Aarray'_osabst_emp in H3.
  assert (x3 = o). rewrite H3 in H2.  apply map_join_emp''. apply H2. rewrite H in Hx. apply Hx.

  destruct head.
  simpl in H; simpljoin1. lets Hx: IHvl H4.
  apply Astruct'_osabst_emp in H3.
  assert (x3 = o). rewrite H3 in H2.  apply map_join_emp''. apply H2. rewrite H in Hx. apply Hx.
  
  destruct head.
  simpl in H; simpljoin1. lets Hx: IHvl H4.
  apply Astruct'_osabst_emp in H3.
  assert (x3 = o). rewrite H3 in H2.  apply map_join_emp''. apply H2. rewrite H in Hx. apply Hx.
Qed.

Lemma Aarray_new_osabst_emp :
  forall vl head t n e e0 M i ier lo o a ,
    (e, e0, M, i, ier, lo, o, a) |= Aarray_new head (Tarray t n) vl ->
    o = empabst.
Proof.
  intros.
  unfold Aarray in H; destruct t; tryfalse;
  eapply Aarray_new'_osabst_emp; eauto.
Qed.

(* Lemma struct_atom_val_eq_vl_eq: *)
(*   forall vl1 vl2,  *)
(*     struct_atom_val_eq vl1 vl2 os_ucos_h.sem_info_t -> *)
(*     vl1 = vl2. *)
(* Proof. *)
(*   intros. *)
(*   destruct vl1; destruct vl2; tryfalse. *)
(*   auto. *)
(*   simpl in H. destruct H. subst v0. *)
(*   destruct vl1; destruct vl2; tryfalse. *)
(*   auto. *)
(*   simpl in H0. destruct H0. subst v1. *)
(*   destruct vl1; destruct vl2; tryfalse. *)
(*   auto. *)
(*   simpl in H0. destruct H0. subst v2. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   destruct H0. subst v3. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   simpl in H0. destruct H0. subst v4. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   destruct H0. subst v5. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   destruct H0. subst v6. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   destruct H0. subst v7. *)
(*   destruct vl1; destruct vl2; simpl in *; tryfalse. *)
(*   auto. *)
(*   admit. *)
(* Admitted. *)

(* copy form Aarray_new_common.v  *)
Lemma Aarray_new_emp:
  forall e e0 i ier l a b i0, 
    (e, e0, empenv, i, ier, l, empenv, a) |= Aarray_new (b, i0) (Tarray sem_info_t 0) nil. 
Proof.
  intros.
  unfold Aarray_new.
  unfold Aarray_new'.
  simpl; split; auto. 
  unfold emposabst.
  auto.
Qed.

Lemma Aarray'_vl_eq:
  forall vl vl' (M1 M2 M:mem) o1 o2 e e0 i ier l a n adr tp, 
    array_type_vallist_match tp vl -> 
    array_type_vallist_match tp vl' -> 
    (e, e0, M1, i, ier, l, o1, a) |= Aarray' adr n tp vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray' adr n tp vl' -> 
    sub M1 M ->
    sub M2 M ->
    vl = vl'.
Proof.
  inductions vl; induction vl';
  introv Hmat1 Hmat2 Hsat1 Hsat2 Hsub1 Hsub2; auto.
  destruct n.
  simpl in Hsat2; tryfalse.
  simpl in Hsat1; tryfalse.
  destruct n.
  simpl in Hsat2; tryfalse.
  simpl in Hsat1; tryfalse.
  destruct n.
  simpl in Hsat1. tryfalse.
  simpl in Hsat1, Hsat2.
  destruct adr.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in Hmat1, Hmat2.
  destruct Hmat1 as (Hr1 & Hmt1).
  destruct Hmat2 as (Hr2 & Hmt2).
  assert (Hsub1': sub x6 M) by mem_join_sub_solver.
  assert (Hsub2': sub x0 M) by mem_join_sub_solver.
  lets H00: IHvl H10 H5 Hsub1' Hsub2'; auto.
  simpl in H9, H4.
  simpljoin.
  lets Heq: mapstoval_true_rule_type_val_match_eq M Hr1 Hr2 H2 H.
  destruct Heq; subst; auto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

Lemma Aarray_vl_eq:
  forall vl vl' (M1 M2 M:mem) o1 o2 e e0 i ier l a n adr tp, 
    array_type_vallist_match tp vl -> 
    array_type_vallist_match tp vl' -> 
    (e, e0, M1, i, ier, l, o1, a) |= Aarray adr (Tarray tp n) vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray adr (Tarray tp n) vl' -> 
    sub M1 M ->
    sub M2 M ->
    vl = vl'.
Proof.
  unfold Aarray.
  apply Aarray'_vl_eq.
Qed. 

Lemma Aarray_new'_vll_eq:
  forall vll vll' (M1 M2 M:mem) o1 o2 e e0 i ier l a n adr , 
    new_array_type_vallist_match os_ucos_h.sem_info_t vll -> 
    new_array_type_vallist_match os_ucos_h.sem_info_t vll' -> 
    (e, e0, M1, i, ier, l, o1, a) |= Aarray_new' adr n os_ucos_h.sem_info_t vll ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray_new' adr n os_ucos_h.sem_info_t vll' -> 
    sub M1 M ->
    sub M2 M ->
    (forall k vl vl',
     nth_error vll k = Some vl ->
     nth_error vll' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t).
Proof.
  inductions vll.
  intros.
  destruct vll'.
  auto.
  unfold Aarray_new' in H.
  rewrite nth_error_nil in *; tryfalse.
  rewrite nth_error_nil in *; tryfalse.

  introv Hmt1 Hmt2 Hsat1 Hsat2.
  destruct vll'.
  destruct n.
  simpl in Hsat1. tryfalse.
  simpl in Hsat2. tryfalse.

  destruct n.
  simpl in Hsat1. tryfalse.
  destruct adr.
  eapply Aarray_new'_succ_imp in Hsat1; eauto.
  eapply Aarray_new'_succ_imp in Hsat2; eauto.
  introv Hsub1 Hsub2.

  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  assert (Hsub1': sub x6 M) by mem_join_sub_solver.
  assert (Hsub2': sub x0 M) by mem_join_sub_solver.
  lets H00: IHvll H10 H5 Hsub1' Hsub2'.
  unfold new_array_type_vallist_match in Hmt1.
  fold new_array_type_vallist_match in Hmt1.
  unfold os_ucos_h.sem_info_t in Hmt1.
  fold os_ucos_h.sem_info_t in Hmt1.
  destruct Hmt1. auto.
  unfold new_array_type_vallist_match in Hmt2.
  fold new_array_type_vallist_match in Hmt2.
  unfold os_ucos_h.sem_info_t in Hmt2.
  fold os_ucos_h.sem_info_t in Hmt2.
  destruct Hmt2. auto.

  unfold Aarray_new' in H9.
  unfold os_ucos_h.sem_info_t in H9. fold os_ucos_h.sem_info_t in H9.
  unfold Aarray_new' in H4.
  unfold os_ucos_h.sem_info_t in H4. fold os_ucos_h.sem_info_t in H4.
  apply astar_r_aemp_elim in H9.
  apply astar_r_aemp_elim in H4.
  unfold new_array_type_vallist_match in Hmt1.
  fold new_array_type_vallist_match in Hmt1.
  unfold os_ucos_h.sem_info_t in Hmt1.
  fold os_ucos_h.sem_info_t in Hmt1.
  destruct Hmt1. 
  unfold new_array_type_vallist_match in Hmt2.
  fold new_array_type_vallist_match in Hmt2.
  unfold os_ucos_h.sem_info_t in Hmt2.
  fold os_ucos_h.sem_info_t in Hmt2.
  destruct Hmt2.
  assert (Hveq: struct_atom_val_eq a v os_ucos_h.sem_info_t). 
  {
    eapply Astruct_vl_eq; eauto.
    instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver.
  }
  introv Hnth Hnth'.
  destruct k; simpl in Hnth,Hnth'.
  inverts Hnth; inverts Hnth'; auto.
  eapply H00; eauto.
Qed.

(* Lemma Aarray_new'_vll_eq: *)
(*   forall vll vll' (M1 M2 M:mem) o1 o2 e e0 i ier l a n adr ,  *)
(*     new_array_type_vallist_match os_ucos_h.sem_info_t vll ->  *)
(*     new_array_type_vallist_match os_ucos_h.sem_info_t vll' ->  *)
(*     (e, e0, M1, i, ier, l, o1, a) |= Aarray_new' adr n os_ucos_h.sem_info_t vll -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= Aarray_new' adr n os_ucos_h.sem_info_t vll' ->  *)
(*     sub M1 M -> *)
(*     sub M2 M -> *)
(*     vll = vll'.  *)
(* Proof.  *)
(*   inductions vll. *)
(*   intros. *)
(*   destruct vll'. *)
(*   auto. *)
(*   unfold Aarray_new' in H. *)
(*   destruct n. *)
(*   simpl in H0. tryfalse. *)
(*   tryfalse. *)

(*   introv Hmt1 Hmt2 Hsat1 Hsat2. *)
(*   destruct vll'. *)
(*   destruct n. *)
(*   simpl in Hsat1. tryfalse. *)
(*   simpl in Hsat2. tryfalse. *)

(*   destruct n. *)
(*   simpl in Hsat1. tryfalse. *)
(*   destruct adr. *)
(*   eapply Aarray_new'_succ_imp in Hsat1; eauto. *)
(*   eapply Aarray_new'_succ_imp in Hsat2; eauto. *)
(*   introv Hsub1 Hsub2. *)

(*   simpl_sat Hsat1. *)
(*   simpl_sat Hsat2. *)
(*   simpljoin1. *)
(*   assert (Hsub1': sub x6 M) by mem_join_sub_solver. *)
(*   assert (Hsub2': sub x0 M) by mem_join_sub_solver. *)
(*   lets H00: IHvll H10 H5 Hsub1' Hsub2'. *)
(*   unfold new_array_type_vallist_match in Hmt1. *)
(*   fold new_array_type_vallist_match in Hmt1. *)
(*   unfold os_ucos_h.sem_info_t in Hmt1. *)
(*   fold os_ucos_h.sem_info_t in Hmt1. *)
(*   destruct Hmt1. auto. *)
(*   unfold new_array_type_vallist_match in Hmt2. *)
(*   fold new_array_type_vallist_match in Hmt2. *)
(*   unfold os_ucos_h.sem_info_t in Hmt2. *)
(*   fold os_ucos_h.sem_info_t in Hmt2. *)
(*   destruct Hmt2. auto. *)

(*   unfold Aarray_new' in H9. *)
(*   unfold os_ucos_h.sem_info_t in H9. fold os_ucos_h.sem_info_t in H9. *)
(*   unfold Aarray_new' in H4. *)
(*   unfold os_ucos_h.sem_info_t in H4. fold os_ucos_h.sem_info_t in H4. *)
(*   apply astar_r_aemp_elim in H9. *)
(*   apply astar_r_aemp_elim in H4. *)
(*   unfold new_array_type_vallist_match in Hmt1. *)
(*   fold new_array_type_vallist_match in Hmt1. *)
(*   unfold os_ucos_h.sem_info_t in Hmt1. *)
(*   fold os_ucos_h.sem_info_t in Hmt1. *)
(*   destruct Hmt1.  *)
(*   unfold new_array_type_vallist_match in Hmt2. *)
(*   fold new_array_type_vallist_match in Hmt2. *)
(*   unfold os_ucos_h.sem_info_t in Hmt2. *)
(*   fold os_ucos_h.sem_info_t in Hmt2. *)
(*   destruct Hmt2. *)
(*   assert (Hveq: struct_atom_val_eq a v os_ucos_h.sem_info_t).  *)
(*   { *)
(*     eapply Astruct_vl_eq; eauto. *)
(*     instantiate (1:=M). mem_join_sub_solver. mem_join_sub_solver. *)
(*   } *)
(*   apply struct_atom_val_eq_vl_eq in Hveq. *)
(*   subst a. *)
(*   congruence. *)
(* Qed. *)

Lemma Aarray_new_vll_eq:
  forall vll vll' M1 M2 o1 o2 e e0 i ier l a adr M n, 
    new_array_type_vallist_match os_ucos_h.sem_info_t vll -> 
    new_array_type_vallist_match os_ucos_h.sem_info_t vll' -> 
    (e, e0, M1, i, ier, l, o1, a) |= Aarray_new adr (Tarray os_ucos_h.sem_info_t n) vll ->
    (e, e0, M2, i, ier, l, o2, a) |= Aarray_new adr (Tarray os_ucos_h.sem_info_t n) vll' -> 
    sub M1 M ->
    sub M2 M ->
    (forall k vl vl',
     nth_error vll k = Some vl ->
     nth_error vll' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t).
Proof.
  intros.
  unfold Aarray_new in *.
  unfold os_ucos_h.sem_info_t in *.
  fold os_ucos_h.sem_info_t in *.
  eapply Aarray_new'_vll_eq with (vll := vll); eauto.
Qed.

(* Lemma Aarray_new_vll_eq: *)
(*   forall vll vll' M1 M2 o1 o2 e e0 i ier l a adr M n,  *)
(*     new_array_type_vallist_match os_ucos_h.sem_info_t vll ->  *)
(*     new_array_type_vallist_match os_ucos_h.sem_info_t vll' ->  *)
(*     (e, e0, M1, i, ier, l, o1, a) |= Aarray_new adr (Tarray os_ucos_h.sem_info_t n) vll -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= Aarray_new adr (Tarray os_ucos_h.sem_info_t n) vll' ->  *)
(*     sub M1 M -> *)
(*     sub M2 M -> *)
(*     vll = vll'.  *)
(* Proof. *)
(*   intros. *)
(*   unfold Aarray_new in *. *)
(*   unfold os_ucos_h.sem_info_t in *. *)
(*   fold os_ucos_h.sem_info_t in *. *)
(*   eapply Aarray_new'_vll_eq; eauto. *)
(* Qed. *)

Lemma ASeminfo_vll_eq:
  forall bi bi' vll vll' M1 M2 o1 o2 e e0 i ier l a M, 
    (e, e0, M1, i, ier, l, o1, a) |= ASeminfo bi vll  ->
    (e, e0, M2, i, ier, l, o2, a) |= ASeminfo bi' vll' ->
    sub M1 M ->
    sub M2 M ->
    (forall k vl vl',
     nth_error vll k = Some vl ->
     nth_error vll' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t).
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold ASeminfo in *.
  sep split in Hsat1.
  sep split in Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  simpl in H12. simpl in H6.
  simpljoin1.
  rewrite H23 in H12. inverts H12.
  assert (Hsub1': sub x5 M) by mem_join_sub_solver.
  assert (Hsub2': sub x M) by mem_join_sub_solver.
  lets H00: mapstoval_true_vptr_eq H24 H15 Hsub1' Hsub2'.
  destruct H00.
  subst bi.
  eapply Aarray_new_vll_eq with (vll:= vll); eauto.
  instantiate (1:=M).
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

(* Lemma ASeminfo_vll_eq: *)
(*   forall bi bi' vll vll' scapl scapl' M1 M2 o1 o2 e e0 i ier l a M,  *)
(*     (e, e0, M1, i, ier, l, o1, a) |= ASeminfo bi vll ** ASemCap bi scapl -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= ASeminfo bi' vll' ** ASemCap bi scapl' -> *)
(*     sub M1 M -> *)
(*     sub M2 M -> *)
(*     vll = vll' /\ scapl = scapl'. *)
(* Proof. *)
(*   introv Hsat1 Hsat2 Hsub1 Hsub2. *)
(*   unfold ASeminfo in *. *)
(*   sep split in Hsat1. *)
(*   sep split in Hsat2. *)
(*   simpl_sat Hsat1. *)
(*   simpl_sat Hsat2. *)
(*   simpljoin1. *)
(*   simpl in H12. simpl in H6. *)
(*   simpljoin1. *)
(*   admit. *)
(*   (* rewrite H23 in H12. inverts H12. *)
(*   assert (Hsub1': sub x5 M) by mem_join_sub_solver. *)
(*   assert (Hsub2': sub x M) by mem_join_sub_solver. *)
(*   lets H00: mapstoval_true_vptr_eq H24 H15 Hsub1' Hsub2'. *)
(*   destruct H00. *)
(*   subst bi. *)
(*   eapply Aarray_new_vll_eq; eauto. *)
(*   instantiate (1:=M). *)
(*   mem_join_sub_solver. *)
(*   mem_join_sub_solver. *)
(* Qed. *) *)
(* Admitted. *)

Lemma AEvtCap_vll_eq:
  forall scapl scapl' bi fieldname eibtype M1 M2 o1 o2 e e0 i ier l a M,
    length scapl = length scapl' ->
    (e, e0, M1, i, ier, l, o1, a) |= AEvtCap bi scapl fieldname eibtype ->
    (e, e0, M2, i, ier, l, o2, a) |= AEvtCap bi scapl' fieldname eibtype ->
    sub M1 M ->
    sub M2 M ->
    scapl = scapl'.
Proof.
  induction scapl; induction scapl';
  introv Hlen Hsat1 Hsat2 Hsub1 Hsub2;
  simpl in Hlen; tryfalse.
  auto.
  destruct bi.
  eapply Nat.succ_inj in Hlen.
  unfold AEvtCap in Hsat1, Hsat2.
  fold AEvtCap in Hsat1, Hsat2.
  sep destruct Hsat1; sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  rewrite H in H2; inverts H2.
  lets Heq: Aarray_vl_eq M H0 H3 H15 H10.
  destruct Heq; auto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  eapply IHscapl with (M := M) in H11; eauto.
  subst; auto.
  mem_join_sub_solver.
  mem_join_sub_solver.
Qed.

Lemma map_Vint32_eq:
  forall sc1 sc2,
    map Vint32 sc1 = map Vint32 sc2 -> sc1 = sc2.
Proof.
  intros.
  generalize dependent sc2.
  induction sc1.
  {
    intros sc2 H.
    simpl in *.
    destruct sc2; tryfalse. auto.
  }
  {
    intros sc2 H.
    simpl in *.
    destruct sc2; tryfalse.
    simpl in *. inversion H.
    apply IHsc1 in H2.
    rewrite H2. auto.
  }
Qed.

(* Lemma RHL_EINFO_vl_eq_eib_eq: *)
(*   forall vl eib1 eib2 vhold,   *)
(*     RHL_EINFO_P vl eib1 vhold ->  *)
(*     RHL_EINFO_P vl eib2 vhold -> *)
(*     eib1 = eib2.  *)
(* Proof. *)
(*   introv Hre1 Hre2. *)
(*   unfold RHL_EINFO_P in *. *)
(*   destruct eib1 as ((e1 & tp1) & sc1). *)
(*   destruct eib2 as ((e2 & tp2) & sc2). *)
(*   specialize (Hre1 e1 tp1 sc1 (eq_refl _)). *)
(*   specialize (Hre2 e2 tp2 sc2 (eq_refl _)). *)
(*   destruct Hre1. *)
(*   destruct Hre2. *)
(*   rewrite H in H1. *)
(*   inverts H1. *)
(*   destruct H0 as [H0 eq_sc1]. *)
(*   destruct H2 as [H2 eq_sc2]. *)
(*   destruct H0; destruct H2. *)
(*   destruct H0. destruct H1. *)
(*   destructs H0. destructs H1. rewrite H2 in H4. inverts H4. *)
(*   rewrite eq_sc1 in eq_sc2. apply map_Vint32_eq in eq_sc2. *)
(*   congruence. *)
(*   destruct H0. destructs H0. *)
(*   destruct H1. destruct H1. rewrite H2 in H4. inverts H4. *)
(*   tryfalse. *)
(*   destructs H1. rewrite H2 in H4. inverts H4. *)
(*   destruct H1. *)
(*   destructs H1. *)
(*   destruct H0. *)
(*   destruct H0. rewrite H2 in H4. inverts H4. tryfalse. *)
(*   destruct H0. *)
(*   rewrite H2 in H4. inverts H4. *)
(*   destruct H0. destruct H1. destruct H0. destruct H1. *)
(*   rewrite eq_sc1 in eq_sc2. apply map_Vint32_eq in eq_sc2. *)
(*   congruence. *)
(*   destruct H0. destruct H1. rewrite H2 in H3. inverts H3. *)
(*   destruct H1. *)
(*   destruct H0. destruct H1. *)
(*   rewrite H2 in H3. inverts H3. *)
(*   destruct H0. destruct H1. *)
(*   rewrite eq_sc1 in eq_sc2. apply map_Vint32_eq in eq_sc2. *)
(*   congruence. *)
(* Qed. *)

Lemma RHL_EINFO_vl_eq_eib_ptreq:
  forall vl eib1 eib2 vhold1 vhold2 eid1 eid2 tp1 tp2 sc1 sc2,  
    RHL_EINFO_P vl eib1 vhold1 -> 
    RHL_EINFO_P vl eib2 vhold2 ->
    eib1 = (infotid eid1, tp1, sc1) ->
    eib2 = (infotid eid2, tp2, sc2) ->
    eid1 = eid2.  
Proof.
  introv Hre1 Hre2 Heib1 Heib2.
  unfold RHL_EINFO_P in *.
  destruct eib1 as ((e1 & tp1') & sc1').
  destruct eib2 as ((e2 & tp2') & sc2').
  specialize (Hre1 e1 tp1' sc1' (eq_refl _)).
  specialize (Hre2 e2 tp2' sc2' (eq_refl _)).
  inverts Heib1. inverts Heib2.
  destruct Hre1.  destruct Hre2.
  rewrite H in H1. inverts H1.
  (* destruct H0 as [H0 eq_sc1]. *)
  (* destruct H2 as [H2 eq_sc2]. *)
  destruct H0; destruct H2.
  destruct H0. destruct H1. destructs H0. destructs H1.
  inverts H0. inverts H1.
  congruence.
  destruct H1. destruct H1. tryfalse.
  destruct H1. tryfalse.
  destruct H0.
  destruct H0. inverts H0.
  destruct H0. inverts H0.
  destruct H0. destruct H1.
  destruct H0. destruct H1.
  congruence.
  destruct H0. destruct H1. rewrite H2 in H3. tryfalse.
  destruct H0. tryfalse.
Qed.   

(* Lemma EIBArray_P_vl_eq_mp_eq: *)
(*   forall infol i embls1 embls2 vhold,  *)
(*     EIBArray_P i infol embls1 vhold -> *)
(*     EIBArray_P i infol embls2 vhold -> *)
(*     embls1 = embls2.      *)
(* Proof. *)
(*   inductions infol. *)
(*   intros. *)
(*   simpl in H. simpl in H0. congruence. *)
(*   introv Hep1 Hep2. *)
(*   simpl in Hep1. *)
(*   simpl in Hep2. *)
(*   simpljoin1. *)
(*   inverts H. *)
(*   lets H00: IHinfol H8 H4. *)
(*   assert (Heibeq: x5 = x1). *)
(*   { *)
(*     eapply RHL_EINFO_vl_eq_eib_eq; eauto. *)
(*   } *)
(*   subst x4. subst x5.  *)
(*   eapply join_unique; eauto. *)
(* Qed. *)

Lemma struct_atom_val_eq_sinfo_tp_eq:
  forall vl vl',
    struct_atom_val_eq vl vl' os_ucos_h.sem_info_t ->
    V_OSSINFOType vl' = V_OSSINFOType vl.
Proof.
  intros.
  destruct vl; destruct vl'; simpl in H; tryfalse.
  auto.
  destruct H; subst; auto.
Qed.

Lemma struct_atom_val_eq_sinfo_eid_eq:
  forall vl vl',
    struct_atom_val_eq vl vl' os_ucos_h.sem_info_t ->
    V_OSSINFOPevent vl' = V_OSSINFOPevent vl.
Proof.
  intros.
  do 8 try (destruct vl; destruct vl'; simpl in H; tryfalse; auto;
            try destruct H as (Heq & H); subst).
  simpl; auto.
Qed.

Lemma RHL_EINFO_vl_eq_eib_ptreq':
  forall vl vl' eib1 eib2 vhold eid1 eid2 tp1 tp2 sc1 sc2,
    struct_atom_val_eq vl vl' os_ucos_h.sem_info_t ->
    RHL_EINFO_P vl eib1 vhold -> 
    RHL_EINFO_P vl' eib2 vhold ->
    eib1 = (eid1, tp1, sc1) ->
    eib2 = (eid2, tp2, sc2) ->
    eid1 = eid2.  
Proof.
  introv Hvleq Hre1 Hre2 Heib1 Heib2.
  unfold RHL_EINFO_P in *.
  destruct eib1 as ((e1 & tp1') & sc1').
  destruct eib2 as ((e2 & tp2') & sc2').
  specialize (Hre1 e1 tp1' sc1' (eq_refl _)).
  specialize (Hre2 e2 tp2' sc2' (eq_refl _)).
  inverts Heib1. inverts Heib2.
  destruct Hre1 as (Hvtp1 & Hre1).
  destruct Hre2 as (Hvtp2  & Hre2).
  eapply struct_atom_val_eq_sinfo_eid_eq in Hvleq.
  rewrite Hvleq in *.
  clear -Hre1 Hre2.
  destruct Hre1 as [ | [ | ]]; simpljoin;
  destruct Hre2 as [ | [ | ]]; simpljoin;
  congruence.
Qed.

Lemma RHL_EINFO_vl_eq_tp_eq:
  forall vl vl' eib1 eib2 vhold1 vhold2 ed1 ed2 tp1 tp2 sc1 sc2,
    struct_atom_val_eq vl vl' os_ucos_h.sem_info_t ->
    RHL_EINFO_P vl eib1 vhold1 -> 
    RHL_EINFO_P vl' eib2 vhold2 ->
    eib1 = (ed1, tp1, sc1) ->
    eib2 = (ed2, tp2, sc2) ->
    tp1 = tp2.  
Proof.
  introv Hvleq Hre1 Hre2 Heib1 Heib2.
  unfold RHL_EINFO_P in *.
  destruct eib1 as ((e1 & tp1') & sc1').
  destruct eib2 as ((e2 & tp2') & sc2').
  specialize (Hre1 e1 tp1' sc1' (eq_refl _)).
  specialize (Hre2 e2 tp2' sc2' (eq_refl _)).
  inverts Heib1. inverts Heib2.
  destruct Hre1 as (Hvtp1 & Hre1).
  destruct Hre2 as (Hvtp2  & Hre2).
  eapply struct_atom_val_eq_sinfo_tp_eq in Hvleq.
  rewrite Hvleq in *.
  congruence.
Qed.

Lemma RHL_EINFO_CAP_vl_eq_tp_eq:
  forall vl eib1 eib2 ed1 ed2 tp1 tp2 sc1 sc2,
    RHL_EINFO_CAP_P vl eib1 -> 
    RHL_EINFO_CAP_P vl eib2 ->
    eib1 = (ed1, tp1, sc1) ->
    eib2 = (ed2, tp2, sc2) ->
    sc1 = sc2.
Proof.
  introv Hre1 Hre2 Heib1 Heib2.
  unfold RHL_EINFO_CAP_P in *.
  destruct eib1 as ((e1 & tp1') & sc1').
  destruct eib2 as ((e2 & tp2') & sc2').
  inverts Heib1. inverts Heib2.
  simpljoin.
  eapply map_Vint32_eq; eauto.
Qed.

Lemma EIBArray_SemCapArray_P_vl_eq_mp_eq':
  forall infol infol' scapl i embls1 embls2 vhold,
    length infol = length infol' ->
    (forall k vl vl',
     nth_error infol k = Some vl ->
     nth_error infol' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t) ->
    EIBArray_P i infol embls1 vhold ->
    EIBArray_P i infol' embls2 vhold ->
    SemCapArray_P i scapl embls1 ->
    SemCapArray_P i scapl embls2 ->
    embls1 = embls2.
Proof.
  inductions infol; induction infol';
  introv Hlen Hvleq Hep1 Hep2 Hcp1 Hcp2;
  tryfalse.
  simpl in *; subst; auto.
  simpl EIBArray_P in *.
  simpljoin1.
  inverts H.
  simpl length in *.
  destruct x1 as ((ed' & tp') & cty').
  destruct x5 as ((ed & tp) & cty).
  lets Hvleq': Hvleq 0%nat.
  simpl nth_error in Hvleq'.
  specialize (Hvleq' _ _ (eq_refl _) (eq_refl _)).
  assert (Heq: ed = ed' /\ tp = tp').
  split.
  eapply RHL_EINFO_vl_eq_eib_ptreq'; eauto.
  eapply RHL_EINFO_vl_eq_tp_eq; eauto.
  destruct Heq; subst.
  destruct scapl.
  simpl in Hcp1; subst.
  eapply EmbMod.map_join_pos in H6.
  simpljoin1.
  inverts H.
  simpl SemCapArray_P in *.
  simpljoin1.
  inverts H; inverts H0.
  lets Hj1: H12. lets Hj2: H5.
  eapply EmbMod.join_sig_get in H12.
  eapply EmbMod.join_sig_get in H5.
  lets Hget1': EmbMod.join_sig_get H6.
  lets Hget2': EmbMod.join_sig_get H2.
  rewrite Hget1' in H12; rewrite Hget2' in H5.
  inverts H12; inverts H5.
  assert (Heq: cty = cty').
  eapply RHL_EINFO_CAP_vl_eq_tp_eq; [ | | eauto | eauto]; eauto.
  subst.
  lets Heq: EmbMod.join_unique_r Hj1 H6; subst.
  lets Heq: EmbMod.join_unique_r Hj2 H2; subst.
  eapply IHinfol in H4; eauto.
  subst.
  eapply EmbMod.map_join_deter ; eauto.
  intros.
  eapply Hvleq with (k:= S k); eauto.
Qed.

Lemma EIBArray_P_vl_eq_mp_ptreq:
  forall infol i embls1 embls2 vhold1 vhold2 posv eid1 tp1 eid2 tp2 sc1 sc2, 
    EIBArray_P i infol embls1 vhold1 ->
    EIBArray_P i infol embls2 vhold2 ->
    get embls1 posv = Some (infotid eid1, tp1, sc1) ->
    get embls2 posv = Some (infotid eid2, tp2, sc2) -> 
    eid1 = eid2. 
Proof.
  inductions infol.
  intros.
  simpl in H. simpl in H0. subst embls1. subst embls2.
  rewrite map_emp_get in H1. tryfalse.
  
  introv Hep1 Hep2 Hget1 Hget2.
  simpl in Hep1. simpl in Hep2.
  simpljoin1.
  inverts H.
  assert (Hcases: posv = x \/ posv <> x) by tauto.
  destruct Hcases.
  subst x.
  assert (Hget1': get embls1 posv = Some x5).
  {
    eapply join_sig_get; eauto.
  }
  assert (Hget2': get embls2 posv = Some x1).
  {
    eapply join_sig_get; eauto.
  }
  rewrite Hget1' in Hget1. rewrite Hget2' in Hget2.
  inversion Hget1. inversion Hget2.
  eapply RHL_EINFO_vl_eq_eib_ptreq with (eib1:=x5) (eib2:=x1); eauto.
  assert (Hget1': get x4 posv = Some (infotid eid1, tp1, sc1)).
  {
    eapply join_sig_get_r; eauto.
  }
  assert (Hget2': get x0 posv = Some (infotid eid2, tp2, sc2)).
  {
    eapply join_sig_get_r; eauto.
  }
  eapply IHinfol with (embls1:=x4) (embls2:=x0); eauto.
Qed.

Lemma EIBArray_P_vl_eq_mp_ptreq':
  forall infol infol' i embls1 embls2 vhold posv eid1 tp1 eid2 tp2 sc1 sc2, 
    (forall k vl vl',
     nth_error infol k = Some vl ->
     nth_error infol' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t) ->
    EIBArray_P i infol embls1 vhold ->
    EIBArray_P i infol' embls2 vhold ->
    get embls1 posv = Some (infotid eid1, tp1, sc1) ->
    get embls2 posv = Some (infotid eid2, tp2, sc2) -> 
    eid1 = eid2. 
Proof.
  inductions infol.
  introv Hvleq. intros.
  simpl in H. simpl in H0. subst embls1.
  rewrite map_emp_get in H1. tryfalse.
  inductions infol'.
   introv Hvleq. intros.
  simpl in H0. simpl in H2. subst.
  rewrite map_emp_get in H2. tryfalse.
  introv Hvleq.

  introv Hep1 Hep2 Hget1 Hget2.
  simpl in Hep1. simpl in Hep2.
  simpljoin1.
  inverts H.
  assert (Hcases: posv = x \/ posv <> x) by tauto.
  destruct Hcases.
  subst x.
  assert (Hget1': get embls1 posv = Some x5).
  {
    eapply join_sig_get; eauto.
  }
  assert (Hget2': get embls2 posv = Some x1).
  {
    eapply join_sig_get; eauto.
  }
  rewrite Hget1' in Hget1. rewrite Hget2' in Hget2.
  inversion Hget1. inversion Hget2.
  eapply RHL_EINFO_vl_eq_eib_ptreq' with (eib1:=x5) (eib2:=x1) in H1; eauto.
  congruence.
  eapply Hvleq with (k:= 0%nat); eauto.
  assert (Hget1': get x4 posv = Some (infotid eid1, tp1, sc1)).
  {
    eapply join_sig_get_r; eauto.
  }
  assert (Hget2': get x0 posv = Some (infotid eid2, tp2, sc2)).
  {
    eapply join_sig_get_r; eauto.
  }
  eapply IHinfol with (embls1:=x4) (embls2:=x0); eauto.
  intros.
  eapply Hvleq with (k:= S k); eauto.
Qed.

Lemma ASemEIBs_vl_mp_eq:
  forall infol infol' scapl scapl' embls embls' ecbls ecbls' vhold e e0 M1 M2 i ier l o1 o2 a M,  
  (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold ->
  (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold -> 
  sub M1 M -> 
  sub M2 M -> 
  (forall k vl vl',
     nth_error infol k = Some vl ->
     nth_error infol' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t)
  /\ scapl = scapl' /\ embls = embls'.
Proof.
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold ASemEIBs in *.
  sep destruct Hsat1.
  sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  assert (Ht: forall P Q R: Prop, (P /\ Q /\ ((P /\ Q) -> R)) -> (P /\ Q /\ R)).
  tauto.
  eapply Ht.
  splits.
  eapply ASeminfo_vll_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  assert (Heq: x = x0).
  {
     unfold ASeminfo in *.
     simpl_sat H19; simpl_sat H14.
     simpljoin1.
     simpl in H19, H33; simpljoin1.
     rewrite H22 in H36; inverts H36.
     lets H00: mapstoval_true_vptr_eq M H23 H37.
     destruct H00; auto.
     mem_join_sub_solver.
     mem_join_sub_solver.
   }
  subst.
  rewrite <- H6 in H1.
  unfold ASemCap in *.
  eapply AEvtCap_vll_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  introv Hvleq.
  destruct Hvleq; subst.
  eapply EIBArray_SemCapArray_P_vl_eq_mp_eq'
                with (infol := infol) (infol' := infol'); eauto.
  eapply aseminfo_len in H14, H19.
  congruence.
Qed.

(* Lemma ASemEIBs_vl_mp_eq: *)
(*   forall infol infol' scapl scapl' embls embls' ecbls ecbls' vhold e e0 M1 M2 i ier l o1 o2 a M,   *)
(*   (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold -> *)
(*   (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold ->  *)
(*   sub M1 M ->  *)
(*   sub M2 M ->  *)
(*   infol = infol' /\ scapl = scapl' /\ embls = embls'. *)
(* Proof. *)
(*   introv Hsat1 Hsat2 Hsub1 Hsub2. *)
(*   unfold ASemEIBs in *. *)
(*   sep destruct Hsat1. *)
(*   sep destruct Hsat2. *)
(*   sep split in Hsat1. *)
(*   sep split in Hsat2. *)
(*   admit. *)
(*   (* lets Hvleq: ASeminfo_vll_eq Hsat1 Hsat2 Hsub1 Hsub2. *)
(*   subst infol'.  *)
(*   split; auto. *)
(*   eapply EIBArray_P_vl_eq_mp_eq; eauto. *)
(* Qed. *) *)
(* Admitted. *)

Lemma ASemEIBs_vl_mpptr_eq:
  forall infol infol' scapl scapl' embls embls' ecbls ecbls' vhold e e0 M1 M2 i ier l o1 o2 a M,  
    (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold ->
    sub M1 M -> 
    sub M2 M -> 
    (forall k vl vl',
     nth_error infol k = Some vl ->
     nth_error infol' k = Some vl' ->
     struct_atom_val_eq vl vl' os_ucos_h.sem_info_t) /\
      (forall posv eid1 tp1 sc1 eid2 tp2 sc2,
          get embls posv = Some (infotid eid1, tp1, sc1) ->
          get embls' posv = Some (infotid eid2, tp2, sc2) ->
          eid1 = eid2). 
Proof. 
  introv Hsat1 Hsat2 Hsub1 Hsub2.
  unfold ASemEIBs in *.
  sep destruct Hsat1.
  sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  simpl_sat Hsat1.
  simpl_sat Hsat2.
  simpljoin1.
  assert (Ht: forall P R: Prop, (P /\ (P -> R)) -> (P /\ R)).
  tauto.
  eapply Ht.
  split.
  eapply ASeminfo_vll_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  intros.
  eapply EIBArray_P_vl_eq_mp_ptreq' ; eauto.
Qed.

(* Lemma ASemEIBs_vl_mpptr_eq: *)
(*   forall infol infol' scapl scapl' embls embls' ecbls ecbls' vhold vhold' e e0 M1 M2 i ier l o1 o2 a M,   *)
(*     (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold' -> *)
(*     sub M1 M ->  *)
(*     sub M2 M ->  *)
(*     infol = infol' /\ *)
(*       (forall posv eid1 tp1 sc1 eid2 tp2 sc2, *)
(*           get embls posv = Some (infotid eid1, tp1, sc1) -> *)
(*           get embls' posv = Some (infotid eid2, tp2, sc2) -> *)
(*           eid1 = eid2).  *)
(* Proof.  *)
(*   introv Hsat1 Hsat2 Hsub1 Hsub2. *)
(*   unfold ASemEIBs in *. *)
(*   sep split in Hsat1. *)
(*   sep split in Hsat2. *)
(*   admit. *)
(*   (* lets Hvleq: ASeminfo_vll_eq Hsat1 Hsat2 Hsub1 Hsub2. *)
(*   subst infol'.  *)
(*   split; auto. *)
(*   intros.   *)
(*   eapply EIBArray_P_vl_eq_mp_ptreq with (embls1:=embls) (embls2:=embls'); eauto. *)
(* Qed. *) *)
(* Admitted. *)

Lemma AEvtCap_precise' :
  forall scapl scapl' adr fieldname eibtype e e0 i ier l a M1 M2 o1 o2 , 
    length scapl = length scapl' ->
    (e, e0, M1, i, ier, l, o1, a) |= AEvtCap adr scapl fieldname eibtype ->
    (e, e0, M2, i, ier, l, o2, a) |= AEvtCap adr scapl' fieldname eibtype ->
    (forall M : mem,
        sub M1 M -> sub M2 M -> M1 = M2) /\
      (forall o : osabst,
          sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  induction scapl; induction scapl'; 
    destruct adr;
    unfold AEvtCap;
    try do 2 intro;
    introv Hlen Hsat1 Hsat2;
    simpl length in *;
    sep normal in Hsat1;
    sep normal in Hsat2;
    sep destruct Hsat1;
    sep destruct Hsat2;
    sep split in Hsat1;
    sep split in Hsat2;
    tryfalse.
  simpl in Hsat1, Hsat2.
  unfold emposabst in *.
  simpljoin; auto.
  fold AEvtCap in *.
  sep normal in Hsat1;
    sep normal in Hsat2;
    sep destruct Hsat1;
    sep destruct Hsat2;
    sep split in Hsat1;
    sep split in Hsat2.
  rewrite H in H2; inverts H2.
  eapply eq_add_S in Hlen.
  simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
  lets Hp1: Aarray_precise' H14 H9.
  destruct Hp1 as (Hm1 & Ho1).
  lets Hp2: IHscapl Hlen H15 H10.
  destruct Hp2 as (Hm2 & Ho2).
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AEvtCap_osabst_emp :
  forall scapl adr fieldname eibtype e e0 i ier l a M o ,
    (e, e0, M, i, ier, l, o, a) |= AEvtCap adr scapl fieldname eibtype ->
    o = empenv.
Proof.
  induction scapl;
    destruct adr;
    unfold AEvtCap;
    try do 2 intro;
    introv Hsat.
  simpl in *. simpljoin; auto.
  sep normal in Hsat;
    sep destruct Hsat;
    sep split in Hsat.
  fold AEvtCap in *.
  simpl_sat Hsat; simpljoin1.
  apply Aarray_osabst_emp in H6; simpljoin1.
  eapply IHscapl; eauto.
Qed. 

Lemma ASeminfo_precise' :
  forall infol infol' adr adr' e e0 i ier l a M1 M2 o1 o2 , 
    (e, e0, M1, i, ier, l, o1, a) |= ASeminfo adr infol ->
    (e, e0, M2, i, ier, l, o2, a) |= ASeminfo adr' infol' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold ASeminfo; intros. 
  simpl_sat H; simpl_sat H0; simpljoin1.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  simpljoin1.
  match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
  split; intros.
  assert (Heq: adr' = adr /\  x5 = x).
  { split.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
     eapply mapstoval_true_mem_eq with (M:=M);eauto; mem_join_sub_solver.
  }
  destruct Heq.
  subst.
  lets Hp1: Aarray_new_precise' H22 H9; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  apply Aarray_new_osabst_emp in H9; apply Aarray_new_osabst_emp in H22.
  substs; auto.
Qed.

Lemma ASeminfo_osabst_emp :
  forall infol adr e e0 i ier l a M o , 
    (e, e0, M, i, ier, l, o, a) |= ASeminfo adr infol ->
    o = empenv.
Proof.
  unfold ASeminfo.
  intros.
  simpl_sat H.
  simpljoin1.
  simpl in H3; simpljoin1.
  apply Aarray_new_osabst_emp in H8.
  auto.
Qed.

Lemma ASemEIBs_prop_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 infol scapl embls ecbls embls' ecbls' infol' scapl' vhold vhold', 
    (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold ASemEIBs; intros.
  sep destruct H. sep destruct H0.
  simpl_sat H; simpl_sat H0.
  simpljoin1.
  unfold ASemCap in *.
  split; intros.
  assert (Heq: x = x0 ).
  {  unfold ASeminfo in *.
      simpl_sat H4; simpl_sat H44.
      simpljoin1.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      simpljoin1.
     match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
  }
  subst.
  lets Hp1: ASeminfo_precise' H44 H4; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  rewrite <- H64 in H24.
  lets Hp1: AEvtCap_precise' H49 H9; eauto.
  destruct Hp1 as (Hm2 & Ho2).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  eapply Hm2 with (M:= M); try mem_join_sub_solver.
  apply AEvtCap_osabst_emp in H49, H9.
  apply ASeminfo_osabst_emp in H44, H4.
  simpljoin1; auto.
Qed.

(* Lemma ASemEIBs_prop_precise' : *)
(*   forall e e0 i ier l a M1 M2 o1 o2 infol scapl embls ecbls embls' ecbls' infol' scapl' vhold vhold',  *)
(*     (e, e0, M1, i, ier, l, o1, a) |= ASemEIBs infol scapl embls ecbls vhold -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= ASemEIBs infol' scapl' embls' ecbls' vhold' -> *)
(*     (forall M : mem, *)
(*        sub M1 M -> sub M2 M -> M1 = M2) /\ *)
(*     (forall o : osabst, *)
(*        sub o1 o -> sub o2 o -> o1 = o2). *)
(* Proof. *)
(*   unfold ASemEIBs; intros. *)
(*   unfold ASeminfo in *. *)
(*   simpl_sat H; simpl_sat H0. *)
(*   simpljoin1. *)
(*   (* simpl in H59, H25. *)
(*   simpljoin1. *)
(*   rewrite H4 in H16; inverts H16. *)
(*   split; intros. *)
(*   assert(x17 = x42). *)
(*   assert(sub x18 M). *)
(*   apply join_sub_l in H22. *)
(*   eapply sub_trans;  eauto. *)
(*   assert(sub x43 M). *)
(*   apply join_sub_l in H56. *)
(*   eapply sub_trans; eauto.  *)
(*   lets Hx: mapstoval_true_vptr_eq H5 H17 H1 H2. simpljoin1. *)
(*   assert(x43 = x18). *)
(*   substs. *)
(*   eapply mapstoval_true_mem_eq with (M:=M);eauto; mem_join_sub_solver. *)

(*   eapply eq_join_eq;eauto. *)
(*   eapply Aarray_new_precise'. apply H65. apply H31. apply H64. rewrite H1 in H30. eapply H30. *)

(*   apply join_sub_r in H56. eapply sub_trans; eauto. *)
(*   apply join_sub_r in H22.   eapply sub_trans; eauto. *)
(*   eapply Aarray_new_osabst_emp in H64. *)
(*   eapply Aarray_new_osabst_emp in H30. *)
(*   subst. auto. *)
(* (*   rewrite <- H30 in H64. *)
(*   apply H50. *) *)
(* Qed. *) *)
(* Admitted. *)

Lemma APthreadMutex_precise' :
  forall infol infol' adr adr' e e0 i ier l a M1 M2 o1 o2 , 
    (e, e0, M1, i, ier, l, o1, a) |= APthreadMutex adr infol ->
    (e, e0, M2, i, ier, l, o2, a) |= APthreadMutex adr' infol' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APthreadMutex; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  simpljoin1.
  match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
  split; intros.
  assert (Heq: adr' = adr /\  x5 = x).
  { split.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
     eapply mapstoval_true_mem_eq with (M:=M);eauto; mem_join_sub_solver.
  }
  destruct Heq.
  subst.
  lets Hp1: Aarray_new_precise' H22 H9; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  apply Aarray_new_osabst_emp in H9; apply Aarray_new_osabst_emp in H22.
  substs; auto.
Qed.

Lemma APthreadMutex_osabst_emp :
  forall infol adr e e0 i ier l a M o , 
    (e, e0, M, i, ier, l, o, a) |= APthreadMutex adr infol ->
    o = empenv.
Proof.
  unfold APthreadMutex.
  intros.
  simpl_sat H.
  simpljoin1.
  simpl in H3; simpljoin1.
  apply Aarray_new_osabst_emp in H8.
  auto.
Qed.

Lemma AMuxEIBs_precise':
  forall e e0 i ier l a M1 M2 o1 o2 minfol mcapl minfob ecbls vhold minfol' mcapl' minfob' ecbls' vhold',
    (e, e0, M1, i, ier, l, o1, a) |= AMuxEIBs minfol mcapl minfob ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AMuxEIBs minfol' mcapl' minfob' ecbls' vhold'->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AMuxEIBs; intros.
  sep destruct H. sep destruct H0.
  simpl_sat H; simpl_sat H0.
  simpljoin1.
  unfold AMuxCap in *.
  split; intros.
  assert (Heq: x = x0 ).
  {  unfold APthreadMutex in *.
      simpl_sat H4; simpl_sat H37.
      simpljoin1.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      simpljoin1.
     match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
  }
  subst.
  lets Hp1: APthreadMutex_precise' H37 H4; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  rewrite <- H57 in H24.
  lets Hp1: AEvtCap_precise' H42 H9; eauto.
  destruct Hp1 as (Hm2 & Ho2).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  eapply Hm2 with (M:= M); try mem_join_sub_solver.
  apply AEvtCap_osabst_emp in H42, H9.
  apply APthreadMutex_osabst_emp in H37, H4.
  simpljoin1; auto.
Qed.

(* Lemma AMuxEIBs_precise': *)
(*   forall e e0 i ier l a M1 M2 o1 o2 minfol mcapl minfob ecbls vhold minfol' mcapl' minfob' ecbls' vhold', *)
(*     (e, e0, M1, i, ier, l, o1, a) |= AMuxEIBs minfol mcapl minfob ecbls vhold -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= AMuxEIBs minfol' mcapl' minfob' ecbls' vhold'-> *)
(*     (forall M : mem, *)
(*        sub M1 M -> sub M2 M -> M1 = M2) /\ *)
(*     (forall o : osabst, *)
(*        sub o1 o -> sub o2 o -> o1 = o2). *)
(* Proof.  *)
(*    unfold AMuxEIBs; intros. *)
(*   unfold APthreadMutex in *. *)
(*   simpl_sat H; simpl_sat H0. *)
(*   simpljoin1. *)
(* Admitted. *)
(*   (* simpl in H45, H18. *)
(*   simpljoin1. *)
(*   rewrite H4 in H16; inverts H16. *)
(*   split; intros. *)

(*   assert(x17 = x36). *)
(*   assert(sub x18 M). *)
(*   apply join_sub_l in H15. *)
(*   eapply sub_trans;  eauto. *)
(*   assert(sub x37 M). *)
(*   apply join_sub_l in H42. *)
(*   eapply sub_trans; eauto.  *)
(*   lets Hx: mapstoval_true_vptr_eq H5 H18 H1 H2. simpljoin1. *)
(*   assert(x37 = x18). *)
(*   substs. *)
(*   eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver. *)

(*   eapply eq_join_eq;eauto. *)
(*   eapply Aarray_new_precise'. apply H51. apply H24. apply H50. rewrite H1 in H23. eapply H23. *)

(*   apply join_sub_r in H42. eapply sub_trans; eauto. *)
(*   apply join_sub_r in H15.   eapply sub_trans; eauto. *)
(*   eapply Aarray_new_osabst_emp in H50. *)
(*   eapply Aarray_new_osabst_emp in H23. *)
(*   rewrite <- H23 in H50. *)
(*   apply H50. *)
(* Qed. *) *)

Lemma AMuxEIBs_precise:
  forall e e0 i ier l a M1 M2 o1 o2 minfol mcapl minfob ecbls vhold minfol' mcapl' minfob' ecbls' vhold',
    (e, e0, M1, i, ier, l, o1, a) |= AMuxEIBs minfol mcapl minfob ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AMuxEIBs minfol' mcapl' minfob' ecbls' vhold'->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).  
Proof.
  intros.
  eapply precise'2precise; eauto.
  eapply AMuxEIBs_precise'; eauto.
Qed.

Lemma struct_type_vallist_match_mqattr: 
  forall v,
    struct_type_vallist_match os_ucos_h.mq_attr_t v -> 
    exists v1 v2 v3 v4 v5 v6 v7,
      v = v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: nil.
Proof.
  intros.
  unfold os_ucos_h.OS_EVENT  in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  destruct v5; simpljoin1; tryfalse.
  destruct v6; simpljoin1; tryfalse.
  do 3 eexists; eauto.
Qed.

Lemma AMqAttr_precise' :
  forall infol infol' adr adr' e e0 i ier l a M1 M2 o1 o2 , 
    (e, e0, M1, i, ier, l, o1, a) |= AMqAttr adr infol ->
    (e, e0, M2, i, ier, l, o2, a) |= AMqAttr adr' infol' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AMqAttr; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
  simpljoin1.
  match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
  split; intros.
  assert (Heq: adr' = adr /\  x5 = x).
  { split.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
     eapply mapstoval_true_mem_eq with (M:=M);eauto; mem_join_sub_solver.
  }
  destruct Heq.
  subst.
  lets Hp1: Aarray_new_precise' H22 H9; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  apply Aarray_new_osabst_emp in H9; apply Aarray_new_osabst_emp in H22.
  substs; auto.
Qed.

Lemma AMqAttr_osabst_emp :
  forall infol adr e e0 i ier l a M o , 
    (e, e0, M, i, ier, l, o, a) |= AMqAttr adr infol ->
    o = empenv.
Proof.
  unfold AMqAttr.
  intros.
  simpl_sat H.
  simpljoin1.
  simpl in H3; simpljoin1.
  apply Aarray_new_osabst_emp in H8.
  auto.
Qed.

Lemma AMqEIBs_precise' :
  forall qattrl qattrl' qcapl qcapl' qattrb qattrb' ecbls ecbls' vhold vhold' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AMqEIBs qattrl qcapl qattrb ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AMqEIBs qattrl' qcapl' qattrb' ecbls' vhold' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AMqEIBs; intros.
  sep destruct H. sep destruct H0.
  simpl_sat H; simpl_sat H0.
  simpljoin1.
  unfold AMqCap in *.
  split; intros.
  assert (Heq: x = x0 ).
  {  unfold AMqAttr in *.
      simpl_sat H4; simpl_sat H44.
      simpljoin1.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      match goal with H: _ |= GV _ @ _ |-> _ |- _ => simpl in H end.
      simpljoin1.
     match goal with H: get _ _ = _ , H00: get _ _ = _ |- _ =>
     rewrite H in H00; inverts H00 end.
     eapply mapstoval_true_vptr_eq with (M:= M); eauto.
     mem_join_sub_solver.
     mem_join_sub_solver.
  }
  subst.
  lets Hp1: AMqAttr_precise' H44 H4; eauto.
  destruct Hp1 as (Hm1 & Ho1).
  rewrite <- H64 in H24.
  lets Hp1: AEvtCap_precise' H49 H9; eauto.
  destruct Hp1 as (Hm2 & Ho2).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  eapply Hm2 with (M:= M); try mem_join_sub_solver.
  apply AEvtCap_osabst_emp in H49, H9.
  apply AMqAttr_osabst_emp in H44, H4.
  simpljoin1; auto.
Qed.

(* Lemma AMqEIBs_precise' : *)
(*   forall qattrl qattrl' qcapl qcapl' qattrb qattrb' ecbls ecbls' vhold vhold' e e0 i ier l a M1 M2 o1 o2, *)
(*     (e, e0, M1, i, ier, l, o1, a) |= AMqEIBs qattrl qcapl qattrb ecbls vhold -> *)
(*     (e, e0, M2, i, ier, l, o2, a) |= AMqEIBs qattrl' qcapl' qattrb' ecbls' vhold' -> *)
(*     (forall M : mem, *)
(*        sub M1 M -> sub M2 M -> M1 = M2) /\ *)
(*     (forall o : osabst, *)
(*        sub o1 o -> sub o2 o -> o1 = o2). *)
(* Proof. *)
(*   unfold AMqEIBs; intros. *)
(*   unfold AMqAttr in *. *)
(*   simpl_sat H; simpl_sat H0. *)
(*   simpljoin1. *)
(* Admitted. *)
(*   (* simpl in H59, H25. *)
(*   simpljoin1. *)

(*   rewrite H4 in H16; inverts H16. *)
(*   split; intros. *)

(*   assert(x17 = x42). *)
(*   assert(sub x18 M). *)
(*   apply join_sub_l in H22. *)
(*   eapply sub_trans;  eauto. *)
(*   assert(sub x43 M). *)
(*   apply join_sub_l in H56. *)
(*   eapply sub_trans; eauto.  *)
(*   lets Hx: mapstoval_true_vptr_eq H5 H17 H1 H2. simpljoin1. *)
(*   assert(x43 = x18). *)
(*   substs. *)
(*   eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver. *)

(*   eapply eq_join_eq;eauto. *)
(*   eapply Aarray_new_precise'.  *)
(*   apply H65. *)
(*   apply H31. *)
(*   apply H64. *)
(*   rewrite H1 in H30. eapply H30. *)

(*   apply join_sub_r in H56. eapply sub_trans; eauto. *)
(*   apply join_sub_r in H22. eapply sub_trans; eauto. *)
(*   eapply Aarray_new_osabst_emp in H64. *)
(*   eapply Aarray_new_osabst_emp in H30. *)
(*   subst. auto. *)
(* Qed. *) *)

Lemma AMqEIBs_precise : 
  forall qattrl qattrl' qcapl qcapl' qattrb qattrb' ecbls ecbls' vhold vhold' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AMqEIBs qattrl qcapl qattrb ecbls vhold ->
    (e, e0, M2, i, ier, l, o2, a) |= AMqEIBs qattrl' qcapl' qattrb' ecbls' vhold' ->
    (forall M o,
        sub M1 M -> sub M2 M -> sub o1 o -> sub o2 o ->
        M1 = M2 /\ o1 = o2
    ). 
Proof.
  intros.
  eapply precise'2precise; eauto.
  eapply AMqEIBs_precise'; eauto.  
Qed.

Lemma AEvAtomHeap_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AEvAtomHeap x ->
  (e, e0, M2, i, ier, l, o2, a) |= AEvAtomHeap x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x;intros.
  -
    simpl in H, H0. unfold emposabst in *.
    destruct H, H0. subst. auto.
  - destruct a. destruct p. destruct t.
    cbn [AEvAtomHeap] in H, H0.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    cbn [AEvAtomHeap] in H, H0.
     sep split in H.
    sep split in H0.
    rename H5 into Hrv1; rename H6 into Hrv2.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
   simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.
    lets Hx2: IHx H H0 M o.
    assert(x1 = x5 /\ x3 = x7).
    apply Hx2; try mem_join_sub_solver.
    destruct H10;subst.
    split;jeat.

    cbn [AEvAtomHeap] in H, H0.
     sep split in H.
    sep split in H0.
    rename H5 into Hrv1; rename H6 into Hrv2.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
   simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.
    lets Hx2: IHx H H0 M o.
    assert(x1 = x5 /\ x3 = x7).
    apply Hx2; mem_join_sub_solver.
    destruct H10;subst.
    split;jeat.

    cbn [AEvAtomHeap] in H, H0.
     sep split in H.
    sep split in H0.
    rename H5 into Hrv1; rename H6 into Hrv2.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
   simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.
    lets Hx2: IHx H H0 M o.
    assert(x1 = x5 /\ x3 = x7).
    apply Hx2; mem_join_sub_solver.
    destruct H10;subst.
    split;jeat.

    cbn [AEvAtomHeap] in H, H0.
     sep split in H.
    sep split in H0.
    rename H5 into Hrv1; rename H6 into Hrv2.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
   simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.
    lets Hx2: IHx H H0 M o.
    assert(x1 = x5 /\ x3 = x7).
    apply Hx2; mem_join_sub_solver.
    destruct H10;subst.
    split;jeat.

    cbn [AEvAtomHeap] in H, H0.
     sep split in H.
    sep split in H0.
    rename H5 into Hrv1; rename H6 into Hrv2.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
   simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.
    lets Hx2: IHx H H0 M o.
    assert(x1 = x5 /\ x3 = x7).
    apply Hx2; mem_join_sub_solver.
    destruct H10;subst.
    split;jeat.

    simpl_sat H; simpl_sat H0;
    eapply except; auto. 
    simpl_sat H; simpl_sat H0;
    eapply except; auto. 
    simpl_sat H; simpl_sat H0;
    eapply except; auto. 
    simpl_sat H; simpl_sat H0;
    eapply except; auto. 
Qed.

Lemma HEvAtomHeap_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= HEvAtomHeap x1  ->
  (e, e0, M2, i, ier, l, o2, a) |= HEvAtomHeap x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma AEvStructHeap_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AEvStructHeap x ->
  (e, e0, M2, i, ier, l, o2, a) |= AEvStructHeap x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x;intros.
  -
    simpl in H, H0. unfold emposabst in *.
    destruct H, H0. subst. auto.
  - destruct a. destruct p. destruct t.
    cbn [AEvStructHeap] in H, H0.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    simpl_sat H; simpl_sat H0;
    eapply except; auto.
    cbn [AEvStructHeap] in H, H0.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
    eapply astar_l_apure_elim in H, H0.
    destruct H, H0.
    eapply astar_l_apure_elim in H9, H10.
    destruct H9, H10.
    lets Hx1: Astruct_precise _H _H0 M o; clear _H _H0; auto.
    assert (x0 = x4 /\ x2 = x6). {apply Hx1; mem_join_sub_solver. }
    destruct H13; subst.
    lets Hx2: IHx H11 H12 M o.
    assert(x1 = x5 /\ x3 = x7). {apply Hx2; mem_join_sub_solver. }
    destruct H13; subst.
    split; jeat.
    eapply except; auto.
Qed.

Lemma HEvStructHeap_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= HEvStructHeap x1  ->
  (e, e0, M2, i, ier, l, o2, a) |= HEvStructHeap x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma AEvArrayHeap_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AEvArrayHeap x ->
  (e, e0, M2, i, ier, l, o2, a) |= AEvArrayHeap x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x;intros.
  -
    simpl in H, H0. unfold emposabst in *.
    destruct H, H0. subst. auto.
  - destruct a. destruct p.
    cbn [AEvArrayHeap] in H, H0.
    elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
    eapply astar_l_apure_elim in H, H0.
    destruct H, H0.
     lets Hx1: Aarray_precise _H _H0 M o; clear _H _H0; auto.
    assert (x0 = x4 /\ x2 = x6). {apply Hx1; mem_join_sub_solver. }
    destruct H11; subst.
     lets Hx2: IHx H9 H10 M o.
    assert(x1 = x5 /\ x3 = x7). {apply Hx2; mem_join_sub_solver. }
    destruct H11; subst.
    split; jeat.
Qed.

Lemma HEvArrayHeap_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= HEvArrayHeap x1  ->
  (e, e0, M2, i, ier, l, o2, a) |= HEvArrayHeap x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma EvtInv_precise: 
  forall ecbls ecbls' tcbh tcbvl tcbvl' tcbls tcbls' vhold vhold',
  forall scapl mcapl qcapl scapl' mcapl' qcapl',
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= EvtInv ecbls tcbh tcbvl tcbls vhold scapl mcapl qcapl ->
    (e, e0, M2, i, ier, l, o2, a) |= EvtInv ecbls' tcbh tcbvl' tcbls' vhold' scapl' mcapl' qcapl' ->
    tcb_linked_list_same_next tcbvl tcbvl' -> 
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
 introv Hsat1 Hsat2 Hnxt Hsubm1 Hsubm2 Hsubo1 Hsubo2.
  unfold EvtInv in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  substs.
  rename H into H_.
  rename H7 into H0_.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevfreelist: AOSEventFreeList_precise' _H _H0; clear _H _H0.
  lets Hevfreelist': precise'2precise Hevfreelist.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hqfreelist: AOSQFreeList_precise' _H _H0; clear _H _H0.
  lets Hqfreelist': precise'2precise Hqfreelist.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hqfreeblk: AOSQFreeBlk_precise' _H _H0; clear _H _H0.
  lets Hqfreeblk': precise'2precise Hqfreeblk.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hecblist: AECBList_precise' _H _H0; clear _H _H0.
  lets Hecblist': precise'2precise Hecblist.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habsels: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habsels': precise'2precise Habsels.

  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hebls: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Hebls': precise'2precise Hebls.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Herrlist: AErrblkList_precise _H _H0; clear _H _H0.
  lets Herrlist': precise'2precise Herrlist.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hpbls: Hpbls_precise' _H _H0.
  lets Hpbls': precise'2precise Hpbls.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hposbls: APosblkList_precise' _H _H0.
   lets Hposbls': precise'2precise Hposbls.
  clear _H _H0.

  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevatom: HEvAtomHeap_precise_eq _H _H0.

  assert (x109 = x113 /\ x111 = x115 /\ x5 = x24) as Hevatom'.
  { eapply (Hevatom M o) ; try mem_join_sub_solver. }
  destruct Hevatom' as [Hevatom_0 [Hevatom_1 Hevatom_2] ]. subst.
  clear Hevatom.
  clear _H _H0.
 elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevatomheap: AEvAtomHeap_precise _H _H0.

 assert (x5 = x118 /\ x111 = x120) as Hevatomheap'.
 { eapply (Hevatomheap M o) ; try mem_join_sub_solver. }
 destruct Hevatomheap' as (Hevatomheap_0 & Hevatomheap_2) . subst.
 clear Hevatomheap.

   clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevstruct: HEvStructHeap_precise_eq _H _H0.

  assert (x5 = x124 /\ x122 = x126 /\ x6 = x25) as Hevstruct'.
  { eapply (Hevstruct M o) ; try mem_join_sub_solver. }
  destruct Hevstruct' as [Hevstruct_0 [Hevstruct_1 Hevstruct_2] ]. subst.
  clear Hevstruct.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevstructheap: AEvStructHeap_precise _H _H0.

 assert (x5 = x129 /\ x122 = x131) as Hevstructheap'.
 { eapply (Hevstructheap M o) ; try mem_join_sub_solver. }
 destruct Hevstructheap' as (Hevstructheap_0 & Hevstructheap_2) . subst.
 clear Hevstructheap.

  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevarray: HEvArrayHeap_precise_eq _H _H0.

  assert (x5 = x135 /\ x133 = x137 /\ x7 = x26) as Hevarray'.
  { eapply (Hevarray M o) ; try mem_join_sub_solver. }
  destruct Hevarray' as [Hevarray_0 [Hevarray_1 Hevarray_2] ]. subst.
  clear Hevarray.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hevarrayheap: AEvArrayHeap_precise _H _H0.

 assert (x5 = x140 /\ x133 = x142) as Hevarrayheap'.
 { eapply (Hevarrayheap M o) ; try mem_join_sub_solver. }
 destruct Hevarrayheap' as (Hevarrayheap_0 & Hevarrayheap_2) . subst.
 clear Hevarrayheap.

  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hsinfo: HSEMInfo_precise' _H _H0. 
   lets Hsinfo': precise'2precise Hsinfo.
  clear _H _H0. 
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hasemeibs: ASemEIBs_prop_precise' _H _H0.
   lets Hasemeibs': precise'2precise Hasemeibs.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hminfo: HMuxInfo_precise' _H _H0.
   lets Hminfo': precise'2precise Hminfo.
   clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Heibarrm: AMuxEIBs_precise' _H _H0.
   lets Heibarrm': precise'2precise Heibarrm.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hqinfo: HQAttr_precise' _H _H0.
   lets Hqinfo': precise'2precise Hqinfo.
  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Heibarrq: AMqEIBs_precise' _H _H0.
   lets Heibarrq': precise'2precise Heibarrq.

  clear _H _H0.
  sep lift 3%nat in H. elim_sep_conj1 H _H.
  sep lift 3%nat in H0. elim_sep_conj1 H0 _H0.
  lets Hevaux: tcbllsegevaux_precise' _H _H0 Hnxt.
  lets Hevaux': precise'2precise Hevaux.

  eapply precise'2precise;eauto.

  simpljoin1.

  Ltac XX x1 x2:= 
    match goal with
      H: forall _, _ -> _ -> ?R |- ?R => apply H with (x1:=x2); mem_join_sub_solver
    end. 

  split.
  introv Hsub1 Hsub2.
  simpl_sat H; simpl_sat H0; simpljoin1.
  mem_eq_solver2; try XX M M.

  simpl in *. congruence.
  simpl in *. congruence.
  
  introv Hsub1 Hsub2.
  mem_eq_solver2; try XX o o.

  clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets H00: HEvExeLoc_mp_eq _H _H0.
  assert (Hsub1': sub x200 o) by mem_join_sub_solver.
  assert (Hsub2': sub x204 o) by mem_join_sub_solver.
  lets Heq1: H00 Hsub1' Hsub2'. clear H00 Hsub1' Hsub2'.
  lets H00: HEvExePtr_mp_eq H H0.
  assert (Hsub1': sub x201 o) by mem_join_sub_solver.
  assert (Hsub2': sub x205 o) by mem_join_sub_solver.
  lets Heq2: H00 Hsub1' Hsub2'. clear H00 Hsub1' Hsub2'.
  subst.
  mem_eq_solver2.
  simpl_sat _H; simpl_sat _H0; simpljoin1.
  simpl_sat H; simpl_sat H0; simpljoin1.
Qed.

(* end of EvtInv precise *)

(* IntInv precise  *)
Lemma IntInv_precise: 
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= IntInv ->
    (e, e0, M2, i, ier, l, o2, a) |= IntInv ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  introv Hsat1 Hsat2 Hsubm1 Hsubm2 Hsubo1 Hsubo2.
  unfold IntInv in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx11: Aabsdata_precise _H _H0; clear _H _H0. (* Hhier *)
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx12: Aabsdata_precise _H _H0; clear _H _H0. (* Hhinthandler *)
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx13: AOSInthandler_precise _H _H0. clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx14: Aabsdata_precise _H _H0; clear _H _H0. (* HhinthandlerParam *)
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx15: AOSInthandlerParam_precise _H _H0. clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx16: AOSExchandler_precise _H _H0. clear _H _H0.
  lets Hx17: Aabsdata_precise H H0. clear H H0. (* Hhexchandler *)

    repeat match goal with 
         | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
            |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
                           apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
         end.
  repeat match goal with 
         | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
           |- _ => assert (m1 = m2);[jeat | ]; subst m1 
         end.
  auto.
Qed.

(* TmrInv Precise *)
Lemma AOSClkRate_precise' :
forall v v' M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSClkRate (Vint32 v) ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSClkRate (Vint32 v') ->
  (forall M : mem,
      sub M1 M -> sub M2 M -> M1 = M2) /\
  (forall o : osabst,
      sub o1 o -> sub o2 o -> o1 = o2).      
Proof.
  intros.
  unfold AOSClkRate in H, H0.
  simpl in H, H0; simpljoin1;
  rewrite H13 in H4; inverts H4.
  simpljoin1; split; intros; auto.
  lets Hx: mapstoval_true_rule_type_val_match_eq H5 H14 H0 H; simpl; auto.
  simpljoin1.
Qed.

Lemma AOSClkRate_precise :
forall v v' M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSClkRate (Vint32 v) ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSClkRate (Vint32 v') ->
  (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros v v' M1 M2 o1 o2 e e0 i ier l a H H0 .
  eapply precise'2precise;eauto.
  eapply AOSClkRate_precise';eauto.
Qed.

Lemma AOSTMRNode_precise :
forall x1 x2 v M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSTMRNode v x1  ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSTMRNode v x2 ->
  (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold AOSTMRNode in H ,H0. 
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.
  simpl in H, H0. destruct tmrRegsAddr.
  simpl in H, H0. simpljoin1.
  split;auto.

  repeat match goal with
  | H: mapstoval ?l ?t true ?v1 ?m1,
    H0 : mapstoval ?l ?t true ?v2 ?m2 
    |- _ => let h:=fresh "H" in 
    assert (v1 = v2 /\ m1 = m2); [
    eapply (mapstoval_true_rule_type_val_match_eq l t v1 v2 m1 m2 M);
    [ reflexivity|
      reflexivity|
      apply H|
      apply H0|
      try mem_join_sub_solver | try mem_join_sub_solver
       ] | ];clear H H0;destruct h;subst m1
  | H: mapstoval ?l ?t false ?v1 ?m1,
    H0 : mapstoval ?l ?t false ?v2 ?m2 
    |- _ => let h:=fresh "H" in 
    assert (v1 = v2 /\ m1 = m2); [
    eapply (mapstoval_false_rule_type_val_match_eq l t v1 v2 m1 m2 M);
    [ reflexivity|
      reflexivity|
      apply H|
      apply H0|
      try mem_join_sub_solver | try mem_join_sub_solver
       ] | ];clear H H0;destruct h;subst m1
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.


Lemma AOSTMRList'_precise :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSTMRList' x1  ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSTMRList' x2 ->
  (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).   
Proof.
  intros.
  unfold AOSTMRList' in H, H0.
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx3: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx4: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx5: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx6: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx7: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx8: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx9: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx10: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx11: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx12: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx13: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx14: AOSTMRNode_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx15: AOSTMRNode_precise _H _H0; clear _H _H0.

  lets Hx16: AOSTMRNode_precise H H0. clear H H0.

  simpljoin1.

  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
  
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed.

Lemma AOSTMRList_TMRused_precise :
forall x1 x2 x3 x4 x1' x2' x3' x4' M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSTMRList_TMRused x1 x2 x3 x4 ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSTMRList_TMRused x1' x2' x3' x4' ->
  (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold AOSTMRList_TMRused in H, H0.
  sep split in H. sep split in H0.

  simpl_sat H;simpl_sat H0;simpljoin1.

  simpl in H12, H23. simpljoin1.
  rewrite H35 in H15. inverts H15.
  assert (x9 = x).
  { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
    1,2: mem_join_sub_solver. }
  subst x9.


  lets Hx: AOSTMRList'_precise H28 H17.
  assert (x21 = x15 /\ x24 = x18).
  {eapply (Hx M o);mem_join_sub_solver. }
  clear Hx.
  destruct H;subst.
  unfold AOSTMRIDUsed,GAarray in *.
  simpl_sat H29;simpl_sat H18;simpljoin1.

  simpl in H32,H48. simpljoin1.
  rewrite H in H0. inverts H0.
  destruct x23. destruct x31.
  unfold addrval_to_addr in *.
  inverts H13. inverts H10.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H12,H13; auto.
  do 2 rewrite Int.repr_unsigned in H0; substs.
  lets Hx: Aarray_precise H33 H49.
  assert (x16 = x22 /\ x19 = x25).
  {eapply (Hx M o);mem_join_sub_solver. }
  destruct H0;subst.
  jeat.
  clear - H20 H25 H9 H14 H1 H2.
  assert (x0 = x10). { eapply map_join_deter;eauto. }
  subst.
  jeat.
Qed.



Lemma Hcoreheap_precise_eq :
forall x1 x2 x3 x4 x5 x6 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= HCoreHeap x1 x2 x5 ->
  (e, e0, M2, i, ier, l, o2, a) |= HCoreHeap x3 x4 x6 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x3 /\ x2 = x4 /\ x5 = x6).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma AOScoreheapl_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOScoreheapl x ->
  (e, e0, M2, i, ier, l, o2, a) |= AOScoreheapl x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x;intros.
  -
  simpl in H, H0. unfold emposabst in *.
  destruct H, H0. subst. auto.
  - destruct a. destruct p.
    cbn [AOScoreheapl] in H, H0. 

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1: Aarray_precise _H _H0 M o; clear _H _H0.
    assert (x0 = x4 /\ x2 = x6). { apply Hx1;mem_join_sub_solver. }
    destruct H9;subst.

    sep split in H. sep split in H0.
    lets Hx2: IHx H H0 M o.
    assert (x1 = x5 /\ x3 = x7). { apply Hx2;mem_join_sub_solver. }
    destruct H11;subst.

    split;jeat.
Qed.

Lemma AOScoreheape_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOScoreheape x ->
  (e, e0, M2, i, ier, l, o2, a) |= AOScoreheape x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x;intros.
  -
  simpl in H, H0. unfold emposabst in *.
  destruct H, H0. subst. auto.
  - destruct a. destruct p.
    cbn [AOScoreheape] in H, H0. 

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    simpl in _H, _H0. unfold emposabst in *.
    destruct _H, _H0.
    assert (x0 = x4).
    { eapply mapstoval_true_mem_eq; eauto. instantiate (1:= M).
      1,2: mem_join_sub_solver. }
    subst.

    lets Hx2: IHx H H0 M o.
    assert (x1 = x5 /\ x3 = x7). { apply Hx2;mem_join_sub_solver. }
    destruct H10;subst.
    
    split;jeat.
Qed.

Lemma AOScoreheapt_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOScoreheapt x ->
  (e, e0, M2, i, ier, l, o2, a) |= AOScoreheapt x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).
Proof.
    induction x;intros.
  -
  simpl in H, H0. unfold emposabst in *.
  destruct H, H0. subst. auto.
  - destruct a. destruct p.
    cbn [AOScoreheapt] in H, H0. 
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    sep split in H0. destruct H9.
    lets Hx1: Astruct_precise _H _H0 M o; clear _H _H0; try tauto.
    assert (x0 = x4 /\ x2 = x6). { apply Hx1;mem_join_sub_solver. }
    destruct H11;subst.

    sep split in H. destruct H11.
    lets Hx2: IHx H H0 M o.
    assert (x1 = x5 /\ x3 = x7). { apply Hx2;mem_join_sub_solver. }
    destruct H13;subst.
    split;jeat.
Qed.

Lemma HipcsendHeap_precise :
forall x2 x4  M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= HipcsendHeap x2 ->
  (e, e0, M2, i, ier, l, o2, a) |= HipcsendHeap x4 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma Memory_sigcore_aux_precise :
forall n vl vl' p m M1 M2 o1 o2 e e0 i ier l a,
  length vl = n -> length vl' = n ->
  (e, e0, M1, i, ier, l, o1, a) |= Memory_sigcore_aux m p vl ->
  (e, e0, M2, i, ier, l, o2, a) |= Memory_sigcore_aux m p vl' ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction n;intros.
  - destruct vl, vl';tryfalse.
    unfold Memory_sigcore_aux in *. 
    simpl in H1,H2; simpljoin1. split;auto.
  - destruct vl, vl';tryfalse.
    simpl in H,H0.
    apply eq_add_S in H,H0.
    cbn [Memory_sigcore_aux] in *.
    simpl_sat H1; simpl_sat H2;simpljoin1.
    unfold Memory_Node in *.
    sep split in H15.
    sep split in H10.
    lets Hx : Aarray_precise H15 H10;auto.
    assert(sub x5 M) by mem_join_sub_solver.
    assert(sub x M) by mem_join_sub_solver.
    assert(sub x8 o) by mem_join_sub_solver.
    assert(sub x2 o) by mem_join_sub_solver.
    specialize (Hx _ _ H2 H8 H13 H17) as [Hx1 Hx2]. substs.
    lets Hy : IHn H16 H11;auto.
    assert(sub x6 M) by mem_join_sub_solver.
    assert(sub x0 M) by mem_join_sub_solver.
    assert(sub x9 o) by mem_join_sub_solver.
    assert(sub x3 o) by mem_join_sub_solver.
    specialize (Hy _ _ H18 H19 H20 H21) as [Hy1 Hy2]. substs.
    splits; jeat.
Qed.

Lemma AOSIPCMem_aux_precise :
forall pl ml ml1 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCMem_aux pl ml ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCMem_aux pl ml1 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction pl;intros.
  - unfold AOSIPCMem_aux in *. destruct ml, ml1;tryfalse.
   simpl in H,H0; simpljoin1. split;auto.
  - unfold AOSIPCMem_aux in *;fold AOSIPCMem_aux in *.
    destruct a;tryfalse.
    destruct ml,ml1;tryfalse.
    simpl_sat H; simpl_sat H0; simpljoin1.
    lets Hx : IHpl H14 H9.
    assert(sub x6 M) by mem_join_sub_solver.
    assert(sub x0 M) by mem_join_sub_solver.
    assert(sub x9 o) by mem_join_sub_solver.
    assert(sub x3 o) by mem_join_sub_solver.
    specialize (Hx _ _ H H0 H6 H11).
    simpljoin1.
    unfold Memory_sigcore in *.
    simpl_sat H13; simpl_sat H8; simpljoin1.
    lets Hy : Memory_sigcore_aux_precise H25 H18;eauto.
    assert(sub x5 M) by mem_join_sub_solver.
    assert(sub x M) by mem_join_sub_solver.
    assert(sub x8 o) by mem_join_sub_solver.
    assert(sub x2 o) by mem_join_sub_solver.
    specialize (Hy _ _ H8 H13 H15 H16) as [Hy1 Hy2]. substs.
    splits; jeat.
Qed.

Lemma Aarray'_precise_Vptr_eq' :	
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,	
    isvptr_list vl-> isvptr_list vl' ->	
    (e, e0, M1, i, ier, l, o1, a) |= Aarray' head n (Tptr t) vl ->	
    (e, e0, M2, i, ier, l, o2, a) |= Aarray' head n (Tptr t) vl' ->	
    (forall (M : mem) ( o : osabst),	
       sub M1 M -> sub M2 M -> 	
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ vl = vl').	
Proof.	
  intro; inductions vl; intros.	
  destruct vl'; destruct n; simpl in H1, H2; tryfalse.	
  simpljoin1; splits;  intros; auto.	

  destruct vl'; destruct n; simpl in H1, H2; tryfalse.	
  destruct head.	

  simpl in H1, H2; simpljoin1. 	
  simpl in H, H0. destruct a,v;tryfalse.	
  lets Hx: IHvl H H0 H17 H11.	
  assert (x6 = x0 /\ o1 = o2 /\ vl = vl').	
  { apply (Hx M o). 	
    mem_join_sub_solver. mem_join_sub_solver. 	
    auto. auto.  }	
  simpljoin1; splits.	
  eapply eq_join_eq; eauto.	
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver. auto.	
  assert (a = a1).	
  eapply mapstoval_true_vptr_eq with (M:=M);eauto. 	
  mem_join_sub_solver.	
  mem_join_sub_solver.	
  substs. auto.	
Qed.

Lemma AOSIPCMem_precise :
forall pl pl1 ml ml1 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCMem pl ml ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCMem pl1 ml1 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros. unfold AOSIPCMem in *.
  unfold GAarray in *.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H41, H22; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H6 in H10.
  unfold addrval_to_addr in H10. destruct x30, x17; inverts H10.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  unfold Aarray in *.
  lets Hx : Aarray'_precise_Vptr_eq' H33 H14 H42 H23.
  assert(sub x5 M) by mem_join_sub_solver.
  assert(sub x M) by mem_join_sub_solver.
  assert(sub x8 o) by mem_join_sub_solver.
  assert(sub x2 o) by mem_join_sub_solver.
  specialize (Hx _ _ H H8 H10 H11).
  simpljoin1. 
  lets Hy : AOSIPCMem_aux_precise H32 H13.
  assert (x6 = x0 /\ x9 = x3) as [Hy1 Hy2].
  { apply (Hy M o);mem_join_sub_solver. } substs.
  split;jeat.
Qed.

Lemma AOSIPCSem_precise :
forall vl M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCSem vl ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCSem vl ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros. unfold AOSIPCSem, GAarray in *. 
  sep split in H. sep split in H0.
  sep destruct H. sep destruct H0.
  simpl_sat H;simpl_sat H0;simpljoin1. 
  simpl in H16,H10;simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H8 in H16.
  unfold addrval_to_addr in H16. destruct x, x0; inverts H16.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise; eauto.
Qed. 

Lemma AOSIPCSendSem_precise :
forall vl M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCSendSem vl ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCSendSem vl ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros. unfold AOSIPCSendSem, GAarray in *. 
  sep split in H. sep split in H0.
  sep destruct H. sep destruct H0.
  simpl_sat H;simpl_sat H0;simpljoin1. 
  simpl in H16,H10;simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H8 in H16.
  unfold addrval_to_addr in H16. destruct x, x0; inverts H16.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H9; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise; eauto.
Qed. 

Lemma AOSIPCSemShared_precise :
forall v M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCSemShared v ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCSemShared v ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros. unfold AOSIPCSemShared, Agvarmapsto in *.
  sep destruct H;sep destruct H0.  
  simpl_sat H;simpl_sat H0;simpljoin1.
  
  simpl in H8 ,H13. simpljoin1.
  rewrite H in H0.
  inverts H0.
  simpl in H9 ,H14. simpljoin1.
  split.
  eapply mapstoval_true_mem_eq with (M:=M);eauto.
  auto.
Qed. 

Lemma AOSIPCBroadList_precise :
 forall pl pl' vl vl' M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCBroadList pl vl ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCBroadList pl' vl' ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).
Proof.
  intros. unfold AOSIPCBroadList, GAarray in *.
  sep normal in H;sep normal in H0.
  sep destruct H;sep destruct H0.
  sep split in H;sep split in H0.

  simpl_sat H;simpl_sat H0;simpljoin1.
  simpl in H20, H33. simpljoin1.
  rewrite H20 in H41. inverts H41.
  assert (x16 =x22).
  { eapply mapstoval_true_mem_eq with (M:= M);eauto.
    1,2: mem_join_sub_solver. }
  subst.

  simpl in H14, H27;simpljoin1.
  destruct x0,x2. cbn [addrval_to_addr] in *. 
  rewrite H in H0; inverts H0.
  rewrite <- H12 in H17. 
  inverts H17.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H13; auto.
  do 2 rewrite Int.repr_unsigned in *. substs.
  lets Hx: Aarray_precise H19 H32.
  assert (x15 = x21 /\ o2 = o1).
  { eapply (Hx M o);eauto. 1,2: mem_join_sub_solver. }
  inverts H0.
  jeat.
Qed.
  
Lemma AOSIPCGRinfo_precise :
forall m m' M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= AOSIPCGRinfo m ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSIPCGRinfo m' ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).
Proof.
  unfold AOSIPCGRinfo; intros.

  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H13, H8;simpljoin1.
  simpl in H14, H9; simpljoin1.
  rewrite H13 in H23.
  inverts H23.
  split;[ | auto].
  assert (x5 = x).
  eapply mapstoval_true_mem_eq with (M:=M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  subst.
  assert (x6 = x0).
  eapply mapstoval_true_mem_eq with (M:=M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  subst.
  jeat.
Qed.

Lemma TmrInv'_precise: 
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= TmrInv' ->
    (e, e0, M2, i, ier, l, o2, a) |= TmrInv' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold TmrInv' in *.
  do 5 destruct H, H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: AOSClkRate_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2: Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx3: AOSTMRList_TMRused_precise _H _H0; clear _H _H0.
  lets Hx5: Aabsdata_precise H H0; clear H H0.

  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed.

Lemma HeapInv'_precise: 
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= HeapInv' ->
    (e, e0, M2, i, ier, l, o2, a) |= HeapInv' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold HeapInv' in *.
  do 3 destruct H, H0.
  sep split in H.
  sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: Hcoreheap_precise_eq _H _H0; clear _H _H0.
  assert (x5 = x9 /\ x7 = x11 /\ x = x0 /\ x1 = x2 /\ x3 = x4) as Hx1'.
  { eapply (Hx1 M o);mem_join_sub_solver. }
  destruct Hx1' as [ ? [? [? [ ? ? ]]]]; subst.
  clear Hx1.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: AOScoreheapl_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2: AOScoreheape_precise _H _H0; clear _H _H0.
  lets Hx3: AOScoreheapt_precise H H0; clear H H0.

  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed.
  

Lemma TmrInv_precise: 
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= TmrInv ->
    (e, e0, M2, i, ier, l, o2, a) |= TmrInv ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold TmrInv in *.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: TmrInv'_precise _H _H0; clear _H _H0.
  lets Hx2: HeapInv'_precise H H0; clear H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed.

Lemma struct_type_vallist_match_dyn_refac_cfg : forall v, struct_type_vallist_match os_ucos_h.dyn_refac_cfg v -> 
         exists v1 v2 v3 v4 v5, v = v1 :: v2 :: v3 :: v4 :: v5 :: nil.
Proof.
  intros.
  unfold os_ucos_h.dyn_refac_cfg in H.
  simpl in H.
  unfolds in H.
  destruct v; tryfalse.
  destruct v0; simpljoin1; tryfalse.
  destruct v1; simpljoin1; tryfalse.
  destruct v2; simpljoin1; tryfalse.
  destruct v3; simpljoin1; tryfalse.
  destruct v4; simpljoin1; tryfalse.
  do 5 eexists; eauto.
Qed.

Lemma dynrefaccfg_sll_precise' :
  forall vl vl' head e e0 M1 M2 i ier l o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |=  sll head vl os_ucos_h.dyn_refac_cfg V_dyn_refac_cfg_Next ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head vl' os_ucos_h.dyn_refac_cfg V_dyn_refac_cfg_Next->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
           sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  inductions vl; intros.
  simpl in H; simpljoin1.
  destruct vl'.
  simpl in H0; simpljoin1; auto.
  unfold sll in H0; unfold sllseg in H0; fold sllseg in H0.
  unfold node in H0; simpl in H0; simpljoin1; tryfalse.
  destruct vl'.
  simpl in H0; simpljoin1.
  unfold sll in H; unfold sllseg in H; fold sllseg in H.
  unfold node in H; simpl in H; simpljoin1; tryfalse.
  unfold sll in H, H0; unfold sllseg in H, H0; fold sllseg in H, H0.
  simpl_sat H; simpljoin1; simpl_sat H0; simpljoin1.
  
  lets Hx: node_precise' H14 H19.
  
  unfold sll in IHvl.
  simpljoin1; split; intros.
  assert(x5 = x6).
  assert(sub x12 M) by mem_join_sub_solver.
  assert(sub x17 M) by mem_join_sub_solver.
  lets Hx: node_vl_eq H14 H19 H5 H6.
  simpl in Hx.
  unfold node in H14, H19.
  destruct H14, H19; sep split in H7; sep split in H8; simpljoin1.
  assert(exists a1 a2 a3 a4 a5 , a = a1::a2::a3::a4::a5::nil).
  eapply struct_type_vallist_match_dyn_refac_cfg; eauto.
  assert(exists v1 v2 v3 v4 v5,  v = v1::v2::v3::v4::v5::nil).
  eapply struct_type_vallist_match_dyn_refac_cfg; eauto.
  simpljoin1; simpl in Hx; simpl in H9, H10; simpljoin1; inversion H9; inversion H10; substs; auto.
  substs.
  
  lets Hx2: IHvl H15 H20.
  simpljoin1; mem_eq_solver M.
  
  eapply sllseg_osabst_emp in H15.
  eapply sllseg_osabst_emp in H20.
  substs.
  eapply osabst_eq_join_eq; eauto.
  osabst_eq_solver o.
Qed.

Lemma dynrefaccfg_sll_precise :
  forall vl vl' head e e0 M1 M2 i ier l  o1 o2 a,
    (e, e0, M1, i, ier, l, o1, a) |= sll head vl os_ucos_h.dyn_refac_cfg V_dyn_refac_cfg_Next ->
    (e, e0, M2, i, ier, l, o2, a) |= sll head vl' os_ucos_h.dyn_refac_cfg V_dyn_refac_cfg_Next ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof. 
  intros vl vl' head e e0 M1 M2 i ier l  o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply dynrefaccfg_sll_precise';eauto.
Qed.

Lemma AdynrefaccfgFreeList_precise:
  forall e e0 i ier l a M1 M2 o1 o2 cfgp  cfgp' vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= AdynrefaccfgFreeList cfgp vl ->
    (e, e0, M2, i, ier, l, o2, a) |= AdynrefaccfgFreeList cfgp' vl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AdynrefaccfgFreeList; intros.
  simpl in H, H0; simpljoin1.
  rewrite H27 in H13; inverts H13.
  split; intros.
  
  assert (cfgp = cfgp').
  assert(isptr cfgp).
  eapply sll_isptr; eauto.
  assert (isptr cfgp').
  eapply sll_isptr; eauto.
  destruct cfgp, cfgp' ; auto;
  try(unfolds in H; destruct H; simpljoin1; tryfalse);
  try(unfolds in H0; destruct H0; simpljoin1; tryfalse).
  unfolds in H28; simpljoin1; simpl in H6; simpljoin1.
  unfolds in H14; simpljoin1; simpl in H14; destruct a0; simpl in H14; simpljoin1.
  clear - H1 H2 H14 H6 H5 H19 H0 H12. 
  unfold ptomval in H6; unfold ptomval in H14; substs.
   assert(sub x5 M).
  clear - H19 H1.
  unfold sub in *; geat.
   assert(sub x M).
  clear - H5 H2.
  unfold sub in *; geat.
  lets Hx: mem_join_sig_sub_eq H12 H0 H3 H; tryfalse.
  
  unfolds in H28; simpljoin1; simpl in H6; destruct a0; simpl in H6; simpljoin1.
  unfolds in H14; simpljoin1; simpl in H14; simpljoin1.
  clear - H1 H2 H14 H6 H5 H19 H0 H12. 
  unfold ptomval in H6; unfold ptomval in H14; substs.
  assert(sub x5 M).
  clear - H19 H1.
  unfold sub in *; geat.
  assert(sub x M).
  clear - H5 H2.
  unfold sub in *; geat.
  lets Hx: mem_join_sig_sub_eq H12 H0 H3 H; tryfalse.
  
  inverts H. inverts H0.
  assert (sub x5 M).
  clear - H1 H19. unfold sub in *; geat.
  assert (sub x M).
  clear - H5 H2. unfold sub in *; geat.
  lets Hx: mapstoval_true_vptr_eq H14 H28 H0 H; simpljoin1.
  
  substs. 
  assert(x = x5).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  substs.
  eapply eq_join_eq; eauto.
  
  lets Hx: dynrefaccfg_sll_precise' H23 H9; simpljoin1.
  mem_eq_solver M.
  
  apply sll_osabst_emp in H23; apply sll_osabst_emp in H9.
  substs; auto.
Qed.

Lemma Hdynheap_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= Hdynheap x1 ->
  (e, e0, M2, i, ier, l, o2, a) |= Hdynheap x2->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2 ).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

(* Only need x because Hdynheap_precise_eq *)
Lemma Adynheap_precise :
forall x M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= Adynheap x ->
  (e, e0, M2, i, ier, l, o2, a) |= Adynheap x  ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).
Proof.
    induction x;intros.
  -
  simpl in H, H0. unfold emposabst in *.
  destruct H, H0. subst. auto.
  - destruct a. 
    cbn [Adynheap] in H, H0. 
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    sep split in H0. 
    lets Hx1: Astruct_precise _H _H0 M o; clear _H _H0; try tauto.
    assert (x0 = x4 /\ x2 = x6). { apply Hx1;mem_join_sub_solver. }
    destruct H10;subst.

    sep split in H. 
    lets Hx2: IHx H H0 M o.
    assert (x1 = x5 /\ x3 = x7). { apply Hx2;mem_join_sub_solver. }
    destruct H11;subst.
    split;jeat.
Qed.

Lemma gvar_ptr_precise :
  forall t gvar v1 v2 M1 M2 o1 o2 e e0 i ier l a , 
    isptr v1 ->
    isptr v2 -> 
    (e, e0, M1, i, ier, l, o1, a)  |= GV gvar @ (Tptr t) |-> v1 ->  
    (e, e0, M2, i, ier, l, o2, a)  |= GV gvar @ (Tptr t) |-> v2 ->
    (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ v1 = v2).
Proof.
  intros. splits.
  + simpl in H1,  H2; simpljoin1.
    rewrite H19 in H10; inverts H10.
    lets Hx1: mapstoval_true_mem_eq M H20 H11; auto. 
  + simpl in H1,  H2; simpljoin1.
  + lets Hx: gvar_ptr_precise' H H0 H1 H2 H3 H4. now subst.
Qed.

(* DynamicRefactorInv precise  *)
Lemma DynamicRefactorINV_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 ecbls ecbls', 
    (e, e0, M1, i, ier, l, o1, a) |= DynamicRefactorINV ecbls ->
    (e, e0, M2, i, ier, l, o2, a) |= DynamicRefactorINV ecbls' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof. 
  intros. 
  unfold DynamicRefactorINV in *.
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: AdynrefaccfgFreeList_precise _H _H0; clear _H _H0.
  assert (x7 = x11 /\ x9 = x13) as Hx1'.
  { eapply (Hx1 M o);mem_join_sub_solver. }
  destruct Hx1'; subst. clear Hx1.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2: Aabsdata_precise _H _H0; clear _H _H0.
  assert (x7 = x17 /\ x15 = x19) as Hx2'.
  { eapply (Hx2 M o);mem_join_sub_solver. }
  destruct Hx2'; subst. clear Hx2.
  sep lift 2%nat in H.
  sep lift 2%nat in H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx3: Hdynheap_precise_eq _H _H0; clear _H _H0.
  assert (x7 = x23 /\ x21 = x25 /\ x2 =x6) as Hx3'.
  { eapply (Hx3 M o);mem_join_sub_solver. }
  destruct Hx3' as [? [? ?]]; subst. clear Hx3.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx4: Adynheap_precise _H _H0; clear _H _H0.
  assert (x2 = x28 /\ x21 = x30) as Hx4'.
  { eapply (Hx4 M o);mem_join_sub_solver. }
  destruct Hx4' as [? ?]; subst. clear Hx4.
  lets Hx5: gvar_ptr_precise H H0.
  cbv. eauto.
  cbv. eauto.
  assert ( x7 = x29 /\ x27 = x31 /\ Vptr dynrefcmsgQ_addr = Vptr dynrefcmsgQ_addr) as Hx5'.
  { eapply (Hx5 M o);mem_join_sub_solver. }
  destruct Hx5' as [? [? ?]]; subst. clear Hx5.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed. 

(* CoreCommuInv precise  *)
Lemma CoreCommuInv_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 ecbls ecbls', 
    (e, e0, M1, i, ier, l, o1, a) |= CoreCommuInv ecbls ->
    (e, e0, M2, i, ier, l, o2, a) |= CoreCommuInv ecbls' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold CoreCommuInv in *.
  do 7 destruct H, H0.
  sep split in H.
  sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2:  HipcsendHeap_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx3: Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx4:  Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx5:  Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx6:  Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx7:  Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx8:  Aabsdata_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx9:  AOSIPCMem_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx10:  AOSIPCSem_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx11:  AOSIPCSendSem_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx12:  AOSIPCSemShared_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx13:  AOSIPCBroadList_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx14:  AOSIPCGRinfo_precise _H _H0; clear _H _H0.
  lets Hx15:  DynamicRefactorINV_precise H H0; clear H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto. 
Qed.

(* PartitionInv precise  *)
Lemma dmportp_sll_head_isptr : forall dportl dportlptr dportmsgll s,
  s |= dmportp_sll dportlptr dportl dportmsgll OS_Port_V_nextPort ->
  isptr dportlptr.
Proof.
  induction dportl.
  - intros. destruct dportmsgll. cbn in H.
    unfold isptr. tauto. 
    cbn in H. false.
  - intros.
    destruct dportmsgll; unfold dmportp_sll in H; cbn [dmportp_sllseg] in H.
    contradiction.
    sep destruct H.
    sep split in H.
    unfold isptr.
    right.
    eexists. eauto.
Qed.

Lemma dmportp_sllseg_qport_msg_precise: 
  forall dportl e e0 i ier l a M1 M2 o1 o2 pnow pend qstart qend qentries  dportl' , 
    (e, e0, M1, i, ier, l, o1, a) |= dmportp_sllseg_qport_msg pnow pend qstart qend qentries dportl ->
    (e, e0, M2, i, ier, l, o2, a) |= dmportp_sllseg_qport_msg pnow pend qstart qend qentries dportl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  induction dportl;intros.
  - destruct qentries, dportl';cbn [dmportp_sllseg_qport_msg] in *;tryfalse.
    simpl in H, H0. simpljoin1.
    auto.
  - destruct qentries, dportl';cbn [dmportp_sllseg_qport_msg] in *;tryfalse.
    sep normal in H. sep normal in H0.
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1 : Aarray_precise _H _H0;clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx3 : IHdportl H H0;clear H H0.
    simpl in _H, _H0. simpljoin1.
    lets Hx2: mapstoval_true_mem_eq M H H16.
    1,2: mem_join_sub_solver.
    repeat match goal with 
    | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
      |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
      apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
      end.
    subst.
      repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto.
Qed. 

Lemma dmportp_sll_precise: 
  forall dportl e e0 i ier l a M1 M2 o1 o2 dportlptr dportmsgll  dportl' dportmsgll', 
    (e, e0, M1, i, ier, l, o1, a) |= dmportp_sll dportlptr dportl dportmsgll OS_Port_V_nextPort ->
    (e, e0, M2, i, ier, l, o2, a) |= dmportp_sll dportlptr dportl' dportmsgll' OS_Port_V_nextPort ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ dportl' = dportl ).
Proof.
  unfold dmportp_sll. induction dportl;intros.
  - destruct dportmsgll, dportl', dportmsgll';
    cbn [dmportp_sllseg] in *; tryfalse.

    simpl_sat H. simpl_sat H0. 
    simpljoin1. auto.
    
    sep destruct  H0. sep split in H0. sep split in H. subst.  false.
  - destruct dportmsgll, dportl', dportmsgll';
    cbn [dmportp_sllseg] in *; tryfalse.
    
    { sep destruct H. sep split in H0. sep split in H. subst.  false. }
    sep destruct H. sep destruct H0.
    sep split in H0. sep split in H.
    simpljoin1.
    inverts H5. 

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1 : Astruct'_precise _H _H0;auto.
    assert (struct_atom_val_eq' a v OS_Port_Seg_dls).
    { eapply Astruct'_vl_eq with (M:= M);eauto.
      1,2: mem_join_sub_solver. }
    clear _H _H0.
    assert (a = v).
    { clear - H15 H7 H11. rename v into l.
      do 18 (destruct l ;simpl in H7;tryfalse; destruct H7 as [? H7]).
      do 18 (destruct a;simpl in H11;tryfalse; destruct H11 as [? H11]).
      cbn in *.
      destruct l;tryfalse. destruct a;tryfalse.
      simpljoin1.  }
    subst v.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    destruct _H as [_H | _H]; destruct _H0 as [_H0 | _H0]; 
    try sep destruct _H; try sep destruct _H0;
    sep split in _H;sep split in _H0.
    2: { rewrite H21 in *. clear - H20. tryfalse. } 
    2: { rewrite H27 in *. clear - H20. tryfalse. }
    { (* sample *)
      rewrite H8 in *. inverts H12.
      rewrite H6 in *. inverts H10.
      lets Hx2: IHdportl H H0.
      clear H H0.
      rename _H into H. rename _H0 into H0. 
      unfold dmportp_sllseg_sampleport_msg in *.
      sep normal in H. sep normal in H0.
      sep destruct H. sep destruct H0.
      sep split in H. sep split in H0.
      inverts H23. inverts H12.
      elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
      lets Hx3: Aarray_precise _H _H0. clear _H _H0.
      simpl in H. simpl in H0.
      simpljoin1.
      lets Hx4: mapstoval_true_mem_eq M H H0; auto.
      1,2: mem_join_sub_solver. 
      specialize (Hx2 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
      repeat match goal with 
      | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
        |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
        apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
        end.
      subst. simpljoin1.
        repeat match goal with 
      | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
        |- _ => assert (m1 = m2);[jeat | ]; subst m1 
        end.
      auto. 
    }
    destruct H31. destruct H32.
    destruct H24. destruct H25.
    rewrite H8 in *. inverts H12.
    rewrite H6 in *. inverts H10.
    rewrite H28 in *. inverts H21.
    rewrite H29 in *. inverts H22.
    rewrite H30 in *. inverts H23.
    rewrite H31 in *. inverts H24.
    rewrite H32 in *. inverts H25.
    lets Hx2: IHdportl H H0.
    clear H H0.
    rename _H into H. rename _H0 into H0. 
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx3: dmportp_sllseg_qport_msg_precise _H _H0. clear _H _H0.
    lets Hx4: dmportp_sllseg_qport_msg_precise H H0; auto.
    repeat match goal with 
    | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
      |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
      apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
      end.
    specialize (Hx2 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
    simpljoin1.
      repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto.
Qed. 

Lemma AOSDomainPortPtrList_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 dportlptr dportl dportmsgll dportlptr' dportl' dportmsgll', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSDomainPortPtrList dportlptr dportl dportmsgll ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSDomainPortPtrList dportlptr' dportl' dportmsgll' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ dportlptr' = dportlptr /\ dportl' =  dportl).
Proof.
  intros.
  unfold AOSDomainPortPtrList in *.
  
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  apply dmportp_sll_head_isptr in H as ?.
  apply dmportp_sll_head_isptr in H0 as ?.
  lets Hx1: gvar_ptr_precise _H _H0;auto.
  specialize (Hx1 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
  simpljoin1.
  lets Hx2: dmportp_sll_precise H H0.
  specialize (Hx2 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
  simpljoin1.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma Aarray'_precise_ptr_eq' :	
  forall vl vl' head n t M1 M2 o1 o2 e e0 i ier l a,	
    array_type_vallist_match (Tptr t) vl -> array_type_vallist_match (Tptr t) vl' ->
    (e, e0, M1, i, ier, l, o1, a) |= Aarray' head n (Tptr t) vl ->	
    (e, e0, M2, i, ier, l, o2, a) |= Aarray' head n (Tptr t) vl' ->	
    (forall (M : mem) ( o : osabst),	
       sub M1 M -> sub M2 M -> 	
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ vl = vl').	
Proof.	
  intro; inductions vl; intros.	
  destruct vl'; destruct n; simpl in H1, H2; tryfalse.	
  simpljoin1; splits;  intros; auto.	

  destruct vl'; destruct n; simpl in H1, H2; tryfalse.	
  destruct head.	

  simpl in H1, H2; simpljoin1. 	
  destruct H; destruct H0.
  lets Hx1 : mapstoval_true_rule_type_val_match_eq M H H0 H16 H10.
  assert (a = v /\ x5 = x). apply Hx1;mem_join_sub_solver.
  simpljoin1.
  
  
  lets Hx: IHvl H1 H2 H17 H11.	
  assert (x6 = x0 /\ o1 = o2 /\ vl = vl').	
  { apply (Hx M o). 	
    mem_join_sub_solver. mem_join_sub_solver. 	
    auto. auto.  }	
  simpljoin1; splits;auto.
  eapply eq_join_eq; eauto.	
Qed.

Lemma kportNode_P_precise: 
  forall kportvl e e0 i ier l a M1 M2 o1 o2 kportl kportl', 
    (e, e0, M1, i, ier, l, o1, a) |= kportNode_P kportvl kportl ->
    (e, e0, M2, i, ier, l, o2, a) |= kportNode_P kportvl kportl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  induction kportvl;intros.
  - destruct kportl, kportl'; cbn [kportNode_P] in *;tryfalse.
    simpl in H, H0. simpljoin1.
    auto.
  - destruct kportl, kportl'; cbn [kportNode_P] in *;tryfalse.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    destruct _H as [_H | _H]; destruct _H0 as [_H0 | _H0]; 
    try sep destruct _H; try sep destruct _H0;
    sep split in _H;sep split in _H0.
    2: { simpljoin1. inverts H10. }
    2: { simpljoin1. inverts H10. }
    { (* Vnull *)
      simpl in _H, _H0. simpljoin1.
      eapply IHkportvl;eauto.
    }
    { (* Vptr *)
      simpljoin1. inverts H10.
      lets Hx1: Astruct'_precise _H _H0;clear _H _H0.
      { clear- H12.
        rename v into l.
        do 7 (destruct l as [ |v l];simpl in H12;tryfalse; destruct H12 as [? H12];destruct v;tryfalse).
        all: cbn;tauto.
      }
      { clear- H11.
        rename v0 into l.
        do 7 (destruct l as [ |v l];simpl in H11;tryfalse; destruct H11 as [? H11];destruct v;tryfalse).
        all: cbn;tauto.
      }
      lets Hx2: IHkportvl H H0.
      repeat match goal with 
      | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
        |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
        apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
        end.
      repeat match goal with 
      | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
        |- _ => assert (m1 = m2);[jeat | ]; subst m1 
        end.
      auto. }
Qed.


Lemma AOSKernelPortIDTbl_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 kportvl kportl kportvl' kportl', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSKernelPortIDTbl kportvl kportl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSKernelPortIDTbl kportvl' kportl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AOSKernelPortIDTbl, GAarray;intros.
  sep normal in H. sep normal in H0.
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H. simpl in _H0.
  simpljoin1.
  rewrite H14 in H13. inverts H13.
  destruct x0,x. cbn [addrval_to_addr] in *. 
  rewrite <- H19 in H15; inverts H15.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H11; auto.
  do 2 rewrite Int.repr_unsigned in *. substs.

  unfold Aarray in *.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1:Aarray'_precise_ptr_eq' _H _H0; clear _H _H0;auto.
  specialize (Hx1 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
  simpljoin1.
  lets Hx2: kportNode_P_precise H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma Channel_dstkport_get_precise: 
  forall vl e e0 i ier l a M1 M2 o1 o2 head  n vl' , 
    (e, e0, M1, i, ier, l, o1, a) |= Channel_dstkport_get head Vnull n vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Channel_dstkport_get head Vnull n vl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  induction vl;intros.
  - destruct n, vl';cbn [Channel_dstkport_get] in *;tryfalse.
    simpl in H, H0.
    simpljoin1. auto.
  - destruct n, vl';cbn [Channel_dstkport_get] in *;tryfalse.
    sep normal in H. sep normal in H0.
    sep destruct H. sep destruct H0.
    sep split in H. sep split in H0.
    simpljoin1. inverts H10.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    simpl in _H, _H0.
    simpljoin1.
    destruct a1.
    cbn in H13, H15.
    do 7 (destruct x as [ |? x];tryfalse; destruct H5 as [? H5]).
    cbn in H6. inverts H6.
    do 7 (destruct x1 as [ |? x1];tryfalse; destruct H8 as [? H8]).
    cbn in H9. inverts H9.
    lets Hx1 : mapstoval_true_rule_type_val_match_eq M H19 H25 H15 H13.
    assert (x0 = x2 /\ x3 = x7). apply Hx1;mem_join_sub_solver.
    simpljoin1.
    clear Hx1.
    lets Hx1: IHvl H H0.
    assert (x4 = x8 /\ o1 = o2).
    { eapply Hx1 with (M:= M) (o:=o);auto;try mem_join_sub_solver. }
    simpljoin1.
    repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto.
Qed.


Lemma ChannelNode_precise: 
  forall chanvl e e0 i ier l a M1 M2 o1 o2 chanl chandstkportll chanl' chandstkportll', 
    (e, e0, M1, i, ier, l, o1, a) |= ChannelNode chanvl chanl chandstkportll ->
    (e, e0, M2, i, ier, l, o2, a) |= ChannelNode chanvl chanl' chandstkportll' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  induction chanvl;intros.
  - destruct chanl,chandstkportll, chanl', chandstkportll'; cbn [ChannelNode] in *;tryfalse.
    simpl in H, H0. simpljoin1.
    auto.
  - destruct chanl,chandstkportll, chanl', chandstkportll'; cbn [ChannelNode] in *;tryfalse.
    
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    destruct _H as [_H | _H]; destruct _H0 as [_H0 | _H0]; 
    unfold node in *;
    sep normal in _H; sep normal in _H0;
    try sep destruct _H; try sep destruct _H0;
    sep split in _H;sep split in _H0.
    2: { simpljoin1. inverts H12. }
    2: { simpljoin1. inverts H11. }
    { (* Vnull *)
      simpl in _H, _H0. simpljoin1.
      eapply IHchanvl;eauto.
    }
    { (* Vptr *)
      simpljoin1. inverts H14.
      lets Hx1: IHchanvl H H0. clear H H0.
      rename _H into H. rename _H0 into H0. 
      elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
      lets Hx2: Astruct_precise H H0; auto.
      unfold Astruct in *. unfold OS_Channel in H, H0.
      eapply Astruct'_vl_eq with (M:= M) (vl:= v) (vl':= v0)in H0;eauto.
      2,3: mem_join_sub_solver.
      assert (v = v0).
      { clear - H15 H16 H0.
        rename v into l. 
        do 8 (destruct l as [ | ];simpl in H16;tryfalse; destruct H16 as [? H16]).
        destruct l;tryfalse.
        rename v0 into l.
        do 8 (destruct l as [ | ];simpl in H15;tryfalse; destruct H15 as [? H15]).
        destruct l;tryfalse.
        cbn in *. simpljoin1. }
      subst v0.
      rewrite H12 in *. inverts H9.
      rewrite H13 in *. inverts H10.
      lets Hx3: Channel_dstkport_get_precise _H _H0.
      repeat match goal with 
      | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
        |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
        apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
        end.
      repeat match goal with 
      | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
        |- _ => assert (m1 = m2);[jeat | ]; subst m1 
        end.
      auto. }
Qed.

Lemma AOSChannelIDTbl_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 chanvl chanl chandstkportll chanvl' chanl' chandstkportll', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSChannelIDTbl chanvl chanl chandstkportll ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSChannelIDTbl chanvl' chanl' chandstkportll' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AOSChannelIDTbl, GAarray;intros.
  sep normal in H. sep normal in H0.
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H. simpl in _H0.
  simpljoin1.
  rewrite H14 in H13. inverts H13.
  destruct x0,x. cbn [addrval_to_addr] in *. 
  rewrite <- H19 in H15; inverts H15.
  assert(Int.repr (Int.unsigned i0) = Int.repr (Int.unsigned i1)).
  rewrite H11; auto.
  do 2 rewrite Int.repr_unsigned in *. substs.

  unfold Aarray in *.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1:Aarray'_precise_ptr_eq' _H _H0; clear _H _H0;auto.
  specialize (Hx1 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
  simpljoin1.
  lets Hx2: ChannelNode_precise H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma kportf_sll_head_isptr : forall l p s,
  s |= kportf_sll p l OS_K_Port OS_K_Port_V_OSEventPtr ->
  isptr p.
Proof.
  induction l.
  - intros. cbn in H.
    unfold isptr. tauto. 
  - intros.
    unfold kportf_sll in H; cbn [kportf_sllseg] in H;unfold node in H.
    sep normal in H.
    sep destruct H.
    sep split in H.
    simpljoin1.
    unfold isptr.
    right.
    eexists. eauto.
Qed.

Lemma kportf_sll_precise: 
  forall vl e e0 i ier l a M1 M2 o1 o2 p vl', 
    (e, e0, M1, i, ier, l, o1, a) |= kportf_sll p vl OS_K_Port OS_K_Port_V_OSEventPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= kportf_sll p vl' OS_K_Port OS_K_Port_V_OSEventPtr ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold kportf_sll. induction vl;intros.
  - destruct vl'; cbn [kportf_sllseg] in *.
    simpl in H, H0. simpljoin1. auto.
    sep split in H.

    unfold node in H0.
    sep normal in H0. sep destruct H0. sep split in H0.
    simpljoin1. inverts H6.
  - destruct vl'; cbn [kportf_sllseg] in *.
    sep split in H0.
    unfold node in H.
    sep normal in H. sep destruct H. sep split in H.
    simpljoin1. inverts H6.
    unfold node in *.
    sep normal in H. sep normal in H0.
    sep destruct H. sep destruct H0. 
    sep split in H. sep split in H0.
    simpljoin1. inverts H14.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1: Astruct_precise _H _H0;auto.
    assert (struct_atom_val_eq a v OS_K_Port).
    { eapply  Astruct_vl_eq with (M:= M);eauto.
      1,2: mem_join_sub_solver. }
    assert (a = v).
    { clear - H23 H24 H27.
      rename a into l. 
      do 7 (destruct l as [ | ];simpl in H24;tryfalse; destruct H24 as [? H24]).
      destruct l;tryfalse.
      rename v into l.
      do 7 (destruct l as [ | ];simpl in H23;tryfalse; destruct H23 as [? H23]).
      destruct l;tryfalse.
      cbn in *. simpljoin1. }
    subst a. 
    rewrite H15 in *. inverts H8.
    lets Hx2:  IHvl H H0.
    repeat match goal with 
    | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
      |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
      apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
      end.
    repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto.
Qed.

Lemma channelf_sll_head_isptr : forall l p s,
  s |= channelf_sll p l OS_Channel OS_Channel_V_OSEventPtr ->
  isptr p.
Proof.
  induction l.
  - intros. cbn in H.
    unfold isptr. tauto. 
  - intros.
    unfold channelf_sll in H; cbn [channelf_sllseg] in H;unfold node in H.
    sep normal in H.
    sep destruct H.
    sep split in H.
    simpljoin1.
    unfold isptr.
    right.
    eexists. eauto.
Qed.


Lemma AOSKernelPortFreeList_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 kportfptr kportfl kportfptr' kportfl', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSKernelPortFreeList kportfptr kportfl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSKernelPortFreeList kportfptr' kportfl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AOSKernelPortFreeList;intros.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H. simpl in _H0.
  simpljoin1.
  rewrite H23 in H14. inverts H14.
  eapply kportf_sll_head_isptr in H as ?.
  eapply kportf_sll_head_isptr in H0 as ?.

  lets Hx1 : mapstoval_true_rule_type_val_match_eq M H24 H15.
  { unfold isptr in H6. cbn. destruct H6 as [? | [? ?]];subst;auto. } 
  { unfold isptr in H8. cbn. destruct H8 as [? | [? ?]];subst;auto. }
  assert (kportfptr = kportfptr' /\ x = x3).
  { apply Hx1;mem_join_sub_solver. }
  clear Hx1.
  simpljoin1.
  lets Hx2: kportf_sll_precise H H0. clear H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);auto;mem_join_sub_solver| ];destruct h; subst x1 y1;clear Hx
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma channelf_sll_precise: 
  forall vl e e0 i ier l a M1 M2 o1 o2 p vl', 
    (e, e0, M1, i, ier, l, o1, a) |= channelf_sll p vl OS_Channel OS_Channel_V_OSEventPtr ->
    (e, e0, M2, i, ier, l, o2, a) |= channelf_sll p vl' OS_Channel OS_Channel_V_OSEventPtr ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold channelf_sll. induction vl;intros.
  - destruct vl'; cbn [channelf_sllseg] in *.
    simpl in H, H0. simpljoin1. auto.
    sep split in H.

    unfold node in H0.
    sep normal in H0. sep destruct H0. sep split in H0.
    simpljoin1. inverts H6.
  - destruct vl'; cbn [channelf_sllseg] in *.
    sep split in H0.
    unfold node in H.
    sep normal in H. sep destruct H. sep split in H.
    simpljoin1. inverts H6.
    unfold node in *.
    sep normal in H. sep normal in H0.
    sep destruct H. sep destruct H0. 
    sep split in H. sep split in H0.
    simpljoin1. inverts H14.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1: Astruct_precise _H _H0;auto.
    assert (struct_atom_val_eq a v OS_Channel).
    { eapply  Astruct_vl_eq with (M:= M);eauto.
      1,2: mem_join_sub_solver. }
    assert (a = v).
    { clear - H23 H24 H27.
      rename a into l. 
      do 8 (destruct l as [ | ];simpl in H24;tryfalse; destruct H24 as [? H24]).
      destruct l;tryfalse.
      rename v into l.
      do 8 (destruct l as [ | ];simpl in H23;tryfalse; destruct H23 as [? H23]).
      destruct l;tryfalse.
      cbn in *. simpljoin1. }
    subst a. 
    rewrite H15 in *. inverts H6.
    lets Hx2:  IHvl H H0.
    repeat match goal with 
    | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
      |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
      apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
      end.
    repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto.
Qed.

Lemma AOSChannelFreeList_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 chanfptr chanfl chanfptr' chanfl', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSChannelFreeList chanfptr chanfl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSChannelFreeList chanfptr' chanfl' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AOSChannelFreeList;intros.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H. simpl in _H0.
  simpljoin1.
  rewrite H23 in H14. inverts H14.
  eapply channelf_sll_head_isptr in H as ?.
  eapply channelf_sll_head_isptr in H0 as ?.

  lets Hx1 : mapstoval_true_rule_type_val_match_eq M H24 H15.
  { unfold isptr in H6. cbn. destruct H6 as [? | [? ?]];subst;auto. } 
  { unfold isptr in H8. cbn. destruct H8 as [? | [? ?]];subst;auto. }
  assert (chanfptr = chanfptr' /\ x = x3).
  { apply Hx1;mem_join_sub_solver. }
  clear Hx1.
  simpljoin1.
  lets Hx2: channelf_sll_precise H H0. clear H H0.
  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);auto;mem_join_sub_solver| ];destruct h; subst x1 y1;clear Hx
    end.
  repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma Hdomainportl_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= Hdomainportl x1 ->
  (e, e0, M2, i, ier, l, o2, a) |= Hdomainportl x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma Hcoreportpl_precise_eq :
forall x1 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= Hcoreportpl x1 ->
  (e, e0, M2, i, ier, l, o2, a) |= Hcoreportpl x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 /\ x1 = x2).      
Proof.
  intros.
  simpl in H, H0.
  destruct H, H0. subst.
  lets Hx : osabst_sub_sig_eq H3 H4.
  inversion Hx. auto.
Qed.

Lemma RH_CorePortPtrList_isptr : forall pl p dportls s,
  s |= [| RH_CorePortPtrList p pl dportls |]->
  isptr p.
Proof.
  induction pl; intros.
  + unfold RH_CorePortPtrList in H.
    sep split in H.
    subst. left. auto.
  + simpl RH_CorePortPtrList in H.
    sep split in H.
    simpljoin1.
    right. eauto.
Qed.

Lemma AOSCorePortPtrList_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 p p' pl pl' dportls dportls', 
    (e, e0, M1, i, ier, l, o1, a) |= AOSCorePortPtrList p pl dportls ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSCorePortPtrList p' pl' dportls' ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold AOSCorePortPtrList;intros.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H. simpl in _H0.
  simpljoin1.
  rewrite H23 in H14. inverts H14.
  eapply RH_CorePortPtrList_isptr in H as ?.
  eapply RH_CorePortPtrList_isptr in H0 as ?.

  lets Hx1 : mapstoval_true_rule_type_val_match_eq M H24 H15.
  { unfold isptr in H6. cbn. destruct H6 as [? | [? ?]];subst;auto. } 
  { unfold isptr in H8. cbn. destruct H8 as [? | [? ?]];subst;auto. }
  assert (p = p' /\ x = x3).
  { apply Hx1;mem_join_sub_solver. }
  clear Hx1.
  simpljoin1.
  sep split in H. inverts H.
  sep split in H0. inverts H0.
  simpl in H10, H11, H12, H13. subst.
  unfold emposabst in H11, H13. subst.
  jeat. 
Qed.

Lemma dportls1_eq: forall dportl dportls1 dportls1' dportls2 dportls2' dportls dportlptr dportmsgll dportmsgll',
  join dportls1 dportls2 dportls ->
  join dportls1' dportls2' dportls ->
  RLH_Domainportl dportlptr dportl dportmsgll dportls1 ->
  RLH_Domainportl dportlptr dportl dportmsgll' dportls1' ->
  dportls1 = dportls1'.
Proof.
  induction dportl; 
  destruct dportmsgll; destruct dportmsgll';
  simpl; intros; tryfalse.
  { destruct H1, H2; subst; auto. }
  simpljoin1. inverts H2.
  pose proof map_join_assoc H7 H. simpljoin1.
  pose proof map_join_assoc H3 H0. simpljoin1.
  assert (x0 = x3); [ |subst].
  { assert (get dportls x = Some x0).
    { eapply join_sig_get; eauto. }
    assert (get dportls x = Some x3).
    { eapply join_sig_get; eauto. }
    rewrite H13 in H14. inverts H14. auto. }
  assert (x2 = x7); [ |subst].
  { eapply map_join_cancel; eauto. }
  rewrite H9 in H5; inverts H5.
  assert (x1 = x4); [ |subst].
  { eapply IHdportl; eauto. }
  eapply map_join_deter; eauto.
Qed.

Lemma join_two_sig: forall [A B T : Type] [MC : PermMap A B T] 
  (a: A) (a0: A) (x: B) (x0: B) (y: T) (y0: T) (z: T),
  usePerm = false -> a <> a0 -> join (sig a x) y z -> join (sig a0 x0) y0 z ->
  exists u, join (sig a x) u y0 /\ join (sig a0 x0) u y.
Proof.
  intros.
  assert (indom z a0).
  { unfold indom. exists x0.
    eapply join_sig_get; eauto. }
  pose proof join_in_or H1 H3.
  destruct H4.
  { unfold indom in H4. destruct H4.
    pose proof map_get_sig' x H0.
    rewrite H4 in H5. inverts H5. }
  unfold indom in H3. destruct H3.
  unfold indom in H4. destruct H4.
  pose proof join_sig_get H H2.
  rewrite H3 in H5. inverts H5.
  pose proof join_get_get_r H H1 H4.
  rewrite H3 in H5. inverts H5.
  pose proof map_join_get_sig H4.
  destruct H5. exists x0. split; auto.
  apply map_join_comm in H1.
  pose proof map_join_assoc H5 H1.
  destruct H6 as [? [? ?]].
  pose proof map_join_cancel H2 H6.
  subst. apply map_join_comm. auto.
Qed.

Lemma RLH_OtherPortPtrList_join_sig:
  forall otherppl otherpl othermsgll x2 t x x3,
    RLH_OtherPortPtrList otherppl otherpl othermsgll x2 ->
    join (sig t x) x3 x2 ->
    exists n port msgl otherppl1 otherppl2 otherpl1 otherpl2
    othermsgll1 othermsgll2,
      OtherPortNode_P port x msgl /\
      length otherppl1 = n /\ otherppl = otherppl1 ++ t :: otherppl2 /\
      length otherpl1 = n /\ otherpl = otherpl1 ++ port :: otherpl2 /\
      length othermsgll1 = n /\ othermsgll = othermsgll1 ++ msgl :: othermsgll2 /\
      RLH_OtherPortPtrList (otherppl1 ++ otherppl2)
        (otherpl1 ++ otherpl2) (othermsgll1 ++ othermsgll2) x3.
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll;
  simpl; intros; tryfalse; subst.
  { apply map_join_pos in H0.
    destruct H0. inverts H. }
  simpljoin1.
  assert (a = t \/ a <> t) as [? | ?] by tauto.
  { subst. assert (x = x0); [ |subst].
    { assert (get x2 t = Some x).
      { eapply join_sig_get; eauto. }
      assert (get x2 t = Some x0).
      { eapply join_sig_get; eauto. }
      rewrite H3 in H4. inverts H4. auto. }
    assert (x1 = x3); [ |subst; clear H].
    { eapply map_join_cancel; eauto. }
    exists 0%nat v l (@nil tid) otherppl (@nil vallist).
    exists otherpl (@nil (list vallist)) othermsgll.
    splits; eauto. }
  assert (exists u, join (sig a x0) u x3 /\ join (sig t x) u x1).
  { eapply join_two_sig; eauto. }
  destruct H4 as [? [? ?]].
  lets ?: IHotherppl H2 H5.
  simpljoin1.
  exists (S (length x8)) x6 x7 (a :: x8) x9 (v :: x10).
  exists x11 (l :: x12) x13. splits; eauto.
  { simpl. lia. }
  { simpl. lia. }
  cbn. exists x0 x4. splits; eauto.
Qed.

Lemma RLH_OtherPortPtrList_in_dportls:
  forall otherppl otherpl othermsgll dportls n x,
    RLH_OtherPortPtrList otherppl otherpl othermsgll dportls ->
    nth_error otherppl n = Some x ->
    exists y dportls', join (sig x y) dportls' dportls.
Proof.
  induction otherppl; destruct otherpl; destruct othermsgll;
  simpl; intros; tryfalse; subst.
  { rewrite nth_error_nil in H0. inverts H0. }
  simpljoin1. destruct n; simpl in *.
  { inverts H0. exists x0 x1; auto. }
  lets ?: IHotherppl H2 H0. simpljoin1.
  apply map_join_comm in H.
  pose proof map_join_assoc H3 H.
  destruct H4 as [? [? ?]].
  eexists; eauto.
Qed.

Lemma RLH_OtherPortPtrList_add_one: 
  forall x16 x17 x18 x19 x20 x21 t x5 x2 x4 x6 x13,
    RLH_OtherPortPtrList (x16 ++ x17) (x18 ++ x19) (x20 ++ x21) x13 ->
    join (sig t x4) x13 x2 ->
    OtherPortNode_P x5 x4 x6 ->
    length x18 = length x16 ->
    length x20 = length x16 ->
    RLH_OtherPortPtrList (x16 ++ t :: x17) (x18 ++ x5 :: x19) (x20 ++ x6 :: x21) x2.
Proof.
  induction x16; destruct x18; destruct x20;
  simpl; intros; tryfalse.
  { do 2 eexists; splits; eauto. }
  simpljoin1.
  apply map_join_comm in H0.
  pose proof map_join_assoc H H0.
  destruct H6 as [? [? ?]].
  exists x x1; splits; eauto.
  eapply IHx16; eauto.
  apply map_join_comm; auto.
Qed.

Lemma OtherPortPtrList_perm: forall otherppl otherpl othermsgll dportls2 otherppl' otherpl' othermsgll',
  RLH_OtherPortPtrList otherppl otherpl othermsgll dportls2 ->
  RLH_OtherPortPtrList otherppl' otherpl' othermsgll' dportls2 ->
  Permutation otherppl otherppl'.
Proof.
  induction otherppl; destruct otherppl'; destruct otherpl;
  destruct otherpl'; destruct othermsgll;
  destruct othermsgll'; simpl; intros; auto; tryfalse.
  { simpljoin1. apply map_join_pos' in H0. inverts H0. }
  { simpljoin1. apply map_join_pos' in H. inverts H. }
  { simpljoin1.
    assert (a = t \/ a <> t) as [? | ?] by tauto.
    { subst. apply perm_skip.
      assert (x = x1); [ |subst].
      { assert (get dportls2 t = Some x).
        { eapply join_sig_get; eauto. }
        assert (get dportls2 t = Some x1).
        { eapply join_sig_get; eauto. }
        rewrite H5 in H6. inverts H6. auto. }
      assert (x0 = x2); [ |subst].
      { eapply map_join_cancel; eauto. }
      eapply IHotherppl; eauto. }
    assert (exists u, join (sig a x1) u x0 /\ join (sig t x) u x2).
    { eapply join_two_sig; eauto. }
    simpljoin1.
    lets ?: RLH_OtherPortPtrList_join_sig H2 H6.
    lets ?: RLH_OtherPortPtrList_join_sig H4 H7.
    simpljoin1.
    eapply Permutation_trans.
    2:{ instantiate (1:=a :: x16 ++ t :: x17).
        eapply Permutation_trans.
        { apply Permutation_middle. }
        eapply Permutation_trans.
        2:{ eapply Permutation_sym.
            apply Permutation_middle. }
        apply Permutation_app_head.
        apply perm_swap. }
    apply perm_skip.
    eapply IHotherppl; eauto.
    assert (nth_error (x7 ++ t :: x8) (length x7) = Some t).
    { clear. induction x7; simpl; eauto. }
    lets ?: RLH_OtherPortPtrList_in_dportls H4 H10.
    destruct H11 as [? [? ?]].
    instantiate (2:=x18 ++ x5 :: x19).
    instantiate (1:=x20 ++ x6 :: x21).
    assert (x = x4); [ |subst].
    { assert (get x2 t = Some x).
      { eapply join_sig_get; eauto. }
      assert (get x2 t = Some x4).
      { eapply join_sig_get; eauto. }
      unfold absdomainport.B in H13, H15.
      rewrite H13 in H15. inverts H15. auto. }
    assert (x3 = x13); [ |subst; clear H11].
    { eapply map_join_cancel; eauto. }
    eapply RLH_OtherPortPtrList_add_one; eauto. }
Qed.

Lemma OtherPortPtrList_match:
  forall x a x0 l1 l2 s P,
    s |= OtherPortPtrList (x ++ a :: x0) l1 l2 ** P ->
    exists u v l3 l4 l5 l6,
      l1 = l3 ++ u :: l4 /\
      l2 = l5 ++ v :: l6 /\
      length l3 = length x /\
      length l5 = length x.
Proof.
  induction x; intros.
  { simpl (_ ++ _) in *.
    destruct l1; destruct l2.
    4:{ exists v l (@nil vallist) l1 (@nil (list vallist)) l2.
        splits; simpl; auto. }
    all:  cbn [OtherPortPtrList] in *;
          apply astar_l_afalse_elim in H;
          tryfalse. }
  { simpl ((_ :: _) ++ _) in *.
    destruct l1; destruct l2; tryfalse.
    1,2,3:  cbn [OtherPortPtrList] in *;
            apply astar_l_afalse_elim in H;
            tryfalse.
    cbn [OtherPortPtrList] in *.
    sep normal in H. sep destruct H. sep split in H.
    sep lift 3%nat in H.
    lets ?: IHx H. simpljoin1.
    exists x2 x3 (v :: x4) x5 (l :: x6) x7.
    splits; simpl; auto; lia. }
Qed.

Lemma OtherPortPtrList_change:
  forall x s a x0 x3 x1 x4 x5 x2 x6 P,
    length x3 = length x -> length x5 = length x ->
    s |= OtherPortPtrList (x ++ a :: x0) (x3 ++ x1 :: x4) (x5 ++ x2 :: x6) ** P ->
    s |= OtherPortPtrList (a :: x ++ x0) (x1 :: x3 ++ x4) (x2 :: x5 ++ x6) ** P.
Proof.
  induction x; destruct x3; destruct x5;
  simpl (length _); intros; tryfalse.
  { simpl (_ ++ _) in *. auto. }
  simpl ((_ :: _) ++ _) in *.
  cbn [OtherPortPtrList] in H1.
  sep normal in H1. sep destruct H1. sep split in H1.
  sep lift 3%nat in H1.
  lets ?: IHx H1. 1,2: lia.
  cbn [OtherPortPtrList] in *.
  sep pauto. 2,3: eauto.
  sep lifts (4::5::3::1::2::nil)%nat.
  auto.
Qed.

Lemma OtherPortPtrList_precise: 
forall otherppl otherppl', 
  Permutation otherppl otherppl' ->
  forall otherpl othermsgll otherpl' othermsgll' e e0 i ier l a M1 M2 o1 o2,
  (e, e0, M1, i, ier, l, o1, a) |= OtherPortPtrList otherppl otherpl othermsgll ->
  (e, e0, M2, i, ier, l, o2, a) |= OtherPortPtrList otherppl' otherpl' othermsgll' ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  induction otherppl; intros.
  { destruct otherpl; destruct othermsgll; tryfalse.
    cbn [OtherPortPtrList] in *; tryfalse.
    apply Permutation_nil in H; subst.
    destruct otherpl'; destruct othermsgll'; tryfalse.
    cbn [OtherPortPtrList] in *; tryfalse.
    simpl_sat H0. simpl_sat H1. 
    simpljoin1. auto. }
  { destruct otherpl; destruct othermsgll; tryfalse.
    apply Permutation_sym in H.
    lets ?: Permutation_vs_cons_inv a H. simpljoin1.
    apply Permutation_sym in H.
    apply Permutation_cons_app_inv in H.
    apply step_prop.StarEmpIR in H1.
    lets ?: OtherPortPtrList_match H1. simpljoin1.
    apply OtherPortPtrList_change in H1; auto.
    apply step_prop.StarEmpER in H1.

    cbn [OtherPortPtrList] in H0, H1.
    sep destruct H0. sep destruct H1.
    sep split in H0. sep split in H1.

    elim_sep_conj1 H0 _H0; elim_sep_conj1 H1 _H1.
    lets Hx1 : Astruct'_precise _H0 _H1; auto.
    assert (struct_atom_val_eq' v x1 OS_Port_Seg_dls).
    { eapply Astruct'_vl_eq with (M:= M);eauto.
      1,2: mem_join_sub_solver. }
    clear _H0 _H1.
    assert (v = x1).
    { clear - H16 H6 H10. rename v into l.
      do 18 (destruct l; simpl in H6; tryfalse; destruct H6 as [? H6]).
      do 18 (destruct x1; simpl in H10; tryfalse; destruct H10 as [? H10]).
      cbn in *.
      destruct l; tryfalse. destruct x1; tryfalse.
      simpljoin1. }
    subst v.
    elim_sep_conj1 H0 _H0; elim_sep_conj1 H1 _H1.
    destruct _H0 as [_H0 | _H0]; destruct _H1 as [_H1 | _H1]; 
    try sep destruct _H0; try sep destruct _H1;
    sep split in _H0; sep split in _H1.
    2: { rewrite H22 in *. clear - H21. tryfalse. } 
    2: { rewrite H28 in *. clear - H21. tryfalse. }
    { (* sample *)
      rewrite H7 in *. inverts H11.
      rewrite H21 in *. inverts H22.
      lets Hx2: IHotherppl H H0 H1.
      clear H0 H1.
      rename _H1 into H1. rename _H0 into H0. 
      unfold dmportp_sllseg_sampleport_msg in *.
      sep normal in H1. sep normal in H0.
      sep destruct H1. sep destruct H0.
      sep split in H1. sep split in H0.
      inverts H22. inverts H24.
      elim_sep_conj1 H1 _H1; elim_sep_conj1 H0 _H0.
      lets Hx3: Aarray_precise _H0 _H1. clear _H1 _H0.
      simpl in H1. simpl in H0.
      simpljoin1.
      lets Hx4: mapstoval_true_mem_eq M H0 H1; auto.
      1,2: mem_join_sub_solver. 
      specialize (Hx2 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))).
      repeat match goal with 
      | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
        |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
        apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
        end.
      subst. simpljoin1.
        repeat match goal with 
      | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
        |- _ => assert (m1 = m2);[jeat | ]; subst m1 
        end.
      auto. }
    destruct H32. destruct H33.
    destruct H25. destruct H26.
    rewrite H7 in *. inverts H11.
    rewrite H28 in *. inverts H21.
    rewrite H29 in *. inverts H22.
    rewrite H30 in *. inverts H23.
    rewrite H31 in *. inverts H24.
    rewrite H32 in *. inverts H25.
    rewrite H33 in *. inverts H26.
    lets Hx2: IHotherppl H H0 H1.
    clear H1 H0.
    rename _H1 into H1. rename _H0 into H0. 
    elim_sep_conj1 H1 _H1; elim_sep_conj1 H0 _H0.
    lets Hx3: dmportp_sllseg_qport_msg_precise _H0 _H1. clear _H0 _H1.
    lets Hx4: dmportp_sllseg_qport_msg_precise H0 H1; auto.
    repeat match goal with 
    | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
      |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
      apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
      end.
    (* specialize (Hx2 M o (ltac:(mem_join_sub_solver)) ((ltac:(mem_join_sub_solver))) (ltac:(mem_join_sub_solver)) (ltac:(mem_join_sub_solver))). *)
    simpljoin1.
      repeat match goal with 
    | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
      |- _ => assert (m1 = m2);[jeat | ]; subst m1 
      end.
    auto. }
Qed.

(* add by CNU *)

(* Adomain2index *)
Lemma Adomain2index'_precise' :
  forall vl vl' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= Adomain2index' vl ->
    (e, e0, M2, i, ier, l, o2, a) |= Adomain2index' vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold Adomain2index'; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H25, H12; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H1 in H4.
  unfold addrval_to_addr in H4; destruct x18, x11; inverts H4.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma Adomain2index_precise' :
  forall vl vl' domls domls' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= Adomain2index vl domls->
    (e, e0, M2, i, ier, l, o2, a) |= Adomain2index vl' domls'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold Adomain2index; intros.
  sep split in H.
  sep split in H0.
  sep remember (2:: nil)%nat in H.
  sep remember (2:: nil)%nat in H0.
  simpl in H, H0.
  simpljoin1.
  eapply Adomain2index'_precise' in H17; eauto.
  destruct H17.
  split; intros.
  eapply H in H5; eauto.
  specialize H0 with (o := o).
  destruct H0;
  try eapply sub_trans;
  try solve [eapply osabst_join_sub_r; eauto]; eauto.
  eapply join_unique; eauto.
  assert ((domindexlist domls) = (domindexlist domls')).
  eapply osabst_sub_sig_eq;
  eapply sub_trans;
  try solve [eapply osabst_join_sub_l; eauto];
  eauto.
  rewrite H0 in *. eauto.
Qed.

Lemma Adomain2index_precise :
  forall vl vl' domls domls' e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= Adomain2index vl domls ->
    (e, e0, M2, i, ier, l, o2, a) |= Adomain2index vl' domls' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' dom domls' e e0 i ier l a M1 M2 o1 o2 H H0.
  eapply precise'2precise;eauto.
  eapply Adomain2index_precise';eauto.
Qed.

(* AisChangePartion *)
Lemma AisChangePartion_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 iscp iscp',
    (e, e0, M1, i, ier, l, o1, a) |= AisChangePartion iscp ->
    (e, e0, M2, i, ier, l, o2, a) |= AisChangePartion iscp' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AisChangePartion; intros.
  simpl in H, H0; simpljoin1.
  rewrite H27 in H11; inverts H11.
  split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AisChangePartion_precise :
forall e e0 i ier l a M1 M2 o1 o2 iscp iscp',
  (e, e0, M1, i, ier, l, o1, a) |= AisChangePartion iscp ->
  (e, e0, M2, i, ier, l, o2, a) |= AisChangePartion iscp' ->
  (forall (M : mem) (o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AisChangePartion_precise';eauto.
Qed.

(* AKsDSchdidx *)
Lemma AKsDSchdidx_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 ksdomscdidx ksdomscdidx',
    (e, e0, M1, i, ier, l, o1, a) |= AKsDSchdidx ksdomscdidx ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsDSchdidx ksdomscdidx' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AKsDSchdidx; intros.
  simpl in H, H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AKsDSchdidx_precise :
forall e e0 i ier l a M1 M2 o1 o2 ksdomscdidx ksdomscdidx',
  (e, e0, M1, i, ier, l, o1, a) |= AKsDSchdidx ksdomscdidx ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsDSchdidx ksdomscdidx' ->
  (forall (M : mem) (o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 ksdomscdidx ksdomscdidx' H H0.
  eapply precise'2precise;eauto.
  eapply AKsDSchdidx_precise';eauto.
Qed.

(* AKsDSchdlen *)
Lemma AKsDSchdlen_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 ksdomscdlen ksdomscdlen',
    (e, e0, M1, i, ier, l, o1, a) |= AKsDSchdlen ksdomscdlen ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsDSchdlen ksdomscdlen' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AKsDSchdlen; intros.
  simpl in H, H0; simpljoin1.
  rewrite H27 in H11; inverts H11.
  split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AKsDSchdlen_precise :
forall e e0 i ier l a M1 M2 o1 o2 ksdomscdlen ksdomscdlen',
  (e, e0, M1, i, ier, l, o1, a) |= AKsDSchdlen ksdomscdlen ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsDSchdlen ksdomscdlen' ->
  (forall (M : mem) (o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 ksdomscdlen ksdomscdlen' H H0.
  eapply precise'2precise;eauto.
  eapply AKsDSchdlen_precise';eauto.
Qed.

(* AKsCurDomain *)
Lemma AKsCurDomain_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 kscurdom kscurdom',
    (e, e0, M1, i, ier, l, o1, a) |= AKsCurDomain kscurdom ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsCurDomain kscurdom' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   unfold AKsCurDomain; intros.
   simpl in H, H0; simpljoin1.
   rewrite H27 in H11; inverts H11.
   split; intros.
   eapply mapstoval_true_mem_eq; eauto.
   auto.
Qed.

Lemma AKsCurDomain_precise :
forall e e0 i ier l a M1 M2 o1 o2 kscurdom kscurdom',
  (e, e0, M1, i, ier, l, o1, a) |= AKsCurDomain kscurdom ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsCurDomain kscurdom' ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 kscurdom kscurdom' H H0.
  eapply precise'2precise;eauto.
  eapply AKsCurDomain_precise';eauto.
Qed.

(* AKsLastDomain *)
Lemma AKsLastDomain_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 kslastd kslastd',
    (e, e0, M1, i, ier, l, o1, a) |= AKsLastDomain kslastd ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsLastDomain kslastd' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   unfold AKsLastDomain; intros.
   simpl in H, H0; simpljoin1.
   rewrite H13 in H4; inverts H4.
   split; intros.
   eapply mapstoval_true_mem_eq; eauto.
   auto.
Qed.

Lemma AKsLastDomain_precise :
forall e e0 i ier l a M1 M2 o1 o2 kslastd kslastd',
  (e, e0, M1, i, ier, l, o1, a) |= AKsLastDomain kslastd ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsLastDomain kslastd' ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 kslastd kslastd' H H0.
  eapply precise'2precise;eauto.
  eapply AKsLastDomain_precise';eauto.
Qed.

(* AKsDomainTime *)
Lemma AKsDomainTime_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 ksdomt ksdomt',
    (e, e0, M1, i, ier, l, o1, a) |= AKsDomainTime ksdomt ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsDomainTime ksdomt' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   unfold AKsDomainTime; intros.
   simpl in H, H0; simpljoin1.
   rewrite H13 in H4; inverts H4.
   split; intros.
   eapply mapstoval_true_mem_eq; eauto.
   auto.
Qed.

Lemma AKsDomainTime_precise :
forall e e0 i ier l a M1 M2 o1 o2 ksdomt ksdomt',
  (e, e0, M1, i, ier, l, o1, a) |= AKsDomainTime ksdomt ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsDomainTime ksdomt' ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 ksdomt ksdomt' H H0.
  eapply precise'2precise;eauto.
  eapply AKsDomainTime_precise';eauto.
Qed.

(* AKsDomSchedule' *)
Lemma AKsDomSchedule'_precise' :
forall e e0 i ier l a M1 M2 o1 o2 ksdschedule ksdschedule',
  (e, e0, M1, i, ier, l, o1, a) |= AKsDomSchedule' ksdschedule ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsDomSchedule' ksdschedule' ->
  (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AKsDomSchedule'; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H24, H4; simpljoin1.
  rewrite H18 in H6; inverts H6.
  split; intros.
  assert(sub x7 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  assert (x6 = x /\ x7 = x0).
  eapply mapstoval_true_vptr_eq; eauto.
  destruct H4.
  subst.
  lets Hx1: Aarray_new_precise' H29 H9 H35 H15; simpljoin1.
  eapply eq_join_eq; eauto.
  symmetry.
  specialize H4 with (M := M).
  assert(sub x8 M) by mem_join_sub_solver.
  assert(sub x1 M) by mem_join_sub_solver.
  assert (x8 = x1).

  eauto. eauto.
  apply Aarray_new_osabst_emp in H15; apply Aarray_new_osabst_emp in H35.
  substs; auto.
Qed.

(* AKsDomSchedule *)
Lemma AKsDomSchedule_precise' :
forall e e0 i ier l a M1 M2 o1 o2 ksdschedule ksdschedule' ksdscd ksdscd',
  (e, e0, M1, i, ier, l, o1, a) |= AKsDomSchedule ksdschedule ksdscd ->
  (e, e0, M2, i, ier, l, o2, a) |= AKsDomSchedule ksdschedule' ksdscd' ->
 (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AKsDomSchedule; intros.
  sep split in H.
  sep split in H0.
  sep remember (2:: nil)%nat in H.
  sep remember (2:: nil)%nat in H0.
  simpl in H, H0.
  simpljoin1.
  eapply AKsDomSchedule'_precise' in H17; eauto.
  destruct H17.
  split; intros.
  eapply H in H5; eauto.
  specialize H0 with (o := o).
  destruct H0;
  try eapply sub_trans;
  try solve [eapply osabst_join_sub_r; eauto]; eauto.
  eapply join_unique; eauto.
  assert ((ksdsched ksdscd) = (ksdsched ksdscd')).
  eapply osabst_sub_sig_eq;
  eapply sub_trans;
  try solve [eapply osabst_join_sub_l; eauto];
  eauto.
  rewrite H0 in *. eauto.
Qed.

Lemma AKsDomSchedule_precise :
  forall e e0 i ier l a M1 M2 o1 o2 ksdschedule ksdschedule' ksdscd ksdscd',
    (e, e0, M1, i, ier, l, o1, a) |= AKsDomSchedule ksdschedule ksdscd ->
    (e, e0, M2, i, ier, l, o2, a) |= AKsDomSchedule ksdschedule' ksdscd' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 ksdschedule ksdschedule' ksdscd ksdscd' H H0.
  eapply precise'2precise;eauto.
  eapply AKsDomSchedule_precise';eauto.
Qed.

(* AIntPartMux' *)
Lemma AIntPartMux'_precise' :
forall e e0 i ier l a M1 M2 o1 o2 intpmuxvl intpmuxvl',
  (e, e0, M1, i, ier, l, o1, a) |= AIntPartMux' intpmuxvl ->
  (e, e0, M2, i, ier, l, o2, a) |= AIntPartMux' intpmuxvl' ->
  (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AIntPartMux'; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H17, H4; simpljoin1.
  rewrite H20 in H6; inverts H6.
  split; intros.
  assert(sub x7 M) by mem_join_sub_solver.
  assert(sub x0 M) by mem_join_sub_solver.
  assert (x6 = x /\ x7 = x0).
  clear - H21 H7 H2 H3.
  eapply mapstoval_true_vptr_eq; eauto.
  destruct H4.
  rewrite H4 in H21. rewrite H5 in H21.
  substs.
  lets Hx1: Aarray_precise' H23 H10; simpljoin1.
  eapply eq_join_eq; eauto.
  symmetry.
  specialize H4 with (M := M).
  assert(sub x8 M) by mem_join_sub_solver.
  assert(sub x1 M) by mem_join_sub_solver.
  assert (x8 = x1).
  clear -H4 H6 H8.
  eauto. eauto.
  apply Aarray_osabst_emp in H10; apply Aarray_osabst_emp in H23.
  substs; auto.
Qed.

(* AIntPartMux *)
Lemma AIntPartMux_precise' :
forall e e0 i ier l a M1 M2 o1 o2 intpmuxvl intpmuxvl' intpmux intpmux',
  (e, e0, M1, i, ier, l, o1, a) |= AIntPartMux intpmuxvl intpmux ->
  (e, e0, M2, i, ier, l, o2, a) |= AIntPartMux intpmuxvl' intpmux' ->
 (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AIntPartMux; intros.
  sep split in H.
  sep split in H0.
  sep remember (2:: nil)%nat in H.
  sep remember (2:: nil)%nat in H0.
  simpl in H, H0.
  simpljoin1.
  eapply AIntPartMux'_precise' in H17; eauto.
  destruct H17.
  split; intros.
  eapply H in H5; eauto.
  specialize H0 with (o := o).
  destruct H0;
  try eapply sub_trans;
  try solve [eapply osabst_join_sub_r; eauto]; eauto.
  eapply join_unique; eauto.
  assert ((intparmux intpmux) = (intparmux intpmux')).
  eapply osabst_sub_sig_eq;
  eapply sub_trans;
  try solve [eapply osabst_join_sub_l; eauto];
  eauto.
  rewrite H0 in *. eauto.
Qed.

Lemma AIntPartMux_precise :
  forall e e0 i ier l a M1 M2 o1 o2 intpmuxvl intpmuxvl' intpmux intpmux',
    (e, e0, M1, i, ier, l, o1, a) |= AIntPartMux intpmuxvl intpmux ->
    (e, e0, M2, i, ier, l, o2, a) |= AIntPartMux intpmuxvl' intpmux' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier l a M1 M2 o1 o2 intpmuxvl intpmuxvl' intpmux intpmux' H H0.
  eapply precise'2precise;eauto.
  eapply AIntPartMux_precise';eauto.
Qed.


(* AIntrDomainMux *)
Lemma AIntrDomainMux_precise' :
  forall e e0 i ier lo a M1 M2 o1 o2 l vl absintrdom vl' absintrdom',
    (e, e0, M1, i, ier, lo, o1, a) |= AIntrDomainMux l vl absintrdom ->
    (e, e0, M2, i, ier, lo, o2, a) |= AIntrDomainMux l vl' absintrdom' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   unfold AIntrDomainMux; intros.
   simpl_sat H; simpl_sat H0; simpljoin1.
   rewrite H25 in H4; inverts H4.
   eapply Aarray_precise'; eauto.
Qed.

Lemma AIntrDomainMux_precise :
forall e e0 i ier lo a M1 M2 o1 o2 l vl absintrdom vl' absintrdom',
  (e, e0, M1, i, ier, lo, o1, a) |= AIntrDomainMux l vl absintrdom ->
  (e, e0, M2, i, ier, lo, o2, a) |= AIntrDomainMux l vl' absintrdom' ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier lo a M1 M2 o1 o2 l vl absintrdom vl' absintrdom' H H0.
  eapply precise'2precise;eauto.
  eapply AIntrDomainMux_precise';eauto.
Qed.

(* node_offt *)
Lemma node_offt_precise' :
forall vl vl' head t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= node_offt head vl t ->
    (e, e0, M2, i, ier, l, o2, a) |= node_offt head vl' t ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  intros.
  simpl in H, H0; simpljoin1; inverts H4.
  lets Hx: Astruct_precise' H16 H8 H13 H5; auto.
Qed.

Lemma node_offt_precise :
  forall vl vl' head t M1 M2 o1 o2 e e0 i ier l a,
    (e, e0, M1, i, ier, l, o1, a) |= node_offt head vl t ->
    (e, e0, M2, i, ier, l, o2, a) |= node_offt head vl' t ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros vl vl' head t M1 M2 o1 o2 e e0 i ier l a H H0.
  simpl in H, H0; simpljoin1; inverts H4.
  lets Hx: Astruct_precise H16 H8 H13 H5; auto.
Qed.

(* AAllArea *)
Lemma AAllArea_precise' :
  forall e e0 i ier lo a M1 M2 o1 o2 l vl areaconf vl' areaconf',
    (e, e0, M1, i, ier, lo, o1, a) |= AAllArea l vl areaconf ->
    (e, e0, M2, i, ier, lo, o2, a) |= AAllArea l vl' areaconf' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
   unfold AAllArea; intros.
   simpl_sat H; simpl_sat H0; simpljoin1.
   rewrite H23 in H9; inverts H9.
   eapply node_offt_precise'; eauto.
Qed.

Lemma AAllArea_precise :
forall e e0 i ier lo a M1 M2 o1 o2 l vl areaconf vl' areaconf',
  (e, e0, M1, i, ier, lo, o1, a) |= AAllArea l vl areaconf ->
  (e, e0, M2, i, ier, lo, o2, a) |= AAllArea l vl' areaconf' ->
  (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros e e0 i ier lo a M1 M2 o1 o2 l vl areaconf vl' areaconf' H H0.
  eapply precise'2precise;eauto.
  eapply AAllArea_precise';eauto.
Qed.

Lemma ADeviceioTbl'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= ADeviceioTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= ADeviceioTbl' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold ADeviceioTbl';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold ADeviceioTbl' in *.
destruct a as [].
destruct a0 as [].
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
subst.
inverts H1.
eapply eq_add_S in Hlen.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: Aarray_precise' H16 H6.
destruct Hp1 as (Hm1 & Ho1).
lets Hp2: node_offt_precise' H21 H11.
destruct Hp2 as (Hm2 & Ho2).
lets Hp3: IHvl Hlen H22 H12.
destruct Hp3 as (Hm3 & Ho3).
splits; intros.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma ADeviceioTbl'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= ADeviceioTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= ADeviceioTbl' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply ADeviceioTbl'_precise';eauto.
Qed.

Lemma AksDomains'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AksDomains' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AksDomains' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold AksDomains';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
try destruct a as [[[]]];
try destruct a0 as [[[]]];
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold AksDomains' in *.
subst. inverts H11.
rewrite H in H6; inverts H6.
rewrite H0 in H7; inverts H7.
rewrite H2 in H9; inverts H9.
rewrite <- H8 in H1.
eapply eq_add_S in Hlen.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: node_offt_precise' H33 H13.
destruct Hp1 as (Hm1 & Ho1).
lets Hp2: ADeviceioTbl'_precise' H1 H38 H18.
destruct Hp2 as (Hm2 & Ho2).
lets Hp3: Aarray_precise' H43 H23.
destruct Hp3 as (Hm3 & Ho3).
lets Hp4: IHvl Hlen H48 H28.
destruct Hp4 as (Hm4 & Ho4).
lets Hp5: node_offt_precise' H49 H29.
destruct Hp5 as (Hm5 & Ho5).
splits; intros.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma AksDomains'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AksDomains' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AksDomains' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AksDomains'_precise';eauto.
Qed.

Lemma AksDomSchedule'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AksDomSchedule' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AksDomSchedule' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold AksDomSchedule';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
try destruct a as [[[]]];
try destruct a0 as [[[]]];
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold AksDomSchedule' in *.
eapply eq_add_S in Hlen.
subst. inverts H0.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: node_offt_precise' H5 H10.
destruct Hp1 as (Hm1 & Ho1).
lets Hp2: IHvl Hlen H4 H9.
destruct Hp2 as (Hm2 & Ho2).
splits; intros.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma AksDomSchedule'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AksDomSchedule' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AksDomSchedule' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AksDomSchedule'_precise';eauto.
Qed.

Lemma Acpus'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Acpus' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Acpus' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold Acpus';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
try destruct a as [[[]]];
try destruct a0 as [[[]]];
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold Acpus' in *.
eapply eq_add_S in Hlen.
match goal with Hi1: ?l = _ , Hi2: ?l = _ |- _ => rewrite Hi1 in Hi2; inverts Hi2 end.
repeat try (match goal with
 Hi1: id_addrval (?b, ?i) ?idx cpu_conf_t = Some _ ,
 Hi2: id_addrval (?b, ?i) ?idx cpu_conf_t = Some _
  |- _ => rewrite Hi1 in Hi2; inverts Hi2
 end).
rewrite <- H9 in H.
rewrite <- H12 in H2.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: AksDomains'_precise' H40 H20; auto.
lets Hp2: AksDomSchedule'_precise' H45 H25; auto.
lets Hp3: Aarray_precise' H50 H30.
lets Hp4: IHvl H55 H35; auto.
lets Hp5: node_offt_precise' H56 H36.
simpljoin.
splits; intros.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma Acpus'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= Acpus' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= Acpus' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply Acpus'_precise';eauto.
Qed.


(* ACPUs *)
Lemma ACPUs_precise' :
  forall vl vl' l cpus_ cpus_' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= ACPUs l vl cpus_ ->
    (e, e0, M2, i, ier, lo, o2, a) |= ACPUs l vl' cpus_' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold ACPUs.
introv Hsat1 Hsat2.
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
rewrite <- H in H3.
rewrite H0 in H4; inverts H4.
lets Hp1: Acpus'_precise' Hsat1 Hsat2; auto.
Qed.

Lemma ACPUs_precise :
  forall vl vl' l cpus_ cpus_' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= ACPUs l vl cpus_ ->
    (e, e0, M2, i, ier, lo, o2, a) |= ACPUs l vl' cpus_' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply ACPUs_precise';eauto.
Qed.

(* AchannelTbl' *)
Lemma AchannelTbl'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AchannelTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AchannelTbl' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold AchannelTbl';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold AchannelTbl' in *.
destruct a as [].
destruct a0 as [].
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
subst.
inverts H2.
eapply eq_add_S in Hlen.
 rewrite H3 in H0; inverts H0.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: Aarray_precise' H17 H7.
destruct Hp1 as (Hm1 & Ho1).
lets Hp2: node_offt_precise' H23 H13.
destruct Hp2 as (Hm2 & Ho2).
lets Hp3: IHvl Hlen H22 H12.
destruct Hp3 as (Hm3 & Ho3).
splits; intros.
simpljoin.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma AchannelTbl'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AchannelTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AchannelTbl' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AchannelTbl'_precise';eauto.
Qed.

(* AChannelTbl *)
Lemma AChannelTbl_precise' :
  forall vl vl' l channels channels' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AChannelTbl l vl channels ->
    (e, e0, M2, i, ier, lo, o2, a) |= AChannelTbl l vl' channels' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold AChannelTbl.
introv Hsat1 Hsat2.
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
rewrite <- H in H2.
rewrite H0 in H3; inverts H3.
lets Hp1: AchannelTbl'_precise' Hsat1 Hsat2; auto.
Qed.

Lemma AChannelTbl_precise :
  forall vl vl' l channels channels' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AChannelTbl l vl channels ->
    (e, e0, M2, i, ier, lo, o2, a) |= AChannelTbl l vl' channels' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AChannelTbl_precise';eauto.
Qed.

(* AportTbl' *)
Lemma AportTbl'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AportTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AportTbl' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold AportTbl';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
try destruct a as [[[]]];
try destruct a0 as [[[]]];
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold AportTbl' in *.
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
subst.
inverts H0.
eapply eq_add_S in Hlen.
simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
lets Hp1: IHvl Hlen H4 H9; auto.
destruct Hp1 as (Hm1 & Ho1).
lets Hp2: node_offt_precise' H5 H10.
destruct Hp2 as (Hm2 & Ho2).
splits; intros.
simpljoin.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma AportTbl'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AportTbl' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AportTbl' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AportTbl'_precise';eauto.
Qed.

(* APortTbl *)
Lemma APortTbl_precise' :
  forall vl vl' l prttbl prttbl' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= APortTbl l vl prttbl ->
    (e, e0, M2, i, ier, lo, o2, a) |= APortTbl l vl' prttbl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold APortTbl.
introv Hsat1 Hsat2.
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
rewrite <- H in H3.
rewrite H0 in H4; inverts H4.
lets Hp1: AportTbl'_precise' Hsat1 Hsat2; auto.
Qed.

Lemma APortTbl_precise :
  forall vl vl' l prttbl prttbl' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= APortTbl l vl prttbl  ->
    (e, e0, M2, i, ier, lo, o2, a) |= APortTbl l vl' prttbl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply APortTbl_precise';eauto.
Qed.

(* AucosConf *)
Lemma AucosConf_precise' :
  forall l l' ucosf ucosf' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AucosConf l ucosf ->
    (e, e0, M2, i, ier, lo, o2, a) |= AucosConf l' ucosf' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AucosConf;
  try intro;
  introv Hsat1 Hsat2;
  try destruct l as [[[[[[]]]]]];
  try destruct ucosf as  [[[[[[[[[[[[[]]]]]]]]]]]]];
  try destruct l' as [[[[[[]]]]]];
  try destruct ucosf' as  [[[[[[[[[[[[[]]]]]]]]]]]]];
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  rewrite H in H2; inverts H2.
  simpl_sat Hsat1; simpl_sat Hsat2; simpljoin1.
  lets Hp1: AIntrDomainMux_precise' H34 H9; simpljoin1.
  lets Hp2: AAllArea_precise' H39 H14; simpljoin1.
  lets Hp3: ACPUs_precise' H44 H19; simpljoin1.
  lets Hp4: AChannelTbl_precise' H49 H24; simpljoin1.
  lets Hp5: APortTbl_precise' H54 H29; simpljoin1.
  lets Hp6: node_precise' H55 H30; simpljoin1.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AucosConf_precise :
  forall l l' ucosf ucosf' e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AucosConf l ucosf ->
    (e, e0, M2, i, ier, lo, o2, a) |= AucosConf l' ucosf' ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AucosConf_precise';eauto.
Qed.

(* ASMSMpax *)
Lemma Asms_mpaxinfo_precise' :
  forall vl vl'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= Asms_mpaxinfo vl  ->
    (e, e0, M2, i, ier, lo, o2, a) |= Asms_mpaxinfo vl'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
 unfold Asms_mpaxinfo;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  eapply Aarray_precise'; eauto.
Qed.

Lemma ASMSMpax_precise' :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= ASMSMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= ASMSMpax vl' abs'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold ASMSMpax;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  clear - Hsat1 Hsat2.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp1: Asms_mpaxinfo_precise' _H _H0; clear _H _H0.
  lets Hp2: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma ASMSMpax_precise :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= ASMSMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= ASMSMpax vl' abs'  ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply ASMSMpax_precise';eauto.
Qed.

(* ASESMpax *)
Lemma Ases_mpaxinfo_precise' :
  forall vl vl'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= Ases_mpaxinfo vl  ->
    (e, e0, M2, i, ier, lo, o2, a) |= Ases_mpaxinfo vl'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
 unfold Ases_mpaxinfo;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  eapply Aarray_precise'; eauto.
Qed.

Lemma ASESMpax_precise' :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= ASESMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= ASESMpax vl' abs'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold ASESMpax;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  clear - Hsat1 Hsat2.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp1: Ases_mpaxinfo_precise' _H _H0; clear _H _H0.
  lets Hp2: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma ASESMpax_precise :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= ASESMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= ASESMpax vl' abs'  ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply ASESMpax_precise';eauto.
Qed.

(* AXMpax *)
Lemma Axmpaxinfo_precise' :
  forall vl vl'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= Axmpaxinfo vl  ->
    (e, e0, M2, i, ier, lo, o2, a) |= Axmpaxinfo vl'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
 unfold Axmpaxinfo;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  eapply Aarray_precise'; eauto.
Qed.

Lemma AXMpax_precise' :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AXMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= AXMpax vl' abs'  ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold AXMpax;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  clear - Hsat1 Hsat2.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp1: Axmpaxinfo_precise' _H _H0; clear _H _H0.
  lets Hp2: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AXMpax_precise :
  forall vl abs vl' abs'  e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AXMpax vl abs  ->
    (e, e0, M2, i, ier, lo, o2, a) |= AXMpax vl' abs'  ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AXMpax_precise';eauto.
Qed.

(* AMPAXs *)
Lemma AMPAXs_precise' :
  forall e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AMPAXs ->
    (e, e0, M2, i, ier, lo, o2, a) |= AMPAXs ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AMPAXs;
  try intro;
  introv Hsat1 Hsat2;
  sep normal in Hsat1;
  sep normal in Hsat2;
  sep destruct Hsat1;
  sep destruct Hsat2;
  sep split in Hsat1;
  sep split in Hsat2;
  tryfalse.
  clear - Hsat1 Hsat2.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp1: ASMSMpax_precise' _H _H0; clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp2: ASESMpax_precise' _H _H0; clear _H _H0.
  lets Hp3: AXMpax_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AMPAXs_precise :
  forall e e0 M1 M2 i ier lo o1 o2 a,
    (e, e0, M1, i, ier, lo, o1, a) |= AMPAXs->
    (e, e0, M2, i, ier, lo, o2, a) |= AMPAXs ->
    (forall (M : mem) ( o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AMPAXs_precise';eauto.
Qed.

(* AKsDomains' *)
Lemma AKsDomains'_precise':
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AKsDomains' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AKsDomains' l vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
induction vl; induction vl'; 
unfold AKsDomains';
try intro;
introv Hlen Hsat1 Hsat2;
simpl length in *;
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2;
tryfalse.
simpl in Hsat1, Hsat2.
unfold emposabst in *.
simpljoin; auto.
fold AKsDomains' in *.
try destruct a as [];
try destruct a0 as [];
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
subst.
inverts H2.
eapply eq_add_S in Hlen.
rewrite H0 in H3; inverts H3.
clear - Hsat1 Hsat2 Hlen IHvl.
rename Hsat1 into H.
rename Hsat2 into H0.
elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
lets Hp1: Aarray_precise' _H _H0; clear _H _H0.
elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
lets Hp2: IHvl Hlen _H _H0; clear _H _H0.
lets Hp3: node_offt_precise' H H0; clear H H0.
simpljoin.
splits; intros.
mem_eq_solver M.
osabst_eq_solver o.
Qed.

Lemma AKsDomains'_precise:
  forall vl vl' l M1 M2 o1 o2 e e0 i ier lo a,
    length vl = length vl' ->
    (e, e0, M1, i, ier, lo, o1, a) |= AKsDomains' l vl ->
    (e, e0, M2, i, ier, lo, o2, a) |= AKsDomains' l vl' ->
    (forall (M: mem) (o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o ->
       M1 = M2 /\ o1 = o2).
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AKsDomains'_precise';eauto.
Qed.

Lemma AKsDomains'_osabst_emp :
  forall vl l e e0 M i ier lo o a,
    (e, e0, M, i, ier, lo, o, a) |= AKsDomains' l vl ->
    o = empabst.
Proof.
  induction vl.
  simpl; intros.
  simpljoin1.
  introv Hsat.
  destruct a.
  unfold AKsDomains' in Hsat.
  fold AKsDomains' in Hsat.
  unfold node_offt in Hsat.
  sep normal in Hsat;
  sep destruct Hsat; sep split in Hsat.
  simpljoin1.
  simpl_sat Hsat; simpljoin1.
  eapply Astruct_osabst_emp in H14.
  eapply Aarray_osabst_emp in H8; auto.
  eapply IHvl in H13; auto.
  simpljoin1.
Qed.

(* AKsDomains *)
Lemma AKsDomains_precise':
  forall vl vl' abs abs' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AKsDomains vl abs ->
    (e, e0, M2, i, ier, lo, o2, a) |= AKsDomains vl' abs' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
 unfold AKsDomains; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H30, H4; simpljoin1.
  rewrite H17 in H6; inverts H6.
  split; intros.
  assert (x6 = x /\ x7 = x0).
  eapply mapstoval_true_vptr_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin.
  rewrite <- H40 in H14.
  lets Hx1: AKsDomains'_precise' H35 H9; auto.
  destruct Hx1 as (Hm1 & Ho1).
  eapply eq_join_eq; eauto.
  eapply Hm1 with (M:= M); try mem_join_sub_solver.
  apply AKsDomains'_osabst_emp in H9; apply AKsDomains'_osabst_emp in H35.
  substs; auto.
Qed.


Lemma AKsDomains_precise :
  forall vl vl' abs abs' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AKsDomains vl abs   ->
    (e, e0, M2, i, ier, lo, o2, a) |= AKsDomains vl' abs' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
unfold AKsDomains.
introv Hsat1 Hsat2 Hm1 Hm2 Ho1 Ho2.
sep normal in Hsat1;
sep normal in Hsat2;
sep destruct Hsat1;
sep destruct Hsat2;
sep split in Hsat1;
sep split in Hsat2.
rewrite <- H in H2.
clear -Hm1 Hm2 Ho1 Ho2 Hsat1 Hsat2 H2.
rename Hsat1 into H.
rename Hsat2 into H0.
elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
lets Hp1: gvar_ptr_precise _H _H0; clear _H _H0.
unfolds; eauto.
unfolds; eauto.
specialize Hp1 with (M:= M) (o := o).
destruct Hp1; try mem_join_sub_solver M.
simpljoin.
inverts H8.
lets Hp2: AKsDomains'_precise H H0; clear H H0; auto.
repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

(* AisCoreBoot *)
Lemma AisCoreBoot_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 v v',
    (e, e0, M1, i, ier, l, o1, a) |= AisCoreBoot v ->
    (e, e0, M2, i, ier, l, o2, a) |= AisCoreBoot v' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AisCoreBoot; intros.
  simpl in H, H0; simpljoin1.
  rewrite H27 in H11; inverts H11.
  split; intros.
  eapply mapstoval_true_mem_eq; eauto.
  auto.
Qed.

Lemma AisCoreBoot_precise :
  forall v v' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AisCoreBoot v   ->
    (e, e0, M2, i, ier, lo, o2, a) |= AisCoreBoot v' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AisCoreBoot_precise';eauto.
Qed.

(* AsystemStck' *)
Lemma AsystemStck'_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= AsystemStck' vl ->
    (e, e0, M2, i, ier, l, o2, a) |= AsystemStck' vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AsystemStck'; intros.
  sep normal in H;
  sep normal in H0;
  sep destruct H;
  sep destruct H0;
  sep split in H;
  sep split in H0.
  simpl_sat H; simpl_sat H0; simpljoin1.
  rewrite <- H14 in H8.
  simpl in H6, H12; simpljoin1.
  rewrite H23 in H12; inverts H12.
  split; intros.
  assert (x = x0 /\ x7 = x1).
  eapply mapstoval_true_vptr_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin.
  lets Hp: Aarray_precise' H7 H13.
  destruct Hp as (Hm & Ho).
  eapply eq_join_eq; eauto.
  symmetry.
  eapply Hm with (M:= M); try mem_join_sub_solver.
  apply Aarray_osabst_emp in H7; apply Aarray_osabst_emp in H13.
  substs; auto.
Qed.

Lemma AsystemStck'_precise :
  forall v v' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AsystemStck' v   ->
    (e, e0, M2, i, ier, lo, o2, a) |= AsystemStck' v' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AsystemStck'_precise';eauto.
Qed.

(* AOSSystemSP *)
Lemma AOSSystemSP_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 v v',
    (e, e0, M1, i, ier, l, o1, a) |= AOSSystemSP v ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSSystemSP v' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSSystemSP; intros.
  simpl in H,H0; simpljoin1.
  rewrite H13 in H4; inverts H4.
  split; intros; auto.
  eapply mapstoval_true_vptr_eq in H; eauto.
  simpljoin.
Qed.

Lemma AOSSystemSP_precise :
  forall v v' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSSystemSP v   ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSSystemSP v' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AOSSystemSP_precise';eauto.
Qed.

(* ACorepartnum *)
Lemma ACorepartnum'_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 v v',
    (e, e0, M1, i, ier, l, o1, a) |= ACorepartnum' v ->
    (e, e0, M2, i, ier, l, o2, a) |= ACorepartnum' v' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold ACorepartnum'; intros.
  sep split in H; sep split in H0.
  simpl in H,H0; simpljoin1.
  rewrite H18 in H8; inverts H8.
  split; intros; auto.
  eapply mapstoval_true_mem_eq; eauto.
Qed.

Lemma ACorepartnum_precise :
  forall v v' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= ACorepartnum v   ->
    (e, e0, M2, i, ier, lo, o2, a) |= ACorepartnum v' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  unfold ACorepartnum in *.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp: ACorepartnum'_precise' _H _H0; clear _H _H0.
  lets Habslen: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

(* APortnumcur *)
Lemma APortnumcur_precise' :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= APortnumcur ->
    (e, e0, M2, i, ier, l, o2, a) |= APortnumcur ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APortnumcur; intros.
  sep destruct H; sep destruct H0.
  sep split in H; sep split in H0.
  simpl in H,H0; simpljoin1.
  rewrite H15 in H6; inverts H6.
  split; intros; auto.
  eapply mapstoval_true_mem_eq; eauto.
Qed.

Lemma APortnumcur_precise :
  forall M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= APortnumcur   ->
    (e, e0, M2, i, ier, lo, o2, a) |= APortnumcur ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply APortnumcur_precise';eauto.
Qed.

(* APartArea' *)
Lemma APartArea'_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= APartArea' vl ->
    (e, e0, M2, i, ier, l, o2, a) |= APartArea' vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APartArea'; intros.
  sep destruct H;
  sep destruct H0;
  sep split in H;
  sep split in H0.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H4, H9; simpljoin1.
  rewrite H19 in H9; inverts H9.
  split; intros.
  assert (x = x0 /\ x7 = x1).
  eapply mapstoval_true_vptr_eq with (M:= M); eauto.
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin.
  lets Hp: node_precise' H5 H10.
  destruct Hp as (Hm & Ho).
  eapply eq_join_eq; eauto.
  symmetry.
  eapply Hm with (M:= M); try mem_join_sub_solver.
  apply node_osabst_emp in H5; apply node_osabst_emp in H10.
  substs; auto.
Qed.

Lemma APartArea'_precise :
  forall vl vl' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= APartArea' vl   ->
    (e, e0, M2, i, ier, lo, o2, a) |= APartArea' vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply APartArea'_precise';eauto.
Qed.

(* APartArea *)
Lemma APartArea_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 vl vl' abs abs',
    (e, e0, M1, i, ier, l, o1, a) |= APartArea vl abs ->
    (e, e0, M2, i, ier, l, o2, a) |= APartArea vl' abs' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APartArea; intros.
  sep split in H;
  sep split in H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp1: APartArea'_precise' _H _H0; clear _H _H0.
  lets Hp2: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma APartArea_precise :
  forall M1 M2 o1 o2 e e0 i ier lo a vl vl' abs abs',
    (e, e0, M1, i, ier, lo, o1, a) |= APartArea vl abs   ->
    (e, e0, M2, i, ier, lo, o2, a) |= APartArea vl' abs' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply APartArea_precise';eauto.
Qed.

(* APartID2Dom *)
Lemma APartID2Dom_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= APartID2Dom vl ->
    (e, e0, M2, i, ier, l, o2, a) |= APartID2Dom vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold APartID2Dom; unfold GAarray; intros.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H25, H12; simpljoin1.
  rewrite H0 in H; inverts H.
  rewrite <- H1 in H4.
  unfold addrval_to_addr in H4; destruct x18, x11; inverts H4.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H3; auto.
  do 2 rewrite Int.repr_unsigned in H; substs.
  eapply Aarray_precise'; eauto.
Qed.

Lemma APartID2Dom_precise :
  forall M1 M2 o1 o2 e e0 i ier lo a vl vl',
    (e, e0, M1, i, ier, lo, o1, a) |= APartID2Dom vl   ->
    (e, e0, M2, i, ier, lo, o2, a) |= APartID2Dom vl' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply APartID2Dom_precise';eauto.
Qed.

Lemma ARootTaskStk'_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 rtsk_vll  rtsk_vll',
    (e, e0, M1, i, ier, l, o1, a) |= ARootTaskStk' rtsk_vll ->
    (e, e0, M2, i, ier, l, o2, a) |= ARootTaskStk' rtsk_vll' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
unfold ARootTaskStk'; intros.
sep destruct H;
sep destruct H0;
sep split in H;
sep split in H0.
simpl_sat H; simpl_sat H0; simpljoin1.
simpl in H15, H10; simpljoin1.
rewrite H25 in H15; inverts H15.
split; intros.
assert (x = x5 ).
eapply mapstoval_true_vptr_eq with (M:= M); eauto.
mem_join_sub_solver.
mem_join_sub_solver.
simpljoin.
lets Hp: Aarray_new_precise' H16 H11; auto.
destruct Hp as (Hm & Ho).
eapply eq_join_eq; eauto.
eapply Hm with (M:= M); try mem_join_sub_solver.
lets Hp: Aarray_new_precise' H16 H11; auto.
destruct Hp as (Hm & Ho).
eauto.
Qed.

Lemma ARootTaskStk_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 rtsk_vll  rtsk_vll' absrtsk absrtsk',
    (e, e0, M1, i, ier, l, o1, a) |= ARootTaskStk rtsk_vll absrtsk ->
    (e, e0, M2, i, ier, l, o2, a) |= ARootTaskStk rtsk_vll' absrtsk' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold ARootTaskStk; intros.
  sep destruct H;
  sep destruct H0;
  sep split in H;
  sep split in H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp: ARootTaskStk'_precise' _H _H0; clear _H _H0.
  lets Habslen: Aabsdata_precise' H H0; clear H H0.
  simpljoin.
  splits; intros.
  mem_eq_solver M.
  osabst_eq_solver o.
Qed.

Lemma AXMPFR_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AXMPFR ->
    (e, e0, M2, i, ier, l, o2, a) |= AXMPFR ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
unfold AXMPFR; intros.
sep destruct H;
sep destruct H0;
sep split in H;
sep split in H0.
simpl_sat H; simpl_sat H0; simpljoin1.
repeat try (match goal with H: _ |= PV _ @ _ |-> _ |- _ => simpl in H end).
simpl in *.
simpljoin1.
repeat  try (match goal with
 H: mapstoval (?b , _) _ _ _ _, H': mapstoval (?b , _) _ _ _ _ |- _ =>
 lets Heq: mapstoval_true_rule_type_val_match_eq M H H'; auto; clear H H';
 destruct Heq; try mem_join_sub_solver end).
simpljoin.
do 2 (match goal with H: Vint32 _ = Vint32 _ |- _ => inverts H end).
split;
eapply eq_join_eq; eauto.
Qed.

Lemma AMDMAER_precise :
  forall e e0 i ier l a M1 M2 o1 o2,
    (e, e0, M1, i, ier, l, o1, a) |= AMDMAER ->
    (e, e0, M2, i, ier, l, o2, a) |= AMDMAER ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
unfold AMDMAER; intros.
sep destruct H;
sep destruct H0;
sep split in H;
sep split in H0.
simpl_sat H; simpl_sat H0; simpljoin1.
repeat try (match goal with H: _ |= PV _ @ _ |-> _ |- _ => simpl in H end).
simpl in *.
simpljoin1.
(match goal with
 H: mapstoval (?b , _) _ _ _ _, H': mapstoval (?b , _) _ _ _ _ |- _ =>
 lets Heq: mapstoval_true_rule_type_val_match_eq M H H'; auto;
 destruct Heq; try auto end).
simpljoin.
(match goal with H: Vint32 _ = Vint32 _ |- _ => inverts H end).
auto.
Qed.

(* AOSPortAttrTbl' *)
Lemma AOSPortAttrTbl'_precise' :
  forall e e0 i ier l a M1 M2 o1 o2 vl vl',
    (e, e0, M1, i, ier, l, o1, a) |= AOSPortAttrTbl' vl ->
    (e, e0, M2, i, ier, l, o2, a) |= AOSPortAttrTbl' vl' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o : osabst,
       sub o1 o -> sub o2 o -> o1 = o2).
Proof.
  unfold AOSPortAttrTbl'; intros.
  sep normal in H;
  sep normal in H0;
  sep destruct H;
  sep destruct H0;
  sep split in H;
  sep split in H0.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  simpl in _H, _H0; simpljoin.
  match goal with H: get ?e ?id = _, H': get ?e ?id  = _ |- _ => rewrite H in H'; inverts H' end.
  split; intros.
  (match goal with
 H: mapstoval (?b , _) _ _ _ _, H': mapstoval (?b , _) _ _ _ _ |- _ =>
 lets Heq: mapstoval_true_vptr_eq M H H'; auto;
 destruct Heq; try auto end).
  mem_join_sub_solver.
  mem_join_sub_solver.
  simpljoin1.
  match goal with
  H: _ |= Aarray_new _ _ _ , H':  _ |= Aarray_new _ _ _ |- _ =>
  lets Hx1: Aarray_new_precise' H H'; eauto; simpljoin end.
  eapply eq_join_eq; eauto.
  mem_eq_solver M.
  match goal with
  H: _ |= Aarray_new _ _ _ , H':  _ |= Aarray_new _ _ _ |- _ =>
  eapply Aarray_new_osabst_emp in H,H' end.
  simpljoin1.
Qed.

Lemma AOSPortAttrTbl'_precise :
  forall v v' M1 M2 o1 o2 e e0 i ier lo a,
    (e, e0, M1, i, ier, lo, o1, a) |= AOSPortAttrTbl' v   ->
    (e, e0, M2, i, ier, lo, o2, a) |= AOSPortAttrTbl' v' ->
    (forall (M : mem) ( o : osabst),
       sub M1 M -> sub M2 M -> 
       sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).     
Proof.
  intros.
  eapply precise'2precise;eauto.
  eapply AOSPortAttrTbl'_precise';eauto.
Qed.

(* end add by CNU *)
Require Import partinv_lemmas.

Lemma PartitionInv_precise1:
  forall e e0 i ier l a M1 M2 o1 o2 ecbls ecbls', 
    (e, e0, M1, i, ier, l, o1, a) |= PartitionInv_part1 ecbls->
    (e, e0, M2, i, ier, l, o2, a) |= PartitionInv_part1 ecbls'->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold PartitionInv_part1 in *.
  do  23 destruct H, H0.
  sep split in H.
  sep split in H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx1: AOSDomainPortPtrList_precise _H _H0; clear _H _H0.

  assert (x45 = x49 /\ x47 = x51 /\ x0 = x /\ x2 = x1) as Hx1'.
  { eapply (Hx1 M o);mem_join_sub_solver. }
  destruct Hx1' as [ ? [? [? ?]]]; subst; clear Hx1.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx2: Hdomainportl_precise_eq _H _H0; clear _H _H0.
  assert (x0 = x53 /\ x45 = x55 /\ x17 = x18) as Hx2'.
  { eapply (Hx2 M o);mem_join_sub_solver. }
  destruct Hx2' as [? [? ?]]; subst; clear Hx2.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx3: AOSKernelPortIDTbl_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx4: Aabsdata_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx5: AOSChannelIDTbl_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx6: Aabsdata_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx7: AOSKernelPortFreeList_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx8: AOSChannelFreeList_precise _H _H0; clear _H _H0.

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx9: OtherPortPtrList_precise _H _H0; clear _H _H0.
  { eapply OtherPortPtrList_perm; eauto.
    instantiate (1:=x14).
    instantiate (1:=x12).
    assert (x5 = x6); [ |subst].
    { eapply dportls1_eq; eauto. }
    pose proof map_join_cancel H5 H15.
    subst; auto. }

  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
  lets Hx10: Aabsdata_precise _H _H0; clear _H _H0.

  lets Hx11: AOSCorePortPtrList_precise H H0; clear H H0.

  repeat match goal with 
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end. 
  auto.
Qed.

Lemma PartitionInv_precise2: 
  forall e e0 i ier l a M1 M2 o1 o2, 
    (e, e0, M1, i, ier, l, o1, a) |= PartitionInv_part2 ->
    (e, e0, M2, i, ier, l, o2, a) |= PartitionInv_part2 ->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  introv Hsat1 Hsat2 Hsubm1 Hsubm2 Hsubo1 Hsubo2.
  unfold PartitionInv_part2 in Hsat1, Hsat2.
  sep destruct Hsat1.
  sep destruct Hsat2.
  sep split in Hsat1.
  sep split in Hsat2.
  substs.
  clear H H0.
  rename Hsat1 into H.
  rename Hsat2 into H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hrtsk: ARootTaskStk_precise' _H _H0; clear _H _H0.
  lets Hrtsk': precise'2precise Hrtsk.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hmpax: AMPAXs_precise' _H _H0; clear _H _H0.
  lets Hmpax': precise'2precise Hmpax.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hxmpfr: AXMPFR_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hmdma: AMDMAER_precise _H _H0; clear _H _H0.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hucos: AucosConf_precise' _H _H0; clear _H _H0.
  lets Hucos': precise'2precise Hucos.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habsucos: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habsucos': precise'2precise Habsucos.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hdom2: Adomain2index_precise' _H _H0; clear _H _H0.
  lets Hdom2': precise'2precise Hdom2.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hdscdidx: AKsDSchdidx_precise' _H _H0; clear _H _H0.
  lets Hdscdidx': precise'2precise Hdscdidx.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habsidx: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habsidx': precise'2precise Habsidx.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hdscdlen: AKsDSchdlen_precise' _H _H0; clear _H _H0.
  lets Hdscdlen': precise'2precise Hdscdlen.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habslen: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habslen': precise'2precise Habslen.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hcurd: AKsCurDomain_precise' _H _H0; clear _H _H0.
  lets Hcurd': precise'2precise Hcurd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habscurd: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habscurd': precise'2precise Habscurd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hlastd: AKsLastDomain_precise' _H _H0; clear _H _H0.
  lets Hlastd': precise'2precise Hlastd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habslastd: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habslastd': precise'2precise Habslastd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hdomt: AKsDomainTime_precise' _H _H0; clear _H _H0.
  lets Hdomt': precise'2precise Hdomt.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habsdomt: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habsdomt': precise'2precise Habsdomt.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hdomscd: AKsDomSchedule_precise' _H _H0; clear _H _H0.
  lets Hdomscd': precise'2precise Hdomscd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hiscp: AisChangePartion_precise' _H _H0; clear _H _H0.
  lets Hiscp': precise'2precise Hiscp.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hintp: AIntPartMux_precise' _H _H0; clear _H _H0.
  lets Hintp': precise'2precise Hintp.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hksd: AKsDomains_precise' _H _H0; clear _H _H0.
  lets Hksd': precise'2precise Hksd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Habsksd: Aabsdata_precise' _H _H0; clear _H _H0.
  lets Habsksd': precise'2precise Habsksd.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hiscb: AisCoreBoot_precise' _H _H0; clear _H _H0.
  lets Hiscb': precise'2precise Hiscb.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hstck: AsystemStck'_precise' _H _H0; clear _H _H0.
  lets Hstck': precise'2precise Hstck.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hossp: AOSSystemSP_precise' _H _H0; clear _H _H0.
  lets Hossp': precise'2precise Hossp.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hcpn: ACorepartnum_precise _H _H0; clear _H _H0.
(*   lets Hcpn': precise'2precise Hcpn. *)
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hpnc: APortnumcur_precise' _H _H0; clear _H _H0.
  lets Hpnc': precise'2precise Hpnc.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hpta: APartArea_precise' _H _H0; clear _H _H0.
  lets Hpta': precise'2precise Hpta.
  elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
  lets Hp2d: APartID2Dom_precise' _H _H0; clear _H _H0.
  lets Hp2d': precise'2precise Hp2d.
  rename H into _H. rename H0 into _H0.
  lets Hport: AOSPortAttrTbl'_precise' _H _H0; clear _H _H0.
  lets Hport': precise'2precise Hport.
  simpljoin.

  repeat match goal with
  | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
    |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
    apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
    end.
    repeat match goal with 
  | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
    |- _ => assert (m1 = m2);[jeat | ]; subst m1 
    end.
  auto.
Qed.

Lemma PartitionInv_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 ecbls ecbls', 
    (e, e0, M1, i, ier, l, o1, a) |= PartitionInv ecbls->
    (e, e0, M2, i, ier, l, o2, a) |= PartitionInv ecbls'->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
introv Hsat1 Hsat2 Hsubm1 Hsubm2 Hsubo1 Hsubo2.
erewrite PartitionInv_eq in Hsat1, Hsat2.
rename Hsat1 into H.
rename Hsat2 into H0.
elim_sep_conj1 H _H. elim_sep_conj1 H0 _H0.
lets Hx: PartitionInv_precise1 _H _H0; clear _H _H0.
rename H into _H. rename H0 into _H0.
lets Hy: PartitionInv_precise2 _H _H0; clear _H _H0.
repeat match goal with
| Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
  |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
  apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
  end.
  repeat match goal with 
| H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
  |- _ => assert (m1 = m2);[jeat | ]; subst m1 
  end.
auto.
Qed.

(* CapabilityInv precise  *)
Lemma ACSpaceAarrayTptr_succ_imp_help:
  forall s a vll n  p ptrvl2 cspacels, 
  s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels->
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels ** ACSpaceAarrayTptr  n ptrvl2 vll cspacels.
    
Proof.
  intros.
  sep pauto.
  simpl ACSpaceAarrayTptr in *.
  destruct p. simpl in H. tryfalse.
  sep auto.
  simpl in H. tryfalse.
  sep auto.
Qed.


Lemma ASlots_precise:
  forall   vl vl' n add M1 M2 o1 o2 e e0 i ier l a, 
  (e, e0, M1, i, ier, l, o1, a) |= ASlots add n vl ->
  (e, e0, M2, i, ier, l, o2, a) |= ASlots add n vl' ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction vl; destruct vl'; destruct n; intros.
  simpl in H, H0. simpljoin. unfolds in H6. unfolds in H5.
  substs. auto.
  simpl in H. tryfalse.
  simpl in H0. destruct p. tryfalse.
  simpl in H. tryfalse.
  simpl in H. destruct a. tryfalse.
  simpl in H0. tryfalse.
  simpl in H0. destruct p. tryfalse.
  unfold ASlots in H.  destruct a, add. 
  fold ASlots in H. 
  unfold ASlots in H0. destruct p. 
  fold ASlots in H0. 
  unfold ACap in *.
  destruct p0, c, p0.
  destruct p, c, p. 
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H40, H8. simpljoin1.
  assert(x5 = x).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x5.
  simpl in H50, H18. simpljoin1.
  assert(x17 = x47).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x47.
  assert(x53 = x23).
  simpl in H23, H55. simpljoin.
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x53.
  assert(x59 = x29).
  simpl in H60, H28. simpljoin. 
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x59.
  
  assert(x60 = x30).
  simpl in H65, H33. simpljoin. 
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x60.
  lets Hy: IHvl H14.
  eauto.
  split. 
  assert(x42 = x12 /\ x45 = x15).
  eapply Hy with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin. 
  join auto.
  simpl in *.
  simpljoin.
  unfold emposabst in *. substs.
  simpljoin.
  assert(x42 = x12 /\ x45 = x15).
  eapply Hy with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin. join auto.
Qed.

Lemma Acnode_precise:
  forall add c1 c2 M1 M2 o1 o2 e e0 i ier l a, 
  (e, e0, M1, i, ier, l, o1, a) |= Acnode add c1 ->
  (e, e0, M2, i, ier, l, o2, a) |= Acnode add c2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof. 
  intros. unfold Acnode in *.
  destruct c1, p, add. 
  destruct c2, p. 
  sep split in H. 
  simpl_sat H; simpl_sat H0; simpljoin.
  
  simpl in H9, H26. simpljoin.
  assert(x = x5).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x5.
  simpl in H14, H31. simpljoin.
  assert(x11 = x23). 
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x23.
  lets Hx: ASlots_precise H19 H32.
  assert(x17 = x24 /\ x20 = x27).
  eapply Hx with(M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin. join auto.
Qed.



Lemma ACSpace_precise :
forall add c1 x1 c2 x2 M1 M2 o1 o2 e e0 i ier l a,
  (e, e0, M1, i, ier, l, o1, a) |= ACSpace add c1 x1 ->
  (e, e0, M2, i, ier, l, o2, a) |= ACSpace add c2 x2 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  intros.
  unfold ACSpace in *.
  destruct c1. destruct p. destruct p. destruct p.  destruct add.
  destruct c2. destruct p. destruct p. destruct p.
  sep split in H. sep split in H0. 
  simpl_sat H; simpl_sat H0; simpljoin1.
  lets Hx: Acnode_precise H37 H16.
  assert(x7 = x /\ x10 = x4).
  eapply Hx with(M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin.
  clear Hx.
  clear H16 H37. 
  lets Hx: Aarray_precise H26 H47.
  assert(x19 = x37 /\ x22 = x40).
  eapply Hx with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin.
  clear H26 H47.
  simpl in H42, H52, H53, H21, H31, H32.
  simpljoin.
  assert(x13 = x31).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x31.
  unfold emposabst in *. subst.
  
  assert(x43 = x25).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x43.
  assert(x44 = x26).
  eapply mapstoval_true_mem_eq with (M:=M); eauto; mem_join_sub_solver.
  subst x44.
  join auto. 
Qed.

Lemma ACSpaceAarrayTptr_precise :
forall x1 x2 x3 x5 x6 n M1 M2 o1 o2 e e0 i ier l a,

  (e, e0, M1, i, ier, l, o1, a) |= ACSpaceAarrayTptr n x1 x2 x3 ->
  (e, e0, M2, i, ier, l, o2, a) |= ACSpaceAarrayTptr n x1 x5 x6 ->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  induction x1; destruct x2; destruct x5; destruct n;intros.
  simpl in H. simpl in H0. simpljoin. unfold emposabst in H5, H6. subst o1. auto.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H0. destruct a; tryfalse.
  simpl in H. tryfalse.
  simpl in H0. destruct a; tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse. simpl in H. tryfalse.
  simpl in H. tryfalse.
  destruct a; tryfalse.
  simpl in H. destruct a; tryfalse.
  simpl in H. destruct a; tryfalse.
  simpl in H. destruct a; tryfalse.
  simpl in H0. simpl in H. destruct a; tryfalse.
  simpl in H0. tryfalse.
  simpl in H. 
  destruct a; tryfalse.
  lets Hx: IHx1 H H0. 
  eapply Hx; eauto. 
  simpl_sat H; simpl_sat H0; simpljoin.
  lets Hx: ACSpace_precise H13 H8.
  assert(x10 = x /\ x13 = x7).
  eapply Hx with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin.
  clear Hx.
  lets Hx: IHx1 H14 H9.
  assert(x11 = x0 /\ x14 = x8).
  eapply Hx with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin.  join auto. 
Qed.

Lemma gvar_ptr_precise_ext :
  forall m1 m2 v1 v2 e e0 i ier l o1 o2 a t, 
    (e, e0, m1, i, ier, l, o1, a) |= G& ios_cap_defs.OSCSpacePrioTbl @ t == v1 ->  
    (e, e0, m2, i, ier, l, o2, a) |= G& ios_cap_defs.OSCSpacePrioTbl @ t == v2 ->
    v1 = v2. 
Proof.
  intros.
  simpl in H. simpl in H0. 
  simpljoin1.
  rewrite H in H0. inverts H0.
  unfolds in H4.
  destruct v1.
  unfolds in H1.
  destruct v2. rewrite <- H4 in H1.
  inverts H1.
  assert(Int.repr(Int.unsigned i1) = Int.repr(Int.unsigned i0)).
  rewrite H3. 
  auto. 
  do 2 rewrite Int.repr_unsigned in H0. 
  subst i1. auto.   
Qed.

Lemma  AOSCSpacePrioTbl_precise :
forall x1 x2 x3 x4 x5 x6 x7 x8 M1 M2 o1 o2 e e0 i ier l a,
array_type_vallist_match (Tptr ios_cap_defs.CSPACE) x2 ->
array_type_vallist_match (Tptr ios_cap_defs.CSPACE) x6 ->
  (e, e0, M1, i, ier, l, o1, a) |= AOSCSpacePrioTbl x1 x2 x3 x4 ->
  (e, e0, M2, i, ier, l, o2, a) |= AOSCSpacePrioTbl x5 x6 x7 x8 ->
  
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2 ).      
Proof.
  introv Hptr1 Hptr2.
  intros.
  unfold AOSCSpacePrioTbl in *.
  sep split in H. sep split in H0.
  clear H5 H6.
  eapply sat_star in H. eapply sat_star in H0.
  simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.
  simpl substmo in H0; simpl getmem in H0; simpl getabst in H0; simpl empst in H0.
  simpljoin1.
  assert(x1 = x5).
  simpl in H8, H13. simpljoin1.
  rewrite H in H0. inverts H0.
  rewrite <- H6 in H13.
  unfold addrval_to_addr in H13; destruct x1, x5; inverts H13.
  assert(Int.repr (Int.unsigned i1) = Int.repr (Int.unsigned i0)).
  rewrite H7; auto.
  do 2 rewrite Int.repr_unsigned in H0; substs.
  eapply sat_star in H9. eapply sat_star in H14.
  simpl substmo in H9; simpl getmem in H9; simpl getabst in H9; simpl empst in H9.
  simpl substmo in H14; simpl getmem in H14; simpl getabst in H14; simpl empst in H14.
  simpljoin1.
  lets Hx: gvar_ptr_precise_ext H8 H13.
  simpljoin1.
  eapply sat_star in H9. eapply sat_star in H14.
  simpl substmo in H9; simpl getmem in H9; simpl getabst in H9; simpl empst in H9.
  simpl substmo in H14; simpl getmem in H14; simpl getabst in H14; simpl empst in H14.
  simpljoin1.
  assert(x2 = x6).
  eapply Aarray'_vl_eq with(M:=M); eauto.
  mem_join_sub_solver. mem_join_sub_solver.
  subst x6.
  lets Hx: Aarray_precise H14 H19.
  assert(x1 = x20 /\ x15 = x23).
  eapply Hx with (M:=M)(o:=o).
  mem_join_sub_solver. mem_join_sub_solver.
  mem_join_sub_solver. mem_join_sub_solver.
  simpljoin. 
  clear Hx.
  lets Hx: ACSpaceAarrayTptr_precise H15 H20.
  assert(x9 = x21 /\ x18 = x24).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  clear Hx.
  simpl in H8, H13.
  simpljoin.
  rewrite H in H0. inverts H0. 
  unfold emposabst in *. simpljoin.
  join auto. 
Qed.


Lemma AOSCSpaceObjectPointer_precise:
  forall e e0 i ier l a M1 M2 o1 o2 l1 l2,
  (e, e0, M1, i, ier, l, o1, a) |= AOSCSpaceObjectPointer l1->
  (e, e0, M2, i, ier, l, o2, a) |= AOSCSpaceObjectPointer l2->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold AOSCSpaceObjectPointer in *.
  unfold GAarray in *.
  simpl_sat H; simpl_sat H0; simpljoin1.
  simpl in H17, H31.
  simpljoin. 
  assert(x18 = x11).
  rewrite H0 in H. 
  inverts H. 
  rewrite <- H8 in H5.
  clear -H5.
  unfolds in H5.
  destruct x11, x18. inverts H5.
  assert(Int.repr(Int.unsigned i) = Int.repr(Int.unsigned i0)).
  rewrite H1. auto. 
  rewrite Int.repr_unsigned in H. 
  rewrite Int.repr_unsigned in H. subst i. auto. 
  subst x18.
  lets Hx: Aarray_precise H32 H18.
  assert(x20 = x13 /\ x23 = x16).
  eapply Hx with (M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  join auto. 
Qed.

Lemma AOSCSpaceCapParent_precise:
  forall e e0 i ier l a M1 M2 o1 o2 l1 l2,
  (e, e0, M1, i, ier, l, o1, a) |= AOSCSpaceCapParent l1->
  (e, e0, M2, i, ier, l, o2, a) |= AOSCSpaceCapParent l2->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold AOSCSpaceCapParent in *.
  sep split in H. sep split in H0.
  unfold GAarray in *.
  simpl_sat H; simpl_sat H0; simpljoin.
  simpl in H17, H10. simpljoin.
  unfold emposabst in *.
  substs.
  assert(x = x6).
  rewrite H in H0. inverts H0. 
  rewrite <- H17 in H8.
  destruct x. destruct x6.
  unfold addrval_to_addr in H8.
  inverts H8.
  eapply int_auto.unsigned_inj in H15.
  substs. auto. 
  subst x6.
  lets Hx: Aarray_precise H18 H11.
  assert(x8 = x1 /\ x11 = x4).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  join auto.
Qed.




Lemma CSpaceGVars_precise:
  forall e e0 i ier l a M1 M2 o1 o2,
  (e, e0, M1, i, ier, l, o1, a) |= CSpaceGVars->
  (e, e0, M2, i, ier, l, o2, a) |= CSpaceGVars->
  (forall (M : mem) (o : osabst),
      sub M1 M -> sub M2 M -> 
      sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  unfold CSpaceGVars.
  intros.
  simpl_sat H; simpl_sat H0; simpljoin.
  simpl in H8, H18. simpljoin. 
  simpl in H13, H23. simpljoin. 
  simpl in H14, H24. simpljoin.
  rewrite H29 in H11. inverts H11.
  assert(x9 = x30).
  eapply mapstoval_true_mem_eq with(M:=M); eauto. 
  mem_join_sub_solver. mem_join_sub_solver.
  subst x30.
  rewrite H39 in H21. inverts H21.
  assert(x12 = x38).
  eapply mapstoval_true_mem_eq with(M:=M); eauto. 
  mem_join_sub_solver. mem_join_sub_solver.
  subst x38.
  rewrite H49 in H32. inverts H32.
  assert(x24 = x46).
  eapply mapstoval_true_mem_eq with(M:=M); eauto. 
  mem_join_sub_solver. mem_join_sub_solver.
  subst x46.
  unfold emposabst in *.  substs.
  join auto.
Qed.

Lemma CapabilityInv_precise: 
  forall e e0 i ier l a M1 M2 o1 o2 acspace acspace' ,
    (e, e0, M1, i, ier, l, o1, a) |= CapabilityInv acspace->
    (e, e0, M2, i, ier, l, o2, a) |= CapabilityInv acspace'->
    (forall (M : mem) (o : osabst),
        sub M1 M -> sub M2 M -> 
        sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).
Proof.
  intros.
  unfold CapabilityInv in *.
  sep destruct H. sep destruct H0.
  sep split in H. sep split in H0.
  destruct H, H0. simpljoin.
  destruct H23, H28. simpljoin.
  destruct H29, H34. simpljoin.
  destruct H35, H40. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  lets Hx: AOSCSpacePrioTbl_precise H22 H27.
  unfold AOSCSpacePrioTbl in *.
  sep split in H22. sep split in H27.
  simpljoin. auto. 
  unfold AOSCSpacePrioTbl in *.
  sep split in H22. sep split in H27.
  simpljoin. auto. 
  assert(x12 = x11 /\ x15 = x20).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  clear Hx. 
  lets Hx: AOSCSpaceObjectPointer_precise H28 H33.
  assert(x14 = x17 /\ x23 = x28).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  clear Hx.
  lets Hx: AOSCSpaceCapParent_precise H34 H39.
  assert(x22 = x25 /\ x31 = x36).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  clear Hx.
  lets Hx: CSpaceGVars_precise H40  H45.
  assert(x30 = x33 /\ x39 = x44).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  clear Hx.
  lets Hx: Aabsdata_precise H41 H46.
  assert(x35 = x42 /\ x40 = x45).
  eapply Hx with(M:=M)(o:=o); mem_join_sub_solver.
  simpljoin.
  join auto.
Qed.


(*main lemmas*)
Lemma OSInv_precise : precise OSInv.
Proof.
  unfold precise; intros.
  destruct s; destruct r; destruct t; destruct p; destruct p;
  destruct s; destruct p; simpl substmo in *.
  unfold OSInv in *.
  do 21 destruct H, H0.
  sep remember (4::5::13::nil)%nat in H.
    sep remember (4::5::13::nil)%nat in H0.
  sep remember (4::nil)%nat in H;
    sep remember (4::nil)%nat in H0.
  simpl in H, H0; simpljoin1.
  assert (
      forall (M: mem) (o0 : osabst),
        sub x47 M -> sub x41 M -> sub x50 o0 -> sub x44 o0 ->  
        x47 = x41 /\ x50 = x44
    ).
   {
    clear H18 H13.
    rename H17 into H; rename H12 into H0.

    intros.

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx1: AOSMapTbl_precise _H _H0; clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx2: AOSUnMapTbl_precise _H _H0; clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx3: AOSTCBPrioTbl_precise _H _H0; clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx4: AOSRdyTblGrp_precise _H _H0; clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx5: AOSTime_precise _H _H0; clear _H _H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx6: Aabsdata_precise _H _H0; clear _H _H0. (* HTCBList *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx7: Aabsdata_precise _H _H0; clear _H _H0. (* HTime *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx8: Aabsdata_precise _H _H0; clear _H _H0. (* HCurTCB *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx9: AGVars_precise _H _H0; clear _H _H0.
    sep split in H; sep split in H0.
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    unfold APthreadAttr in *.
    sep normal in H0.
    sep normal in H.

    lets Hx10: Aabsdata_precise _H _H0; clear _H _H0.  (*add*)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx11: A_isr_is_prop_precise _H _H0; clear _H _H0.

    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx12: IntInv_precise _H _H0; clear _H _H0. (* IntInv *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx13: TmrInv_precise _H _H0; clear _H _H0. (* TmrInv *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx14: CoreCommuInv_precise _H _H0. clear _H _H0. (* CoreCommuInv *)
    elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.
    lets Hx15: PartitionInv_precise _H _H0; clear _H _H0. (* PartitionInv *)
    lets Hx16: CapabilityInv_precise H H0. clear H H0. (* CapabilityInv *)

    repeat match goal with 
           | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
             |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
                           apply (Hx M0 o3);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
           end. 
    repeat match goal with 
           | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
             |- _ => assert (m1 = m2);[jeat | ]; subst m1 
           end.
    auto.
  }

  clear H17 H12. 

  assert (x22 = x21).
  {
    simpl_sat H18; simpl_sat H13; simpljoin1.
    eapply AOSTCBList'_ct_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  substs.

  sep normal in H18. sep destruct H18.
  sep normal in H13. sep destruct H13.
  rename H into H_prec0.

  rename H18 into H. rename H13 into H0.
  elim_sep_conj1 H H_. elim_sep_conj1 H0 H0_.
  assert (H18:=H). assert (H13:=H0).
  elim_sep_conj1 H H'_. elim_sep_conj1 H0 H0'_.

  assert (x25 = x26).
  {
    eapply AOSTCBFreeList'_pfree_eq with (M := M); eauto.
    mem_join_sub_solver.
    mem_join_sub_solver.
  }
  subst.

  (* the two pieces of mems for AOSTCBList' are the same *)
  assert (Hmoeq: x22 = x52 /\ x46 = x54).
  {
    lets H00: AOSTCBList'_precise H_ H0_.
    apply (H00 M o); mem_join_sub_solver.
  }
  destruct Hmoeq; subst.
  lets Htcbheq: AOSTCBList'_tcb_list_same_head H_ H0_.
  subst.
  lets Htcblsamenxt: AOSTCBList'_tcb_list_same_next_intro' H_ H0_.

  lets Hxfreelst: AOSTCBFreeList'_precise H'_ H0'_. 
  lets Hxlst: AOSTCBList'_precise H_ H0_.

  lets Hxevts: EvtInv_precise H H0 Htcblsamenxt; clear H H0 Htcblsamenxt.

  repeat match goal with 
         | Hx: forall _ _, sub ?x1 _ -> sub ?x2 _ -> sub ?y1 _ -> sub ?y2 _ -> ?x1 = ?x2 /\ ?y1 = ?y2 
            |- _ => let h:=fresh "H" in assert (x1 = x2 /\ y1 = y2) as h;[
                           apply (Hx M o);mem_join_sub_solver | ];destruct h; subst x1 y1;clear Hx
         end.
  repeat match goal with 
         | H: join ?a ?b ?m1, H1: join ?a ?b ?m2 
           |- _ => assert (m1 = m2);[jeat | ]; subst m1 
         end.
  auto.
Qed. 

(*----is isr irrelvant lemmas----*)
Ltac destr_and_inst H v:= let s := fresh v in (destruct H as [s H]; exists s).

Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Ltac cancel_pure H := sep split in H; sep split; auto.

Ltac solve_sat H := simpl_sat H; simpl_sat_goal; simpljoin1; do 6 eexists; repeat(split; eauto); eauto.

Ltac get_isr_is_prop H := unfold OSInv in H; simpljoin1; sep destruct H; seplog_trm_tacs.sep_lifts_trms_in H A_isr_is_prop; sep remember (1::nil)%nat in H; simpl in H; simpljoin1.
(* Ltac get_isr_is_prop H := unfold OSInv in H; simpljoin1; do 20 destruct H; sep remember (18::nil)%nat in H; simpl in H; simpljoin1. *)

Ltac solve_sat_auto :=
  match goal with
    | H: _ |= ?P ** ?Q |- _ => sep remember (1::nil)%nat in H; solve_sat H; solve_sat_auto
    | _ => idtac
  end.

Lemma is_isr_irrel_Astruct' :
  forall vl l d a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Astruct' l d vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Astruct' l d vl.
Proof.
  inductions vl; intros.
  destruct d; simpl in H; simpl; auto.
  
  destruct d; simpl in H; tryfalse.
          
  destruct t; destruct l;
  try solve [
        simpl in H; simpl; simpljoin1;
        do 6 eexists; repeat(split; eauto);
        apply OSAbstMod.join_emp; auto;
        eapply IHvl];
  try solve [
        simpl; eapply IHvl; eauto].
Qed.

Lemma is_isr_irrel_Astruct :
  forall vl l t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Astruct l t vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Astruct l t vl.
Proof.
  unfold Astruct; intros; destruct t; tryfalse.
  eapply is_isr_irrel_Astruct'; eauto.
  eapply is_isr_irrel_Astruct'; eauto.
Qed.

Lemma is_isr_irrel_node :
  forall vl v t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= node v vl t ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= node v vl t.
Proof.
  unfold node; intros.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  
  eapply is_isr_irrel_Astruct; eauto.
Qed.

Lemma is_isr_irrel_Aarray' :
  forall vl l n t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Aarray' l n t vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Aarray' l n t vl.
Proof.
  inductions vl; destruct n; intros.
  simpl in H; simpl;auto.
  simpl in H; tryfalse.
  
  simpl in H; tryfalse.
  simpl in H; destruct l; simpl.
  simpl in H; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  apply OSAbstMod.join_emp; auto.
Qed.

Lemma is_isr_irrel_Aarray :
  forall vl l t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Aarray l t vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Aarray l t vl.
Proof.
  unfold Aarray; intros.
  destruct t; tryfalse.
  eapply is_isr_irrel_Aarray'; eauto.
Qed.

Lemma is_isr_irrel_sllseg :
  forall l head tail t next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= sllseg head tail l t next ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= sllseg head tail l t next.
Proof.
  inductions l; intros.
  simpl in H; simpl; simpljoin1; splits; auto.
  unfolds; auto.
  
  unfold sllseg in H; fold sllseg in H.
  unfold sllseg; fold sllseg.
  sep split in H; sep split; auto.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_node; eauto.
Qed.

Lemma is_isr_irrel_sll :
  forall l head t next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= sll head l t next ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= sll head l t next.
Proof.
  unfold sll; intros.      
  eapply is_isr_irrel_sllseg; eauto.
Qed.

Lemma is_isr_AOSEvent :
  forall v osevent etbl petbl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSEvent v osevent etbl petbl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSEvent v osevent etbl petbl.
Proof.
  unfold AOSEvent; intros.
  do 4 destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  eapply is_isr_irrel_node; eauto.
  
  do 6 eexists; repeat (split; eauto).
  unfold AOSEventTbl in *.
  sep split in H14; sep split; auto.
  eapply is_isr_irrel_Aarray; eauto.
  
  unfold AOSPostEventTbl in *.
  sep split in H15; sep split; auto.
  eapply is_isr_irrel_Aarray; eauto.
Qed. 

Lemma is_isr_AEventData :
  forall osevent d a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEventData osevent d ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEventData osevent d.
Proof.
  unfold AEventData; intros.
  destruct d; try (sep split in H; sep split; auto).
  unfold AMsgData in *.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  clear - H.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H3.
  unfold AOSQCtr in *.
  sep split in H3; sep split; auto.
  eapply is_isr_irrel_node; eauto.
  clear - H4.
  unfold AOSQBlk in *.
  destr_and_inst H4 v.
  sep split in H4; sep split; auto.
  simpl_sat H4; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  eapply is_isr_irrel_node; eauto.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma is_isr_AEventNode :
  forall v osevent etbl petbl d a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEventNode v osevent etbl petbl d ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEventNode v osevent etbl petbl d.
Proof.
  unfold AEventNode in *; intros.
  simpl_sat H; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat (split; eauto).
  clear - H3.
  
  eapply is_isr_AOSEvent; eauto.
  clear - H4.
  eapply is_isr_AEventData; eauto.
Qed.

Lemma is_isr_qblkf_evsllseg :
  forall vl head tail ecbls a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= evsllseg head tail vl ecbls  ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= evsllseg head tail vl ecbls.
Proof.
  inductions vl; intros.
  simpl in H; simpl; simpljoin1.
  splits; eauto.
  unfolds; auto.
  
  unfold evsllseg in H; fold evsllseg in H.
  unfold evsllseg; fold evsllseg.
  destruct ecbls; tryfalse; destruct a. destruct p.
  destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  clear - H4.
  
  eapply is_isr_AEventNode; eauto.
Qed. 

Lemma is_isr_dllseg :
  forall l head headprev tail tailnext t prev next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= dllseg head headprev tail tailnext l t prev next->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= dllseg head headprev tail tailnext l t prev next.
Proof.
  inductions l; intros.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; auto.
  unfolds; auto.

  unfold dllseg in H; fold dllseg in H.
  unfold dllseg; fold dllseg.
  sep split in H; sep split; auto.
  destr_and_inst H v.
  cancel_pure H.

  solve_sat H.
  eapply is_isr_irrel_node; eauto.
Qed.

Lemma is_isr_tcbdllseg :
  forall head headprev tail tailnext l a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= tcbdllseg head headprev tail tailnext l->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= tcbdllseg head headprev tail tailnext l.
Proof.
  unfold tcbdllseg; intros.
  eapply is_isr_dllseg; eauto.
Qed.

Lemma is_isr_qblkf_sllseg :
  forall l head tailnext t next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= qblkf_sllseg head tailnext l t next  ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= qblkf_sllseg head tailnext l t next.
Proof.
  inductions l; intros.
  simpl in H; simpl; simpljoin1.
  splits; eauto.
  unfolds; auto.

  unfold qblkf_sllseg in H; fold qblkf_sllseg in H.
  unfold qblkf_sllseg; fold qblkf_sllseg.
  do 3 destr_and_inst H v.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_node; eauto.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
Qed.
(*--end--*)

Lemma is_isr_sllsegfreeflag :
  forall l head tailnext next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= sllsegfreeflag head tailnext l next->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= sllsegfreeflag head tailnext l next.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  simpl.
  unfold emposabst; auto.

  unfold sllsegfreeflag in *; fold sllsegfreeflag in *.
  sep destruct H.
  exists x0 x1 x2 x3 x4 x5.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl. 
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
Qed.

Lemma is_isr_sllfreeflag :
  forall head l a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= sllfreeflag head l->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= sllfreeflag head l.
Proof.
  intros.
  unfold sllfreeflag in *.
  eapply is_isr_sllsegfreeflag; eauto.
Qed.

Lemma is_isr_dllsegflag :
  forall l head tailnext next a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= dllsegflag head tailnext l next->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= dllsegflag head tailnext l next.
Proof.
  inductions l; intros.
  simpl in H; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst; auto.
  unfolds; auto.

  unfold dllsegflag in *; fold dllsegflag in *.
  do 2 destruct H.
  exists x0 x1.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
Qed.

Lemma is_isr_tcbdllflag :
  forall head l a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= tcbdllflag head l->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= tcbdllflag head l.
Proof.
  intros.
  unfold tcbdllflag in *.
  eapply is_isr_dllsegflag; eauto.
Qed.

(*  is isr irrelvant lemmas about EvtInv *)

Lemma is_isr_irrel_Aarray_new' :
  forall vl l n t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Aarray_new' l n t vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Aarray_new' l n t vl.
Proof.
  inductions vl; destruct n; intros.
  simpl in H; simpl;auto.
  simpl in H; tryfalse.
  
  simpl in H; tryfalse.
  simpl in H. destruct t; destruct a ; tryfalse;
  try (destruct a;tryfalse; destruct l; simpl;  simpl in H; simpljoin1;
          do 6 eexists; repeat (split; eauto);  apply OSAbstMod.join_emp; auto).

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Aarray'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Aarray'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.
  
  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.

  destruct l. simpl.  simpl in H. simpljoin1. 
  do 6 eexists; repeat (split; eauto).  eapply is_isr_irrel_Astruct'; eauto.
Qed.

Lemma is_isr_irrel_Aarray_new :
  forall vl l t a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Aarray_new l t vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Aarray_new l t vl.
Proof.
  intros.
  unfold Aarray_new in *.
  destruct t; tryfalse.
  eapply is_isr_irrel_Aarray_new'. apply H.
Qed.

Lemma is_isr_ASeminfo :
  forall l head a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= ASeminfo l head ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= ASeminfo l head .
Proof.
  intros.
  unfold ASeminfo in *.
  do 2 destr_and_inst H head.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 5 eexists; repeat (split; eauto). 
  do 6 eexists. split; eauto. split; eauto. apply join_comm.
  apply join_emp. eauto. 
  split. eauto. split. apply join_comm . apply join_emp. eauto. 
  split. eapply is_isr_irrel_Aarray_new. eauto.
  split; eauto.
  simpl. split; eauto. unfold emposabst. auto.
Qed.

Lemma is_isr_APthreadMutex:
  forall a b c ir ir' ier ier' ie0 si si' cs0 x aop l minfol ,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= APthreadMutex l minfol ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= APthreadMutex l minfol .
Proof. 
  intros.
  unfold APthreadMutex in *.
  do 2 destr_and_inst H minfol .
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 5 eexists; repeat (split; eauto). 
  do 6 eexists. split; eauto. split; eauto. apply join_comm . 
  apply join_emp.  eauto. split. eauto. split. apply join_comm . apply join_emp. eauto. 
  split. eapply is_isr_irrel_Aarray_new. eauto.
  split; eauto.
  simpl. split; eauto. unfold emposabst. auto.
Qed.

Lemma is_isr_AMqAttr:
  forall a b c ir ir' ier ier' ie0 si si' cs0 x aop l qattr,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AMqAttr l qattr ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AMqAttr l qattr .
Proof. 
  intros.
  unfold AMqAttr in *.
  do 2 destr_and_inst H minfol .
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 5 eexists; repeat (split; eauto). 
  do 6 eexists. split; eauto. split; eauto. apply join_comm . 
  apply join_emp.  eauto. split. eauto. split. apply join_comm . apply join_emp. eauto. 
  split. eapply is_isr_irrel_Aarray_new. eauto.
  split; eauto.
  simpl. split; eauto. unfold emposabst. auto.
Qed.

Lemma is_isr_pos_sllseg :
  forall vll a b c ir ir' ier ier' ie si si' cs x aop hd tn pbls,  
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= pos_sllseg hd tn vll pbls ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= pos_sllseg hd tn vll pbls.
Proof.
  inductions vll; intros.
  - 
    simpl in *. simpljoin1.
    do 6 eexists; splits; eauto. 
    join auto. join auto.
    splits; auto.
    unfold emposabst; auto.
    unfold emposabst; auto.
  -
    unfold pos_sllseg in H; fold pos_sllseg in H.
    simpl_sat H. simpljoin1.
    eapply IHvll with (ir':=ir') (ier':=ier') (si':=si') in H24.
    unfold pos_sllseg; fold pos_sllseg.
    match goal with
      H: _ |- ?s |= ?A ** ?B =>
        remember A as X; remember B as Y
    end.
    simpl.
    exists x0. exists x1. exists c.
    exists x3. exists x4. exists x.
    splits; auto.

    subst.
    eapply is_isr_irrel_node; eauto.
    subst.
    apply aexists_intro. exists x6.
    sep pauto.
    split; eauto. 
    auto.
Qed.

Lemma is_isr_APosblkList:
  forall a b c ir ir' ier ier' ie si si' cs x aop pbls,  
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= APosblkList pbls ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= APosblkList pbls. 
Proof.
  intros.
  unfold APosblkList in *.
  destr_and_inst H p.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  exists x0 x1. exists c.
  exists x3 x4. exists x.
  splits; auto.
  exists x6.
  eapply is_isr_pos_sllseg; eauto.
Qed.

Lemma is_isr_llsegevaux: 
  forall l a b c ir ir' ier ier' ie si si' cs x aop head locmp ptrmp, 
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= llsegevaux head Vnull l locmp ptrmp V_OSTCBNext ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= llsegevaux head Vnull l locmp ptrmp V_OSTCBNext. 
Proof.
  inductions l.
  introv Hsat.
  simpl in Hsat. simpljoin1.
  simpl.
  do 6 eexists.
  splits; eauto.
  join auto. join auto. splits; auto. unfold emposabst. auto.
  unfold emposabst.
  do 6 eexists. splits; auto. join auto. join auto. 

  introv Hsat.
  unfold llsegevaux in Hsat. fold llsegevaux in Hsat.
  sep destruct Hsat.
  unfold llsegevaux. fold llsegevaux.

  exists x0 x1 x2 x3 x4.
  exists x5 x6 x7.
  sep split in Hsat.
  sep split; eauto.

  sep remember (1::nil)%nat in Hsat.
  solve_sat Hsat.
Qed.

Lemma is_isr_tcbdllsegevaux: 
  forall a b c ir ir' ier ier' ie si si' cs x aop tcbh tcbvl locvl ptrvl, 
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= tcbllsegevaux tcbh tcbvl locvl ptrvl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= tcbllsegevaux tcbh tcbvl locvl ptrvl. 
Proof.
  introv Hsat.
  unfold tcbllsegevaux in *.
  sep split in Hsat.
  sep split; eauto.
  eapply is_isr_llsegevaux; eauto.
Qed.

Lemma is_isr_AEvAtomHeap :
  forall ev a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEvAtomHeap ev->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEvAtomHeap ev.
Proof.
  inductions ev; intros.
  simpl in H; simpljoin1.
  simpl. 
  split; auto.
  unfold emposabst; auto.
  destruct a. destruct p. destruct t;
  unfold AEvAtomHeap in *; fold AEvAtomHeap in *;
  sep split in H;
  sep split;
  eauto;
  sep remember (1:: nil)%nat in H;
  sep remember (1:: nil)%nat;
  solve_sat H.
Qed.

Lemma is_isr_AEvStructHeap :
  forall ev a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEvStructHeap ev->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEvStructHeap ev.
Proof.
  inductions ev; intros.
  simpl in H; simpljoin1.
  simpl. 
  split; auto.
  unfold emposabst; auto.
  destruct a. destruct p. destruct t.
  unfolds; auto.
  unfolds; auto.  
  unfolds; auto.  
  unfolds; auto.  
  unfolds; auto.  
  unfolds; auto.
  unfolds; auto.  
  unfolds; auto.
  unfold AEvStructHeap in *; fold AEvStructHeap in *.
  sep split in H. sep split; auto.
  sep remember (1::nil)%nat in H.
  sep remember (1::nil)%nat.
  solve_sat H.
  eapply is_isr_irrel_Astruct; eauto.
  unfold AEvStructHeap in *; fold AEvStructHeap in *.
  sep split in H. sep split; auto.
Qed.

Lemma is_isr_AEvArrayHeap :
  forall ev a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEvArrayHeap ev->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEvArrayHeap ev.
Proof.
  inductions ev; intros.
  simpl in H; simpljoin1.
  simpl. 
  split; auto.
  unfold emposabst; auto.
  destruct a. destruct p.
  unfold AEvArrayHeap in *; fold AEvArrayHeap in *.
  sep split in H. sep split; auto.
  sep remember (1::nil)%nat in H.
  sep remember (1::nil)%nat.
  solve_sat H.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma is_isr_err_sllseg :
  forall vll a b c ir ir' ier ier' ie si si' cs x aop hd tn pbls,  
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= err_sllseg hd tn vll pbls ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= err_sllseg hd tn vll pbls.
Proof.
  inductions vll; intros.
  - 
    simpl in *. simpljoin1.
    do 6 eexists; splits; eauto. 
    join auto. join auto.
    splits; auto.
    unfold emposabst; auto.
    unfold emposabst; auto.
  -
    unfold err_sllseg in H; fold err_sllseg in H.
    simpl_sat H. simpljoin1.
    eapply IHvll with (ir':=ir') (ier':=ier') (si':=si') in H24.
    unfold err_sllseg; fold err_sllseg.
    match goal with
      H: _ |- ?s |= ?A ** ?B =>
        remember A as X; remember B as Y
    end.
    simpl.
    exists x0. exists x1. exists c.
    exists x3. exists x4. exists x.
    splits; auto.

    subst.
    eapply is_isr_irrel_node; eauto.
    subst.
    apply aexists_intro. exists x6.
    sep pauto.
    split; eauto. 
    auto.
Qed.

Lemma is_isr_AErrblkList:
  forall a b c ir ir' ier ier' ie si si' cs x aop ebls,  
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AErrblkList ebls ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AErrblkList ebls. 
Proof.
  intros.
  unfold AErrblkList in *.
  destr_and_inst H p.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  exists x0 x1. exists c.
  exists x3 x4. exists x.
  splits; auto.
  exists x6.
  eapply is_isr_err_sllseg; eauto.
Qed.

Lemma is_isr_AOSEventFreeList:
  forall eventl a b c ir ir' ier ier' ie si si' cs x aop fecbh,  
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSEventFreeList fecbh eventl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSEventFreeList fecbh eventl. 
Proof.
  intros.
  unfold AOSEventFreeList in *.
  sep remember (1::nil)%nat in H.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto. join auto.
  do 4 eexists; do 3 exists empabst.
  splits; eauto. join auto.
  symmetry; eapply ecbf_sllseg_osabst_emp; eauto.
  apply map_join_emp.
  eexists. splits; eauto.
  unfold emposabst. auto. unfold emposabst. auto.
  clear - H5.
  (*ecbf_sll isr_is_irrel*)
  unfold ecbf_sll in *.
  inductions eventl.
  simpl in H5; simpljoin1.
  simpl; intuition.
  unfolds; auto.
  unfold ecbf_sllseg in H5; fold ecbf_sllseg in H5.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  do 5 destr_and_inst H5 eventl.

  sep split in H5; sep split; auto.
  simpl_sat H5.
  simpl_sat_goal.
  simpljoin1.

  do 3 eexists; do 3 exists empabst.
  repeat (split; eauto).
  lets Hx : node_osabst_emp H7; substs.
  eapply is_isr_irrel_node; eauto.

  do 6 eexists; repeat(split; eauto).
  eapply OSAbstMod.join_emp; auto.
  lets Hx: Aarray_osabst_emp H12; substs.
  eapply is_isr_irrel_Aarray; eauto.

   do 6 eexists; repeat(split; eauto).
  eapply OSAbstMod.join_emp; auto.
  lets Hx': Aarray_osabst_emp H17; substs. 
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma is_isr_AOSQFreeList:
  forall osql a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSQFreeList osql ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSQFreeList osql. 
Proof.
  intros.
  unfold AOSQFreeList in *.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 7 eexists; repeat(split; eauto).
  simpl in H3; simpl; simpljoin1.
  do 7 eexists; splits; eauto.
  apply map_join_comm; apply map_join_emp.
  apply map_join_emp.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; auto.
  eapply is_isr_irrel_sll; eauto.
Qed.

Lemma is_isr_AOSQFreeBlk:
  forall qblkl a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSQFreeBlk qblkl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSQFreeBlk qblkl. 
Proof.
  intros.
  unfold AOSQFreeBlk in *.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 7 eexists; repeat(split; eauto).
  simpl in H3; simpl; simpljoin1.
  do 7 eexists; splits; eauto.
  apply map_join_comm; apply map_join_emp.
  apply map_join_emp.
  eexists; splits; eauto.
  unfolds; auto.
  unfolds; auto.
  clear - H4.
  unfold qblkf_sll.
  unfold qblkf_sll in *.
  eapply is_isr_qblkf_sllseg; eauto.
Qed.

Lemma is_isr_AECBList:
  forall ectrl msgql ecbls tcbls a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AECBList ectrl msgql ecbls tcbls ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AECBList ectrl msgql ecbls tcbls. 
Proof.
  intros.
  unfold AECBList in *.
  destr_and_inst H msgql.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_qblkf_evsllseg; eauto.
Qed.

Lemma is_isr_AEvtCap :
  forall capl l fieldname eibtype a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AEvtCap l capl fieldname eibtype ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AEvtCap l capl fieldname eibtype .
Proof.
  induction capl; destruct l;
  unfold AEvtCap; fold AEvtCap; intros.
  simpl in *; auto.
  destr_and_inst H head.
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat (split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma EvtInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop ecbls tcbh tcbvl tcbls vhold scapl mcapl qcapl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= EvtInv ecbls tcbh tcbvl tcbls vhold scapl mcapl qcapl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= EvtInv ecbls tcbh tcbvl tcbls vhold scapl mcapl qcapl.
Proof.
  introv Hsat.
  unfold EvtInv in *.
  unfold ASemEIBs in *.
  unfold AMuxEIBs in *.
  unfold AMqEIBs in *.
  unfold ASemCap in *.
  unfold AMuxCap in *.
  unfold AMqCap in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2 x3 x4 x5.
  exists x6 x7 x8 x9 x10 x11.
  exists x12 x13 x14 x15 x16 x17.
  exists x18 x19 x20 x21.
  sep split in Hsat. sep split; eauto.
  sep remember (1::nil)%nat in Hsat.
  solve_sat Hsat.
  eapply is_isr_AMqAttr; eauto.
  clear -H27.
  sep remember (1::nil)%nat in H27.
  solve_sat H27.
  eapply is_isr_AEvtCap; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_APthreadMutex; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AEvtCap; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_ASeminfo; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AEvtCap; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AOSEventFreeList; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AOSQFreeList; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AOSQFreeBlk; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AECBList; eauto.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.

  sep lift 2%nat in H5. sep lift 2%nat.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AErrblkList; eauto.
  clear -H5. 
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear -H5.
  sep lift 2%nat in H5. sep lift 2%nat.
  sep remember (1::nil)%nat in H5.  
  solve_sat H5.
  eapply is_isr_APosblkList; eauto.
   clear -H5. 
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear -H5. 
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AEvAtomHeap; eauto. 
  clear -H8. 
  sep remember (1::nil)%nat in H8.
  solve_sat H8.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AEvStructHeap; eauto. 
  clear -H8. 
  sep remember (1::nil)%nat in H8.
  solve_sat H8.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_AEvArrayHeap; eauto. 
  clear -H8. 
  sep remember (1::nil)%nat in H8.
  solve_sat H8.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear -H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply is_isr_tcbdllsegevaux; eauto.
Qed.

(* Proof. *)
(*   introv Hsat. *)
(*   unfold EvtInv in *. *)
(*   unfold ASemEIBs in *. *)
(*   unfold AMuxEIBs in *. *)
(*   unfold AMqEIBs in *. *)
(*   sep normal in Hsat. sep normal. *)
(*   sep destruct Hsat. *)
(*   exists x0 x1 x2 x3 x4 x5. *)
(*   exists x6 x7 x8 x9 x10 x11. *)
(*   exists x12 x13 x14 x15 x16 x17. *)
(*   exists x18 x19 x20 x21. *)
(* Admitted. *)
(*   (* sep split in Hsat. sep split; eauto. *)
(*   sep remember (1::nil)%nat in Hsat. *)
(*   solve_sat Hsat. *)
(*   eapply is_isr_AOSEventFreeList; eauto. *)
(*   clear -H21. *)
(*   sep remember (1::nil)%nat in H21. *)
(*   solve_sat H21. *)
(*   eapply is_isr_AOSQFreeList; eauto. *)
(*   clear -H5. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AOSQFreeBlk; eauto. *)
(*   clear -H5. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AECBList; eauto. *)
(*   clear -H5. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)

(*   sep lift 2%nat in H5. sep lift 2%nat. *)
(*   clear -H5. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AErrblkList; eauto. *)
(*   clear -H5.  *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   clear -H5. *)
(*   sep lift 2%nat in H5. sep lift 2%nat. *)
(*   sep remember (1::nil)%nat in H5.   *)
(*   solve_sat H5. *)
(*   eapply is_isr_APosblkList; eauto. *)
(*    clear -H5.  *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   clear -H5.  *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AEvAtomHeap; eauto.  *)
(*   clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AEvStructHeap; eauto.  *)
(*   clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AEvArrayHeap; eauto.  *)
(*   clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_ASeminfo; eauto. *)
(*    clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_APthreadMutex; eauto. *)
(*    clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_AMqAttr; eauto. *)
(*   clear -H8.  *)
(*   sep remember (1::nil)%nat in H8. *)
(*   solve_sat H8. *)
(*   clear -H5.  *)
(*   sep remember (1::nil)%nat in H5. *)
(*   solve_sat H5. *)
(*   eapply is_isr_tcbdllsegevaux; eauto. *)
(* Qed. *) *)

(*  end of is isr irrelvant lemmas about EvtInv *)

(* IntInv isr_is_irrel *)

Lemma IntInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= IntInv -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= IntInv.
Proof.
  introv Hsat.
  unfold IntInv in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2 x3.
  sep remember (1::nil)%nat in Hsat.
  solve_sat Hsat.
  clear - H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear - H5.
  sep remember (1::nil)%nat in H5. solve_sat H5. 
  unfold AOSInthandler in *. 
  unfold GAarray in *.
  destr_and_inst H4 v.
  solve_sat H4.
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5.
  sep remember (1::nil)%nat in H5; solve_sat H5. clear - H5.
  sep remember (1::nil)%nat in H5. solve_sat H5. 
  unfold AOSInthandlerParam in *. 
  unfold GAarray in *.
  destr_and_inst H4 v.
  solve_sat H4.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

(* TmrInv isr_is_irrel *)
Lemma is_isr_irrel_AOSTMRList_TMRused :
  forall v1l vl2 vl3 vl4 a b c ir ir'  ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSTMRList_TMRused v1l vl2 vl3 vl4 ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSTMRList_TMRused v1l vl2 vl3 vl4.
Proof.
  intros. unfold AOSTMRList_TMRused, AOSTMRIDUsed,GAarray in *.
  simpl_sat H; simpl_sat_goal;simpljoin1.

  do 6 eexists; splits; eauto.
  do 6 eexists. splits; eauto.

  do 6 eexists. splits; auto.
  eapply map_join_emp. 
  eapply map_join_emp.

  do 6 eexists. splits; auto. 
  eapply map_join_emp. 
  eapply map_join_emp.

  do 7 eexists. splits;eauto.
  apply H37. 
  eapply is_isr_irrel_Aarray;eauto.
  cbn;unfold emposabst;auto.

  do 6 eexists. splits; auto. 
  eapply map_join_emp. 
  eapply map_join_emp.
  splits;eauto.
  1,2: cbn;unfold emposabst;auto.
Qed.

Lemma TmrInv'_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= TmrInv'-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= TmrInv'.
Proof.
  introv Hsat.
  unfold TmrInv' in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2 x3 x4.

  sep remember (1::nil)%nat in Hsat.
  simpl_sat Hsat; simpl_sat_goal.
  simpljoin1. 
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOSTMRList_TMRused;eauto.
Qed.

Lemma is_isr_irrel_AOScoreheapl :
  forall vl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |=  AOScoreheapl vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOScoreheapl vl.
Proof.
  induction vl;intros.
  - cbn in *. auto.
  - destruct a. destruct p. 
    unfold AOScoreheapl in *;fold AOScoreheapl in *.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_Aarray;eauto.
    do 6 eexists. splits;eauto.
    eapply join_emp;auto.
    eapply join_emp;auto.
    splits;auto.
    cbn;splits;auto. unfold emposabst. auto.
Qed.

Lemma is_isr_irrel_AOScoreheape :
  forall vl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |=  AOScoreheape vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOScoreheape vl.
Proof.
  induction vl;intros.
  - cbn in *. auto.
  - destruct a. destruct p. 
    unfold AOScoreheape in *;fold AOScoreheape in *.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
Qed.

Lemma is_isr_irrel_AOScoreheapt :
  forall vl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |=  AOScoreheapt vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOScoreheapt vl.
Proof.
  induction vl;intros.
  - cbn in *. auto.
  - destruct a. destruct p. 
    unfold AOScoreheapt in *;fold AOScoreheapt in *.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_Astruct;eauto.
    do 6 eexists. splits;eauto.
    eapply join_emp;auto.
    eapply join_emp;auto.
    splits;auto.
    cbn;splits;auto. unfold emposabst. auto.
Qed.

Lemma HeapInv'_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= HeapInv' -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= HeapInv'.
Proof.
  introv Hsat.
  unfold HeapInv' in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2.

  sep remember (1::nil)%nat in Hsat.
  simpl_sat Hsat; simpl_sat_goal.
  simpljoin1. 
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOScoreheapl;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOScoreheape;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOScoreheapt;eauto.
Qed.


Lemma TmrInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= TmrInv -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= TmrInv.
Proof.
  introv Hsat.
  unfold TmrInv in *.
  simpl_sat Hsat; simpl_sat_goal.
  simpljoin1. 
  do 6 eexists; repeat(split; eauto).
  eapply TmrInv'_isr_is_irrel;eauto.
  eapply HeapInv'_isr_is_irrel;eauto.
Qed.

(* CoreCommuInv isr_is_irrel *)
Lemma is_isr_irrel_Memory_sigcore_aux :
  forall vl p n a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Memory_sigcore_aux n p vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Memory_sigcore_aux n p vl.
Proof.
 induction vl;intros.
 - cbn in *;auto.
 - unfold Memory_sigcore_aux in *;fold Memory_sigcore_aux in *.
   simpl_sat H; simpl_sat_goal;simpljoin1.
   do 6 eexists; repeat(split; eauto).
   unfold Memory_Node in *.
   cancel_pure H3.
   eapply is_isr_irrel_Aarray;eauto.
Qed.

Lemma is_isr_irrel_AOSIPCMem_aux :
  forall pl ml a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSIPCMem_aux pl ml->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSIPCMem_aux pl ml.
Proof.
  induction pl;intros.
  - destruct ml;tryfalse.
    cbn in *. auto.
  - unfold AOSIPCMem_aux in *;fold AOSIPCMem_aux in *. 
    destruct a;tryfalse.
    destruct ml;tryfalse.
    simpl_sat H; simpl_sat_goal;simpljoin1.
    do 6 eexists; repeat(split; eauto).
    unfold Memory_sigcore in *.
    cancel_pure H3.
    eapply is_isr_irrel_Memory_sigcore_aux;eauto.
Qed.

Lemma is_isr_irrel_AOSIPCMem :
  forall pl ml a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSIPCMem pl ml ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSIPCMem pl ml.
Proof.
  intros. unfold AOSIPCMem,GAarray in *.
  simpl_sat H; simpl_sat_goal;simpljoin1.
  do 6 eexists; repeat(split; eauto).
  do 7 eexists; repeat(split; eauto). apply H17.
  eapply is_isr_irrel_Aarray;eauto.
  do 6 eexists; splits;eauto.
  eapply map_join_emp. 
  eapply map_join_emp. 
  2: cbn;unfold emposabst;auto.
  eapply is_isr_irrel_AOSIPCMem_aux;eauto.
Qed.

Lemma is_isr_irrel_AOSIPCSem :
  forall vl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSIPCSem vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSIPCSem vl.
Proof.
  induction vl;intros.
  - cbn in *;auto.
  - unfold AOSIPCSem in *.
    cancel_pure H.
    unfold GAarray in *.
    sep destruct H.
    simpl_sat H;simpl_sat_goal;simpljoin1.
    do 7 eexists; repeat(split; eauto).
    apply H4.
    eapply is_isr_irrel_Aarray;eauto.
Qed.

Lemma is_isr_irrel_AOSIPCSendSem :
  forall vl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSIPCSendSem vl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSIPCSendSem vl.
Proof.
  induction vl;intros.
  - cbn in *;auto.
  - unfold AOSIPCSendSem in *.
    cancel_pure H.
    unfold GAarray in *.
    sep destruct H.
    simpl_sat H;simpl_sat_goal;simpljoin1.
    do 7 eexists; repeat(split; eauto).
    apply H4.
    eapply is_isr_irrel_Aarray;eauto.
Qed.

Lemma is_isr_irrel_Agvarenv' :
  forall lv t v a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= G& v @ t == lv ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= G& v @ t == lv.
Proof.
  intros.
  simpl in H;simpl. simpljoin1.
  eexists.
  splits;eauto.
  unfold emposabst;auto.
Qed.

Lemma is_isr_irrel_Aptrmapsto :
  forall lv t v pb a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= Aptrmapsto lv t pb v ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= Aptrmapsto lv t pb v.
Proof.
  intros.
  simpl in H;simpl. simpljoin1.
  splits;eauto.
  unfold emposabst;auto.
Qed.

Lemma is_isr_irrel_AOSIPCBroadList :
  forall vl cl a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= AOSIPCBroadList vl cl ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= AOSIPCBroadList vl cl.
Proof.
  intros. unfold AOSIPCBroadList,GAarray,Agvarmapsto in *.
  simpl_sat H; simpl_sat_goal;simpljoin1.

  do 7 eexists; repeat(split; eauto).
  { do 7 eexists. splits; eauto.
    eapply is_isr_irrel_Agvarenv';eauto.
    eapply is_isr_irrel_Aptrmapsto;eauto. }

  do 6 eexists; repeat(split; eauto). 
  simpl in H29. simpljoin1. cbn;eauto. 
  simpl in H29. simpljoin1. unfold emposabst;eauto.

  do 6 eexists; splits;eauto.
  eapply map_join_emp. 
  eapply map_join_emp.
  
  do 7 eexists; splits;eauto.
  eapply join_comm; eapply map_join_emp. 
  eapply join_comm; eapply map_join_emp.
  { simpl in H29. simpljoin1. simpl. eexists. splits;eauto. unfold emposabst;eauto.  }
  eapply is_isr_irrel_Aarray;eauto.
  
  do 6 eexists; splits; eauto.
  eapply map_join_emp.
  eapply map_join_emp.
  splits;eauto.
  1,2: cbn;unfold emposabst;auto.
Qed.

Lemma is_isr_AdynrefaccfgFreeList:
  forall  cfgp vl a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AdynrefaccfgFreeList cfgp vl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |=  AdynrefaccfgFreeList cfgp vl . 
Proof.
  intros.
  unfold AdynrefaccfgFreeList in *.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 7 eexists; repeat(split; eauto).
  simpl in H3; simpl; simpljoin1.
  eapply is_isr_irrel_sll; eauto.
Qed.

Lemma is_isr_Adynheap:
  forall vl a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Adynheap  vl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |=  Adynheap vl . 
Proof.
  induction vl;intros.
  - cbn in *. auto.
  - destruct a. 
    cbn [Adynheap] in *. 
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_Astruct;eauto.
    do 6 eexists. splits;eauto.
    eapply join_emp;auto.
    eapply join_emp;auto.
    splits;auto.
    cbn;splits;auto. unfold emposabst. auto.
Qed.

Lemma DynamicRefactorINV_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop ecbls,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= DynamicRefactorINV  ecbls-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= DynamicRefactorINV ecbls .
Proof. 
  intros.
  unfold DynamicRefactorINV in *.
  sep destruct H.
  exists x0 x1 x2 x3.
  sep split in H.
  sep split; auto.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_AdynrefaccfgFreeList. eauto.
  do 6 eexists; repeat(split; eauto).
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_Adynheap; eauto.
  do 6 eexists; repeat(split; eauto).
Qed.

Lemma CoreCommuInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= CoreCommuInv vl-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= CoreCommuInv vl.
Proof.
  introv Hsat.
  unfold CoreCommuInv in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2 x3 x4 x5. 
  exists x6.
  sep split in Hsat.
  sep split;auto.
  clear H H0.

  sep remember (1::nil)%nat in Hsat.
  simpl_sat Hsat; simpl_sat_goal.
  simpljoin1. 
  do 6 eexists; repeat(split; eauto).

  clear -H8. rename H8 into H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  
  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOSIPCMem;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOSIPCSem;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOSIPCSendSem;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_AOSIPCBroadList;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply DynamicRefactorINV_isr_is_irrel;eauto.
Qed.

(* PartitionInv isr_is_irrel *)

Lemma dmportp_sllseg_qport_msg_isr_is_irrel:
  forall dportl a b c ir ir' ier ier' ie si si' cs x aop pnow pend qstart qend qentries,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= dmportp_sllseg_qport_msg pnow pend qstart qend qentries dportl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= dmportp_sllseg_qport_msg pnow pend qstart qend qentries dportl.
Proof.
  induction dportl;intros.
  - destruct qentries;cbn [dmportp_sllseg_qport_msg] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst. auto.
  - destruct qentries;cbn [dmportp_sllseg_qport_msg] in *;tryfalse.
    sep normal in H. sep normal.
    sep destruct H. exists x0.
    sep split in H.
    sep split;auto.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1. 
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_Aarray;eauto.

    rename H6 into H. clear - H IHdportl.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1. 
    do 6 eexists; repeat(split; eauto).
Qed.



Lemma dmportp_sll_isr_is_irrel:
  forall dportl a b c ir ir' ier ier' ie si si' cs x aop dportlptr dportmsgll,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= dmportp_sll dportlptr dportl dportmsgll OS_Port_V_nextPort -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= dmportp_sll dportlptr dportl dportmsgll OS_Port_V_nextPort.
Proof.
  unfold dmportp_sll;induction dportl;intros.
  - destruct dportmsgll;cbn [dmportp_sllseg] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn.  unfold emposabst. auto.
  - destruct dportmsgll;cbn [dmportp_sllseg] in *;tryfalse.
    sep normal in H. sep normal.
    sep destruct H. exists x0 x1 x2.
    sep split in H.
    sep split;auto.

    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1. 
    do 6 eexists; repeat(split; eauto).
    unfold APortStruct in *.
    eapply is_isr_irrel_Astruct'; eauto.

    clear H8. rename H9 into H.
    sep remember (2::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    eapply join_comm in H4.
    eapply join_comm in H8.
    do 6 eexists; repeat(split; eauto).
    destruct H10.
    { left.
      sep split in H. sep split;auto.
      unfold dmportp_sllseg_sampleport_msg in *.
      sep normal in H. sep normal.
      sep destruct H. exists x9 x12.
      sep split in H.
      sep split;auto.
      sep remember (1::nil)%nat in H.
      simpl_sat H;simpl_sat_goal.
      simpljoin1.
      do 6 eexists; repeat(split; eauto).
      eapply is_isr_irrel_Aarray;eauto. }
    { right.
      sep normal in H. sep normal.
      sep destruct H. exists x9 x12 x13 x14 x15 x16.
      sep split in H.
      sep split;auto.
      sep remember (1::nil)%nat in H.
      simpl_sat H;simpl_sat_goal.
      simpljoin1.
      do 6 eexists; repeat(split; eauto).
      eapply dmportp_sllseg_qport_msg_isr_is_irrel;eauto.
      
      eapply dmportp_sllseg_qport_msg_isr_is_irrel;eauto. }
Qed. 

Lemma AOSDomainPortPtrList_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop dportlptr dportl dportmsgll,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSDomainPortPtrList dportlptr dportl dportmsgll-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSDomainPortPtrList dportlptr dportl dportmsgll.
Proof. 
  intros.
  unfold AOSDomainPortPtrList in *.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply dmportp_sll_isr_is_irrel;eauto.
Qed.


Lemma kportNode_P_isr_is_irrel:
  forall kportvl a b c ir ir' ier ier' ie si si' cs x aop kportl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= kportNode_P kportvl kportl-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= kportNode_P kportvl kportl.
Proof.
  induction kportvl;intros.
  - destruct kportl; cbn [kportNode_P] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - destruct kportl; cbn [kportNode_P] in *;tryfalse.
    
    sep remember (2::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    eapply join_comm in H1. eapply join_comm in H3.
    do 6 eexists; repeat(split; eauto).
    
    destruct H5.
    + left.
      simpl_sat H;simpl_sat_goal.
      simpljoin1. cbn. unfold emposabst. auto.
    + right.
      clear - H.
      sep normal in H. sep normal.
      sep destruct H. exists x.
      sep split in H.
      sep split;auto.
      eapply is_isr_irrel_Astruct';eauto.
Qed.

Lemma AOSKernelPortIDTbl_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop kportvl kportl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSKernelPortIDTbl kportvl kportl-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSKernelPortIDTbl kportvl kportl.
Proof. 
  intros.
  unfold AOSKernelPortIDTbl, GAarray in *.
  sep normal in H. sep normal.
  sep destruct H. exists x0.
  sep split in H.
  sep split;auto.

  clear - H.
  sep remember (1::nil)%nat in H.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray;eauto.

  eapply kportNode_P_isr_is_irrel;eauto.
Qed.

Lemma Channel_dstkport_get_isr_is_irrel:
  forall l a b c ir ir' ier ier' ie si si' cs x aop p n,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Channel_dstkport_get p Vnull n l-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Channel_dstkport_get p Vnull n l.
Proof.
  induction l;intros.
  - destruct n;cbn [Channel_dstkport_get] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - destruct n;cbn [Channel_dstkport_get] in *;tryfalse.
    sep normal in H. sep normal.
    sep destruct H. exists x0 x1.
    sep split in H.
    sep split;auto.

    clear - H IHl.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
Qed.

Lemma ChannelNode_isr_is_irrel:
  forall chanvl a b c ir ir' ier ier' ie si si' cs x aop chanl chandstkportll,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ChannelNode chanvl chanl chandstkportll-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ChannelNode chanvl chanl chandstkportll.
Proof.
  induction chanvl;intros.
  - destruct chanl, chandstkportll; cbn [ChannelNode] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - destruct chanl, chandstkportll; cbn [ChannelNode] in *;tryfalse.
    
    sep remember (2::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    eapply join_comm in H1. eapply join_comm in H3.
    do 6 eexists; repeat(split; eauto).
    
    destruct H5.
    + left.
      simpl_sat H;simpl_sat_goal.
      simpljoin1. cbn. unfold emposabst. auto.
    + right.
      clear - H.
      sep normal in H. sep normal.
      sep destruct H. exists x x0.
      sep split in H.
      sep split;auto.

      sep remember (1::nil)%nat in H.
      simpl_sat H;simpl_sat_goal.
      simpljoin1.
      do 6 eexists; repeat(split; eauto).
      eapply Channel_dstkport_get_isr_is_irrel;eauto.
      eapply is_isr_irrel_node;eauto.
Qed.

Lemma AOSChannelIDTbl_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop chanvl chanl chandstkportll,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSChannelIDTbl chanvl chanl chandstkportll-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSChannelIDTbl chanvl chanl chandstkportll.
Proof. 
  intros.
  unfold AOSChannelIDTbl, GAarray in *.
  sep normal in H. sep normal.
  sep destruct H. exists x0.
  sep split in H.
  sep split;auto.

  clear - H.
  sep remember (1::nil)%nat in H.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray;eauto.

  eapply ChannelNode_isr_is_irrel;eauto.
Qed.

Lemma AOSKernelPortFreeList_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop p l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSKernelPortFreeList p l -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSKernelPortFreeList p l.
Proof. 
  intros.
  unfold AOSKernelPortFreeList in *.

  sep remember (1::nil)%nat in H.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5. rename H5 into H.
  revert a b ir ir' ier ier' ie si si' cs aop p x1 x4 H.
  induction l;unfold kportf_sll;intros.
  - cbn [kportf_sllseg] in *.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - cbn [kportf_sllseg] in *.
    sep destruct H. exists x.
    sep split in H. sep split;auto.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_node;eauto.
Qed.

Lemma AOSChannelFreeList_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop p l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSChannelFreeList p l -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSChannelFreeList p l.
Proof. 
  intros.
  unfold AOSChannelFreeList in *.

  sep remember (1::nil)%nat in H.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5. rename H5 into H.
  revert a b ir ir' ier ier' ie si si' cs aop p x1 x4 H.
  induction l;unfold channelf_sll;intros.
  - cbn [channelf_sllseg] in *.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - cbn [channelf_sllseg] in *.
    sep destruct H. exists x.
    sep split in H. sep split;auto.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    eapply is_isr_irrel_node;eauto.
Qed.

Lemma OtherPortPtrList_isr_is_irrel:
  forall otherppl a b c ir ir' ier ier' ie si si' cs x aop otherpl othermsgll,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= OtherPortPtrList otherppl otherpl othermsgll -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= OtherPortPtrList otherppl otherpl othermsgll.
Proof.
  induction otherppl;intros.
  - destruct otherpl, othermsgll;cbn [OtherPortPtrList] in *;tryfalse.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    cbn. unfold emposabst;auto.
  - destruct otherpl, othermsgll;cbn [OtherPortPtrList] in *;tryfalse.
    sep destruct H. exists x0.
    sep split in H. sep split;auto.
    sep remember (1::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    do 6 eexists; repeat(split; eauto).
    unfold APortStruct in *.
    eapply is_isr_irrel_Astruct';eauto.
    
    clear -H7 IHotherppl. rename H7 into H.
    sep remember (2::nil)%nat in H.
    simpl_sat H;simpl_sat_goal.
    simpljoin1.
    eapply join_comm in H1. eapply join_comm in H3.
    do 6 eexists; repeat(split; eauto).

    destruct H5.
    + left.
      sep split in H. sep split;auto.
      unfold dmportp_sllseg_sampleport_msg in *.
      sep normal in H. sep normal.
      sep destruct H. exists x3 x7. sep split in H. sep split;auto.
      sep remember (1::nil)%nat in H.
      simpl_sat H;simpl_sat_goal.
      simpljoin1.
      do 6 eexists; repeat(split; eauto).
      eapply is_isr_irrel_Aarray;eauto.
    + right.
      sep destruct H. exists x3 x7 x8 x9 x10 x11. sep split in H. sep split;auto.
      sep remember (1::nil)%nat in H.
      simpl_sat H;simpl_sat_goal.
      simpljoin1.
      do 6 eexists; repeat(split; eauto).
      eapply dmportp_sllseg_qport_msg_isr_is_irrel;eauto.
      eapply dmportp_sllseg_qport_msg_isr_is_irrel;eauto.
Qed.

Lemma AOSCorePortPtrList_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop p pl dportls,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSCorePortPtrList p pl dportls -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSCorePortPtrList p pl dportls.
Proof. 
  intros.
  unfold AOSCorePortPtrList in *.

  sep remember (1::nil)%nat in H.
  simpl_sat H;simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
Qed.

(* add by CNU *)

(* Adomain2index *)
Lemma Adomain2index'_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Adomain2index' vl  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Adomain2index' vl.
Proof.
  intros.
  unfold Adomain2index' in *.
  do 2 destr_and_inst H m .
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 4 eexists.
  unfold empst.
  unfold emptaskst, emposabst.
  splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold GAarray in *.
  destr_and_inst H3 v.
  solve_sat H3.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma Adomain2index_isr_is_irrel:
    forall a b c ir ir' ier ier' ie si si' cs x aop vl domls,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Adomain2index vl domls  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Adomain2index vl domls.
Proof.
  intros.
  unfold Adomain2index in *.
  sep split in H.
  sep split; eauto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 6 eexists. splits; eauto.
  eapply Adomain2index'_isr_is_irrel; eauto.
Qed.

(* AKsDSchdidx *)

Lemma AKsDSchdidx_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop ksdomscdidx,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDSchdidx ksdomscdidx  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDSchdidx ksdomscdidx.
Proof.
   intros.
   unfold AKsDSchdidx in *.
   sep split in H. sep split; auto.
Qed.

(* AKsDSchdlen *)
Lemma AKsDSchdlen_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop ksdomscdlen,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDSchdlen ksdomscdlen  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDSchdlen ksdomscdlen.
Proof.
  unfold AKsDSchdlen; intros.
  sep split in H. sep split; auto.
Qed.

(* AKsCurDomain *)
Lemma AKsCurDomain_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop kscurdom,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsCurDomain kscurdom  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsCurDomain kscurdom.
Proof.
   unfold AKsCurDomain; intros.
   sep split in H. sep split; auto.
Qed.

(* AKsLastDomain *)
Lemma AKsLastDomain_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop kslastd,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsLastDomain kslastd  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsLastDomain kslastd.
Proof.
   unfold AKsLastDomain; intros.
   sep split in H. sep split; auto.
Qed.

(* AKsDomainTime *)
Lemma AKsDomainTime_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop ksdomt,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDomainTime ksdomt  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDomainTime ksdomt.
Proof.
   unfold AKsDomainTime; intros.
   sep split in H. sep split; auto.
Qed.

(* AKsDomSchedule' *)
Lemma AKsDomSchedule'_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop ksdschedule,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDomSchedule' ksdschedule  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDomSchedule' ksdschedule.
Proof.
  unfold AKsDomSchedule'; intros.
  destr_and_inst H v.
  sep split in H. simpljoin. sep split; auto.
  simpl_sat H; simpl_sat_goal ; simpljoin.
  do 6 eexists. splits; eauto.
  eapply is_isr_irrel_Aarray_new; eauto.
Qed.

(* AKsDomSchedule *)
Lemma AKsDomSchedule_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop ksdschedule ksdscd,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDomSchedule ksdschedule ksdscd  ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDomSchedule ksdschedule ksdscd.
Proof.
  unfold AKsDomSchedule; intros.
  sep split in H. simpljoin. sep split; auto.
  simpl_sat H; simpl_sat_goal ; simpljoin.
  do 6 eexists. splits; eauto.
  eapply AKsDomSchedule'_isr_is_irrel; eauto.
Qed.

(* AIntPartMux' *)
Lemma AIntPartMux'_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop intpmuxvl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AIntPartMux' intpmuxvl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AIntPartMux' intpmuxvl.
Proof.
  unfold AIntPartMux'; intros.
  destr_and_inst H v.
  sep split in H. simpljoin. sep split; auto.
  simpl_sat H; simpl_sat_goal ; simpljoin.
  do 6 eexists. splits; eauto.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

(* AIntPartMux *)
Lemma AIntPartMux_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop intpmuxvl intpmux,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AIntPartMux intpmuxvl intpmux ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AIntPartMux intpmuxvl intpmux.
Proof.
  unfold AIntPartMux; intros.
  sep split in H. simpljoin. sep split; auto.
  simpl_sat H; simpl_sat_goal ; simpljoin.
  do 6 eexists. splits; eauto.
  eapply AIntPartMux'_isr_is_irrel; eauto.
Qed.

(* AIntrDomainMux *)
Lemma AIntrDomainMux_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl absintrdom,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AIntrDomainMux l vl absintrdom ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AIntrDomainMux l vl absintrdom.
Proof.
   unfold AIntrDomainMux; intros.
   destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

(* node_offt *)
Lemma node_offt_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl t,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= node_offt l vl t ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= node_offt l vl t.
Proof.
  unfold node_offt; intros.
  do 2 destr_and_inst H v.
  sep split in H. simpljoin. sep split; auto.
  eapply is_isr_irrel_Astruct; eauto.
Qed.

(* AAllArea *)
Lemma AAllArea_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl areaconf,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AAllArea l vl areaconf ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AAllArea l vl areaconf.
Proof.
   unfold AAllArea; intros.
   destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   eapply node_offt_isr_is_irrel; eauto.
Qed.

Lemma ADeviceioTbl'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ADeviceioTbl' l vl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ADeviceioTbl' l vl.
Proof.
induction vl; unfold ADeviceioTbl'; fold ADeviceioTbl';
intros.
simpl in *.
auto.
destruct a.
do 2 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply is_isr_irrel_Aarray; eauto.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.

Lemma AksDomains'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AksDomains' l vl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AksDomains' l vl.
Proof.
induction vl; unfold AksDomains'; fold AksDomains';
intros.
simpl in *.
auto.
destruct a as [[[]]].
sep normal in H.
sep normal.
do 5 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
do 6 eexists. splits; eauto.
eapply ADeviceioTbl'_isr_is_irrel; eauto.
do 6 eexists. splits; eauto.
eapply is_isr_irrel_Aarray; eauto.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.

Lemma AksDomSchedule'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AksDomSchedule' l vl ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AksDomSchedule' l vl.
Proof.
induction vl; unfold AksDomSchedule'; fold AksDomSchedule';
intros.
simpl in *.
auto.
sep normal in H.
sep normal.
do 2 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.

Lemma Acpus'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Acpus' l vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Acpus' l vl.
Proof.
induction vl; unfold Acpus'; fold Acpus';
intros.
simpl in *.
auto.
destruct a as [[[]]].
sep normal in H.
sep normal.
do 5 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply AksDomains'_isr_is_irrel; eauto.
do 6 eexists. splits; eauto.
eapply AksDomSchedule'_isr_is_irrel; eauto.
do 6 eexists. splits; eauto.
eapply is_isr_irrel_Aarray; eauto.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.


(* ACPUs *)
Lemma ACPUs_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl cpus_,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ACPUs l vl cpus_ -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ACPUs l vl cpus_.
Proof.
   unfold ACPUs; intros.
   destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   eapply Acpus'_isr_is_irrel; eauto.
Qed.

(* AchannelTbl' *)
Lemma AchannelTbl'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AchannelTbl' l vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AchannelTbl' l vl.
Proof.
induction vl; unfold AchannelTbl'; fold AchannelTbl';
intros.
simpl in *.
auto.
destruct a.
sep normal in H.
sep normal.
do 3 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply is_isr_irrel_Aarray; eauto.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.

(* AChannelTbl *)
Lemma AChannelTbl_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl channels,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AChannelTbl l vl channels -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AChannelTbl l vl channels.
Proof.
   unfold AChannelTbl; intros.
   destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   eapply AchannelTbl'_isr_is_irrel; eauto.
Qed.

(* AportTbl' *)
Lemma AportTbl'_isr_is_irrel:
    forall vl a b c ir ir' ier ier' ie si si' cs x aop l,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AportTbl' l vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AportTbl' l vl.
Proof.
induction vl; unfold AportTbl'; fold AportTbl';
intros.
simpl in *.
auto.
sep normal in H.
sep normal.
do 2 destr_and_inst H v.
sep split in H. simpljoin. sep split; auto.
simpl_sat H; simpl_sat_goal ; simpljoin.
do 6 eexists. splits; eauto.
eapply node_offt_isr_is_irrel; eauto.
Qed.

(* APortTbl *)
Lemma APortTbl_isr_is_irrel :
    forall a b c ir ir' ier ier' ie si si' cs x aop l vl prttbl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= APortTbl l vl prttbl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= APortTbl l vl prttbl.
Proof.
   unfold APortTbl; intros.
   destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   eapply AportTbl'_isr_is_irrel; eauto.
Qed.

(* AucosConf *)
Lemma AucosConf_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop l ucosf,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AucosConf l ucosf -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AucosConf l ucosf.
Proof.
   unfold AucosConf; intros.
   destruct l as [[[[[[]]]]]].
   destruct ucosf as  [[[[[[[[[[[[[]]]]]]]]]]]]].
   sep normal in H.
   sep normal.
   do 2 destr_and_inst H v.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply AIntrDomainMux_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply AAllArea_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply ACPUs_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply AChannelTbl_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply APortTbl_isr_is_irrel; eauto.
   eapply is_isr_irrel_node; eauto.
Qed.

(* Asms_mpaxinfo *)
Lemma Asms_mpaxinfo_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Asms_mpaxinfo vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Asms_mpaxinfo vl.
Proof.
   unfold Asms_mpaxinfo; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   eapply is_isr_irrel_Aarray; eauto.
Qed.

(* ASMSMpax *)
Lemma ASMSMpax_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ASMSMpax vl abs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ASMSMpax vl abs.
Proof.
   unfold ASMSMpax; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply Asms_mpaxinfo_isr_is_irrel; eauto.
Qed.

(* Ases_mpaxinfo *)
Lemma Ases_mpaxinfo_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Ases_mpaxinfo vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Ases_mpaxinfo vl.
Proof.
   unfold Ases_mpaxinfo; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   eapply is_isr_irrel_Aarray; eauto.
Qed.

(* ASESMpax *)
Lemma ASESMpax_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ASESMpax vl abs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ASESMpax vl abs.
Proof.
   unfold ASESMpax; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply Ases_mpaxinfo_isr_is_irrel; eauto.
Qed.

(* Axmpaxinfo *)
Lemma Axmpaxinfo_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Axmpaxinfo vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Axmpaxinfo vl.
Proof.
   unfold Axmpaxinfo; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   eapply is_isr_irrel_Aarray; eauto.
Qed.

(* AXMpax *)
Lemma AXMpax_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AXMpax vl abs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AXMpax vl abs.
Proof.
   unfold AXMpax; intros.
   sep split in H. simpljoin. sep split; auto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply Axmpaxinfo_isr_is_irrel; eauto.
Qed.

(* AMPAXs *)
Lemma AMPAXs_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AMPAXs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AMPAXs.
Proof.
   unfold AMPAXs; intros.
   do 6 destr_and_inst H v.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply ASMSMpax_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply ASESMpax_isr_is_irrel; eauto.
   eapply AXMpax_isr_is_irrel; eauto.
Qed.

(* AKsDomains' *)
Lemma AKsDomains'_isr_is_irrel :
   forall vl l a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDomains' (Vptr l) vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDomains' (Vptr l) vl.
Proof.
  induction vl; destruct l.
  simpl; auto.
  destruct a.
  unfold AKsDomains'; fold AKsDomains'.
  intros.
  sep normal in H; sep normal.
  sep destruct H; sep eexists.
  sep split in H; sep split; eauto.
  simpl_sat H; simpl_sat_goal ; simpljoin.
  do 6 eexists. splits; eauto.
  eapply is_isr_irrel_Aarray; eauto.
  do 6 eexists. splits; eauto.
  eapply node_offt_isr_is_irrel; eauto.
Qed.

(* AKsDomains *)
Lemma AKsDomains_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AKsDomains vl abs-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AKsDomains vl abs.
Proof.
   unfold AKsDomains; intros.
   destr_and_inst H v.
   sep split in H; sep split; eauto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply AKsDomains'_isr_is_irrel; eauto.
Qed.

(* AsystemStck' *)
Lemma AsystemStck'_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AsystemStck' vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AsystemStck' vl.
Proof.
   unfold AsystemStck'; intros.
   destr_and_inst H v.
   sep split in H; sep split; eauto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply is_isr_irrel_Aarray; eauto.
Qed.

(* APartArea' *)
Lemma APartArea'_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= APartArea' vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= APartArea' vl.
Proof.
   unfold APartArea'; intros.
   destr_and_inst H v.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply is_isr_irrel_node; eauto.
Qed.

(* APartArea *)
Lemma APartArea_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= APartArea vl abs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= APartArea vl abs.
Proof.
   unfold APartArea; intros.
   sep split in H; sep split; eauto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply APartArea'_isr_is_irrel; eauto.
Qed.

(* APartID2Dom *)
Lemma APartID2Dom_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= APartID2Dom vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= APartID2Dom vl.
Proof.
   unfold APartID2Dom; intros.
  do 2 destr_and_inst H m .
  sep split in H; sep split; auto.
  simpl_sat H; simpl_sat_goal; simpljoin1.
  do 4 eexists.
  unfold empst.
  unfold emptaskst, emposabst.
  splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold GAarray in *.
  destr_and_inst H3 v.
  solve_sat H3.
  eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma ARootTaskStk_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl abs,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ARootTaskStk vl abs -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ARootTaskStk vl abs.
Proof.
   unfold ARootTaskStk, ARootTaskStk'; intros.
   sep split in H; sep split; eauto.
   simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply is_isr_irrel_Aarray_new; eauto.
Qed.

Lemma AXMPFR_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AXMPFR -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AXMPFR.
Proof.
   unfold AXMPFR; intros.
   do 2 destr_and_inst H v.
   sep split in H; sep split; eauto.
Qed.

Lemma AMDMAER_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AMDMAER ->
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AMDMAER.
Proof.
   unfold AMDMAER; intros.
   sep split in H; sep split; eauto.
Qed.

(* AOSPortAttrTbl' *)
Lemma AOSPortAttrTbl'_isr_is_irrel :
   forall a b c ir ir' ier ier' ie si si' cs x aop vl,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSPortAttrTbl' vl -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSPortAttrTbl' vl.
Proof.
   unfold AOSPortAttrTbl'; intros.
   destr_and_inst H v.
   elim_sep_conj1 H _H.
   do 6 eexists. splits; eauto.
   sep split in H; sep split; eauto.
   eapply is_isr_irrel_Aarray_new; eauto.
Qed.

(* end add by CNU *)

Lemma PartitionInv_isr_is_irrel1:
  forall a b c ir ir' ier ier' ie si si' cs x aop ecbls,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= PartitionInv_part1 ecbls-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= PartitionInv_part1 ecbls.
Proof.
  introv Hsat.
  unfold PartitionInv_part1 in *.
  sep normal in Hsat. sep normal.
  sep destruct Hsat.
  exists x0 x1 x2 x3 x4 x5. 
  exists x6 x7 x8 x9 x10 x11.
  exists x12 x13 x14 x15 x16 x17.
  exists x18 x19 x20 x21 x22.
  sep split in Hsat.
  sep split;auto.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8.

  sep remember (1::nil)%nat in Hsat.
  simpl_sat Hsat; simpl_sat_goal.
  simpljoin1. 
  do 6 eexists; repeat(split; eauto).
  eapply AOSDomainPortPtrList_isr_is_irrel;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply AOSKernelPortIDTbl_isr_is_irrel;eauto.

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear -H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply AOSChannelIDTbl_isr_is_irrel;eauto.

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply AOSKernelPortFreeList_isr_is_irrel;eauto.

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply AOSChannelFreeList_isr_is_irrel;eauto.

  clear - H5.
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply OtherPortPtrList_isr_is_irrel;eauto.
Qed.

Lemma PartitionInv_isr_is_irrel2:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= PartitionInv_part2 -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= PartitionInv_part2.
Proof.
   unfold PartitionInv_part2; intros.
   do 26 destr_and_inst H v.
   sep split in H; sep split; eauto.
    simpl_sat H; simpl_sat_goal ; simpljoin.
   do 6 eexists. splits; eauto.
   eapply ARootTaskStk_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply AMPAXs_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply AucosConf_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply Adomain2index_isr_is_irrel; eauto.
   do 10 (do 6 eexists; splits; eauto).
   do 6 eexists. splits; eauto.
   eapply AKsDomSchedule_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply AIntPartMux_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply AKsDomains_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply AsystemStck'_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   do 6 eexists. splits; eauto.
   eapply APartArea_isr_is_irrel; eauto.
   do 6 eexists. splits; eauto.
   eapply APartID2Dom_isr_is_irrel; eauto.
   eapply AOSPortAttrTbl'_isr_is_irrel; eauto.
Qed.


Lemma sat_sep_conj_comm1 :
  forall e e0 M i ier l O a P Q M1 M2 O1 O2,
    join M1 M2 M /\ join O1 O2 O ->
    (e, e0, M1, i, ier, l, O1, a) |= P ->
    (e, e0, M2, i, ier, l, O2, a) |= Q ->
    (e, e0, M, i, ier, l, O, a) |= P ** Q.
Proof.
  intros.
  simpl; simpljoin.
  do 6 eexists; repeat (split; eauto).
Qed.

Lemma PartitionInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop els,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= PartitionInv els -> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= PartitionInv els.
Proof.
intros.
rewrite PartitionInv_eq in *.
elim_sep_conj1 H _H.
eapply sat_sep_conj_comm1; eauto.
eapply PartitionInv_isr_is_irrel1; eauto.
eapply PartitionInv_isr_is_irrel2; eauto.
Qed.

(* CapabilityInv isr_is_irrel *)

Lemma sat_star_rev: 
  forall s p q M1 M2 M o1 o2 o , 
                             M = getmem s /\  join M1 M2 M
                            /\ o = getabst s /\ join o1 o2 o
                           /\ sat (substmo s  M1 o1) p
                           /\ sat (substmo s  M2 o2) q ->
  s |= p ** q .
  
Proof.
  intros.
  unfold sat. fold sat.  eauto. simpljoin.
  do 6 eexists. splits; eauto. 
Qed.
Lemma ASlots_isr_is_irrel:
  forall   vl n add a b c ir ir' ier ier' ie si si' cs x aop, 
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ASlots add n vl ->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ASlots add n vl.
Proof.
  induction vl; destruct n; intros.
  simpl in H. 
  simpl. auto. 
  simpl in H. tryfalse.
  simpl in H. destruct a; tryfalse.
  unfold ASlots in H.  
  fold ASlots in H. destruct a, add. 
  unfold ASlots. fold ASlots.
  simpl_sat H; simpl_sat_goal; simpljoin.
  simpl in H3.
  simpljoin. simpl.
  do 6 eexists. splits; eauto.
  do 6 eexists. splits; eauto. 
  unfold ACap in *.
  destruct p, c0, p.
  simpl in H8. simpl. simpljoin.
  do 6 eexists. splits; eauto.
  do 6 eexists. splits; eauto.
  do 6 eexists. splits; eauto.
  do 6 eexists. splits; eauto.
Qed.

Lemma Acnode_isr_is_irrel:
  forall  v  add a b c ir ir' ier ier' ie si si' cs x aop, 
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= Acnode add v ->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= Acnode add v.   
Proof. 
  intros.
  unfold Acnode in *.
  destruct v. destruct p. 
  destruct add. destruct H. 
  simpljoin. simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  destruct H4. 
  simpljoin. simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  simpl in H6. simpljoin. sep split in H7.
  eapply sat_star_rev.
  splits; eauto.
  eapply sat_star_rev.
  splits; eauto.  simpl. 
  splits; eauto. 
  simpl substmo.
  sep split; eauto. 
  eapply ASlots_isr_is_irrel; eauto.
Qed.



Lemma ACSpace_isr_is_irrel :
forall v1 v2  add a b c ir ir' ier ier' ie si si' cs x aop,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ACSpace add v1 v2 ->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ACSpace add v1 v2.
Proof.
  intros.
  unfold ACSpace in *.
  destruct v1, p, p, p, add. 
  sep split in H. sep split; eauto.
  destruct H. 
  simpljoin. simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto. 
  simpl substmo.
  eapply Acnode_isr_is_irrel; eauto. 
  destruct H8. 
  simpljoin. simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto.
  destruct H12. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto.
  simpl substmo. eapply is_isr_irrel_Aarray; eauto.
Qed.

Lemma ACSpaceAarrayTptr_isr_is_irrel :
forall  v1 v2 v3 n a b c ir ir' ier ier' ie si si' cs x aop,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= ACSpaceAarrayTptr n v1 v2 v3 ->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= ACSpaceAarrayTptr n v1 v2 v3.     
Proof.
  induction v1; destruct v2; destruct n; intros.
  simpl in H. simpl. auto. 
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. tryfalse.
  simpl in H. destruct a; tryfalse.
  simpl in H. destruct a; tryfalse.
  simpl in H. destruct a; tryfalse.
  unfold ACSpaceAarrayTptr. fold ACSpaceAarrayTptr.
  destruct a. simpl in H. tryfalse.
  simpl in H. eauto. 
  simpl in H. tryfalse.
  eapply ACSpaceAarrayTptr_succ_imp_help in H. 
  destruct H. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  unfold ACSpaceAarrayTptr in H3. 
  eapply astar_r_aemp_elim in H3.
  eapply sat_star_rev.
  splits; eauto. 
  simpl substmo.
  eapply ACSpace_isr_is_irrel; eauto.
Qed.
Lemma AOSCSpacePrioTbl_unfold_help: 
  forall s x1 x2 x3 x4,
  s |= AOSCSpacePrioTbl x1 x2 x3 x4 ->
  s |= G& ios_cap_defs.OSCSpacePrioTbl @
  Tarray (Tptr ios_cap_defs.CSPACE) 64 == x1 **
  Aarray x1 (Tarray (Tptr ios_cap_defs.CSPACE) 64) x2 **
  ACSpaceAarrayTptr 64 x2 x3 x4 **
  [|length x2 = 64 /\
    length x3 = 64 /\
    array_type_vallist_match (Tptr ios_cap_defs.CSPACE) x2|].
Proof.
  intros. unfold AOSCSpacePrioTbl in H. 
  auto. 
Qed.

Lemma AOSCSpacePrioTbl_fold_help: 
  forall s x1 x2 x3 x4, 
  s |= G& ios_cap_defs.OSCSpacePrioTbl @
  Tarray (Tptr ios_cap_defs.CSPACE) 64 == x1 **
  Aarray x1 (Tarray (Tptr ios_cap_defs.CSPACE) 64) x2 **
  ACSpaceAarrayTptr 64 x2 x3 x4 **
  [|length x2 = 64 /\
    length x3 = 64 /\
    array_type_vallist_match (Tptr ios_cap_defs.CSPACE) x2|] ->
    s |= AOSCSpacePrioTbl x1 x2 x3 x4.
Proof.
  intros. unfold AOSCSpacePrioTbl.
  auto. 
Qed.

Lemma  AOSCSpacePrioTbl_isr_is_irrel :
forall x1 x2 x3 x4 a b c ir ir' ier ier' ie si si' cs x aop,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSCSpacePrioTbl x1 x2 x3 x4 ->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSCSpacePrioTbl x1 x2 x3 x4.
Proof.
  unfold AOSCSpacePrioTbl. intros.
  sep split in H. sep split; eauto.
  eapply sat_star in H. 
  simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto.
  simpl substmo.
  eapply sat_star in H5.
  simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto.
  simpl substmo.
  eapply is_isr_irrel_Aarray; eauto.
  simpl substmo.
  eapply ACSpaceAarrayTptr_isr_is_irrel. eauto.
Qed.

Lemma AOSCSpaceObjectPointer_isr_is_irrel:
  forall  a b c ir ir' ier ier' ie si si' cs x aop l,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSCSpaceObjectPointer l->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSCSpaceObjectPointer l.
Proof.
  intros.
  unfold AOSCSpaceObjectPointer in *.
  sep split in H. sep split; eauto. 
  unfold GAarray in *.
  destruct H. destruct H. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  simpl in H4. simpljoin. 
  eexists. eapply sat_star_rev. splits; eauto. 
  simpl. eauto. 
  simpl substmo. eapply is_isr_irrel_Aarray; eauto. 
Qed.

Lemma AOSCSpaceCapParent_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop v,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= AOSCSpaceCapParent v->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= AOSCSpaceCapParent v.
Proof.
  unfold AOSCSpaceCapParent. intros.
  sep split in H. sep split; eauto. 
  unfold GAarray in *.
  destruct H. destruct H. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  simpl in H4. simpljoin. 
  eexists. eapply sat_star_rev. splits; eauto. 
  simpl. eauto. 
  simpl substmo. eapply is_isr_irrel_Aarray; eauto. 
Qed.




Lemma CSpaceGVars_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop,
  (a, b, c, ir, ier, (ie, si, cs), x, aop) |= CSpaceGVars->
  (a, b, c, ir', ier', (ie, si', cs), x, aop) |= CSpaceGVars.
Proof.
  unfold CSpaceGVars.
  intros.
  simpl_sat H; simpl_sat_goal; simpljoin.
  do 7 eexists. 
  simpl in H3, H8, H9. simpljoin.
  splits; eauto. 
  simpl. do 7 eexists.  splits; eauto. 
  do 7 eexists. splits; eauto. 
  simpl. do 7 eexists. splits; eauto. 
  eexists. simpl. do 7 eexists. splits; eauto.  
Qed.



Lemma CapabilityInv_isr_is_irrel:
  forall a b c ir ir' ier ier' ie si si' cs x aop acspace,
    (a, b, c, ir, ier, (ie, si, cs), x, aop) |= CapabilityInv acspace-> 
    (a, b, c, ir', ier', (ie, si', cs), x, aop) |= CapabilityInv acspace.
Proof.
  intros.
  unfold CapabilityInv in *.
  sep destruct H. sep eexists.
  sep split in H. sep split; eauto. 
  destruct H. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto. 
  eapply AOSCSpacePrioTbl_isr_is_irrel; eauto. 
  destruct H11. simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto.  simpl substmo.
  eapply AOSCSpaceObjectPointer_isr_is_irrel; eauto. 
  simpl substmo. 
  destruct H14. simpljoin.
  simpljoin.
  simpl substmo in *; simpl getmem in *; simpl getabst in *; simpl empst in *.
  eapply sat_star_rev. splits; eauto. 
  eapply AOSCSpaceCapParent_isr_is_irrel; eauto. 
Qed.


Lemma is_isr_APthreadAttr:
  forall a b c ir ir' ier ier' ie0 si si' cs0 x aop pattrb ,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= APthreadAttr pattrb ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= APthreadAttr pattrb .
Proof. 
  intros.
  unfold APthreadAttr in *.
  (* do 2 destr_and_inst H minfol . *)
  sep split in H; sep split; auto.
  (* simpl_sat H; simpl_sat_goal; simpljoin1.
  do 5 eexists; repeat (split; eauto). 
  do 6 eexists. split; eauto. split; eauto. apply join_comm . 
  apply join_emp.  eauto. split. eauto. split. apply join_comm . apply join_emp. eauto. 
  split. eapply is_isr_irrel_Aarray_new. eauto.
  split; eauto.
  simpl. split; eauto. unfold emposabst. auto. *)
Qed.

(*main lemma*)
Lemma OSInv_isr_is_irrel :
  forall a b c ir ir' ier ier' ie0 si si' cs0 x aop,
    (a, b, c, ir, ier, (ie0, si, cs0), x, aop) |= OSInv -> isr_is_prop ir' si' ->
    (a, b, c, ir', ier', (ie0, si', cs0), x, aop) |= OSInv.
(*     (a, b, c, ir', ier, (ie0, si', cs0), x, aop) |= OSInv. *)
Proof.
  unfold OSInv; intros.
  rename H0 into Hxxx.
  do 21 destr_and_inst H v.
  (* AOSMapTbl *)
  sep remember (1::nil)%nat in H.
  simpl_sat H; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.
  unfold AOSMapTbl in *; unfold GAarray in *.
  destr_and_inst H4 v.
  simpl_sat H4; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5 Hxxx.
  (* AOSUnMapTbl *)
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.
  unfold AOSUnMapTbl in *; unfold GAarray in *.
  destr_and_inst H4 v.
  simpl_sat H4; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5 Hxxx.
  (* AOSTCBPrioTbl *)
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.
  unfold AOSTCBPrioTbl in *.
  sep split in H4; sep split; auto.
  simpl_sat H4; simpl_sat_goal; simpljoin1.

  do 6 eexists; repeat (split; eauto).
  unfold GAarray in *.
  destr_and_inst H7 v.
  simpl_sat H7; simpl_sat_goal; simpljoin1.
  do 6 eexists; repeat(split; eauto).
  eapply is_isr_irrel_Aarray; eauto.
  do 6 eexists; repeat(split; eauto).
  eexists; simpl in H12; simpl; eauto.
  do 6 eexists; repeat(split; eauto).
  eexists; simpl in H17; simpl; eauto.
  clear - H5 Hxxx.
  (* AOSTCBList' *)
  sep remember (1::nil)%nat in H5.
  simpl_sat H5; simpl_sat_goal.
  simpljoin1.
  do 6 eexists; repeat(split; eauto).
  clear - H4.

  unfold AOSTCBList' in *.
  destruct H4.
  left.
  do 4 destruct H.
  exists x0 x1 x2 x4.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  do 6 eexists; splits; eauto.
  eapply is_isr_tcbdllseg; eauto.
  do 6 eexists; splits; eauto.
  do 6 eexists; splits; eauto.
  eapply is_isr_tcbdllseg; eauto.  
  eapply is_isr_tcbdllflag; eauto.

  right.
  destruct H.
  exists x0.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  unfold tcblist in *.
  sep split in H15.
  sep split; auto.
  eapply is_isr_tcbdllseg; eauto.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_tcbdllflag; eauto.
  (* AOSTCBFreeList' *)
  clear - H5 Hxxx.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear - H4.
  unfold AOSTCBFreeList' in *.
  simpl_sat H4; simpljoin1.
  simpl_sat_goal.
  do 6 eexists; splits; eauto.
  destruct H4.
  left.
  unfold TCBFree_Not_Eq in *.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_sll; eauto.  
  eapply is_isr_sllfreeflag; eauto.

  right.
  unfold TCBFree_Eq in *.
  do 3 destruct H.
  exists x2 x6 x7.
  sep split in H.
  sep split; auto.
  simpl_sat H; simpljoin1.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_Astruct; eauto.
  do 6 eexists.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  do 10 eexists.
  splits; eauto.
  simpl in H28. simpl. destruct H28. split; eauto.
  do 6 eexists.
  splits; eauto.
  simpl in H33. simpl. destruct H33. split; eauto.
  do 6 eexists.
  splits; eauto.
  simpl in H38. simpl. destruct H38. split; eauto.
  simpl in H39. simpl. destruct H39. split; eauto.
  do 6 eexists.
  splits; eauto.
  eapply is_isr_irrel_sll; eauto.
  eapply is_isr_sllfreeflag; eauto.
  (* AOSRdyTblGrp *)
  clear - H5 Hxxx.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  clear - H4.
  unfold AOSRdyTblGrp in *.
  cancel_pure H4; clear - H4.
  solve_sat H4.
  unfold AOSRdyTbl in *.
  cancel_pure H3.
  unfold GAarray in *.
  destr_and_inst H3 v.
  solve_sat H3.
  eapply is_isr_irrel_Aarray; eauto.
  clear - H5 Hxxx.
  (* APthreadAttr *)
  sep remember ((6::nil)%nat) in H5.
  sep remember ((6::nil)%nat).
  solve_sat H5.
  clear H5. 
  (* EvtInv *)
  sep remember ((6::nil)%nat) in H6.
  sep remember ((6::nil)%nat).
  solve_sat H6.
  eapply EvtInv_isr_is_irrel; eauto. 
  clear H7. 
  (* end of EvtInv *)
  sep split in H8. sep split; eauto.
  sep remember (1::nil) in H8.
  solve_sat H8.
  clear H9.
  sep remember (1::nil) in H10.
  solve_sat H10.
  sep remember (1::nil) in H12.
  solve_sat H12.
  sep remember (1::nil) in H15.
  solve_sat H15.
  sep remember (1::nil) in H18.
  solve_sat H18.
  (* A_isr_is_prop *)
  clear - H21 Hxxx.
  sep remember (1::nil)%nat in H21.
  solve_sat H21. 
  simpl in H4; simpl; simpljoin1.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.
  unfolds; auto.
  (* IntInv *)
  clear - H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply IntInv_isr_is_irrel; eauto.

  (* TmrInv *)
  clear - H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply TmrInv_isr_is_irrel; eauto.

  (* CoreCommuInv *)
  clear - H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply CoreCommuInv_isr_is_irrel; eauto.

  (* PartitionInv *)
  clear - H5.
  sep remember (1::nil)%nat in H5.
  solve_sat H5.
  eapply PartitionInv_isr_is_irrel; eauto.
  (* CapabilityInv *)  
  eapply CapabilityInv_isr_is_irrel; eauto.

Qed.

(*----good inv asrt lemmas ----*)
Lemma GoodInvAsrt_Astruct' :
  forall vl l d, GoodInvAsrt (Astruct' l d vl).
Proof.
  inductions vl; intros.
  destruct d; simpl; auto.
  destruct d; simpl; auto.
  destruct t; destruct l; try solve [simpl; split; auto];
  try solve [simpl; apply IHvl].
Qed.

Lemma GoodInvAsrt_Astruct :
  forall vl l t, GoodInvAsrt (Astruct l t vl).
Proof.
  intros.
  destruct t; simpl; auto.
  apply GoodInvAsrt_Astruct'.
  apply GoodInvAsrt_Astruct'.
Qed.

Lemma GoodInvAsrt_Aarray' :
  forall vl l n t, GoodInvAsrt (Aarray' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; destruct l; simpl; auto.
Qed.

Lemma GoodInvAsrt_Aarray :
  forall vl l t, GoodInvAsrt (Aarray l t vl).
Proof.
  intros.
  destruct t; simpl; auto.
  apply GoodInvAsrt_Aarray'.
Qed.

Lemma GoodInvAsrt_AEventNode :
  forall v1 v2 v3 v4 v5,  GoodInvAsrt (AEventNode v1 v2 v3 v4 v5).
Proof.
  intros.
  unfold AEventNode; unfold GoodInvAsrt; fold GoodInvAsrt; split.

  unfold AOSEvent.
  unfold GoodInvAsrt; fold GoodInvAsrt; intros.
  repeat(split; auto).

  apply GoodInvAsrt_Astruct.

  apply GoodInvAsrt_Aarray.
  apply GoodInvAsrt_Aarray.
  unfold AEventData; destruct v5; try solve [simpl; auto].
  unfold GoodInvAsrt; fold GoodInvAsrt.
  repeat (split; auto).
  apply GoodInvAsrt_Astruct.
  apply GoodInvAsrt_Astruct.
  apply GoodInvAsrt_Aarray.
Qed.

Lemma GoodInvAsrt_dllseg :
  forall vl head headprev tail tailnext t prev next,
    GoodInvAsrt (dllseg head headprev tail tailnext vl t prev next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; split; auto.
  intros.
  repeat (split; auto).
  unfold Astruct; destruct t; simpl; auto.

  apply GoodInvAsrt_Astruct'.
  apply GoodInvAsrt_Astruct'.
Qed.

Lemma GoodInvAsrt_dllsegflag :
  forall vl head tailnext next,
    GoodInvAsrt (dllsegflag head tailnext vl next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; split; auto.
Qed.

Lemma GoodInvAsrt_tcbdllflag :
  forall vl head,
    GoodInvAsrt (tcbdllflag head vl).
Proof.
  intros.
  unfold tcbdllflag.
  apply GoodInvAsrt_dllsegflag.
Qed.

Lemma GoodInvAsrt_sllseg :
  forall l head tailnext t next,
    GoodInvAsrt (sllseg head tailnext l t next).
Proof.
  inductions l.
  simpl; auto.
  simpl; split; auto.
  intro.
  splits; auto.
  intro.
  split; auto.
  apply GoodInvAsrt_Astruct.
Qed.

Lemma GoodInvAsrt_sll :
  forall head l t next,
    GoodInvAsrt (sll head l t next).
Proof.
  intros.
  unfold sll.
  apply GoodInvAsrt_sllseg.
Qed.

Lemma GoodInvAsrt_sllsegfreeflag :
  forall vl head tailnext next,
    GoodInvAsrt (sllsegfreeflag head tailnext vl next).
Proof.
  inductions vl; intros.
  simpl; auto.
  simpl; intros.
  splits; auto.
Qed.

Lemma GoodInvAsrt_sllfreeflag :
  forall head l,
    GoodInvAsrt (sllfreeflag head l).
Proof.
  intros.
  unfold sllfreeflag.
  apply GoodInvAsrt_sllsegfreeflag.
Qed.


(*---end of auxiliary lemmas----*)

Lemma invprop : inv_prop OSInv.
Proof.
  unfolds.
  split.
  apply OSInv_precise. 
  unfolds.

  split; intros.
  destruct_s s; simpl set_isr_s.

  eapply OSInv_isr_is_irrel; eauto.
  get_isr_is_prop H. clear - H15.
  
  unfold isr_is_prop in *; intros.
  apply H15 in H.
  unfold isrupd.
  destruct(beq_nat i x); auto.

  split; intros.
  destruct_s s; simpl set_isisr_s.
  eapply OSInv_isr_is_irrel; eauto.
  get_isr_is_prop H; clear - H15.
  
  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct(beq_nat i x) eqn : eq1.
  false; apply H.
  simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H15.
  intro; apply H.
  simpl; right; auto.
  
  split; intros.
  destruct_s s; simpl set_is_s.
  simpl get_isr_s in H0; simpl get_is_s in H1.
  eapply OSInv_isr_is_irrel; eauto.
  get_isr_is_prop H; clear - H16 H0.
  unfold isr_is_prop in *; intros.
  destruct(beq_nat i x) eqn : eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H16.
  intro; apply H.
  simpl in H1; destruct H1; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.

  destruct_s s; simpl set_is_s.
  simpl get_isr_s in H0; substs.
  eapply OSInv_isr_is_irrel; eauto.
  unfolds; intros.
  unfold empisr; auto.
Qed.

(* GoodInvAsrt about EvtInv *)

Lemma GoodInvAsrt_pos_sllseg:
  forall vll hd pbls, GoodInvAsrt (pos_sllseg hd Vnull vll pbls). 
Proof.    
  inductions vll; intros.
  unfold pos_sllseg. simpl; auto.
  simpl. 
  destruct a; simpl.
  splits; auto.
  splits; auto.
  intros. splits; auto.
  destruct a; simpl; auto.
  split; auto.
  destruct a; simpl; auto.
Qed.

Hint Resolve GoodInvAsrt_pos_sllseg: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AEvAtomHeap:
  forall x26, GoodInvAsrt (AEvAtomHeap x26).
Proof.
  inductions x26; intros.
  unfold AEvAtomHeap. simpl; auto.
  simpl. 
  destruct a; simpl.
  destruct p; simpl.
  destruct t; simpl; eauto.
Qed.

Hint Resolve GoodInvAsrt_AEvAtomHeap: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AEvStructHeap:
  forall x26, GoodInvAsrt (AEvStructHeap x26).
Proof.
  inductions x26; intros.
  unfold AEvStructHeap. simpl; auto.
  simpl. 
  destruct a; simpl.
  destruct p; simpl.
  destruct t; simpl; eauto.
  splits; auto.
  eapply GoodInvAsrt_Astruct'.
Qed.

Hint Resolve GoodInvAsrt_AEvStructHeap: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AEvArrayHeap:
  forall x26, GoodInvAsrt (AEvArrayHeap x26).
Proof.
  inductions x26; intros.
  unfold AEvArrayHeap. simpl; auto.
  simpl. 
  destruct a; simpl.
  destruct p; simpl.
  splits; auto.
  eapply GoodInvAsrt_Aarray'.
Qed.

Hint Resolve GoodInvAsrt_AEvArrayHeap: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_err_sllseg:
  forall vll p t ebls, GoodInvAsrt (err_sllseg p t vll ebls).
Proof.
   inductions vll.
  intros. simpl. auto.

  intros.
  unfold err_sllseg. fold err_sllseg.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  splits; auto.
  unfold node.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros; splits; auto.
  apply GoodInvAsrt_Astruct.
Qed.

Hint Resolve GoodInvAsrt_err_sllseg: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AErrblkList:
  forall x26, GoodInvAsrt (AErrblkList x26).
Proof.
  inductions x26; intros.
  unfold AErrblkList. simpl; auto.
  intros; split; auto.
  intros.
  apply GoodInvAsrt_err_sllseg.
Qed.

Hint Resolve GoodInvAsrt_AErrblkList: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ecbf_sllseg:
  forall vl hd tn t, 
    GoodInvAsrt (ecbf_sllseg hd tn vl t V_OSEventListPtr).
Proof.
  inductions vl.
  intros. simpl. auto.

  intros.
  unfold ecbf_sllseg. fold ecbf_sllseg.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  splits; auto.
  simpl. intros. split; auto.
  apply GoodInvAsrt_Astruct.
  apply GoodInvAsrt_Aarray.
  apply GoodInvAsrt_Aarray. (* new add *)
Qed.

Hint Resolve GoodInvAsrt_ecbf_sllseg: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_qblkf_sllseg: 
  forall vll hd tn t, GoodInvAsrt (qblkf_sllseg hd tn vll t V_nextblk). 
Proof.
  inductions vll.
  intros. simpl. auto.

  intros.
  unfold qblkf_sllseg. fold qblkf_sllseg.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  splits; auto.
  simpl. intros. split; auto.
  apply GoodInvAsrt_Astruct.
  apply GoodInvAsrt_Aarray.
Qed.   

Hint Resolve GoodInvAsrt_qblkf_sllseg: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_evsllseg: 
  forall vl hd tn ecbls, GoodInvAsrt (evsllseg hd tn vl ecbls). 
Proof.
  inductions vl.
  intros.
  simpl. auto.
  intros. simpl evsllseg.
  destruct ecbls.
  simpl. auto.
  destruct a.
  destruct p.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros.
  split; auto.
  split.
  apply GoodInvAsrt_AEventNode.
  apply IHvl.
Qed. 

Hint Resolve GoodInvAsrt_evsllseg: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Aarray_new': 
  forall vll l m t, GoodInvAsrt (Aarray_new' l m t vll).
Proof.
  inductions vll.
  intros.
  destruct m.
  simpl. auto.
  simpl. auto.
  intros.
  destruct m.
  simpl. auto.
  simpl.
  destruct t eqn: et;
    try
      (destruct a; simpl; auto;
       destruct a; [destruct l; simpl; split; auto | simpl; auto]).
  destruct l.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. apply GoodInvAsrt_Aarray.
  apply IHvll.
  destruct l.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. apply GoodInvAsrt_Astruct.
  apply IHvll.
  destruct l.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  split. apply GoodInvAsrt_Astruct.
  apply IHvll.
Qed.

Hint Resolve GoodInvAsrt_Aarray_new': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_llsegevaux:
  forall l head locvl ptrvl, 
    GoodInvAsrt (llsegevaux head Vnull l locvl ptrvl V_OSTCBNext). 
Proof.
  inductions l.
  intros.
  simpl.
  destruct locvl; destruct ptrvl; tryfalse; simpl; auto.
  intros.
  simpl.
  destruct locvl; destruct ptrvl; tryfalse; simpl; auto. 
  intros.
  splits; auto. splits; auto.
Qed.

Hint Resolve GoodInvAsrt_llsegevaux: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AEvtCap:
  forall scapl l fieldname eibtype,
    GoodInvAsrt (AEvtCap l scapl fieldname eibtype). 
Proof.
  induction scapl; destruct l;
    unfold AEvtCap; fold AEvtCap.
  simpl; auto.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros.
  repeat try splits; auto.
  apply GoodInvAsrt_Aarray.
Qed.

Hint Resolve GoodInvAsrt_AEvtCap: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_EvtInv:
 forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl,
  GoodInvAsrt (EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl).
Proof.
  unfold EvtInv.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros.
  repeat try splits; auto.
  unfold GoodInvAsrt.
  unfold AOSEventFreeList. fold GoodInvAsrt.
  intros.
  split.
  simpl. auto.
  unfold ecbf_sll.
  apply GoodInvAsrt_ecbf_sllseg.
  unfold AOSQFreeList.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  split.
  simpl. auto.
  apply GoodInvAsrt_sll.
  unfold AOSQFreeBlk. 
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros.
  split.
  simpl. auto.
  apply GoodInvAsrt_qblkf_sllseg.
  unfold AECBList.
  unfold GoodInvAsrt. fold GoodInvAsrt.
  intros. split; auto.
  split. simpl. auto.
  apply GoodInvAsrt_evsllseg.
  apply GoodInvAsrt_AErrblkList.
  repeat try splits; auto.
  unfold APosblkList. unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. intros. apply GoodInvAsrt_pos_sllseg.
  apply GoodInvAsrt_AEvAtomHeap.
  apply GoodInvAsrt_AEvStructHeap.
  apply GoodInvAsrt_AEvArrayHeap.
  unfold ASemEIBs.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros; splits; auto.
  unfold ASeminfo.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. split; auto.
  unfold Aarray_new.
  apply GoodInvAsrt_Aarray_new'.
  unfold ASemCap.
  apply GoodInvAsrt_AEvtCap.
  unfold AMuxEIBs. 
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros; splits; auto.
  unfold APthreadMutex.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. split; auto.
  unfold Aarray_new.
  apply GoodInvAsrt_Aarray_new'.
  unfold AMuxCap.
  apply GoodInvAsrt_AEvtCap.
  unfold AMqEIBs.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros; splits; auto.
  unfold AMqAttr.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. split. simpl. auto. split; auto.
  unfold Aarray_new.
  apply GoodInvAsrt_Aarray_new'.
  unfold AMqCap.
  apply GoodInvAsrt_AEvtCap.
  unfold tcbllsegevaux. 
  unfold GoodInvAsrt. fold GoodInvAsrt.  
  apply GoodInvAsrt_llsegevaux.
Qed.

Hint Resolve GoodInvAsrt_EvtInv: GoodInvAsrt_lemmas.

(* Proof.  *)
(*   unfold EvtInv. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros. *)
(*   repeat try splits; auto. *)
(*   unfold GoodInvAsrt. *)
(*   unfold AOSEventFreeList. fold GoodInvAsrt. *)
(*   intros. *)
(*   split. *)
(*   simpl. auto. *)
(*   unfold ecbf_sll. *)
(*   apply GoodInvAsrt_ecbf_sllseg. *)
(*   unfold AOSQFreeList. *)
(*   unfold GoodInvAsrt. fold GoodInvAsrt. *)
(*   intros. *)
(*   split. *)
(*   simpl. auto. *)
(*   apply GoodInvAsrt_sll. *)
(*   unfold AOSQFreeBlk.  *)
(*   unfold GoodInvAsrt. fold GoodInvAsrt. *)
(*   intros. *)
(*   split. *)
(*   simpl. auto. *)
(*   apply GoodInvAsrt_qblkf_sllseg. *)
(*   unfold AECBList. *)
(*   unfold GoodInvAsrt. fold GoodInvAsrt. *)
(*   intros. split; auto. *)
(*   split. simpl. auto. *)
(*   apply GoodInvAsrt_evsllseg. *)
(*   apply GoodInvAsrt_AErrblkList. *)
(*   repeat try splits; auto. *)
(*   unfold APosblkList. unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros. split. simpl. auto. intros. apply GoodInvAsrt_pos_sllseg. *)
(*   apply GoodInvAsrt_AEvAtomHeap. *)
(*   apply GoodInvAsrt_AEvStructHeap. *)
(*   apply GoodInvAsrt_AEvArrayHeap. *)
(*   unfold ASemEIBs. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros; splits; auto. *)
(*   unfold ASeminfo. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros. split. simpl. auto. split; auto. *)
(*   unfold Aarray_new. *)
(*   apply GoodInvAsrt_Aarray_new'. *)
(*   admit. *)
(*   unfold AMuxEIBs.  *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros; splits; auto. *)
(*   unfold APthreadMutex. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros. split. simpl. auto. split; auto. *)
(*   unfold Aarray_new. *)
(*   apply GoodInvAsrt_Aarray_new'. *)
(*   admit. *)
(*   unfold AMqEIBs. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros; splits; auto. *)
(*   unfold AMqAttr. *)
(*   unfold GoodInvAsrt; fold GoodInvAsrt. *)
(*   intros. split. simpl. auto. split; auto. *)
(*   unfold Aarray_new. *)
(*   apply GoodInvAsrt_Aarray_new'. *)
(*   admit. *)
(*   unfold tcbllsegevaux.  *)
(*   unfold GoodInvAsrt. fold GoodInvAsrt.   *)
(*   apply GoodInvAsrt_llsegevaux. *)
(* Admitted. *)

(* end of GoodInvAsrt about EvtInv *)

Lemma GoodInvAsrt_IntInv:
  GoodInvAsrt (IntInv).
Proof.
  unfold IntInv.
  unfold AOSInthandler.
  unfold GAarray.
  unfold GoodInvAsrt; fold GoodInvAsrt.
  intros. splits;auto. 
  intros. split. simpl. auto.
  apply GoodInvAsrt_Aarray.
  unfold AOSInthandlerParam.
  unfold GAarray.
  unfold GoodInvAsrt; fold GoodInvAsrt.  
  intros. split. simpl. auto.
  apply GoodInvAsrt_Aarray.
  simpl; auto.
Qed.


(* add by SJTU *)
Theorem GoodInvAsrt_ex : forall [A: Type]  p , (forall x : A, GoodInvAsrt (p x)) -> GoodInvAsrt (EX (x: A), p x).
Proof.
  intros. cbn. auto.
Qed. 

Theorem GoodInvAsrt_star : 
  forall p q,  GoodInvAsrt p ->  GoodInvAsrt q -> 
              GoodInvAsrt (p ** q). 
Proof.
  introv Hp Hq.
  simpl; auto.
Qed.

Theorem GoodInvAsrt_aemp :
   GoodInvAsrt ( Aemp).
Proof.
  simpl; auto.
Qed.

Theorem GoodInvAsrt_adisj : forall p q,
   GoodInvAsrt p -> GoodInvAsrt q  -> GoodInvAsrt ( p \\// q).
Proof.
  simpl; auto.
Qed.

Hint Resolve 
    GoodInvAsrt_ex
    GoodInvAsrt_aemp
    GoodInvAsrt_star
    GoodInvAsrt_adisj
    : GoodInvAsrt_lemmas.

Ltac GoodInvAsrt_solver := 
  try unfold OSInv;
  try unfold AOSEventFreeList, AOSQFreeList, AOSQFreeBlk, AECBList;
  try unfold AOSMapTbl, AOSUnMapTbl, AOSTCBPrioTbl, AOSIntNesting, AOSTCBList', AOSTCBFreeList';
  try unfold AOSRdyTblGrp, AOSRdyTbl, AOSRdyGrp, AOSTime, AGVars;
  try unfold AOSEvent, AOSEventTbl, AMsgData, AOSQCtr, AOSQBlk, node;
  try unfold GAarray;
  try unfold tcblist; try unfold tcbdllseg;
  try unfold TCBFree_Eq; try unfold TCBFree_Not_Eq;
  match goal with
    | |-  GoodInvAsrt ?p =>
      match p with
          | Aexists _  => apply  GoodInvAsrt_ex; intros;  GoodInvAsrt_solver
          | ?p1 ** ?p2 => apply  GoodInvAsrt_star; GoodInvAsrt_solver
          | _ \\// _ => apply GoodInvAsrt_adisj; GoodInvAsrt_solver
          | A_isr_is_prop => simpl;auto
          | _ =>   first [auto with GoodInvAsrt_lemmas | simpl; auto]
      end
    | _ => idtac
end.

Hint Resolve
    GoodInvAsrt_tcbdllflag
    GoodInvAsrt_sllfreeflag
    GoodInvAsrt_AEventNode
    GoodInvAsrt_Astruct
    GoodInvAsrt_Astruct' 
    GoodInvAsrt_Aarray'
    GoodInvAsrt_Aarray
    GoodInvAsrt_sllsegfreeflag
    GoodInvAsrt_dllsegflag
    GoodInvAsrt_sll
    GoodInvAsrt_sllseg
    GoodInvAsrt_dllseg
        : GoodInvAsrt_lemmas.

Hint Resolve  GoodInvAsrt_IntInv
              GoodInvAsrt_EvtInv : GoodInvAsrt_lemmas.


Theorem GoodInvAsrt_Aptrmapsto :
forall l t p v,
   GoodInvAsrt (Aptrmapsto l t p v).
Proof.
  simpl; auto.
Qed.

Theorem gooinv_Agvarenv': forall x t l, GoodInvAsrt (Agvarenv' x t l).
Proof. simpl; auto. Qed.

Theorem gooinv_GV: forall x t v, GoodInvAsrt (GV x @ t |-> v).
Proof. simpl; auto. Qed.

Theorem gooinv_GV_ro: forall x t v, GoodInvAsrt (GV x @ t |-r-> v).
Proof. simpl; auto. Qed.


Hint Resolve
    GoodInvAsrt_Aptrmapsto
    gooinv_Agvarenv'
    gooinv_GV
    gooinv_GV_ro
        : GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSTMRNode :
  forall v l,
    GoodInvAsrt (AOSTMRNode v l).
Proof.
  intros.
  unfold AOSTMRNode.
  GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_AOSTMRNode: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSTMRList' :
  forall l,
    GoodInvAsrt (AOSTMRList' l).
Proof.
  intros.
  unfold AOSTMRList'.
  GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_AOSTMRList': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSTMRList_TMRused :
  forall l1 l2 l3 absl,
    GoodInvAsrt (AOSTMRList_TMRused l1 l2 l3 absl).
Proof.
  intros.
  unfold AOSTMRList_TMRused,AOSTMRIDUsed.
  GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSTMRList_TMRused: GoodInvAsrt_lemmas.


Lemma GoodInvAsrt_AOScoreheapl :
  forall l,
    GoodInvAsrt (AOScoreheapl l).
Proof.
  induction l;intros.
  simpl;auto.
  simpl. destruct a;destruct p. GoodInvAsrt_solver. 
Qed.
Hint Resolve GoodInvAsrt_AOScoreheapl: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOScoreheape :
  forall l,
    GoodInvAsrt (AOScoreheape l).
Proof.
  induction l;intros.
  simpl;auto.
  simpl. destruct a;destruct p. GoodInvAsrt_solver. 
Qed.
Hint Resolve GoodInvAsrt_AOScoreheape: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOScoreheapt :
  forall l,
    GoodInvAsrt (AOScoreheapt l).
Proof.
  induction l;intros.
  simpl;auto.
  simpl. destruct a;destruct p. GoodInvAsrt_solver. 
Qed.
Hint Resolve GoodInvAsrt_AOScoreheapt: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AdynrefaccfgFreeList :
  forall p l,
    GoodInvAsrt (AdynrefaccfgFreeList p l ).
Proof.
  intros. unfold AdynrefaccfgFreeList.
  GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_AdynrefaccfgFreeList: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Adynheap:
  forall l,
    GoodInvAsrt (Adynheap l).
Proof.
  induction l;intros.
  simpl;auto.
  destruct a. cbn [Adynheap]. GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_Adynheap: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Memory_Node :
  forall l n a,
    GoodInvAsrt (Memory_Node n a l).
Proof.
  intros.
  unfold Memory_Node.  GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_Memory_Node: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Memory_sigcore_aux :
  forall l n a,
    GoodInvAsrt (Memory_sigcore_aux n a l).
Proof.
  induction l;intros.
  simpl;auto.
  cbn [Memory_sigcore_aux]. GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_Memory_sigcore_aux: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Memory_sigcore :
  forall l a,
    GoodInvAsrt (Memory_sigcore a l).
Proof.
  intros. unfold Memory_sigcore ;GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_Memory_sigcore: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSIPCMem_aux :
  forall l1 l2,
    GoodInvAsrt (AOSIPCMem_aux l1 l2).
Proof.
  induction l1;intros.
  simpl;destruct l2;simpl;auto.
  simpl. destruct a;destruct l2; GoodInvAsrt_solver. 
Qed.
Hint Resolve GoodInvAsrt_AOSIPCMem_aux: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSIPCGRinfo :
  forall m,
    GoodInvAsrt (AOSIPCGRinfo m).
Proof.
  intros. unfold AOSIPCGRinfo ;GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_AOSIPCGRinfo: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_TmrInv:
  GoodInvAsrt (TmrInv).
Proof.
  intros. unfold TmrInv, TmrInv', HeapInv', AOSClkRate. 
  GoodInvAsrt_solver.
Qed.
Hint Resolve GoodInvAsrt_TmrInv: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_DynamicRefactorINV:
forall vl, GoodInvAsrt (DynamicRefactorINV vl).
Proof.
  intros;unfold DynamicRefactorINV.
  GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_DynamicRefactorINV: GoodInvAsrt_lemmas.


Lemma GoodInvAsrt_CoreCommuInv:
  forall vl, GoodInvAsrt (CoreCommuInv vl).
Proof.
  intros. unfold CoreCommuInv, AOSIPCMem, AOSIPCSem, AOSIPCSendSem, AOSIPCSemShared,AOSIPCBroadList.
  GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_CoreCommuInv: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_dmportp_sllseg_qport_msg : forall dportl pnow pend qstart qend qentries, GoodInvAsrt (dmportp_sllseg_qport_msg pnow pend qstart qend qentries dportl).
Proof.
  induction dportl;intros.  
  - destruct qentries; cbn [dmportp_sllseg_qport_msg];GoodInvAsrt_solver.
  - destruct qentries; cbn [dmportp_sllseg_qport_msg];GoodInvAsrt_solver. 
Qed.

Hint Resolve GoodInvAsrt_dmportp_sllseg_qport_msg: GoodInvAsrt_lemmas.

Lemma  GoodInvAsrt_AOSDomainPortPtrList : forall x x0 x1, GoodInvAsrt (AOSDomainPortPtrList x x0 x1).
Proof.
  intros. unfold AOSDomainPortPtrList. GoodInvAsrt_solver.
  revert x x1. 
  unfold dmportp_sll. induction x0;intros.
  - destruct x1;cbn;auto.
  - destruct x1;cbn [dmportp_sllseg];auto.
    cbn;auto.
    GoodInvAsrt_solver.
    + unfold APortStruct. GoodInvAsrt_solver.
    + unfold dmportp_sllseg_sampleport_msg. GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSDomainPortPtrList: GoodInvAsrt_lemmas.

Lemma  GoodInvAsrt_AOSKernelPortIDTbl : forall kportvl kportl, GoodInvAsrt (AOSKernelPortIDTbl kportvl kportl).
Proof.
  intros. unfold AOSKernelPortIDTbl. GoodInvAsrt_solver.
  revert kportl. 
  induction kportvl;intros.
  - destruct kportl;cbn;auto.
  - destruct kportl;cbn [kportNode_P];auto.
    cbn;auto.
    GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSKernelPortIDTbl: GoodInvAsrt_lemmas.

Lemma  GoodInvAsrt_AOSChannelIDTbl : forall x x0 x1, GoodInvAsrt (AOSChannelIDTbl x x0 x1).
Proof.
  intros. unfold AOSChannelIDTbl. GoodInvAsrt_solver.
  revert x0 x1. 
  induction x;intros.
  - destruct x0,x1;cbn;auto.
  - destruct x0,x1;cbn [ChannelNode];GoodInvAsrt_solver.
    remember (Z.to_nat (Int.unsigned x3)) as n. 
    clear. 
    revert x2 n. 
    induction l;intros.
    + destruct n;cbn;auto.
    + destruct n;cbn [Channel_dstkport_get];GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSChannelIDTbl: GoodInvAsrt_lemmas.


Lemma  GoodInvAsrt_AOSKernelPortFreeList : forall x x0, GoodInvAsrt (AOSKernelPortFreeList x x0).
Proof.
  intros. unfold AOSKernelPortFreeList. GoodInvAsrt_solver.
  revert x.  unfold kportf_sll.
  induction x0;intros.
  - cbn;auto.
  - cbn [kportf_sllseg ];GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSKernelPortFreeList: GoodInvAsrt_lemmas.


Lemma  GoodInvAsrt_AOSChannelFreeList : forall x x0, GoodInvAsrt (AOSChannelFreeList x x0).
Proof.
  intros. unfold AOSChannelFreeList. GoodInvAsrt_solver.
  revert x.  unfold channelf_sll.
  induction x0;intros.
  - cbn;auto.
  - cbn [channelf_sllseg ];GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSChannelFreeList: GoodInvAsrt_lemmas.


Lemma  GoodInvAsrt_OtherPortPtrList : forall x x0 x1, GoodInvAsrt (OtherPortPtrList x x0 x1).
Proof.
  induction x;intros.
  - destruct x0,x1;cbn;auto.
  - destruct x0,x1;cbn [OtherPortPtrList];GoodInvAsrt_solver.
    + unfold APortStruct. GoodInvAsrt_solver.
    + unfold dmportp_sllseg_sampleport_msg. GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_OtherPortPtrList: GoodInvAsrt_lemmas.

(* add by CNU *)

Lemma GoodInvAsrt_AKsDSchdidx:
 forall x, GoodInvAsrt (AKsDSchdidx x).
Proof.
 intros.
 unfold AKsDSchdidx.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDSchdidx: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDSchdlen:
  forall x,  GoodInvAsrt (AKsDSchdlen x).
Proof.
 intros.
 unfold AKsDSchdlen.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDSchdlen: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsCurDomain:
  forall x,  GoodInvAsrt (AKsCurDomain x).
Proof.
 intros.
 unfold AKsCurDomain.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsCurDomain: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsLastDomain:
 forall x,   GoodInvAsrt (AKsLastDomain x).
Proof.
 intros.
 unfold AKsLastDomain.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsLastDomain: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDomainTime:
   forall x, GoodInvAsrt (AKsDomainTime x).
Proof.
 intros.
 unfold AKsDomainTime.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDomainTime: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDomSchedule':
   forall x, GoodInvAsrt (AKsDomSchedule' x).
Proof.
 intros.
 unfold AKsDomSchedule'.
 unfold Aarray_new.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDomSchedule': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDomSchedule:
   forall x x0, GoodInvAsrt (AKsDomSchedule x x0).
Proof.
 intros.
 unfold AKsDomSchedule.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDomSchedule: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AIntPartMux':
  forall x,  GoodInvAsrt (AIntPartMux' x).
Proof.
 intros.
 unfold AIntPartMux'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AIntPartMux': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AIntPartMux:
  forall x x0,  GoodInvAsrt (AIntPartMux x x0).
Proof.
 intros.
 unfold AIntPartMux.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AIntPartMux: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Adomain2index:
  forall x x0, GoodInvAsrt (Adomain2index x x0).
Proof.
 intros.
 unfold Adomain2index.
 unfold Adomain2index'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_Adomain2index: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AIntrDomainMux:
  forall x x0 x1,  GoodInvAsrt (AIntrDomainMux x x0 x1).
Proof.
 intros.
 unfold AIntrDomainMux.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AIntrDomainMux: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_node_offt:
  forall x x0 x1,  GoodInvAsrt (node_offt x x0 x1).
Proof.
 intros.
 unfold node_offt.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_node_offt: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AAllArea:
  forall x x0 x1,  GoodInvAsrt (AAllArea x x0 x1).
Proof.
 intros.
 unfold AAllArea.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AAllArea: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AchannelTbl':
  forall x0 x,  GoodInvAsrt (AchannelTbl' x x0).
Proof.
 induction x0; intros;
 unfold AchannelTbl';
 fold AchannelTbl';
 try destruct a;
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AchannelTbl': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AChannelTbl:
  forall x x0 x1,  GoodInvAsrt (AChannelTbl x x0 x1).
Proof.
 intros.
 unfold AChannelTbl.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AChannelTbl: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AportTbl':
  forall x0 x,  GoodInvAsrt (AportTbl' x x0).
Proof.
 induction x0; intros;
 unfold AportTbl';
 fold AportTbl';
 try destruct a;
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AportTbl': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_APortTbl:
  forall x x0 x1,  GoodInvAsrt (APortTbl x x0 x1).
Proof.
 intros.
  unfold APortTbl.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_APortTbl: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AksDomSchedule':
  forall x0 x,  GoodInvAsrt (AksDomSchedule' x x0).
Proof.
 induction x0; intros;
 unfold AksDomSchedule';
 fold AksDomSchedule';
 try destruct a;
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AksDomSchedule': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ADeviceioTbl':
  forall x0 x,  GoodInvAsrt (ADeviceioTbl' x x0).
Proof.
 induction x0; intros;
 unfold ADeviceioTbl';
 fold ADeviceioTbl';
 try destruct a;
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ADeviceioTbl': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AksDomains':
  forall x0 x,  GoodInvAsrt (AksDomains' x x0).
Proof.
 induction x0; intros;
 unfold AksDomains';
 fold AksDomains';
 try destruct a as [[[]]];
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AksDomains': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Acpus':
  forall x0 x,  GoodInvAsrt (Acpus' x x0).
Proof.
 induction x0; intros;
 unfold Acpus';
 fold Acpus';
 try destruct a as [[[]]];
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_Acpus': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ACPUs:
  forall x x0 x1,  GoodInvAsrt (ACPUs x x0 x1).
Proof.
 intros.
 unfold ACPUs.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ACPUs: GoodInvAsrt_lemmas.


Lemma GoodInvAsrt_AucosConf:
  forall x x0,  GoodInvAsrt (AucosConf x x0).
Proof.
 intros.
  unfold AucosConf.
 destruct x as [[[[[[]]]]]].
 destruct x0 as [[[[[[[[[[[[[]]]]]]]]]]]]].
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AucosConf: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Asms_mpaxinfo:
  forall x,  GoodInvAsrt (Asms_mpaxinfo x).
Proof.
 intros.
  unfold Asms_mpaxinfo.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_Asms_mpaxinfo: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ASMSMpax:
  forall x x0,  GoodInvAsrt (ASMSMpax x x0).
Proof.
 intros.
  unfold ASMSMpax.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ASMSMpax: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Ases_mpaxinfo:
  forall x,  GoodInvAsrt (Ases_mpaxinfo x).
Proof.
 intros.
  unfold Ases_mpaxinfo.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_Ases_mpaxinfo: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ASESMpax:
  forall x x0,  GoodInvAsrt (ASESMpax x x0).
Proof.
 intros.
  unfold ASESMpax.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ASESMpax: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_Axmpaxinfo:
  forall x,  GoodInvAsrt (Axmpaxinfo x).
Proof.
 intros.
  unfold Axmpaxinfo.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_Axmpaxinfo: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AXMpax:
  forall x x0,  GoodInvAsrt (AXMpax x x0).
Proof.
 intros.
  unfold AXMpax.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AXMpax: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AMPAXs:
  GoodInvAsrt (AMPAXs).
Proof.
 intros.
  unfold AMPAXs.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AMPAXs: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AisChangePartion:
  forall x, GoodInvAsrt (AisChangePartion x).
Proof.
 intros.
  unfold AisChangePartion.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AisChangePartion: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDomains':
  forall x0 x, GoodInvAsrt (AKsDomains' x x0).
Proof.
 induction x0.
 simpl; auto.
 destruct a.
 intros.
 unfold AKsDomains'; fold AKsDomains'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDomains': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AKsDomains:
  forall x x0, GoodInvAsrt (AKsDomains x x0).
Proof.
 intros.
  unfold AKsDomains.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AKsDomains: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AisCoreBoot:
  forall x, GoodInvAsrt (AisCoreBoot x).
Proof.
 intros.
  unfold AisCoreBoot.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AisCoreBoot: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AsystemStck':
  forall x, GoodInvAsrt (AsystemStck' x).
Proof.
 intros.
  unfold AsystemStck'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AsystemStck': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSSystemSP:
  forall x, GoodInvAsrt (AOSSystemSP x).
Proof.
 intros.
  unfold AOSSystemSP.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AOSSystemSP: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ACorepartnum':
  forall x, GoodInvAsrt (ACorepartnum' x).
Proof.
 intros.
  unfold ACorepartnum'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ACorepartnum': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ACorepartnum:
  forall x, GoodInvAsrt (ACorepartnum x).
Proof.
 intros.
  unfold ACorepartnum.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ACorepartnum: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_APortnumcur:
   GoodInvAsrt (APortnumcur).
Proof.
 intros.
  unfold APortnumcur.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_APortnumcur: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_APartArea':
  forall x, GoodInvAsrt (APartArea' x).
Proof.
 intros.
 unfold APartArea'.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_APartArea': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_APartArea:
  forall x x0, GoodInvAsrt (APartArea x x0).
Proof.
 intros.
  unfold APartArea.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_APartArea: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_APartID2Dom:
  forall x, GoodInvAsrt (APartID2Dom x).
Proof.
 intros.
  unfold APartID2Dom.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_APartID2Dom: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ARootTaskStk':
  forall x, GoodInvAsrt (ARootTaskStk' x).
Proof.
   unfold ARootTaskStk'.
   intros.
   unfold Aarray_new in *.
   GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ARootTaskStk': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ARootTaskStk:
  forall x x0, GoodInvAsrt (ARootTaskStk x x0).
Proof.
 intros.
  unfold ARootTaskStk.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_ARootTaskStk: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AXMPFR:
  GoodInvAsrt (AXMPFR).
Proof.
 intros.
  unfold AXMPFR.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AXMPFR: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AMDMAER:
  GoodInvAsrt (AMDMAER).
Proof.
 intros.
  unfold AMDMAER.
 GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_AMDMAER: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_AOSPortAttrTbl':
  forall vl, GoodInvAsrt (AOSPortAttrTbl' vl).
Proof.
 intros.
  unfold AOSPortAttrTbl'.
 GoodInvAsrt_solver.
 unfold Aarray_new.
 apply GoodInvAsrt_Aarray_new'.
Qed.

Hint Resolve GoodInvAsrt_AOSPortAttrTbl': GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_PartitionInv1: forall ecbls,
  GoodInvAsrt (PartitionInv_part1 ecbls).
Proof.
  intros. unfold PartitionInv_part1. 
  GoodInvAsrt_solver.
  unfold AOSCorePortPtrList. GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_PartitionInv1: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_PartitionInv2:
  GoodInvAsrt PartitionInv_part2.
Proof.
  intros. unfold PartitionInv_part2.
  GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_PartitionInv2: GoodInvAsrt_lemmas.

(* end add by CNU *)

Lemma GoodInvAsrt_PartitionInv: forall ecbls,
  GoodInvAsrt (PartitionInv ecbls).
Proof.
  intros. unfold PartitionInv. 
  GoodInvAsrt_solver.
  unfold AOSCorePortPtrList. GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_PartitionInv: GoodInvAsrt_lemmas.

Lemma GoodInvAsrt_ASlots: 
    forall vl n l, GoodInvAsrt(ASlots l n vl).
Proof.
    inductions vl; intros.
    destruct n; simpl; auto.
    destruct n; simpl; auto.
    destruct a. simpl. auto.
    destruct a. destruct l. 
    unfold ACap.
    destruct p, c, p. 
    GoodInvAsrt_solver.
Qed.


Lemma GoodInvAsrt_ACSpaceAarrayTptr :
    forall vl pvl n cspacels, GoodInvAsrt(ACSpaceAarrayTptr n pvl vl cspacels).
Proof.
    inductions vl; intros.
    destruct n; destruct pvl. simpl. auto.
    simpl. destruct v; simpl; auto.
    simpl. auto.
    simpl. destruct v; simpl; auto.
    destruct n; destruct pvl; simpl; auto.
    destruct v; simpl; auto.
    destruct v; simpl; auto.
    splits; simpl; auto.
    unfold ACSpace.
    destruct a. destruct p. destruct p. destruct a0. destruct p.
    unfold GoodInvAsrt; fold GoodInvAsrt.
    splits.
    unfold Acnode.
    destruct c. destruct p.
    GoodInvAsrt_solver.
    eapply GoodInvAsrt_ASlots.
    
    simpl. auto. auto.
    eapply GoodInvAsrt_Aarray.
    auto. simpl. auto.
    simpl. auto.
    simpl. auto.
Qed.
Lemma GoodInvAsrt_CapabilityInv:
  forall acspace,  
  GoodInvAsrt (CapabilityInv acspace).
Proof.
  intros.
  unfold CapabilityInv.
  GoodInvAsrt_solver.
  unfold AOSCSpacePrioTbl. 
  GoodInvAsrt_solver.
  eapply GoodInvAsrt_ACSpaceAarrayTptr.
  unfold AOSCSpacePrioTbl. 
  GoodInvAsrt_solver.
  unfold AOSCSpaceObjectPointer.
  GoodInvAsrt_solver.
  unfold AOSCSpaceCapParent.
  GoodInvAsrt_solver.
  unfold CSpaceGVars.
  GoodInvAsrt_solver.
Qed.

Hint Resolve GoodInvAsrt_CapabilityInv: GoodInvAsrt_lemmas.

(*add end by SJTU *)
Lemma goodinv:  GoodInvAsrt OSInv.
Proof.
  unfold OSInv.
  GoodInvAsrt_solver.
Qed.

Lemma goodinv_aemp :
  GoodInvAsrt aemp_isr_is.
Proof.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  unfold GoodInvAsrt; auto.
Qed.

Lemma invprop_aemp :
  inv_prop aemp_isr_is.
Proof.
  unfolds; split.
  unfolds; destruct_s s; intros.
  simpl in H, H0; simpljoin1; intros; auto.

  unfolds; split; intros.
  destruct_s s.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; split; auto.

  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  unfold isr_is_prop in *; intros.
  apply H14 in H.
  unfolds.
  destruct(beq_nat i x); auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
  
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
    
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.

  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct( beq_nat i x ) eqn :eq1.
  false; apply H; simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H14; intro; apply H.
  simpl; right; auto. 
  unfolds; auto.

  split; intros.
  destruct_s s; simpl in H; simpl; simpljoin1.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.

  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; splits; eauto.
 
  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; eauto.
  split.
  apply map_join_emp.
  split.
  splits; eauto.
  unfolds; auto.
  splits; eauto.
  
  unfold isr_is_prop in *; unfold get_isr_s in H0; unfold get_is_s in H1; intros.
  destruct( beq_nat i x ) eqn :eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H16; intro; apply H; substs.
  simpl in H2; destruct H2; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.
  unfolds; auto.

  destruct_s s; simpl in H; simpl; simpljoin1.
  simpl in H0; substs.
  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst; split; auto.

  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; eauto.
  split.
  apply map_join_emp.
  split.
  splits; eauto.
  unfolds; auto.
  splits; eauto.
  unfolds.
  intros.
  unfolds; auto.
  unfolds; auto.
Qed.

Lemma atoy_inv'_precise' :
  forall e e0 M1 M2 i ier i0 i1 c o1 o2 a,
    (e, e0, M1, i, ier, (i0, i1, c), o1, a) |= atoy_inv' ->
    (e, e0, M2, i, ier, (i0, i1, c), o2, a) |= atoy_inv' ->
    (forall M : mem,
       sub M1 M -> sub M2 M -> M1 = M2) /\
    (forall o0 : osabst,
       sub o1 o0 -> sub o2 o0 -> o1 = o2).
Proof.
  intros.
  unfold atoy_inv' in *.
  simpl in H, H0; simpljoin1; split; auto; intros.
  rewrite H13 in H4; inverts H4.
  eapply mapstoval_true_mem_eq; eauto.
Qed.

Lemma atoy_inv'_precise :
  forall e e0 M1 M2 i ier i0 i1 c o1 o2 a,
    (e, e0, M1, i, ier, (i0, i1, c), o1, a) |= atoy_inv' ->
    (e, e0, M2, i, ier, (i0, i1, c), o2, a) |= atoy_inv' ->
    (forall (M : mem) (o : osabst),
    sub M1 M -> sub M2 M -> 
    sub o1 o -> sub o2 o -> M1 = M2 /\ o1 = o2).      
Proof.
  intros e e0 M1 M2 i ier i0 i1 c o1 o2 a H H0.
  eapply precise'2precise;eauto.
  eapply atoy_inv'_precise';eauto.
Qed.

Lemma OSInv_prop :
  forall o O O' aop,
    (o, O, aop) |= OSInv -> disjoint O O' -> O' = empabst.
Proof.
  intros.
  unfold OSInv in H.
  unfold EvtInv in H.
  unfold IntInv in H.
  unfold AOSTCBPrioTbl in H.
  unfold TmrInv in H.
  unfold TmrInv' in H.
  unfold HeapInv' in H.
  unfold CoreCommuInv in H.
  unfold PartitionInv in H.
  unfold AKsDomSchedule, AIntPartMux, Adomain2index,APartArea, ACorepartnum in H.
  unfold AMPAXs, ASMSMpax, ASESMpax, AXMpax, ARootTaskStk in H.
  unfold AXMPFR, AMDMAER in H.
  unfold CapabilityInv in H.
  unfold DynamicRefactorINV in H.
  unfold APthreadAttr in H.
  sep normal in H; sep destruct H.

  eapply join_lib.extensionality; intros.
  rewrite emp_sem.
  destruct a.
  all: 
  match goal with 
  | |- get _ ?x = None => 
  seplog_trm_tacs.sep_lifts_trms_in H (x);
  sep remember (1::nil)%nat in H;
  simpl in H; simpljoin1;
  eapply osabst_disjoint_join_sig_get_none; eauto end.
Qed.


Lemma goodinv_atoy :
  GoodInvAsrt atoy_inv.
Proof.
  unfold atoy_inv.
  unfold atoy_inv'.
  unfold A_isr_is_prop.
  unfold GoodInvAsrt; simpl;auto.
Qed.

Lemma invprop_atoyinv :
  inv_prop atoy_inv.
Proof.
  unfolds; split.

  {
  unfolds; intros; destruct_s s; unfold substmo in *; unfold substaskst in *.
  unfold atoy_inv in *.
  elim_sep_conj1 H _H; elim_sep_conj1 H0 _H0.

  lets Hx1: atoy_inv'_precise _H _H0.
  lets Hx2: A_isr_is_prop_precise H H0.
  assert (x = x3 /\ x1 = x5).
  { apply (Hx1 M o);mem_join_sub_solver. } destruct H9;subst.
  assert (x0 = x4 /\ x2 = x6).
  { apply (Hx2 M o);mem_join_sub_solver. } destruct H9;subst.
  split;jeat. }

  unfolds.
  split; intros. 
  unfold atoy_inv in *.
  destruct_s s.
  unfold set_isr_s; unfold get_isr_s.
  solve_sat_auto.
  unfold A_isr_is_prop in *.
  simpl in H5; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  clear - H12.
  unfold isr_is_prop in *; intros.
  apply H12 in H.
  unfold isrupd.
  destruct(beq_nat i x); auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  unfold set_isisr_s; unfold get_is_s; unfold get_isr_s.
  unfold atoy_inv in *.
  solve_sat_auto.
  simpl in H5; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  clear - H12.
  unfold isr_is_prop in *; intros.
  unfold isrupd.
  destruct(beq_nat i x) eqn : eq1.
  false; apply H.
  simpl; left.
  apply beq_nat_true in eq1; auto.
  apply H12.
  intro; apply H.
  simpl; right; auto.
  unfolds; auto.
  
  split; intros.
  destruct_s s.
  unfold set_isr_s, get_is_s, get_isr_s in *.
  unfold atoy_inv in *.
  solve_sat_auto.
  unfold set_is_s.
  simpl in H7; simpljoin1.
  simpl.
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  splits; eauto.
  unfolds; auto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; auto.
  split.
  apply map_join_emp.
  repeat (split; eauto).

  unfold isr_is_prop in *; intros.
  destruct( beq_nat i x ) eqn :eq1.
  apply beq_nat_true in eq1; substs; auto.
  apply H13; intro; apply H; substs.
  simpl in H1; destruct H1; substs.
  rewrite <- beq_nat_refl in eq1; tryfalse.
  auto.

  destruct_s s.
  unfold get_isr_s in *; substs.
  unfold atoy_inv in *.
  solve_sat_auto.
  unfold set_is_s.
  simpl in H5; simpljoin1.
  simpl.
  
  do 8 eexists; splits; eauto.
  apply map_join_emp.
  apply map_join_emp.
  unfold emposabst.
  splits; eauto.

  do 6 eexists.
  split; eauto.
  split.
  apply map_join_emp.
  split; auto.
  split.
  apply map_join_emp.
  repeat (split; eauto).
Qed.

Definition I (n:hid) :=
  match n with 
  | 0%nat => mkinvasrt goodinv invprop
  | _ => mkinvasrt goodinv_aemp invprop_aemp
  end.

Lemma disj_star_elim_disj_dup:
  forall p q r, ( p \\// q )** r ==> (p ** r) \\// (q ** r).
Proof.
  intros.
  simpl in *;simpljoin.
  destruct H3;simpljoin.
  left.
  do 6 eexists;splits;eauto.
  right.
  do 6 eexists;splits;eauto.
Qed.

Lemma disj_star_elim_disj':
  forall p q r, ( p ** r) \\// (q ** r) ==> ( p \\// q )** r.
Proof.
  intros. destruct H; simpl in *;simpljoin; do 6 eexists;splits;eauto.
Qed.

(*added by zhanghui*)
Lemma osq_inv_in:
  forall n e e0 m x ier i1 c O ab, 
    (forall i : hid, x i = false)->
    (e, e0, m, x, ier, (false, i1, c), O, ab)
      |= invlth_isr I 0%nat n ->
    (e, e0, m, x, ier, (false, i1, c), O, ab)
      |= EX p1 p2 tcbl1 tcbcur tcbl2 ct tcbls rtbl pf,
  (AOSTCBList' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls pf) ** HCurTCB ct** Atrue.
Proof.
  inductions n.
  introv Hfor Hsat.
  unfold invlth_isr in Hsat.
  replace (0-0)%nat with (0%nat) in Hsat by omega.
  unfold starinv_isr in Hsat.
  sep destruct Hsat.
  destruct Hsat.
  simpl in H.
  simpljoin1.
  tryfalse.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H0 in H.
  remember (([|x0 0%nat = false|] //\\ Aisr x0) ) as P.
  clear HeqP.
  unfold OSInv in H.
  unfold IntInv in *.
  sep normal in H.
  sep destruct H. 
  (* do 23 destruct H. *) (*把20改成22*)
  Require Import seplog_trm_tacs.
  sep_rmb_trms_in H AOSTCBList'.
  (* sep remember (10::nil)%nat in H. *)
  sep eexists. 
  sep auto.
  
  introv Hfor Hsat.
  unfold invlth_isr in Hsat.
  replace (S n-0)%nat with (S n%nat) in Hsat by omega.
  unfold starinv_isr in Hsat.
  fold starinv_isr in Hsat.
  remember ( starinv_isr I 1%nat n) as P.
  clear HeqP.
  sep normal in Hsat.
  destruct Hsat.  
  
  apply disj_star_elim_disj_dup in H.
  destruct H.
  simpl in H.
  simpljoin1.
  tryfalse.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H0 in H.
  remember (([|x0 0%nat = false|] //\\ Aisr x0) ) as d.
  clear Heqd.
  unfold OSInv in H.
  sep auto.
Qed.

Lemma join_join_disj_copy :
  forall m1 m2 m3 m4 m5,
    TcbMod.join m1 m2 m3 -> TcbMod.join m4 m5 m2 -> TcbMod.disj m1 m4.
Proof.
  intros.
  intro.
  pose proof H a.
  pose proof H0 a.
  
  destruct (TcbMod.get m1 a);
    destruct (TcbMod.get m2 a);
    destruct (TcbMod.get m3 a);
    destruct (TcbMod.get m4 a);
    destruct (TcbMod.get m5 a);
    tryfalse; auto.
Qed.

Lemma TCBList_P_combine_copy :
  forall l1 l2 v1 v2 rtbl tcbls1 tcbls2 tcbls,
    TcbMod.join tcbls1 tcbls2 tcbls ->
    TCBList_P v1 l1 rtbl tcbls1 ->
    TCBList_P v2 l2 rtbl tcbls2 ->
    l1 <> nil ->
    V_OSTCBNext (last l1 nil) = Some v2 ->
    TCBList_P v1 (l1++l2) rtbl tcbls.
Proof.
  intros.
  destruct l1; tryfalse.
  
  clear H2.
  gen v.
  inductions l1; intros.
  simpl in H3.
  simpl.
  simpl in H0; simpljoin1.
  do 4 eexists; repeat split; eauto.

  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  rewrite TcbMod.emp_sem in H.
  unfold sig in *; simpl in *.
  destruct (TcbMod.get tcbls1 a);
    destruct (TcbMod.get tcbls2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get (TcbMod.sig x x2) a);
    tryfalse; substs; auto.
  
  rewrite <- app_comm_cons.
  unfold TCBList_P; fold TCBList_P.
  remember (a::l1) as lx.
  unfold TCBList_P in H0; fold TCBList_P in H0.
  substs.
  simpljoin1. 
  do 4 eexists; repeat split; eauto.
  instantiate (1:=TcbMod.merge x1 tcbls2).
  clear - H H4.
  unfold TcbJoin in *.
  intro.
  pose proof H a; clear H.
  pose proof H4 a; clear H4.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get tcbls1 a);
    destruct (TcbMod.get tcbls2 a);
    destruct (TcbMod.get (TcbMod.sig x x2) a);
    tryfalse; substs; auto.

  eapply IHl1; eauto.

  clear - H H4.
  apply TcbMod.join_merge_disj.
  unfold TcbJoin in H4.
  apply TcbMod.join_comm in H.
  apply TcbMod.join_comm in H4.
  apply TcbMod.disj_sym.
  eapply join_join_disj_copy; eauto.
Qed.

Lemma tcb_list_split_by_tcbls :
  forall l tls tid htcb s head hprev tail tnext rtbl P,
    get tls tid = Some htcb ->
    TCBList_P head l rtbl tls ->
    s |= tcbdllseg head hprev tail tnext l ** P ->
    (exists l1 tcbnode l2 tls1 tls2 tail1,
       s |= tcbdllseg head hprev tail1 (Vptr tid) l1 **
         tcbdllseg (Vptr tid) tail1 tail tnext (tcbnode :: l2) ** P /\
       TCBList_P head l1 rtbl tls1 /\
       TCBList_P (Vptr tid) (tcbnode :: l2) rtbl tls2 /\
       join tls1 tls2 tls /\ l = l1 ++ tcbnode :: l2).
Proof.
  inductions l; intros.
  simpl in H0; substs.
  rewrite TcbMod.emp_sem in H; tryfalse.

  simpl in H0; simpljoin1.
  destruct (tidspec.beq tid x) eqn : eq1.
  pose proof tidspec.beq_true_eq tid x eq1; substs.
  exists (nil(A:=vallist)) a l TcbMod.emp tls hprev.
  simpljoin1; splits.
  sep auto.
  destruct_s s.
  simpl in H1; simpljoin1.
  simpl.
  do 6 eexists; splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst; auto.
  unfolds; auto.

  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  destruct_s s.
  sep split in H1.
  simpl_sat H1; simpljoin1.
  simpl; auto.
  simpl.
  do 4 eexists; repeat (split; eauto).
  apply TcbMod.join_emp; auto.
  rewrite app_nil_l; auto.
  
  unfold tcbdllseg in H1.
  unfold dllseg in H1; fold dllseg in H1.
  destruct_s s.
  sep split in H1.
  simpl_sat H1; simpljoin1.  
  assert((e, e0, (merge x23 x4), i, i0, (i1, i2, c), (merge x26 x7), a0)
           |= dllseg x9 (Vptr x) tail tnext l OS_TCB_flag V_OSTCBPrev
           V_OSTCBNext ** P).
  simpl_sat_goal.
  exists x23 x4; eexists.
  exists x26 x7; eexists.
  splits; eauto.
  eapply join_merge_disj.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm; eauto.
  eapply join_merge_disj.
  eapply osabst_join_join_disjoint; eauto.
  apply join_comm; eauto.

  assert(get x1 tid = Some htcb).
  clear - H H3 eq1.
  unfolds in H3.
  pose proof H3 tid.
  rewrite TcbMod.get_sig_none in H0.
  unfold get in H; simpl in H.
  rewrite H in H0.
  unfold get; simpl.
  destruct(TcbMod.get x1 tid); tryfalse.
  substs; auto.
  apply tidspec.beq_false_neq in eq1.
  auto.

  rewrite H2 in H14; inverts H14.
  unfold tcbdllseg at 1 in IHl.
  lets Hx: IHl H7 H5 H1.
  simpljoin1.
  
  exists (a::x0) x5 x8 (TcbMod.merge (TcbMod.sig x x2) x10) x11 x12.
  simpljoin1; splits; auto.
  simpl_sat H9; simpljoin1.
  simpl_sat_goal.
  
  exists (merge x22 x13) x14 m (merge x25 x16) x17 o.
  splits; eauto.
  clear - H14 H6 H21.

  eapply mem_join_join_join_merge_join_merge; eauto.
  
  clear - H16 H8 H23.
  eapply osabst_join_join_join_merge_join_merge; eauto.
  
  unfold tcbdllseg; unfold dllseg; fold dllseg.
  sep split; auto.
  exists x9.
  sep split; auto.
  simpl_sat_goal.
  exists x22 x13; eexists.
  exists x25 x16; eexists.
  splits; eauto.
  clear - H6 H21 H14.
  eapply join_merge_disj.
  
  eapply mem_join_join_join_merge_disjoint.
  eapply H6.
  eauto.
  eauto.

  clear - H8 H23 H16.
  eapply join_merge_disj.
  eapply osabst_join_join_join_merge_disjoint.
  eapply H8.
  eauto.
  eauto.

  exists x19 x20 x14 x24 x27 x17.
  splits; eauto.
  
  simpl; do 4 eexists; splits; eauto.
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; auto.
 
  clear - H3 H13.
  unfold TcbJoin in *.
  unfolds; intros.
  simpl.
  unfolds; intros.
  pose proof H3 a; pose proof H13 a.
  unfold sig in *; simpl in *.
  rewrite TcbMod.merge_sem.
  destruct(TcbMod.get (TcbMod.sig x x2) a);
    destruct (TcbMod.get x1 a);
    destruct (TcbMod.get tls a);
    destruct (TcbMod.get x10 a);
    destruct (TcbMod.get x11 a); tryfalse; substs; auto.
Qed.

Lemma starinv_isr_osabst_emp :
  forall n i e e0 M isr ier st O ab,
    (i > 0)%nat ->
    (forall i0, isr i0 = false) ->
    (e, e0, M, isr, ier, st, O, ab) |= starinv_isr I i n ->
    O = OSAbstMod.emp.
Proof.
  inductions n; intros.
  simpl in H1; simpljoin1.
  destruct H1; simpljoin1.
  destruct i.
  lia.
  destruct i.
  simpl in H6; simpljoin1.
  simpl in H6; simpljoin1.
  simpl in H1; simpljoin1.
  destruct H5; simpljoin1.
  pose proof H0 i; rewrite H1 in H2; false.
  lets Hx: IHn H6; eauto.
  destruct i.
  lia.
  destruct i.
  simpl in H9; simpljoin1.
  simpl in H9; simpljoin1.
Qed.

Lemma tcbdllseg_last_nextptr :
  forall l s head hprev tail tid h P,
    s |= tcbdllseg head hprev tail (Vptr tid) (h::l) ** P ->
    V_OSTCBNext (last (h :: l) nil) = Some (Vptr tid).
Proof.
  inductions l; intros.
  destruct_s s.
  unfold tcbdllseg in H; unfold dllseg in H.
  simpl_sat H; simpljoin1.
  simpl; auto.

  remember (a::l) as xxx.
  unfold tcbdllseg in *.
  unfold dllseg in H; fold dllseg in H.
  sep pure.
  destruct_s s.
  sep remember (1::nil)%nat in H.
  simpl_sat H; simpljoin1.
  lets Hx: IHl H8.
  simpl last in *; auto.
Qed.

(*
Lemma AOSTCBList_set_curtid :
  forall e e0 M M' is st O ab b tp p1 p2 l1 curtcb l2 rtbl hcurt hcurt' tcbls,
    RH_CurTCB hcurt' tcbls ->
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) M (b, 0) (Vptr hcurt') = Some M' ->
    (e, e0, M, is, st, O, ab) |= AOSTCBList p1 p2 l1 (curtcb :: l2) rtbl hcurt tcbls ->
    exists p2' l1' curtcb' l2', (e, e0, M', is, st, O, ab) |= AOSTCBList p1 p2' l1' (curtcb' :: l2') rtbl hcurt' tcbls.
Proof.
  intros.
  exists (Vptr hcurt').
  unfold AOSTCBList in H2.
  sep pure.
  unfold RH_CurTCB in H; do 3 destruct H.
  pose proof H4 hcurt'.
  rewrite H in H7.
  destruct(TcbMod.get x1 hcurt') eqn : eq1;
    destruct(TcbMod.get x2 hcurt') eqn : eq2;
    tryfalse; substs.
  
  sep lift 2%nat in H2.
  lets Hx : TCBList_P_split_by_tcbls eq1 H5 H2.
  simpljoin1.
  exists x6 x7 (x8 ++ (curtcb :: l2)).
  unfold AOSTCBList.
  exists x11 x0 x9 (TcbMod.merge x10 x2).
  sep split; auto.
  sep remember (4::nil)%nat in H7.
  simpl_sat H7; simpljoin1.
  assert(exists x12', store (Tptr tp) x12 (b, 0) (Vptr hcurt') = Some x12').
  simpl in H15; simpljoin1.
  rewrite H0 in H17; inverts H17.
  lets Hx : lmachLib.store_mapstoval_frame H18 H1; eauto.
  simpljoin1; eauto.
  simpljoin1.
  sep remember (3::nil)%nat.
  simpl_sat_goal.
  exists x14 x13 M' x15 x16 O.
  repeat (split; eauto).
  eapply join_store; eauto.
  clear - H15 H7 H0.
  simpl in H15; simpljoin1.
  rewrite H0 in H4; inverts H4.
  simpl.
  eexists; exists empmem x14 x14 OSAbstMod.emp OSAbstMod.emp OSAbstMod.emp.
  repeat (split; eauto).
  apply MemMod.join_emp; auto.
  eexists.
  repeat (split; eauto).
  lets Hx :lmachLib.store_mapstoval_frame1 x12 MemMod.emp H5 H7.
  eapply MemMod.join_emp; auto.
  simpljoin1; auto.

  substs.
  clear - H16.
  sep auto.
  assert (H
            |= tcbdllseg (Vptr hcurt') x11 x (Vptr hcurt) (x7 :: x8) **
            tcbdllseg (Vptr hcurt) x x0 Vnull (curtcb :: l2) ** Aemp).
  sep auto.
  lets Hx: tcbdllseg_compose H0.
  sep auto.

  replace (x7 :: x8 ++ curtcb :: l2) with ((x7 :: x8) ++ curtcb :: l2).
  eapply TCBList_P_combine_copy; eauto.
  clear - H4 H10.
  unfolds; intro.
  pose proof H4 a; pose proof H10 a.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get x2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get x9 a);
    destruct (TcbMod.get x10 a);
    tryfalse; substs; auto.
  clear - H7.
  sep lift 2%nat in H7.

  eapply tcbdllseg_last_nextptr; eauto.

  rewrite app_comm_cons; auto.
  clear - H4 H10.
  unfolds; intros.
  pose proof H4 a; pose proof H10 a.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get x2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get x9 a);
    destruct (TcbMod.get x10 a);
    tryfalse; substs; auto.
  
  sep lift 4%nat in H2.
  lets Hx : TCBList_P_split_by_tcbls eq2 H6 H2.
  simpljoin1.
  exists (l1++x6) x7 x8.
  unfold AOSTCBList.
  exists x11 x0 (TcbMod.merge x1 x9) x10.
  sep split; auto.
  sep remember (5::nil)%nat in H7.
  simpl_sat H7; simpljoin1.
  assert(exists x12', store (Tptr tp) x12 (b, 0) (Vptr hcurt') = Some x12').
  simpl in H15; simpljoin1.
  rewrite H0 in H17; inverts H17.
  lets Hx : lmachLib.store_mapstoval_frame H18 H1; eauto.
  simpljoin1; eauto.
  simpljoin1.
  sep remember (3::nil)%nat.
  simpl_sat_goal.
  exists x14 x13 M' x15 x16 O.
  repeat (split; eauto).
  eapply join_store; eauto.
  
  clear - H15 H7 H0.
  simpl in H15; simpljoin1.
  rewrite H0 in H4; inverts H4.
  simpl.
  eexists; exists empmem x14 x14 OSAbstMod.emp OSAbstMod.emp OSAbstMod.emp.
  repeat (split; eauto).
  apply MemMod.join_emp; auto.
  eexists.
  repeat (split; eauto).
  lets Hx :lmachLib.store_mapstoval_frame1 x12 MemMod.emp H5 H7.
  eapply MemMod.join_emp; auto.
  simpljoin1; auto.

  substs.
  clear - H16.
  sep auto.
  sep lift 2%nat in H16.
  assert (H |= tcbdllseg p1 Vnull x (Vptr hcurt) l1 **
            tcbdllseg (Vptr hcurt) x x11 (Vptr hcurt') x6 ** Aemp).
  sep auto.
  lets Hx: tcbdllseg_compose H0.
  sep auto.

  destruct l1.
  simpl in H5; substs.
  simpl.
  assert ((TcbMod.merge TcbMod.emp x9) = x9).
  apply TcbMod.extensionality; intro.
  rewrite TcbMod.merge_sem; rewrite TcbMod.emp_sem.
  destruct( TcbMod.get x9 a); auto.
  rewrite H5.
  unfold tcbdllseg at 2 in H2; unfold dllseg in H2.
  sep split in H2; substs; auto.

  eapply TCBList_P_combine_copy; eauto.
  clear - H4 H10.
  unfolds; intro.
  pose proof H4 a; pose proof H10 a.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get x2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get x9 a);
    destruct (TcbMod.get x10 a);
    tryfalse; auto.

  sep lift 3%nat in H2.
  eapply tcbdllseg_last_nextptr; eauto.
  
  clear - H4 H10.
  unfolds; intro.
  pose proof H4 a; pose proof H10 a.
  rewrite TcbMod.merge_sem.
  destruct (TcbMod.get x1 a);
    destruct (TcbMod.get x2 a);
    destruct (TcbMod.get tcbls a);
    destruct (TcbMod.get x9 a);
    destruct (TcbMod.get x10 a);
    tryfalse; substs; auto.
Qed.

Lemma OSInv_set_curtid :
  forall e e0 M M' isr st O ab b tp tid,
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) M (b, 0) (Vptr tid) = Some M' ->
    (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M, isr, st, O, ab) |= OSInv ->
    (e, e0, M', isr, st, OSAbstMod.set O curtid (oscurt tid), ab) |= OSInv.
Proof.
  intros.
  unfold OSInv in H2.
  do 20 destruct H2.
  sep split in H2.

  sep remember (9::nil)%nat in H2.
  unfold sat in H2; fold sat in H2; simpl substmo in H2; simpl getmem in H2; simpl getabst in H2; simpljoin1.
  assert(exists x19', store (Tptr tp) x19 (b, 0) (Vptr tid) = Some x19').
  simpl; destruct tid.
  unfold AOSTCBList in H9.
  destruct H9.
  do 3 destruct H2.
  sep remember (3::nil)%nat in H2.
  simpl in H2; simpljoin1.
  rewrite H in H17; inverts H17.
  unfold mapstoval in H18; simpljoin1.
  sep split in H13; simpljoin1.
  simpl in H5; destruct x15.
  unfold ptomvallist in H5; unfold ptomval in H5;  simpljoin1.
  unfold storebytes.
  clear - H7 H15 H5 H17.
  assert(Int.unsigned Int.zero = 0).
  rewrite Int.unsigned_zero; auto.
  rewrite H in H5, H15, H17.
  Ltac join_get_solver :=
    match goal with 
      | H: MemMod.join (MemMod.sig ?x ?y) _ ?O |- MemMod.get ?O ?x = Some ?y =>
        eapply MemMod.join_get_get_l; eauto
      | H: MemMod.join ?O1 ?O2 ?O |- MemMod.get ?O ?x = Some ?y =>
        eapply MemMod.join_get_get_r; [eauto | join_get_solver]
    end.
  assert(MemMod.get x19 (x40, 0) = Some (Pointer b i0 3)).
  eapply MemMod.join_get_get_l.
  eapply H7.
  join_get_solver.
  rewrite MemMod.get_sig_some; auto.
  rewrite H0.
  assert(MemMod.get x19 (x40, 0 + 1) = Some (Pointer b i0 2)).
  eapply MemMod.join_get_get_l.
  eapply H7.
  join_get_solver.
  rewrite MemMod.get_sig_some; auto.
  rewrite H1.
  assert(MemMod.get x19 (x40, 0 + 1 + 1) = Some (Pointer b i0 1)).
  eapply MemMod.join_get_get_l.
  eapply H7.
  join_get_solver.
  rewrite MemMod.get_sig_some; auto.
  rewrite H2.
  assert(MemMod.get x19 (x40, 0 + 1 + 1 + 1) = Some (Pointer b i0 0)).
  eapply MemMod.join_get_get_l.
  eapply H7.
  do 3 (eapply MemMod.join_get_get_r; eauto).
  rewrite MemMod.get_sig_some; auto.
  rewrite H3.
  eexists; eauto.
  destruct H2.
  assert(RH_CurTCB tid x13).
  simpl in H1; simpljoin1.
  unfolds in H12; simpljoin1.
  pose proof H11 abtcblsid.
  rewrite H1 in H13.
  destruct (OSAbstMod.get x28 abtcblsid); tryfalse.
  destruct (OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
  substs.
  assert (OSAbstMod.get O abtcblsid = Some (abstcblist x13)).
  sep remember (13::nil)%nat in H10.
  simpl in H10; simpljoin1.
  pose proof H16 abtcblsid.
  rewrite OSAbstMod.get_sig_some in H10.
  destruct (OSAbstMod.get x34 abtcblsid); tryfalse.
  destruct (OSAbstMod.get x23 abtcblsid) eqn : eq2; tryfalse.
  substs.
  pose proof H8 abtcblsid.
  rewrite eq2 in H10.
  destruct(OSAbstMod.get x22 abtcblsid); tryfalse.
  destruct( OSAbstMod.get O abtcblsid); tryfalse.
  substs; auto.
  rewrite eq1 in H13; inverts H13.
  unfolds; eauto.
  
  lets Hx: AOSTCBList_set_curtid H5 H H2 H9.
  simpljoin1.
  unfold OSInv.
  exists x x0 x1 x2 x3 x4.
  exists x5 x24 x24 x25 x27.
  exists x10 x11 x12 x13 x14.
  exists tid x16 x17 x18.
  sep remember (15::nil)%nat in H10.
  simpl in H10; simpljoin1.
  sep split; auto.
  sep remember (9::nil)%nat.
  unfold sat; fold sat; simpl substmo; simpl getmem; simpl getabst.
  exists x21 x20 M' x22 (OSAbstMod.set x23 curtid (oscurt tid)) (OSAbstMod.set O curtid (oscurt tid)).
  repeat (split; eauto).
  eapply join_store; eauto.


  clear - H8 H14.
  eapply OSAbstMod.join_set_r; eauto.
  unfolds.
  pose proof H14 curtid.
  rewrite OSAbstMod.get_sig_some in H.
  destruct(OSAbstMod.get x32 curtid); tryfalse.
  destruct(OSAbstMod.get x23 curtid); tryfalse; substs; eauto.
  
  substs.
  sep remember (15::nil)%nat.
  simpl.
  exists empmem x20 x20 (OSAbstMod.sig curtid (oscurt tid)) x32 (OSAbstMod.set x23 curtid (oscurt tid)).
  repeat (split; eauto).
  eapply MemMod.join_emp; eauto.
  clear - H14.
  unfolds; intro.
  pose proof H14 a.
  destruct (absdataidspec.beq curtid a) eqn : eq1.
  pose proof absdataidspec.beq_true_eq eq1; substs.
  rewrite OSAbstMod.get_sig_some in *.
  rewrite OSAbstMod.set_a_get_a; auto.
  destruct(OSAbstMod.get x32 curtid); tryfalse; auto.

  pose proof absdataidspec.beq_false_neq eq1.
  rewrite OSAbstMod.get_sig_none in *; auto.
  rewrite OSAbstMod.set_a_get_a'; auto.
Qed.
*)

Lemma atoy_inv_osabst_emp :
  forall e e0 M isr st o ab,
    (e, e0, M, isr, st, o, ab) |= atoy_inv ->
    o = OSAbstMod.emp.
Proof.
  intros.
  simpl in H; simpljoin1.
Qed.

(*
Lemma AHprio_starinv_isr_atoy_inv_false :
  forall e e0 M M1 M2 isr st O o1 o2 ab n i tid,
    OSAbstMod.join o1 o2 O -> (i > 0)%nat -> (forall i : hid, isr i = false) ->
    (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M1, isr, st, o2, ab) |= starinv_isr I i n ->
    (e, e0, M2, isr, st, o1, ab) |= atoy_inv ->
    False.
Proof.
  intros.
  apply starinv_isr_osabst_emp in H3; auto.
  apply atoy_inv_osabst_emp in H4; auto.
  substs.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  rewrite OSAbstMod.emp_sem in H6.
  rewrite H in H6.
  destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
Qed.
*)

(*
Lemma starinv_isr_set_highest_tid :
  forall n low i0 e e0 m c O ab tid b tp M' x11,
    (forall i : hid, x11 i = false) ->
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) m (b, 0) (Vptr tid) = Some M' ->
    (e, e0, m, x11, (false, i0, c), O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, m, x11, (false, i0, c), O, ab) |= starinv_isr i ier l ow n ->
    (e, e0, M', x11, (false, i0, c), OSAbstMod.set O curtid (oscurt tid), ab) |= starinv_isr i ier l ow n.
Proof.
  inductions n; intros.
  unfold starinv_isr in *.
  destruct H3.
  destruct H3.
  destruct H3; simpl in H3; simpl in H4; simpljoin1.
  pose proof H low; rewrite H3 in H4; tryfalse.
  simpl in H3; simpljoin1.
  exists x;right.
  simpl.
  exists empmem M' M' OSAbstMod.emp (OSAbstMod.set O curtid (oscurt tid)) (OSAbstMod.set O curtid (oscurt tid)).
  repeat (split; eauto).
  eapply MemMod.join_emp; auto.
  eapply OSAbstMod.join_emp; auto.
  destruct low.
  unfold I in *; unfold getinv in *.


  eapply OSInv_set_curtid; eauto.

  destruct low.
  unfold I in *; unfold getinv in *.
  simpl in H8; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  rewrite H2 in H8.
  rewrite OSAbstMod.emp_sem in H8.
  destruct(OSAbstMod.get x3 abtcblsid); tryfalse.

  unfold I in *; unfold getinv in *.
  simpl in H8; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  rewrite OSAbstMod.emp_sem in H8.
  rewrite H2 in H8.
  destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
  
  unfold starinv_isr in *; fold starinv_isr in *.
  simpl in H3; simpljoin1.
  destruct H7; simpljoin1.
  pose proof H low; tryfalse.
  cut((e, e0, M', x5, (false, i0, c), OSAbstMod.set O curtid (oscurt tid), ab)
        |= (getinv (i ier l ow)) ** starinv_isr I (S low) n).
  intro.
  clear - H3 H10.
  simpl in H3; simpljoin1.
  simpl.
  do 6 eexists; repeat (split; eauto).
  exists x5; right.
  do 6 eexists; repeat (split; eauto).
  apply MemMod.join_emp; auto.
  apply OSAbstMod.join_emp; auto.
  
  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  assert(exists x1, store (Tptr tp) x (b, 0) (Vptr tid) = Some x1).
  unfold OSInv in H11.
  unfold AOSTCBList in H11.
  sep pure.
  sep remember (3::nil)%nat in H11.
  simpl in H11; simpljoin1.
  rewrite H0 in H23; inverts H23.
  lets Hx : lmachLib.store_mapstoval_frame (MemMod.merge x29 x0) H24 H1; eauto.
  clear - H4 H15.
  unfolds; intro.
  pose proof H4 a.
  pose proof H15 a.
  rewrite MemMod.merge_sem.
  destruct(MemMod.get x a);
    destruct(MemMod.get x0 a);
    destruct(MemMod.get m a);
    destruct(MemMod.get x28 a);
    destruct(MemMod.get x29 a);
    tryfalse; substs; auto.

  simpljoin1.
  eapply lmachLib.store_mono; eauto.

  simpljoin1.
  unfold sat; fold sat; simpl substmo; simpl getmem; simpl getabst.
  exists x1 x0 M' (OSAbstMod.set x2 curtid (oscurt tid)) x3 (OSAbstMod.set O curtid (oscurt tid)).
  repeat (split; eauto).
  eapply join_store; eauto.

  clear - H6 H11.
  eapply OSAbstMod.join_set_l; eauto.
  unfolds.
  unfold OSInv in H11.
  destruct H11; do 19 destruct H.
  sep remember (16::nil)%nat in H.
  simpl_sat H; simpljoin1.
  pose proof H3 curtid.
  rewrite OSAbstMod.get_sig_some in H.
  destruct(OSAbstMod.get x27 curtid); tryfalse.
  destruct(OSAbstMod.get x2 curtid); tryfalse.
  eauto.

  eapply OSInv_set_curtid; eauto.
  
  lets Hx : starinv_isr_osabst_emp H8; eauto.
  substs.
  simpl in H2.
  do 6 destruct H2. (*simpljoin1 will clear H6 ?*)
  destruct H2; destruct H5.
  destruct H7.
  destruct H9.
  destruct H12.
  destruct H12.
  substs.
  unfolds in H12.
  destruct H12.
  do 4 destruct H2.
  pose proof H9 abtcblsid.
  rewrite H2 in H12.
  destruct(OSAbstMod.get x8 abtcblsid); tryfalse.
  destruct(OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
  substs.
  pose proof H6 abtcblsid.
  rewrite OSAbstMod.emp_sem in H12.
  rewrite eq1 in H12.
  destruct(OSAbstMod.get x2 abtcblsid) eqn : eq2; tryfalse.
  substs.
  simpl.
  
  do 3 eexists; exists x2; do 2 eexists; repeat (split; eauto).
  apply MemMod.join_emp; eauto.
  apply OSAbstMod.join_comm; apply OSAbstMod.join_emp; eauto.
  unfolds.
  do 4 eexists; repeat (split; eauto).
  
  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  (*    unfold sat; fold sat; simpl substmo; simpl getmem; simpl getabst.
    assert(exists x0', store (Tptr tp) x0 (b, 0) (Vptr tid) = Some x0').
   *)
  false.
  lets Hx: AHprio_starinv_isr_atoy_inv_false 2%nat H6 H H2 H8.
  lia.
  apply Hx; eauto.
  
  unfold I in *; fold I in *; unfold getinv in *. 

  assert(x2 = OSAbstMod.emp).
  simpl in H11; simpljoin1.
  apply starinv_isr_osabst_emp in H8; eauto.
  substs.
  simpl in H2; simpljoin1.
  unfolds in H8; simpljoin1.
  pose proof H7 abtcblsid.
  rewrite OSAbstMod.emp_sem in H8.
  rewrite H2 in H8.
  destruct (OSAbstMod.get x6 abtcblsid); tryfalse.
  lia.
Qed.
*)

Lemma GoodSched_GetHPrio : GoodSched GetHPrio.
Proof.
  unfolds.
  splits; intros.
  unfold GetHPrio in *; simpljoin1.
  do 5 eexists.
  splits; eauto.
  eapply join_get_l; eauto.

  unfold GetHPrio in *; simpljoin1.
  do 2 eexists; splits; eauto.
  
  
  unfold GetHPrio in *; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x4)).
  eapply join_get_l; eauto.
  rewrite H1 in H3; inverts H3.
  do 5 eexists; splits; eauto.
Qed.

Lemma aemp_isr_elim_dup:
  forall o O ab P,
    (o, O , ab) |= aemp_isr_is ** P -> (o, O, ab) |= P.
Proof.
  introv Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[[]]]]].
  simpl in *.
  destruct l.
  destruct p.
  assert (m=x0) by join auto.
  assert (O=x3) by join auto.
  subst.
  auto.
Qed.

Lemma atoy_abst_elim_dup :
  forall o O ab P,
    (o,O,ab) |= atoy_inv ** P ->
    exists o', (o',O,ab) |= P.
Proof.
  introv Hsat.
  unfold atoy_inv in Hsat.
  simpl in Hsat.
  simpljoin.
  destruct o as [[[[[]]]]].
  simpl in *.
  simpljoin.
  destruct l.
  destruct p.
  eexists .
  assert (O = x3) by join auto.
  subst.
  eauto.
Qed.

Require Import invariant_prop.

Lemma mapstoval_false_join_load_vptr :
  forall l x a m1 m2 m,
    mapstoval l (Tptr x) false (Vptr a) m1 ->
    join m1 m2 m ->
    load (Tptr x) m l = Some (Vptr a).
Proof.
  intros.
  unfold mapstoval in H; simpljoin1.
  unfold load.
  unfold loadm.
  destruct l.
  lets Hx: symbolic_lemmas.ptomvallist_loadbytes H1.
  lets Hx1: lmachLib.loadbytes_mono H0 Hx.
  rewrite Hx in Hx1.
  rewrite encode_val_length in Hx1.
  rewrite Hx1.
  rewrite symbolic_lemmas.type_val_mach_encode_val_decode_val; auto.
Qed.

(*
Definition GoodI1 :=
  fun (I : Inv) (sd : ossched) (pa : LocalInv) =>
    (forall (o : taskst) (O0 O' : osabst) (ab : absop) (OO : osabst),
        (o, O0, ab) |= starinv_noisr I 0%nat (S INUM) -> join O0 O' OO -> O' = empabst) /\
    (forall (o : taskst) (O : osabst) (ab : absop) (tid : addrval),
        (o, O, ab) |= SWINVt I tid ->
        exists b tp,
          get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) /\
          load (Tptr tp) (get_mem (get_smem o)) (b, 0) = Some (Vptr tid) /\
          get O curtid = Some (oscurt tid)) /\
    (forall (o : taskst) (O : osabst) (ab : absop) (tid : tid) 
            (b : block) (tp : type) (M' : mem) (ct : addrval),
        (o, O, ab) |= SWINVt I ct ->
        (o, O, ab) |= AHprio sd tid ** Atrue ->
        get (get_genv (get_smem o)) OSTCBCur = Some (b, Tptr tp) ->
        store (Tptr tp) (get_mem (get_smem o)) (b, 0) (Vptr tid) = Some M' ->
        exists tls,
          get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\ (substaskst o M', set O curtid (oscurt tid), ab) |= SWINVt I tid \/
                           ~ indom tls ct /\
           (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
               satp (substaskst o Mx) Ox (EX lg : list logicvar, pa ct lg) ->
               join M' Mx MM ->
               join O Ox OO -> (substaskst o MM, set OO curtid (oscurt tid), ab) |= SWINVt I tid))) /\
    GoodSched sd.
*)

Definition AOSTCBList'' :=
  fun (p1 p2 : val) (l1 l2 : list vallist) (rtbl : vallist)
      (hcurt : addrval) (tcbls : TcbMod.map) (pf : val) =>
    ((EX (tail1 tail2 : val) (tcbls1 tcbls2 : TcbMod.map),
      GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
         tcbdllseg p1 Vnull tail1 p2 l1 **
         tcbdllseg p2 tail1 tail2 Vnull l2 **
         [|p1 <> Vnull /\ p2 = Vptr hcurt|] **
         [|join tcbls1 tcbls2 tcbls|] **
         [|TCBList_P p1 l1 rtbl tcbls1|] **
         [|TCBList_P p2 l2 rtbl tcbls2|] **
         tcbdllflag p1 (l1 ++ l2) ** [|p2 <> pf|])
       \\//
       ( EX (tail : val),
         GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
            tcblist p1 Vnull tail Vnull (l1 ++ l2) rtbl tcbls **
            TCB_Not_In p2 p1 (l1 ++ l2) **
            tcbdllflag p1 (l1 ++ l2) **
            [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** [|p2 = pf|])).

Lemma AOSTCBList'_AOSTCBList'' :
  forall a b c d e f g h P,
    AOSTCBList' a b c d e f g h **P <==>   GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> b ** AOSTCBList'' a b c d e f g h **P.
Proof.
  intros.
  unfold AOSTCBList'; unfold AOSTCBList''.
  split; intros; sep cancel P. 
  destruct H.
  sep destruct H.
  sep cancel 3%nat 1%nat.
  left.
  sep auto; eauto.
  sep destruct H.
  sep cancel 2%nat 1%nat.
  right.
  sep auto; eauto.

  sep lift 2%nat in H.
  apply disj_split in H.
  destruct H.
  left.
  sep auto; eauto.
  right.
  sep auto; eauto.
Qed.

Definition osinv'' :=
  EX (ptbl : vallist) (p1 p2 : val)
     (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
     (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
     (tcbls : TcbMod.map) (t : int32) (ct vhold : addrval)
     (scapl mcapl qcapl : list vallist) 
     (ptfree : val) (lfree : list vallist) ptls pattrb acspace,
  GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> p2 **
    AOSTCBList'' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ptfree **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold **
    AOSTCBFreeList' ptfree lfree ct tcbls  **
    AOSRdyTblGrp rtbl rgrp **
    AOSTime (Vint32 t) **
    HTCBList tcbls **
    HTime t **
    HCurTCB ct **
    AGVars **
    EvtInv ecbls p1 (tcbl1++(tcbcur::tcbl2)) tcbls vhold scapl mcapl qcapl **
    [|RH_TCBList_ECBList_P ecbls tcbls ct|] ** 
    A_isr_is_prop **
    IntInv **
    TmrInv **
    CoreCommuInv ecbls**
    PartitionInv ecbls**
    CapabilityInv acspace ** APthreadAttr pattrb.

Lemma osinv''_OSInv: forall P,
    osinv'' ** P <==> OSInv ** P.
Proof.
  unfold osinv'', OSInv.
  split.
  intros.
  sep cancel P.
  sep destruct H.
  rewrite <- AOSTCBList'_AOSTCBList'' in H.
  sep auto.
  intros.
  sep cancel P.
  sep destruct H.
  sep eexists.
  rewrite <- AOSTCBList'_AOSTCBList'' .
  sep auto.
Qed.

Lemma tcblist_indom_ptr_in_tcblist :
  forall vltcb head rtbl tcbls ct,
    TCBList_P head vltcb rtbl tcbls ->
    indom tcbls ct ->
    ptr_in_tcblist (Vptr ct) head vltcb.
Proof.
  inductions vltcb; intros.
  simpl in H; substs.
  unfolds in H0; destruct H0.
  rewrite emp_sem in H; tryfalse.

  unfold1 TCBList_P in H; simpljoin1.
  unfold ptr_in_tcblist.
  unfold1 ptr_in_tcbdllseg.
  destruct (beq_val (Vptr ct) (Vptr x)) eqn : eq1; auto.
  rewrite H1.
  eapply IHvltcb; eauto.
  clear - H2 H0 eq1.
  unfold indom in *; simpljoin1.
  exists x0.
  unfolds in H2.
  assert (ct <> x).
  intro; substs.
  unfold beq_val in eq1.
  unfolds in eq1.
  destruct x.
  rewrite beq_pos_Pos_eqb_eq in eq1.
  rewrite Int.eq_true in eq1.
  assert (b = b) by auto.
  apply Pos.eqb_eq in H0.
  rewrite H0 in eq1.
  simpl in eq1; tryfalse.
  clear eq1.
  hy.
Qed.

Lemma tcbdllseg_sll_neq :
  forall ct lfree pf s tid x x7 x8 x11 H,
    s
      |= tcbdllseg (Vptr tid) x11 x ct (x7 :: x8) **
      assertion.sll pf lfree OS_TCB_flag V_OSTCBNext ** H ->
    pf <> Vptr tid.
Proof.
  intros.
  intro; substs.
  unfold assertion.sll in H0.
  destruct lfree.
  unfold sllseg in H0; fold sllseg in H0; sep split in H0; tryfalse.
  unfold sllseg in H0; fold sllseg in H0.
  unfold tcbdllseg in H0.
  unfold dllseg in H0; fold dllseg in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1.
  inverts H1; inverts H3.
  sep lifts (1::3::nil)%nat in H0.
  eapply os_inv.node_OS_TCB_dup_false; eauto.
Qed.

Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom
  : forall (p1 p2 : val) (l1 : list vallist) (curtcb : vallist)
           (l2 : list vallist) (rtbl : vallist) (ct : addrval)
           (tcbls : TcbMod.map) (lfree : list vallist) 
           (pf : val) (P : asrt) (tid : Modules.tid) ecbls vhold
           (scapl mcapl qcapl : list vallist)
           e e0 isr ier st ab M O Mx Ox MM OO,
    RH_CurTCB tid tcbls ->
    ~indom tcbls ct ->
    (e, e0, M, isr, ier, st, O, ab)
      |= AOSTCBList'' p1 p2 l1 (curtcb :: l2) rtbl ct tcbls pf **
      AOSTCBFreeList' pf lfree ct tcbls **
      EvtInv ecbls p1 (l1++(curtcb::l2)) tcbls vhold scapl mcapl qcapl ** P ->
    join M Mx MM ->
    join O Ox OO ->
    (e, e0, Mx, isr, ier, st, Ox, ab) |=
      EX lg : list logicvar, OSLInv ct lg ->
        exists l1' curtcb' l2' pf' lfree',
          (e, e0, MM, isr, ier, st, OO, ab)
            |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls pf' **
                AOSTCBFreeList' pf' lfree' tid tcbls **
                EvtInv ecbls p1 (l1'++(curtcb'::l2')) tcbls vhold scapl mcapl qcapl ** P.
Proof.
  intros.
  rename H0 into H_indom.
  rename H1 into H0.
  unfold AOSTCBList'' in H0.
  unfold AOSTCBFreeList' in H0.

  (*4 cases*)
  apply disj_split in H0.
  destruct H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.

  (*1 false*)
  simpljoin1.
  unfold1 TCBList_P in H7.
  simpljoin1.
  inverts H7.
  clear - H5 H10 H_indom.
  false.
  apply H_indom.
  unfold indom.
  exists x6.
  unfolds in H10.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.
  apply get_sig_some.

  (*2 false*)
  unfold TCBFree_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.
  
  (*3 false*)
  unfold TCBFree_Not_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  (*4*)
  simpljoin1.
  unfold TCBFree_Eq in H0.
  sep normal in H0.
  sep destruct H0.
  sep split in H0; simpljoin1.
  unfolds in H; simpljoin1.
  sep_lift_context_in H0 tcblist.
  unfold tcblist in H0.
  sep split in H0.
  lets Hx: tcb_list_split_by_tcbls H H5 H0.
  simpljoin1.
  exists x12 x13 x14.
  exists (Vptr ct) (x1::x0).
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep lift 2%nat.
  unfold AOSTCBFreeList'.
  sep normal.
  exists x17 x x15 x16.
  sep_lift_context Adisj.
  apply disj_split.
  left.
  sep split; auto.
  unfold TCB_Not_In in H10.
  sep split in H10.
  sep remember (7::8::3::4::5::6::9::10::nil)%nat in H10.  
  sep remember (9::nil)%nat in H10.
  sep lift 2%nat in H10.
  simpl in H10; simpljoin1.
  sep remember (1::nil)%nat.
  simpl_sat_goal.
  exists (merge x18 Mx) x19 MM. 
  exists (merge x21 Ox) x22 OO.
  splits; eauto.
  eapply mem_join_join_merge13_join'; eauto.
  eapply join_join_merge1; eauto.
  apply join_comm in H3; eauto.
  assert (
      (e, e0, merge x18 Mx, isr, ier, st, merge x21 Ox, ab)
        |= (EX lg : list logicvar, OSLInv ct lg) ** Astruct ct OS_TCB_flag x1 **
        PV get_off_addr ct flag_off @ Tint8 |-r-> Vint32 (Int.repr 0) **
           PV get_off_addr ct evloc_off @ Tint8 |-r-> x3 **
           PV get_off_addr ct muxptr_off @ Tptr OS_EVENT |-r-> x4 ** 
           PV get_off_addr ct semptr_off @ Tptr OS_EVENT |-r-> x5 ** 
           PV get_off_addr ct qptr_off @ Tptr OS_EVENT |-r-> x6 ** 
         assertion.sll x2 x0 OS_TCB_flag V_OSTCBNext ** sllfreeflag x2 x0
    ).
  {
  sep remember (1::nil)%nat.
  simpl_sat_goal.
  exists Mx x18; eexists.
  exists Ox x21; eexists.
  splits; eauto.
  apply join_comm.
  apply join_merge_disj.
  clear - H19 H2.
  eapply mem_join_join_disjoint; eauto.
  apply join_comm.
  apply join_merge_disj.
  eapply osabst_join_join_disjoint; eauto.
  }
  unfold OSLInv in H17.
  sep normal in H17.
  sep destruct H17.
  sep split in H17; simpljoin1.
  sep lifts (5::11::nil)%nat in H17.
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  sep lifts (5::10::nil)%nat in H17.
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  sep lifts (5::9::nil)%nat in H17.
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17. 
  sep lifts (5::8::nil)%nat in H17.
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  sep lifts (5::7::nil)%nat in H17.
  apply sep_combine_lemmas.PV_combine_ro_frm in H17.
  sep split in H17.
  
  unfold TCBFree_Not_Eq.
  sep split.
  unfold assertion.sll in *.
  unfold1 sllseg.
  unfold sllfreeflag in *.
  unfold1 sllsegfreeflag.
  sep normal.
  sep eexists.
  sep split; eauto.
  inverts H24.
  unfold node; sep normal.
  sep eexists.
  sep split; eauto.
  assert (x23 = (Vint32 (Int.repr 0))).
  {
    clear -H31 H20.
    unfolds in H20; destruct H20.
    substs.
    simpl in H31; tryfalse.
    auto.
  }
  substs.
  instantiate (1:=x28). instantiate (1:=x27). instantiate (1:=x26). instantiate (1:=x25).
  sep auto.

  clear - H H_indom.
  intro.
  inverts H0.
  unfolds in H_indom.
  apply H_indom.
  unfold indom.
  eauto.

  substs.
  sep auto.
  rewrite <- H15.
  auto.

  clear - H H_indom.
  intro.
  inverts H0.
  unfolds in H_indom.
  apply H_indom.
  unfold indom.
  eauto.
Qed.

Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_indom :
  forall p1 p2 l1 curtcb l2 rtbl ct tcbls lfree pf s P tid ecbls vhold,
  forall scapl mcapl qcapl,
    RH_CurTCB tid tcbls ->
    indom tcbls ct ->
    s |= AOSTCBList'' p1 p2 l1 (curtcb::l2) rtbl ct tcbls pf **
      AOSTCBFreeList' pf lfree ct tcbls **
      EvtInv ecbls p1 (l1++(curtcb::l2)) tcbls vhold scapl mcapl qcapl ** P ->
    exists l1' curtcb' l2' pf' lfree',
      s |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls pf' **
           AOSTCBFreeList' pf' lfree' tid tcbls **
           EvtInv ecbls p1 (l1'++(curtcb'::l2')) tcbls vhold scapl mcapl qcapl ** P.
Proof.
  intros.
  rename H0 into H_indom.
  rename H1 into H0.
  unfold AOSTCBList'' in H0.
  unfold AOSTCBFreeList' in H0.
  
  (*4 cases*)
  apply disj_split in H0.
  destruct H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.

  (*1*)
  unfold TCBFree_Not_Eq in H0.
  sep split in H0; simpljoin1.
  unfolds in H; simpljoin1.
  sep lifts (4::5::nil)%nat in H0.
  pose proof H2 tid.
  unfold get in H; simpl in H.
  rewrite H in H7.
  destruct (TcbMod.get x1 tid) eqn : eq1;
    destruct (TcbMod.get x2 tid) eqn : eq2;
    tryfalse.
  substs.
  (*tid in x1*)
  lets Hx : tcb_list_split_by_tcbls eq1 H3 H0.
  simpljoin1.
  assert (
      s |= tcbdllseg p1 Vnull x12 (Vptr tid) x7 **
        tcbdllseg (Vptr tid) x12 x (Vptr ct) (x8 :: x9) **
        tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: l2) **
        assertion.sll pf lfree OS_TCB_flag V_OSTCBNext **
        sllfreeflag pf lfree **
        GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
        tcbdllflag p1 ((x7 ++ x8 :: x9) ++ curtcb :: l2) **
        GV OSTCBFreeList @ Tptr os_ucos_h.OS_TCB |-> pf **
        EvtInv ecbls p1 ((x7 ++ x8 :: x9) ++ curtcb :: l2) tcbls vhold scapl mcapl qcapl ** 
        P
    ) as H7_bak by auto.
  sep lifts (2::3::nil)%nat in H7.
  assert (V_OSTCBNext (last (x8 :: x9) nil) = Some (Vptr ct)) as H_last.
  eapply tcbdllseg_last_nextptr in H7; auto.
  eapply tcbdllseg_compose in H7.
  
  lets Hx: TCBList_P_combine_copy H9 H4.
  instantiate (1:=merge x11 x2).
  clear - H2 H10.
  eapply TcbMod.join_merge_disj.
  apply join_comm in H10.
  eapply TcbMod.join_join_disj_l; eauto.
  assert (x8 :: x9 <> nil) by auto.
  apply Hx in H11; auto; clear Hx.
  replace ((x8 :: x9) ++ curtcb :: l2) with (x8 :: x9 ++ curtcb :: l2) in H7, H11.
  exists x7 x8 (x9 ++ curtcb :: l2) pf lfree.
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep normal.
  do 4 eexists.
  sep split; eauto.
  sep cancel 5%nat 1%nat.
  sep cancel 2%nat 1%nat.
  sep cancel 1%nat 1%nat.
  replace ((x7 ++ x8 :: x9) ++ curtcb :: l2) with (x7 ++ x8 :: x9 ++ curtcb :: l2) in H7.
  sep cancel 3%nat 1%nat.
  sep cancel EvtInv. (* added by CNU *)
  unfold AOSTCBFreeList'.
  sep auto.
  left.
  unfold TCBFree_Not_Eq.
  sep auto.
  clear - H7_bak.
  sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
  clears.
  eapply tcbdllseg_sll_neq; eauto.
  
  rewrite <- app_assoc.
  auto.
  
  clear - H7_bak.
  sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
  clears.
  assert (pf <> Vptr tid).
  eapply tcbdllseg_sll_neq; eauto.
  auto.
  clear - H2 H10.
  eapply join_merge23_join; eauto.
  rewrite app_comm_cons; auto.

  (*tid in x2*)
  substs.
  sep lift 2%nat in H0.
  lets Hx : tcb_list_split_by_tcbls eq2 H4 H0.
  simpljoin1.
  assert (
      s
        |= tcbdllseg (Vptr ct) x x12 (Vptr tid) x7 **
        tcbdllseg (Vptr tid) x12 x0 Vnull (x8 :: x9) **
        tcbdllseg p1 Vnull x (Vptr ct) l1 **
        assertion.sll pf lfree OS_TCB_flag V_OSTCBNext **
        sllfreeflag pf lfree **
        GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
        tcbdllflag p1 (l1 ++ curtcb :: l2) **
        GV OSTCBFreeList @ Tptr os_ucos_h.OS_TCB |-> pf **
        EvtInv ecbls p1 (l1 ++ curtcb :: l2) tcbls vhold scapl mcapl qcapl **
        P
    ) as H7_bak by auto.
  exists (l1 ++ x7) x8 x9 pf lfree.
  unfold AOSTCBList''.
  apply disj_split.
  left.
  sep normal.
  exists x12 x0 (merge x1 x10) x11.
  sep split; eauto.
  sep cancel 6%nat 1%nat.
  sep cancel 2%nat 2%nat.
  rewrite H11 in H7_bak.
  replace (l1 ++ x7 ++ x8 :: x9) with ((l1 ++ x7) ++ x8 :: x9) in H7_bak.
  sep cancel 5%nat 2%nat.
  sep cancel EvtInv. (* added by CNU *)
  unfold AOSTCBFreeList'.
  sep auto.
  sep lift 2%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  sep lifts (2::1::nil)%nat in H7_bak.
  eapply tcbdllseg_compose in H7_bak.
  sep auto.

  clear - H7.
  sep lifts (2::4::nil)%nat in H7.
  eapply tcbdllseg_sll_neq; eauto.
  
  rewrite <- app_assoc.
  auto.

  assert (pf <> Vptr tid).
  sep lifts (2::4::nil)%nat in H7.
  eapply tcbdllseg_sll_neq; eauto.
  auto.

  clear - H1 H3 H8 H10 H2 H7.
  destruct l1.
  rewrite app_nil_l.
  simpl in H3; simpljoin1.
  sep remember (3::nil)%nat in H7.
  destruct_s s.
  simpl in H7; simpljoin1.
  rewrite jl_merge_emp'.
  auto.
  eapply TCBList_P_combine_copy; eauto.
  clear - H2 H10.
  eapply TcbMod.join_merge_disj.
  apply join_comm in H2.
  apply TcbMod.disj_comm.
  eapply TcbMod.join_join_disj_l; eauto.
  sep lift 3%nat in H7.
  eapply tcbdllseg_last_nextptr; eauto.

  clear - H2 H10.
  eapply join_join_join_merge; eauto.

  (*2 false*)
  unfold TCBFree_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  sep normal in H0; sep destruct H0.
  sep split in H0.
  sep lift 6%nat in H0.
  apply disj_split in H0.
  destruct H0.
  
  (*3 false*)
  unfold TCBFree_Not_Eq in H0.
  sep normal in H0; sep destruct H0.
  sep split in H0.
  simpljoin1.
  tryfalse.

  (*4*)
  simpljoin1.

  unfold TCB_Not_In in H0.
  unfold tcblist in H0.
  sep split in H0.
  lets Hx: tcblist_indom_ptr_in_tcblist H2 H_indom.
  simpljoin1.
  false; apply H3; auto.
Qed.

Lemma OSInv_set_curtid1 :
  forall e e0 M M' isr ier st O ab b tp tp0 tid ct P,
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) M (b, 0) (Vptr tid) = Some M' ->
    (e, e0, M, isr, ier, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M, isr, ier, st, O, ab) |=
      OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr ct ** P ->
        exists tls,
          get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\
            (e, e0, M', isr, ier, st, set O curtid (oscurt tid), ab)
              |= OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P \/
        ~ indom tls ct /\
        (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
            satp (e, e0, Mx, isr, ier, st) Ox (EX lg, OSLInv ct lg) ->
            join M' Mx MM ->
            join O Ox OO ->
            (e, e0, MM, isr, ier, st, set OO curtid (oscurt tid), ab)
              |=  OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P)).
Proof.
  intros.
  rewrite <- osinv''_OSInv in H2.
  unfold osinv'' in H2.
  sep normal in H2.
  sep destruct H2.
  assert (get O abtcblsid = Some (abstcblist x8)).
  sep_lifts_trms_in H2 abstcblist.
  sep remember (1::nil)%nat in H2.
  simpl in H2; simpljoin1.
  eapply join_get_l; eauto.
  eexists.
  split; eauto.

  assert (os_ucos_h.OS_TCB = tp0).
  sep_lifts_skp_in H2 (OSTCBCur, _N_ 1).
  sep remember (1::2::nil)%nat in H2.
  simpl in H2; simpljoin1.
  rewrite H27 in H18; inverts H18.
  auto.
  subst tp0.

  assert (x1 = Vptr x10).
  { sep_lifts_trms_in H2 AOSTCBList''.
    sep remember (1::nil)%nat in H2.
    simpl in H2; simpljoin1.
    destruct H8; simpljoin1; auto.
  }
  substs.
  sep_lifts_skp_in H2 (OSTCBCur, _N_ 1).
  sep remember (1::2::nil)%nat in H2.
  eapply sep_combine_lemmas.GV_combine_ro_frm in H2.
  sep split in H2.
  simpl in H2; simpljoin1.
  assert (x10 = ct).
  {
    clear - H5.
    simpl in H5.
    destruct x10; destruct ct.
    inverts H5; auto.
  }
  substs.

  assert (indom x8 ct \/ ~ indom x8 ct).
  {
    unfold indom.
    destruct (get x8 ct) eqn : eq1; clear - eq1.
    left; eauto.
    right.
    intro; destruct H; tryfalse.
  }
  destruct H2.
  (*indom tcbls ct*)
  left.
  split; auto.
  rewrite <- osinv''_OSInv.
  unfold osinv''.
  sep normal.
  unfolds in H14; simpl in H14.
  rewrite H in H14; inverts H14.
  lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
  simpljoin1.

  sep_lifts_trms_in H10 (AOSTCBList'', AOSTCBFreeList', EvtInv).
  lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_indom H10; auto.
  unfolds.
  instantiate (TEMP11 := tid).
  clear - H1 H3.
  simpl in H1; simpljoin1.
  unfolds in H4; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x)).
  eapply join_get_l; eauto.
  rewrite H3 in H1.
  inverts H1.
  eauto.
  simpljoin1.
  sep eexists.

  sep_lifts_skp (OSTCBCur, _N_ 1).
  eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
  sep remember (1::nil)%nat.
  simpl.
  exists x10 x20. (* join x10 x19 M' *)
  do 4 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  do 7 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  eapply join_emp; eauto.
  eexists.
  unfold emposabst; splits; eauto.
  unfolds.
  eexists; splits; eauto.
  unfolds in H15; simpljoin1.
  unfold store in H4.
  lets Hx: lmachLib.storebytes_ptomvallist_eqlen_infer p H4.
  simpl.
  destruct tid; destruct ct; simpl; auto.
  auto.
  unfolds; auto.
  substs.
  sep_lifts_trms_in H5 curtid.
  sep remember (1::nil)%nat in H5.
  simpl in H5; simpljoin1.
  sep_lifts_trms curtid.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_sig_set; eauto.
  substs.
  sep auto.

  (*not indom x8 ct*)
  right.
  split; auto.
  intros.

  pose proof H4 ab.
  rewrite <- osinv''_OSInv.
  unfold osinv''.
  sep normal.
  unfolds in H14; simpl in H14.
  rewrite H in H14; inverts H14.
  lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
  simpljoin1.

  sep remember (1::nil)%nat in H10.
  assert ((e, e0, M', isr, ier, st, O, ab)
            |= GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-> (Vptr tid) **
               AOSTCBList'' x0 (Vptr ct) x2 (x3 :: x4) x5 ct x8 x15 ** H5).
  substs.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  do 7 eexists.
  splits; eauto.
  eapply join_emp; eauto.
  apply join_emp; eauto.
  eexists.
  splits; eauto.
  unfolds; auto.
  unfolds.
  eexists; splits; eauto.
  unfolds in H15; simpljoin1.
  eapply lmachLib.storebytes_ptomvallist_eqlen_infer; eauto.
  simpl; destruct tid, ct; auto.
  unfolds; auto.
  substs.
  sep_lifts_trms_in H13 (AOSTCBList'', AOSTCBFreeList', EvtInv).
  lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom H13 H7 H8 H9.
  unfolds.
  instantiate (TEMP10 := tid).
  clear - H1 H3.
  simpl in H1; simpljoin1.
  unfolds in H4; simpljoin1.
  assert (get O abtcblsid = Some (abstcblist x)).
  eapply join_get_l; eauto.
  rewrite H3 in H1.
  inverts H1.
  eauto.
  auto.
  simpljoin1.
  sep eexists.
  sep_lifts_skp (OSTCBCur, _N_ 1).
  eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
  sep_lifts_trms_in H5 curtid.
  sep remember (1::nil)%nat in H5.
  simpl in H5; simpljoin1.
  sep_lifts_trms curtid.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem MM.
  do 4 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_sig_set; eauto.
  substs.
  sep auto.
Qed.

Lemma AHprio_starinv_isr_atoy_inv_false :
  forall e e0 M M1 M2 isr ier st O o1 o2 ab n i tid,
    join o1 o2 O -> (i > 0)%nat -> (forall i : hid, isr i = false) ->
    (e, e0, M, isr, ier, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M1, isr, ier, st, o2, ab) |= starinv_isr I i n ->
    (e, e0, M2, isr, ier, st, o1, ab) |= atoy_inv ->
    False.
Proof.
  intros.
  apply starinv_isr_osabst_emp in H3; auto.
  apply atoy_inv_osabst_emp in H4; auto.
  substs.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  pose proof H abtcblsid.
  rewrite OSAbstMod.emp_sem in H8.
  destruct (OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
  destruct (OSAbstMod.get x2 abtcblsid) eqn: eq2; tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid) eqn : eq3; tryfalse.
  unfold get in H2; simpl in H2; rewrite H2 in eq2; tryfalse.
Qed.

Lemma aemp_osabst_emp :
  forall e e0 M isr st o ab,
    (e, e0, M, isr, st, o, ab) |= aemp_isr_is ->
    o = OSAbstMod.emp.
Proof.
  intros.
  simpl in H; simpljoin1.
Qed.

Lemma AHprio_starinv_isr_aemp_false :
  forall e e0 M M1 M2 isr ier st O o1 o2 ab n i tid,
    join o1 o2 O -> (i > 0)%nat -> (forall i : hid, isr i = false) ->
    (e, e0, M, isr, ier, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
    (e, e0, M1, isr, ier, st, o2, ab) |= starinv_isr I i n ->
    (e, e0, M2, isr, ier, st, o1, ab) |= aemp_isr_is ->
    False.
Proof.
  intros.
  apply starinv_isr_osabst_emp in H3; auto.
  apply aemp_osabst_emp in H4; auto.
  substs.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  pose proof H5 abtcblsid.
  pose proof H abtcblsid.
  rewrite OSAbstMod.emp_sem in H8.
  destruct (OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
  destruct (OSAbstMod.get x2 abtcblsid) eqn: eq2; tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
  destruct (OSAbstMod.get x3 abtcblsid) eqn : eq3; tryfalse.
  unfold get in H2; simpl in H2; rewrite H2 in eq2; tryfalse.
Qed.

Lemma starinv_isr_set_highest_tid :
  forall n low i0 e e0 m c O ab tid b tp tp' ct M' x11 ier i,
    (forall i : hid, x11 i = false) ->
    EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
    store (Tptr tp) m (b, 0) (Vptr tid) = Some M' ->
    (e, e0, m, x11, ier, (i, i0, c), O, ab) |= AHprio GetHPrio tid ** Atrue -> 
    (e, e0, m, x11, ier, (i, i0, c), O, ab) |= GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** starinv_isr I low n ->
      (exists tls,
          get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\
          (e, e0, M', x11, ier, (i, i0, c), set O curtid (oscurt tid), ab)
            |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid) \/
          ~ indom tls ct /\
          (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
              satp (e, e0, Mx, x11, ier, (i, i0, c)) Ox (EX lg, OSLInv ct lg) ->
              join M' Mx MM ->
              join O Ox OO ->
              (e, e0, MM, x11, ier, (i, i0, c), set OO curtid (oscurt tid), ab)
                |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid)))).
Proof.
  inductions n; intros.
  unfold starinv_isr in *.
  destruct low.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1.
  tryfalse. 
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.

  unfold I in *; unfold getinv in *.
  
  assert ((e, e0, m, x, ier, (i, i0, c), O, ab)
            |= OSInv ** GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** Aemp).
  sep auto.
  lets Hx: OSInv_set_curtid1 H0 H1 H2 H3.
  simpljoin1.
  eexists.
  splits; eauto.
  destruct H5; simpljoin1.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  right.
  split; auto.
  intros.
  lets Hx: H6 H7 H10 H11.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  substs.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  sep auto.

  destruct low.
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  apply map_join_pos in H5; simpljoin1.
  rewrite emp_sem in H2; tryfalse.
  
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  unfold aemp_isr_is in H9.
  unfold A_isr_is_prop in H9.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  apply map_join_pos in H5; simpljoin1.
  rewrite emp_sem in H2; tryfalse.

  (*ind case*)
  unfold starinv_isr in *; fold starinv_isr in *.
  sep normal in H3; destruct H3.
  (*  sep normal; exists x. *)
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.

  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  eapply OSInv_set_curtid1 in H9; eauto.
  simpljoin1.
  destruct H4; simpljoin1.
  eexists; splits; eauto.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.

  eexists.
  splits; eauto.
  right.
  split; eauto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  
  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  false.

  simpl_sat H9; simpljoin1.
  simpl in H13; simpljoin1.
  eapply AHprio_starinv_isr_aemp_false with (i:=2%nat); eauto.

  sep remember (1::nil)%nat in H9.
  simpl_sat H9; simpljoin1.
  simpl in H9; simpljoin1.
  lets Hx: IHn H H0 H1 H2 H10.
  simpljoin1.
  eexists; splits; eauto.
  destruct H4; simpljoin1.
  left.
  split; auto.
  sep normal in H5; destruct H5.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.

  right.
  split; auto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal in Hx; destruct Hx.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.
Qed.

Lemma GoodI_I :
  GoodI I GetHPrio OSLInv.
Proof.
  intros.
  unfold GoodI.
  splits.
-
  unfolds INUM.
  intros.
  unfold starinv_noisr in H.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H1 in H.
  assert (getinv (I 1%nat) = aemp_isr_is) by auto. 
  assert (getinv (I 2%nat) = aemp_isr_is ) by auto.
  assert (getinv (I 3%nat) = aemp_isr_is) by auto.
  assert (getinv (I 4%nat) = aemp_isr_is) by auto.
  assert (getinv (I 5%nat) = aemp_isr_is) by auto.
  assert (getinv (I 6%nat) = aemp_isr_is) by auto.
  assert (getinv (I 7%nat) = aemp_isr_is) by auto.
  assert (getinv (I 8%nat) = aemp_isr_is) by auto.
  assert (getinv (I 9%nat) = aemp_isr_is) by auto.
  assert (getinv (I 10%nat) = aemp_isr_is) by auto.
  assert (getinv (I 11%nat) = aemp_isr_is) by auto.
  assert (getinv (I 12%nat) = aemp_isr_is) by auto.
  assert (getinv (I 13%nat) = aemp_isr_is) by auto.
  assert (getinv (I 14%nat) = aemp_isr_is) by auto.
  assert (getinv (I 15%nat) = aemp_isr_is) by auto.
  assert (getinv (I 16%nat) = aemp_isr_is) by auto.
  assert (getinv (I 17%nat) = aemp_isr_is) by auto.
  rewrite H3 in H.  
  rewrite H2 in H.
  rewrite H4 in H.
  rewrite H5 in H.
  rewrite H6 in H.
  rewrite H7 in H.
  rewrite H8 in H.
  rewrite H9 in H.
  rewrite H10 in H.
  rewrite H11 in H.
  rewrite H12 in H.
  rewrite H13 in H.
  rewrite H14 in H.
  rewrite H15 in H.
  rewrite H16 in H.
  rewrite H17 in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H;
  apply aemp_isr_elim_dup in H.
  simpljoin1.
  eapply OSInv_prop; eauto.
  eapply my_join_disj; eauto.

-
  introv Hsw.
  unfold SWINVt in Hsw.
  destruct o as [[[[[]]]]].
  simpl_sat Hsw; simpljoin1.
  simpl in H4; simpljoin1.
  exists x11 x5.
  splits; eauto.
  simpl get_mem.
  apply join_comm in H0.
  eapply mapstoval_false_join_load_vptr; eauto.
  
  unfold SWINV in H3.
  simpl_sat H3; simpljoin1.
  unfold getie in *; unfold gettaskst in *.
  destruct l; destruct p.
  simpl in H12.
  simpl in H18; simpljoin1.
  lets Hres : osq_inv_in H2 H12.
  sep destruct Hres.

  simpl_sat Hres; simpljoin1.
  simpl in H15; simpljoin1.
  unfold AOSTCBList' in H5.
  destruct H5.
  do 4 destruct H.
  sep split in H.
  simpljoin1.
  clear H3 H5 H8 H9 H10; clears.
  sep remember (3::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H17; inverts H17.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H5; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

  destruct H.
  sep split in H.
  simpljoin1.
  sep remember (2::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H18; inverts H18.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H8; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

-
  introv Hsw Hpr Hget Hs.
  destruct o as [[[[[]]]]].
  simpl in Hget.
  unfold get_smem in Hs; unfold get_mem in Hs.
  unfold SWINVt in *.
  unfold substaskst.
  unfold SWINV in *.
  sep normal in Hsw.
  destruct Hsw; destruct H.

  sep remember (2::4::5::nil)%nat in H.
  simpl in H; simpljoin1.
  destruct l; destruct p.
  substs.

  unfold invlth_isr in *.
  rewrite Nat.sub_0_r in *.
  lets Hx: starinv_isr_set_highest_tid H18 Hget Hs Hpr H15.
  simpljoin1.
  eexists.
  splits;eauto.
  destruct H0; simpljoin1.
  left.
  split; auto.
  sep normal in H1; destruct H1.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  auto.

  right.
  split; auto.
  intros.
  lets Hx: H1 H2 H3 H4.
  sep normal in Hx.
  destruct Hx.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  pose proof H2 ab.
  destruct H6.
  unfold OSLInv in H6.
  destruct H6.
  simpl in H6; simpljoin1.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.

- apply GoodSched_GetHPrio.
Qed.

(*GoodI_I backup

Lemma GoodI_I :
  GoodI I GetHPrio OSLInv.
Proof.
  intros.
  unfold GoodI.
  splits.
  
-
  unfolds INUM.
  intros.
  unfold starinv_noisr in H.
  assert (getinv (I 0%nat) = OSInv) by auto.
  rewrite H1 in H.
  assert (getinv (I 1%nat) = atoy_inv) by auto. 
  assert (getinv (I 2%nat) = aemp_isr_is ) by auto.
  assert (getinv (I 3%nat) = aemp_isr_is) by auto.
  rewrite H3 in H.  
  rewrite H2 in H.
  rewrite H4 in H.
  sep lift 4%nat in H.
  apply aemp_isr_elim_dup in H.
  sep lift 3%nat in H.
  apply aemp_isr_elim_dup in H.
  sep lift 2%nat in H.
  apply atoy_abst_elim_dup in H.
  simpljoin1.
  eapply OSInv_prop; eauto.
  eapply my_join_disj; eauto.

-
  introv Hsw.
  unfold SWINVt in Hsw.
  destruct o as [[[[]]]].
  simpl_sat Hsw; simpljoin1.
  simpl in H4; simpljoin1.
  exists x11 x5.
  splits; eauto.
  simpl get_mem.
  apply join_comm in H0.
  eapply mapstoval_false_join_load_vptr; eauto.
  
  unfold SWINV in H3.
  simpl_sat H3; simpljoin1.
  unfold getie in *; unfold gettaskst in *.
  destruct l; destruct p.
  simpl in H12.
  simpl in H18; simpljoin1.
  lets Hres : osq_inv_in H2 H12.
  sep destruct Hres.

  simpl_sat Hres; simpljoin1.
  simpl in H15; simpljoin1.
  unfold AOSTCBList' in H5.
  destruct H5.
  do 4 destruct H.
  sep split in H.
  simpljoin1.
  clear H3 H5 H8 H9 H10; clears.
  sep remember (3::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H17; inverts H17.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H5; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

  destruct H.
  sep split in H.
  simpljoin1.
  sep remember (2::nil)%nat in H.
  simpl in H; simpljoin1.
  rewrite H6 in H18; inverts H18.
  assert (Vptr tid = Vptr x8 /\ x0 = x2).
  eapply mapstoval_false_rule_type_val_match_eq with (M := m) (t := Tptr os_ucos_h.OS_TCB).
  simpl; auto.
  simpl; auto.
  eauto.
  eauto. 
  eapply join_sub_r; eauto.

  apply join_sub_l in H8; apply sub_trans with (m2 := x13); auto.
  apply join_sub_l in H1; apply sub_trans with (m2 := x); auto.
  apply join_sub_l in H0; apply sub_trans with (m2 := m); auto.
  unfold sub.
  eexists emp.
  apply join_comm.
  apply join_emp; auto.

  destruct H; substs.
  inverts H.
  eapply join_get_r; eauto.
  eapply join_get_l; eauto.

-
  introv Hsw Hpr Hget Hs.
  destruct o as [[[[]]]].
  simpl in Hget.
  unfold get_smem in Hs; unfold get_mem in Hs.
  unfold SWINVt in *.
  unfold substaskst.
  unfold SWINV in *.
  sep normal in Hsw.
  destruct Hsw; destruct H.

  sep remember (2::4::5::nil)%nat in H.
  simpl in H; simpljoin1.
  destruct l; destruct p.
  substs.
(*  
  sep normal.
  exists x x0.
  sep remember (2::4::5::nil)%nat in H.
  sep remember (2::4::5::nil)%nat.
  simpl in H.
  simpl; simpljoin1.
  do 6 eexists.
  splits; eauto.
  eapply join_emp; auto.
  eapply join_emp; auto.
  unfold emposabst; splits; auto.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; auto.
  destruct l, p.
*)

  Definition AOSTCBList'' :=
    fun (p1 p2 : val) (l1 l2 : list vallist) (rtbl : vallist)
        (hcurt : addrval) (tcbls : TcbMod.map) (pf : val) =>
      ((EX (tail1 tail2 : val) (tcbls1 tcbls2 : TcbMod.map),
        GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
           tcbdllseg p1 Vnull tail1 p2 l1 **
           tcbdllseg p2 tail1 tail2 Vnull l2 **
           [|p1 <> Vnull /\ p2 = Vptr hcurt|] **
           [|join tcbls1 tcbls2 tcbls|] **
           [|TCBList_P p1 l1 rtbl tcbls1|] **
           [|TCBList_P p2 l2 rtbl tcbls2|] **
           tcbdllflag p1 (l1 ++ l2) ** [|p2 <> pf|])
         \\//
         ( EX (tail : val),
           GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
              tcblist p1 Vnull tail Vnull (l1 ++ l2) rtbl tcbls **
              TCB_Not_In p2 p1 (l1 ++ l2) **
              tcbdllflag p1 (l1 ++ l2) **
              [|p1 <> Vnull /\ p2 = Vptr hcurt|] ** [|p2 = pf|])).
  
  Lemma AOSTCBList'_AOSTCBList'' :
    forall a b c d e f g h P,
      AOSTCBList' a b c d e f g h **P <==>   GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> b ** AOSTCBList'' a b c d e f g h **P.
  Proof.
    intros.
    unfold AOSTCBList'; unfold AOSTCBList''.
    split; intros; sep cancel P. 
    destruct H.
    sep destruct H.
    sep cancel 3%nat 1%nat.
    left.
    sep auto; eauto.
    sep destruct H.
    sep cancel 2%nat 1%nat.
    right.
    sep auto; eauto.

    sep lift 2%nat in H.
    apply disj_split in H.
    destruct H.
    left.
    sep auto; eauto.
    right.
    sep auto; eauto.
  Qed.
  
  Definition osinv'' :=
    EX (eventl osql qblkl : list vallist) (msgql : list EventData)
       (ectrl : list EventCtr) (ptbl : vallist) (p1 p2 : val)
       (tcbl1 : list vallist) (tcbcur : vallist) (tcbl2 : list vallist)
       (rtbl : vallist) (rgrp : val) (ecbls : EcbMod.map) 
       (tcbls : TcbMod.map) (t : int32) (ct vhold : addrval) 
       (ptfree : val) (lfree : list vallist),
    GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-r-> p2 **
    AOSTCBList'' p1 p2 tcbl1 (tcbcur :: tcbl2) rtbl ct tcbls ptfree **
    AOSEventFreeList eventl **
    AOSQFreeList osql **
    AOSQFreeBlk qblkl **
    AECBList ectrl msgql ecbls tcbls **
    AOSMapTbl **
    AOSUnMapTbl **
    AOSTCBPrioTbl ptbl rtbl tcbls vhold **
    AOSIntNesting **
    AOSTCBFreeList' ptfree lfree ct tcbls  **
    AOSRdyTblGrp rtbl rgrp **
    AOSTime (Vint32 t) **
    HECBList ecbls **
    HTCBList tcbls **
    HTime t **
    HCurTCB ct **
    AGVars ** [|RH_TCBList_ECBList_P ecbls tcbls ct|] ** A_isr_is_prop.
  
  Lemma osinv''_OSInv: forall P,
      osinv'' ** P <==> OSInv ** P.
  Proof.
    unfold osinv'', OSInv.
    split.
    intros.
    sep cancel P.
    sep destruct H.
    rewrite <- AOSTCBList'_AOSTCBList'' in H.
    sep auto.
    intros.
    sep cancel P.
    sep destruct H.
    sep eexists.
    rewrite <- AOSTCBList'_AOSTCBList'' .
    sep auto.
  Qed.

  Lemma starinv_isr_set_highest_tid :
    forall n low i0 e e0 m c O ab tid b tp tp' ct M' x11 i,
      (forall i : hid, x11 i = false) ->
      EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
      store (Tptr tp) m (b, 0) (Vptr tid) = Some M' ->
      (e, e0, m, x11, (i, i0, c), O, ab) |= AHprio GetHPrio tid ** Atrue -> 
      (e, e0, m, x11, (i, i0, c), O, ab) |= GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** starinv_isr I low n ->
      (exists tls,
          get O abtcblsid = Some (abstcblist tls) /\
          (indom tls ct /\
           (e, e0, M', x11, (i, i0, c), set O curtid (oscurt tid), ab)
             |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid) \/
           ~ indom tls ct /\
           (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
               satp (e, e0, Mx, x11, (i, i0, c)) Ox (EX lg, OSLInv ct lg) ->
               join M' Mx MM ->
               join O Ox OO ->
               (e, e0, MM, x11, (i, i0, c), set OO curtid (oscurt tid), ab)
                 |= starinv_isr I low n ** (EX tp0 : type, GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid)))).
  Proof.
    inductions n; intros.
    unfold starinv_isr in *.
    destruct low.
    sep normal in H3.
    destruct H3.
    apply disj_split in H3.
    destruct H3.
    simpl in H3; simpljoin1.
    tryfalse. 
    sep remember (1::nil)%nat in H3.
    simpl in H3; simpljoin1.

    unfold I in *; unfold getinv in *.
(*    sep normal.
    sep eexists.
    rewrite disj_split.
    right.
    sep normal.
    sep remember (1::nil)%nat.
    simpl_sat_goal.
    do 6 eexists.
    splits; eauto. 
    apply join_emp; auto. 
    apply join_emp; auto.
    simpl; splits; eauto.
    unfold emposabst; splits; eauto.
    unfolds; auto.
    substs.  
 *)
    
    Lemma OSInv_set_curtid1 :
      forall e e0 M M' isr st O ab b tp tp0 tid ct P,
        EnvMod.get e OSTCBCur = Some (b, Tptr tp) ->
        store (Tptr tp) M (b, 0) (Vptr tid) = Some M' ->
        (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
        (e, e0, M, isr, st, O, ab) |= OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr ct ** P ->
    exists tls,
      get O abtcblsid = Some (abstcblist tls) /\
      (indom tls ct /\
       (e, e0, M', isr, st, set O curtid (oscurt tid), ab)
         |= OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P \/
    ~ indom tls ct /\
    (forall (Mx : mem) (Ox : osabst) (MM : mem) (OO : osabst),
     satp (e, e0, Mx, isr, st) Ox (EX lg, OSLInv ct lg) ->
     join M' Mx MM ->
     join O Ox OO ->
     (e, e0, MM, isr, st, set OO curtid (oscurt tid), ab)
     |=  OSInv ** GV OSTCBCur @ Tptr tp0 |-r-> Vptr tid ** P)).
  Proof.
    intros.
    rewrite <- osinv''_OSInv in H2.
    unfold osinv'' in H2.
    sep normal in H2.
    sep destruct H2.
    assert (get O abtcblsid = Some (abstcblist x13)).
    sep remember (15::nil)%nat in H2.
    simpl in H2; simpljoin1.
    eapply join_get_l; eauto.
    eexists.
    split; eauto.
    
(*    rewrite <- osinv''_OSInv.
    unfold osinv'' in *.
    sep normal in H2.
    sep destruct H2.
 *)
    
    Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_indom :
      forall p1 p2 l1 curtcb l2 rtbl ct tcbls lfree pf s P tid,
        RH_CurTCB tid tcbls ->
        indom tcbls ct ->
        s |= AOSTCBList'' p1 p2 l1 (curtcb::l2) rtbl ct tcbls pf **
          AOSTCBFreeList' pf lfree ct tcbls ** P ->
        exists l1' curtcb' l2' pf' lfree',
          s |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls pf' **
            AOSTCBFreeList' pf' lfree' tid tcbls ** P.
    Proof.
      intros.
      rename H0 into H_indom.
      rename H1 into H0.
      unfold AOSTCBList'' in H0.
      unfold AOSTCBFreeList' in H0.
      
      (*4 cases*)
      apply disj_split in H0.
      destruct H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      sep lift 6%nat in H0.
      apply disj_split in H0.
      destruct H0.

      (*1*)
      unfold TCBFree_Not_Eq in H0.
      sep split in H0; simpljoin1.
      unfolds in H; simpljoin1.
      sep lifts (4::5::nil)%nat in H0.
      pose proof H2 tid.
      unfold get in H; simpl in H.
      rewrite H in H7.
      destruct (TcbMod.get x1 tid) eqn : eq1;
        destruct (TcbMod.get x2 tid) eqn : eq2;
        tryfalse.
      substs.
      (*tid in x1*)
      lets Hx : tcb_list_split_by_tcbls eq1 H3 H0.
      simpljoin1.
      assert (
        s |= tcbdllseg p1 Vnull x11 (Vptr tid) x6 **
          tcbdllseg (Vptr tid) x11 x (Vptr ct) (x7 :: x8) **
          tcbdllseg (Vptr ct) x x0 Vnull (curtcb :: l2) **
          assertion.sll pf lfree OS_TCB_flag V_OSTCBNext **
          sllfreeflag pf lfree **
          GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
          tcbdllflag p1 ((x6 ++ x7 :: x8) ++ curtcb :: l2) **
          GV OSTCBFreeList @ Tptr os_ucos_h.OS_TCB |-> pf ** P  
        ) as H7_bak by auto.
      sep lifts (2::3::nil)%nat in H7.
      assert (V_OSTCBNext (last (x7 :: x8) nil) = Some (Vptr ct)) as H_last.
      eapply tcbdllseg_last_nextptr in H7; auto.
      eapply tcbdllseg_compose in H7.
      
      lets Hx: TCBList_P_combine_copy H9 H4.
      instantiate (1:=merge x10 x2).
      clear - H2 H10.
      eapply TcbMod.join_merge_disj.
      apply join_comm in H10.
      eapply TcbMod.join_join_disj_l; eauto.
      assert (x7 :: x8 <> nil) by auto.
      apply Hx in H11; auto; clear Hx.
      replace ((x7 :: x8) ++ curtcb :: l2) with (x7 :: x8 ++ curtcb :: l2) in H7, H11.
      exists x6 x7 (x8 ++ curtcb :: l2) pf lfree.
      unfold AOSTCBList''.
      apply disj_split.
      left.
      sep normal.
      do 4 eexists.
      sep split; eauto.
      sep cancel 5%nat 1%nat.
      sep cancel 2%nat 1%nat.
      sep cancel 1%nat 1%nat.
      replace ((x6 ++ x7 :: x8) ++ curtcb :: l2) with (x6 ++ x7 :: x8 ++ curtcb :: l2) in H7.
      sep cancel 3%nat 1%nat.
      unfold AOSTCBFreeList'.
      sep auto.
      left.
      unfold TCBFree_Not_Eq.
      sep auto.
      clear - H7_bak.
      sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
      clears.
      Lemma tcbdllseg_sll_neq :
        forall ct lfree pf s tid x x7 x8 x11 H,
          s
           |= tcbdllseg (Vptr tid) x11 x ct (x7 :: x8) **
           assertion.sll pf lfree OS_TCB_flag V_OSTCBNext ** H ->
          pf <> Vptr tid.
      Proof.
        intros.
        intro; substs.
        unfold assertion.sll in H0.
        destruct lfree.
        unfold sllseg in H0; fold sllseg in H0; sep split in H0; tryfalse.
        unfold sllseg in H0; fold sllseg in H0.
        unfold tcbdllseg in H0.
        unfold dllseg in H0; fold dllseg in H0.
        sep normal in H0.
        sep destruct H0.
        sep split in H0; simpljoin1.
        inverts H1; inverts H3.
        sep lifts (1::3::nil)%nat in H0.
        eapply os_inv.node_OS_TCB_dup_false; eauto.
      Qed.
      eapply tcbdllseg_sll_neq; eauto.
      
      rewrite <- app_assoc.
      auto.
      
      clear - H7_bak.
      sep remember (2::4::nil)%nat in H7_bak; clear HeqH.
      clears.
      assert (pf <> Vptr tid).
      eapply tcbdllseg_sll_neq; eauto.
      auto.
      clear - H2 H10.
      eapply join_merge23_join; eauto.
      rewrite app_comm_cons; auto.

      (*tid in x2*)
      substs.
      sep lift 2%nat in H0.
      lets Hx : tcb_list_split_by_tcbls eq2 H4 H0.
      simpljoin1.
      assert (
        s
       |= tcbdllseg (Vptr ct) x x11 (Vptr tid) x6 **
          tcbdllseg (Vptr tid) x11 x0 Vnull (x7 :: x8) **
          tcbdllseg p1 Vnull x (Vptr ct) l1 **
          assertion.sll pf lfree OS_TCB_flag V_OSTCBNext **
          sllfreeflag pf lfree **
          GV OSTCBList @ Tptr os_ucos_h.OS_TCB |-> p1 **
          tcbdllflag p1 (l1 ++ curtcb :: l2) **
          GV OSTCBFreeList @ Tptr os_ucos_h.OS_TCB |-> pf ** P
        ) as H7_bak by auto.
(*      assert (V_OSTCBNext (last l1 nil) = Some (Vptr ct)) as H_last.
(* ** ac:       Check  TCBList_P_combine_copy. *)

     
      eapply tcbdllseg_last_nextptr in H7; auto.
      eapply tcbdllseg_compose in H7.
 *)
      exists (l1 ++ x6) x7 x8 pf lfree.
      unfold AOSTCBList''.
      apply disj_split.
      left.
      sep normal.
      exists x11 x0 (merge x1 x9) x10.
      sep split; eauto.
      sep cancel 6%nat 1%nat.
      sep cancel 2%nat 2%nat.
      rewrite H11 in H7_bak.
      replace (l1 ++ x6 ++ x7 :: x8) with ((l1 ++ x6) ++ x7 :: x8) in H7_bak.
      sep cancel 5%nat 2%nat.
      unfold AOSTCBFreeList'.
      sep auto.
      sep lift 2%nat.
      apply disj_split.
      left.
      unfold TCBFree_Not_Eq.
      sep lifts (2::1::nil)%nat in H7_bak.
      eapply tcbdllseg_compose in H7_bak.
      sep auto.

      clear - H7.
      sep lifts (2::4::nil)%nat in H7.
      eapply tcbdllseg_sll_neq; eauto.
      
      rewrite <- app_assoc.
      auto.

      assert (pf <> Vptr tid).
      sep lifts (2::4::nil)%nat in H7.
      eapply tcbdllseg_sll_neq; eauto.
      auto.

      clear - H1 H3 H8 H10 H2 H7.
      destruct l1.
      rewrite app_nil_l.
      simpl in H3; simpljoin1.
      sep remember (3::nil)%nat in H7.
      destruct_s s.
      simpl in H7; simpljoin1.
      rewrite jl_merge_emp'.
      auto.
      eapply TCBList_P_combine_copy; eauto.
      clear - H2 H10.
      eapply TcbMod.join_merge_disj.
      apply join_comm in H2.
      apply TcbMod.disj_comm.
      eapply TcbMod.join_join_disj_l; eauto.
      sep lift 3%nat in H7.
      eapply tcbdllseg_last_nextptr; eauto.

      clear - H2 H10.
      eapply join_join_join_merge; eauto.

      (*2 false*)
      unfold TCBFree_Eq in H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      simpljoin1.
      tryfalse.

      sep normal in H0; sep destruct H0.
      sep split in H0.
      sep lift 6%nat in H0.
      apply disj_split in H0.
      destruct H0.
      (*3 false*)
      unfold TCBFree_Not_Eq in H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      simpljoin1.
      tryfalse.

      (*4*)
      simpljoin1.
      
      Lemma tcblist_indom_ptr_in_tcblist :
        forall vltcb head rtbl tcbls ct,
          TCBList_P head vltcb rtbl tcbls ->
          indom tcbls ct ->
          ptr_in_tcblist (Vptr ct) head vltcb.
      Proof.
        inductions vltcb; intros.
        simpl in H; substs.
        unfolds in H0; destruct H0.
        rewrite emp_sem in H; tryfalse.

        unfold1 TCBList_P in H; simpljoin1.
        unfold ptr_in_tcblist.
        unfold1 ptr_in_tcbdllseg.
        destruct (beq_val (Vptr ct) (Vptr x)) eqn : eq1; auto.
        rewrite H1.
        eapply IHvltcb; eauto.
        clear - H2 H0 eq1.
        unfold indom in *; simpljoin1.
        exists x0.
        unfolds in H2.
        assert (ct <> x).
        intro; substs.
        unfold beq_val in eq1.
        unfolds in eq1.
        destruct x.
        rewrite beq_pos_Pos_eqb_eq in eq1.
        rewrite Int.eq_true in eq1.
        assert (b = b) by auto.
        apply Pos.eqb_eq in H0.
        rewrite H0 in eq1.
        simpl in eq1; tryfalse.
        clear eq1.
        hy.
      Qed.

      unfold TCB_Not_In in H0.
      unfold tcblist in H0.
      sep split in H0.
      lets Hx: tcblist_indom_ptr_in_tcblist H2 H_indom.
      simpljoin1.
      false; apply H3; auto.
    Qed.

    assert (os_ucos_h.OS_TCB = tp0).
    sep remember (1::21::nil)%nat in H2.
    simpl in H2; simpljoin1.
    rewrite H27 in H18; inverts H18.
    auto.
    subst tp0.
    
    assert (x6 = Vptr x15).
    sep remember (2::nil)%nat in H2.
    simpl in H2; simpljoin1.
    destruct H8; simpljoin1; auto.
    substs.
    sep remember (1::21::nil)%nat in H2.
    eapply sep_combine_lemmas.GV_combine_ro_frm in H2.
    sep split in H2.
    simpl in H2; simpljoin1.
    assert (x15 = ct).
    clear - H5.
    simpl in H5.
    destruct x15; destruct ct.
    inverts H5; auto.
    substs.
    
    assert (indom x13 ct \/ ~ indom x13 ct).
    unfold indom.
    destruct (get x13 ct) eqn : eq1; clear - eq1.
    left; eauto.
    right.
    intro; destruct H; tryfalse.
    destruct H2.
    (*indom tcbls ct*)
    left.
    split; auto.
    rewrite <- osinv''_OSInv.
    unfold osinv''.
    sep normal.
    unfolds in H14; simpl in H14.
    rewrite H in H14; inverts H14.
    lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
    simpljoin1.

    sep lifts (1::10::nil)%nat in H10.
    lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_indom H10; auto.
    unfolds.
    instantiate (TEMP11 := tid).
    clear - H1 H3.
    simpl in H1; simpljoin1.
    unfolds in H4; simpljoin1.
    assert (get O abtcblsid = Some (abstcblist x)).
    eapply join_get_l; eauto.
    rewrite H3 in H5.
    inverts H5.
    eauto.
    simpljoin1.
    sep eexists.

    sep lifts (1::21::nil)%nat.
    eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
    sep remember (1::nil)%nat.
    simpl.
    exists x15 x19.
    do 4 eexists.
    splits; eauto.
    eapply join_emp; eauto.
    do 7 eexists.
    splits; eauto.
    eapply join_emp; eauto.
    eapply join_emp; eauto.
    eexists.
    unfold emposabst; splits; eauto.
    unfolds.
    eexists; splits; eauto.
    unfolds in H15; simpljoin1.
    unfold store in H4.
    lets Hx: lmachLib.storebytes_ptomvallist_eqlen_infer p H4.
    simpl.
    destruct tid; destruct ct; simpl; auto.
    auto.
    unfolds; auto.
    substs.
    sep remember (16::nil)%nat in H5.
    simpl in H5; simpljoin1.
    sep remember (16::nil)%nat.
    simpl.
    do 6 eexists.
    splits; eauto.
    eapply join_emp; auto.
    eapply join_sig_set; eauto.
    substs.
    sep auto.

    (*not indom 13 ct*)
    right.
    split; auto.
    intros.

    pose proof H4 ab.
    
    Lemma AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom
      : forall (p1 p2 : val) (l1 : list vallist) (curtcb : vallist)
               (l2 : list vallist) (rtbl : vallist) (ct : addrval)
               (tcbls : TcbMod.map) (lfree : list vallist) 
               (pf : val) (P : asrt) (tid : Modules.tid) e e0 isr st ab M O Mx Ox MM OO,
        RH_CurTCB tid tcbls ->
        ~indom tcbls ct ->
        (e, e0, M, isr, st, O, ab)
          |= AOSTCBList'' p1 p2 l1 (curtcb :: l2) rtbl ct tcbls pf **
          AOSTCBFreeList' pf lfree ct tcbls ** P ->
        join M Mx MM ->
        join O Ox OO ->
        (e, e0, Mx, isr, st, Ox, ab) |= EX lg : list logicvar, OSLInv ct lg ->
        exists l1' curtcb' l2' pf' lfree',
          (e, e0, MM, isr, st, OO, ab)
            |= AOSTCBList'' p1 (Vptr tid) l1' (curtcb' :: l2') rtbl tid tcbls
            pf' ** AOSTCBFreeList' pf' lfree' tid tcbls ** P.
    Proof.
      intros.
      rename H0 into H_indom.
      rename H1 into H0.
      unfold AOSTCBList'' in H0.
      unfold AOSTCBFreeList' in H0.
      
      (*4 cases*)
      apply disj_split in H0.
      destruct H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      sep lift 6%nat in H0.
      apply disj_split in H0.
      destruct H0.

      (*1 false*)
      simpljoin1.
      unfold1 TCBList_P in H7.
      simpljoin1.
      inverts H7.
      clear - H5 H10 H_indom.
      false.
      apply H_indom.
      unfold indom.
      exists x6.
      unfolds in H10.
      eapply join_get_r; eauto.
      eapply join_get_l; eauto.
      apply get_sig_some.

      (*2 false*)
      unfold TCBFree_Eq in H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      simpljoin1.
      tryfalse.

      sep normal in H0; sep destruct H0.
      sep split in H0.
      sep lift 6%nat in H0.
      apply disj_split in H0.
      destruct H0.
      (*3 false*)
      unfold TCBFree_Not_Eq in H0.
      sep normal in H0; sep destruct H0.
      sep split in H0.
      simpljoin1.
      tryfalse.

      (*4*)
      simpljoin1.
      unfold TCBFree_Eq in H0.
      sep normal in H0.
      sep destruct H0.
      sep split in H0; simpljoin1.
      unfolds in H; simpljoin1.
      sep lift 6%nat in H0.
      unfold tcblist in H0.
      sep split in H0.
      lets Hx: tcb_list_split_by_tcbls H H5 H0.
      simpljoin1.
      exists x7 x8 x9.
      exists (Vptr ct) (x1::x0).
      unfold AOSTCBList''.
      apply disj_split.
      left.
      sep lift 2%nat.
      unfold AOSTCBFreeList'.
      sep normal.
      exists x12 x x10 x11.
      sep lift 11%nat.
      apply disj_split.
      left.
      sep split; auto.
      unfold TCB_Not_In in H10.
      sep split in H10.
      sep remember (3::4::5::6::nil)%nat in H10.
      sep remember (5::nil)%nat in H10.
      sep lift 2%nat in H10.
      simpl in H10; simpljoin1.
      sep remember (1::nil)%nat.
      simpl_sat_goal.
      exists (merge x13 Mx) x14 MM.
      exists (merge x16 Ox) x17 OO.
      splits; eauto.
      eapply mem_join_join_merge13_join'; eauto.
      eapply join_join_merge1; eauto.
      apply join_comm in H3; eauto.
      assert (
          (e, e0, merge x13 Mx, isr, st, merge x16 Ox, ab)
            |= (EX lg : list logicvar, OSLInv ct lg) ** Astruct ct OS_TCB_flag x1 **
           PV get_off_addr ct flag_off @ Tint8 |-r-> Vint32 (Int.repr 0) **
           assertion.sll x2 x0 OS_TCB_flag V_OSTCBNext ** sllfreeflag x2 x0
        ).
      sep remember (1::nil)%nat.
      simpl_sat_goal.
      exists Mx x13; eexists.
      exists Ox x16; eexists.
      splits; eauto.
      apply join_comm.
      apply join_merge_disj.
      clear - H19 H2.
      eapply mem_join_join_disjoint; eauto.
      apply join_comm.
      apply join_merge_disj.
      eapply osabst_join_join_disjoint; eauto.
      unfold OSLInv in H17.
      sep normal in H17.
      sep destruct H17.
      sep split in H17; simpljoin1.
      sep lifts (1::3::nil)%nat in H17.
      apply sep_combine_lemmas.PV_combine_ro_frm in H17.
      sep split in H17.
      unfold TCBFree_Not_Eq.
      sep split.
      unfold  assertion.sll in *.
      unfold1 sllseg.
      unfold sllfreeflag in *.
      unfold1 sllsegfreeflag.
      sep normal.
      sep eexists.
      sep split; eauto.
      inverts H24.
      unfold node; sep normal.
      sep eexists.
      sep split; eauto.
      assert (x18 = (Vint32 (Int.repr 0))).
      clear - H10 H20.
      unfolds in H20; destruct H20.
      substs.
      simpl in H10; tryfalse.
      auto.
      substs.
      sep auto.

      clear - H H_indom.
      intro.
      inverts H0.
      unfolds in H_indom.
      apply H_indom.
      unfold indom.
      eauto.

      substs.
      sep auto.
      rewrite <- H15.
      auto.

      clear - H H_indom.
      intro.
      inverts H0.
      unfolds in H_indom.
      apply H_indom.
      unfold indom.
      eauto.
    Qed.

    rewrite <- osinv''_OSInv.
    unfold osinv''.
    sep normal.
    unfolds in H14; simpl in H14.
    rewrite H in H14; inverts H14.
    lets Hx: lmachLib.store_mapstoval_frame H15 H6 H0.
    simpljoin1.

    sep remember (1::nil)%nat in H10.
    assert ((e, e0, M', isr, st, O, ab)
              |=  GV OSTCBCur @ Tptr os_ucos_h.OS_TCB |-> (Vptr tid) ** AOSTCBList'' x5 (Vptr ct) x7 (x8 :: x9) x10 ct x13 x17 ** H5).
    substs.
    sep remember (1::nil)%nat.
    simpl.
    do 6 eexists.
    splits; eauto.
    apply join_emp; auto.
    do 7 eexists.
    splits; eauto.
    eapply join_emp; eauto.
    apply join_emp; eauto.
    eexists.
    splits; eauto.
    unfolds; auto.
    unfolds.
    eexists; splits; eauto.
    unfolds in H15; simpljoin1.
    eapply lmachLib.storebytes_ptomvallist_eqlen_infer; eauto.
    simpl; destruct tid, ct; auto.
    unfolds; auto.
    substs.
    sep lifts (2::11::nil)%nat in H13.
    lets Hx: AOSTCBList'_AOSTCBFreeList_set_curtid_not_indom H13 H7 H8 H9.
    unfolds.
    instantiate (TEMP10 := tid).
    clear - H1 H3.
    simpl in H1; simpljoin1.
    unfolds in H4; simpljoin1.
    assert (get O abtcblsid = Some (abstcblist x)).
    eapply join_get_l; eauto.
    rewrite H3 in H5.
    inverts H5.
    eauto.
    auto.
    simpljoin1.
    sep eexists.
    sep lifts (1::21::nil)%nat.
    eapply sep_combine_lemmas.GV_combine_ro'_frm; eauto.
    sep remember (17::nil)%nat in H5.
    simpl in H5; simpljoin1.
    sep remember (17::nil)%nat.
    simpl.
    exists empmem MM.
    do 4 eexists.
    splits; eauto.
    eapply join_emp; auto.
    eapply join_sig_set; eauto.
    substs.
    sep auto.
  Qed.

  assert ((e, e0, m, x, (i, i0, c), O, ab)
            |= OSInv ** GV OSTCBCur @ Tptr tp' |-r-> Vptr ct ** Aemp).
  sep auto.
  lets Hx: OSInv_set_curtid1 H0 H1 H2 H3.
  simpljoin1.
  eexists.
  splits; eauto.
  destruct H5; simpljoin1.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  right.
  split; auto.
  intros.
  lets Hx: H6 H7 H10 H11.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  substs.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  sep auto.

  destruct low.
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  unfold atoy_inv in H9.
  unfold A_isr_is_prop in H9.
  unfold atoy_inv' in H9.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H7; simpljoin1.
  apply map_join_pos in H6; simpljoin1.
  rewrite emp_sem in H2; tryfalse.
  
  simpl getinv in *.
  sep normal in H3.
  destruct H3.
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.
  unfold aemp_isr_is in H9.
  unfold A_isr_is_prop in H9.
  simpl in H9; simpljoin1.
  simpl in H2; simpljoin1.
  unfolds in H6; simpljoin1.
  apply map_join_pos in H5; simpljoin1.
  rewrite emp_sem in H2; tryfalse.

  (*ind case*)
  unfold starinv_isr in *; fold starinv_isr in *.
  sep normal in H3; destruct H3.
(*  sep normal; exists x. *)
  apply disj_split in H3.
  destruct H3.
  simpl in H3; simpljoin1; tryfalse.
  sep remember (1::nil)%nat in H3.
  simpl in H3; simpljoin1.

  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  eapply OSInv_set_curtid1 in H9; eauto.
  simpljoin1.
  destruct H4; simpljoin1.
  eexists; splits; eauto.
  left.
  split; auto.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.

  eexists.
  splits; eauto.
  right.
  split; eauto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  
  destruct low.
  unfold I in *; fold I in *; unfold getinv in *.
  false.

  Lemma AHprio_starinv_isr_atoy_inv_false :
    forall e e0 M M1 M2 isr st O o1 o2 ab n i tid,
      join o1 o2 O -> (i > 0)%nat -> (forall i : hid, isr i = false) ->
      (e, e0, M, isr, st, O, ab) |= AHprio GetHPrio tid ** Atrue ->
      (e, e0, M1, isr, st, o2, ab) |= starinv_isr I i n ->
      (e, e0, M2, isr, st, o1, ab) |= atoy_inv ->
      False.
  Proof.
    intros.
    apply starinv_isr_osabst_emp in H3; auto.
    apply atoy_inv_osabst_emp in H4; auto.
    substs.
    simpl in H2; simpljoin1.
    unfolds in H6; simpljoin1.
    pose proof H5 abtcblsid.
    pose proof H abtcblsid.
    rewrite OSAbstMod.emp_sem in H8.
    destruct (OSAbstMod.get O abtcblsid) eqn : eq1; tryfalse.
    destruct (OSAbstMod.get x2 abtcblsid) eqn: eq2; tryfalse.
    destruct (OSAbstMod.get x3 abtcblsid); tryfalse.
    destruct (OSAbstMod.get x3 abtcblsid) eqn : eq3; tryfalse.
    unfold get in H2; simpl in H2; rewrite H2 in eq2; tryfalse.
  Qed.

  simpl_sat H9; simpljoin1.
  simpl in H13; simpljoin1.
  eapply AHprio_starinv_isr_atoy_inv_false with (i:=2%nat); eauto.

  sep remember (1::nil)%nat in H9.
  simpl_sat H9; simpljoin1.
  simpl in H9; simpljoin1.
  lets Hx: IHn H H0 H1 H2 H10.
  simpljoin1.
  eexists; splits; eauto.
  destruct H4; simpljoin1.
  left.
  split; auto.
  sep normal in H5; destruct H5.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.

  right.
  split; auto.
  intros.
  lets Hx: H5 H6 H7 H9.
  sep normal in Hx; destruct Hx.
  sep normal.
  sep eexists.
  sep lift 2%nat.
  apply disj_split.
  right.
  sep normal.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; eauto.
  apply join_emp; eauto.
  unfold emposabst.
  splits; eauto.
  substs.
  simpl getinv.
  unfold aemp_isr_is.
  unfold A_isr_is_prop.
  sep auto.
  Qed.

  unfold invlth_isr in *.
  rewrite Nat.sub_0_r in *.
  lets Hx: starinv_isr_set_highest_tid H18 Hget Hs Hpr H15.
  simpljoin1.
  eexists.
  splits;eauto.
  destruct H0; simpljoin1.
  left.
  split; auto.
  sep normal in H1; destruct H1.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  do 6 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep auto.
  rewrite Nat.add_0_r.
  auto.

  right.
  split; auto.
  intros.
  lets Hx: H1 H2 H3 H4.
  sep normal in Hx.
  destruct Hx.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  eexists.
  unfold emposabst.
  splits; eauto.
  substs.
  sep remember (1::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  sep normal.
  pose proof H2 ab.
  destruct H6.
  unfold OSLInv in H6.
  destruct H6.
  simpl in H6; simpljoin1.
  sep eexists.
  rewrite Nat.sub_0_r.
  sep remember (2::nil)%nat.
  simpl.
  exists empmem.
  do 5 eexists.
  splits; eauto.
  apply join_emp; auto.
  apply join_emp; auto.
  unfold emposabst.
  splits; eauto.
  substs.
  rewrite Nat.add_0_r.
  sep auto.

- apply GoodSched_GetHPrio.
Qed.



*)
Require Import derived_rules.
Import rulesoundlib.
Import DeprecatedTactic.
Open Scope nat_scope.
Require Import Lia.
Lemma starinv_isr_elim1':
  forall e0 e1 x0 i i0 si x3 P ab j r,
  (e1, e0, x0, i, i0, (false, si, nil), x3, ab) |= (([|r (S j) = true|] //\\ Aisr r) \\//
  ([|r (S j) = false|] //\\ Aisr r) ** getinv (I (S j))) ** P ->
  (e1, e0, x0, i, i0, (false, si, nil), x3, ab) |= P.
Proof.
  intros.
  simpl in H.
  simpljoin.
  destruct H3.
  destruct H.
  destruct H1 as (_&Hx&_).
  destruct H as (_&_&H).
  unfold emposabst in H.
  subst.
  eapply join_emp_eq in H0.
  eapply join_emp_eq in H2.
  subst; auto.
  destruct H as (y1&y2&y3&y4&y5&y6&H11&H12&H13&H14&H15&H).
  destruct H as (y11&y12&y13&y14&y15&y16&H21&H22&H23&H24&H25&H).
  destruct H as (y21&y22&y23&y24&y25&y26&y27&y28&H31&H32&H33&H34&H35&H).
  destruct H as (y31&y32&y33&y34&y35&y36&H41&H42&H43&H44&H45&H).
  destruct H as (_&H&H').
  destruct H45 as (_&H45&H45').
  subst.
  eapply join_emp_eq in H42.
  subst y24.
  destruct H35 as (_&H35&H35').
  subst y23.
  eapply join_emp_eq in H32.
  subst y12.
  destruct H25 as (H25&H25').
  subst y11.
  eapply join_emp_eq in H22.
  subst y2.
  destruct H15.
  destruct H1 as (_&H1&H1').
  subst y1.
  eapply join_emp_eq in H12.
  subst x.
  eapply join_emp_eq in H0.
  subst x1.
  unfold emposabst in *.
  subst.
  eapply join_emp_eq in H44.
  subst y27.
  eapply join_emp_eq in H34.
  subst y15.
  eapply join_emp_eq in H24.
  subst y5.
  eapply join_emp_eq in H14.
  subst x4.
  eapply join_emp_eq in H2.
  subst x5.
  auto.
Qed.

Lemma starinv_isr_elim1:
  forall e0 e1 x0 i i0 si x3 ab j r,
  (e1, e0, x0, i, i0, (false, si, nil), x3, ab) |= ([|r (S j) = true|] //\\ Aisr r) \\//
  ([|r (S j) = false|] //\\ Aisr r) ** aemp_isr_is ->
  (e1, e0, x0, i, i0, (false, si, nil), x3, ab) |= Aemp.
Proof.
  intros.
  assert ((e1, e0, x0, i, i0, (false, si, nil), x3, ab)
          |= (([|r (S j) = true|] //\\ Aisr r) \\//
          ([|r (S j) = false|] //\\ Aisr r) ** aemp_isr_is) ** Aemp).
  sep auto.
  eapply starinv_isr_elim1' in H0.
  auto.
Qed.

Lemma invlth_isr_emp: 
  forall e1 e0 x0 i i0 si x3 hid,
  hid < INUM ->
  (e1, e0, x0, i, i0, (false, si, nil), x3, absopx) |= invlth_isr I (hid + 1) INUM ->
  (e1, e0, x0, i, i0, (false, si, nil), x3, absopx) |= Aemp.
Proof.
  introv Hhid H.
  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&z10&z11&z12&z13&z14&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.
  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&z10&z11&z12&z13&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.
  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&z10&z11&z12&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&z10&z11&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.
  
  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&z10&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&z9&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&z8&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&z7&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&z6&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&z5&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&z4&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&z3&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&z2&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&z1&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&z0&H).
  eapply starinv_isr_elim1' in H.
  eapply starinv_isr_elim1 in H.
  auto.

  destruct hid.
  unfold invlth_isr in H.
  trysimplsall.
  sep normal in H.
  destruct H as (z&H).
  eapply starinv_isr_elim1 in H.
  auto.

  replace (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S hid)))))))))))))))) with (hid+16) in Hhid by lia.
  unfold INUM in Hhid.
  assert (hid + 16 < 16 -> False) by lia.
  false.
Qed.


Lemma starinv_isr_add:
  forall e0 e1 i i0 si ab x1 x6,
  (e1, e0, x1, i, i0, (false, si, nil), x6, absopx) |= getinv (I (S INUM)) ->
  (e1, empenv, empenv, isrupd i 1 true, ierupd i0 1 false, (false, 1 :: si, nil), empenv, ab) |= invlth_isr I (1 + 1) INUM.
Proof.
  intros.
  unfold invlth_isr.
  simpl.
  simpljoin.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.

  exists (isrupd i 1 true).
  destruct (isrupd i 1 true).
  left.
  mytac.
  right.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists (isrupd i 1 true) (1::si).
  exists empmem empmem empmem empabst empabst empabst; mytac.
  exists empmem empmem empmem empabst empabst empabst; mytac.
  simpl in H.
  simpljoin.
  unfold isr_is_prop in *.
  intros.
  unfold isrupd.
  remember ( beq_nat 1 x) as X.
  destruct X.
  symmetry in HeqX.
  apply beq_nat_true in HeqX.
  subst.
  simpl in H.
  destruct H.
  left;auto.
  simpl in H.
  apply H14.
  intro.
  destruct H.
  right;auto.
Qed.

Lemma isr_true_S_i_rev':
  forall I i ge le M ir er ie is cs ie' cs' ab ab' O j,
    i<j ->
    (ge,le,M,ir,er,(ie,is,cs),O,ab) |= invlth_isr I (i+1)%nat j ->
    (ge,le,M,isrupd ir i true, ierupd er i false,(ie',i::is,cs'),O,ab') |= invlth_isr I (i+1)%nat j.
Proof.
  introv Hij Hinv.
  unfold invlth_isr in *.
  replace (i+1) with (S i) in * by lia. 
  eapply  starinv_isr_prop4' ; eauto.
  eapply inv_isr_irrev_prop_noempisr; eauto.
  Unshelve. all: first [exact nil | exact false].
Qed.

Lemma invariant_prop_map1 :
forall (A B T : Type) (MC : PermMap A B T) x x0 x1 x4,
  usePerm = true ->
  disjoint x x0 ->
  join x1 x4 x0 ->
  disjoint (merge x4 x) x1.
hy.
(** TODO **)
Qed.

Lemma invariant_prop_map2 :
forall (A B T : Type) (MC : PermMap A B T) x x0 x1 x4,
  usePerm = true ->
  disjoint x x0 ->
  join x1 x4 x0 ->
  disjoint (merge x x4) x1.
hy.
(** TODO **)
Qed.



Lemma int_mem_trans1
: forall sd p C C' o o' Ms Os Ml li,
    GoodI I sd li->
    lintstep p C o C' o' ->
    disjoint Ml Ms ->
    merge Ml Ms = get_mem (get_smem o) ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    exists Ms' Ml' Os' Ol,
      Ms = merge Ml' Ms' /\
      disjoint Ml' Ms' /\
      Os = merge Os' Ol /\
      disjoint Ol Os' /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I).
Proof.
  introv Hgoodi.
  intros.
  destruct o as [[[[[]]]]].
  destruct o' as [[[[[]]]]].
  inversion H;subst.
  simpl in H1.
  subst m0.
  
  lets Hinv: H2 absopx.
  unfold INV in *.
  unfold sat in Hinv;fold sat in Hinv;trysimplsall;mytac;tryfalse.
  destruct H7.
  Focus 2.
  unfold inv_ieoff in H1;unfold sat in H1;fold sat in H1;trysimplsall;mytac;tryfalse.
  unfold inv_ieon in *.
  unfold sat in H1;fold sat in H1;trysimplsall;mytac.
  simpl in H11.
  unfold emposabst in *.
  destruct H11.
  subst.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  
  apply join_emp_eq in H4.
  subst x4.
  apply join_emp_eq in H8.
  subst x7.
  
  apply invlth_divide with (i:=i3) in H10;auto.
  mytac.
  exists (merge x x4) x1 (merge x2 x6) x5.
  mytac.

  eapply mem_join_join_merge_eq;eauto.
  apply disjoint_sym.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  assert (disjoint (merge x4 x) x1).

  eapply invariant_prop_map1; eauto.
  
  (* eapply mem_disj_join_disjmerge;eauto. *)
  (* apply disj_merge_intro_l . *)
  (* apply disj_merge_elim_l in H10. *)
  (* destruct H10. *)
  (* auto. *)

  eapply invariant_prop_map2; eauto.
  
  eapply abst_join_join_merge_eq';eauto.
  apply disjoint_sym.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  assert (OSAbstMod.disj (OSAbstMod.merge x6 x2) x5).

  eapply abst_disj_join_disjmerge;eauto.
  apply disj_merge_intro_l.
  unfold usePerm; simpl; auto.
  apply OSAbstMod.disj_merge_elim_l in H10.
  destruct H10.
  apply osabst_disj_disjoint in H10.
  apply osabst_disj_disjoint in H11.
  split; auto.
  
  intros.
  unfold sat;fold sat;trysimplsall;mytac.
  unfold assertion.getmem.
  unfold get_mem; unfold get_smem.
  exists x x4 (merge x x4) x2 x6 (OSAbstMod.merge x2 x6).
  mytac.
  apply join_merge_disj.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  apply join_comm in H1.
  apply disjoint_sym in H3.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.
  unfold merge; simpl; auto.
  
  apply OSAbstMod.join_merge_disj.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  apply OSAbstMod.join_comm in H4.
  apply OSAbstMod.disj_sym in H5.
  apply OSAbstMod.disj_sym.

  eapply abst_join_disj_disj;eauto.
  eapply good_inv_prop;eauto.
  apply invp.
  assert (inv_prop (getinv (I (S INUM)))).
  apply prec.
  unfolds in H9.
  destruct H9.
  unfolds in H10.
  mytac.
  eapply H11 with (i:=i3) in H6.
  simpl in H6.
  eapply H6.
  right.
  unfold inv_ieoff.
  unfold sat;fold sat;trysimplsall;mytac.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; splits; auto.
  exists i3.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  left.
  exists empmem x4 x4 empabst x6 x6;mytac.
  auto.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  
  eapply isr_true_S_i_rev;eauto.
  unfold invlth_isr in *.
  eapply inv_isr_irrev_prop;eauto.

  simpl in H1.
  subst m0.
  
  lets Hinv: H2 absopx.
  unfold INV in *.
  unfold sat in Hinv;fold sat in Hinv;trysimplsall;mytac;tryfalse.
  destruct H7.
  (*Focus 2.
  unfold inv_ieoff in H1;unfold sat in H1;fold sat in H1;trysimplsall;mytac;tryfalse.
*)  unfold inv_ieon in *.
  unfold sat in H1;fold sat in H1;trysimplsall;mytac.
  simpl in H11.
  unfold emposabst in *.
  destruct H11.
  subst.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  
  apply join_emp_eq in H4.
  subst x4.
  apply join_emp_eq in H8.
  subst x7.
  
  apply invlth_divide with (i:=1%nat) in H10;auto.
  mytac.
  exists (merge x x4) x1 (merge x2 x6) x5.
  mytac.

  eapply mem_join_join_merge_eq;eauto.
  apply disjoint_sym.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  assert (disjoint (merge x4 x) x1).
  eapply invariant_prop_map1; eauto.
  eapply invariant_prop_map2; eauto.
  
  eapply abst_join_join_merge_eq';eauto.
  apply disjoint_sym.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  assert (OSAbstMod.disj (OSAbstMod.merge x6 x2) x5).

  eapply abst_disj_join_disjmerge;eauto.
  apply disj_merge_intro_l.
  unfold usePerm; simpl; auto.
  apply OSAbstMod.disj_merge_elim_l in H10.
  destruct H10.
  apply osabst_disj_disjoint in H10.
  apply osabst_disj_disjoint in H11.
  split; auto.
  
  intros.
  unfold sat;fold sat;trysimplsall;mytac.
  unfold assertion.getmem.
  unfold get_mem; unfold get_smem.
  exists x x4 (merge x x4) x2 x6 (OSAbstMod.merge x2 x6).
  mytac.
  apply join_merge_disj.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3.
  apply join_comm in H1.
  apply disjoint_sym in H3.
  apply disjoint_sym.
  eapply mem_join_disjoint_disjoint; eauto.
  unfold merge; simpl; auto.
  
  apply OSAbstMod.join_merge_disj.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5.
  apply OSAbstMod.join_comm in H4.
  apply OSAbstMod.disj_sym in H5.
  apply OSAbstMod.disj_sym.

  eapply abst_join_disj_disj;eauto.
  eapply good_inv_prop;eauto.
  apply invp.
  assert (inv_prop (getinv (I (S INUM)))).
  apply prec.
  unfolds in H9.
  destruct H9.
  unfolds in H10.
  mytac.
  eapply H11 with (i:=1%nat) in H6.
  simpl in H6.
  eapply H6.
  right.
  unfold inv_ieoff.
  unfold sat;fold sat;trysimplsall;mytac.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; split; auto.
  unfolds; auto.
  exists 1%nat.
  exists empmem x4 x4 empabst x6 x6;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  left.
  exists empmem x4 x4 empabst x6 x6;mytac.
  auto.
  unfold INUM.
  lia.
  simpl;unfold emposabst;auto. 
  eapply isr_true_S_i_rev';eauto.
  unfold INUM.
  lia.
  unfold INUM.
  lia.

  lets Hinv: H2 absopx.
  unfold sat in Hinv;fold sat in Hinv;trysimplsall;mytac;tryfalse.
  destruct H11.
  unfold inv_ieoff in H1.
  unfold sat in H1;fold sat in H1;trysimplsall;mytac.
  unfold inv_ieon in H4;unfold sat in H4;fold sat in H4;trysimplsall;mytac;tryfalse.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  unfold inv_ieoff in H1.
  unfold sat in H1;fold sat in H1;trysimplsall;mytac.
  simpl in H23.
  unfold emposabst in *.
  destruct H23.
  subst.
  unfold assertion.getmem in *.
  unfold get_smem in *; unfold get_mem in *.
  apply join_emp_eq in H8.
  subst x8.
  apply join_emp_eq in H12.
  subst x11.

  simpl in H22.
  unfold emposabst in *.
  destruct H22.
  subst.
  apply join_emp_eq in H15.
  apply join_emp_eq in H17.
  subst.
  destruct H20.
  destruct H1 as (M1 & M2 & M & o1 & o2 & o & HM & HjoinM & Ho & Hjoino & Hsat & H1).
  subst.
  destruct Hsat as (Hsi & Hempst).
  simpl in Hempst.
  unfold emposabst in *.
  destruct Hempst.
  subst.
  apply join_emp_eq in HjoinM.
  apply join_emp_eq in Hjoino.
  subst.

  exists (merge x x0) empmem (merge x2 x3) empabst.
  mytac.

  eapply mem_join_join_merge_eq;eauto.
  join auto.
  eapply disjoint_emp_r.
  eapply abst_join_join_merge_eq';eauto.
  eapply OSAbstMod.join_emp.
  auto.
  eapply disjoint_emp_r.
  intro.
  unfold sat;fold sat;trysimplsall;mytac.
  exists x x0 (merge x x0) x2 x3 (merge x2 x3).
  splits; eauto.
  apply join_merge_disj.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3; auto.
  apply OSAbstMod.join_merge_disj.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5; auto.

  eapply good_inv_prop;eauto.
  apply invp.
  assert (inv_prop (getinv (I (S INUM)))).
  apply prec.
  unfolds in H8.
  destruct H8.
  unfolds in H11.
  mytac.
  eapply H12 with (i:=1%nat) in H6.
  simpl in H6.
  eapply H6.
  right.
  unfold inv_ieoff.
  unfold sat;fold sat;trysimplsall;mytac.
  exists empmem x0 x0 empabst x3 x3;mytac.
  simpl;unfold emposabst;auto.
  simpl; split; auto.
  unfolds; auto.
  exists 1%nat.
  exists empmem x0 x0 empabst x3 x3;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  left.
  exists empmem x0 x0 empabst x3 x3;mytac.
  auto.
  unfold INUM; lia.
  simpl;unfold emposabst;auto.
  eapply invlth_isr_emp in H1.
  simpl in H1.
  unfold emposabst in H1.
  simpljoin.
  eapply starinv_isr_add; auto.
  apply H10.
  auto.

  exists (merge x x0) empmem (merge x2 x3) empabst.
  mytac.
  eapply mem_join_join_merge_eq;eauto.
  join auto.
  eapply disjoint_emp_r.
  eapply abst_join_join_merge_eq';eauto.
  eapply OSAbstMod.join_emp.
  auto.
  eapply disjoint_emp_r.
  intro.
  unfold sat;fold sat;trysimplsall;mytac.
  exists x x0 (merge x x0) x2 x3 (merge x2 x3).
  splits; eauto.
  apply join_merge_disj.
  apply mem_join_disjoint_eq_merge in H3.
  destruct H3; auto.
  apply OSAbstMod.join_merge_disj.
  apply OSAbstMod.join_disj_meq in H5.
  destruct H5; auto.
  eapply good_inv_prop;eauto.
  apply invp.
  assert (inv_prop (getinv (I (S INUM)))).
  apply prec.
  unfolds in H11.
  destruct H11.
  unfolds in H12.
  mytac.
  eapply H13 with (i:=1%nat) in H6.
  simpl in H6.
  eapply H6.
  right.
  unfold inv_ieoff.
  unfold sat;fold sat;trysimplsall;mytac.
  exists empmem x0 x0 empabst x3 x3;mytac.
  simpl;unfold emposabst;auto.
  simpl; split; auto.
  unfolds; auto.
  exists 1%nat.
  exists empmem x0 x0 empabst x3 x3;mytac.
  simpl;unfold emposabst;auto.
  simpl; unfold emposabst; auto.
  left.
  exists empmem x0 x0 empabst x3 x3;mytac.
  auto.
  unfold INUM; lia.
  simpl;unfold emposabst;auto.
  unfold empst in H8.
  unfold emptaskst in H8.
  unfold emposabst in H8.
  simpljoin.
  eapply starinv_isr_add; auto.
  apply H10.

  Unshelve.
  all: first [exact nil | exact false | exact i0 | exact e0 |
              exact ab | exact i2 | trivial].
Qed.

Lemma int_mem_trans
: forall sd p C C' o o' Ms Os Ml li,
    GoodI I sd li->
    lintstep p C o C' o' ->
    join Ml Ms (get_mem (get_smem o)) ->
    (forall ab : absop, (substaskst o Ms, Os, ab) |= INV I) ->
    exists Ms' Ml' Os' Ol,
      join Ml' Ms' Ms /\
      join Ol Os' Os /\
      (forall ab : absop, (substaskst o' Ms', Os', ab) |= INV I).
Proof.
  intros.
  assert (disjoint Ml Ms).
  eapply my_join_disj; eauto.
  assert (merge Ml Ms = get_mem (get_smem o)).
  erewrite join_merge; eauto.
  lets Hx: int_mem_trans1 H H0 H3 H4 H2.
  simpljoin.
  do 4 eexists; splits; eauto.
  eapply join_merge_disj; auto.
  apply join_comm.
  apply disjoint_sym in H8.
  eapply join_merge_disj; eauto.
Qed.
Close Scope nat_scope.
