Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import include_frm.
Require Import NPeano.
Require Import os_inv.

Require Import pure_auto.
Require Import math_auto.
Require Import OSTimeTickPure.

Open Scope list_scope.
Open Scope code_scope.

Fixpoint get_tls_blocked_num (tls : TcbMod.rlist) (sid: addrval) :=
match tls with
| nil => 0%nat
| ( (tid,(p,st,m,sus)) :: tls') => 
        match st with
        | wait (os_stat_sem eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_num tls' sid)
                                                                     else (get_tls_blocked_num tls' sid)
        | _ => (get_tls_blocked_num tls' sid)
        end
end.

Fixpoint Int_sub_n (n:nat) (vh: int32) (vsub: int32) :int32 :=
match n with
0%nat => vh
| S n' => Int.sub (Int_sub_n n' vh vsub) vsub
end.

Definition val_eq' (v1 v2:val):bool :=
  match v1, v2 with
    | Vint32 n1, Vint32 n2 => Int.eq n1 n2
    | Vptr (b1, ofs1), Vptr (b2, ofs2) => (peq b1 b2) && (Int.eq ofs1 ofs2)
    | Vnull, Vptr (b,ofs) => false
    | Vptr (b,ofs), Vnull => false
    | Vnull, Vnull => true
    | _, _ => false
  end.

Lemma TcbMod_lb_app:
forall lst1 lst2 a,
TcbMod.lb a lst1 ->
TcbMod.lb a lst2 ->
TcbMod.lb a (lst1 ++ lst2).
Proof.
induction lst1. simpl; auto.
simpl.
intros.
destruct a.
destruct H.
split; auto.
Qed.

Lemma TcbMod_lb_app_imp:
forall lst1 lst2 a,
TcbMod.lb a (lst1 ++ lst2) ->
TcbMod.lb a lst1 /\ TcbMod.lb a lst2 .
Proof.
induction lst1. simpl; auto.
simpl.
intros.
destruct a.
destruct H.
eapply IHlst1 in H0.
destruct H0.
split; auto.
Qed.

Lemma TcbMod_set'_eq:
forall lst a b,
TcbMod.lb a lst ->
TcbMod.set' a b lst = (a,b) :: lst.
Proof.
induction lst; simpl; auto.
intros.
destruct a.
destruct H.
rewrite H.
auto.
Qed.

Lemma TcbMod_set'_eq_imp:
forall lst a b,
TcbMod.is_orderset lst ->
TcbMod.set' a b lst = (a,b) :: lst ->
TcbMod.lb a lst.
Proof.
induction lst. simpl; auto.
intros.
destruct a.
simpl in *.
destruct H.
destruct (tidspec.blt a0 a) eqn: eq1.
split; auto.
eapply TcbMod.lb_trans; eauto.
destruct (tidspec.beq a0 a) eqn: eq2.
inverts H0.
assert (Hf: length (lst) = length ((a0, b0) :: lst)).
rewrite <- H4; auto.
simpl in Hf; false; auto with zarith.
inverts H0.
rewrite tid_beq_true in eq2; tryfalse.
Qed.


Lemma TcbMod_lb_orderset: 
forall lst1 lst2 a a0 b0,
lst1 <> nil ->
TcbMod.lb a (lst1 ++ lst2) ->
TcbMod.is_orderset (lst1 ++ (a0, b0) :: lst2) ->
TcbMod.lb a (lst1 ++ (a0, b0) :: lst2).
Proof.
induction lst1; simpl; intros.
tryfalse.
destruct a.
destruct H0.
destruct H1.
split; auto.
destruct lst1.
subst.
simpl in *.
destruct H1.
split; auto.
eapply tidspec.blt_trans; eauto.
eapply IHlst1; eauto.
Qed.

Lemma TcbMod_set'_app_len:
forall lst a b,
TcbMod.lb a lst ->
length (TcbMod.set' a b lst) = S (length lst).
Proof.
induction lst; simpl; intros.
auto.
destruct a.
destruct H.
rewrite H.
simpl. auto.
Qed.

Lemma TcbMod_set'_app_len_alt:
forall lst a b i,
TcbMod.get (TcbMod.listset_con (lst:=lst) i) a = None ->
length (TcbMod.set' a b lst) = S (length lst).
Proof.
induction lst; simpl; intros.
auto.
destruct a.
destruct i.
destruct (tidspec.blt a0 a) eqn: eq1.
simpl; auto.
destruct (tidspec.beq a0 a) eqn: eq2.
eapply tidspec.beq_true_eq in eq2; subst.
assert (Hsome: TcbMod.get (TcbMod.listset_con (lst:=(a, b0) :: lst) (conj l i)) a = Some b0).
{ eapply TcbMod.join_get_l.
   eapply joinsig_listset_con; eauto.
   rewrite TcbMod.map_get_sig; auto.
}
rewrite Hsome in H.
tryfalse.
simpl.
rewrite Nat.succ_inj_wd.
eapply IHlst.
instantiate (1:= i).
destruct (TcbMod.get (TcbMod.listset_con (lst:=lst) i) a0 ) eqn: eq3.
eapply TcbMod.join_get_r in eq3.
2: {  lets Hjo: joinsig_listset_con lst a b0 i l.
              unfold TcbMod.joinsig in Hjo.
              apply Hjo. }
rewrite H in eq3. tryfalse.
auto.
Qed.

Lemma TcbMod_get'_app_none:
forall lst1 lst2 a,
TcbMod.get' lst1 a = None ->
TcbMod.get' lst2 a = None ->
TcbMod.get' (TcbMod.app' lst1 lst2) a = None.
Proof.
induction lst1; induction lst2; simpl; intros; auto.
destruct a.
destruct (tidspec.beq a0 a) eqn: eq1; tryfalse.
eapply tidspec.beq_false_neq in eq1.
rewrite TcbMod.get'_set'_neq; eauto.
destruct a.
destruct a0.
destruct (tidspec.beq a1 a) eqn: eq1; tryfalse.
destruct (tidspec.beq a1 a0) eqn: eq2; tryfalse.
eapply tidspec.beq_false_neq in eq1.
rewrite TcbMod.get'_set'_neq; eauto.
eapply IHlst1; eauto.
simpl.
rewrite eq2. auto.
Qed.


Lemma TcbMod_app_join:
forall lst1 l1 a b l,
TcbMod.get (TcbMod.listset_con (lst:=lst1) l1) a = None ->
TcbMod.join (TcbMod.listset_con (lst:=lst1) l1)  (TcbMod.sig a b)
(TcbMod.listset_con (lst:=TcbMod.app' lst1 (TcbMod.sig' a b)) l).
Proof.
induction lst1. simpl; intros.
unfold TcbMod.sig'.
apply join_fst. simpl; auto.
destruct a.
destruct l1.
intros.
rename H into Hnone.
lets Hnone1: TcbMod.lb_notin l.
simpl in *.
assert (Hnone': TcbMod.get (TcbMod.listset_con (lst:=lst1) i) a0 = None).
{ destruct (TcbMod.get (TcbMod.listset_con (lst:=lst1) i) a0) eqn: eq1; auto.
  eapply TcbMod.join_get_l in eq1.
  rewrite Hnone in eq1. tryfalse.
  apply join_fst. simpl; auto.
}
assert (Hor: TcbMod.is_orderset (TcbMod.app' lst1 (TcbMod.sig' a0 b0))).
{ eapply TcbMod.is_set_app'; eauto.
   unfold TcbMod.sig'. simpl; auto.
}
assert (Htj: TcbMod.join (TcbMod.listset_con (lst:=lst1) i) 
           (TcbMod.sig a0 b0)
           (TcbMod.listset_con (lst:=TcbMod.app' lst1 (TcbMod.sig' a0 b0)) Hor)).
{ eapply IHlst1; eauto. }
lets Hnone2: TcbMod.map_join_get_none Htj Hnone1.
assert (Hnone_sig: TcbMod.get (TcbMod.sig a b) a0 = None).
{ lets Hneq: TcbMod.map_join_get_none join_fst Hnone'.
eauto.
rewrite Hnone in Hneq.
rewrite <- Hneq; auto.
}
rewrite TcbMod.sig_sem in Hnone_sig.
destruct (tidspec.beq a a0) eqn: Hneq; tryfalse.
(* eapply TasksMod.beq_sym in Hneq. *)
eapply TcbMod.join_comm in Htj.
eapply TcbMod.join_comm.
eapply TcbMod.join_assoc; eauto.
2: { apply join_fst. simpl; auto. }
unfold TcbMod.join.
intros.
unfold TcbMod.get in *.
simpl in *.
destruct (TcbMod.get' (TcbMod.app' lst1 (TcbMod.sig' a0 b0)) a1) eqn: eq1;
destruct ( tidspec.beq a1 a) eqn: eq2;
try (eapply tidspec.beq_true_eq in eq2; subst);
try (eapply tidspec.beq_false_neq in eq2;
rewrite TcbMod.get'_set'_neq; eauto).
rewrite Hnone2 in eq1.
rewrite Hneq in eq1. tryfalse.
rewrite eq1. auto.
rewrite TcbMod.get'_set'; auto.
rewrite eq1. auto.
Qed.

Lemma TcbMod_lst_merge_sig_len:
forall tls1 a b,
   TcbMod.get tls1 a = None ->
   length (TcbMod.lst (TcbMod.merge tls1 (TcbMod.sig a b) )) = S(length (TcbMod.lst tls1)).
Proof.
  induction tls1.
  simpl.
  induction lst.
  simpl. auto.
  intros.
  destruct a.
  simpl in *.
  unfold TcbMod.sig' in *.
  destruct i.
  assert(Heq: length(TcbMod.app' lst ((a0, b) :: nil)) = S (length lst)%nat ).
  { eapply IHlst.
     instantiate (1:= i).
     destruct (TcbMod.get (TcbMod.listset_con (lst:=lst) i) a0 ) eqn: eq1.
     eapply TcbMod.join_get_r in eq1.
     2: {  lets Hjo: joinsig_listset_con lst a b0 i l.
              unfold TcbMod.joinsig in Hjo.
              apply Hjo. }
       rewrite H in eq1. tryfalse.
       auto.
  }
  rewrite <- Heq.
  eapply TcbMod_set'_app_len_alt; eauto.
  unfold TcbMod.get in *.
  simpl in *.
  destruct (tidspec.beq a0 a) eqn: eq1; tryfalse.
  eapply TcbMod_get'_app_none; eauto.
  eapply TcbMod.lb_notin; eauto.
  simpl. eapply TasksMod.beq_sym in eq1.
  rewrite eq1. auto.
  Unshelve.
  eapply TcbMod.is_set_app'; eauto.
  simpl; auto.
Qed.

Lemma get_tls_blocked_succ_sem:
forall lst a sid p wt msg sus,
get_tls_blocked_num ((a,(p, wait (os_stat_sem sid) wt, msg, sus)) :: lst) sid = 
(1 + get_tls_blocked_num lst sid)%nat.
Proof.
intros.
unfold get_tls_blocked_num.
fold get_tls_blocked_num.
rewrite tid_beq_true.
auto.
Qed.

Lemma get_tls_blocked_succ_nosem:
forall lst a b sid,
~(exists p wt msg sus, b = (p, wait (os_stat_sem sid) wt, msg, sus)) ->
get_tls_blocked_num ((a,b) :: lst) sid = 
get_tls_blocked_num lst sid.
Proof.
intros.
destruct b. destruct p. destruct p.
unfold get_tls_blocked_num.
fold get_tls_blocked_num.
destruct t; auto.
destruct t; auto.
destruct (tidspec.beq e sid) eqn: eq1.
eapply tidspec.beq_true_eq in eq1; subst.
false.
eapply H; eauto.
auto.
Qed.


Lemma get_tls_blocked_sym:
forall lst a b a' b' sid ,
get_tls_blocked_num ((a,b) :: (a',b') :: lst) sid = 
get_tls_blocked_num ((a',b'):: (a,b) :: lst) sid.
Proof.
intros.
destruct b.  destruct p. destruct p.
destruct b'. destruct p0. destruct p0.
unfold get_tls_blocked_num.
fold get_tls_blocked_num.
destruct t0; destruct t; auto with zarith.
destruct t; auto with zarith.
destruct t0; auto with zarith.
destruct (tidspec.beq e sid) eqn: eq1;
destruct (tidspec.beq e0 sid) eqn: eq2; auto.
Qed.

Lemma get_tls_blocked_succ:
forall lst a b sid ,
get_tls_blocked_num ((a,b) :: lst) sid = 
(get_tls_blocked_num ((a,b)::nil) sid + get_tls_blocked_num lst sid)%nat.
Proof.
induction lst; intros; try destruct a;
try (destruct b; destruct p; destruct p).
simpl in *.
destruct t; auto.
destruct t; auto.
auto with zarith.
rewrite IHlst.
destruct b0.
destruct p0.
destruct p0.
simpl.
destruct t0; destruct t; auto with zarith;
try destruct t0; try destruct t; auto with zarith;
try destruct (tidspec.beq e sid) eqn: eq1; 
try destruct (tidspec.beq e0 sid) eqn: eq2;
auto with zarith.
Qed.

Lemma get_tls_blocked_set:
forall lst a b sid,
TcbMod.get' lst a = None ->
get_tls_blocked_num (TcbMod.set' a b lst) sid = 
(get_tls_blocked_num ((a,b)::nil) sid + get_tls_blocked_num lst sid)%nat.
Proof.
induction lst; intros;
try destruct a;
try (destruct b; destruct p; destruct p).
simpl.
destruct t; auto.
(* destruct t; auto. *)
auto with zarith.
destruct b0.
destruct p0.
simpl TcbMod.set'.
destruct (tidspec.blt a0 a) eqn: eq1.
rewrite <- get_tls_blocked_succ.
rewrite get_tls_blocked_sym. auto.
simpl in H.
destruct (tidspec.beq a0 a ) eqn: eq2; tryfalse.
rewrite get_tls_blocked_succ.
rewrite IHlst; eauto.
rewrite <- get_tls_blocked_succ.
rewrite <- get_tls_blocked_succ.
rewrite <- get_tls_blocked_succ.
rewrite get_tls_blocked_sym. auto.
Qed.


Lemma get_tls_blocked_app:
forall lst1 sid a b,
TcbMod.get' lst1 a = None ->
get_tls_blocked_num (TcbMod.app' (TcbMod.sig' a b) lst1) sid = 
(get_tls_blocked_num lst1 sid + get_tls_blocked_num (TcbMod.sig' a b) sid)%nat.
Proof.
unfold TcbMod.sig'.
induction lst1; intros.
simpl; auto.
destruct a.
simpl TcbMod.app'.
simpl in H.
destruct (tidspec.beq a0 a) eqn: eq1; tryfalse.
destruct (tidspec.blt a0 a) eqn: eq2.
rewrite get_tls_blocked_succ.
auto with zarith.
rewrite get_tls_blocked_succ.
eapply IHlst1 in H; eauto.
simpl TcbMod.app' in H.
rewrite H.
rewrite get_tls_blocked_succ with (lst:= lst1).
auto with zarith.
Qed.


Lemma get_tls_blocked_succ_eq_sem: 
forall tls1 a b sid p wt msg sus,
TcbMod.get tls1 a = None ->
b = (p, wait (os_stat_sem sid) wt, msg, sus) ->
get_tls_blocked_num (TcbMod.lst (TcbMod.merge (TcbMod.sig a b) tls1)) sid 
   = (1 + (get_tls_blocked_num (TcbMod.lst tls1) sid))%nat.
Proof.
intros.
subst.
simpl.
rewrite get_tls_blocked_set; eauto.
rewrite get_tls_blocked_succ_sem.
auto.
Qed.

Lemma get_tls_blocked_succ_eq: 
forall tls1 a b sid,
TcbMod.get tls1 a = None ->
get_tls_blocked_num (TcbMod.lst (TcbMod.merge (TcbMod.sig a b) tls1)) sid 
   = (get_tls_blocked_num ((a,b)::nil) sid + (get_tls_blocked_num (TcbMod.lst tls1) sid))%nat.
Proof.
intros.
simpl.
rewrite get_tls_blocked_set; eauto.
Qed.

Lemma get_tls_blocked_pos:
forall lst sid, (0 <= get_tls_blocked_num lst sid)%nat.
Proof.
auto with zarith.
(* induction lst.
simpl; auto with zarith.
intros.
destruct a.
rewrite get_tls_blocked_succ.
eapply Ztac.add_le; eauto.
destruct b. destruct p.
simpl.
destruct t; auto with zarith.
destruct t; auto with zarith.
destruct (tidspec.beq e sid); auto with zarith. *)
Qed.

Lemma Int_sub_zero_eq:
Int.sub Int.zero Int.one = (Int.repr Int.max_unsigned).
Proof.
rewrite Int.sub_add_not.
int auto.
simpl.
int auto.
Qed.


Lemma Int_sub_succ_eq:
forall n vh vsub,
Int_sub_n (S n) vh vsub = Int.sub (Int_sub_n n vh vsub) vsub.
Proof.
simpl; auto.
Qed.




