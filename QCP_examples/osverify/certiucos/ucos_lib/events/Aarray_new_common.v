Require Import List.
Require Export include_frm.
Require Import int_auto.
Require Export sep_auto.
Require Import pure_lib.
Require Import math_auto.

Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
Require Import os_inv.
Require Import step_prop.
Require Import seplog_trm_tacs.

Local Open Scope list_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma Aarray_new'_succ :
  forall s a vll n t b i, 
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll -> 
    s |= Aarray_new' (b,i) (S n) t (a :: vll).
Proof.
intros.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_elim in H; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_elim in H);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll ** P -> 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ** P.
Proof.
intros.
sep pauto.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_elim in H; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_elim in H);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_imp :
  forall s a vll n t b i, 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ->
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll.
Proof.
intros.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_intro; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_intro);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_imp_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ** P ->
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll ** P.
Proof.
intros.
sep pauto.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_intro; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_intro);
try(sep pauto).
Qed.

Lemma Aarray_new'_compose :
  forall vll1 n vll2 m t b i s, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2).
Proof.
induction vll1; induction n; intros.
clear H.
simpl Aarray_new' in H0.
assert (i +ᵢ  $ 0 = i) by int auto.
rewrite H in H0.
sep pauto.
eapply astar_l_afalse_elim in H0.
tryfalse.
eapply astar_l_afalse_elim in H0.
tryfalse.
eapply Aarray_new'_succ_imp_alt in H0.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
rewrite Nat.add_succ_l.
eapply Aarray_new'_succ.
sep pauto.
assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
assert (Ht: 0 <= Z.of_nat (typelen t) <= Int.max_unsigned /\ 0 <= Z.of_nat (n * typelen t) <= Int.max_unsigned).
{ clear -H H1 Htrans. split; eapply Htrans; int auto. }
assert ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
{ simpl.
rewrite Nat2Z.inj_add.
clear -H H1 Ht.
simpl in H.
int auto. }
rewrite H2 in H0.
eapply IHvll1.
clear -H H1 Ht H2 Htrans.
int auto.
int auto.
rewrite Int.add_assoc.
sep pauto.
Qed.

Lemma Aarray_new'_compose_alt :
  forall vll1 n vll2 m t b i s P, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 ** P -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ** P.
Proof.
intros.
sep pauto.
eapply Aarray_new'_compose.
eauto.
sep pauto.
Qed.

Lemma Aarray_new'_split :
  forall vll1 n vll2 m t b i s, 
     s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2.
Proof.
induction vll1; induction n; intros.
simpl Aarray_new' in *.
assert (i +ᵢ  $ 0 = i) by int auto.
rewrite H2.
sep pauto.
inverts H1.
inverts H2.
inverts H1.
inverts H2.
(* simpl Aarray_new' in *. *)
(* eapply astar_l_afalse_intro. *)
(* simpl in H1. *)
eapply Aarray_new'_succ_alt.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in H.
rewrite Nat.add_succ_l in H.
eapply Aarray_new'_succ_imp in H.
sep pauto.
assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
assert (Ht: 0 <= Z.of_nat (typelen t) <= Int.max_unsigned /\ 0 <= Z.of_nat (n * typelen t) <= Int.max_unsigned).
{ clear -H0 H3 Htrans. split; eapply Htrans; int auto. }
assert ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
{ simpl.
rewrite Nat2Z.inj_add.
clear -H0 H3 Ht.
simpl in H0.
int auto. }
rewrite H4.
rewrite <- Int.add_assoc.
eapply IHvll1.
sep pauto.
clear -H0 H3 Ht H4 Htrans.
int auto.
int auto.
eauto.
Qed.

Lemma Aarray_new'_split_alt :
  forall vll1 n vll2 m t b i s P, 
     s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ** P ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 ** P.
Proof.
intros.
sep pauto.
eapply Aarray_new'_split;
eauto.
Qed.

Lemma Aarray_new_succ :
  forall s a vll n t b i, 
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll -> 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll).
Proof.
unfold Aarray_new.
apply Aarray_new'_succ.
Qed.

Lemma Aarray_new_succ_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll ** P -> 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_alt.
Qed.

Lemma Aarray_new_succ_imp :
  forall s a vll n t b i, 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ->
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_imp.
Qed.

Lemma Aarray_new_succ_imp_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ** P ->
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_imp_alt.
Qed.

Lemma Aarray_new_compose :
  forall vll1 n vll2 m t b i s, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2).
Proof.
unfold Aarray_new.
apply Aarray_new'_compose.
Qed.

Lemma Aarray_new_compose_alt :
  forall vll1 n vll2 m t b i s P, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 ** P -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_compose_alt.
Qed.

Lemma Aarray_new_split :
  forall vll1 n vll2 m t b i s, 
     s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2.
Proof.
unfold Aarray_new.
apply Aarray_new'_split.
Qed.

Lemma Aarray_new_split_alt :
  forall vll1 n vll2 m t b i s P, 
     s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ** P ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_split_alt.
Qed.

Lemma Aarray_new'_split_strong :
  forall vll1 n vll2 m t b i s, 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ->
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
    length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b, i) n t vll1 ** Aarray_new' (b, i +ᵢ $ Z.of_nat (n * (typelen t))) m t vll2.
Proof.
  induction vll1; induction n; intros.
  simpl Aarray_new' in *.
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H2.
  sep pauto.
  inverts H1.
  inverts H2.
  inverts H1.
  inverts H2.
  eapply Aarray_new'_succ_alt.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in H.
  rewrite Nat.add_succ_l in H.
  eapply Aarray_new'_succ_imp in H.
  sep pauto.
  cut ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
  {
    intro.
    rewrite H3.
    rewrite <- Int.add_assoc.
    eapply IHvll1.
    sep pauto.
    auto with zarith.
    inverts H1. auto.
  }
  int auto.
Qed.

Lemma Aarray_new_split_strong :
  forall vll1 n vll2 m t b i s, 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ->
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
    length vll1 = n /\ length vll2 = m ->
    s |=
      Aarray_new (b, i) (Tarray t n) vll1 **
      Aarray_new (b, i +ᵢ $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2.
Proof.
  unfold Aarray_new.
  apply Aarray_new'_split_strong.
Qed.

Lemma Aarray_new_split_strong_frm :
  forall vll1 n vll2 m t b i s P, 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ** P ->
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
    length vll1 = n /\ length vll2 = m ->
    s |=
      Aarray_new (b, i) (Tarray t n) vll1 **
      Aarray_new (b, i +ᵢ $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 ** P.
Proof.
  intros.
  sep pauto.
  eapply Aarray_new_split_strong; eauto.
Qed.

Lemma Aarray_new'_compose_strong :
  forall vll1 n vll2 m t b i s, 
    Z.of_nat (S n * typelen t) <= Int.max_unsigned ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2).
Proof.
  induction vll1; induction n; intros.
  simpl Aarray_new' in H0.
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H1 in H0.
  sep pauto.
  eapply astar_l_afalse_elim in H0.
  tryfalse.
  eapply astar_l_afalse_elim in H0.
  tryfalse.
  eapply Aarray_new'_succ_imp_alt in H0.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  rewrite Nat.add_succ_l.
  eapply Aarray_new'_succ.
  sep pauto.
  eapply IHvll1 with (i:=i +ᵢ  $ Z.of_nat (typelen t)); eauto.
  auto with zarith.
  rewrite Int.add_assoc.
  assert (Heq:
           $ Z.of_nat (S n * typelen t) = ($ Z.of_nat (typelen t) +ᵢ  $ Z.of_nat (n * typelen t))).
  { int auto. }
  rewrite <- Heq.
  auto.
Qed.

Lemma Aarray_new_compose_strong:
  forall vll1 n vll2 m t b i s, 
    Z.of_nat (S n * typelen t) <= Int.max_unsigned ->     
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2).
Proof.
  unfold Aarray_new.
  apply Aarray_new'_compose_strong.
Qed.

(* Require Import os_inv. *)
(* Require Import step_prop. *)

Local Open Scope code_scope.
(* Local Open Scope int_scope. *)
(* Local Open Scope Z_scope. *)

(* new add in 5-14 *)

Lemma usr_max_evts_rgn:
1 <= OS_USER_MAX_EVENTS / 3 <= 79.
Proof.
lets Hrgn: OS_MAX_EVENTS_range.
unfold OS_USER_MAX_EVENTS.
unfold CORENUM in *.
destruct Hrgn as (Hrgn1 & Hrgn2).
rewrite Z.sub_le_mono_r with (p:= 8 * 2) in Hrgn1, Hrgn2.
rewrite Z.add_simpl_l in Hrgn1.
eapply Z.div_le_mono with (c:= 3) in Hrgn2; auto with zarith.
eapply Z.div_le_mono with (c:= 3) in Hrgn1; auto with zarith.
Qed.

Lemma usr_max_evts_rgn':
3 <= OS_USER_MAX_EVENTS <= 239.
Proof.
lets Hrgn: OS_MAX_EVENTS_range.
unfold OS_USER_MAX_EVENTS.
unfold CORENUM in *.
destruct Hrgn as (Hrgn1 & Hrgn2).
rewrite Z.sub_le_mono_r with (p:= 8 * 2) in Hrgn1, Hrgn2.
rewrite Z.add_simpl_l in Hrgn1.
split; auto with zarith.
Qed.

Lemma usr_max_evts_succ:
∘(OS_USER_MAX_EVENTS / 3) = S (∘ (OS_USER_MAX_EVENTS / 3 - 1)).
Proof.
lets Hrgn: usr_max_evts_rgn.
destruct Hrgn as (Hrgn1 & Hrgn2).
unfold nat_of_Z.
auto with zarith.
Qed.

Ltac conv_max_unsigned:= 
         try change Int.max_unsigned with 4294967295%Z in *;
         try change Int.max_signed with 2147483647%Z in *.


(* Ltac solve_usr_max_evts_rgn :=
let Hrgn:= fresh in
let Hrgn1:= fresh in
let Hrgn2:= fresh in
try solve
       [lets Hrgn: usr_max_evts_rgn;
        destruct Hrgn as (Hrgn1 & Hrgn2);
        try unfold nat_of_Z;
        try conv_max_unsigned;
        auto with zarith];
try (rewrite usr_max_evts_succ in *; auto with zarith). *)

Ltac solve_usr_max_evts_rgn :=
let Hrgn:= fresh in
let Hrgn1:= fresh in
let Hrgn2:= fresh in
let Hrgn1':= fresh in
let Hrgn2':= fresh in
try solve
       [lets Hrgn: usr_max_evts_rgn;
        destruct Hrgn as (Hrgn1 & Hrgn2);
        lets Hrgn: usr_max_evts_rgn';
        destruct Hrgn as (Hrgn1' & Hrgn2');
        try unfold nat_of_Z;
        try conv_max_unsigned;
        auto with zarith];
try (rewrite usr_max_evts_succ in *; auto with zarith).

(* end of new add in 5-14 *)

Lemma ASeminfo_succ:
  forall s P b i vl vll,
    s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
            Astruct (b,i) sem_info_t vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat (typelen sem_info_t))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - 1))) vll ** P ->
     new_array_type_vallist_match sem_info_t (vl::vll) ->
     length (vl::vll) = ∘ (OS_USER_MAX_EVENTS / 3) ->
     s |= ASeminfo (b, i) (vl::vll) ** P .
Proof.
  intros.
  unfold ASeminfo.
  solve_usr_max_evts_rgn.
  sep pauto.
Qed.

Lemma ASeminfo_succ_imp:
  forall s P vl b i vll,
    s |= ASeminfo (b,i) (vl::vll) ** P ->
    s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
            Astruct (b,i) sem_info_t vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat (typelen sem_info_t))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - 1))) vll **
            [| struct_type_vallist_match sem_info_t vl /\ 
                new_array_type_vallist_match sem_info_t vll /\
                length (vl::vll) = ∘ (OS_USER_MAX_EVENTS / 3)|] ** P.
Proof.
  unfold ASeminfo.
  unfold Aarray_new.
  (* change (∘  (OS_USER_MAX_EVENTS / 3)) with 6%nat.
  change (∘ (OS_USER_MAX_EVENTS / 3 - 1)) with 5%nat. *)
  solve_usr_max_evts_rgn.
  intros.
  sep cancel 4%nat 5%nat.
  unfold new_array_type_vallist_match in H.
  unfold sem_info_t in H.
  fold sem_info_t in H.
  fold new_array_type_vallist_match in H.
  sep pauto.
Qed.

Lemma ASeminfo_select_sn :
  forall vll1 n vll2 b i s vl P, 
      Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 ->
     0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned ->
     s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
              Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
              Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t)))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 ** P ->
     new_array_type_vallist_match sem_info_t (vll1 ++ (vl::vll2)) ->
     length (vll1 ++ (vl::vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    s |= ASeminfo (b,i) (vll1 ++ (vl::vll2)) ** P.
Proof.
intros.
unfold ASeminfo.
sep pauto.
assert (Heq: ∘ (OS_USER_MAX_EVENTS / 3) 
                =  Nat.add n (S (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n))) )).
unfold nat_of_Z.
(* assert (Heq1: Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (OS_USER_MAX_EVENTS / 3))  (Z.to_nat (Z.of_nat (S n))) ).
apply Z2Nat.inj_sub.
eauto with zarith.
rewrite Heq1.
eauto with zarith. *)
solve_usr_max_evts_rgn.
rewrite Heq.
eapply Aarray_new_compose.
rewrite <- Heq.
(* eauto. *)
solve_usr_max_evts_rgn.
sep pauto.
eapply Aarray_new_succ.
rewrite Int.add_assoc.
assert ($ Z.of_nat (n * typelen sem_info_t) +ᵢ  $ Z.of_nat (typelen sem_info_t) 
              = $ Z.of_nat (S n * typelen sem_info_t)).
{
rewrite Nat.mul_succ_l.
rewrite Nat2Z.inj_add.
clear -H H0 H4.
assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
rewrite <- Nat.add_1_r in H.
simpl in *.
int auto.
eapply Htrans.
instantiate (1:=OS_USER_MAX_EVENTS / 3 * 60).
(* split.
simpl. int auto.
split.
int auto.
eauto with zarith. *)
split; solve_usr_max_evts_rgn.
}
rewrite H5.
sep pauto.
unfold sem_info_t.
unfold Aarray_new.
unfold Aarray_new'.
fold sem_info_t.
sep pauto.
Qed.

(* new add in 5-14 *)

Lemma ASeminfo_select_sn_ex :
  forall s P b i semvl,
     s |= EX vll1 n vll2 vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t)))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] **
             [| 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned |] **
              P ->
    s |= ASeminfo (b, i) semvl ** P.
Proof.
intros.
do 4 destruct H.
sep split in H.
subst.
eapply ASeminfo_select_sn.
eauto.
eauto.
sep pauto.
eauto.
eauto.
Qed.

(* end of new add in 5-14 *)

Lemma ASeminfo_unfold_sn:
  forall s semvl b i,
     s |= ASeminfo (b,i) semvl ->
     s |= EX vll1 n vll2 vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t)))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |].
Proof.
intros.
unfold ASeminfo in H.
sep split in H.
destruct H0.
solve_usr_max_evts_rgn.
destruct semvl.
inverts H1.
do 4 eexists.
instantiate (1 := 0%nat).
instantiate (1 := semvl).
instantiate (1 := nil).
instantiate (1 := v).
sep pauto.
unfold Aarray_new in *.
simpl Aarray_new' at 1.
change ($ Z.of_nat (0 * typelen sem_info_t)) with ($ 0).
change ($ Z.of_nat (1 * typelen sem_info_t)) with ($ Z.of_nat ( typelen sem_info_t)).
assert (i +ᵢ  $ 0 = i) by int auto.
rewrite H2.
sep pauto.
(* change (OS_USER_MAX_EVENTS / 3) with 6.
eauto with zarith. *)
solve_usr_max_evts_rgn.
Qed.

(* new add in 5-14 *)

Lemma ASeminfo_unfold_sn_alt:
  forall s semvl P b i,
      s |= ASeminfo (b, i) semvl ** P ->
     s |= EX vll1 n vll2 vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t)))) (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] ** P.
Proof.
intros.
unfold ASeminfo in H.
(* eapply astar_l_aexists_elim in H.
destruct H.
destruct x. *)
sep split in H.
destruct H0.
solve_usr_max_evts_rgn.
destruct semvl.
inverts H1.
do 4 eexists.
instantiate (1 := 0%nat).
instantiate (1 := semvl).
instantiate (1 := nil).
instantiate (1 := v).
sep pauto.
unfold Aarray_new in *.
simpl Aarray_new' at 1.
change ($ Z.of_nat (0 * typelen sem_info_t)) with ($ 0).
change ($ Z.of_nat (1 * typelen sem_info_t)) with ($ Z.of_nat ( typelen sem_info_t)).
assert (i +ᵢ  $ 0 = i) by int auto.
rewrite H2.
sep pauto.
(* change (OS_USER_MAX_EVENTS / 3) with 6.
eauto with zarith. *)
solve_usr_max_evts_rgn.
Qed.

(* end of new add in 5-14 *)

Ltac unfold_usr_max_evts := 
  unfold OS_USER_MAX_EVENTS; unfold OS_MAX_EVENTS; unfold CORENUM.

Ltac unfold_usr_max_evts_in h :=
  unfold OS_USER_MAX_EVENTS in h; unfold OS_MAX_EVENTS in h; unfold CORENUM in h.

Lemma mul_typelen_transform: 
  forall i, 
    Int.ltu i ($ 0) = false -> 
    Z.of_nat (S (Z.to_nat (Int.unsigned i))) <= OS_USER_MAX_EVENTS / 3 ->
    Int.mul ($ Z.of_nat (typelen sem_info_t)) i =
      $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen sem_info_t).
Proof.
  introv Hrgn1 Hrgn2.
  (* unfold_usr_max_evts_in Hrgn2.
  simpl in Hrgn2. 
  simpl.  
  assert (Hle: 0 <= Int.unsigned i) by int auto.
  destruct (Int.unsigned i) eqn: E.
  mauto.
  2: {
    lets H0: Pos2Z.neg_is_nonpos p.
    assert (Z.neg p = 0) by auto with zarith.
    rewrite H. mauto.
  }
  rewrite <- E. 
  unfold Int.mul. 
  rewrite Nat2Z.inj_mul.
  rewrite Z.mul_comm.
  asserts_rewrite (Int.unsigned ($ 60) = Z.of_nat 60). { mauto. }
  rewrite Z2Nat.id; auto. 
  mauto. *)
  simpl in *.
  int auto.
Qed.
  
Ltac mytac :=
  heat; jeauto2.

Lemma new_array_type_vallist_match_split2: 
  forall semvl vll1 vll2 t, 
    new_array_type_vallist_match t semvl ->
    semvl = vll1 ++ vll2 ->
    new_array_type_vallist_match t vll1 /\
      new_array_type_vallist_match t vll2.
Proof.
  inductions semvl.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0. 
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    simpl in Hmt1.
    destruct t;
      (destruct Hmt1 as (Hmta & Hmtb);
       specialize (IHsemvl vll1 vll2 _ Hmtb (eq_refl _));
       split; [simpl; mytac | mytac]).
Qed.

Lemma new_array_type_vallist_match_split: 
  forall semvl vll1 vll2 vl, 
    new_array_type_vallist_match sem_info_t semvl ->
    semvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match sem_info_t vll1 /\
      new_array_type_vallist_match sem_info_t vll2 /\ 
      struct_type_vallist_match sem_info_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.

(* Lemma Aarray_new_emp:
  forall e e0 i ier l a b i0, 
    (e, e0, empenv, i, ier, l, empenv, a) |= Aarray_new (b, i0) (Tarray sem_info_t 0) nil. 
Proof.
  intros.
  unfold Aarray_new.
  unfold Aarray_new'.
  simpl; split; auto. 
  unfold emposabst.
  auto.
Qed. *)

(* Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H. *)

(* Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem. *)

Lemma aseminfo_len: 
  forall s l vl, s |= ASeminfo l vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed. 


Lemma pos_to_nat_6: Pos.to_nat 6 = 6%nat. 
auto with arith. Qed. 

Lemma mul_arith:
  forall idx, (idx < 6)%nat -> Z.of_nat (idx * 32) < 192.
intros. auto with zarith. Qed.

Lemma sub_Z_nat:
  forall (a:nat) b, (a <= ∘ b)%nat -> (∘ (b - Z.of_nat a) = (∘ b) - a)%nat. 
  unfold nat_of_Z in *. intros. auto with zarith. Qed.

Lemma sub_eq_succ:
  forall m n l,  (S m <= l -> S n = l - m -> n = l - (S m))%nat. 
intros. auto with zarith. Qed.

(* (* add ier *)
Ltac change_smo hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i, ?i0, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i, i0, l, o, a) m' o') with (e, e0, m', i, i0, l, o', a) in hyp
      end). *)

(* (* add ier *)
Ltac change_smo_hyps :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i, ?i0, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i, i0, l, o, a) m' o') with (e, e0, m', i, i0, l, o', a) in H
      end). *)

Require Import Lia.

Lemma length_exists: 
	forall {A:Type} (l: list A), (length l > 0)%nat -> exists h t, l = h :: t.
Proof.
  intros.
  destruct l.
  simpl in H; lia.
  eauto.
Qed.

Lemma ASeminfo_unfold_any_idx: 
  forall s b i semvl idx,
    s |= ASeminfo (b, i) semvl ->
    (idx < length semvl)%nat ->
    s |= EX vll1 vll2 vl ,
        GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
          (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t semvl |] **
          [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| semvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length semvl * typelen sem_info_t) <= Int.max_unsigned). 
  { erewrite aseminfo_len; eauto.  simpl. (* mauto. *) solve_usr_max_evts_rgn. }
  introv Hlenle. 
  unfold ASeminfo in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length semvl = idx + (length semvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx semvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length semvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen sem_info_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length semvl * typelen sem_info_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx semvl) = idx /\ length (skipn idx semvl) = (length semvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[[]]]]]]].
(*   destruct s as [[[[[[]]]]]]. *)
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length semvl - idx = S (length semvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx semvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length semvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen sem_info_t) +ᵢ  $ Z.of_nat (typelen sem_info_t) =
                   $ Z.of_nat (S idx * typelen sem_info_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen sem_info_t)%nat with (typelen sem_info_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 60) = Int.unsigned ($ (Z.of_nat (idx * 60)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. 
     (* unfold_usr_max_evts_in H11.
      simpl in H11.
      rewrite pos_to_nat_6 in H11. 
      rewrite H11 in Hlengt.
      apply lt_imply_le.
      apply Z.lt_le_trans with (m:=360). auto. 
      mauto. mauto. *)
      simpl typelen in *.
      clear -Harith.
      eapply Z.le_trans; eauto.
      auto with zarith.
    }
    assert (Hb: 60 = Int.unsigned ($60)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) = length semvl - S idx)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17. unfold sem_info_t in H17. fold sem_info_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idx semvl). exists vlt.
  exists vh. exists x. exists x0. exists m. exists x2. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx7emp & Hx10emp).
  subst x6. unfold emposabst in Hx10emp. subst x9. 
  assert (x5 = x0). { apply map_join_emp' in H5. auto. }
  subst x5.
  simpl in H7. simpl in H2.
  assert (x8 = x3). { apply map_join_emp' in H7. auto. }
  subst x8.
  simpl in H6. 
  simpl in H1.

  exists x1. do 5 eexists. splits; eauto.
  eexists x7. do 2 eexists. exists x14. do 2 eexists. 
  splits; eauto.

  unfold Aarray_new.
  exists x12. do 2 eexists. exists x15. do 2 eexists.
  splits; eauto.
  instantiate (1:=empenv). join auto.
  instantiate (1:=emp). join auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto. 
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. eauto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. 
  rewrite <- Hsplit at 1. rewrite Hlst. auto.
  simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. split; auto.
  rewrite Hlst in H15. simpl in H15. 
  eapply sub_eq_succ; eauto.
  simpl. split; auto. unfolds. auto.
  rewrite H11 in HSidx.
  apply inj_le in HSidx.
  (* simpl in HSidx.
  unfold_usr_max_evts. simpl. 
  asserts_rewrite (20/3 = 6). { auto. }
  auto. *)
  rewrite nat_of_Z_eq in HSidx; auto.
  solve_usr_max_evts_rgn.
  simpl. split; auto. unfolds. auto.

Qed. 

Lemma ASeminfo_unfold_any_idx_frm: 
  forall s semvl idx b i P,
    s |= ASeminfo (b,i) semvl ** P ->
    (idx < length semvl)%nat ->
    s |= (EX vll1 vll2 vl ,
        GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray sem_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen sem_info_t))) sem_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen sem_info_t))))
            (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match sem_info_t semvl |] **
          [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| semvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply ASeminfo_unfold_any_idx; eauto.
Qed. 



Lemma ASeminfo_select_sn_strong :
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 ->
    (* 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned -> *)
    s |= GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
      Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t))))
        (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match sem_info_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    s |= ASeminfo (b,i) (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen sem_info_t) <= Int.max_unsigned).
  {
    remember (typelen sem_info_t) as X. 
    unfold sem_info_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    (* unfold_usr_max_evts_in H.
    simpl in H.
    asserts_rewrite (20 / 3 = 6)  in H. { auto with zarith. } 
    int auto. *)
    solve_usr_max_evts_rgn.
  }
  unfold ASeminfo.
  sep pauto.
  assert (Heq: ∘ (OS_USER_MAX_EVENTS / 3) 
               =  Nat.add n (S (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  (* assert (Heq1: Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (OS_USER_MAX_EVENTS / 3))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith. *)
  solve_usr_max_evts_rgn.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.

  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen sem_info_t) +ᵢ  $ Z.of_nat (typelen sem_info_t) 
                   = $ Z.of_nat (S n * typelen sem_info_t)).
  { int auto. }
  sep pauto.
  unfold sem_info_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold sem_info_t.
  sep pauto.
Qed.

Lemma ASeminfo_select_sn_ex_strong:
  forall s P b i semvl,
     s |= EX vll1 n vll2 vl ,
             GV Sem_info @ sem_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray sem_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen sem_info_t)))) sem_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen sem_info_t))))
               (Tarray sem_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match sem_info_t semvl |] **
             [| length semvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| semvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] **
             (* [| 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned |] ** *)
              P ->
    s |= ASeminfo (b,i) semvl ** P.
Proof.
  intros.
  do 4 destruct H.
  sep split in H.
  subst.
  eapply ASeminfo_select_sn_strong.
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed.

Lemma apthreadmutex_len: 
  forall s l vl, s |= APthreadMutex l vl -> length vl = ∘ (OS_USER_MAX_EVENTS / 3).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed.


Lemma APthreadMutex_unfold_any_idx: 
  forall s b i muxvl idx,
    s |= APthreadMutex (b, i) muxvl ->
    (idx < length muxvl)%nat ->
    s |= EX vll1 vll2 vl ,
        GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray pthread_mutex_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen pthread_mutex_info_t))) pthread_mutex_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen pthread_mutex_info_t))))
          (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
          [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| muxvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length muxvl * typelen pthread_mutex_info_t) <= Int.max_unsigned). 
  { erewrite apthreadmutex_len; eauto.  simpl. (* mauto. *) solve_usr_max_evts_rgn. }
  introv Hlenle. 
  unfold APthreadMutex in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length muxvl = idx + (length muxvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx muxvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length muxvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen pthread_mutex_info_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length muxvl * typelen pthread_mutex_info_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx muxvl) = idx /\ length (skipn idx muxvl) = (length muxvl - idx)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[[]]]]]]].
(*   destruct s as [[[[[[]]]]]]. *)
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length muxvl - idx = S (length muxvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx muxvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length muxvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen pthread_mutex_info_t) +ᵢ  $ Z.of_nat (typelen pthread_mutex_info_t) =
                   $ Z.of_nat (S idx * typelen pthread_mutex_info_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen pthread_mutex_info_t)%nat with (typelen pthread_mutex_info_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 64) = Int.unsigned ($ (Z.of_nat (idx * 64)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. 
      (* unfold_usr_max_evts_in H11.
      simpl in H11.
      rewrite pos_to_nat_6 in H11. 
      rewrite H11 in Hlengt.
      apply lt_imply_le.
      apply Z.lt_le_trans with (m:=396). auto. 
      mauto. mauto. *)
      simpl typelen in *.
      clear -Harith.
      eapply Z.le_trans; eauto.
      auto with zarith.
    }
    assert (Hb: 64 = Int.unsigned ($64)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) = length muxvl - S idx)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17. unfold pthread_mutex_info_t in H17. fold pthread_mutex_info_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idx muxvl). exists vlt.
  exists vh. exists x. exists x0. exists m. exists x2. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx7emp & Hx10emp).
  subst x6. unfold emposabst in Hx10emp. subst x9. 
  assert (x5 = x0). { apply map_join_emp' in H5. auto. }
  subst x5.
  simpl in H7. simpl in H2.
  assert (x8 = x3). { apply map_join_emp' in H7. auto. }
  subst x8.
  simpl in H6. 
  simpl in H1.

  exists x1.  do 5 eexists. splits; eauto.
  eexists x7. do 2 eexists. exists x14. do 2 eexists. 
  splits; eauto.

  unfold Aarray_new.
  exists x12. do 2 eexists. exists x15. do 2 eexists.
  splits; eauto.
  instantiate (1:=empenv). join auto.
  instantiate (1:=emp). join auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto. 
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. eauto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. 
  rewrite <- Hsplit at 1. rewrite Hlst. auto.
  simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. split; auto.
  rewrite Hlst in H15. simpl in H15. 
  eapply sub_eq_succ; eauto.
  simpl. split; auto. unfolds. auto.
  rewrite H11 in HSidx.
  apply inj_le in HSidx. 
  (* simpl in HSidx.
  unfold_usr_max_evts. simpl. 
  asserts_rewrite (20/3 = 6). { auto. }
  auto. *)
  rewrite nat_of_Z_eq in HSidx; auto.
  solve_usr_max_evts_rgn.
  simpl. split; auto. unfolds. auto.

Qed. 

Lemma APthreadMutex_unfold_any_idx_frm: 
  forall s b i muxvl idx P,
    s |= APthreadMutex (b, i) muxvl ** P ->
    (idx < length muxvl)%nat ->
    s |= (EX vll1 vll2 vl ,
        GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray pthread_mutex_info_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen pthread_mutex_info_t))) pthread_mutex_info_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen pthread_mutex_info_t))))
            (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
          [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
          [| muxvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= OS_USER_MAX_EVENTS / 3 |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply APthreadMutex_unfold_any_idx; eauto.
Qed. 



Lemma APthreadMutex_select_sn_strong :
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 ->
    (* 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned -> *)
    s |= GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
      Aarray_new (b, i) (Tarray pthread_mutex_info_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen pthread_mutex_info_t)))) pthread_mutex_info_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen pthread_mutex_info_t))))
        (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match pthread_mutex_info_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (OS_USER_MAX_EVENTS / 3) ->
    s |= APthreadMutex (b, i) (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen pthread_mutex_info_t) <= Int.max_unsigned).
  {
    remember (typelen pthread_mutex_info_t) as X. 
    unfold pthread_mutex_info_t in HeqX. simpl in HeqX. 
    rewrite HeqX.
    (* unfold_usr_max_evts_in H.
    simpl in H.
    asserts_rewrite (20 / 3 = 6)  in H. { auto with zarith. } 
    int auto. *)
    solve_usr_max_evts_rgn.
  }
  unfold APthreadMutex.
  sep pauto.
  assert (Heq: ∘ (OS_USER_MAX_EVENTS / 3) 
               =  Nat.add n (S (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  (* assert (Heq1: Z.to_nat (OS_USER_MAX_EVENTS / 3 - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (OS_USER_MAX_EVENTS / 3))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith. *)
  solve_usr_max_evts_rgn.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.

  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen pthread_mutex_info_t) +ᵢ  $ Z.of_nat (typelen pthread_mutex_info_t) 
                   = $ Z.of_nat (S n * typelen pthread_mutex_info_t)).
  { int auto. }
  sep pauto.
  unfold pthread_mutex_info_t.
  unfold assertion.Aarray_new.
  unfold assertion.Aarray_new'.
  fold pthread_mutex_info_t.
  sep pauto.
Qed.

Lemma APthreadMutex_select_sn_ex_strong:
  forall s P b i muxvl,
     s |= EX vll1 n vll2 vl ,
             GV Pthread_Mutex @ pthread_mutex_info_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray pthread_mutex_info_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen pthread_mutex_info_t)))) pthread_mutex_info_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen pthread_mutex_info_t))))
               (Tarray pthread_mutex_info_t (∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match pthread_mutex_info_t muxvl |] **
             [| length muxvl = ∘ (OS_USER_MAX_EVENTS / 3) |] **
             [| muxvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (OS_USER_MAX_EVENTS / 3 - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= OS_USER_MAX_EVENTS / 3 |] **
             (* [| 0 <= Int.unsigned i + (OS_USER_MAX_EVENTS / 3) * (Z.of_nat (typelen sem_info_t)) <= Int.max_unsigned |] ** *)
              P ->
    s |= APthreadMutex (b, i) muxvl ** P.
Proof.
  intros.
  do 4 destruct H.
  sep split in H.
  subst.
  eapply APthreadMutex_select_sn_strong.
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed.
