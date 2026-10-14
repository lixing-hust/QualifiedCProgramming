(* Code, spec, and proof of internal function UserAddrCheck *) 
(* as formalized by CNU *)

(*
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.
*)

(* (* new definitions in os_code_defs.v *) *)

(* Definition UserAddrStart := 0%Z. *)
(* Definition UserAddrEnd := 4294867295%Z. *)
(* Definition addr : ident := 670%Z. *)
(* Definition UserAddrCheck := 671%Z. *)

(* (*err Int8s, Tint8 stands for Int8u*) *)
(* Notation "'Int8s'" := (Tint8) (at level 5) : code_scope . *)

(*
Open Scope code_scope.

Definition UserAddrCheck_impl :=
 Int8s ·UserAddrCheck·(⌞addr @ Int32u ⌟)··{
        ⌞⌟;

         If (′UserAddrStart ≥ addr′ ||ₑ addr′ >ₑ ′UserAddrEnd){
           RETURN 〈Int8s〉 ′0
         };ₛ
         RETURN 〈Int8s〉 ′1
 }· . 

Close Scope code_scope.
*)

(* new definitions of UserAddrCheck in spec\ifun_spec.v *)

(*
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.

Require Import abs_op.
Require Import os_core.
Require Import ifun_spec.
*)

(*
Require Import include_frm.
Require Import os_inv.
Require Import inv_prop.
Require Import init_spec.
Require Import ucos_forward.
Require Import math_auto.
Require Import hoare_tactics.
Require Import derived_rules.
Require Import symbolic_execution.
Require Import seplog_tactics.
*)
Require Import ucos_include.
Require Import ios_int.
Require Import Lia.

Open Scope code_scope.
Local Open Scope int_scope.

(* new in UserAddrCheckProof.v *)

(*
Require Import ucos_include.
Require Import absop_rules.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import oscore_common.
*)

Lemma UserAddrCheck6713_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal UserAddrCheck_6713
                  vl logicl UserAddrCheckPre ct ->
      Some r =
      BuildRetI os_internal UserAddrCheck_6713 vl logicl UserAddrCheckPost_6713 ct ->
      exists t d1 d2 s,
        os_internal UserAddrCheck_6713 = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- ct {{p}} s {{Afalse}}. 
Proof.
 init spec.
 hoare unfold.
assert (Z.le (Int.unsigned v') (UserAddrStart_6713) \/ Z.lt (UserAddrEnd) (Int.unsigned v') \/ (Z.lt (UserAddrStart_6713) (Int.unsigned v') /\  Z.le (Int.unsigned v') (UserAddrEnd))).
mauto.
unfold UserAddrStart_6713 in *.
unfold UserAddrEnd in *.
(* destruct H. *)
hoare unfold.
(*L1: if condition*)
hoare forward. 
destruct (Int.ltu v' ($ 0)); simpl; intro; tryfalse.
destruct (Int.eq ($ 0) v'); simpl; intro; tryfalse.
destruct (Int.ltu v' ($ 0)); destruct (Int.eq ($ 0) v'); simpl; intro; tryfalse.
destruct (Int.ltu ($ 4294967295) v'); simpl; intro; tryfalse.
destruct (Int.ltu v' ($ 0)); destruct (Int.eq ($ 0) v'); destruct (Int.ltu ($ 4294967295) v'); simpl; intro; tryfalse.
hoare unfold.

destruct H as [ Ha1 | [Ha2 | Ha3] ].
(*L2 : RETURN 0*)
(* Int.unsigned v' <= 0 *)
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$0)).
destruct H; symbolic_execution.
sep pauto.
sep cancel A_dom_lenv.
left.
exists v' v'0.
sep pauto.

(* 4294967295 < Int.unsigned v' *)
(*RETURN 0*)
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$0)).
destruct H.
symbolic_execution.
sep pauto.
sep cancel A_dom_lenv.
left.
exists v' v'0.
sep pauto.

(* 0 < Int.unsigned v' <= 4294967295 *)
assert (Int.ltu v' ($ 0) = false /\ Int.eq ($ 0) v' = false /\ Int.ltu ($ 4294967295) v' = false) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1 in *; rewrite Hq2 in *; rewrite Hq3 in *.
destruct H0.
simpl.
int auto.

(*L3: RETURN 1*)
assert (Int.ltu Int.zero Int.one = true /\ Int.ltu Int.zero Int.zero = false) as Hc.
int auto.
destruct Hc as [ Hc1 Hc2 ].
destruct H as [ Ha1 | [Ha2 | Ha3] ].
(* Int.unsigned v' <= 0 *)
assert ((Int.unsigned v' <= 0)%Z <-> (Int.unsigned v' < 0)%Z \/ (Int.unsigned v' = 0)%Z).
int auto.
rewrite H in Ha1.
destruct Ha1 as [Hb1 | Hb2].
assert (Int.ltu v' ($ 0) = true /\ Int.eq ($ 0) v' = false).
int auto.
(*mauto.*)
_mathsolver.munfold. (*_mathsolver.pre.*)
repeat _mathsolver.pre'. 
repeat (try lia; timeout 8 _mathsolver.stdrange_fin_elem).
(*_mathsolver.mrewrite; _mathsolver.bf_basic_solver.*)

assert (Int.ltu v' ($ 0) = false /\ Int.eq ($ 0) v' = true /\ Int.ltu ($ 4294967295) v' = false)as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1; rewrite Hq2; rewrite Hq3.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.

eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H0.
symbolic_execution.
destruct H0.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H0.
sep split in H0.
tryfalse.
sep pauto.
destruct H1.
inverts H1.
inverts H1.

(* 4294967295 < Int.unsigned v' *)
 assert (Int.ltu v' ($ 0) = false /\ Int.eq ($ 0) v' = false /\ Int.ltu ($ 4294967295) v' = true) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1; rewrite Hq2; rewrite Hq3.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.

eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H.
symbolic_execution.
destruct H.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H.
sep split in H.
tryfalse.
sep pauto.
destruct H0.
inverts H0.
inverts H0.

(* 0 < Int.unsigned v' <= 4294967295 *)
assert (Int.ltu v' ($ 0) = false /\ Int.eq ($ 0) v' = false /\ Int.ltu ($ 4294967295) v' = false) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1 in *; rewrite Hq2 in *; rewrite Hq3 in *.
simpl.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.

eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H.
symbolic_execution.
destruct H.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H.
sep split in H.
tryfalse.
sep pauto.
sep cancel A_dom_lenv.
right.
exists v' v'0.
sep pauto.
Qed.

Lemma UserAddrCheck6678_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal UserAddrCheck_6678
                  vl logicl UserAddrCheckPre ct ->
      Some r =
      BuildRetI os_internal UserAddrCheck_6678 vl logicl UserAddrCheckPost_6678 ct ->
      exists t d1 d2 s,
        os_internal UserAddrCheck_6678 = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- ct {{p}} s {{Afalse}}. 
Proof.
 init spec.
 hoare unfold.
assert (Z.le (Int.unsigned v') (UserAddrStart_6678) \/ Z.lt (UserAddrEnd) (Int.unsigned v') \/ (Z.lt (UserAddrStart_6678) (Int.unsigned v') /\  Z.le (Int.unsigned v') (UserAddrEnd))).
mauto.
unfold UserAddrStart_6678 in *.
unfold UserAddrEnd in *.
(* destruct H. *)
hoare unfold.
(*L1: if condition*)
hoare forward. 
destruct (Int.ltu v' ($ 8388608)); simpl; intro; tryfalse.
destruct (Int.eq ($ 8388608) v'); simpl; intro; tryfalse.
destruct (Int.ltu v' ($ 8388608)); destruct (Int.eq ($ 8388608) v'); simpl; intro; tryfalse.
destruct (Int.ltu ($ 4294967295) v'); simpl; intro; tryfalse.
destruct (Int.ltu v' ($ 8388608)); destruct (Int.eq ($ 8388608) v'); destruct (Int.ltu ($ 4294967295) v'); simpl; intro; tryfalse.
hoare unfold.

destruct H as [ Ha1 | [Ha2 | Ha3] ].
(*L2 : RETURN 0*)
(* Int.unsigned v' <= 8388608 *)
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$0)).
destruct H; symbolic_execution.
sep pauto.
sep cancel A_dom_lenv.
left.
exists v' v'0.
sep pauto.

(* 4294967295 < Int.unsigned v' *)
(*RETURN 0*)
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$0)).
destruct H.
symbolic_execution.
sep pauto.
sep cancel A_dom_lenv.
left.
exists v' v'0.
sep pauto.

(* 8388608 < Int.unsigned v' <= 4294967295 *)
assert (Int.ltu v' ($ 8388608) = false /\ Int.eq ($ 8388608) v' = false /\ Int.ltu ($ 4294967295) v' = false) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1 in *; rewrite Hq2 in *; rewrite Hq3 in *.
destruct H0.
simpl.
int auto.

(*L3: RETURN 1*)
assert (Int.ltu Int.zero Int.one = true /\ Int.ltu Int.zero Int.zero = false) as Hc.
int auto.
destruct Hc as [ Hc1 Hc2 ].
destruct H as [ Ha1 | [Ha2 | Ha3] ].
(* Int.unsigned v' <= 8388608 *)
assert ((Int.unsigned v' <= 8388608)%Z <-> (Int.unsigned v' < 8388608)%Z \/ (Int.unsigned v' = 8388608)%Z).
int auto.
rewrite H in Ha1.
destruct Ha1 as [Hb1 | Hb2].
assert (Int.ltu v' ($ 8388608) = true /\ Int.eq ($ 8388608) v' = false /\ Int.ltu ($ 4294967295) v' = false).
int auto.
destruct H0 as [H0A [H0B H0C]].
  rewrite H0A; rewrite H0B; rewrite H0C.
  do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
  simpl.
  eapply rete_rule' with (t := Int32u); intros.
  instantiate (1:=(V$1)).
  destruct H0.
  symbolic_execution.
  destruct H0.
  symbolic_execution.
  sep pauto.
  instantiate (1:= (Vint32 v')).
  destruct H0.
  sep split in H0.
  tryfalse.
  sep pauto.
  destruct H1.
  inverts H1.
  inverts H1.
  
assert (Int.ltu v' ($ 8388608) = false /\ Int.eq ($ 8388608) v' = true /\ Int.ltu ($ 4294967295) v' = false) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1; rewrite Hq2; rewrite Hq3.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H0.
symbolic_execution.
destruct H0.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H0.
sep split in H0.
tryfalse.
sep pauto.
destruct H1.
inverts H1.
inverts H1.

(* 4294967295 < Int.unsigned v' *)
 assert (Int.ltu v' ($ 8388608) = false /\ Int.eq ($ 8388608) v' = false /\ Int.ltu ($ 4294967295) v' = true) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1; rewrite Hq2; rewrite Hq3.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H.
symbolic_execution.
destruct H.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H.
sep split in H.
tryfalse.
sep pauto.
destruct H0.
inverts H0.
inverts H0.

(* 0 < Int.unsigned v' <= 4294967295 *)
assert (Int.ltu v' ($ 8388608) = false /\ Int.eq ($ 8388608) v' = false /\ Int.ltu ($ 4294967295) v' = false) as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1 in *; rewrite Hq2 in *; rewrite Hq3 in *.
simpl.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.
eapply rete_rule' with (t := Int32u); intros.
instantiate (1:=(V$1)).
destruct H.
symbolic_execution.
destruct H.
symbolic_execution.
sep pauto.
instantiate (1:= (Vint32 v')).
destruct H.
sep split in H.
tryfalse.
sep pauto.
sep cancel A_dom_lenv.
right.
exists v' v'0.
sep pauto.
Qed.

Local Close Scope int_scope.
Close Scope code_scope.
