
(* Code, spec, and proof of internal function UserAddrCheck *) 
(* as formalized by CNU *)

Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(* (* new definitions in os_code_defs.v *) *)

(* Definition UserAddrStart := 0%Z. *)
(* Definition UserAddrEnd := 4294867295%Z. *)
(* Definition addr : ident := 670%Z. *)
(* Definition UserAddrCheck := 671%Z. *)

(* (*err Int8s, Tint8 stands for Int8u*) *)
(* Notation "'Int8s'" := (Tint8) (at level 5) : code_scope . *)

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

(* new definitions of UserAddrCheck in spec\ifun_spec.v *)

Require Import include_frm.
Require Import Lists.ListSet.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Export os_inv.
Require Import abs_op.
Require Import os_core.
Require Import code_notations.
Require Import inv_prop.
Require Import ifun_spec.

Require Import List.


(* UserAddrCheck *)
(* pre *)
Definition UserAddrCheckPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX a s,
    Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a)|] ** [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg.

Theorem UserAddrCheckPreGood (vl:vallist) ll ct:
  GoodFunAsrt (UserAddrCheckPre' vl ll ct).
Proof.
unfold GoodFunAsrt.
unfold UserAddrCheckPre'.
intros.
simpl.
repeat split; try auto.
Qed.

Definition UserAddrCheckPre : fpre :=
  fun vl ll ct => mkfunasrt (UserAddrCheckPreGood vl ll ct).

Open Scope int_scope.

Definition UserAddrCheckPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
   (EX a s,
     Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a) /\ (Z.le (Int.unsigned a) (UserAddrStart) \/ Z.lt (UserAddrEnd) (Int.unsigned a)) |] **
    [| v = Some (V$ 0)|] **
    [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg) \\//
  (EX a s,
      Aisr empisr ** Aie true ** Ais nil ** Acs nil **
     <||s||> **
    [| nth_val 0 vl = Some (Vint32 a) /\ Z.lt (UserAddrStart) (Int.unsigned a) /\  Z.le (Int.unsigned a) (UserAddrEnd) |] **
    [| v = Some (V$ 1)|] **
    [|logicl = logic_code s::nil|] ** p_local OSLInv  ct init_lg).


Theorem UserAddrCheckPostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (UserAddrCheckPost' vl v ll ct).
Proof.
 unfold GoodFunAsrt.
unfold UserAddrCheckPost'.
intros.
simpl.
repeat split; try auto.
Qed.

Definition UserAddrCheckPost : fpost :=
  fun vl v ll ct => mkfunasrt (UserAddrCheckPostGood vl v ll ct).

Open Scope list_scope.

Definition UserAddrCheck_spec : fspec:= (UserAddrCheckPre,UserAddrCheckPost,(Int8s, Int32u::nil)).

Definition new_osq_spec_list := 
  (UserAddrCheck, UserAddrCheck_spec) ::
  nil.  

Definition new_OS_spec :=  convert_spec new_osq_spec_list.

Close Scope list_scope.

(* modified/new in os_program.v *)

Definition new_internal_fun_list := 
  ( UserAddrCheck_impl :: nil)%list.

Definition new_os_internal :=   convert_cfuns new_internal_fun_list.

(* new in UserAddrCheckProof.v *)

Require Import ucos_include.
Require Import absop_rules.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
(* Require Import oscore_common. *)

Require Import Integers.

Local Open Scope Z_scope.
Local Open Scope int_scope.
Local Open Scope code_scope.

Lemma UserAddrCheck_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI new_os_internal UserAddrCheck
                  vl logicl UserAddrCheckPre ct ->
      Some r =
      BuildRetI new_os_internal UserAddrCheck vl logicl UserAddrCheckPost ct ->
      exists t d1 d2 s,
        new_os_internal UserAddrCheck = Some (t, d1, d2, s) /\
        {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
 init spec.
 hoare unfold.
assert (Z.le (Int.unsigned v') (UserAddrStart) \/ Z.lt (UserAddrEnd) (Int.unsigned v') \/ (Z.lt (UserAddrStart) (Int.unsigned v') /\  Z.le (Int.unsigned v') (UserAddrEnd))).
mauto.
unfold UserAddrStart in *.
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
eapply rete_rule' with (t := Int8s); intros.
instantiate (1:=(V$0)).
destruct H; symbolic_execution.
sep pauto.
sep cancel A_dom_lenv.
left.
exists v' v'0.
sep pauto.

(* 4294967295 < Int.unsigned v' *)
(*RETURN 0*)
eapply rete_rule' with (t := Int8s); intros.
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
assert ((Int.unsigned v' <= 0) <-> Int.unsigned v' < 0 \/ Int.unsigned v' = 0).
int auto.
rewrite H in Ha1.
destruct Ha1 as [Hb1 | Hb2].
assert (Int.ltu v' ($ 0) = true /\ Int.eq ($ 0) v' = false).
int auto.
mauto.
assert (Int.ltu v' ($ 0) = false /\ Int.eq ($ 0) v' = true /\ Int.ltu ($ 4294967295) v' = false)as Hq.
int auto.
destruct Hq as [ Hq1  [Hq2 Hq3] ].
rewrite Hq1; rewrite Hq2; rewrite Hq3.
do 2 (simpl; try(rewrite Hc1); try(rewrite Hc2)).
simpl.

eapply rete_rule' with (t := Int8s); intros.
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

eapply rete_rule' with (t := Int8s); intros.
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

eapply rete_rule' with (t := Int8s); intros.
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


