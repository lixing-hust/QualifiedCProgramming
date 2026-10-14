Require Import FunctionalExtensionality.

Require Import memory. 
Require Import if_language.
Require Import if_opsem.
Require Import mq_apispecs.
Require Import prt_apispecs. 
Require Import osspecs. 
Require Import properties.
Require Import if_assms.
Require Import sem_prop.
Require Import equiv_sem_prop.
Require Import if_succ_gen.
Require Import if_common_lemmas.
Require Import mqsend_cproof.
Require Import equiv_prop. 
Require Import sem_prop_2.
Require Import if_good_code.
Require Import data_invs.
Require Import equiv_prop.
(* Require Import assms. *)
(* Require Import succ_gen. *)
Require Import math_auto.
Require Import symbolic_lemmas.
Require Import hasrt_sat_preserve.
Require Import intspecs.
Require Import sched_lemma.
Set Keyed Unification.



Lemma speccode_not_eniact:
forall act pu T t cst' O O' A pc cd cd' ke ks ,
act = EniAct->
good_client_code pu->
reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst' O->
(pu, (api_spec, int_spec, get_hprio_d)) = (pc, A)->
spec_step (snd A) cd O cd' O' act->
get T t = Some (curs (hapi_code cd), (ke, ks))->
False.
Proof.
introv Hact Hgod Hrch HA Hstep1 Hget.
inverts Hact.
lets Hgoodcode: reachable_good_tasks Hgod Hrch.
unfolds in Hgoodcode.
lets H':Hgoodcode Hget.
clear Hgoodcode.
unfolds in H'.
destruct H' as (Hgodeval & H'').
unfolds in Hgodeval.
unfolds in Hgodeval.
unfolds in Hgodeval.
destruct Hgodeval as [Hgodapi|[Hgodint|[Hgodend|Hgodabort]]].
destruct Hgodapi as (fid & acode & ft & vl & Hapispec & Hin).
unfold api_spec in Hapispec.
destruct fid.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
destruct p.
destruct p.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
(*bufferpostapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferpost in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v1.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

unfold buffer_apispecs.bufferpost in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
(*end bufferpostapi*)
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*Qportpendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold qportpend in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v1.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

(*In cd (get_all_succs_aux (qportpend vl))*)
unfold qportpend in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
destruct v1.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.


destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

tryfalse.
tryfalse.
tryfalse.

simpl in Hapispec.
tryfalse.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*sampleportpostapi begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold sampleportpost in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

unfold sampleportpost in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
(*sampleportpostapi end*)


destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
(*bufferpendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferpend in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

unfold buffer_apispecs.bufferpend in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
(*bufferpendapi end*)
tryfalse.

simpl in Hapispec.
(*mqtimerecv begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqtimedreceive in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

destruct vl.
simpl in Hin.
tryfalse.
simpl in Hin.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
(*mqtimerecv end*)

destruct p.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.

(*portacceptapi begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold portaccept in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

unfold portaccept in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
(*sampleportpostapi end*)

tryfalse.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.

(*qportpostapi *)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold qportpost in Hin.
inverts Hin.
destruct vl.
inverts Hstep1.
destruct vl.
repeat step_contra0;
spec_act_solver EniAct.
destruct v0.
repeat step_contra0;
spec_act_solver EniAct.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
repeat step_contra0;
spec_act_solver EniAct.
repeat step_contra0;
spec_act_solver EniAct.
repeat step_contra0;
spec_act_solver EniAct.
unfold qportpost in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.


destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*bufferacceptapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferaccept in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.

unfold buffer_apispecs.bufferaccept in Hin.
destruct vl.
inverts Hin.
destruct vl.
inverts Hin.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.

(*bufferacceptapi end*)
simpl in Hapispec.
tryfalse.
simpl in Hapispec.


inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqreceive in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
unfold mqreceive in Hin.
destruct vl.
tryfalse.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.



simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.




simpl in Hapispec.
(*mqsendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqsend in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.


unfold mqsend in Hin.
destruct vl.
tryfalse.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.




destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.




simpl in Hapispec.
tryfalse.


(*int_spec hid = Some icode /\ In cd (get_all_succs icode)*)
destruct Hgodint as (hid & icode & Hintspec & Hin).
unfold int_spec in Hintspec.

do 6 (destruct hid;simpl in Hintspec;tryfalse).
inverts Hintspec.
simpl in Hin.
destruct Hin as [Hin|[Hin|[Hin|Hin]]].
inverts Hin.

repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
tryfalse.
destruct Hgodend as (v & Hin).
inverts Hin.
repeat step_contra0;
spec_act_solver EniAct.
inverts Hgodabort.

repeat step_contra0;
spec_act_solver EniAct.
Qed.


Lemma speccode_not_schedact:
forall act pu T t cst' O O' A pc cd cd' ke ks ,
act = SchAct->
good_client_code pu->
reachable (pu, (api_spec, int_spec, get_hprio_d)) T cst' O->
(pu, (api_spec, int_spec, get_hprio_d)) = (pc, A)->
spec_step (snd A) cd O cd' O' act->
get T t = Some (curs (hapi_code cd), (ke, ks))->
False.
Proof.
introv Hact Hgod Hrch HA Hstep1 Hget.
inverts Hact.
lets Hgoodcode: reachable_good_tasks Hgod Hrch.
unfolds in Hgoodcode.
lets H':Hgoodcode Hget.
clear Hgoodcode.
unfolds in H'.
destruct H' as (Hgodeval & H'').
unfolds in Hgodeval.
unfolds in Hgodeval.
unfolds in Hgodeval.
destruct Hgodeval as [Hgodapi|[Hgodint|[Hgodend|Hgodabort]]].
destruct Hgodapi as (fid & acode & ft & vl & Hapispec & Hin).
unfold api_spec in Hapispec.
destruct fid.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
destruct p.
destruct p.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
(*bufferpostapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferpost in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v1.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

unfold buffer_apispecs.bufferpost in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
(*end bufferpostapi*)
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*Qportpendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold qportpend in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v1.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

(*In cd (get_all_succs_aux (qportpend vl))*)
unfold qportpend in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
destruct v1.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.


destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

tryfalse.
tryfalse.
tryfalse.

simpl in Hapispec.
tryfalse.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.

(*sampleportpostapi begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold portaccept in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

unfold portaccept in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
(*sampleportpostapi end*)

destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*bufferpendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferpend in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
inverts Hstep1.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.


unfold buffer_apispecs.bufferpend in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
(*bufferpendapi end*)
tryfalse.
tryfalse.
simpl in Hapispec.
(*mqtimerecv begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqtimedreceive in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

destruct vl.
simpl in Hin.
tryfalse.
simpl in Hin.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
(*mqtimerecv end*)

destruct p.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.

(*portacceptapi begin*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold portaccept in Hin.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct v0.
inverts Hin.
inverts Hstep1.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
inverts Hstep1.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.

unfold portaccept in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
(*portacceptapi end*)

destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.

(*qportpostapi *)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold qportpost in Hin.
inverts Hin.
destruct vl.
inverts Hstep1.
destruct vl.
repeat step_contra0;
spec_act_solver SchAct.
destruct v0.
repeat step_contra0;
spec_act_solver SchAct.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
repeat step_contra0;
spec_act_solver SchAct.
repeat step_contra0;
spec_act_solver SchAct.
repeat step_contra0;
spec_act_solver SchAct.
unfold qportpost in Hin.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.


destruct p.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
destruct p.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.
(*bufferacceptapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold buffer_apispecs.bufferaccept in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.


unfold buffer_apispecs.bufferaccept in Hin.
destruct vl.
inverts Hin.
destruct vl.
inverts Hin.
destruct vl.
simpl in Hin.

destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.

(*bufferacceptapi end*)
simpl in Hapispec.
tryfalse.
simpl in Hapispec.
tryfalse.


inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqreceive in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
unfold mqreceive in Hin.
destruct vl.
tryfalse.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.



simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.




simpl in Hapispec.
(*mqsendapi*)
inverts Hapispec.
simpl in Hin.
destruct Hin as [Hin|Hin].
unfold mqsend in Hin.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v0.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v1.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct v2.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct vl.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.


unfold mqsend in Hin.
destruct vl.
tryfalse.
destruct v.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v0.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v1.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.
destruct vl.
tryfalse.
destruct v2.
tryfalse.
tryfalse.




destruct vl.
simpl in Hin.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
destruct Hin as [Hin|Hin].
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.
tryfalse.




simpl in Hapispec.
tryfalse.


(*int_spec hid = Some icode /\ In cd (get_all_succs icode)*)
destruct Hgodint as (hid & icode & Hintspec & Hin).
unfold int_spec in Hintspec.

do 6 (destruct hid;simpl in Hintspec;tryfalse).
inverts Hintspec.
simpl in Hin.
destruct Hin as [Hin|[Hin|[Hin|Hin]]].
inverts Hin.

repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
tryfalse.
destruct Hgodend as (v & Hin).
inverts Hin.
repeat step_contra0;
spec_act_solver SchAct.
inverts Hgodabort.

repeat step_contra0;
spec_act_solver SchAct.
Qed.

Require Import join_lib.
Lemma dom_impl_8_proof:
forall x x0 x1 x5 x4 x6 x7 x8 x9 x3 x2 x13 x12
      O Of O',
join O Of O'->
get O abtcblsid = Some (abstcblist x)->
get O absecblsid = Some (absecblist x0)->
get O ostmid = Some (ostm x1)->
get O ksdomtimeid = Some (ksdomtime x5)->
get O ksdschedidxid = Some (ksdschedidx x4)->
get O ksdschedlenid = Some (ksdschedlen x6)->
get O kscurdomid = Some (kscurdom x7)->
get O kslastdomid = Some (kslastdom x8)->
get O ksdschedid = Some (ksdsched x9)->
dom_impl O'
  (set
     (set
        (set
           (set
              (set
                 (set
                    (set (set O' absecblsid (absecblist x3)) abtcblsid
                       (abstcblist x2)) ostmid 
                    (ostm (x1 +ᵢ  Int.one))) ksdomtimeid
                 (ksdomtime (x5 -ᵢ Int.one))) ksdschedidxid
              (ksdschedidx
                 (if Int.ltu (x4 +ᵢ  Int.one) x6
                  then x4 +ᵢ  Int.one
                  else Int.zero))) kslastdomid 
           (kslastdom x7)) kscurdomid (kscurdom x12)) ksdomtimeid
     (ksdomtime x13)).
Proof.
intros.
unfolds.
intros.
destruct (get O' x10) eqn: eq1. 
2:{destruct x10; repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]).
  rewrite set_a_get_a. assert (get O' abstcblsid = Some (abstcblist x)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' absecblsid = Some (absecblist x0)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' ostmid = Some (ostm x1)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' ksdschedidxid = Some (ksdschedidx x4)). eapply join_get_get_l;eauto. tryfalse. tryfalse.
  rewrite set_a_get_a. assert (get O' kscurdomid = Some (kscurdom x7)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' kslastdomid = Some (kslastdom x8)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' ksdomtimeid = Some (ksdomtime x5)). eapply join_get_get_l;eauto. tryfalse.
  }
match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
lets Hoabstcblsid_: Hoabstcblsid.
eapply join_get_get_l in Hoabstcblsid_;eauto.
match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid end. 
lets Hoabsecblsid_: Hoabsecblsid.
eapply join_get_get_l in Hoabsecblsid_;eauto.
match goal with H: get O ostmid = _ |-_=> rename H into Hoostmid end. 
lets Hoostmid_: Hoostmid.
eapply join_get_get_l in Hoostmid_;eauto.
match goal with H: get O ksdomtimeid = _ |-_=> rename H into Hoksdomtimeid end. 
lets Hoksdomtimeid_: Hoksdomtimeid.
eapply join_get_get_l in Hoksdomtimeid_;eauto.
match goal with H: get O ksdschedidxid = _ |-_=> rename H into Hoksdschedidxid end. 
lets Hoksdschedidxid_: Hoksdschedidxid.
eapply join_get_get_l in Hoksdschedidxid_;eauto.
match goal with H: get O kslastdomid = _ |-_=> rename H into Hokslastdomid end. 
lets Hokslastdomid_: Hokslastdomid.
eapply join_get_get_l in Hokslastdomid_;eauto.
match goal with H: get O kscurdomid = _ |-_=> rename H into Hokscurdomid end. 
lets Hokscurdomid_: Hokscurdomid.
eapply join_get_get_l in Hokscurdomid_;eauto.


destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdschedidxid_ in eq1;tryfalse. rewrite Hokscurdomid_ in eq1;tryfalse.
rewrite Hokslastdomid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdschedidxid_ in eq1;tryfalse. rewrite Hokscurdomid_ in eq1;tryfalse.
rewrite Hokslastdomid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoksdschedidxid_ in eq1;tryfalse. rewrite Hokscurdomid_ in eq1;tryfalse.
rewrite Hokslastdomid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hokscurdomid_ in eq1;tryfalse.
rewrite Hokslastdomid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdschedidxid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hokslastdomid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdschedidxid_ in eq1;tryfalse.
rewrite Hokscurdomid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x10;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdschedidxid_ in eq1;tryfalse.
rewrite Hokscurdomid_ in eq1;tryfalse. rewrite Hokslastdomid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.

Qed.

Lemma dom_impl_4_proof:
forall x x0 x1 x5 x3 x2
      O Of O',
join O Of O'->
get O abtcblsid = Some (abstcblist x)->
get O absecblsid = Some (absecblist x0)->
get O ostmid = Some (ostm x1)->
get O ksdomtimeid = Some (ksdomtime x5)->
dom_impl O' (set (set (set (set O' absecblsid (absecblist x3)) abstcblsid (abstcblist x2)) ostmid
              (ostm (x1 +ᵢ  Int.one))) ksdomtimeid (ksdomtime (x5 -ᵢ Int.one))).
Proof.
intros.
unfolds.
intros.
destruct (get O' x4) eqn: eq1. 
2:{destruct x4; repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]).
  rewrite set_a_get_a. assert (get O' abstcblsid = Some (abstcblist x)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' absecblsid = Some (absecblist x0)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' ostmid = Some (ostm x1)). eapply join_get_get_l;eauto. tryfalse.
  rewrite set_a_get_a. assert (get O' ksdomtimeid = Some (ksdomtime x5)). eapply join_get_get_l;eauto. tryfalse.
  }
match goal with H: get O abstcblsid = _ |-_=> rename H into Hoabstcblsid end. 
lets Hoabstcblsid_: Hoabstcblsid.
eapply join_get_get_l in Hoabstcblsid_;eauto.
match goal with H: get O absecblsid = _ |-_=> rename H into Hoabsecblsid end. 
lets Hoabsecblsid_: Hoabsecblsid.
eapply join_get_get_l in Hoabsecblsid_;eauto.
match goal with H: get O ostmid = _ |-_=> rename H into Hoostmid end. 
lets Hoostmid_: Hoostmid.
eapply join_get_get_l in Hoostmid_;eauto.
match goal with H: get O ksdomtimeid = _ |-_=> rename H into Hoksdomtimeid end. 
lets Hoksdomtimeid_: Hoksdomtimeid.
eapply join_get_get_l in Hoksdomtimeid_;eauto.



destruct a;
try solve [ eexists;repeat (try rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse])].

destruct x4;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x4;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoostmid_ in eq1;tryfalse. rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x4;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
rewrite Hoksdomtimeid_ in eq1;tryfalse.

destruct x4;try solve[eexists; repeat(try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv H_;inverts H_;tryfalse] )]. 
rewrite Hoabstcblsid_ in eq1;tryfalse. rewrite Hoabsecblsid_ in eq1;tryfalse. rewrite Hoostmid_ in eq1;tryfalse.
eexists. repeat (try rewrite set_a_get_a;rewrite set_a_get_a';[eauto|introv Hfalse; tryfalse]). rewrite set_a_get_a. eauto.
Qed.


