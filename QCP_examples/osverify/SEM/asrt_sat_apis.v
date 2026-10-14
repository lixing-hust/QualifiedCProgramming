
Require Import sem_language.
Require Import sem_opsem. 
Require Import succ_gen.
Require Import sem_sys.

Require Import sem_lemmas.

Fixpoint head_asrt_sat (cd: spec_code) (lau: LAuxSt) := 
  match cd with
    spec_prim asrt _ _ => asrt lau
  | sched asrt => asrt lau
  | spec_done _ => True 
  | spec_seq cd1 cd2 => head_asrt_sat cd1 lau
  | spec_choice cd1 cd2 => head_asrt_sat cd1 lau /\ head_asrt_sat cd2 lau
  | spec_assume asrt _ => asrt lau
  | spec_assert _ => True
  | spec_abort => True 
  | spec_set_pt _ => True
  | spec_atm cd => head_asrt_sat cd lau
  end.


Ltac des_vl_absprog hstep := 
  match goal with
    vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
      destruct vl; inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst; inverts hstep
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst; inverts hstep)   
  end.

Ltac show_n := 
  match goal with H: nth_error _ ?n = _ |- _ => idtac n end.

Ltac contra :=
  match goal with H: context[nth_error] |- _ => simpl in H; tryfalse end.


(* Ltac semtrywait_symexe0_ := *)
(*   match goal with *)
(*     H: context[nth_error] |- _ => simpl in H; inverts H *)
(*   | H: context[spec_step], Hhsat: context[head_asrt_sat] |- _ => *)
(*       first [solve [unfolds in Hhsat; simpljoin; simpl; unfold nml_asrt; auto] | *)
(*               inverts H]   *)
(*   | H: _ |- _ => solve [simpl; unfold nml_asrt; auto] *)
(*   end. *)

Lemma nml_asrt_tskpt:
  forall lau, 
    nml_asrt lau -> tskpt lau = PtNormal.
Proof.
  introv Hna.
  unfolds in Hna.
  subst.
  simpl; auto.
Qed.

Local Hint Resolve nml_asrt_tskpt: nml_ppt_lemmas. 

(* Ltac semtrywait_symexe0_ := *)
(*   match goal with *)
(*     H: context[nth_error] |- _ => simpl in H; inverts H *)
(*   | H: context[spec_step], Hhsat: context[head_asrt_sat] |- _ => *)
(*       first [solve [unfolds in Hhsat; simpljoin; simpl; unfold nml_asrt; subst; simpl; auto] | *)
(*               inverts H]  *)
(*   | Hhsat: context[head_asrt_sat] |- _ => *)
(*       solve [ unfolds in Hhsat; simpljoin; simpl; unfold nml_asrt; subst; simpl; auto] *)
(*   end. *)

Ltac semtrywait_symexe0 :=
  match goal with
    H: context[nth_error] |- _ => simpl in H; inverts H; semtrywait_symexe0
  | H: context[spec_step], Hhsat: context[head_asrt_sat] |- _ =>
      first [
          solve [
              unfolds in Hhsat; simpljoin;
              simpl; unfold nml_asrt; simpl;
              eauto with nml_ppt_lemmas
            ] |
          inverts H; semtrywait_symexe0 ] 
  | Hhsat: context[head_asrt_sat] |- _ =>
      solve [
          unfolds in Hhsat; simpljoin;
          simpl; unfold nml_asrt; simpl;
          eauto with nml_ppt_lemmas ]
  end.

Ltac semtrywait_symexe k :=
  match k with
    S ?k' => 
      first [
          solve [contra] | 
          match goal with n: nat |- _ => destruct n end;
          [ show_n; semtrywait_symexe0 | semtrywait_symexe k' ]
        ]
  | _ => idtac
  end.
  
Lemma semtrywait_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semtrywait vl <> ABORT -> 
    nth_error (get_all_succs (semtrywait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semtrywait in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semtrywait_succ_asrt_preserved".
  semtrywait_symexe 30%nat. 
Qed.   

Lemma semtrywait_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    semtrywait vl <> ABORT -> 
    nth_error (get_all_succs (semtrywait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semtrywait in Hnth.
  repeat des_vl_absprog Hstep.
  idtac "semtrywait_succ_asrt_end".
  semtrywait_symexe 30%nat.
Qed. 

Require Import protect. 

(* Ltac symexe0 := *)
(*   match goal with *)
(*     H: context[nth_error] |- _ => simpl in H; inverts H; symexe0 *)
(*   | H: ~(exists _, END _ = END _) /\ _ |- _ => *)
(*       let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto) *)
(*   | H: _ /\ (ABORT <> ABORT) |- _ => *)
(*       let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto *)
(*   | H: ~(exists _, END _ = END _) |- _ => false; apply H; eexists; eauto *)
(*   | H: ABORT <> ABORT |- _ => false; apply H; auto  *)
(*   | H: spec_step _ spec_abort _ _ _ _ _ |- _ => inverts H *)
(*   | cd: spec_code, H: spec_step _ ?cd _ _ _ _ _ |- _ => *)
(*       protect H; symexe0 *)
(*   | cd: spec_step, H: spec_step _ spec_atm (?cd) _ _ _ _ _ |- _ => *)
(*       protect H; symexe0 *)
(*   | H: context[spec_step], Hhsat: context[head_asrt_sat] |- _ => *)
(*       first [solve [simpl in Hhsat; simpljoin; *)
(*                     simpl; unfold trivial_asrt; unfold pend_asrt; simpl; (try splits); auto] | *)
(*               inverts H; symexe0]  *)
(*   | Hhsat: context[head_asrt_sat] |- _ => *)
(*       solve [ *)
(*           simpl in Hhsat; simpljoin; *)
(*           simpl; unfold trivial_asrt; unfold pend_asrt; simpl; (try splits); auto *)
(*         ] *)
(*   end. *)

Ltac semwait_symexe0 :=
  match goal with
    H: context[nth_error] |- _ => simpl in H; inverts H; semwait_symexe0
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto)
  | H: _ /\ (ABORT <> ABORT) |- _ =>
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto
  | H: ~(exists _, END _ = END _) |- _ => false; apply H; eexists; eauto
  | H: ABORT <> ABORT |- _ => false; apply H; auto
  | H: spec_step _ spec_abort _ _ _ _ _ |- _ => inverts H
  | cd: spec_code, H: spec_step _ ?cd _ _ _ _ _ |- _ =>
      protect H; semwait_symexe0
  | cd: spec_step, H: spec_step _ spec_atm (?cd) _ _ _ _ _ |- _ =>
      protect H; semwait_symexe0
  | H: context[spec_step] |- _ => inverts H; semwait_symexe0
  | Hhsat: context[head_asrt_sat] |- _ =>
      solve [
          simpl in Hhsat; simpljoin;
          simpl; unfold nml_asrt; unfold pend_asrt; simpl; (try splits);
          eauto with nml_ppt_lemmas
        ]
  end.

Ltac semwait_symexe k :=
  match k with
    S ?k' => 
      first [
          solve [contra] | 
          match goal with n: nat |- _ => destruct n end;
          [ show_n; semwait_symexe0 | semwait_symexe k' ]
        ]
  | _ => idtac
  end.


Lemma semwait_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semwait vl <> ABORT -> 
    nth_error (get_all_succs (semwait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semwait in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semwait_succ_asrt_preserved".
  semwait_symexe 50%nat.
Qed. 

Lemma semwait_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    semwait vl <> ABORT -> 
    nth_error (get_all_succs (semwait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semwait in Hnth.
  repeat des_vl_absprog Hstep.
  idtac "semwait_succ_asrt_end".
  semwait_symexe 50%nat.
Qed. 


Lemma semtimedwait_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semtimedwait vl <> ABORT -> 
    nth_error (get_all_succs (semtimedwait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semtimedwait in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semtimedwait_succ_asrt_preserved".
  semwait_symexe 50%nat.
Qed. 

Lemma semtimedwait_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    semtimedwait vl <> ABORT -> 
    nth_error (get_all_succs (semtimedwait vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal.
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semtimedwait in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semtimedwait_succ_asrt_end".
  semwait_symexe 50%nat.
Qed. 


Lemma semsignal_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semsignal vl <> ABORT -> 
    nth_error (get_all_succs (semsignal vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semsignal in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semsignal_succ_asrt_preserved".
  semwait_symexe 75%nat.
Qed.

Lemma semsignal_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    semsignal vl <> ABORT -> 
    nth_error (get_all_succs (semsignal vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semsignal in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semsignal_succ_asrt_end".
  semwait_symexe 75%nat.
Qed.


Lemma seminit_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    seminit vl <> ABORT -> 
    nth_error (get_all_succs (seminit vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold seminit in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "seminit_succ_asrt_preserved".
  semwait_symexe 40%nat.
Qed. 

Lemma seminit_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    seminit vl <> ABORT -> 
    nth_error (get_all_succs (seminit vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold seminit in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "seminit_succ_asrt_end".
  semwait_symexe 40%nat.
Qed. 


Lemma seminitbin_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    seminitbin vl <> ABORT -> 
    nth_error (get_all_succs (seminitbin vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold seminitbin in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "seminitbin_succ_asrt_preserved".
  semwait_symexe 40%nat.
Qed.

Lemma seminitbin_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    seminitbin vl <> ABORT -> 
    nth_error (get_all_succs (seminitbin vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold seminitbin in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "seminitbin_succ_asrt_end".
  semwait_symexe 40%nat.
Qed.


Lemma semdestroy_nabt_spec_step_sat_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semdestroy vl <> ABORT -> 
    nth_error (get_all_succs (semdestroy vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau cd' O' lau' ->
    head_asrt_sat cd' lau'. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semdestroy in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semdestroy_succ_asrt_preserved".
  semwait_symexe 30%nat.
Qed.

Lemma semdestroy_nabt_spec_step_sat_end:
  forall sc n vl cd O vo O' lau lau',
    semdestroy vl <> ABORT -> 
    nth_error (get_all_succs (semdestroy vl)) n = Some cd ->
    head_asrt_sat cd lau -> 
    spec_step sc cd O lau (END vo) O' lau' ->
    tskpt lau' = PtNormal. 
Proof.
  introv Hnabt Hnth Hhsat Hstep.
  unfold semdestroy in Hnth.
  repeat des_vl_absprog Hstep. 
  idtac "semdestroy_succ_asrt_end".
  semwait_symexe 30%nat.
Qed.



