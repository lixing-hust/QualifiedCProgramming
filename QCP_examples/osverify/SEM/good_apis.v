
Require Import sem_language.
Require Import sem_opsem.
Require Import sem_sys.
Require Import succ_gen.
Require Import sem_init.
Require Import sem_tacs.
Require Import join_lib. 
Require Import sem_lemmas.

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

Ltac succ_solver0 :=
  match goal with
    H: context [nth_error] |- _ => simpl in H; inverts H; succ_solver0
  (* | H: spec_step _ (ASSUME _;; _) _ _ _ _ _ |- _ => inverts H; succ_solver0 *)
  (* | H: spec_step _ (ASSUME _) _ _ _ _ _ |- _ => inverts H; succ_solver0 *)
  | H: ~(exists _, END _ = END _) /\ _ |- _ =>
      let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto); succ_solver0
  | H: _ /\ (ABORT <> ABORT) |- _ =>
      let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto; succ_solver0
  | H: _ |- _ \/ ABORT = ABORT \/ _ => try solve [right; left; auto]
  | H: _ |- _ \/ _ \/ (exists _, END _  = END _) => try solve [right; right; eexists; eauto]
  | H: _ : spec_code |- _ =>
      first [solve [left; simpl; auto 65] |
              match goal with H: context[spec_step] |- _ => inverts H; succ_solver0 end]
  | H: _ |- _ => solve [left; simpl; auto 65]
  end.

(* Ltac succ_solver0 := *)
(*   match goal with *)
(*     H: context [nth_error] |- _ => simpl in H; inverts H; succ_solver0 *)
(*   | H: spec_step _ (ASSUME _;; _) _ _ _ _ _ |- _ => inverts H; succ_solver0 *)
(*   | H: spec_step _ (ASSUME _) _ _ _ _ _ |- _ => inverts H; succ_solver0 *)
(*   | H: ~(exists _, END _ = END _) /\ _ |- _ => *)
(*       let hf := fresh in (destruct H as (hf & _); false; apply hf; eexists; eauto); succ_solver0 *)
(*   | H: _ /\ (ABORT <> ABORT) |- _ => *)
(*       let hf := fresh in (destruct H as (_ & hf)); false; apply hf; auto; succ_solver0 *)
(*   | H: _ |- _ \/ ABORT = ABORT \/ _ => try solve [right; left; auto] *)
(*   | H: _ |- _ \/ _ \/ (exists _, END _  = END _) => try solve [right; right; eexists; eauto] *)
(*   | H: _ |- _ => *)
(*       first [ *)
(*           solve [ left; simpl; auto 50 ] | *)
(*           match goal with H: context[spec_step] |- _ => inverts H; succ_solver0 end *)
(*         ] *)
(*   end. *)

Ltac show_n := 
  match goal with H: nth_error _ ?n = _ |- _ => idtac n end.

Ltac contra :=
  match goal with H: context[nth_error] |- _ => simpl in H; tryfalse end.

Ltac succ_solver k :=
  match k with
    S ?k' => 
      first [
          solve [contra] | 
          match goal with n: nat |- _ => destruct n end;
          [ show_n; succ_solver0 | succ_solver k' ]
        ]
  | _ => idtac
  end.
    

Lemma semtrywait_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semtrywait vl <> ABORT -> 
    nth_error (get_all_succs (semtrywait vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (semtrywait vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold semtrywait in Hnth.
  idtac "semtrywait_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 30%nat. 
Qed. 

Lemma semwait_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semwait vl <> ABORT -> 
    nth_error (get_all_succs (semwait vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (semwait vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold semwait in Hnth.
  idtac "semwait_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 45%nat.
Qed.   

Lemma semsignal_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semsignal vl <> ABORT -> 
    nth_error (get_all_succs (semsignal vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (semsignal vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold semsignal in Hnth.
  idtac "semsignal_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 55%nat.
  succ_solver 20%nat.
Qed. 

Lemma semtimedwait_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semtimedwait vl <> ABORT -> 
    nth_error (get_all_succs (semtimedwait vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (semtimedwait vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold semtimedwait in Hnth.
  idtac "semtimedwait_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 55%nat.
Qed. 

Lemma seminit_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    seminit vl <> ABORT -> 
    nth_error (get_all_succs (seminit vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (seminit vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold seminit in Hnth.
  idtac "seminit_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 40%nat.
Qed. 

Lemma seminitbin_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    seminitbin vl <> ABORT -> 
    nth_error (get_all_succs (seminitbin vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (seminitbin vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold seminitbin in Hnth.
  idtac "seminitbin_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 40%nat.
Qed. 

Lemma semdestroy_nabt_spec_step_succs_preserve:
  forall sc n vl cd O cd' O' lau lau',
    semdestroy vl <> ABORT -> 
    nth_error (get_all_succs (semdestroy vl)) n = Some cd ->
    spec_step sc cd O lau cd' O' lau' ->
    List.In cd' (get_all_succs (semdestroy vl)) 
    \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof.
  introv Hnabt Hnth Hstep.
  unfold semdestroy in Hnth.
  idtac "semdestroy_succ_preserved".
  repeat des_vl_absprog Hstep.
  succ_solver 20%nat.
Qed. 

Lemma api_spec_step_succs_preserve:
  forall fid acode ft vl cd cd' O O' sc laust laust',
    api_spec' fid = Some (acode, ft) ->
    In cd (get_all_succs (acode vl)) ->
    spec_step sc cd O laust cd' O' laust' ->
    In cd' (get_all_succs (acode vl)) \/ (cd' = ABORT) \/ (exists vo, cd' = END vo).
Proof. 
  introv Hpu Hcd Hstep.
  unfold api_spec' in Hpu.
  lets Hnth: In_nth_error cd Hcd.
  destruct Hnth as (n & Hnth).
  simpl in Hpu.
  destruct (Zeq_bool sem_trywait fid) eqn: eq1;
    try destruct (Zeq_bool sem_wait fid) eqn: eq2;
    try destruct (Zeq_bool sem_timedwait fid) eqn: eq3; 
    try destruct (Zeq_bool sem_signal fid) eqn: eq4;
    try destruct (Zeq_bool sem_init fid) eqn: eq5;
    try destruct (Zeq_bool sem_init_bin fid) eqn: eq6; 
    try destruct (Zeq_bool sem_destroy fid) eqn: eq7; 
    try inverts Hpu;
    tryfalse;
    try rewrite <- Zeq_is_eq_bool in eq1;
    try rewrite <- Zeq_is_eq_bool in eq2;
    try rewrite <- Zeq_is_eq_bool in eq3;
    try rewrite <- Zeq_is_eq_bool in eq4;
    try rewrite <- Zeq_is_eq_bool in eq5;
    try rewrite <- Zeq_is_eq_bool in eq6;
    try rewrite <- Zeq_is_eq_bool in eq7; 
    unfold sem_trywait, sem_wait, sem_timedwait, sem_signal, 
    sem_init, sem_init_bin, sem_destroy in *; 
    subst;
    tryfalse.
  
  - casetac (semtrywait vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply semtrywait_nabt_spec_step_succs_preserve; eauto.

  - casetac (semwait vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply semwait_nabt_spec_step_succs_preserve; eauto.

  - casetac (semtimedwait vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply semtimedwait_nabt_spec_step_succs_preserve; eauto.

  - casetac (semsignal vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply semsignal_nabt_spec_step_succs_preserve; eauto.

  - casetac (seminit vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply seminit_nabt_spec_step_succs_preserve; eauto.

  - casetac (seminitbin vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply seminitbin_nabt_spec_step_succs_preserve; eauto.

  - casetac (semdestroy vl) spec_abort Ht Hf.
    +
      rewrite Ht in *.       
      simpl in Hcd.
      destruct Hcd; tryfalse.
      subst. inverts Hstep.
    +    
      eapply semdestroy_nabt_spec_step_succs_preserve; eauto.

Qed. 
