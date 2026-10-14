
Require Import FIFO_sys.
(* Require Import PIF_succs. *)
Require Import FIFO_spec.
Require Import log_language.
Require Import List.
Require Import log_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import FIFO_inv_and_init.

Open Scope nat_scope.
Require Import base_tac. 
Require Import Integers.

Require Import mq_succ_gen. 
Require Import fifo_tacs. 

Open Scope int_scope.

Require Import seplog_lemmas.
Require Import fifo_lemmas. 

Require Import protect. 
Require Import join_lib.

Require Import qpendacc_dt_lemmas. 

Ltac some_none_tac Hs :=
  match Hs with
    (pnil, ?hyp) => 
      match type of hyp with
        ?P /\ ?Q => let h1 := fresh "h" in let h2 := fresh "h" in destruct hyp as (h1 & h2); some_none_tac pnil
      | ?P \/ ?Q =>
          let h1 := fresh "h" in
          let h2 := fresh "h" in
          destruct hyp as [h1 | h2];
          [some_none_tac (pnil, h1) | some_none_tac (pnil, h2)]
      | Some _ = None => solve [false]
      (* | Some _ = Some _ => inverts hyp *)
      | _ => idtac
      end
  | pnil =>
      match goal with
        h: context [Some ?t1 = None] |- _ => some_none_tac (pnil, h)
      | h: context [Some ?t1 = Some ?t2] |- _ => some_none_tac (pnil, h) 
      | h: _ |- _ => idtac
      end
  end.
  
Ltac end_abt H tac := 
  match type of H with
    ?P /\ ?Q => let h1 := fresh in let h2 := fresh in destruct H as (h1 & h2); tac h1; tac h2
  | ?P \/ ?Q => let h1 := fresh in let h2 := fresh in destruct H as [h1 | h2]; [tac h1 | tac h2]
  | ABORT <> ABORT => solve [false]
  | ~exists vo, END ?vo_ = END vo => solve [false; apply H; eexists; eauto]
  end. 
       
Ltac end_abt_tac H := 
  match type of H with
    context [ABORT <> ABORT] => end_abt H end_abt_tac
  | context [~exists vo, END ?vo1 = END vo] => end_abt H end_abt_tac
  end.
       
Ltac symexe0 := 
  match goal with
    H: has_succ0 _ _ |- _ =>
      inverts H;
      try (
          match goal with
            H_: has_succ0 _ _ |- _ =>
              protect H_;
              try (match goal with
                     H__: spec_step _ _ _ _ _ |- _ => protect H__
                   end)
          end); symexe0
  | H: spec_step _ _ _ _ _ |- _ => inverts H; symexe0
  | H: ?r _ _ (_, _) |- _ => inverts H; simpljoin; tryfalse; some_none_tac pnil; symexe0
  | H: context[ABORT <> ABORT] |- _ => end_abt_tac H
  | H: context[~exists vo, END ?vo1 = END vo] |- _ => end_abt_tac H
  | H: Some _ = Some _ |- _ => inverts H; symexe0 
  | H: FIFO_ext ?O |- FIFO_ext ?O => solve[auto]
  | Hjo1: join ?O ?Of ?OO, Hjo2: join ?O ?Of ?OO' |- _ =>
      assert (OO = OO') by join auto; subst; symexe0 
  | H: _ |- _ => idtac
  end.

Ltac symexe :=
  match goal with
    H1: ProtectWrapper _, H2: ProtectWrapper _ |- _ =>
      unprotect H1; unprotect H2;
      symexe0
  | _ => symexe0
  end.


Lemma mqtimedrecv_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mqtimedreceive vl) cd ->
    FIFO_ext O ->
    spec_step sc cd O cd' O' -> 
    FIFO_ext O'.
Proof.
  introv Hhs Hgd Hsp. 
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto; fail).

  repeat symexe.

  Set Nested Proofs Allowed.      
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }     
  { eapply fifo_ext_qpend_get_no_pwl_succ_preserved; eauto. }  
  { fifo_ext_preserve_eq. }
  { eapply fifo_ext_qpend_expwl_before_sched_preserved; eauto. }
  { fifo_ext_preserve_eq. }
  { eapply fifo_ext_qpend_block_preserved; eauto. }       
  { eapply fifo_ext_qpend_to_preserved; eauto. } 
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. }
  { fifo_ext_preserve_eq. } 
  { eapply fifo_ext_qacc_succ_preserved; eauto. }
  { fifo_ext_preserve_eq. }
Qed.   
