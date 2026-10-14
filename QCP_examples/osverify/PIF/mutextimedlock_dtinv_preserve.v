
Require Import PIF_sys.
Require Import PIF_spec.
Require Import PIF_language.
Require Import PIF_Modules.
Require Import List.
Require Import PIF_opsem.
Require Import Coqlib.
Require Import Maps.
Require Import PIF_memory.
Require Import PIF_assertion.
Require Import init_and_inv_PIF.
Require Import inv_hold_init.
Open Scope nat_scope.
Require Import PIF_LibTactics.
Require Import Integers.
Require Import PIF_os_code_defs. 

Require Import PIF_os_ucos_h.
Require Import aux_lemmas.

Require Import mux_succ_gen. 
Require Import pif_lemmas. 
Require Import pif_tacs. 

Open Scope int_scope.

Require Import seplog_lemmas. 
Require Import int_auto.

Require Import protect. 
Require Import join_lib.

Require Import mutexlock_dt_lemmas.

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
      | exists _, _ => let x := fresh "x" in let h1 := fresh "h" in destruct hyp as (x & h1); some_none_tac (pnil, h1)
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
  | H: GOOD_DT ?O |- GOOD_DT ?O => solve[auto]
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
               
Lemma mutextimedlock_dtinv_preserve:
  forall sc vl cd O cd' O', 
    has_succ (mutextimedlock vl) cd ->
    NO_NEST_PENDING_O O ->
    GOOD_DT O ->
    spec_step sc cd O cd' O' -> 
    NO_NEST_PENDING_O O' ->
    GOOD_DT O'.
Proof.
  introv Hhs Hnn Hgd Hsp Hnn'.
  repeat des_vl.
  simpl in Hhs. destruct vl.
  2: { eapply abt_no_succ in Hhs; eauto. subst. inverts Hsp. }

  inverts Hhs.
  inverts Hsp; (auto).

  repeat symexe. 
  repeat symexe. 
  repeat symexe.

  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_muxpend_get_succ_preserved; eauto. } 
  { eapply good_dt_muxpend_blocklift_preserved; eauto. }
  { eapply good_dt_muxpend_blocknolift_preserved; eauto. }
  { eapply good_dt_muxpend_timeouterr_preserved; eauto. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }
  { eapply good_dt_muxpend_get_succ_preserved; eauto. }
  { eapply good_dt_muxpend_blocklift_preserved; eauto. }
  { eapply good_dt_muxpend_blocknolift_preserved; eauto. }
  { eapply good_dt_muxpend_timeouterr_preserved; eauto. }  
  { dt_presesrve_eq_impl O0 O. }
  { dt_presesrve_eq_impl O0 O. }

Qed. 
