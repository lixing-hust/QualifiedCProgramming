
Require Import base_tac.
Require Import memory.
Require Import sem_language.
Require Import sem_opsem.
Require Import sem_init.
Require Import sem_invs.

Require Import sem_tacs. 

Set Keyed Unification.

Lemma init_inv :
  forall pu T cst O laump, 
    init pu T cst O laump ->
    dtinv O laump. 
Proof.
   introv Hini.
   unfolds in Hini.
   unfolds.
   destruct Hini as (Hit & Hist).
   unfolds in Hist.
   destruct Hist as (Hics & Hits & Hiss & Higmp & Hilmp).
   unfolds in Hits.
   unfolds in Hiss.
   unfolds in Higmp.
   simpljoin.
   do 4 eexists.
   split; eauto.
   split; eauto.
   split; eauto.
   split; eauto. 
   splits.
   - (* atids_valid *)
     auto.
   - (* cond_pv1 *)
     unfolds.
     introv Hf.
     rewrite H4 in Hf.
     false.
   - (* cond_pv0 *)
     unfolds.
     introv Hf.
     rewrite H4 in Hf.
     false.
   - (* wait_progpt *)
     unfolds.
     introv Hf.
     rewrite H4 in Hf.
     false.
   - (* none_progpt *)
     unfold none_progpt.
     introv Hnex.
     introv Hf.
     unfolds in Hilmp.
     unfolds in Hit.
     destruct Hit as (Heqd & _).
     unfolds in Heqd.
     destruct Heqd as (tls & Hgtls & Haiff).
     l_rew21 (get O abstcblsid).
     match goal with
       H: context [atids_valid] |- _ =>
         destruct H as (_ & Hiff)
     end.
     eapply Hiff in Hf; eauto.
     assert (Hex: exists a, get tls t = Some a).
     {
       destruct (get tls t) eqn: E.
       eexists. eauto.
       false.
     }
     eapply Haiff in Hex; eauto.
     assert (Hnn: get T t <> None).
     {
       introv Hff. destruct Hex as (C& Hg).
       rewrite Hg in Hff. inverts Hff.
     }
     eapply Hilmp in Hnn; eauto.
     introv Hgso.
     rewrite Hnn in Hgso.
     inverts Hgso.
     
Qed. 


