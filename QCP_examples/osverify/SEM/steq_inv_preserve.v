
Require Import memory.
Require Import sem_language.
Require Import sem_init.
Require Import sem_invs.
Require Import sem_sys.
Require Import succ_gen.

Require Import join_lib.
Require Import seplog_lemmas.

Require Import sem_tacs. 
Require Import sem_lemmas.

Require Import math_auto.

Require Import assms.

Set Keyed Unification. 

Lemma steq_preserves_inv: 
  forall O O' lau lau' t (laump laump': LAuxStMod.map), 
    (get O abstcblsid = get O' abstcblsid /\
       get O absecblsid = get O' absecblsid /\
       get O gauxstid = get O' gauxstid /\
       get O atidlsid = get O' atidlsid /\ 
       lau = lau') -> 
    get laump t = Some lau ->
    laump' = set laump t lau' -> 
    dtinv O laump ->
    dtinv O' laump'.
Proof.
  introv Heq Hgl Hl' Hdti.  
  simpljoin.
  unfold dtinv in *.
  simpljoin.
  assert (Hseq: set laump t lau' = laump).
  { eapply get_set_same; eauto. }
  repeat rewrite Hseq. 
  l_rew21 (get O abstcblsid).
  l_rew21 (get O absecblsid). 
  l_rew21 (get O atidlsid).
  l_rew21 (get O gauxstid). 
  do 4 eexists.
  split; eauto.
  split; eauto. 
  split; eauto.
  split; eauto.
Qed.   
