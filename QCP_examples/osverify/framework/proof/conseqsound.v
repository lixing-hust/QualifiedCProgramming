Require Import sound_include.

Lemma conseq_rule_sound_aux : 
  forall p  sd  I r ri q q' li t,
    (q ==> q') ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hlostep Hinv Hjm1 Hjm2 Hlstop Hnabt.
  lets Hex : H Hfcall Hlostep Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.
  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto. 
  eapply H39; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H39; eauto.
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H38; [simp join; left;split; eauto | right; eauto]. 
 
  introv Hc Hdis Hinv Hdd Hnabt.
  lets Hsk : H2 Hc Hdis Hinv Hdd Hnabt.
  simp join.
  do 4 eexists; splits; eauto.
  
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H33; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H9 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H10 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt.
  lets Hex : H11 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H12 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin Hnabt.
  lets Hres: H13 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 8 eexists; splits; eauto. splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H14 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H15 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H16 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H17 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 9 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H18 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
(* new add mpax *)
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H19 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H20 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H21 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H22 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H23 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H24 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H25 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H26 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H27 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H28 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H29 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 
(* end of add *)
Qed.

Lemma conseq_rule_sound :
  forall Spec sd I r ri p' p q q' s li t, 
    (p' ==>  p) ->  (q ==> q') ->
    RuleSem Spec sd li I r ri p s q  t ->
    RuleSem  Spec sd li  I r ri p' s q' t.
Proof.
  introv Himp1 Himp2 Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets (Hsat1 & Hsat2) : Hsat.
  lets Hsatp : Himp1 Hsat1.
  assert ((o, O, aop) |= p /\ satp o O (CurLINV li t)) by (split; auto).  lets Hsim1 : Hsim  H. 
  eapply  conseq_rule_sound_aux; eauto.
Qed.


Lemma conseq_rule_r_sound_aux :
  forall p sd I r ri ri' q r' li t, 
    (
      forall v,  r v==> r' v
    ) ->
    ri ==> ri' ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri q t ->
      MethSimMod p sd C o aop O li I  r' ri' q t .
Proof.
  introv Himp1 Himp2.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hlostep Hinv Hjm1 Hjm2 Hlstop Hnabt.
  lets Hex : H Hfcall Hlostep Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.
  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H39; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H39; eauto.
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H38; [simp join; left;split; eauto | right; eauto]. 

  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H3 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  
  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H4 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.

  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H5 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.

  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H33; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H9 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H10 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt.
  lets Hex : H11 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H12 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt.
  lets Hres: H13 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 8 eexists; splits; eauto. splits; eauto.
  
   introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H14 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H15 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H16 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H17 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 9 eexists; splits; eauto.
  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H18 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
(* new add mpax *)
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H19 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H20 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H21 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H22 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H23 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H24 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H25 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H26 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H27 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H28 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H29 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 
(* end of add *)
Qed.

Lemma conseq_rule_r_sound : 
  forall  Spec sd I r r' ri ri' p q s li t, 
    (forall v,r v ==> r' v) ->
    ri ==> ri' ->
    RuleSem Spec sd  li I  r ri p s q  t->
    RuleSem  Spec sd li I  r' ri' p s q t.
Proof.
  introv Himp Himp' Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets Hsim1 : Hsim  Hsat. 
  eapply  conseq_rule_r_sound_aux; eauto.
Qed.


Lemma absconseq_rule_sound_aux : 
  forall p  sd I r ri q q' li t,
    (absimp' sd li q q' t) ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  introv Hfcall Hlostep Hinv Hjm1 Hjm2 Hlstop Hnabt.
  lets Hex : H Hfcall Hlostep Hinv Hjm1.  
  lets Hex' : Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt.
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H39; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H39; eauto.

  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H1 Hc  Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H38; [simp join; left;split; eauto | right; eauto]. 

  introv Hc Hdis Hinv Hdd Hnabt.
  lets Hsk : H2 Hc Hdis Hinv Hdd Hnabt.
  simp join.
  assert ((o, x1, x) |= lift q v/\  satp o x1 (CurLINV li t)) by (split;auto).
  lets Hss : Himp H35.
  lets Htt : Hss H31.
  simp join.
  lets Hspp : hmstepstar_trans H30 H37.  
  exists x4 x5 x3 x2.
  splits; eauto.
  
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H33; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H9 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H10 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt.
  lets Hex : H11 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  simp join.
  do 8 eexists; splits; eauto.
  introv Hc Hinv Hjm1 Hjm2 Hlostep Hnabt Hlenv Hmem Hget Hload.
  lets Hex : H12 Hc Hinv Hjm1. 
  lets Hex' : Hex Hjm2 Hlostep Hnabt.
  lets Hress : Hex' Hlenv Hmem Hget Hload.
  simp join.
  do 8 eexists; splits; eauto.
  
  introv Hc Hinv Hdisj Hjoin  Hnabt.
  lets Hres: H13 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 8 eexists; splits; eauto. splits; eauto.
  
   introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H14 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.

  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H15 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
  
  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  lets Hres: H16 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  lets Hres: H17 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 9 eexists; splits; eauto.

  introv Hc Hinv Hdisj Hjoin  Hnabt. 
  lets Hres: H18 Hc Hinv Hdisj Hjoin Hnabt.
  simp join.
  do 7 eexists; splits; eauto.
(* new add mpax *)
  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H19 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H20 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H21 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H22 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H23 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H24 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H25 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H26 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 11 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H27 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 10 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H28 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 

  introv Hc Hinv Hjm1 Hjm2 Hstep  Hnabt.
  lets Hres: H29 Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  simp join.
  do 8 eexists; splits; eauto. 
(* end of add *)
Qed.

Lemma abscsq_rule_sound :  
  forall   Spec sd I r ri p' p q q' s li t , 
    absinferfull sd li p' p t -> 
    absinferfull sd li q q' t ->
    RuleSem Spec sd  li I r ri p s q t  ->
    RuleSem  Spec sd  li I r ri p' s q' t.
Proof.
  introv  Himp1 Himp2 Hsim.
  apply absinfersound in Himp1.
  apply absinfersound in Himp2.
  apply absimp_eq_absimp' in Himp1.
  apply absimp_eq_absimp'  in Himp2.
  introv .
  unfold RuleSem in *.
  introv  Hsat.
  unfold absimp' in Himp1.
  lets Hsatt :  Himp1  Hsat.
  constructors; try auto.
  introv Hfcall Hlostep Hinv Hjm1 Hjm2 Hstep Hnabt.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm0 : H Hfcall Hlostep Hinv Hjm1 Hdsjj Hstep.
  lets Hsm : Hsm0 Hnex. clear Hsm0.
  simp join.
  lets Hks : hmstepstar_trans Hstar H30.
  exists x x0 x1 x2 x3 x4.  
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).  
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hress0 : H0 Hc Hmdisj Hinv Hdsjj.
  lets Hress: Hress0 Hnex. clear Hress0. 
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H30.
  do 12 eexists; 
    splits; eauto.
  splits; auto.
  introv Henv.  
  splits.
  eapply H39; eauto.
  introv Hvv Hvvv Hdss.
  eapply absconseq_rule_sound_aux ; eauto.
  eapply H39; eauto.

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hress : H1 Hc Hmdisj Hinv Hdsjj Hnex.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H31.  
  clear Hstar H27.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H38; [simp join; left;split; eauto | right; eauto]. 
 
  introv  Hs Hjmm Hswin.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }    
  lets Hsk : H2 Hc Hmdisj Hinv Hdsjj Hnex.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H30.  
  assert ((o, x1, x) |= lift q v /\ satp o x1 (CurLINV li t)) by (split; auto).
  lets Hds : Himp2 H39 H31.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstt  H41.  
  do 4 eexists; splits; eauto.

   introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.
   lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }  
  lets Hsk : H3 Hc Hmdisj Hinv Hdsjj Hnex; eauto.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H30.  
  do 4 eexists; splits; eauto.

  introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }    
  lets Hsk : H4 Hc Hmdisj Hinv Hdsjj Hnex; eauto.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H30.  
  do 4 eexists; splits; eauto.

  introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsk0 : H5 Hc Hmdisj Hinv Hdsjj; eauto.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.    
  }
  lets Hsk: Hsk0 Hnex.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H30.  
  do 4 eexists; splits; eauto.

  introv Hnot Hinv Hjon Hdisj Hjoin Hnabt.
  unfolds in Hdisj.
  destruct Hdisj as (OO0 & Hdisj).
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (disjoint O' Os) as Hds.
  unfolds.
  eauto.
  lets Hree0 : H6 Hnot Hinv Hjon Hds Hdsjj; eauto.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0.
    lets HOOeq: join_lib.join_unique Hdisj Hjoin.
    rewrite <- HOOeq in *.  
    eapply hmstepstar_trans; eauto.
  }
  lets Hree: Hree0 Hnex.
  eauto.  

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hress : H7 Hc Hmdisj Hinv Hdsjj Hnex.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H34.  
  eexists.
  exists x0 x1 x2.
  do 10 eexists; splits; eauto.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hress : H8 Hc Hmdisj Hinv Hdsjj Hnex.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H32.
  clear Hstar H11.
  eexists.
  exists x0 x1 x2.
  exists x3.
  splits; eauto.
  destruct H33; simp join.
  left.
  exists x x4 x5.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  right.
  exists x x4 x5.
  splits; eauto.
  introv Hs1 Hj1 Hj2.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm : H9 Hc Hinv Hjm1. 
  lets Hsm'0 : Hsm Hdsjj  Hstep.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm' : Hsm'0 Hnex. clear Hsm'0.  
  lets Hress : Hsm' Hlenv Hmem Hget Hload.
  simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm : H10 Hc Hinv Hjm1. 
  lets Hsm'0 : Hsm Hdsjj  Hstep.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.   
  lets Hress : Hsm' Hlenv Hmem Hget Hload.
  simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm : H11 Hc Hinv Hjm1. 
  lets Hsm'0 : Hsm Hdsjj  Hstep.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
  simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt Hlenv Hmem Hget Hload.
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm : H12 Hc Hinv Hjm1. 
  lets Hsm'0 : Hsm Hdsjj  Hstep.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
  lets Hress : Hsm' Hlenv Hmem Hget Hload.
  simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  
   introv Hc Hinv Hdisj Hjoin Hnabt.
   lets Hres: Hsatt Hjoin.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H13 Hc Hinv Hdisj.
  lets Hsm'0: Hsm Hdsjj.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H37.
  do 8 eexists; splits; eauto. splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  
    introv Hc Hinv Hdisj Hjoin Hnabt.
   lets Hres: Hsatt Hjoin.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H14 Hc Hinv Hdisj.
  lets Hsm'0: Hsm Hdsjj.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H34.
  do 7 eexists; splits; eauto. splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  
  introv Hc Hinv Hdisj Hjoin Hnabt.
   lets Hres: Hsatt Hjoin.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H15 Hc Hinv Hdisj.
  lets Hsm'0: Hsm Hdsjj.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H34.
  do 7 eexists; splits; eauto. splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  
  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H16 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 10 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H17 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 9 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hdisj Hjoin Hnabt.
   lets Hres: Hsatt Hjoin.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H18 Hc Hinv Hdisj.
  lets Hsm'0: Hsm Hdsjj.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H34.
  do 7 eexists; splits; eauto. splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
(* new add mpax *)
  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H19 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H20 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H21 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H22 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H23 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 10 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H24 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 10 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H25 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H26 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 11 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H27 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 10 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H28 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

  introv Hc Hinv Hjm1 Hjm2 Hstep Hnabt.
   lets Hres: Hsatt Hjm2.
   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
   lets Hsm : Hsim  Hsp.
  inverts Hsm.
  lets Hsm: H29 Hc Hinv Hjm1.
  lets Hsm'0: Hsm Hdsjj. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsm': Hsm'0 Hstep Hnex. clear Hsm'0.
   simp join.
  lets Hks : hmstepstar_trans Hstar H31.
  do 8 eexists; splits; eauto. 
  eapply absconseq_rule_sound_aux ; eauto.

Qed.
