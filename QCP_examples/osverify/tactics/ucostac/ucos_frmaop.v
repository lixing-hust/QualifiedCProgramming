Require Import include_frm.
Require Export frmaop_sol.
Require Import os_inv.
Require Import os_code_defs.
Require Import os_ucos_h.
Require Import code_notations.

Open Scope code_scope.

Lemma GoodFunAsrt_Aarray' :
  forall vl n t l, GoodFunAsrt (Aarray' l n t vl).
Proof.
  inductions vl; intros.
  destruct n; simpl; auto.
  destruct n; simpl; auto.
  destruct l.
  unfold GoodFunAsrt; fold GoodFunAsrt.
  split; simpl; auto.
Qed.

Lemma GoodFunAsrt_Aarray :
  forall l t vl, GoodFunAsrt(Aarray l t vl).
Proof.
  destruct t; simpl; auto.
  intros.
  apply GoodFunAsrt_Aarray'.
Qed.

Lemma good_frm_tcbdllseg : 
  forall vl head hp tail tn , 
    GoodFrm(tcbdllseg head hp tail tn vl).
Proof.
  intros.
  unfold tcbdllseg.
  apply good_frm_dllseg.
Qed.

Hint Resolve good_frm_tcbdllseg : good_frm_lemmas.

Lemma good_frm_AOSEventTbl : 
  forall x0 v0, GoodFrm (AOSEventTbl x0 v0).
Proof.
  intros.
  unfold AOSEventTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventTbl : good_frm_lemmas.

Lemma good_frm_node : 
  forall v vl t , GoodFrm (node v vl t).
Proof. 
  introv.
  unfold node.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_node : good_frm_lemmas.


Lemma good_frm_AOSEvent : 
  forall l a0 v x, GoodFrm  (AOSEvent l a0 v x).
Proof.
  intros.
  unfold AOSEvent.
  good_frm_sovler.
Qed. 

Hint Resolve  good_frm_AOSEvent : good_frm_lemmas.

Lemma good_frm_AOSQBlk : 
  forall x1 v2 x2, GoodFrm (AOSQBlk x1 v2 x2).
Proof.
  introv.
  unfold AOSQBlk.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQBlk : good_frm_lemmas.

Lemma good_frm_AOSQCtr :
  forall x1 v2, GoodFrm (AOSQCtr x1 v2).
Proof.
  introv.
  unfold AOSQCtr.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQCtr : good_frm_lemmas.

Lemma good_frm_AMsgData : 
  forall  x v1 x1 x2, GoodFrm ( AMsgData x v1 x1 x2).
Proof.
  intros.
  unfold AMsgData.
  good_frm_sovler.
Qed. 

Hint Resolve   good_frm_AMsgData : good_frm_lemmas.

Lemma good_frm_amsgnode : 
  forall p a  b c  v1 v2 v3 l, 
    GoodFrm (AEventNode p a b c (DMsgQ l v1 v2 v3)).
Proof.
  introv.
  unfold AEventNode.
  unfold AEventData.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_amsgnode : good_frm_lemmas.

Lemma good_frm_mqsllseg :
  forall p n l msgqls, GoodFrm (evsllseg p n l msgqls).
Proof.
  introv.
  gen l n p msgqls.
  inductions l; intros; simpl; good_frm_sovler; auto.
  destruct msgqls.
  simpl;auto.
  destruct a.
  good_frm_sovler.
  unfold AEventNode.
  good_frm_sovler.
  unfold AEventData.
  destruct e; destruct p0; good_frm_sovler.
Qed.

Hint Resolve good_frm_mqsllseg  : good_frm_lemmas.


Lemma good_frm_ecbfslleg : 
  forall ls x y ,
    GoodFrm (ecbf_sllseg x  y ls OS_EVENT V_OSEventListPtr).
Proof.
   inductions ls; intros.  
   simpl.   auto. 
   unfold ecbf_sllseg; fold ecbf_sllseg.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfslleg  : good_frm_lemmas.


Lemma good_frm_ecbfsll: forall ls x ,
                               GoodFrm (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.
   unfold ecbf_sll. 
    intros.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_ecbfsll  : good_frm_lemmas.

Lemma good_frm_AOSEventFreeList: 
  forall p x ,
    GoodFrm (AOSEventFreeList p x).
Proof.
  unfold AOSEventFreeList.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSEventFreeList : good_frm_lemmas.


Lemma  good_frm_qblkf_sllseg : 
  forall x y qblkl, GoodFrm (qblkf_sllseg x y qblkl OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  gen x y.
  inductions qblkl.
  intros.
  unfold qblkf_sllseg.
  good_frm_sovler.
  intros.
  unfold qblkf_sllseg.
  fold qblkf_sllseg.   
  good_frm_sovler.
Qed.


Hint Resolve  good_frm_qblkf_sllseg : good_frm_lemmas.

Lemma  good_frm_qblkf_sll : 
  forall x qblkl, GoodFrm (qblkf_sll x qblkl OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  unfold qblkf_sll.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_qblkf_sll : good_frm_lemmas.

Lemma good_frm_AOSQFreeList: forall x ,
                               GoodFrm (AOSQFreeList x ).
Proof.
  unfold AOSQFreeList.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQFreeList : good_frm_lemmas.

Lemma good_frm_AOSQFreeBlk : forall qblkl, GoodFrm (AOSQFreeBlk qblkl).
Proof.
  introv.
  unfold AOSQFreeBlk.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSQFreeBlk : good_frm_lemmas.


Lemma good_frm_EventList'  : forall  qptrl msgql,
                               GoodFrm ((EX p : val,
       GV OSEventList @ OS_EVENT∗ |-> p ** evsllseg p Vnull qptrl msgql)).
Proof.
  intros.  
   good_frm_sovler.
Qed.

Hint Resolve good_frm_EventList' : good_frm_lemmas.

Lemma good_frm_AMsgQList : forall qptrl msgql mqls tcbls,
                             GoodFrm (AECBList qptrl msgql mqls tcbls ).
Proof.
  introv.
  unfold AECBList.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AMsgQList : good_frm_lemmas.  

Lemma good_frm_AOSMapTbl : GoodFrm AOSMapTbl.
Proof. 
  unfold AOSMapTbl.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSMapTbl : good_frm_lemmas. 


Lemma good_frm_AOSUnMapTbl : GoodFrm AOSUnMapTbl.
Proof. 
  unfold AOSUnMapTbl.
  good_frm_sovler.  
Qed.

Hint Resolve good_frm_AOSUnMapTbl : good_frm_lemmas. 

Lemma good_frm_AOSTCBPrioTbl:  forall  ptbl rtbl tcbls ptls vhold,
                                GoodFrm (AOSTCBPrioTbl ptbl rtbl tcbls ptls vhold).
Proof.
  unfold AOSTCBPrioTbl.
  intros.
  good_frm_sovler.
Qed.


Hint Resolve good_frm_AOSTCBPrioTbl : good_frm_lemmas. 


Lemma good_frm_AOSIntNesting : GoodFrm (AOSIntNesting).
Proof.
  intros.
  unfold AOSIntNesting.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIntNesting : good_frm_lemmas. 

Lemma good_frm_AOSTime : forall t,GoodFrm (AOSTime t).
Proof.
  unfold AOSTime.
  intros;  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSTime : good_frm_lemmas. 

Lemma good_frm_AGVars : GoodFrm AGVars.
Proof.
  unfold AGVars.
  intros.
   good_frm_sovler.
Qed.


Hint Resolve good_frm_AGVars : good_frm_lemmas. 



Lemma good_frm_AOSTCBList: forall x1 x2 x3 x4 x5 x6 x7,
                             GoodFrm (AOSTCBList x1 x2 x3 x4 x5 x6 x7).
Proof.
  introv.
  unfold AOSTCBList.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBList  : good_frm_lemmas.

Lemma good_frm_tcbdllflsg : forall x1 x2, 
   GoodFrm (tcbdllflag x1 x2).
Proof.
  intros.
  gen x1.
  inductions x2.
  simpl; split; auto.
  intros.
  unfold tcbdllflag in *.
  simpl.
  intros; splits; auto.
Qed.

Hint Resolve   good_frm_tcbdllflsg   : good_frm_lemmas.

Lemma good_frm_AOSTCBList':
  forall x1 x2 x3 x4 x5 x6 x7 x8,
    GoodFrm (AOSTCBList' x1 x2 x3 x4 x5 x6 x7 x8).
Proof.
  introv.
  unfold AOSTCBList'.
  unfold GoodFrm.
  fold GoodFrm.
  split; intros.
  splits;  good_frm_sovler; auto.
  simpl; intros; splits; auto.
  good_frm_sovler.
  splits; good_frm_sovler; auto.
  unfold tcblist.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBList'  : good_frm_lemmas.


Lemma good_frm_sllfreeflag :
  forall x1 x2,
    GoodFrm (sllfreeflag x1 x2).
Proof.
  introv.
  unfold sllfreeflag.
  gen x1.
  inductions x2. 
  intros.
  simpl; auto.
  intros.
  simpl.
  intros;splits; auto.
Qed.

Hint Resolve  good_frm_sllfreeflag  : good_frm_lemmas.

Lemma good_frm_AOSTCBFreeList: forall x1 x2,
                             GoodFrm (AOSTCBFreeList x1 x2).
Proof.
  introv.
  unfold AOSTCBFreeList.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList  : good_frm_lemmas. 

Lemma good_frm_AOSTCBFreeList': 
  forall x1 x2 x3 x4,
    GoodFrm (AOSTCBFreeList' x1 x2 x3 x4).
Proof.
  introv.
  unfold AOSTCBFreeList'.
  good_frm_sovler.
  unfold GoodFrm. fold GoodFrm.
  splits.
  unfold TCBFree_Not_Eq.
  good_frm_sovler.
  unfold TCBFree_Eq.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSTCBFreeList'  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTbl : forall vl,  
                               GoodFrm (AOSRdyTbl vl).
Proof.
  intros.
  unfold AOSRdyTbl .
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTbl  : good_frm_lemmas. 


Lemma good_frm_AOSRdyGrp : forall vl,  
                               GoodFrm (AOSRdyGrp vl).
Proof.
  intros.
  unfold AOSRdyGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyGrp  : good_frm_lemmas. 

Lemma good_frm_AOSRdyTblGrp  : forall rtbl rgrp,  
                               GoodFrm (AOSRdyTblGrp rtbl rgrp).
Proof.
  intros.
  unfold   AOSRdyTblGrp .
 good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSRdyTblGrp  : good_frm_lemmas.

(* all modules' good frm lemmas  *)

Lemma good_frm_p_local:
forall ct lg,
  GoodFrm (p_local OSLInv ct lg).
Proof.
  intros.
  unfold p_local.
  unfold LINV,CurTid.
  unfold OSLInv.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_p_local : good_frm_lemmas.


(* good frm lemmas for EvtInv *)

Lemma good_frm_Aarray_new' :
forall n vll t l , GoodFrm (Aarray_new' l n t vll).
Proof.
induction n; induction vll; intros;
try good_frm_sovler.
clear -IHn.
destruct l.
destruct t;
simpl Aarray_new' in *;
destruct a; 
try good_frm_sovler;
destruct a;
try good_frm_sovler.
Qed.

Hint Resolve  good_frm_Aarray_new': good_frm_lemmas.  

Lemma good_frm_Aarray_new :
forall vll t l , GoodFrm (Aarray_new l t vll).
Proof.
intros.
unfold Aarray_new.
destruct t; try good_frm_sovler. 
Qed.

Hint Resolve  good_frm_Aarray_new: good_frm_lemmas.  

Lemma good_frm_ASeminfo :
  forall l infol,
    GoodFrm (ASeminfo l infol).
Proof.
  intros.
  unfold ASeminfo.
  unfold GoodFrm.
  fold GoodFrm.
  split; good_frm_sovler.
  split; good_frm_sovler.
  auto.
Qed.

Hint Resolve  good_frm_ASeminfo: good_frm_lemmas.

Lemma good_frm_AEvtCap:
  forall scapl l fieldname eibtype,
    GoodFrm (AEvtCap l scapl fieldname eibtype).
Proof.
  (* intros.
  unfold AEvtCap. *)
  induction scapl; (* induction l; *) intros.
  destruct l.
  simpl; auto.

  destruct l.
  unfold AEvtCap; fold AEvtCap.
  unfold GoodFrm.
  fold GoodFrm.
  split; good_frm_sovler.
  splits; auto.
Qed.

Hint Resolve  good_frm_AEvtCap: good_frm_lemmas.

Lemma good_frm_ASemCap:
  forall l scapl,
    GoodFrm (ASemCap l scapl).
Proof.
  intros.
  unfold ASemCap.
  good_frm_sovler.
Qed. 

Hint Resolve  good_frm_ASemCap: good_frm_lemmas.

Lemma good_frm_ASemEIBs :
  forall infol scapl embls ecbls vhold,
    GoodFrm (ASemEIBs infol scapl embls ecbls vhold ).  
Proof.
  intros.
  unfold ASemEIBs.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ASemEIBs: good_frm_lemmas. 

Lemma good_frm_APthreadMutex:
  forall l minfol,
    GoodFrm (APthreadMutex l minfol).
Proof.
  intros.
  unfold APthreadMutex.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_APthreadMutex : good_frm_lemmas.

Lemma good_frm_AMuxCap:
  forall l mcapl,
    GoodFrm (AMuxCap l mcapl).
Proof.
  intros.
  unfold AMuxCap.
  good_frm_sovler.
Qed. 

Hint Resolve good_frm_AMuxCap : good_frm_lemmas.

Lemma good_frm_AMuxEIBs :
  forall minfol mcapl minfob ecbls vhold,
    GoodFrm (AMuxEIBs minfol mcapl minfob ecbls vhold).
Proof.
  introv.
  unfold AMuxEIBs.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AMuxEIBs : good_frm_lemmas.  

Lemma good_frm_AMqAttr :
  forall l (qattrl :list vallist),
    GoodFrm (AMqAttr l qattrl).
Proof.
  intros.
  unfold AMqAttr.
  unfold GoodFrm.
  fold GoodFrm.
  split; good_frm_sovler.
  split; good_frm_sovler.
  auto.
Qed.

Hint Resolve  good_frm_AMqAttr: good_frm_lemmas.  

Lemma good_frm_AMqCap:
  forall l qcapl,
    GoodFrm (AMqCap l qcapl).
Proof.
  intros.
  unfold AMqCap.
  good_frm_sovler.
Qed. 

Hint Resolve good_frm_AMqCap: good_frm_lemmas.

Lemma good_frm_AMqEIBs :
  forall qattrl qcapl qattr ecbls vhold,
    GoodFrm (AMqEIBs qattrl qcapl qattr ecbls vhold).
Proof.
  intros.
  unfold AMqEIBs.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AMqEIBs: good_frm_lemmas. 

Lemma good_frm_pos_sllseg:
  forall vll hd tn pbls, GoodFrm (pos_sllseg hd tn vll pbls).
Proof.
  inductions vll; intros.
  unfold pos_sllseg. simpl; auto.
  unfold pos_sllseg. good_frm_sovler.
Qed.

Hint Resolve good_frm_pos_sllseg: good_frm_lemmas.

Lemma good_frm_APosblkList:
  forall pbls, GoodFrm (APosblkList pbls).
Proof.
  unfold APosblkList.
  intros.
  good_frm_sovler.
Qed.
    
Hint Resolve good_frm_APosblkList: good_frm_lemmas.

Lemma good_frm_evaux_node:
  forall a v1 v2 v3 v4,
    GoodFrm (evaux_node a v1 v2 v3 v4). 
Proof.
  intros. simpl. splits; auto.
Qed.

Hint Resolve good_frm_evaux_node: good_frm_lemmas. 

Lemma good_frm_llsegevaux:
  forall l hd tn locmp ptrmp nextf, 
    GoodFrm (llsegevaux hd tn l locmp ptrmp nextf).  
Proof.
  inductions l.
  intros. simpl. splits; auto.
  intros. simpl. intros. splits; auto. splits; auto.
Qed.

Hint Resolve good_frm_llsegevaux : good_frm_lemmas.

Lemma good_frm_tcbllsegevaux:
  forall tcbvl tcbh locmp ptrmp, 
    GoodFrm (tcbllsegevaux tcbh tcbvl locmp ptrmp).  
Proof.
  intros.
  unfold tcbllsegevaux. apply good_frm_llsegevaux.
Qed.

Hint Resolve good_frm_tcbllsegevaux: good_frm_lemmas.

Lemma good_frm_AEvAtomHeap : forall x,
                             GoodFrm (AEvAtomHeap x).
Proof.
  introv.
  inductions x.
  simpl; auto.
  unfold AEvAtomHeap.
  destruct a. destruct p. destruct t; simpl; auto.
Qed.

Hint Resolve good_frm_AEvAtomHeap: good_frm_lemmas.

Lemma good_frm_AEvStructHeap : forall x,
                             GoodFrm (AEvStructHeap x).
Proof.
  introv.
  inductions x.
  simpl; auto.
  unfold AEvStructHeap.
  destruct a. destruct p. destruct t; simpl; auto.
  splits; eauto.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AEvStructHeap: good_frm_lemmas.

Lemma good_frm_AEvArrayHeap : forall x,
                             GoodFrm (AEvArrayHeap x).
Proof.
  introv.
  inductions x.
  simpl; auto.
  unfold AEvArrayHeap.
  destruct a. destruct p.
  simpl; auto.
  splits; eauto.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AEvArrayHeap: good_frm_lemmas.

Lemma good_frm_err_sllseg :
 forall vll p t ebls, GoodFrm (err_sllseg p t vll ebls).
Proof.
  inductions vll.
  simpl; auto.
  simpl err_sllseg.
  unfold GoodFrm; fold GoodFrm.
  intros; splits; auto.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_err_sllseg: good_frm_lemmas.

Lemma good_frm_AErrblkList : forall x,
                             GoodFrm (AErrblkList x).
Proof.
  introv.
  inductions x.
  simpl; auto.
  intros; splits; auto.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AErrblkList: good_frm_lemmas.

Lemma good_frm_EvtInv:
  forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl,
    GoodFrm (EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl).
Proof.
  intros.
  unfold EvtInv.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_EvtInv  : good_frm_lemmas.

(* end of good frm lemmas for EvtInv *)

Lemma good_frm_IntInv : GoodFrm IntInv.
Proof.
  unfold IntInv.
  unfold AOSInthandler.
  unfold AOSInthandlerParam.
  unfold AOSExchandler.
  good_frm_sovler.
Qed.  

Hint Resolve good_frm_IntInv : good_frm_lemmas.

(* add by SJTU *)
Lemma good_frm_AOScoreheapl: 
forall vl, GoodFrm (AOScoreheapl vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. good_frm_sovler.
Qed.

Hint Resolve good_frm_AOScoreheapl : good_frm_lemmas.

Lemma good_frm_AOScoreheape: 
forall vl, GoodFrm (AOScoreheape vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. good_frm_sovler.
Qed.

Hint Resolve good_frm_AOScoreheape : good_frm_lemmas.

Lemma good_frm_AOScoreheapt: 
forall vl, GoodFrm (AOScoreheapt vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. good_frm_sovler.
Qed.

Hint Resolve good_frm_AOScoreheapt : good_frm_lemmas.



Lemma good_frm_AOSClkRate: 
forall v, GoodFrm (AOSClkRate v).
Proof.
  unfold AOSClkRate. intros. good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSClkRate : good_frm_lemmas.

Theorem good_frm_AOSTMRNode:
 forall n v , GoodFrm (AOSTMRNode n v).
 Proof.
  intros. unfold AOSTMRNode.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSTMRNode : good_frm_lemmas.
Theorem good_frm_AOSTMRList':
 forall v, GoodFrm (AOSTMRList' v).
Proof.
  intros. unfold AOSTMRList'.
  repeat (apply good_frm_ex;intros).
  good_frm_sovler.
  all: apply good_frm_AOSTMRNode.
Qed.

Hint Resolve good_frm_AOSTMRList' : good_frm_lemmas.

Theorem good_frm_AOSTMRIDUsed:
 forall v, GoodFrm (AOSTMRIDUsed v).
Proof.
  intros. unfold AOSTMRIDUsed.
  good_frm_sovler.
  Qed.

Hint Resolve good_frm_AOSTMRIDUsed : good_frm_lemmas.

Theorem good_frm_AOSTMRList_TMRused:
 forall systmrl utmrl tmrusedl tmrls, GoodFrm (AOSTMRList_TMRused systmrl utmrl tmrusedl tmrls).
Proof.
  intros. unfold AOSTMRList_TMRused,AOSTMRIDUsed.
  good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSTMRList_TMRused : good_frm_lemmas.


(* Theorem good_frm_timerregVar:
GoodFrm (timerregVar ).
Proof.
  intros. unfold timerregVar.
  good_frm_sovler.
Qed. 

Hint Resolve good_frm_timerregVar : good_frm_lemmas. *)

Theorem good_frm_AOSIPCSem:
forall vl,
GoodFrm (AOSIPCSem vl).
Proof.
induction vl;intros.
- cbn;auto.
- destruct a; unfold AOSIPCSem; good_frm_sovler.
Qed. 

Hint Resolve good_frm_AOSIPCSem : good_frm_lemmas.

Theorem good_frm_AOSIPCSendSem:
forall vl,
GoodFrm (AOSIPCSendSem vl).
Proof.
induction vl;intros.
- cbn;auto.
- destruct a; unfold AOSIPCSendSem; good_frm_sovler.
Qed. 

Hint Resolve good_frm_AOSIPCSendSem : good_frm_lemmas.

Theorem good_frm_AOSIPCSemShared:
forall l,
GoodFrm (AOSIPCSemShared l).
Proof.
unfold AOSIPCSemShared;intros;good_frm_sovler.
Qed. 

Hint Resolve good_frm_AOSIPCSemShared : good_frm_lemmas.

Theorem good_frm_Memory_sigcore_aux:
 forall vl p n, GoodFrm (Memory_sigcore_aux n p vl).
Proof.
  induction vl;intros.
  - cbn;auto.
  - cbn. splits;auto. split;auto. good_frm_sovler.
Qed.

Hint Resolve good_frm_Memory_sigcore_aux : good_frm_lemmas.

Theorem  good_frm_AOSIPCMem_aux: 
  forall pl memlls, GoodFrm (AOSIPCMem_aux pl memlls).
Proof.
  induction pl;intros;destruct memlls;cbn;auto.
  - destruct a;cbn;auto.
  - destruct a;try (cbn;auto).
    splits;auto. splits;auto.
    good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIPCMem_aux : good_frm_lemmas.

Theorem  good_frm_AOSIPCMem: 
  forall pl memlls, GoodFrm (AOSIPCMem pl memlls).
Proof.
  intros;unfold AOSIPCMem.
  good_frm_sovler. 
Qed.

Hint Resolve good_frm_AOSIPCMem: good_frm_lemmas.

Theorem  good_frm_AOSIPCinfo: 
  forall m, GoodFrm (AOSIPCGRinfo m).
Proof.
  intros;unfold AOSIPCGRinfo;good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIPCinfo: good_frm_lemmas.

Theorem  good_frm_AOSIPCBroadList:
 forall vl bl, GoodFrm (AOSIPCBroadList vl bl).
Proof.
  intros; unfold AOSIPCBroadList;good_frm_sovler.
Qed.

Hint Resolve good_frm_AOSIPCBroadList: good_frm_lemmas.



Lemma good_frm_PhdrSingle: forall v1 v2 v3 v4 p,
 GoodFrm (PhdrSingle p v1 v2 v3 v4).
Proof.
  intros. simpl. intros.
  repeat (split; try tauto).
  destruct v2; good_frm_sovler.
  destruct v4; good_frm_sovler.
  destruct v4; good_frm_sovler.
  destruct v3; good_frm_sovler.
Qed.

Hint Resolve   good_frm_PhdrSingle: good_frm_lemmas.

Lemma good_frm_PhdrArray: forall v1 v2 v3 v4 p1 p2,
 GoodFrm (PhdrArray p1 p2 v1 v2 v3 v4).
Proof.
  induction v1; intros.
  + destruct v2; destruct v3; destruct v4; good_frm_sovler.
  + simpl. 
      destruct v2; good_frm_sovler.
      destruct v3; good_frm_sovler.
      destruct v4; good_frm_sovler.
      destruct a; good_frm_sovler.
      destruct p2; good_frm_sovler.
      do 8 (destruct a; good_frm_sovler).
Qed.

Hint Resolve   good_frm_PhdrArray: good_frm_lemmas.

Lemma good_frm_AdynrefaccfgFreeList: forall v1 v2,
 GoodFrm (AdynrefaccfgFreeList v1 v2).
Proof.
  intros. unfold AdynrefaccfgFreeList.
  repeat (split; try tauto).
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AdynrefaccfgFreeList: good_frm_lemmas.

Lemma good_frm_Adynheap: forall v,
  GoodFrm (Adynheap v).
Proof.
  induction v; good_frm_sovler.
  unfold Adynheap. fold Adynheap.
  destruct a. good_frm_sovler.
Qed.

Hint Resolve good_frm_Adynheap: good_frm_lemmas.

(* add end by SJTU *)
Lemma good_frm_TmrInv': GoodFrm TmrInv'.
Proof. unfold TmrInv'. good_frm_sovler. Qed.
Hint Resolve good_frm_TmrInv'  : good_frm_lemmas.

Lemma good_frm_HeapInv': GoodFrm HeapInv'.
Proof. unfold HeapInv'. good_frm_sovler. Qed.
Hint Resolve good_frm_HeapInv'  : good_frm_lemmas.

Lemma goof_frm_DynamicRefactorINV: forall vl, GoodFrm (DynamicRefactorINV vl).
Proof. intros. unfold DynamicRefactorINV. good_frm_sovler. Qed.
Hint Resolve goof_frm_DynamicRefactorINV  : good_frm_lemmas.

Lemma good_frm_TmrInv: GoodFrm TmrInv.
Proof. unfold TmrInv. good_frm_sovler. Qed.
Hint Resolve good_frm_TmrInv  : good_frm_lemmas.

Lemma good_frm_CoreCommuInv: forall vl, GoodFrm (CoreCommuInv vl).
Proof. intros;unfold CoreCommuInv. good_frm_sovler. Qed.
Hint Resolve good_frm_CoreCommuInv  : good_frm_lemmas.

Lemma good_frm_APortStruct: forall v u, GoodFrm (APortStruct u v).
Proof.
  intros.
  unfold APortStruct.
  good_frm_sovler.
Qed.
Hint Resolve good_frm_APortStruct  : good_frm_lemmas.

Lemma good_frm_dmportp_sllseg_sampleport_msg: forall l v, GoodFrm (dmportp_sllseg_sampleport_msg v l).
Proof.
  intros. unfold dmportp_sllseg_sampleport_msg. good_frm_sovler.
Qed.
Hint Resolve good_frm_dmportp_sllseg_sampleport_msg  : good_frm_lemmas.

Lemma good_frm_dmportp_sllseg_qport_msg: forall v5 v0 v1 v2 v3 v4, GoodFrm (dmportp_sllseg_qport_msg v0 v1 v2 v3 v4 v5).
Proof.
  induction v5; destruct v4; intros.
  { good_frm_sovler. }
  { good_frm_sovler. }
  { good_frm_sovler. }
  cbn [dmportp_sllseg_qport_msg].
  good_frm_sovler.
Qed.
Hint Resolve good_frm_dmportp_sllseg_qport_msg  : good_frm_lemmas.

Lemma good_frm_dmportp_sllseg: forall l0 l1 u v, GoodFrm (dmportp_sllseg u v l0 l1 OS_Port_V_nextPort).
Proof.
  induction l0; destruct l1; intros.
  { good_frm_sovler. }
  { good_frm_sovler. }
  { good_frm_sovler. }
  cbn [dmportp_sllseg].
  good_frm_sovler.
  simpl. split.
  { split; auto.
    intros. split; auto.
    split; auto.
    intros. split; auto.
    destruct x2; destruct x3; good_frm_sovler; simpl.
    { split; auto; repeat (destruct x3; good_frm_sovler). }
    { repeat (simpl; split; auto; destruct x2; good_frm_sovler). }
    { repeat (simpl; split; auto; destruct x2; good_frm_sovler);
      simpl; split; auto; repeat (destruct x3; good_frm_sovler). } }
  intros.
  repeat (splits; auto); good_frm_sovler.
Qed.
Hint Resolve good_frm_dmportp_sllseg  : good_frm_lemmas.

Lemma good_frm_dmportp_sll: forall v0 v1 v, GoodFrm (dmportp_sll v v0 v1 OS_Port_V_nextPort).
Proof.
  unfold dmportp_sll.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_dmportp_sll  : good_frm_lemmas.

Lemma good_frm_AOSDomainPortPtrList: forall v v0 v1, GoodFrm (AOSDomainPortPtrList v v0 v1).
Proof.
  unfold AOSDomainPortPtrList.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSDomainPortPtrList  : good_frm_lemmas.

Lemma good_frm_kportNode_P: forall v v0, GoodFrm (kportNode_P v v0).
Proof.
  induction v; destruct v0; intros.
  { good_frm_sovler. }
  { good_frm_sovler. }
  { good_frm_sovler. }
  cbn [kportNode_P]. good_frm_sovler.
  simpl. split; auto.
  intros; split; auto.
  destruct v0; good_frm_sovler.
  destruct v2; good_frm_sovler.
  destruct v3; good_frm_sovler.
  destruct v4; good_frm_sovler.
  destruct v5; good_frm_sovler.
  destruct v6; good_frm_sovler.
Qed.
Hint Resolve good_frm_kportNode_P  : good_frm_lemmas.

Lemma good_frm_AOSKernelPortIDTbl: forall v v0, GoodFrm (AOSKernelPortIDTbl v v0).
Proof.
  unfold AOSKernelPortIDTbl.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSKernelPortIDTbl  : good_frm_lemmas.

Lemma good_frm_Channel_dstkport_get: forall l u v w, GoodFrm (Channel_dstkport_get u v w l).
Proof.
  induction l; destruct w; intros; good_frm_sovler.
  cbn [Channel_dstkport_get]. good_frm_sovler.
Qed.
Hint Resolve good_frm_Channel_dstkport_get  : good_frm_lemmas.

Lemma good_frm_ChannelNode: forall v v0 v1, GoodFrm (ChannelNode v v0 v1).
Proof.
  induction v; induction v0; destruct v1; intros; good_frm_sovler.
  cbn [ChannelNode]. good_frm_sovler.
  simpl. split; auto. split.
  { intros. split; auto.
    repeat (destruct a0; good_frm_sovler). }
  intros. splits; auto. good_frm_sovler.
Qed.
Hint Resolve good_frm_ChannelNode  : good_frm_lemmas.

Lemma good_frm_AOSChannelIDTbl: forall v v0 v1, GoodFrm (AOSChannelIDTbl v v0 v1).
Proof.
  unfold AOSChannelIDTbl.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSChannelIDTbl  : good_frm_lemmas.

Lemma good_frm_kportf_sllseg: forall l u v, GoodFrm (kportf_sllseg u v l OS_K_Port OS_K_Port_V_OSEventPtr).
Proof.
  induction l; intros; good_frm_sovler.
  cbn [kportf_sllseg]. good_frm_sovler.
Qed.
Hint Resolve good_frm_kportf_sllseg  : good_frm_lemmas.

Lemma good_frm_kportf_sll: forall v v0, GoodFrm (kportf_sll v v0 OS_K_Port OS_K_Port_V_OSEventPtr).
Proof.
  unfold kportf_sll.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_kportf_sll  : good_frm_lemmas.

Lemma good_frm_AOSKernelPortFreeList: forall v v0, GoodFrm (AOSKernelPortFreeList v v0).
Proof.
  unfold AOSKernelPortFreeList.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSKernelPortFreeList  : good_frm_lemmas.

Lemma good_frm_channelf_sllseg: forall l u v, GoodFrm (channelf_sllseg u v l OS_Channel OS_Channel_V_OSEventPtr).
Proof.
  induction l; intros; good_frm_sovler.
  cbn [channelf_sllseg]. good_frm_sovler.
Qed.
Hint Resolve good_frm_channelf_sllseg  : good_frm_lemmas.

Lemma good_frm_channelf_sll: forall v v0, GoodFrm (channelf_sll v v0 OS_Channel OS_Channel_V_OSEventPtr).
Proof.
  unfold channelf_sll.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_channelf_sll  : good_frm_lemmas.

Lemma good_frm_AOSChannelFreeList: forall v v0, GoodFrm (AOSChannelFreeList v v0).
Proof.
  unfold AOSChannelFreeList.
  intros. good_frm_sovler.
Qed.
Hint Resolve good_frm_AOSChannelFreeList  : good_frm_lemmas.

Lemma good_frm_OtherPortPtrList: forall l l0 l1, GoodFrm (OtherPortPtrList l l0 l1).
Proof.
  induction l; induction l0; destruct l1; intros; good_frm_sovler.
  cbn [OtherPortPtrList]. good_frm_sovler.
  simpl. split.
  { split; auto.
    intros. repeat (split; auto).
    destruct x0; destruct x1; good_frm_sovler; simpl.
    { split; auto; repeat (destruct x1; good_frm_sovler). }
    { repeat (simpl; split; auto; destruct x0; good_frm_sovler). }
    { repeat (simpl; split; auto; destruct x0; good_frm_sovler);
      simpl; split; auto; repeat (destruct x1; good_frm_sovler). } }
  intros.
  repeat (splits; auto); good_frm_sovler.
Qed.
Hint Resolve good_frm_OtherPortPtrList  : good_frm_lemmas.

Lemma good_frm_AOSCorePortPtrList: forall l l0 l1, GoodFrm (AOSCorePortPtrList l l0 l1).
Proof.
  unfold AOSCorePortPtrList; intros. good_frm_sovler. Qed.
Hint Resolve good_frm_AOSCorePortPtrList  : good_frm_lemmas.

(* add by CNU *)

Lemma good_frm_AIntrDomainMux :
  forall l vl abs,
    GoodFrm (AIntrDomainMux l vl abs).
Proof.
  intros.
  unfold AIntrDomainMux.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AIntrDomainMux: good_frm_lemmas. 

Lemma good_frm_node_offt :
  forall l vl t,
    GoodFrm (node_offt l vl t).
Proof.
  intros.
  unfold node_offt.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_node_offt: good_frm_lemmas. 

Lemma good_frm_AAllArea :
  forall l vl abs,
    GoodFrm (AAllArea l vl abs).
Proof.
  intros.
  unfold AAllArea.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AAllArea: good_frm_lemmas.

Lemma good_frm_AksDomSchedule' :
  forall vl l,
    GoodFrm (AksDomSchedule' l vl).
Proof.
  induction vl.
  intros.
  unfold AksDomSchedule'.
  good_frm_sovler.
  intros.
  unfolds AksDomSchedule'; fold AksDomSchedule'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AksDomSchedule': good_frm_lemmas.

Lemma good_frm_ADeviceioTbl' :
  forall vl l,
    GoodFrm (ADeviceioTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold ADeviceioTbl'.
  good_frm_sovler.
  intros.
  unfolds ADeviceioTbl'; fold ADeviceioTbl'.
  destruct a as [].
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ADeviceioTbl': good_frm_lemmas.

Lemma good_frm_AksDomains' :
  forall vl l,
    GoodFrm (AksDomains' l vl).
Proof.
  induction vl.
  intros.
  unfold AksDomains'.
  good_frm_sovler.
  intros.
  unfolds AksDomains'; fold AksDomains'.
  destruct a as [[[]]].
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AksDomains': good_frm_lemmas.

Lemma good_frm_Acpus' :
  forall vl l, 
    GoodFrm (Acpus' l vl).
Proof.
  induction vl.
  intros.
  unfold Acpus'.
  good_frm_sovler.
  intros.
  unfolds Acpus'; fold Acpus'.
  destruct a as [[[]]].
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Acpus': good_frm_lemmas.

Lemma good_frm_ACPUs :
  forall l vl abs,
    GoodFrm (ACPUs l vl abs).
Proof.
  intros.
  unfold ACPUs.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ACPUs: good_frm_lemmas.

Lemma good_frm_AchannelTbl' :
  forall vl l, 
    GoodFrm (AchannelTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold AchannelTbl'.
  good_frm_sovler.
  intros.
  unfolds AchannelTbl'; fold AchannelTbl'.
  destruct a as [].
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AchannelTbl': good_frm_lemmas.

Lemma good_frm_AChannelTbl :
  forall l vl abs,
    GoodFrm (AChannelTbl l vl abs).
Proof.
  intros.
  unfold AChannelTbl.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AChannelTbl: good_frm_lemmas.

Lemma good_frm_AportTbl' :
  forall vl l, 
    GoodFrm (AportTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold AportTbl'.
  good_frm_sovler.
  intros.
  unfolds AportTbl'; fold AportTbl'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AportTbl': good_frm_lemmas.

Lemma good_frm_APortTbl :
  forall l vl abs,
    GoodFrm (APortTbl l vl abs).
Proof.
  intros.
  unfold APortTbl.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_APortTbl: good_frm_lemmas.

Lemma good_frm_AucosConf :
  forall l abs,
    GoodFrm (AucosConf l abs).
Proof.
  intros.
  unfold AucosConf.
  destruct l as [[[[[[]]]]]].
  destruct abs as [[[[[[[[[[[[[]]]]]]]]]]]]].
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AucosConf: good_frm_lemmas. 

Lemma good_frm_Adomain2index' :
  forall l, 
    GoodFrm (Adomain2index' l).
Proof.
  induction l.
  intros.
  unfold Adomain2index'.
  good_frm_sovler.
  intros.
  unfolds Adomain2index'; fold Adomain2index'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Adomain2index': good_frm_lemmas.

Lemma good_frm_Adomain2index :
  forall l abs,
    GoodFrm (Adomain2index l abs).
Proof.
  intros.
  unfold Adomain2index.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Adomain2index: good_frm_lemmas. 

Lemma good_frm_AKsDSchdidx :
  forall abs,
    GoodFrm (AKsDSchdidx abs).
Proof.
  intros.
  unfold AKsDSchdidx.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDSchdidx: good_frm_lemmas. 

Lemma good_frm_AKsDSchdlen :
  forall abs,
    GoodFrm (AKsDSchdlen abs).
Proof.
  intros.
  unfold AKsDSchdlen.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDSchdlen: good_frm_lemmas. 

Lemma good_frm_AKsCurDomain :
  forall abs,
    GoodFrm (AKsCurDomain abs).
Proof.
  intros.
  unfold AKsCurDomain.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsCurDomain: good_frm_lemmas. 

Lemma good_frm_AKsLastDomain :
  forall abs,
    GoodFrm (AKsLastDomain abs).
Proof.
  intros.
  unfold AKsLastDomain.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsLastDomain: good_frm_lemmas.

Lemma good_frm_AKsDomainTime :
  forall abs,
    GoodFrm (AKsDomainTime abs).
Proof.
  intros.
  unfold AKsDomainTime.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDomainTime: good_frm_lemmas.

Lemma good_frm_AKsDomSchedule' :
  forall l, 
    GoodFrm (AKsDomSchedule' l).
Proof.
  induction l.
  intros.
  unfold AKsDomSchedule'.
  good_frm_sovler.
  intros.
  unfolds AKsDomSchedule'; fold AKsDomSchedule'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDomSchedule': good_frm_lemmas.

Lemma good_frm_AKsDomSchedule :
  forall l abs,
    GoodFrm (AKsDomSchedule l abs).
Proof.
  intros.
  unfold AKsDomSchedule.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDomSchedule: good_frm_lemmas.

Lemma good_frm_AisChangePartion :
  forall v,
    GoodFrm (AisChangePartion v).
Proof.
  intros.
  unfold AisChangePartion.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AisChangePartion: good_frm_lemmas.

Lemma good_frm_AIntPartMux' :
  forall l, 
    GoodFrm (AIntPartMux' l).
Proof.
  induction l.
  intros.
  unfold AIntPartMux'.
  good_frm_sovler.
  intros.
  unfolds AIntPartMux'; fold AIntPartMux'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AIntPartMux': good_frm_lemmas.

Lemma good_frm_AIntPartMux :
  forall l abs,
    GoodFrm (AIntPartMux l abs).
Proof.
  intros.
  unfold AIntPartMux.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AIntPartMux: good_frm_lemmas.

Lemma good_frm_Asms_mpaxinfo :
  forall vl,
    GoodFrm (Asms_mpaxinfo vl).
Proof.
  intros.
  unfold Asms_mpaxinfo.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Asms_mpaxinfo: good_frm_lemmas.

Lemma good_frm_ASMSMpax :
  forall vl abs,
    GoodFrm (ASMSMpax vl abs).
Proof.
  intros.
  unfold ASMSMpax.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ASMSMpax: good_frm_lemmas.

Lemma good_frm_Ases_mpaxinfo :
  forall vl,
    GoodFrm (Ases_mpaxinfo vl).
Proof.
  intros.
  unfold Ases_mpaxinfo.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Ases_mpaxinfo: good_frm_lemmas.

Lemma good_frm_ASESMpax :
  forall vl abs,
    GoodFrm (ASESMpax vl abs).
Proof.
  intros.
  unfold ASESMpax.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ASESMpax: good_frm_lemmas.

Lemma good_frm_Axmpaxinfo :
  forall vl,
    GoodFrm (Axmpaxinfo vl).
Proof.
  intros.
  unfold Axmpaxinfo.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_Axmpaxinfo: good_frm_lemmas.

Lemma good_frm_AXMpax :
  forall vl abs,
    GoodFrm (AXMpax vl abs).
Proof.
  intros.
  unfold AXMpax.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AXMpax: good_frm_lemmas.

Lemma good_frm_AMPAXs :
    GoodFrm (AMPAXs).
Proof.
  intros.
  unfold AMPAXs.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AMPAXs: good_frm_lemmas.

Lemma good_frm_AXMPFR :
    GoodFrm (AXMPFR).
Proof.
  intros.
  unfold AXMPFR.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AXMPFR: good_frm_lemmas.

Lemma good_frm_AMDMAER :
    GoodFrm (AMDMAER).
Proof.
  intros.
  unfold AMDMAER.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AMDMAER: good_frm_lemmas.

Lemma good_frm_AKsDomains' :
  forall vl l,  GoodFrm (AKsDomains' l vl).
Proof.
  induction vl.
  simpl; auto.
  destruct a.
  unfold AKsDomains'; fold AKsDomains'.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDomains': good_frm_lemmas.

Lemma good_frm_AKsDomains :
  forall vl abs,  GoodFrm (AKsDomains vl abs).
Proof.
  intros.
  unfold AKsDomains.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AKsDomains: good_frm_lemmas.

Lemma good_frm_AisCoreBoot :
  forall v,  GoodFrm (AisCoreBoot v).
Proof.
  intros.
  unfold AisCoreBoot.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AisCoreBoot: good_frm_lemmas.

Lemma good_frm_AsystemStck' :
  forall vl,  GoodFrm (AsystemStck' vl).
Proof.
  intros.
  unfold AsystemStck'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AsystemStck': good_frm_lemmas.

Lemma good_frm_AOSSystemSP :
  forall v,  GoodFrm (AOSSystemSP v).
Proof.
  intros.
  unfold AOSSystemSP.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSSystemSP: good_frm_lemmas.

Lemma good_frm_ACorepartnum' :
  forall v,  GoodFrm (ACorepartnum' v).
Proof.
  intros.
  unfold ACorepartnum'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ACorepartnum': good_frm_lemmas.

Lemma good_frm_ACorepartnum :
  forall v,  GoodFrm (ACorepartnum v).
Proof.
  intros.
  unfold ACorepartnum.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ACorepartnum: good_frm_lemmas.

Lemma good_frm_APortnumcur :
  GoodFrm (APortnumcur).
Proof.
  intros.
  unfold APortnumcur.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_APortnumcur: good_frm_lemmas.

Lemma good_frm_APartArea' :
  forall vl,  GoodFrm (APartArea' vl).
Proof.
  unfold APartArea'.
  intros.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_APartArea': good_frm_lemmas.

Lemma good_frm_APartArea :
  forall vl abs,  GoodFrm (APartArea vl abs).
Proof.
  intros.
  unfold APartArea.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_APartArea: good_frm_lemmas.

Lemma good_frm_APartID2Dom :
  forall vl,  GoodFrm (APartID2Dom vl).
Proof.
  intros.
  unfold APartID2Dom.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_APartID2Dom: good_frm_lemmas.

Lemma good_frm_ARootTaskStk' :
  forall vl,  GoodFrm (ARootTaskStk' vl).
Proof.
  intros.
  unfold ARootTaskStk'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ARootTaskStk': good_frm_lemmas.

Lemma good_frm_ARootTaskStk :
  forall vl abs,  GoodFrm (ARootTaskStk vl abs).
Proof.
  intros.
  unfold ARootTaskStk.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_ARootTaskStk: good_frm_lemmas.

Lemma good_frm_AOSPortAttrTbl' :
  forall vl,  GoodFrm (AOSPortAttrTbl' vl).
Proof.
  intros.
  unfold AOSPortAttrTbl'.
  good_frm_sovler.
Qed.

Hint Resolve  good_frm_AOSPortAttrTbl': good_frm_lemmas.

(* end add by CNU *)

Lemma good_frm_PartitionInv: forall ecbls, GoodFrm (PartitionInv ecbls).
Proof. 
  intros. unfold PartitionInv. good_frm_sovler.
Qed.
Hint Resolve good_frm_PartitionInv  : good_frm_lemmas.

(*add by xjl, some lemmas about capability*)
Lemma  GoodFunAsrt_ACap: 
    forall l vl, GoodFunAsrt(ACap l vl).
Proof.
    intros.
    unfold ACap.
    destruct vl.
    destruct c.
    destruct l.
    destruct p.
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits; simpl; auto.
Qed.

Lemma GoodFrm_ACap: 
    forall l vl, GoodFrm(ACap l vl).
Proof.
    intros.
    unfold ACap.
    destruct vl. destruct c. destruct l. destruct p.
    unfold GoodFrm; fold GoodFrm; simpl; auto.
Qed.
 
Lemma GoodFunAsrt_ASlots: 
    forall vl n l, GoodFunAsrt(ASlots l n vl).
Proof.
    inductions vl; intros.
    destruct n; simpl; auto.
    destruct n; simpl; auto.
    destruct a. simpl. auto.
    destruct a. destruct l. 
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits; simpl; auto.
    apply  GoodFunAsrt_ACap.
Qed.

Lemma GoodFrm_ASlots: 
    forall vl n l, GoodFrm(ASlots l n vl).
Proof.
    inductions vl; intros.
    destruct n; simpl; auto.
    destruct n; simpl; auto.
    destruct a. simpl. auto.
    destruct a. destruct l. 
    unfold GoodFrm; fold GoodFrm.
    splits; simpl; auto.
    apply GoodFrm_ACap.
Qed.

Lemma GoodFunAsrt_Acnode: 
    forall vl l, GoodFunAsrt(Acnode l vl).
Proof.
  unfold Acnode. intros.
  destruct vl. destruct p. destruct l. 
  unfold GoodFunAsrt; fold GoodFunAsrt.
  splits. simpl. auto.
  simpl. auto.
  apply GoodFunAsrt_ASlots.
  auto.
Qed.

Lemma GoodFrm_Acnode: 
    forall vl l, GoodFrm(Acnode l vl).
Proof.
  unfold Acnode. intros.
  destruct vl. destruct p. destruct l. 
  unfold GoodFrm; fold GoodFrm.
  splits. simpl. auto.
  simpl. auto.
  apply GoodFrm_ASlots.
  auto.
Qed.

Lemma GoodFunAsrt_ACSpaceAarrayTptr :
    forall vl pvl n cspacels, GoodFunAsrt(ACSpaceAarrayTptr n pvl vl cspacels).
Proof.
    inductions vl; intros.
    destruct n; destruct pvl. simpl. auto.
    simpl. destruct v; simpl; auto.
    simpl. auto.
    simpl. destruct v; simpl; auto.
    destruct n; destruct pvl; simpl; auto.
    destruct v; simpl; auto.
    destruct v; simpl; auto.
    splits; simpl; auto.
    unfold ACSpace.
    destruct a. destruct p.  destruct p. destruct a0. destruct p.
    unfold GoodFunAsrt; fold GoodFunAsrt.
    splits.
    apply GoodFunAsrt_Acnode.
    simpl. auto. auto.
    eapply GoodFunAsrt_Aarray.
    auto. simpl. auto.
    simpl. auto.
    simpl. auto.
Qed.

Hint Resolve GoodFrm_Acnode  : good_frm_lemmas.

Require Import go.

Lemma GoodFrm_ACSpaceAarrayTptr :
    forall vl pvl n cspacels, GoodFrm(ACSpaceAarrayTptr  n pvl vl cspacels).
Proof.
    inductions vl; intros.
    destruct n; destruct pvl. simpl. auto.
    simpl. destruct v; simpl; auto.
    simpl. auto.
    simpl. destruct v; simpl; auto.
    destruct n; destruct pvl; simpl; auto.
    destruct v; simpl; auto.
    destruct v; simpl; auto.
    splits; simpl; auto.
    unfold ACSpace.
    destruct a. destruct p. destruct p. destruct a0. destruct p.
    unfold GoodFrm; fold GoodFrm.
    splits.
    apply GoodFrm_Acnode.
    simpl. auto. auto.
    unfold Aarray.
    go. auto. go.
    simpl. auto.
    simpl. auto.
Qed.

Hint Resolve GoodFrm_ACSpaceAarrayTptr  : good_frm_lemmas.

Lemma GoodFunAsrt_comm: 
  forall p q,
  GoodFunAsrt p ->
  GoodFunAsrt q ->
  GoodFunAsrt (p ** q).
Proof.
  intros.
  unfold GoodFunAsrt.
  fold GoodFunAsrt.
  splits; eauto.
Qed.



Lemma GoodFunAsrt_AOSCSpacePrioTbl: 
    forall l ptrvl vl cspacels, GoodFunAsrt (AOSCSpacePrioTbl l ptrvl vl cspacels).
Proof.
    intros.
    unfold AOSCSpacePrioTbl.
    eapply GoodFunAsrt_comm.
    simpl. auto. 
    eapply GoodFunAsrt_comm.
    eapply GoodFunAsrt_Aarray.
    eapply GoodFunAsrt_comm.
    eapply GoodFunAsrt_ACSpaceAarrayTptr.
    simpl. auto. 
Qed.

Lemma GoodFrm_comm: 
  forall p q,
  GoodFrm p ->
  GoodFrm q ->
  GoodFrm (p ** q).
Proof.
  intros.
  unfold GoodFrm.
  fold GoodFrm.
  splits; eauto.
Qed.


Lemma GoodFrm_AOSCSpacePrioTbl: 
    forall l ptrvl vl cspacels, GoodFrm(AOSCSpacePrioTbl l ptrvl vl cspacels).
Proof.
intros.
  unfold AOSCSpacePrioTbl.
  eapply GoodFrm_comm.
  simpl. auto.
  eapply GoodFrm_comm.
  go.
  eapply GoodFrm_comm.
  eapply GoodFrm_ACSpaceAarrayTptr.
  simpl. 
  auto.
Qed.

(* Ltac GoodFunAsrt_solver :=
  repeat (split;
          try (apply GoodFunAsrt_Aarray);
          try (apply GoodFunAsrt_Astruct);
          try (apply GoodFunAsrt_AEventData);
          try (apply GoodFunAsrt_evsllseg);
          try (apply GoodFunAsrt_tcbdllseg);
          try (apply GoodFunAsrt_dllseg);
          try (apply GoodFunAsrt_ecbf_sll);
          try (apply GoodFunAsrt_sll);
          try (apply GoodFunAsrt_qblkf_sll);
          try (apply GoodFunAsrt_invlth_isr');
          try (apply GoodFunAsrt_Aarray_new); 
                    auto). *)

(* Require Import seplog_tactics.
Require Import seplog_lemmas.
Lemma sub_eq_succ:
forall m n l,  (S m <= l -> S n = l - m -> n = l - (S m))%nat. 
intros. auto with zarith. Qed.

Lemma ACSpaceAarrayTptr_succ_alt :
  forall s a vll n P p ptrvl2 cspacels, 
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels** ACSpaceAarrayTptr  n ptrvl2 vll cspacels ** P -> 
    s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels ** P.
Proof.
    intros.
    sep pauto.
    simpl ACSpaceAarrayTptr in *.
    destruct p. simpl.
    eapply astar_l_afalse_elim in H.
    simpl in H. tryfalse.
sep auto. 
    eapply astar_l_afalse_elim in H.
    simpl in H. tryfalse.
    sep auto.
Qed.




Lemma ACSpaceAarrayTptr_succ_imp :
  forall s a vll n  p ptrvl2 cspacels, 
  s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels->
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels ** ACSpaceAarrayTptr  n ptrvl2 vll cspacels.
    
Proof.
    intros.
    sep pauto.
    simpl ACSpaceAarrayTptr in *.
    destruct p. simpl in H. tryfalse.
sep auto.
    simpl in H. tryfalse.
        sep auto.
Qed.

Lemma ACSpaceAarrayTptr_succ_imp_frm :
  forall s a vll n  p ptrvl2 cspacels P, 
  s |= ACSpaceAarrayTptr  (S n) (p :: ptrvl2) (a :: vll) cspacels ** P->
    s |= ACSpaceAarrayTptr  1 (p::nil) (a::nil) cspacels ** ACSpaceAarrayTptr  n ptrvl2 vll cspacels ** P.
    
Proof.
  intros.
  sep cancel P.
  eapply ACSpaceAarrayTptr_succ_imp; eauto.
Qed.
Open Scope Z_scope.
Open Scope int_scope.
Lemma ACSpaceAarrayTptr_split_strong :
  forall ptrvl1 n ptrvl2 m  s vll1 vll2 cspacels, 
    s |= ACSpaceAarrayTptr (n + m) (ptrvl1 ++ ptrvl2) (vll1 ++ vll2) cspacels->
    Z.of_nat (S n * typelen (Tptr CSPACE)) <= Int.max_unsigned -> 
    (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    length ptrvl1 = n /\ length ptrvl2 = m ->
    length vll1 = n /\ length vll2 = m ->
    s |= ACSpaceAarrayTptr n ptrvl1 vll1 cspacels** ACSpaceAarrayTptr  m ptrvl2 vll2 cspacels.
Proof.
  induction ptrvl1;induction n; intros.
  simpl ACSpaceAarrayTptr in *.
  simpl in H.
  destruct vll1.
  eapply astar_l_aemp_intro.
  auto.
  destruct H2.
  tryfalse.
  destruct H1. tryfalse.
  destruct H2; tryfalse.
  destruct H1. tryfalse.
  destruct vll1.
  destruct H2; tryfalse.
  eapply ACSpaceAarrayTptr_succ_alt.
  change ((a :: ptrvl1) ++ ptrvl2) with (a :: (ptrvl1 ++ ptrvl2)) in H.
  change ((c :: vll1) ++ vll2) with (c :: (vll1 ++ vll2)) in H.
  rewrite Nat.add_succ_l in H.
  eapply ACSpaceAarrayTptr_succ_imp in H.
  sep pauto.
  eapply IHptrvl1.

  sep pauto.
  auto with zarith.
  inverts H1. auto.
  inverts H2. splits; auto.
Qed.

Lemma GoodFrm_AOSCSpacePrioTbl: 
    forall l ptrvl vl cspacels, GoodFrm(AOSCSpacePrioTbl l ptrvl vl cspacels).
Proof.
intros.
unfold AOSCSpacePrioTbl.
good_frm_sovler.
Qed.

Hint Resolve GoodFrm_AOSCSpacePrioTbl  : good_frm_lemmas. *)

Lemma good_frm_CapabilityInv: forall acspace, GoodFrm (CapabilityInv acspace).
Proof.
  intros.
  unfold CapabilityInv.
  good_frm_sovler.
  eapply GoodFrm_AOSCSpacePrioTbl.
  unfold AOSCSpaceObjectPointer.
  good_frm_sovler.
  unfold AOSCSpaceCapParent.
  good_frm_sovler.
  unfold CSpaceGVars.
  good_frm_sovler.
Qed.
Hint Resolve good_frm_CapabilityInv  : good_frm_lemmas. 

(***********************************************************)

(*
Ltac can_change_aop_solver :=
  try unfold OSInv;
  try unfold AOSEventFreeList,
  AOSQFreeList, AOSQFreeBlk, AECBList;
  try unfold AOSMapTbl, AOSUnMapTbl,
  AOSTCBPrioTbl, AOSIntNesting,
  AOSTCBList', AOSTCBFreeList';
  try unfold AOSRdyTblGrp,
  AOSRdyTbl, AOSRdyGrp, AOSTime, AGVars;
  try unfold AOSEvent, AOSEventTbl,
  AMsgData, AOSQCtr, AOSQBlk, node;
  try unfold tcblist;
  unfold can_change_aop;
  fold can_change_aop;
  intuition auto 1 with can_change_aop;
  simpl; intros;  intuition auto 1 with can_change_aop.
 *)

Lemma can_change_aop_osqctr:
  forall c d, 
  can_change_aop (AOSQCtr c d).
Proof.
  unfold AOSQCtr.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_osqctr : can_change_aop.


Lemma  can_change_aop_aosqblk:
  forall x e f, 
  can_change_aop (AOSQBlk x e f).
Proof.
  unfold AOSQBlk.
  intros.
   can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_aosqblk : can_change_aop.

Theorem can_change_aop_msgq :
  forall c d e f,
    can_change_aop (AMsgData c d e f). 
Proof.
  intros.
  unfold AMsgData.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgq : can_change_aop.

Theorem can_change_aop_aevtdata:
  forall vl d , can_change_aop (AEventData vl d).
Proof.
  intros.
  unfold AEventData.
  destruct d; can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aevtdata : can_change_aop.

Lemma can_change_aop_aoseventtbl:
  forall x d,
  can_change_aop (AOSEventTbl x d).
Proof.
  intros.
  unfold AOSEventTbl.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aoseventtbl : can_change_aop.


Lemma  can_change_aop_aosevent:
  forall l vl vl' d,
   can_change_aop (AOSEvent l vl vl' d).
Proof.
  intros.
  unfold AOSEvent.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aosevent : can_change_aop.

Theorem can_change_aop_msgqnode :
  forall l vl vl' d c,
    can_change_aop (AEventNode l vl vl' d c).
Proof.
  intros.
  unfold AEventNode.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqnode : can_change_aop.

Theorem can_change_aop_msgqllseg :
  forall h tn l msgqls,
    can_change_aop (evsllseg h tn l msgqls).
Proof.
  intros.
  gen h tn msgqls.
  induction l; simpl in *; intuition auto.
  destruct msgqls.
  can_change_aop_solver.
  destruct a.
  destruct p.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_msgqllseg : can_change_aop.


Theorem can_change_aop_tcbdllseg :
  forall h hp t tn l,
    can_change_aop (tcbdllseg h hp t tn l).
Proof.
  intros.
  unfold tcbdllseg.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_tcbdllseg : can_change_aop.


Theorem    can_change_aop_ecbfsllseg :
  forall ls x y,
    can_change_aop (ecbf_sllseg x y ls OS_EVENT V_OSEventListPtr).
Proof.
  inductions ls. 
  intros; simpl; intuition auto.
  unfold ecbf_sllseg; fold ecbf_sllseg.
  unfold dllseg; fold dllseg.
  intros.
  can_change_aop_solver.  
Qed.

Hint Resolve can_change_aop_ecbfsllseg: can_change_aop.

Theorem    can_change_aop_ecbfsll :
  forall ls x , can_change_aop (ecbf_sll x ls OS_EVENT V_OSEventListPtr).
Proof.

  intros; unfold ecbf_sll.
  can_change_aop_solver.  
Qed.


Hint Resolve can_change_aop_ecbfsll: can_change_aop.

Theorem  can_change_aop_qblkfseg :
forall x y ls, can_change_aop (qblkf_sllseg x y ls OS_Q_FREEBLK V_nextblk).
Proof.             
  intros.
  gen x y.
  inductions ls .
  unfold qblkf_sllseg.
  intros.
  can_change_aop_solver.  
  intros.
  unfold qblkf_sllseg.
  fold qblkf_sllseg.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_qblkfseg: can_change_aop.

Theorem  can_change_aop_qblkf :
  forall x ls, can_change_aop (qblkf_sll x  ls OS_Q_FREEBLK V_nextblk).
Proof.
  intros.
  unfold qblkf_sll.
  can_change_aop_solver.
Qed.     


Hint Resolve can_change_aop_qblkf: can_change_aop.

Theorem  can_change_aop_sllfreeflag :
  forall x17 x18, can_change_aop (sllfreeflag x17 x18).
Proof.
  intros.
  unfold sllfreeflag.
  gen x17.
  inductions x18.
  intros.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
Qed.

Hint Resolve  can_change_aop_sllfreeflag: can_change_aop.

Theorem  can_change_aop_tcbdllflag:
  forall x6 x5, can_change_aop (tcbdllflag x5 x6).
Proof.
  inductions x6.
  simpl; auto.
  intros.
  simpl.
  intros.
  splits; auto.
  unfold tcbdllflag in IHx6.
  auto.
Qed.

Hint Resolve  can_change_aop_tcbdllflag: can_change_aop.

Theorem can_change_aop_tcbnotin:
  forall x6 x19 ls,
    can_change_aop (TCB_Not_In x6 x19 ls).
 Proof.
   intros.
   unfold TCB_Not_In.
   unfold can_change_aop.
   fold can_change_aop.
   auto.
Qed.

 Hint Resolve  can_change_aop_tcbnotin: can_change_aop.

 Theorem can_change_aop_tcblist:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ,
   can_change_aop (AOSTCBList p1 p2 tcbl1 ls  rtbl ct tcbls). 
Proof.
  intros.
  unfold AOSTCBList.
   can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist: can_change_aop.

Theorem can_change_aop_tcblist_new:
  forall p1 p2 tcbl1 ls rtbl ct tcbls ptfree,
   can_change_aop (AOSTCBList' p1 p2 tcbl1 ls  rtbl ct tcbls ptfree). 
Proof.
  intros.
  unfold AOSTCBList'.
  unfold can_change_aop.
  fold can_change_aop.
  split.
  intros.
  splits;  can_change_aop_solver; auto.
  simpl; auto.
  splits; can_change_aop_solver; auto.
  intros.
  splits; can_change_aop_solver; auto.
  simpl; auto.
  split; auto.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_tcblist_new: can_change_aop.

Lemma can_change_aop_noteq:
  forall ptfree ct lfree, 
   can_change_aop (TCBFree_Not_Eq ptfree ct lfree).
Proof.
  intros.
  unfold TCBFree_Not_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_noteq: can_change_aop.

Lemma can_change_aop_eq:
  forall ptfree ct lfree tcbls, 
   can_change_aop (TCBFree_Eq ptfree ct lfree tcbls).
Proof.
  intros.
  unfold TCBFree_Eq.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_eq: can_change_aop.

Theorem can_change_aop_tcbfreelist:
  forall ptfree lfree,
   can_change_aop (AOSTCBFreeList ptfree lfree).
Proof.
  intros.
  unfold AOSTCBFreeList.
  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist: can_change_aop.



Theorem can_change_aop_tcbfreelist_new:
  forall ptfree lfree ct tcbls,
   can_change_aop (AOSTCBFreeList' ptfree lfree ct tcbls).
Proof.
  intros.
  unfold AOSTCBFreeList'.
  unfold can_change_aop.
  fold can_change_aop.
  splits;  can_change_aop_solver.
Qed.
  
Hint Resolve  can_change_aop_tcbfreelist_new: can_change_aop.

Lemma can_change_aop_evtfls:
  forall p x,
  can_change_aop (AOSEventFreeList p x).
Proof.
  intros.
  unfold AOSEventFreeList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_evtfls: can_change_aop.

Lemma can_change_aop_qfreels:
  forall x,
  can_change_aop (AOSQFreeList x).
Proof.
  intros.
  unfold AOSQFreeList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_qfreels: can_change_aop.

Lemma can_change_aop_qfreeblk:
  forall x,
  can_change_aop (AOSQFreeBlk x).
Proof.
  intros.
  unfold AOSQFreeBlk.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_qfreeblk: can_change_aop.

Lemma can_change_aop_ecblist:
  forall x3 x2 x12 x13,
  can_change_aop (AECBList x3 x2 x12 x13).
Proof.
  intros.
  unfold AECBList.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_ecblist: can_change_aop.

Lemma can_change_aop_mtbl:
  can_change_aop AOSMapTbl.
Proof.
  intros.
  unfold AOSMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_mtbl: can_change_aop.

Lemma can_change_aop_unmtbl:
  can_change_aop AOSUnMapTbl.
Proof.
  intros.
  unfold AOSUnMapTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_unmtbl: can_change_aop.

Lemma can_change_aop_prtbl:
  forall x4 x10 x13 ptls x16,
  can_change_aop  (AOSTCBPrioTbl x4 x10 x13 ptls x16).
Proof.
  intros.
  unfold AOSTCBPrioTbl.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_prtbl: can_change_aop.


Lemma can_change_aop_intnest:
  can_change_aop (AOSIntNesting).
Proof.
  intros.
  unfold AOSIntNesting.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_intnest: can_change_aop.

Lemma can_change_aop_rdytbl:
  forall x10 ,
  can_change_aop  (AOSRdyTbl x10).
Proof.
  intros.
  unfold AOSRdyTbl.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdytbl: can_change_aop.

Lemma can_change_aop_rdygrp:
  forall x10 ,
  can_change_aop  (AOSRdyGrp x10).
Proof.
  intros.
  unfold AOSRdyGrp.
  can_change_aop_solver.
Qed.


Hint Resolve  can_change_aop_rdygrp: can_change_aop.


Lemma can_change_aop_rdytbgrp:
  forall x10 x11,
  can_change_aop  (AOSRdyTblGrp x10 x11).
Proof.
  intros.
  unfold AOSRdyTblGrp.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_rdytbgrp: can_change_aop.

Lemma can_change_aop_time:
  forall x14, 
  can_change_aop  (AOSTime (Vint32 x14)).
Proof.
  intros.
  unfold AOSTime.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_time: can_change_aop.

Lemma can_change_aop_gvars:
  can_change_aop AGVars.
Proof.
  intros.
  unfold AGVars.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_gvars: can_change_aop.

Lemma can_change_aop_plocal:
  forall tid l, can_change_aop (p_local OSLInv tid l).
Proof.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_plocal : can_change_aop.

Lemma can_change_aop_isris:
  can_change_aop  A_isr_is_prop.
Proof.
  intros.
  unfold  A_isr_is_prop.
  can_change_aop_solver.
Qed.  

Hint Resolve  can_change_aop_isris: can_change_aop.                  



(******************* EvtInv management ***********************)

Theorem can_change_aop_Aarray_new' :
forall n vll t l , can_change_aop (Aarray_new' l n t vll).
Proof.
induction n; induction vll; intros;
try can_change_aop_solver.
clear -IHn.
destruct l.
destruct t;
simpl Aarray_new' in *;
destruct a; 
try can_change_aop_solver;
destruct a;
try can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Aarray_new': can_change_aop.  

Theorem can_change_aop_Aarray_new :
forall vll t l , can_change_aop (Aarray_new l t vll).
Proof.
intros.
unfold Aarray_new.
destruct t; try can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_Aarray_new: can_change_aop.  

Theorem can_change_aop_ASeminfo :
  forall l infol,
    can_change_aop (ASeminfo l infol).
Proof.
  intros.
  unfold ASeminfo.
  unfold can_change_aop.
  fold can_change_aop.
  split; can_change_aop_solver.
  split; can_change_aop_solver.
  auto.
Qed.

Hint Resolve  can_change_aop_ASeminfo: can_change_aop.  

Theorem can_change_aop_AEvtCap:
  forall scapl l fieldname eibtype,
    can_change_aop (AEvtCap l scapl fieldname eibtype).
Proof.
  induction scapl; intros.
  destruct l.
  simpl; auto.

  destruct l.
  unfold AEvtCap.
  fold AEvtCap.
  unfold can_change_aop.
  fold can_change_aop.
  split; can_change_aop_solver.
  splits; auto.
Qed.

Hint Resolve can_change_aop_AEvtCap: can_change_aop.

Theorem can_change_aop_ASemCap:
  forall l scapl,
    can_change_aop (ASemCap l scapl).
Proof.
  intros.
  unfold ASemCap.
  can_change_aop_solver. 
Qed.

Hint Resolve can_change_aop_ASemCap: can_change_aop.

Theorem can_change_aop_ASemEIBs : 
  forall (infol : list vallist) scapl (embls : EmbMod.map) (ecbls : EcbMod.map) vhold,
  can_change_aop (ASemEIBs infol scapl embls ecbls vhold).
Proof.
  intros.
  unfold ASemEIBs.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ASemEIBs: can_change_aop. 

Lemma can_change_aop_apthreadmutex:
  forall l x23,
    can_change_aop (APthreadMutex l x23).
Proof.
  intros.
  unfold APthreadMutex.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_apthreadmutex: can_change_aop.

Lemma can_change_aop_AMuxCap:
  forall l mcapl,
    can_change_aop (AMuxCap l mcapl).
Proof.
  intros.
  unfold AMuxCap.
  can_change_aop_solver. 
Qed. 

Hint Resolve can_change_aop_AMuxCap: can_change_aop.

Lemma can_change_aop_AMuxEIBs:
  forall x23 mcapl x19 x12 x16,
  can_change_aop (AMuxEIBs x23 mcapl x19 x12 x16).
 Proof.
  intros.
  unfold AMuxEIBs.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AMuxEIBs: can_change_aop.

Theorem can_change_aop_AMqAttr :
  forall l (qattrl :list vallist),
    can_change_aop (AMqAttr l qattrl).
Proof.
  intros.
  unfold AMqAttr.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AMqAttr: can_change_aop. 

Theorem can_change_aop_AMqCap:
  forall l qcapl,
    can_change_aop (AMqCap l qcapl).
Proof.
  intros.
  unfold AMqCap.
  can_change_aop_solver. 
Qed. 

Hint Resolve can_change_aop_AMqCap: can_change_aop.

Theorem can_change_aop_AMqEIBs :
  forall (qattrl : list vallist) qcapl (qattr : MqattrMod.map)(ecbls:EcbMod.map)(vhold:addrval),
    can_change_aop (AMqEIBs qattrl qcapl qattr ecbls vhold).
Proof.
  intros.
  unfold AMqEIBs.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AMqEIBs: can_change_aop. 

Lemma can_change_aop_pos_sllseg :
  forall vll hd tn pbls, 
    can_change_aop (pos_sllseg hd tn vll pbls).  
Proof.
  inductions vll; intros.
  unfold pos_sllseg. simpl; auto.
  simpl.
  splits; auto.
  intros. splits; auto. 
  destruct a.
  simpl; auto.
  can_change_aop_solver.
  destruct a.
  simpl; auto.
  can_change_aop_solver.
  destruct a; simpl; auto.
Qed. 

Hint Resolve can_change_aop_pos_sllseg: can_change_aop.

Lemma can_change_aop_APosblkList:
  forall pbls, can_change_aop (APosblkList pbls).
Proof.
  intros.
  unfold APosblkList.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_APosblkList: can_change_aop. 

Lemma can_change_aop_evaux_node:
  forall a v1 v2 v3 v4, 
    can_change_aop (evaux_node a v1 v2 v3 v4). 
Proof.
  intros.
  simpl. splits; auto.
Qed.

Hint Resolve can_change_aop_evaux_node: can_change_aop.

Lemma can_change_aop_llsegevaux :
  forall l hd tn locmp ptrmp nextf,  
    can_change_aop (llsegevaux hd tn l locmp ptrmp nextf). 
Proof.
  inductions l.
  intros. simpl. splits; auto.
  intros. simpl. intros. splits; auto. splits; auto.
Qed.   

Hint Resolve can_change_aop_llsegevaux: can_change_aop.

Lemma can_change_aop_tcbllsegevaux:
  forall tcbvl tcbh  locmp ptrmp, 
    can_change_aop (tcbllsegevaux tcbh tcbvl locmp ptrmp).  
Proof.
  unfold tcbllsegevaux.
  intros. apply can_change_aop_llsegevaux.
Qed.

Hint Resolve can_change_aop_tcbllsegevaux: can_change_aop. 

Lemma can_change_aop_AEvAtomHeap:
  forall x25,
  can_change_aop (AEvAtomHeap x25).
 Proof.
  intros.
  induction x25.
  simpl; eauto.
  destruct a. destruct p. 
  destruct t; simpl; eauto.
(*   splits; eauto. *)
(*    can_change_aop_solver. *)
Qed. 

Hint Resolve  can_change_aop_AEvAtomHeap: can_change_aop. 

Lemma can_change_aop_AEvStructHeap:
  forall x25,
  can_change_aop (AEvStructHeap x25).
 Proof.
  intros.
  induction x25.
  simpl; eauto.
  destruct a. destruct p. 
  destruct t; simpl; eauto.
  splits; eauto.
   can_change_aop_solver.
Qed. 

Hint Resolve  can_change_aop_AEvStructHeap: can_change_aop. 

Lemma can_change_aop_AEvArrayHeap:
  forall x25,
  can_change_aop (AEvArrayHeap x25).
 Proof.
  intros.
  induction x25.
  simpl; eauto.
  destruct a. destruct p. 
  simpl; eauto.
  splits; eauto.
   can_change_aop_solver.
Qed. 

Hint Resolve  can_change_aop_AEvArrayHeap: can_change_aop. 

Lemma can_change_aop_errsllseg :
 forall vll p t ebls, can_change_aop (err_sllseg p t vll ebls).
Proof.
  inductions vll.
  simpl; auto.
  simpl err_sllseg.
  unfold can_change_aop; fold can_change_aop.
  intros; splits; auto.
  destruct a.
  simpl; auto.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_errsllseg: can_change_aop.

Lemma can_change_aop_AErrblkList :
  forall x, can_change_aop (AErrblkList x).
Proof.
  introv.
  unfold AErrblkList.
  unfold can_change_aop.  fold can_change_aop.
  split; intros.
  simpl; auto.
  apply can_change_aop_errsllseg.
Qed.

Hint Resolve can_change_aop_AErrblkList: can_change_aop.

Lemma can_change_aop_EvtInv:
  forall ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl,
    can_change_aop (EvtInv ecbls tcblh tcbvl tcbls vhold scapl mcapl qcapl). 
Proof.
  intros.
  unfold EvtInv.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_EvtInv: can_change_aop. 

(******************* End events management ***********************)

Lemma can_change_aop_aemp_isr_is:
can_change_aop aemp_isr_is.
Proof.
unfold aemp_isr_is.
can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_aemp_isr_is: can_change_aop.

Lemma can_change_aop_IntInv: can_change_aop IntInv.
Proof.
  unfold IntInv.
  unfold AOSInthandler, AOSInthandlerParam, AOSExchandler.
  can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_IntInv  : can_change_aop.

(* add by SJTU *)

Theorem  can_change_aop_AOSClkRate : 
forall v, can_change_aop (AOSClkRate v).
Proof.
  unfold AOSClkRate. intros. can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSClkRate : can_change_aop.

Theorem can_change_aop_AOSTMRNode:
 forall n v , can_change_aop (AOSTMRNode n v).
 Proof.
  intros. unfold AOSTMRNode.
  can_change_aop_solver.
  Qed.

Hint Resolve can_change_aop_AOSTMRNode : can_change_aop.

Theorem can_change_aop_AOSTMRList':
 forall v, can_change_aop (AOSTMRList' v).
Proof.
  intros. unfold AOSTMRList'.
  repeat (apply can_change_aop_ex;intros).
  can_change_aop_solver.
  all: apply can_change_aop_AOSTMRNode.
  Qed.

Hint Resolve can_change_aop_AOSTMRList' : can_change_aop.

Theorem  can_change_aop_AOSTMRIDUsed: 
 forall vl, can_change_aop (AOSTMRIDUsed vl).
Proof.
  unfold AOSTMRIDUsed;intros. can_change_aop_solver.  
Qed.

Hint Resolve can_change_aop_AOSTMRIDUsed : can_change_aop.

Theorem can_change_aop_AOSTMRList_TMRused:
 forall systmrl utmrl tmrusedl tmrls, can_change_aop (AOSTMRList_TMRused systmrl utmrl tmrusedl tmrls).
Proof.
  intros. unfold AOSTMRList_TMRused.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSTMRList_TMRused : can_change_aop.


(* 
Theorem can_change_aop_timmerregVar : 
  can_change_aop (timerregVar ).
Proof.
  intros. unfold timerregVar.
  can_change_aop_solver.
Qed. 
Hint Resolve can_change_aop_timmerregVar : can_change_aop. *)

Theorem can_change_aop_AOScoreheapl : 
  forall vl, can_change_aop (AOScoreheapl vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOScoreheapl : can_change_aop.

Theorem can_change_aop_AOScoreheape : 
  forall vl, can_change_aop (AOScoreheape vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOScoreheape : can_change_aop.

Theorem can_change_aop_AOScoreheapt : 
  forall vl, can_change_aop (AOScoreheapt vl).
Proof. 
  induction vl;intros;cbn.
  - auto.
  - destruct a. destruct p. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOScoreheapt : can_change_aop.

Theorem  can_change_aop_Memory_sigcore_aux:
 forall n pl vl, can_change_aop (Memory_sigcore_aux n pl vl).
Proof.
  intros. revert n pl. induction vl;intros.
  - cbn;auto. 
  - unfold Memory_sigcore_aux;fold Memory_sigcore_aux.
    cbn.
    splits;auto.
    split;auto.
    can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_Memory_sigcore_aux : can_change_aop.

Theorem can_change_aop_AOSIPCMem_aux:
  forall pl memlls, can_change_aop (AOSIPCMem_aux pl memlls).
Proof.
  induction pl;intros.
  - destruct memlls;cbn;auto.
  - 
    unfold AOSIPCMem_aux;fold AOSIPCMem_aux.
    destruct a;auto.
    1,2,3: cbn;auto.
    destruct memlls;cbn;auto.
    splits;auto.
    split;auto.
    apply can_change_aop_Memory_sigcore_aux.
Qed.

Hint Resolve can_change_aop_AOSIPCMem_aux : can_change_aop.

Theorem can_change_aop_AOSIPCMem:
  forall pl memlls, can_change_aop (AOSIPCMem pl memlls).
Proof.
  intros. unfold AOSIPCMem.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCMem : can_change_aop.


Theorem can_change_aop_AOSIPCSem:
  forall pl , can_change_aop (AOSIPCSem pl).
Proof. 
  intros. unfold AOSIPCSem.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCSem : can_change_aop.

Theorem can_change_aop_AOSIPCSemShared:
  forall pl , can_change_aop (AOSIPCSemShared pl).
Proof. 
  intros. unfold AOSIPCSemShared.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCSemShared : can_change_aop.

Theorem can_change_aop_AOSIPCSendSem:
  forall pl , can_change_aop (AOSIPCSendSem pl).
Proof. 
  intros. unfold AOSIPCSendSem.
  can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCSendSem : can_change_aop.


Theorem  can_change_aop_AOSIPCGRinfo: 
  forall m, can_change_aop (AOSIPCGRinfo m).
Proof.
  intros. unfold AOSIPCGRinfo. can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCGRinfo : can_change_aop.

Theorem  can_change_aop_AOSIPCBroadList: 
  forall vl bl, can_change_aop (AOSIPCBroadList vl bl).
Proof.
  intros. unfold AOSIPCBroadList. can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AOSIPCBroadList : can_change_aop.

Theorem can_change_aop_Adynheap: 
  forall vl, can_change_aop (Adynheap vl).
Proof.
  induction vl; can_change_aop_solver. destruct a. cbn [Adynheap]. can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_Adynheap : can_change_aop.

Theorem  can_change_aop_AdynrefaccfgFreeList : 
  forall p vl, can_change_aop (AdynrefaccfgFreeList p vl).
Proof.
  intros. unfold AdynrefaccfgFreeList. can_change_aop_solver.
Qed.

Hint Resolve can_change_aop_AdynrefaccfgFreeList : can_change_aop.

Lemma can_change_aop_ASlots: 
  forall c n l,
  can_change_aop (ASlots l n c).
Proof.
  induction c; destruct n; intros.
  simpl. auto.
  simpl. auto.
  destruct a. simpl. auto.
  simpl. destruct a. destruct l. 
  can_change_aop_solver.
  unfold ACap.
  destruct p, c0, p. 
  can_change_aop_solver.
Qed.

Lemma can_change_aop_Acnode: 
  forall l c, 
  can_change_aop (Acnode l c).
Proof.
  intros.
  unfold Acnode.
  destruct c,p,l. 
  can_change_aop_solver.
  eapply can_change_aop_ASlots.
Qed.



(* add end by SJTU *)
Lemma can_change_aop_ACSpaceAarrayTptr: 
  forall x0 x x1 x2,
  can_change_aop (ACSpaceAarrayTptr x x0 x1 x2).
Proof.
  induction x0; destruct x;intros.
  simpl. destruct x1. simpl. auto.
  simpl. auto.
  simpl. destruct x1. simpl. auto.
  simpl. auto.
  simpl. destruct a. simpl. auto.
  destruct x1; simpl; auto.
  simpl. auto.
  destruct x1; simpl; auto.
  simpl. auto.
  destruct a. simpl. auto.
  destruct x1. simpl. auto.
  eapply IHx0.
  simpl. auto.
  destruct x1. simpl. auto.
  unfold ACSpace. 
  destruct c, p, p, a, p.
  good_frm_sovler.
  can_change_aop_solver.
  eapply can_change_aop_Acnode.
Qed.

Lemma can_change_aop_TmrInv': can_change_aop TmrInv'.
Proof. unfold TmrInv'; can_change_aop_solver. Qed.
Hint Resolve can_change_aop_TmrInv'  : can_change_aop.

Lemma can_change_aop_HeapInv': can_change_aop HeapInv'.
Proof. unfold HeapInv'; can_change_aop_solver. Qed.
Hint Resolve can_change_aop_HeapInv'  : can_change_aop. 

Lemma can_change_aop_TmrInv:can_change_aop TmrInv.
Proof. unfold TmrInv; can_change_aop_solver. Qed.
Hint Resolve can_change_aop_TmrInv  : can_change_aop.

Lemma can_change_aop_DynamicRefactorINV: forall vl, can_change_aop (DynamicRefactorINV vl).
Proof. intros. unfold DynamicRefactorINV. can_change_aop_solver. Qed.
Hint Resolve can_change_aop_DynamicRefactorINV  : can_change_aop.

Lemma can_change_aop_CoreCommuInv: forall vl, can_change_aop (CoreCommuInv vl).
Proof. intros;unfold CoreCommuInv; can_change_aop_solver.  Qed.
Hint Resolve can_change_aop_CoreCommuInv  : can_change_aop.

Lemma can_change_aop_APortStruct: forall v u, can_change_aop (APortStruct u v).
Proof.
  intros.
  unfold APortStruct.
  can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_APortStruct  : can_change_aop.

Lemma can_change_aop_dmportp_sllseg_sampleport_msg: forall l v, can_change_aop (dmportp_sllseg_sampleport_msg v l).
Proof.
  intros. unfold dmportp_sllseg_sampleport_msg. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_dmportp_sllseg_sampleport_msg  : can_change_aop.

Lemma can_change_aop_dmportp_sllseg_qport_msg: forall v5 v0 v1 v2 v3 v4, can_change_aop (dmportp_sllseg_qport_msg v0 v1 v2 v3 v4 v5).
Proof.
  induction v5; destruct v4; intros.
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  cbn [dmportp_sllseg_qport_msg].
  can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_dmportp_sllseg_qport_msg  : can_change_aop.

Lemma can_change_aop_dmportp_sllseg: forall l0 l1 u v, can_change_aop (dmportp_sllseg u v l0 l1 OS_Port_V_nextPort).
Proof.
  induction l0; destruct l1; intros.
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  cbn [dmportp_sllseg].
  can_change_aop_solver.
  simpl. split.
  { split; auto.
    intros. split; auto.
    split; auto.
    intros. split; auto.
    destruct x2; destruct x3; can_change_aop_solver; simpl.
    { split; auto; repeat (destruct x3; can_change_aop_solver). }
    { repeat (simpl; split; auto; destruct x2; can_change_aop_solver). }
    { repeat (simpl; split; auto; destruct x2; can_change_aop_solver);
      simpl; split; auto; repeat (destruct x3; can_change_aop_solver). } }
  intros.
  repeat (splits; auto); can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_dmportp_sllseg  : can_change_aop.

Lemma can_change_aop_dmportp_sll: forall v0 v1 v, can_change_aop (dmportp_sll v v0 v1 OS_Port_V_nextPort).
Proof.
  unfold dmportp_sll.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_dmportp_sll  : can_change_aop.

Lemma can_change_aop_AOSDomainPortPtrList: forall dportlptr dportl dportmsgll,
can_change_aop (AOSDomainPortPtrList dportlptr dportl dportmsgll).
Proof.
  intros. unfold AOSDomainPortPtrList. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSDomainPortPtrList  : can_change_aop.

Lemma can_change_aop_kportNode_P: forall v v0, can_change_aop (kportNode_P v v0).
Proof.
  induction v; destruct v0; intros.
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  { can_change_aop_solver. }
  cbn [kportNode_P]. can_change_aop_solver.
  simpl. split; auto.
  intros; split; auto.
  destruct v0; can_change_aop_solver.
  destruct v2; can_change_aop_solver.
  destruct v3; can_change_aop_solver.
  destruct v4; can_change_aop_solver.
  destruct v5; can_change_aop_solver.
  destruct v6; can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_kportNode_P  : can_change_aop.

Lemma can_change_aop_AOSKernelPortIDTbl: forall v v0, can_change_aop (AOSKernelPortIDTbl v v0).
Proof.
  unfold AOSKernelPortIDTbl.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSKernelPortIDTbl  : can_change_aop.

Lemma can_change_aop_Channel_dstkport_get: forall l u v w, can_change_aop (Channel_dstkport_get u v w l).
Proof.
  induction l; destruct w; intros; can_change_aop_solver.
  cbn [Channel_dstkport_get]. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_Channel_dstkport_get  : can_change_aop.

Lemma can_change_aop_ChannelNode: forall v v0 v1, can_change_aop (ChannelNode v v0 v1).
Proof.
  induction v; induction v0; destruct v1; intros; can_change_aop_solver.
  cbn [ChannelNode]. can_change_aop_solver.
  simpl. split; auto. split.
  { intros. split; auto.
    repeat (destruct a0; can_change_aop_solver). }
  intros. splits; auto. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_ChannelNode  : can_change_aop.

Lemma can_change_aop_AOSChannelIDTbl: forall v v0 v1, can_change_aop (AOSChannelIDTbl v v0 v1).
Proof.
  unfold AOSChannelIDTbl.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSChannelIDTbl  : can_change_aop.

Lemma can_change_aop_kportf_sllseg: forall l u v, can_change_aop (kportf_sllseg u v l OS_K_Port OS_K_Port_V_OSEventPtr).
Proof.
  induction l; intros; can_change_aop_solver.
  cbn [kportf_sllseg]. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_kportf_sllseg  : can_change_aop.

Lemma can_change_aop_kportf_sll: forall v v0, can_change_aop (kportf_sll v v0 OS_K_Port OS_K_Port_V_OSEventPtr).
Proof.
  unfold kportf_sll.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_kportf_sll  : can_change_aop.

Lemma can_change_aop_AOSKernelPortFreeList: forall v v0, can_change_aop (AOSKernelPortFreeList v v0).
Proof.
  unfold AOSKernelPortFreeList.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSKernelPortFreeList  : can_change_aop.

Lemma can_change_aop_channelf_sllseg: forall l u v, can_change_aop (channelf_sllseg u v l OS_Channel OS_Channel_V_OSEventPtr).
Proof.
  induction l; intros; can_change_aop_solver.
  cbn [channelf_sllseg]. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_channelf_sllseg  : can_change_aop.

Lemma can_change_aop_channelf_sll: forall v v0, can_change_aop (channelf_sll v v0 OS_Channel OS_Channel_V_OSEventPtr).
Proof.
  unfold channelf_sll.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_channelf_sll  : can_change_aop.

Lemma can_change_aop_AOSChannelFreeList: forall v v0, can_change_aop (AOSChannelFreeList v v0).
Proof.
  unfold AOSChannelFreeList.
  intros. can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_AOSChannelFreeList  : can_change_aop.

Lemma can_change_aop_OtherPortPtrList: forall l l0 l1, can_change_aop (OtherPortPtrList l l0 l1).
Proof.
  induction l; induction l0; destruct l1; intros; can_change_aop_solver.
  cbn [OtherPortPtrList]. can_change_aop_solver.
  simpl. split.
  { split; auto.
    intros. repeat (split; auto).
    destruct x0; destruct x1; can_change_aop_solver; simpl.
    { split; auto; repeat (destruct x1; can_change_aop_solver). }
    { repeat (simpl; split; auto; destruct x0; can_change_aop_solver). }
    { repeat (simpl; split; auto; destruct x0; can_change_aop_solver);
      simpl; split; auto; repeat (destruct x1; can_change_aop_solver). } }
  intros.
  repeat (splits; auto); can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_OtherPortPtrList  : can_change_aop.

Lemma can_change_aop_AOSCorePortPtrList: forall l l0 l1, can_change_aop (AOSCorePortPtrList l l0 l1).
Proof.
  unfold AOSCorePortPtrList; intros. can_change_aop_solver. Qed.
Hint Resolve can_change_aop_AOSCorePortPtrList  : can_change_aop.

(* add by CNU *)

Theorem can_change_aop_Aarray :
forall vl t l , can_change_aop (Aarray l t vl).
Proof.
intros.
unfold Aarray.
destruct t; try can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_Aarray: can_change_aop.

Lemma can_change_aop_AIntrDomainMux :
  forall l vl abs, can_change_aop (AIntrDomainMux l vl abs).
Proof.
  introv.
  unfold AIntrDomainMux.
  unfold can_change_aop. fold can_change_aop.
  split; intros.
  simpl; auto.
  split; intros.
  apply can_change_aop_Aarray. auto.
Qed.

Hint Resolve can_change_aop_AIntrDomainMux: can_change_aop.

Theorem can_change_aop_node_offt :
forall vl l t, can_change_aop (node_offt l vl t).
Proof.
intros.
unfold node_offt.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_node_offt: can_change_aop.

Theorem can_change_aop_AAllArea :
forall vl t l , can_change_aop (AAllArea l t vl).
Proof.
intros.
unfold AAllArea.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AAllArea: can_change_aop.

Theorem can_change_aop_AksDomSchedule' :
forall vl l , can_change_aop (AksDomSchedule' l vl).
Proof.
  induction vl.
  intros.
  unfold AksDomSchedule'.
  can_change_aop_solver.
  intros.
  unfolds AksDomSchedule'; fold AksDomSchedule'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AksDomSchedule': can_change_aop.

Theorem can_change_aop_ADeviceioTbl' :
forall vl l , can_change_aop (ADeviceioTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold ADeviceioTbl'.
  can_change_aop_solver.
  intros.
  unfolds ADeviceioTbl'; fold ADeviceioTbl'.
  destruct a as [].
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ADeviceioTbl': can_change_aop.

Theorem can_change_aop_AksDomains' :
forall vl l , can_change_aop (AksDomains' l vl).
Proof.
  induction vl.
  intros.
  unfold AksDomains'.
  can_change_aop_solver.
  intros.
  unfolds AksDomains'; fold AksDomains'.
  destruct a as [[[]]].
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AksDomains': can_change_aop.

Lemma can_change_aop_Acpus' :
 forall vl l, can_change_aop (Acpus' l vl).
Proof.
  induction vl.
  simpl; auto.
  unfold Acpus'; fold Acpus'.
  destruct a as [[[]]].
  unfold can_change_aop; fold can_change_aop.
  intros; splits; auto.
  can_change_aop_solver.
  intros; splits; auto.
  split; auto.
  split; can_change_aop_solver; auto.
  split; can_change_aop_solver; auto.
  split; can_change_aop_solver; auto.
Qed.

Hint Resolve can_change_aop_Acpus': can_change_aop.

Theorem can_change_aop_ACPUs :
forall l vl abs, can_change_aop (ACPUs l vl abs).
Proof.
intros.
unfold ACPUs.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_ACPUs: can_change_aop.

Theorem can_change_aop_AchannelTbl' :
forall vl l , can_change_aop (AchannelTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold AchannelTbl'.
  can_change_aop_solver.
  intros.
  unfolds AchannelTbl'; fold AchannelTbl'.
  destruct a as [].
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AchannelTbl': can_change_aop.

Theorem can_change_aop_AChannelTbl :
forall l vl abs, can_change_aop (AChannelTbl l vl abs).
Proof.
intros.
unfold AChannelTbl.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AChannelTbl: can_change_aop.

Theorem can_change_aop_AportTbl' :
forall vl l , can_change_aop (AportTbl' l vl).
Proof.
  induction vl.
  intros.
  unfold AportTbl'.
  can_change_aop_solver.
  intros.
  unfolds AportTbl'; fold AportTbl'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AportTbl': can_change_aop.

Theorem can_change_aop_APortTbl :
forall l vl abs, can_change_aop (APortTbl l vl abs).
Proof.
intros.
unfold APortTbl.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_APortTbl: can_change_aop.

Theorem can_change_aop_AucosConf :
forall l abs, can_change_aop (AucosConf l abs).
Proof.
  intros.
  unfold AucosConf; fold AucosConf.
  destruct l as [[[[[[]]]]]].
  destruct abs as [[[[[[[[[[[[[]]]]]]]]]]]]].
  can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AucosConf: can_change_aop.

Theorem can_change_aop_Adomain2index' :
forall l, can_change_aop (Adomain2index' l).
Proof.
  induction l.
  intros.
  unfold Adomain2index'.
  can_change_aop_solver.
  intros.
  unfolds Adomain2index'; fold Adomain2index'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Adomain2index': can_change_aop.

Theorem can_change_aop_Adomain2index :
forall l ls, can_change_aop (Adomain2index l ls).
Proof.
intros.
unfold Adomain2index.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_Adomain2index: can_change_aop.

Theorem can_change_aop_AKsDSchdidx :
forall l, can_change_aop (AKsDSchdidx l).
Proof.
intros.
unfold AKsDSchdidx.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsDSchdidx: can_change_aop.

Theorem can_change_aop_AKsDSchdlen :
forall l, can_change_aop (AKsDSchdlen l).
Proof.
intros.
unfold AKsDSchdlen.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsDSchdlen: can_change_aop.

Theorem can_change_aop_AKsCurDomain :
forall l, can_change_aop (AKsCurDomain l).
Proof.
intros.
unfold AKsCurDomain.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsCurDomain: can_change_aop.

Theorem can_change_aop_AKsLastDomain :
forall l, can_change_aop (AKsLastDomain l).
Proof.
intros.
unfold AKsLastDomain.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsLastDomain: can_change_aop.

Theorem can_change_aop_AKsDomainTime :
forall l, can_change_aop (AKsDomainTime l).
Proof.
intros.
unfold AKsDomainTime.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsDomainTime: can_change_aop.

Theorem can_change_aop_AKsDomSchedule' :
forall l, can_change_aop (AKsDomSchedule' l).
Proof.
  induction l.
  intros.
  unfold AKsDomSchedule'.
  can_change_aop_solver.
  intros.
  unfolds AKsDomSchedule'; fold AKsDomSchedule'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AKsDomSchedule': can_change_aop.

Theorem can_change_aop_AKsDomSchedule :
forall l abs, can_change_aop (AKsDomSchedule l abs).
Proof.
intros.
unfold AKsDomSchedule.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AKsDomSchedule: can_change_aop.

Theorem can_change_aop_AisChangePartion :
forall v, can_change_aop (AisChangePartion v).
Proof.
intros.
unfold AisChangePartion.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AisChangePartion: can_change_aop.

Theorem can_change_aop_AIntPartMux' :
forall l, can_change_aop (AIntPartMux' l).
Proof.
  induction l.
  intros.
  unfold AIntPartMux'.
  can_change_aop_solver.
  intros.
  unfolds AIntPartMux'; fold AIntPartMux'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AIntPartMux': can_change_aop.

Theorem can_change_aop_AIntPartMux :
forall l abs, can_change_aop (AIntPartMux l abs).
Proof.
intros.
unfold AIntPartMux.
can_change_aop_solver. 
Qed.

Hint Resolve  can_change_aop_AIntPartMux: can_change_aop.

Lemma can_change_aop_Asms_mpaxinfo :
  forall vl,
    can_change_aop (Asms_mpaxinfo vl).
Proof.
  intros.
  unfold Asms_mpaxinfo.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Asms_mpaxinfo: can_change_aop.

Lemma can_change_aop_ASMSMpax :
  forall vl abs,
    can_change_aop (ASMSMpax vl abs).
Proof.
  intros.
  unfold ASMSMpax.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ASMSMpax: can_change_aop.

Lemma can_change_aop_Ases_mpaxinfo :
  forall vl,
    can_change_aop (Ases_mpaxinfo vl).
Proof.
  intros.
  unfold Ases_mpaxinfo.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Ases_mpaxinfo: can_change_aop.

Lemma can_change_aop_ASESMpax :
  forall vl abs,
    can_change_aop (ASESMpax vl abs).
Proof.
  intros.
  unfold ASESMpax.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ASESMpax: can_change_aop.

Lemma can_change_aop_Axmpaxinfo :
  forall vl,
    can_change_aop (Axmpaxinfo vl).
Proof.
  intros.
  unfold Axmpaxinfo.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_Axmpaxinfo: can_change_aop.

Lemma can_change_aop_AXMpax :
  forall vl abs,
    can_change_aop (AXMpax vl abs).
Proof.
  intros.
  unfold AXMpax.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AXMpax: can_change_aop.

Lemma can_change_aop_AMPAXs :
    can_change_aop (AMPAXs).
Proof.
  intros.
  unfold AMPAXs.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AMPAXs: can_change_aop.

Lemma can_change_aop_AXMPFR :
    can_change_aop (AXMPFR).
Proof.
  intros.
  unfold AXMPFR.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AXMPFR: can_change_aop.

Lemma can_change_aop_AMDMAER :
    can_change_aop (AMDMAER).
Proof.
  intros.
  unfold AMDMAER.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AMDMAER: can_change_aop.

Lemma can_change_aop_AKsDomains' :
  forall vl l,  can_change_aop (AKsDomains' l vl).
Proof.
  induction vl.
  simpl; auto.
  destruct a.
  unfold AKsDomains'; fold AKsDomains'.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AKsDomains': can_change_aop.

Lemma can_change_aop_AKsDomains :
  forall vl abs,  can_change_aop (AKsDomains vl abs).
Proof.
  intros.
  unfold AKsDomains.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AKsDomains: can_change_aop.

Lemma can_change_aop_AisCoreBoot :
  forall v,  can_change_aop (AisCoreBoot v).
Proof.
  intros.
  unfold AisCoreBoot.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AisCoreBoot: can_change_aop.

Lemma can_change_aop_AsystemStck' :
  forall vl,  can_change_aop (AsystemStck' vl).
Proof.
  intros.
  unfold AsystemStck'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AsystemStck': can_change_aop.

Lemma can_change_aop_AOSSystemSP :
  forall v,  can_change_aop (AOSSystemSP v).
Proof.
  intros.
  unfold AOSSystemSP.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AOSSystemSP: can_change_aop.

Lemma can_change_aop_ACorepartnum' :
  forall v,  can_change_aop (ACorepartnum' v).
Proof.
  intros.
  unfold ACorepartnum'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ACorepartnum': can_change_aop.

Lemma can_change_aop_ACorepartnum :
  forall v,  can_change_aop (ACorepartnum v).
Proof.
  intros.
  unfold ACorepartnum.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ACorepartnum: can_change_aop.

Lemma can_change_aop_APortnumcur :
  can_change_aop (APortnumcur).
Proof.
  intros.
  unfold APortnumcur.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_APortnumcur: can_change_aop.

Lemma can_change_aop_APartArea' :
  forall vl,  can_change_aop (APartArea' vl).
Proof.
  unfold APartArea'.
  intros.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_APartArea': can_change_aop.

Lemma can_change_aop_APartArea :
  forall vl abs,  can_change_aop (APartArea vl abs).
Proof.
  intros.
  unfold APartArea.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_APartArea: can_change_aop.

Lemma can_change_aop_APartID2Dom :
  forall vl,  can_change_aop (APartID2Dom vl).
Proof.
  intros.
  unfold APartID2Dom.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_APartID2Dom: can_change_aop.

Lemma can_change_aop_ARootTaskStk' :
  forall vl,  can_change_aop (ARootTaskStk' vl).
Proof.
  intros.
  unfold ARootTaskStk'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ARootTaskStk': can_change_aop.

Lemma can_change_aop_ARootTaskStk :
  forall vl abs,  can_change_aop (ARootTaskStk vl abs).
Proof.
  intros.
  unfold ARootTaskStk.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_ARootTaskStk: can_change_aop.

Lemma can_change_aop_AOSPortAttrTbl' :
  forall vl,  can_change_aop (AOSPortAttrTbl' vl).
Proof.
  intros.
  unfold AOSPortAttrTbl'.
  can_change_aop_solver.
Qed.

Hint Resolve  can_change_aop_AOSPortAttrTbl': can_change_aop.

(* end add by CNU *)

Lemma can_change_aop_PartitionInv: forall ecbls,can_change_aop (PartitionInv ecbls).
Proof. intros; unfold PartitionInv; can_change_aop_solver. Qed.
Hint Resolve can_change_aop_PartitionInv  : can_change_aop.

Lemma can_change_aop_CapabilityInv: 
  forall acspace, can_change_aop (CapabilityInv acspace).
Proof. 
  intros.
  unfold CapabilityInv.
  can_change_aop_solver.
  unfold AOSCSpacePrioTbl.
  can_change_aop_solver.
  eapply can_change_aop_ACSpaceAarrayTptr.
  unfold AOSCSpaceObjectPointer.
  can_change_aop_solver.
  unfold AOSCSpaceCapParent.
  can_change_aop_solver.
  unfold CSpaceGVars.
  can_change_aop_solver.
Qed.
Hint Resolve can_change_aop_CapabilityInv  : can_change_aop.


Theorem can_change_aop_OSQInv :
  can_change_aop OSInv.
Proof.
  unfold OSInv.
  can_change_aop_solver.  
Qed.


Close Scope code_scope.
