

(** this file contains the simulations used to proof our logic soundness, we build three levels of simulations to support mudular reasoning of function calls and interrupts  **)

Require Import include_frm.
Require Import int_lock.


(* high level abortion due to assertion (actually assumption) failure *) 
Definition absabt (T: tasks) :=
  exists t ke ks, get T t = Some ((curs (hapi_code spec_abort)), (ke, ks)).

Inductive hpsteps:
  hprog -> tasks -> clientst -> osabst -> tasks -> clientst -> osabst -> Prop :=
| hpsteps_O (p:hprog) (T:tasks) (cst:clientst) O: 
  hpsteps p T cst O  T cst O 
| hpsteps_S p T T' T'' cst cst' cst'' O O' O'':
  hpstep p T cst O T' cst' O' ->
  hpsteps p T' cst' O'  T'' cst'' O''-> 
  hpsteps p T cst O T'' cst'' O'' 
| hpsteps_S_ev p T T' T'' cst cst' cst'' O O' O'' ev:
  hpstepev p T cst O T'' cst'' O'' ev ->
  hpsteps p T'' cst'' O'' T' cst' O' ->
  hpsteps p T cst O T' cst' O'.

Definition prgabsabt (p: hprog) (T: tasks) (cst: clientst) (O: osabst) :=
  exists T' cst' O', hpsteps p T cst O T' cst' O' /\ absabt T'.


CoInductive ProgSim :   lprog -> tasks -> osstate  -> hprog -> tasks -> osabst -> clientst -> tid -> Prop:=
| prog_sim:
    forall (pl:lprog) (ph:hprog) (Tl Th:tasks) (S:osstate) (O:osabst) (cst:clientst) t,
      get O curtid = Some (oscurt t) ->
      (
        forall Tl' S' cst' t', 
          lpstep pl Tl cst S t Tl' cst' S' t'->
          ~prgabsabt ph Th cst O -> 
          exists Th' O', hpstepstar ph Th cst O Th' cst' O' /\
                         (ProgSim pl Tl' S' ph Th' O' cst' t')
      ) ->
      (
        forall Tl' S' cst' ev t', 
          lpstepev pl Tl cst S t Tl' cst' S' t' ev ->
          ~prgabsabt ph Th cst O -> 
          exists Th' O', hpstepevstar ph Th cst O Th' cst' O' ev /\
                         (ProgSim pl Tl' S' ph Th' O' cst' t' )
      )->
      (
        lpstepabt pl Tl cst S t->
        ~prgabsabt ph Th cst O -> 
        hpstepabtstar ph Th cst O 
      )
      -> ProgSim pl Tl S ph Th O cst t.

Definition reltaskpred := prod taskst osabst -> Prop.


(*  (EX tp : type, GV OSTCBCur @ Tptr tp |-r-> Vptr t) ** p t lg ** [|GoodLInvAsrt p|].*)

Definition getmem (o:taskst) :=  get_mem (get_smem o).

Definition getapi (pl : lprog) := (fst (fst (snd pl))).

Definition getifun (pl : lprog) := (snd (fst (snd pl))).

Definition getsched (ph: hprog) := (snd (snd ph)).


Definition joinm2 o M1 M2  o' :=   exists o1,  joinmem o M1  o1 /\  joinmem o1 M2 o' .


Inductive htsteps:
  hprog -> tid -> code -> clientst -> osabst -> code -> clientst -> osabst -> Prop :=
| htsteps_O p t c cst O:
  htsteps p t c cst O c cst O
| htsteps_S p t c c' c'' cst cst' cst'' O O' O'':  
  htstep p t c cst O c'' cst'' O'' ->
  htsteps p t c'' cst'' O'' c' cst' O' ->
  htsteps p t c cst O c' cst' O'
| htsteps_S_ev p t c c' c'' cst cst' cst'' O O' O'' ev:
  htstepev p t c cst O c'' cst'' O'' ev ->
  htsteps p t c'' cst'' O'' c' cst' O' ->
  htsteps p t c cst O c' cst' O'.
            
Definition tskabsabt (p: hprog) (c: code) (cst: clientst) (O: osabst) t :=
  exists ke' ks' cst' O',
    htsteps p t c cst O (curs (hapi_code spec_abort), (ke', ks')) cst' O'. 


CoInductive TaskSim: 
  lprog -> code -> taskst -> hprog -> code -> osabst -> 
  LocalInv -> Inv -> reltaskpred -> tid -> Prop :=
| task_sim :
    forall (pl:lprog) (ph:hprog) (Cl Ch:code) (o:taskst) (O:osabst)
           (t:tid) lasrt (I:Inv) (P:reltaskpred),
      (
        forall Cl' Ms Mf cst cst' o'' Os  o2  OO, 
          satp (substaskst o  Ms) Os (INV I)->
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          ltstep pl t Cl cst o2 Cl' cst' o'' ->
          ~tskabsabt ph Ch cst OO t ->
          (
            exists Ch' OO'  o'  Ms'  O' Os', 
              htstepstar ph t Ch cst OO Ch' cst' OO'/\
              joinm2 o' Ms' Mf o'' /\ 
              join O' Os' OO' /\ 
              satp (substaskst o' Ms') Os' (INV I) /\
              satp  o' O' (CurLINV lasrt t)  /\
              TaskSim pl Cl' o' ph Ch' O'  lasrt I P t
          )
      )->
      (
        forall Cl' Ms Mf cst cst' o'' Os  o2  OO ev, 
          satp (substaskst o  Ms) Os (INV I)->
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          ltstepev pl t Cl cst o2 Cl' cst' o'' ev->
          ~tskabsabt ph Ch cst OO t ->
          (
            exists Ch' OO'  o'  Ms'  O' Os', 
              htstepevstar ph t Ch cst OO Ch' cst' OO' ev /\
              joinm2 o' Ms' Mf o'' /\ 
              join O' Os' OO' /\ 
              satp (substaskst o' Ms') Os' (INV I) /\
              satp  o' O' (CurLINV lasrt t)  /\
              TaskSim pl Cl' o' ph Ch' O'  lasrt I P t
          )
      )->  
      (
        forall   Ms ks x Os OO, 
          Cl = (curs (sprim (switch x)), (kenil, ks)) ->
          (*InOS Cl (pumerge (getapi pl) (getifun pl))->*)
          satp (substaskst o Ms)  Os  (INV I) ->                                          
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          (exists cst, ~tskabsabt ph Ch cst OO t) ->
          (
            exists Ch' s k  OO'  Mc ol O' Os' Ol Oc , 
              Ch' = (curs (hapi_code (spec_seq sched s)),k) /\
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO')  /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc O' /\
              satp (substaskst o Ms) Os'  (INV I) /\
              satp  (substaskst o Mc) Oc (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD (getsched ph) x t) /\
                  (
                    forall Mc' Oc' o' O'', 
                      satp  (substaskst o Mc') Oc' (SWINVt I t) ->
                      joinmem ol Mc' o' ->
                      join Ol Oc' O'' ->
                      TaskSim pl  (SKIP, (kenil, ks))  o'  ph (curs (hapi_code s),k) O''  lasrt I P t
                  )
                )
                \/
                
                satp (substaskst o Mc) Oc (SWPRE_DEAD (getsched ph) x t)  
              )
          )
      )->
      (*
      (
        forall  Ms ks x Os OO, 
          Cl = (curs (sprim (switch x)), (kenil, ks)) ->
          InOS Cl (pumerge (getapi pl) (getifun pl))->
          satp (substaskst o  Ms) Os  (INV I) ->  
          disjoint (getmem o) Ms -> 
          join O Os OO  ->
          (
            exists Ch' s k OO' Mc ol O' Os' Ol Oc,  
              Ch' = (curs (hapi_code (spec_seq sched s)),k) /\
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO') /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc  O' /\
              satp (substaskst o Ms) Os'  (INV I) /\
              satp (substaskst o Mc) Oc  (SWINVt I t) /\ 
              satp (substaskst o Mc) Oc (SWPRE_DEAD t)  /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue)            
          )
      )->*)
      (
        forall Ms Os OO,  
          IsEnd Cl -> 
          satp (substaskst o Ms) Os  (INV I) ->   
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          (exists cst, ~tskabsabt ph Ch cst OO t) ->
          (
            exists O' Os' Ch OO', 
              IsEnd Ch /\
              (forall cst, htstepstar ph t Ch cst OO Ch cst OO') /\
              join O' Os' OO'/\
              satp (substaskst o  Ms) Os' (INV I) /\
              satp o O (CurLINV lasrt t) /\
              P (o, O')
          )
      )->
      (
        forall cst o' Ms Os Mf OO Of OOO,
          ~(IsEnd Cl) ->
          ~(IsSwitch Cl) ->
          ~(IsStkInit Cl)->
          ~(IsStkFree Cl) ->
          satp (substaskst o Ms)  Os  (INV I) ->
          joinm2 o Ms  Mf o' ->
          join O Os OO ->
          join OO Of OOO ->
          ltstepabt pl t Cl cst o' ->
          ~tskabsabt ph Ch cst OOO t ->
          htstepabtstar ph t Ch cst OOO
      )->
      (
        forall  Ms Os e1 e2 e3 ks OO, 
          Cl = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          (exists cst, ~tskabsabt ph Ch cst OO t) ->
          (
            exists Ch'  v1 v2  t' p s k   OO' OO''  ,
              exists ol Mcre O' Os' Ol Ocre ,
                Ch' = (curs (hapi_code (spec_seq (spec_crt v1 v2 (Vint32 p)) s)), k) /\
                evalval e1 (get_smem o) = Some v1  /\
                evalval e2 (get_smem o) = Some v2 /\ 
                evalval e3 (get_smem o) = Some (Vptr t') /\
                (forall cst, htstepstar ph t Ch cst OO Ch' cst OO')  /\
                abs_crt_step OO' OO'' t t' p /\
                joinmem ol Mcre o /\
                join O' Os' OO'' /\
                join Ol Ocre O' /\
                satp (substaskst o Ms) Os' (INV I) /\
                satp ol Ol (CurLINV lasrt t) /\
                satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
                TaskSim pl  (SKIP,(kenil,ks))  ol ph  (curs (hapi_code s),k) Ol  lasrt I P t
          )
      )->       
      (*
      (
        forall Cl  Ms  Os e ks OO, 
          Cl = (curs (sprim (stkfree e)),(kenil,ks))->
          evalval e (get_smem o) = Some (Vptr t) ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os OO->
          (
            exists Ch' p s k  OO' OO'' O' Os',
              Ch' = (curs (hapi_code (spec_seq (spec_del (Vint32 p)) s)),k) /\
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO')  /\
              abs_delself_step OO' OO'' t p /\
              join O' Os' OO'' /\ 
              satp (substaskst o Ms) Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              TaskSim pl (SKIP ,(kenil,ks))  o ph  (curs (hapi_code s),k)   O' lasrt I P t
          )
      )->
       *)
      (
        forall Ms  Os e ks  OO, 
          Cl = (curs (sprim (stkfree e)),(kenil,ks))->
          satp (substaskst o Ms) Os  (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os  OO->
          (exists cst, ~tskabsabt ph Ch cst OO t) ->
          (
            exists Ch' p s k t' OO' OO''  O' Os' ,
              Ch' = (curs (hapi_code (spec_seq (spec_del (Vint32 p)) s)),k) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              (forall cst, htstepstar ph t Ch cst OO Ch' cst OO') /\
              (
                (
                  abs_delself_step OO' OO'' t t' p /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os' (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  TaskSim pl (SKIP ,(kenil,ks))  o ph  (curs (hapi_code s),k)   O' lasrt I P t
                )
                \/
                (
                  abs_delother_step OO' OO'' t t' p /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os' (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  forall o' O'' Mdel Odel,
                    (
                      satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                      joinmem o Mdel o' ->
                      join O' Odel O'' ->
                      TaskSim pl  (SKIP, (kenil,ks))  o' ph  (curs (hapi_code s),k)  O''  lasrt I P t
                    )
                )
              )
          )
      )->       
      TaskSim pl Cl o ph Ch O  lasrt I P t.


Definition TaskSimAsrt  
           (pl:lprog) (Cl:code) (ph:hprog) (Ch:code) 
           (t:tid) lasrt (I:Inv) (P:reltaskpred):Prop:=
  forall (o:taskst) (O:osabst), 
    P (o, O)  /\  satp o O (CurLINV lasrt t)  -> TaskSim pl Cl o ph Ch O lasrt I P t.

(*
Definition TcbBJ (tls : TcbMod.map) := 
  (
    forall t t' pr a pr' a' msg msg', 
     t<>t' -> 
     get tls t = Some (pr,a,msg)->
     get tls t' = Some (pr',a',msg') -> 
     pr <>   pr'
  )
  /\
  (
    forall t t' pr a pr' a' msg msg',
     pr<>pr' -> 
     get tls t = Some (pr,a,msg) ->
     get tls t' = Some (pr',a',msg') ->
     t <> t'
  ).
 *)


Definition notabort (C:code):=
  ~IsSwitch C /\ ~IsEnd C /\ 
  ~ IsRet C /\ ~IsRetE C /\ ~IsIRet C /\ 
  ~IsStkInit C /\
  ~IsStkFree C.

Definition rawLoststep (C:code):=
  ~IsDint C /\ ~IsDintp C /\ ~IsRint C /\ ~IsRintp C /\ ~ IsSgenerateipc C /\
  ~ IsSclearipc C /\ ~ IsSgetsem C /\ ~ IsSpostsem C /\
  ~ IsScslsemacc C /\ ~ IsScslsemrel C /\
  ~ IsScsl_msmc_getSMSMPAXL C /\ ~ IsScsl_msmc_setSMSMPAXL C /\ 
  ~ IsScsl_msmc_getSESMPAXL C /\ ~ IsScsl_msmc_setSESMPAXL C /\
  ~ IsScsl_xmc_getXMPAXL C /\ ~ IsScsl_xmc_setXMPAXL C /\
  ~ IsScsl_msmc_setSMSMPAXH C /\ ~ IsScsl_msmc_setSESMPAXH C /\
  ~ IsScsl_xmc_setXMPAXH C /\
  ~ IsScsl_xmc_clearFault C /\ ~ IsScsl_cgem_clearMDMAError C.

Definition notabortm (C:code):= ~IsFcall C /\ notabort C.

Definition IsDintpp (C:code) irqLine := (exists ks, C = (curs (sprim (dintp irqLine)),(kenil,ks))).

CoInductive MethSimMod : funspec -> ossched ->  code -> taskst -> absop -> osabst  -> LocalInv ->
                         Inv -> retasrt -> asrt -> retasrt -> tid -> Prop :=
| meth_sim_mod :
    forall (spec :funspec) sd (C:code)  
           (gamma:absop) (O:osabst) t lasrt (I:Inv)
           (r q : retasrt) (ri: asrt)  (o:taskst) ,
      (
        forall p C' Ms Mf Os OO o2 o2',
          ~IsFcall C ->
          rawLoststep C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO'  o' Ms'  O' Os', 
              hmstepstar sd gamma OO gamma' OO' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO' /\
              satp (substaskst o'  Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' gamma' O' lasrt I r ri q t
          )
      )->
      (
        forall Ms Os ks f vl tl OO,
          C = (curs (sfexec f vl tl), (kenil,ks)) ->
          satp (substaskst o  Ms) Os (INV I)->
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ( 
            exists gamma' OO' om M O' Os' Ot Of ,
              exists pre post tp logicl,
                hmstepstar sd gamma OO gamma' OO' /\
                joinmem om M o /\
                join O' Os' OO' /\
                join Ot Of O'/\
                tl_vl_match tl vl = true /\
                spec f = Some (pre, post,  (tp ,List.rev tl)) /\
                sat (om, Ot, gamma') (getasrt (pre (rev vl) logicl t)) /\ 
                satp om Ot (CurLINV lasrt t) /\ 
                satp (substaskst o Ms) Os' (INV I) /\
                (
                  forall o1 O1  v gamma'', 
                    sat (o1,O1,gamma'') (getasrt (post (rev vl) v logicl t)) ->
                    (
                      satp o1 O1 (CurLINV lasrt t) /\ 
                      (
                        forall o' O'',
                          (* satp o' O'' (CurLINV lasrt t) -> *)
                          joinmem o1 M o' ->
                          join O1 Of O'' ->
                          eqenv o o' ->
                          MethSimMod spec sd (curs (sskip v), (kenil,ks)) o' gamma'' O'' lasrt I r ri q t 
                      )
                    )
                )
          )
      )->
      (*
      (
        forall  Ms ks x Os OO, 
          C = (curs (sprim (switch x)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          (
            exists gamma' s OO' ol Mc O' Os' Ol Oc, 
              gamma' = spec_seq sched s /\
              hmstepstar sd gamma OO gamma' OO' /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc O' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp (substaskst o Mc)  Oc (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              satp (substaskst o Mc) Oc (SWPRE sd x t)  /\
              (
                forall Mc' Oc' o' O'', 
                  satp (substaskst o  Mc') Oc' (SWINVt I t)->
                  joinmem ol Mc' o' ->
                  join Ol Oc' O'' ->
                  MethSimMod spec sd (SKIP, (kenil, ks))  o' s O'' lasrt I r ri q t 
              )
          )
      )->*)
      (
        forall Ms ks x Os OO, 
          C = (curs (sprim (switch x)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' s OO' ol Mc O' Os' Ol Oc,  
              gamma' = spec_seq sched s /\
              hmstepstar sd gamma OO gamma' OO' /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc  O' /\
              satp (substaskst o Ms) Os'  (INV I) /\
              satp (substaskst o Mc) Oc  (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD sd x t)  /\
                  (
                    forall Mc' Oc' o' O'', 
                      satp (substaskst o  Mc') Oc' (SWINVt I t)->
                      joinmem ol Mc' o' ->
                      join Ol Oc' O'' ->
                      MethSimMod spec sd (SKIP, (kenil, ks))  o' s O'' lasrt I r ri q t 
                  ) 
                )

                \/

                satp (substaskst o Mc) Oc  (SWPRE_DEAD sd x t) 
              )
          )
      )->

      (
        forall v Ms Os OO, 
          C = (curs (sskip v), (kenil, kstop)) ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (q v) 
          )
      )->

      (
        forall ks Os Ms OO,
          C = (curs sret, (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (r None)
          )
      )->

      (
        forall ks Os Ms v OO,
          C = ([v], (kenil, (kret ks))) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'), gamma')  (r (Some v)) 
          )
      )->
      
      (
        forall ks Os Ms OO,
          C = (curs (sprim exint), (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists  gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') ri 
          )
      )->
      (
        forall p Os Ms Mf o2 OO,  
          notabortm C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 ->
          disjoint O Os ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ~ (loststepabt p C o2)
      )->
      (
        forall  Ms Os e1 e2 e3 ks  OO, 
          C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' v1 v2 t' p s  OO'  OO'' ol , 
              exists Mcre O' Os' Ol Ocre ,
                gamma' = (spec_seq (spec_crt v1 v2 (Vint32 p)) s) /\
                evalval e1 (get_smem o) = Some v1 /\
                evalval e2 (get_smem o) = Some v2 /\ 
                evalval e3 (get_smem o) = Some (Vptr t') /\
                hmstepstar sd gamma OO gamma' OO' /\
                abs_crt_step OO' OO'' t t' p /\
                joinmem ol Mcre o /\
                join O' Os' OO'' /\
                join Ol Ocre O' /\
                satp (substaskst o Ms) Os' (INV I) /\
                satp ol Ol (CurLINV lasrt t) /\
                satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
                MethSimMod spec sd  (SKIP, (kenil,ks))  ol s Ol lasrt I r ri q t
          )
      )->
      (
        forall  Ms Os e ks OO, 
          C = (curs (sprim (stkfree e)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os OO->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' p s t'  OO' ,
              gamma' = (spec_seq (spec_del (Vint32 p)) s) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              hmstepstar sd gamma OO gamma' OO' /\
              (
                ( 
                  exists OO'' O' Os', 
                    abs_delself_step OO' OO'' t t' p /\
                    join O' Os' OO'' /\ 
                    satp (substaskst o Ms) Os'  (INV I) /\
                    satp o O' (CurLINV lasrt t) /\
                    MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
                ) 
                \/ 
                (
                  exists OO'' O' Os', 
                    abs_delother_step OO' OO'' t t' p /\
                    join O' Os' OO'' /\ 
                    satp (substaskst o Ms) Os' (INV I) /\
                    satp o O' (CurLINV lasrt t) /\
                    forall o' O'' Mdel Odel,
                      (
                        satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                        joinmem o Mdel o' ->
                        join O' Odel O'' ->
                        MethSimMod spec sd  (SKIP, (kenil,ks))  o' s O''  lasrt I r ri q t
                      )
                )
              )
          )
      )->
      (*
      (
        forall  Ms Os e ks t' OO, 
          C = (curs (sprim (stkfree e)),(kenil,ks))->
          evalval e (get_smem o) = Some (Vptr t') ->
          satp (substaskst o Ms) Os  (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os  OO->
          (
            exists gamma' p s OO' OO'' O' Os' ,
              gamma' = (spec_seq (spec_del (Vint32 p)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_delother_step OO' OO' t t' p /\
              join O' Os' OO'' /\ 
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              forall o' O'' Mdel Odel,
                (
                  satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                  joinmem o Mdel o' ->
                  join O' Odel O'' ->
                  MethSimMod spec sd  (SKIP, (kenil,ks))  o' s O''  lasrt I r ri q t
                )
          )
      )->
       *)
       (
        forall p C' Ms Mf Os OO o2 o2' irqLine ks le m b x,
          C = (curs (sprim (dintp irqLine)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le irqLine = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms' O' Os', 
              gamma' = (spec_seq (int_disable_pic_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_dintp_step OO' OO'' (Z.to_nat (Int.unsigned x)) /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' s O' lasrt I r ri q t
          )
      )->
      (
        forall p C' Ms Mf Os OO o2 o2' irqLine ks le m b x,
          C = (curs (sprim (rintp irqLine)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le irqLine = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms'  O' Os', 
              gamma' = (spec_seq (int_enable_pic_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_rintp_step OO' OO'' (Z.to_nat (Int.unsigned x)) /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' s O' lasrt I r ri q t
          )
      )->
      (
        forall p C' Ms Mf Os OO o2 o2' level ks,
          C = (curs (sprim (dint level)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' OO'' o' Ms'  O' Os' er, 
              gamma' = (int_lock_aop(|nil|)) /\
              hmstepstar sd gamma OO gamma' OO' /\
              getier o = er /\
              abs_dint_step OO' OO'' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' (END (Some (Vint32(getLevel er intStart Int.zero intStartInt)))) O' lasrt I r ri q t
          )
      )->
      (
        forall p C' Ms Mf Os OO o2 o2' level ks le m b x,
          C = (curs (sprim (rint level)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le level = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms'  O' Os', 
              gamma' = (spec_seq (int_unlock_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_rint_step OO' OO'' x /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSimMod spec sd C' o' s O' lasrt I r ri q t
          )
      )->
           (
        forall Ms ks  Os OO e1 e2  , 
          C = (curs (sprim (sgenerateipc e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' n m s  OO'  O' Os' Ms',  
              evaltype e1 (get_smem o) = Some Tint8 /\
             evaltype e2 (get_smem o) = Some Tint32 /\
            evalval e1 (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat n)))) /\
            evalval e2 (get_smem o) = Some m /\
             m <> Vundef /\
            (Z.of_nat n <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (coreint n m) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
        
      )->
                (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (sgetsem e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
            (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (getsem i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
        
      )->
                (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (spostsem e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
             (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (postsem i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
      )->
        (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (sclearipc e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             gamma' = spec_seq (clearipc n m) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (clearipc n m) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t) 
      )->
        (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_semaccdir e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' o'  Ms' O' Os',  
             gamma' = spec_seq (cslsemacc n m) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t) 
      )->
        (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (scsl_semrel e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
             (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (cslsemrel i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSimMod spec sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
      )->
        (* new add *)
        (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_getSMSMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l, 
             gamma' = spec_seq (csl_msmc_getSMSMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_getSMSMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSMSMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSMSMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSMSMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_getSESMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l, 
             gamma' = spec_seq (csl_msmc_getSESMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_getSESMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSESMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSESMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSESMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_getXMPAXL e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
             exists l, 
             gamma' = spec_seq (csl_xmc_getXMPAXL n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_getXMPAXL n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_setXMPAXL e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_xmc_setXMPAXL n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_setXMPAXL n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSMSMPAXH e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSMSMPAXH n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSMSMPAXH n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSESMPAXH e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSESMPAXH n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSESMPAXH n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall p C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_setXMPAXH e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_xmc_setXMPAXH n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_setXMPAXH n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
(
        forall p C' Ms Mf ks Os OO o2  o2',
          C = (curs (sprim (scsl_xmc_clearFault)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' s  OO' OO'' o'  Ms' O' Os',
             gamma' = spec_seq (csl_xmc_clearFault) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_clearFault) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           )
      )->
(
        forall p C' Ms Mf ks Os OO o2  o2',
          C = (curs (sprim (scsl_cgem_clearMDMAError)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' s  OO' OO'' o'  Ms' O' Os',
             gamma' = spec_seq (csl_cgem_clearMDMAError) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_cgem_clearMDMAError) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSimMod spec sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      MethSimMod spec sd C o gamma O lasrt I r ri q t.

Notation "  '{[' p , sd , li , I , r , ri , q  ']}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSimMod p sd  C o gamma O li I r ri q t) (at level 200).     


CoInductive MethSim : progunit -> ossched -> code -> taskst -> absop -> osabst -> LocalInv ->
                      Inv -> retasrt -> asrt -> retasrt -> tid -> Prop :=
| meth_sim :
    forall (p:progunit) sd (C:code)
           (gamma:absop) (O:osabst) (I:Inv)
           (r q: retasrt) (ri: asrt)  (o:taskst) t lasrt,
      (
        forall  C' Ms Mf Os OO o2 o2',
          rawLoststep C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO'  o' Ms'  O' Os', 
              hmstepstar sd gamma OO gamma' OO' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO' /\
              satp (substaskst o'  Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' gamma' O' lasrt I r ri q t
          )
      )->
      (
        forall  Ms ks x Os OO, 
          C = (curs (sprim (switch x)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' s OO' ol Mc O' Os' Ol Oc, 
              gamma' = spec_seq sched s /\
              hmstepstar sd gamma OO gamma' OO' /\
              joinmem ol Mc o /\
              join O' Os' OO'/\
              join Ol Oc O' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp (substaskst o Mc)  Oc (SWINVt I t) /\
              satp ol Ol  (EX lg', LINV lasrt t lg' ** Atrue) /\
              (
                (
                  satp (substaskst o Mc) Oc (SWPRE_NDEAD sd x t)  /\
                  (
                    forall Mc' Oc' o' O'', 
                      satp (substaskst o  Mc') Oc' (SWINVt I t)->
                      joinmem ol Mc' o' ->
                      join Ol Oc' O'' ->
                      MethSim p sd (SKIP, (kenil, ks))  o' s O'' lasrt I r ri q t 
                  )
                )
                \/
                
                satp (substaskst o Mc) Oc (SWPRE_DEAD sd x t)
              )
          )
      )->
      (
        forall v Ms Os OO, 
          C = (curs (sskip v), (kenil, kstop)) ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (q v) 
          )
      )->
      (
        forall ks Os Ms OO,
          C = (curs sret, (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I)->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') (r None)
          )
      )->
      (
        forall ks Os Ms v OO,
          C = ([v], (kenil, (kret ks))) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'), gamma')  (r (Some v)) 
          )
      )->
      (
        forall ks Os Ms OO,
          C = (curs (sprim exint), (kenil, ks)) ->
          callcont ks = None -> 
          intcont ks =None ->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists  gamma' OO' O' Os',
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms) Os' (INV I)/\
              satp o O' (CurLINV lasrt t) /\
              sat ((o, O'),gamma') ri 
          )
      )->
      (
        forall  Os Ms Mf o2 OO,   
          notabort C ->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 ->
          disjoint O Os ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          ~ (loststepabt p C o2)
      )->
      (
        forall  Ms Os e1 e2 e3 ks  OO, 
          C = (curs (sprim (stkinit e1 e2 e3)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms ->
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' v1 v2 t' pri s  OO'  OO'' ol , 
              exists Mcre O' Os' Ol Ocre ,
                gamma' = (spec_seq (spec_crt v1 v2 (Vint32 pri)) s) /\
                evalval e1 (get_smem o) = Some v1 /\
                evalval e2 (get_smem o) = Some v2  /\  
                evalval e3 (get_smem o) = Some (Vptr t')  /\
                hmstepstar sd gamma OO gamma' OO' /\
                abs_crt_step OO' OO'' t t' pri /\
                joinmem ol Mcre o /\
                join O' Os' OO'' /\
                join Ol Ocre O' /\
                satp (substaskst o Ms) Os' (INV I) /\
                satp ol Ol (CurLINV lasrt t) /\
                satp (substaskst o Mcre) Ocre (lasrt t' init_lg**[|GoodLInvAsrt lasrt|]) /\
                MethSim p sd  (SKIP, (kenil,ks))  ol s Ol lasrt I r ri q t
          )
      )->
      (
        forall  Ms Os e ks OO, 
          C = (curs (sprim (stkfree e)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          disjoint (getmem o) Ms  ->
          join O Os OO->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' pri s t'  OO' OO'' O' Os' ,
              gamma' = (spec_seq (spec_del (Vint32 pri)) s) /\
              evalval e (get_smem o) = Some (Vptr t')  /\ 
              hmstepstar sd gamma OO gamma' OO' /\
              (
                (
                  abs_delself_step OO' OO'' t t' pri /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os'  (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  MethSim  p  sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
                ) 
                \/ 
                (
                  abs_delother_step OO' OO'' t t' pri /\
                  join O' Os' OO'' /\ 
                  satp (substaskst o Ms) Os' (INV I) /\
                  satp o O' (CurLINV lasrt t) /\
                  forall o' O'' Mdel Odel,
                    (
                      satp (substaskst o Mdel) Odel  (EX lg, LINV lasrt t' lg)  ->
                      joinmem o Mdel o' ->
                      join O' Odel O'' ->
                      MethSim  p  sd  (SKIP, (kenil,ks))  o' s O''  lasrt I r ri q t
                    )
                )
              )
          )
      )->
      (
        forall C' Ms Mf Os OO o2 o2' irqLine ks le m b x,
          C = (curs (sprim (dintp irqLine)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') ->           
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le irqLine = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms'  O' Os', 
              gamma' = (spec_seq (int_disable_pic_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_dintp_step OO' OO'' (Z.to_nat (Int.unsigned x)) /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' s O' lasrt I r ri q t
          )
      )->
      (
        forall C' Ms Mf Os OO o2 o2' irqLine ks le m b x,
          C = (curs (sprim (rintp irqLine)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le irqLine = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms'  O' Os', 
              gamma' = (spec_seq (int_enable_pic_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_rintp_step OO' OO'' (Z.to_nat (Int.unsigned x)) /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' s O' lasrt I r ri q t
          )
      )->
      (
        forall C' Ms Mf Os OO o2 o2' level ks,
          C = (curs (sprim (dint level)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' OO' OO'' o' Ms'  O' Os' er, 
              gamma' = (int_lock_aop(|nil|)) /\
              hmstepstar sd gamma OO gamma' OO' /\
              getier o = er /\
              abs_dint_step OO' OO'' /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' (END (Some (Vint32(getLevel er intStart Int.zero intStartInt)))) O' lasrt I r ri q t
          )
      )->
      (
        forall C' Ms Mf Os OO o2 o2' level ks le m b x,
          C = (curs (sprim (rint level)),(kenil,ks))->
          satp (substaskst o Ms) Os (INV I) ->
          joinm2 o Ms Mf o2 -> 
          join O Os OO ->
          loststep p C o2 C' o2' -> 
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          get_lenv(get_smem o2) = le ->
          get_mem (get_smem o2) = m ->
          get le level = Some (b,Tint32) -> 
          load Tint32 m (b,0%Z) = Some (Vint32 x) ->
          (
            exists gamma' s OO' OO'' o' Ms'  O' Os', 
              gamma' = (spec_seq (int_unlock_aop(|nil|)) s) /\
              hmstepstar sd gamma OO gamma' OO' /\
              abs_rint_step OO' OO'' x /\
              joinm2 o' Ms' Mf o2' /\ 
              join O' Os' OO'' /\
              satp (substaskst o Ms') Os' (INV I)/\
              satp o' O' (CurLINV lasrt t) /\
              MethSim p sd C' o' s O' lasrt I r ri q t
          )
      )->
          (
        forall Ms ks  Os OO e1 e2  , 
          C = (curs (sprim (sgenerateipc e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' n m s  OO'  O' Os' Ms',  
              evaltype e1 (get_smem o) = Some Tint8 /\
             evaltype e2 (get_smem o) = Some Tint32 /\
            evalval e1 (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat n)))) /\
            evalval e2 (get_smem o) = Some m /\
             m <> Vundef /\
            (Z.of_nat n <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (coreint n m) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSim p sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              ) 
              )->
         (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (sgetsem e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
            (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (getsem i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSim p sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
        
      )->
                (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (spostsem e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
             (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (postsem i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSim  p sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
      )->
    (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (sclearipc e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             gamma' = spec_seq (clearipc n m) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (clearipc n m) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_semaccdir e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' o'  Ms' O' Os',  
             gamma' = spec_seq (cslsemacc n m) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall Ms ks  Os OO e , 
          C = (curs (sprim (scsl_semrel e)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          disjoint (getmem o) Ms -> 
          join O Os OO ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
            exists gamma' i s  OO'  O' Os' Ms',  
              evaltype e (get_smem o) = Some Tint8 /\
              evalval e (get_smem o) = Some (Vint32 ((Int.repr (Z.of_nat i)))) /\
             (Z.of_nat i <= Int.max_unsigned )%Z /\
              gamma' = spec_seq (cslsemrel i) s /\
              hmstepstar sd gamma OO gamma' OO' /\
              join O' Os' OO' /\
              satp (substaskst o Ms') Os'  (INV I) /\
              satp o O' (CurLINV lasrt t) /\
              MethSim  p sd  (SKIP, (kenil,ks))  o s O' lasrt I r ri q t
              )
      )->
        (* new add *)
        (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_getSMSMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_msmc_getSMSMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_getSMSMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSMSMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_msmc_setSMSMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSMSMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_getSESMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_msmc_getSESMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_getSESMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSESMPAXL e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_msmc_setSESMPAXL n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSESMPAXL n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_getXMPAXL e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_xmc_getXMPAXL n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_getXMPAXL n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall  C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_setXMPAXL e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
              exists l,
             gamma' = spec_seq (csl_xmc_setXMPAXL n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_setXMPAXL n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t) 
      )->
      (
        forall C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSMSMPAXH e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSMSMPAXH n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSMSMPAXH n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall C' Ms Mf ks Os OO o2  o2' e1 e2 e3, 
          C = (curs (sprim (scsl_msmc_setSESMPAXH e1 e2 e3)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n m s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_msmc_setSESMPAXH n m l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_msmc_setSESMPAXH n m l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall C' Ms Mf ks Os OO o2  o2' e1 e2, 
          C = (curs (sprim (scsl_xmc_setXMPAXH e1 e2)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' n s  OO' OO'' o'  Ms' O' Os',  
             exists l,
             gamma' = spec_seq (csl_xmc_setXMPAXH n l) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_setXMPAXH n l) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
(
        forall C' Ms Mf ks Os OO o2  o2', 
          C = (curs (sprim (scsl_xmc_clearFault)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' s  OO' OO'' o'  Ms' O' Os', 
             gamma' = spec_seq (csl_xmc_clearFault) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_xmc_clearFault) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      (
        forall C' Ms Mf ks Os OO o2  o2', 
          C = (curs (sprim (scsl_cgem_clearMDMAError)), (kenil, ks)) ->
          satp (substaskst o Ms) Os (INV I)-> 
          joinm2 o Ms Mf o2 ->
          join O Os OO ->
          loststep p C o2 C' o2' ->
          ~(exists OO', spec_stepstar sd gamma OO spec_abort OO') -> 
          (
           exists gamma' s  OO' OO'' o'  Ms' O' Os',
             gamma' = spec_seq (csl_cgem_clearMDMAError) s /\
             hmstepstar sd gamma OO  gamma' OO' /\
             spec_step sd (csl_cgem_clearMDMAError) OO' (END None) OO'' /\
             joinm2 o' Ms' Mf o2' /\
             join O' Os' OO'' /\
             satp (substaskst o Ms') Os'  (INV I) /\
             satp o' O' (CurLINV lasrt t) /\
             MethSim p sd  C'  o' s O' lasrt I r ri q t
           ) 
      )->
      MethSim p sd C o gamma O lasrt I r ri q t.



Lemma buldp_some_imp_gooddecl : forall dl vl p, buildp dl vl = Some p -> good_decllist dl = true .
Proof.
  introv Hbul.
  inductions dl.
  simpl; auto.
  simpl.
  simpl in Hbul.
  remember (negb (in_decllist i dl) && good_decllist dl) as H.
  apply sym_eq in HeqH.
  destruct H.
  auto.
  inverts Hbul.
Qed.


Definition RuleSem (spec : funspec) (sd : ossched) lasrt (I:Inv) (r:retasrt) (ri:asrt) 
           (p:asrt) (s:stmts)  (q:asrt) t :Prop:=
  forall o O aop,  (sat ((o, O),aop) p /\  satp o O  (CurLINV lasrt t))  -> 
                   MethSimMod spec sd (nilcont s) o aop O lasrt I r ri (lift q) t.


Definition MethSimAsrt (P : progunit) (sd:ossched) lasrt (I:Inv) (r:retasrt) (ri:asrt) 
           (p:asrt) (s:stmts)  (q:asrt) t :Prop:=
  forall o O aop, (sat ((o, O),aop) p /\  satp o O  (CurLINV lasrt t))  ->
                  MethSim P sd (nilcont s) o aop O lasrt I r ri (lift q) t.


Definition WFFuncsSim (P:progunit) (FSpec:funspec) (sd:ossched) lasrt (I:Inv) :Prop:=
  EqDom P FSpec /\
  forall f pre post t tl,
    FSpec f = Some (pre, post, (t, tl)) -> 
    exists  d1 d2 s,
      P f = Some (t, d1, d2, s)/\   
      tlmatch tl d1 /\
      good_decllist (revlcons d1 d2) = true /\ 
      (
        forall vl p r logicl tid,
          Some p = BuildPreI P f vl logicl pre tid-> 
          Some r = BuildRetI P f vl logicl post tid ->
          RuleSem FSpec sd lasrt I r Afalse p s Afalse tid
      ).



Definition WFFuncsSim' (P:progunit) (FSpec:funspec) (sd:ossched) lasrt (I:Inv) :Prop:=
  EqDom P FSpec /\
  forall f pre post t tl,
    FSpec f = Some (pre, post, (t, tl)) -> 
    exists  d1 d2 s,
      P f = Some (t, d1, d2, s)/\   
      tlmatch tl d1 /\
      good_decllist (revlcons d1 d2) = true /\ 
      (
        forall vl p r logicl tid,
          Some p = BuildPreI P f vl logicl pre tid -> 
          Some r = BuildRetI P f vl logicl post tid ->
          (
            forall o O aop,
              (o, O, aop) |= p /\ satp o O (CurLINV lasrt tid) -> 
              MethSim P sd (nilcont s) o aop O lasrt I r Afalse (lift Afalse) tid
          ) 
      ).

Notation " '[' Spec , sd , lasrt , I , r , ri  , n ']'  '|=' t '{{' pre  '}}' s '{{' post '}}' "
  := (RuleSem Spec sd lasrt I r ri pre s post n t) (at level 200).


Notation "  '{[' p , sd , lasrt , I , r , ri , q   ']}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSimMod p sd C o gamma O lasrt I r ri q t) (at level 200).     



Notation "  '{{[' p , sc , lasrt , I , r , ri , q ']}}'  '||-' t '(' C , o ')'  '<_msim' '(' gamma ,  O  ')' "
  :=  (MethSim p sc C o gamma O lasrt I r ri q t) (at level 201).    
