
Require Import memory. 
Require Import if_language.
Require Import if_opsem.

Require Import spec_aux_defs. 

Definition asrt_and_ret (vl: vallist) (O: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v1 v2, 
      vl = v1::v2::nil 
      /\ opv = Some v2 
      /\ act = TauAct 
      /\ (v1 = v2 /\ O_opt = Some O \/ v1 <> v2 /\ O_opt = None)
  end.   

(* qix_end is "1+(the largest index that can be used for a message queue EIB)" *) 
Parameter qidx_end: int.

Definition qpost_nowt_succ_body (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists qid msg v_ret,
      vl= (Vptr qid :: msg ::v_ret :: nil) /\
        (exists qls n ml pwl,
            opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
              act = TauAct /\
              get O1 absecblsid = Some (absecblist qls) /\
              get qls qid = Some (absmsgq ml n pwl, nil) /\
              Z.lt (Z_of_nat (length ml)) (Int.unsigned n) /\
              (v_ret = Vint32 (Int.repr OS_NO_ERR) /\
                 O_opt = Some ( set O1 absecblsid (absecblist (set qls qid (absmsgq (ml++(msg::nil)) n pwl,nil)))) \/
                 v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None))
  end.

Definition qpost_exwt_succ_body (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists qid msg v_ret,
      vl= (Vptr qid :: msg ::v_ret :: nil) /\
        (exists qls vl wl qls' t' tls tls' m sus,  
            exists p st n pwl pr,
              opv = None /\ act = TauAct /\  
                get O1 abstcblsid = Some (abstcblist tls) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get qls qid = Some (absmsgq vl n pwl,wl) /\
                GetHWait tls wl t'/\
                get tls t' = Some (p,st,m,sus,pr)/\
                tls'=set tls t' (p,rdy,msg,sus,pr)/\
                qls' = set qls qid (absmsgq nil n pwl,(remove_tid t' wl) )/\
                (v_ret = Vint32 (Int.repr OS_NO_ERR) /\
                   O_opt =Some ( set ( set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist qls') ) \/
                   v_ret <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None))
  end.


(* (************************************ q post  **************************************) *)
    
Definition mqdes_dom_qptr idx ptr (O: osabst) (pr: priority) :=
  mqidx_in_dom idx (dom_for_prio pr) = true
  /\ mq_ptr O idx ptr.  

Definition qpost (vl:vallist) :=
  match vl with
    (Vint32 mqd) :: v1 :: vmsg :: vret :: nil =>
      (
          Aif |(mqdes_dom_qptr mqd v1, nil)| (fun O => v1 = Vnull) {
            asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_PEVENT_NULL) :: nil |)
         } else {
          Aif (fun O => exists qid, v1 = Vptr qid /\ vmsg = Vnull) {
              asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_POST_NULL_PTR) :: nil |)
            } else {
            Aif (fun O => exists qid els, v1 = Vptr qid /\ vmsg <> Vnull
                                          /\ get O absecblsid = Some (absecblist els)
                                          /\ (~exists x y pwl wls, get els qid = Some (absmsgq x y pwl,wls))) { 
                asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_EVENT_TYPE) :: nil |)
              } else {
              Aif (fun O => exists qid qls ml n pwl wl, v1 = Vptr qid /\ vmsg <> Vnull 
                                                        /\ get O absecblsid = Some (absecblist qls)
                                                        /\ get qls qid = Some (absmsgq ml n pwl, wl) 
                                                        /\ Z.ge (Z_of_nat (length ml)) (Int.unsigned n)) {
                  asrt_and_ret (| vret :: Vint32 (Int.repr MSGQ_OVF_ERR) :: nil |)
                } else {
                Aif (fun O => exists qls qid ml n pwl, v1 = Vptr qid /\ vmsg <> Vnull
                                                       /\ get O absecblsid = Some (absecblist qls)
                                                       /\ get qls qid = Some (absmsgq ml n pwl, nil) 
                                                       /\ Z.lt (Z_of_nat (length ml)) (Int.unsigned n)) {
                    qpost_nowt_succ_body (| v1 :: vmsg :: vret :: nil |) 
                  } else {
                  Aif (fun O => exists qid els, v1 = Vptr qid /\ vmsg <> Vnull 
                                                /\ get O absecblsid = Some (absecblist els)
                                                /\ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl,wls) /\ wls <> nil)) {
                      qpost_exwt_succ_body (| v1 :: vmsg :: vret :: nil  |) ;;
                      SCHED ;;
                      asrt_and_ret (| vret :: Vint32 (Int.repr OS_NO_ERR) :: nil |)
                    } else {
                    ASSUME (fun O => False)
                  }           
                } 
              } 
            }
          }
      })
  | _ => spec_abort
  end.


(* (************************************ q timedpost  **************************************) *)


Definition qtimedpost_ovf_block_body (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists qid msg sus p st m (* mqd  *)v_ret, 
      vl= (Vptr qid :: msg :: (* Vint32 mqd :: *) v_ret :: nil) /\
        (
          exists t qls qls' tls tls' ml n pwl wl,
          exists pr, 
            get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get qls qid = Some (absmsgq ml n pwl, wl) /\
              Z.ge (Z_of_nat (length ml)) (Int.unsigned n) /\
              qls' = set qls qid (absmsgq ml n (t :: pwl), wl) /\
              get tls t = Some (p,st,m,sus,pr) /\
              (* mqidx_in_dom mqd (dom_for_prio pr) = true /\  *)
              tls' = set tls t (p,wait (os_stat_postq qid) None,msg,sus, pr) /\
              opv = None /\
              act = TauAct /\ 
              O_opt =Some ( set ( set O1 abstcblsid (abstcblist tls')) absecblsid (absecblist qls') ) 
        )
  end.

Definition qtimedpost_after_sched (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) := 
  match rst with
  |(opv, O_opt) =>
     exists qid msg v_ret ,
     vl= (Vptr qid :: msg :: v_ret ::nil) /\
       act = TauAct /\ 
       (exists tls p st t m sus pr,
           get O1 curtid = Some (oscurt t) /\
             get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, st, m, sus, pr)/\ 
             opv = None /\
             (( ((st = rdy /\ sus = false)  \/ ( st = wait (os_stat_postq qid) None /\ sus = false))  /\ O_opt = Some O1)
              \/ 
                ( ~((st = rdy /\ sus = false) \/ ( st = wait (os_stat_postq qid) None /\ sus = false) ) /\ O_opt = None))) 
  end.

Definition qtimedpost_timeout_err_body (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists qid msg v_ret, 
      vl= (Vptr qid :: msg :: v_ret ::nil) /\
      act = TauAct /\ 
        (exists t tls p m sus qls qls' ,
          exists pwl n ml wl pr,
            get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get tls t = Some (p, wait (os_stat_postq qid) None,m,sus,pr) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get qls qid = Some (absmsgq ml n pwl, wl) /\
              In t pwl /\
              qls' = set qls qid (absmsgq ml n (remove_tid t pwl), wl)/\
              opv =  (Some (Vint32 (Int.repr OS_TIMEOUT)))/\
              (v_ret = Vint32 (Int.repr OS_TIMEOUT) /\ 
                 O_opt = Some ( set (set O1 abstcblsid( abstcblist (set tls t (p, rdy, Vnull, false, pr))) ) 
                                  absecblsid (absecblist qls')) 
               \/ v_ret <> Vint32 (Int.repr OS_TIMEOUT) /\ O_opt = None))
  end.

Definition task_notrdy_or_idle O v1 vmsg :=
  exists p qid t tls els st msg sus pr,
    v1 = Vptr qid /\ vmsg <> Vnull 
    /\ get O curtid = Some (oscurt t) 
    /\ get O absecblsid = Some (absecblist els)
    /\ (exists x y pwl, get els qid = Some (absmsgq x y pwl, nil))
    /\ get O abstcblsid = Some (abstcblist tls) 
    /\ get tls t = Some (p,st,msg,sus,pr) /\ ((~(st = rdy /\ sus = false)) \/ p = Int.repr OS_IDLE_PRIO). 

Definition qtimedpost (vl:vallist) :=
  match vl with
    (Vint32 mqd) :: v1 :: vmsg :: vret :: nil =>
      (* "timeout" is 0 when QTimedPost is invoked from mq_receive.
           Hence, this parameter is elided. *) 
      (Aif |(mqdes_dom_qptr mqd v1, nil)| (fun O => v1 = Vnull) {
           asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_PEVENT_NULL) :: nil |)
         } else {
          Aif (fun O => exists qid, v1 = Vptr qid /\ vmsg = Vnull) {
              asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_POST_NULL_PTR) :: nil |) 
            } else {
            Aif (fun O => exists qid els, v1 = Vptr qid /\ vmsg <> Vnull
                                          /\ get O absecblsid = Some (absecblist els)
                                          /\ (~exists x y pwl wls, get els qid = Some (absmsgq x y pwl,wls))) { 
                asrt_and_ret (| vret :: Vint32 (Int.repr OS_ERR_EVENT_TYPE) :: nil |)
              } else {
              Aif (fun O => exists qid els, v1 = Vptr qid /\ vmsg <> Vnull
                                            /\ get O absecblsid = Some (absecblist els)
                                            /\ (exists x y pwl wls, get els qid = Some (absmsgq x y pwl,wls) /\ wls <> nil)) { 
                  qpost_exwt_succ_body (| v1 :: vmsg :: vret :: nil |) ;;
                  SCHED ;;
                  asrt_and_ret (| vret :: Vint32 (Int.repr OS_NO_ERR) :: nil |)  
                } else {
                Aif (fun O => task_notrdy_or_idle O v1 vmsg) {   
                    ASSERT (fun O => False) 
                  } else {
                  Aif (fun O => exists qid qls ml n pwl wl, v1 = Vptr qid /\ vmsg <> Vnull 
                                            /\ get O absecblsid = Some (absecblist qls)
                                            /\ get qls qid = Some (absmsgq ml n pwl, wl)
                                            /\ Z.ge (Z_of_nat (length ml)) (Int.unsigned n)) {
                      qtimedpost_ovf_block_body (| v1 :: vmsg :: (* (Vint32 mqd) :: *) vret :: nil |) ;; 
                      (sched (mqdes_dom_qptr mqd v1, nil)) ;;      
                      (mqdes_dom_qptr mqd v1, nil) # qtimedpost_after_sched [| v1 :: vmsg :: vret :: nil |] ;;
                      Aif | (mqdes_dom_qptr mqd v1, nil) |  
                          (fun O => exists qid pr t tls p m sus, v1 = Vptr qid /\ vmsg <> Vnull 
                                                                 /\ get O curtid = Some (oscurt t) 
                                                                 /\ get O abstcblsid = Some (abstcblist tls)  
                                                                 /\ get tls t = Some (p, wait (os_stat_postq qid) None,m,sus,pr)) {
                          qtimedpost_timeout_err_body (| v1 :: vmsg :: vret :: nil |)
                        } else {
                        Aif (fun O => exists qid t tls p st m sus pr, v1 = Vptr qid /\ vmsg <> Vnull
                                                      /\ get O curtid = Some (oscurt t)
                                                      /\ get O abstcblsid = Some (abstcblist tls)
                                                      /\ get tls t = Some (p, st, m, sus, pr) /\ st = rdy /\ sus = false) {
                            asrt_and_ret (| vret :: Vint32 (Int.repr OS_NO_ERR) :: nil |) 
                          } else {
                          ASSUME (fun O => False) 
                        }  
                      } 
                    } else {
                    Aif (fun O => exists qls qid ml n pwl, v1 = Vptr qid /\ vmsg <> Vnull
                                                  /\ get O absecblsid = Some (absecblist qls)
                                                  /\ get qls qid = Some (absmsgq ml n pwl, nil)
                                                  /\ Z.lt (Z_of_nat (length ml)) (Int.unsigned n)) {
                        qpost_nowt_succ_body (| v1 :: vmsg :: vret :: nil |) 
                      } else {
                      ASSUME (fun O => False) 
                    }
                  }
                }
              }
            }
          }  
        })
  | _ => spec_abort
  end. 


(* (******************************  mq_send ***********************************) *)

Definition mqsend_get_msgsize  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm,
          vl = ((Vint32 mqdes) :: rv :: nil) /\
            get O1 absmqattrid = Some (absmqattr qtls) /\
            get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm) /\
            act = TauAct /\ 
            ((rv = (Vint32 msize) /\ O_opt = Some O1)
             \/ ( rv <> (Vint32 msize) /\ O_opt =  None))
  end.

Definition mqsend_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm sltidxs,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
          get O1 absmqattrid = Some (absmqattr qtls) /\
          get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm, sltidxs) /\
          act = TauAct /\ 
          (
            ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull) /\ O_opt = Some O1 
            \/
              (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                 ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
              /\ O_opt = None
          )
  end.

Definition mqsend_get_mqflags (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
      exists mqdes rv qtls,
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: rv :: nil) /\ 
          act = TauAct /\ 
          get O1 absmqattrid = Some (absmqattr qtls) /\
          get qtls mqdes = Some (e, wtype, flag, maxm, msize, curm) /\
          ((rv = (Vint32 flag) /\ O_opt = Some O1)
             \/ ( rv <> (Vint32 flag) /\ O_opt =  None))
  end.

Definition has_no_cap_send O objptr := 
  exists t pr0 cspc,
    get O curtid = Some (oscurt t) /\
      task_prio_id O pr0 t /\ 
      get O cspaceid = Some (capcspace cspc) /\
      (~has_cat_cap pr0 cspc CAP_QUEUE_CLASS Q_POST_CAP \/
         ~has_obj_cap pr0 cspc objptr).

Definition mqd_in_dom mqd (O: osabst) (pr: priority) :=
  mqidx_in_dom mqd (dom_for_prio pr) = true. 
             

Definition mqsend_res (rv_post: int32) :=
  Aif |(ar_true, ((Vint32 rv_post) :: nil))|
    (fun O => Int.eq rv_post  (Int.repr OS_Q_FULL)= true) {
        ret_val (| (Vint32 (Int.mone)) :: nil |)
      } else {
    Aif |(ar_true, ((Vint32 rv_post) :: nil))|
    (fun O => Int.eq rv_post  (Int.repr OS_NO_ERR) = true) {
        ret_val (| Vint32 (Int.zero) :: nil |) 
      } else {
      ret_val (| Vint32 (Int.mone) :: nil |) 
    }
  }.

Definition mqsend (vl:vallist) :=
  match vl with
    (Vint32 mqd) :: msg_ptr :: (Vint32 msg_len) :: msgprio ::
      (Vint32 rv_size) :: rv_ptr :: (Vint32 rv_flag) :: (Vint32 rv_post) :: nil  => 
      ASSERT (fun O => msg_ptr = Vnull \/ exists a, msg_ptr = Vptr a);;
      (
        Aif (fun O => (Int.ltu mqd Int.zero = true \/ Int.ltu qidx_end mqd = true \/ mqd = qidx_end)) {
            ret_val (| (Vint32 (Int.mone)) :: nil |)
          } else {
         (* abstract version of the following condition in the code
         "mqdes < (OS_USER_MAX_EVENTS/3)/Core_partition_num * Domain2Index[ksCurDomain] ||
          mqdes >= (OS_USER_MAX_EVENTS/3)/Core_partition_num * (Domain2Index[ksCurDomain]+1)" *)
          Aif (fun O => forall td, dom_cur_tsk O td -> mqidx_in_dom mqd td = false) {
              ret_val (| (Vint32 (Int.mone)) :: nil |) 
            } else {
            spec_skip (* preemption possible here *) ;; 
            (mqd_in_dom mqd, nil) # mqsend_get_msgsize [| (Vint32 mqd) :: (Vint32 rv_size) :: nil|] ;; 
            Aif |(mqd_in_dom mqd, ((Vint32 rv_size) :: nil))| (fun O => Int.ltu rv_size msg_len = true) {
              ret_val (| (Vint32 (Int.mone)) :: nil |) 
              } else {
              spec_skip (* preemption possible here *) ;;
              Aif |(mqd_in_dom mqd, nil)| 
                    (fun O => forall a, msg_ptr = Vptr a ->
                                        (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) {
                  ret_val (| (Vint32 (Int.mone)) :: nil |) 
                } else {
                mqsend_get_ecb_ptr (|(Vint32 mqd) :: rv_ptr :: nil|) ;;
                Aif |(mqdes_dom_qptr mqd rv_ptr, nil)| (fun O => rv_ptr = Vnull) {
                      ret_val (| (Vint32 (Int.mone)) :: nil |)
                 } else {
                  spec_skip (* preemption possible here *) ;; 
                  (mqdes_dom_qptr mqd rv_ptr, nil) # mqsend_get_mqflags [| (Vint32 mqd) ::  (Vint32 rv_flag) :: nil |] ;;
                  Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag :: nil))|
                    (fun O => Int.eq rv_flag Int.zero = false /\ Int.eq rv_flag (Int.repr O_NONBLOCK) = false) {
                        ret_val (| (Vint32 (Int.mone)) :: nil |)
                    } else {
                    spec_skip (* preemption possible here *) ;;
                    Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag :: nil))| 
                    (fun O => has_no_cap_send O rv_ptr) {
                        ret_val (| (Vint32 (Int.mone)) :: nil |) 
                      } else {
                      spec_skip (* preemption possible here *) ;; 
                      (AIF |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)| 
                         (fun O => Int.eq rv_flag Int.zero = true) {
                            qtimedpost ((Vint32 mqd) :: rv_ptr :: msg_ptr :: (Vint32 rv_post) :: nil)
                        } ELSE {
                             qpost ((Vint32 mqd) :: rv_ptr :: msg_ptr :: (Vint32 rv_post) :: nil) 
                      });;
                      mqsend_res rv_post
                    }
                  }
                }
              }
            }
          }
      })
  | _ => ABORT
  end.



(* (************************************ q pend  **************************************) *)

Definition upd_ermp (ermp: taskdom -> EbMod.map) td errs :=
  fun td' => if Int.eq_dec td' td then errs else ermp td'. 

Definition asrt_err_ret (vl: vallist) (O: osabst) (act: action) (rst: option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      exists v1 v2 ermp errs erridx err td,  
      vl = v1 :: v2 :: Vint32 erridx :: Vint32 err :: nil 
      /\ opv = Some v2 
      /\ act = TauAct
      /\ get O eblsid = Some (eblist ermp)  
      /\ dom_cur_tsk O td
      /\ ermp td = errs 
      /\ (v1 = v2 /\ get errs erridx <> None /\ 
            O_opt = Some (set O eblsid (eblist (upd_ermp ermp td (set errs erridx err))))
          \/ (v1 <> v2 \/ get errs erridx = None) /\ O_opt = None)
  end.   

Definition qpend_get_no_pwl_succ_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      ( 
        exists qid rv,
          vl= (Vptr qid :: rv ::nil) /\
            (
              exists t qls tcbls msg ml n wl qls',
                get O1 curtid = Some (oscurt t) /\
                  get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\                 
                  get qls qid = Some (absmsgq (msg::ml) n nil, wl) /\ 
                  qls' = set qls qid (absmsgq ml n nil, wl) /\
                  opv = Some msg /\
                  act = TauAct /\ 
                  (rv = msg /\ O_opt = Some (set O1 absecblsid (absecblist qls'))  
                   \/ rv <> msg /\ O_opt = None)
            )     
      )
  end.

Definition qpend_get_ex_pwl_before_sched_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      ( 
        exists qid rv, 
          vl= (Vptr qid ::rv ::nil) /\
            (
              exists qls tcbls msg  ml n pwl wl prio ,
              exists qls' tcbls' m t' sus st pr,
                get O1 absecblsid = Some (absecblist qls) /\
                  get O1 abstcblsid = Some (abstcblist tcbls) /\ 
                  get qls qid = Some (absmsgq (msg::ml) n pwl ,wl) /\
                  qls'= set qls qid (absmsgq (ml++(m::nil)) n (remove_tid t' pwl), wl) /\
                  GetHWait tcbls pwl t' /\
                  get tcbls t' = Some (prio, st, m, sus, pr) /\ 
                  tcbls' = set tcbls t' (prio, rdy, m, sus, pr) /\ 
                  opv= None /\
                  act = TauAct /\ 
                  (rv = msg /\ O_opt = Some (set ( set O1 abstcblsid (abstcblist tcbls'))
                                               absecblsid (absecblist qls'))  
                   \/ rv <> msg /\ O_opt = None)
            )
      )
  end.

Definition qpend_block_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      (
        exists qid v2 m sus,
          vl= (Vptr qid::Vint32 v2 ::nil) /\
            exists tls tls' qls qls' wl p st n t opt_t, exists pwl pr,
              get O1 curtid = Some (oscurt t) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get qls qid = Some (absmsgq nil n pwl, wl) /\
                qls'=set qls qid (absmsgq nil n pwl,t::wl)/\
                get O1 abstcblsid = Some (abstcblist tls) /\ 
                get tls t = Some (p, st, m, sus, pr) /\
                ( v2 <> Int.zero /\ opt_t = Some v2 \/ v2 = Int.zero /\ opt_t = None ) /\
                tls' = set tls t (p,wait (os_stat_q qid) opt_t, m, sus, pr) /\
                O_opt = Some( set ( set O1 abstcblsid (abstcblist tls') ) 
                                absecblsid (absecblist qls')) /\
                opv = None /\ 
                act = TauAct 
      )
  end.

Definition qpend_assm_stat
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      exists qid tls prio st msg sus t, exists pr, 
      vl = (Vptr qid :: nil) /\
        get O1 curtid = Some (oscurt t) /\
        get O1 abstcblsid = Some (abstcblist tls) /\
        get tls t = Some (prio, st, msg, sus, pr) /\ 
        opv = None /\
        act = TauAct /\ 
        ( ((st = rdy /\ msg <> Vnull /\ sus = false \/
              st = wait (os_stat_q qid) (Some Int.zero) /\ msg = Vnull /\ sus = false)
           /\ O_opt = Some O1) \/ 
            (~(st = rdy /\ msg <> Vnull /\ sus = false \/
                 st = wait (os_stat_q qid) (Some Int.zero)  /\ msg = Vnull /\ sus = false) 
             /\ O_opt = None) )
  end.

Definition qpend_to_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) :=  
  match rst with
  | (opv, O_opt) =>
      exists qid rv,
      vl= (Vptr qid :: rv :: nil) /\
        (
            exists tls piro  t els els' ml n pwl wl,
            exists sus pr,
              get O1 curtid = Some (oscurt t) /\
                get O1 abstcblsid = Some (abstcblist tls) /\
                get tls t = Some (piro, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr) /\
                get O1 absecblsid = Some (absecblist els) /\
                get els qid = Some (absmsgq ml n pwl, wl) /\
                In t wl /\
                els' = set els qid (absmsgq ml n pwl, (remove_tid t wl)) /\
                act = TauAct /\ 
                (rv = Vnull /\ O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (piro, rdy, Vnull, false, pr)))) 
                                               absecblsid (absecblist els'))
                 \/ rv <> Vnull /\ O_opt = None)
        )
  end.

Definition qpend_block_get_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
    | (opv, O_opt) =>
     exists qid rv,
       vl = (Vptr qid :: rv :: nil) /\
       (
         exists tls p st m sus t  tls' pr,
           get O1 curtid = Some (oscurt t) /\
             get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (p, st, m, sus, pr) /\ 
             tls' = set tls t (p, rdy, Vnull, false, pr) /\
             act = TauAct /\ 
             opv = Some m /\ 
           (rv = m /\ O_opt = Some (set O1 abstcblsid (abstcblist tls'))
            \/ rv <> m /\ O_opt = None)
       )
  end.


Definition qpend (vl: vallist) :=
  match vl with
    (Vint32 mqd) :: vp :: vt :: rv :: nil =>
     Aif |(mqdes_dom_qptr mqd vp, nil) | 
        (fun O => vp = Vnull \/ (exists qid, vp = Vptr qid))
        {
          Aif |(mqdes_dom_qptr mqd vp, nil)| (fun O => vp = Vnull) {
                asrt_and_ret (| rv :: Vnull :: nil |) 
           } else {
            Aif (fun O => exists qls qid, vp = Vptr qid /\ get O absecblsid = Some (absecblist qls)
                                          /\ (~ exists x y pwls wls,get qls qid = Some (absmsgq x y pwls, wls))) {
                asrt_and_ret (| rv :: Vnull :: nil |)  
              } else {
              Aif (fun O => exists tls st msg sus t pr,
                       get O curtid = Some (oscurt t) /\ get O abstcblsid = Some (abstcblist tls) 
                       /\ get tls t = Some (Int.repr OS_IDLE_PRIO, st, msg, sus, pr)) {
                  ASSERT (fun O => False) 
                } else {
                Aif (fun O => exists tls prio st msg sus t pr, 
                         get O curtid = Some (oscurt t) /\ get O abstcblsid = Some (abstcblist tls)  
                         /\ get tls t = Some (prio, st, msg, sus, pr) /\ ~(st = rdy /\ sus = false)) {
                    ASSERT (fun O => False)
                  } else {
                  Aif (fun O => exists qid qls msg ml n wl, vp = Vptr qid /\ 
                           get O absecblsid = Some (absecblist qls) /\ get qls qid = Some (absmsgq (msg::ml) n nil, wl)) {
                      qpend_get_no_pwl_succ_body (| vp :: rv :: nil |) 
                    } else {
                    Aif (fun O => exists qid qls msg ml n pwl wl,  vp = Vptr qid /\ 
                             get O absecblsid = Some (absecblist qls) /\
                               get qls qid = Some (absmsgq (msg::ml) n pwl, wl) /\ ~ pwl = nil) {
                        qpend_get_ex_pwl_before_sched_body (| vp :: rv :: nil |) ;;
                        
                        (sched(ar_true, rv::nil)) ;;
                        (ar_true, rv::nil) # ret_val [| rv :: nil |]
                      } else {
                      Aif (fun O => exists qid qls wl n pwl, vp = Vptr qid /\
                               get O absecblsid = Some (absecblist qls) /\ get qls qid = Some (absmsgq nil n pwl, wl)) {
                          qpend_block_body (| vp :: vt :: nil |) ;;
                          (sched (mqdes_dom_qptr mqd vp, nil)) ;;
                          (mqdes_dom_qptr mqd vp, nil) # qpend_assm_stat [| vp :: nil |] ;;
                        Aif |(mqdes_dom_qptr mqd vp, nil)| (fun O => exists tls prio t qid sus pr, vp = Vptr qid /\
                                 get O curtid = Some (oscurt t) /\ get O abstcblsid = Some (abstcblist tls) /\
                                   get tls t =Some (prio, wait (os_stat_q qid) (Some Int.zero), Vnull, sus, pr)) {
                            qpend_to_body (| vp :: rv :: nil |) ;;
                            (ar_true, rv::nil) # asrt_and_ret [| rv :: Vnull :: nil |] 
                          } else {
                          Aif (fun O => exists tls p st m sus t pr,
                                   get O curtid = Some (oscurt t) /\ get O abstcblsid = Some (abstcblist tls) /\
                                     get tls t = Some (p, st, m, sus, pr) /\ m<>Vnull) {
                              qpend_block_get_body (| vp :: rv :: nil |) 
                            } else {
                            ASSUME (fun O => False) 
                          }
                        }
                      }
                      else {
                        ASSUME (fun O => False)
                      } 
                    } 
                  } 
                }
              }
            }
          }
        } else {
    ASSUME (fun O => False)
  }
| _ => ABORT 
  end. 

(* (************************************ q accept  **************************************) *) 

Definition qacc_succ_body
  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      (exists qid v_ret,
          vl= ((Vptr qid) :: v_ret :: nil) /\
            act = TauAct /\ 
            exists qls msg mls n pwl wl, 
              opv =  (Some msg) /\
                get O1 absecblsid = Some (absecblist qls) /\
                get qls qid =Some (absmsgq (msg::mls) n pwl,wl) /\
                (v_ret = msg /\ O_opt = Some (set O1 absecblsid (absecblist (set qls qid (absmsgq mls n pwl, wl))))
                 \/ v_ret <>  msg /\ O_opt = None)
      )
  end.

Definition qaccept (vl:vallist) := 
  match vl with
    (Vint32 mqd) :: v1 :: v2 :: nil =>
      (
        Aif |(mqdes_dom_qptr mqd v1, nil)| (fun O => v1 = Vnull) {
            asrt_and_ret (| v2 :: Vnull :: nil |) 
          } else {
          Aif (fun O => exists qid qls,
                   v1 = Vptr qid /\ get O absecblsid = Some (absecblist qls) /\  
                     (~ exists x y pwl wls, get qls qid = Some (absmsgq x y pwl, wls))) {
              asrt_and_ret (| v2 :: Vnull :: nil |)  
            } else {
            Aif (fun O => exists qid qls,
                     v1 = Vptr qid /\ get O absecblsid = Some (absecblist qls) /\
                       (exists wls n pwl, get qls qid =Some (absmsgq nil n pwl, wls))) {
                asrt_and_ret (| v2 :: Vnull :: nil |)  
              } else {
              Aif (fun O => exists qid qls msg mls n wl,  
                       v1 = Vptr qid /\ get O absecblsid = Some (absecblist qls) /\
                         get qls qid =Some (absmsgq (msg::mls) n nil, wl)) {
                  qacc_succ_body (| v1 :: v2 :: nil |) 
                } else {
                ASSUME (fun O => False) 
              } 
            }
          }
      })
  | _ => ABORT
  end. 


(* (****************************** memcpy (stub) ***********************************) *) 

Definition memcpy_empty (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst) := 
  match rst with
  | (opv, O_opt) =>
      exists v1 v2 v3 p, 
      vl =  (v1 :: v2 :: v3 :: nil) /\
        act = TauAct /\ 
        opv = Some (Vptr p) /\ 
        O_opt = Some O1
  end.

Definition memcpy_spec (vl:vallist) :=
  match vl with
    v1 :: v2 :: v3 :: nil =>
      memcpy_empty(| v1::v2::v3::nil |)
  | _ => spec_abort
  end.


(* (************************************ mq_recv  **************************************) *)

(* Definition qreceive_erridx_valid   *)
(*   (vl: vallist) (O: osabst) (act: action) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) =>       *)
(*       exists td ermp erridx errs,  *)
(*       get O eblsid = Some (eblist ermp) *)
(*       /\ dom_cur_tsk O td  *)
(*       /\ ermp td = errs *)
(*       /\ act = TauAct *)
(*       /\ (get errs erridx <> None /\ O_opt = Some O \/ get errs erridx = None /\ O_opt = None) *)
(*   end.  *)

Definition mqrecv_get_msgsize  (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mqdes rv qtls,
     exists e wtype flag maxm msize curm,
          vl = ((Vint32 mqdes) :: rv :: nil) /\
            get O1 absmqattrid = Some (absmqattr qtls) /\
            get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm) /\
            act = TauAct /\ 
            ((rv = (Vint32 msize) /\ O_opt = Some O1)
             \/ ( rv <> (Vint32 msize) /\ O_opt =  None))
  end.

Definition mqrecv_get_ecb_ptr 
  (vl: vallist) (O1: osabst) (act: action) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mqdes v' qtls, 
      exists e wtype flag maxm msize curm sltidxs,
        vl = ((Vint32 mqdes) :: v' :: nil) /\ 
          get O1 absmqattrid = Some (absmqattr qtls) /\ 
          get qtls mqdes =Some (e, wtype, flag, maxm, msize, curm, sltidxs) /\
          act = TauAct /\ 
          (
            ((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull) /\ O_opt = Some O1 
            \/
              (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                 ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
              /\ O_opt = None
          )
  end.

Definition mqrecv_get_mqflags (vl: vallist) (O1 : osabst) (act: action) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
      exists mqdes rv qtls,
      exists e wtype flag maxm msize curm,
        vl = ((Vint32 mqdes) :: rv :: nil) /\ 
          act = TauAct /\ 
          get O1 absmqattrid = Some (absmqattr qtls) /\
          get qtls mqdes = Some (e, wtype, flag, maxm, msize, curm) /\
          ((rv = (Vint32 flag) /\ O_opt = Some O1)
             \/ ( rv <> (Vint32 flag) /\ O_opt =  None))
  end.

Definition has_no_cap_recv O flg objptr :=
  exists t pr0 cspc, 
    get O curtid = Some (oscurt t) /\
      task_prio_id O pr0 t /\ 
      get O cspaceid = Some (capcspace cspc) /\
      (flg = Int.zero /\ ~has_cat_cap pr0 cspc CAP_QUEUE_CLASS Q_PEND_CAP \/
         flg = Int.repr O_NONBLOCK /\ ~has_cat_cap pr0 cspc CAP_QUEUE_CLASS Q_ACCEPT_CAP \/
         ~has_obj_cap pr0 cspc objptr).  

Definition mqrecv_res msg_ptr msg_len rv_post := 
  Aif |(ar_true, (rv_post :: nil))| 
    (fun O => rv_post = Vnull) {
        ret_val (| Vint32 (Int.mone) :: nil |) 
      } else {                                                  
    memcpy_spec (msg_ptr :: rv_post :: (Vint32 msg_len) :: nil);; 
    ret_val (| (Vint32 msg_len) :: nil |) 
  }.

Definition mqreceive (vl:vallist) :=
  match vl with
    (Vint32 mqd) :: msg_ptr :: (Vint32 msg_len) :: msgprio ::
      (Vint32 rv_size) :: rv_ptr :: (Vint32 rv_flag) :: rv_post :: nil => 
      ASSERT (fun O => msg_ptr = Vnull \/ exists a, msg_ptr = Vptr a);; 
      (
        Aif (fun O => (Int.ltu mqd Int.zero = true \/ Int.ltu qidx_end mqd = true \/ mqd = qidx_end)) { 
            ret_val (| (Vint32 (Int.mone)) :: nil |) 
          } else {
          (* abstract version of the following condition in the code 
             "mqdes < (OS_USER_MAX_EVENTS/3)/Core_partition_num * Domain2Index[ksCurDomain] ||
               mqdes >= (OS_USER_MAX_EVENTS/3)/Core_partition_num * (Domain2Index[ksCurDomain]+1)" *) 
          Aif (fun O => forall td, dom_cur_tsk O td -> mqidx_in_dom mqd td = false) {
              ret_val (| (Vint32 (Int.mone)) :: nil |) 
            } else {
            spec_skip (* preemption possible here *) ;; 
            (mqd_in_dom mqd, nil) # mqrecv_get_msgsize [| (Vint32 mqd) :: (Vint32 rv_size) :: nil|] ;; 
            Aif |(mqd_in_dom mqd, ((Vint32 rv_size) :: nil))| (fun O => Int.ltu rv_size msg_len = true) {
                ret_val (| (Vint32 (Int.mone)) :: nil |) 
              } else {
              spec_skip (* preemption possible here *) ;;
              Aif |(mqd_in_dom mqd, nil)|
                (fun O => forall a, msg_ptr = Vptr a ->
                                    (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) {
                  ret_val (| (Vint32 (Int.mone)) :: nil |) 
                } else {
                mqrecv_get_ecb_ptr (|(Vint32 mqd) :: rv_ptr :: nil|) ;;
                Aif |(mqdes_dom_qptr mqd rv_ptr, nil)| (fun O => rv_ptr = Vnull) {
                       ret_val (| (Vint32 (Int.mone)) :: nil |)
                 } else {
                  spec_skip (* preemption possible here *) ;;
                  (mqdes_dom_qptr mqd rv_ptr, nil) # mqrecv_get_mqflags [| (Vint32 mqd) ::  (Vint32 rv_flag) :: nil |] ;; 
                  Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)|
                  (fun O => Int.eq rv_flag Int.zero = false /\ Int.eq rv_flag (Int.repr O_NONBLOCK) = false) {
                      ret_val (| (Vint32 (Int.mone)) :: nil |) 
                    } else {
                    Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)|
                      (fun O => has_no_cap_recv O rv_flag rv_ptr) { 
                        ret_val (| (Vint32 (Int.mone)) :: nil |) 
                      } else {
                      spec_skip (* preemption possible here *) ;;
                      (AIF |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)| (fun O => Int.eq rv_flag Int.zero = true) {
                           qpend ((Vint32 mqd) :: rv_ptr :: Vint32 (Int.repr 0) :: rv_post :: nil)
                        } ELSE { 
                          qaccept ((Vint32 mqd) :: rv_ptr :: rv_post :: nil)  
                        } 
                      );; 
                      mqrecv_res msg_ptr msg_len rv_post                     
                    }
                  }
                }
              }
            }
          }
        }
      )
  | _ => ABORT 
  end.


(* (************************************ mq_timedreceive  **************************************) *)

Definition mqtimedreceive (vl:vallist) :=
  match vl with
    (Vint32 mqd) :: msg_ptr :: (Vint32 msg_len) :: msgprio :: (Vint32 tmo) :: (* tmo is timeout value *) 
      (Vint32 rv_size) :: rv_ptr :: (Vint32 rv_flag) :: rv_post :: nil => 
      ASSERT (fun O => msg_ptr = Vnull \/ exists a, msg_ptr = Vptr a);; 
      (
        Aif (fun O => Int.eq tmo Int.zero = true \/ Int.ltu (Int.repr 65535) tmo = true) {
            ret_val (| (Vint32 (Int.mone)) :: nil |) 
          } else {
          Aif (fun O => (Int.ltu mqd Int.zero = true \/ Int.ltu qidx_end mqd = true \/ mqd = qidx_end)) { 
              ret_val (| (Vint32 (Int.mone)) :: nil |) 
            } else {
            Aif (fun O => forall td, dom_cur_tsk O td -> mqidx_in_dom mqd td = false) {
                ret_val (| (Vint32 (Int.mone)) :: nil |) 
              } else {
              spec_skip (* preemption possible here *) ;; 
              (mqd_in_dom mqd, nil) # mqrecv_get_msgsize [| (Vint32 mqd) :: (Vint32 rv_size) :: nil|] ;; 
              Aif |(mqd_in_dom mqd, ((Vint32 rv_size) :: nil))| (fun O => Int.ltu rv_size msg_len = true) {
                 ret_val (| (Vint32 (Int.mone)) :: nil |) 
               } else {
                spec_skip (* preemption possible here *) ;;
                Aif |(mqd_in_dom mqd, nil)|
                (fun O => forall a, msg_ptr = Vptr a ->
                                    (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)) {
                    ret_val (| (Vint32 (Int.mone)) :: nil |) 
                  } else {
                  mqrecv_get_ecb_ptr (|(Vint32 mqd) :: rv_ptr :: nil|) ;;
                  Aif |(mqdes_dom_qptr mqd rv_ptr, nil)| (fun O => rv_ptr = Vnull) {
                       ret_val (| (Vint32 (Int.mone)) :: nil |)
                   } else {
                    spec_skip (* preemption possible here *) ;;
                    (mqdes_dom_qptr mqd rv_ptr, nil) # mqrecv_get_mqflags [| (Vint32 mqd) ::  (Vint32 rv_flag) :: nil |] ;; 
                    Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)|
                    (fun O => Int.eq rv_flag Int.zero = false /\ Int.eq rv_flag (Int.repr O_NONBLOCK) = false) {
                        ret_val (| (Vint32 (Int.mone)) :: nil |) 
                      } else {
                      Aif |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)|
                      (fun O => has_no_cap_recv O rv_flag rv_ptr) { 
                          ret_val (| (Vint32 (Int.mone)) :: nil |) 
                        } else {
                        spec_skip (* preemption possible here *) ;;
                        (AIF |(mqdes_dom_qptr mqd rv_ptr, (Vint32 rv_flag) :: nil)| (fun O => Int.eq rv_flag Int.zero = true) {
                             qpend (Vint32 mqd :: rv_ptr :: Vint32 tmo :: rv_post :: nil)
                          } ELSE { 
                             qaccept ((Vint32 mqd) :: rv_ptr :: rv_post :: nil)  
                          } 
                        );; 
                        mqrecv_res msg_ptr msg_len rv_post                     
                      }
                    }
                  }
                }
              }
            }
          }
        }
      )
  | _ => ABORT 
  end.

