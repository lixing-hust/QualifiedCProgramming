
Require Import memory. 
Require Import if_language.
Require Import if_opsem.

Require Import spec_aux_defs.

Require Import mq_apispecs.

Definition buffer_indom (vptr: val) (O: osabst) (pr: priority) :=
  vptr = Vnull \/
    exists a, vptr = Vptr a /\ buf_in_dom a (dom_for_prio pr) = true. 

(************************************* qpost_buf (internal def)  ***************************************)

Definition qpost_buf (vl:vallist) :=
  match vl with
    v1 :: vmsg :: vret :: nil =>
      (
          Aif |(buffer_indom v1, nil)| (fun O => v1 = Vnull) {
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

(************************************* bufferpost (interface) ***************************************)

Definition bufferpost (vl:vallist) :=
  match vl with
    vp :: msg_ptr :: (Vint32 rv_post) :: nil => 
      ASSERT (fun O =>
                (vp = Vnull \/ exists a, vp = Vptr a) /\ 
                  (msg_ptr = Vnull \/ exists a, msg_ptr = Vptr a));;
      (
        AIF |(fun O => fun pr => vp = Vnull \/ exists a, vp = Vptr a, nil)|
        (fun O => forall td eid,
             dom_cur_tsk O td ->
             vp = Vptr eid ->
             buf_in_dom eid td = false) {
            ret_val (| (Vint32 (Int.repr OS_ERR_PARTITION_UNMAPPED)) :: nil |)
          } ELSE {
          qpost_buf (vp :: msg_ptr :: (Vint32 rv_post) :: nil);;
          (ar_true, ((Vint32 rv_post) :: nil)) # ret_val [| Vint32 rv_post :: nil |]
          }
      )
  | _ => spec_abort 
  end. 

(************************************* qaccept_buf (internal def)  ***************************************)

Definition qaccept_buf (vl:vallist) := 
  match vl with
    v1 :: v2 :: nil =>
      (
        Aif |(buffer_indom v1, nil)| (fun O => v1 = Vnull) {
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

(************************************* bufferaccept (interface)  ***************************************)

Definition bufferaccept (vl: vallist) :=
  match vl with
    vp :: rv :: nil =>
      (
        ASSERT (fun O => vp = Vnull \/ exists a, vp = Vptr a);; 
        AIF | (fun O => fun pr => vp = Vnull \/ exists a, vp = Vptr a, nil) |
        (fun O => forall td eid,
             dom_cur_tsk O td ->
             vp = Vptr eid ->
             buf_in_dom eid td = false) {
            ret_val (| Vint32 Int.zero :: nil |)  
          } ELSE {
            qaccept_buf (vp :: rv :: nil);; 
            (ar_true, rv::nil) # ret_val [| rv :: nil |]
          }
      )
  | _ => spec_abort
  end.

(************************************* qpend_buf (internal)  ***************************************)

Definition qpend_buf (vl: vallist) :=
  match vl with
    vp :: vt :: rv :: nil =>
     Aif |(buffer_indom vp, nil) | 
        (fun O => vp = Vnull \/ (exists qid, vp = Vptr qid))
        {
          Aif (fun O => vp = Vnull) {
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
                          (sched (buffer_indom vp, nil)) ;;
                          (buffer_indom vp, nil) # qpend_assm_stat [| vp :: nil |] ;;
                        Aif |(buffer_indom vp, nil)| 
                          (fun O => exists tls prio t qid sus pr, vp = Vptr qid /\
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

(************************************* bufferpend (interface)  ***************************************)

Definition bufferpend (vl: vallist) :=
  match vl with
    vp :: (Vint32 tmo) :: rv :: nil =>
      (
        ASSERT (fun O => vp = Vnull \/ exists a, vp = Vptr a);; 
        AIF |(fun O => fun pr => vp = Vnull \/ exists a, vp = Vptr a, nil)|
        (fun O => forall td eid,
             dom_cur_tsk O td ->
             vp = Vptr eid ->
             buf_in_dom eid td = false) {
            ret_val (| Vint32 Int.zero :: nil |)  
          } ELSE {
            qpend_buf (vp :: (Vint32 tmo) :: rv :: nil);;
            (ar_true, rv::nil) # ret_val [| rv :: nil |]
          }
      )
  | _ => spec_abort
  end.

