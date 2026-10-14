
Require Import memory.
Require Import sem_language.
Require Import sem_init.

(*
The initial value of a semaphore, 
increased by the number of V's that increment the semaphore value, 
decreased by the number of P's that decrement the semaphore value, 
equals the current value of the semaphore.
*)
Definition cond_pv1 gau els :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) ->
    Int.ltu n (Int.repr 65536) = true /\     
    exists ga,
      get gau eid = Some ga /\
        Int.unsigned n = (Int.unsigned (ninit ga) + Z_of_nat (nsig1 ga) - Z_of_nat (nacq1 ga))%Z. 

Definition n_wait_rdy (eid: ecbid) tids (tls: TcbMod.map) (aust: LAuxStMod.map) :=
  List.length
    (List.filter
       (fun t =>
          match (get tls t), (get aust t) with
            Some (_, rdy, _, _), Some (mkLAuxSt (PtPend (Vptr eid'))) =>
              beq_tid eid eid' 
          | _, _ => false
          end) tids). 

(*
The number of successful V's that do not change the value of a semaphore is equal to: 
the number of  successful P's that do not change the value of a semaphore, 
plus the number of tasks still at the program point of pending on the semaphore  
but are already made ready. 
*)
Definition cond_pv0 els tls ts gau (aust: LAuxStMod.map) :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) ->
    exists ga, 
      get gau eid = Some ga /\
        nsig0 ga = (nacq0 ga + n_wait_rdy eid ts tls aust)%nat. 

Definition wait_progpt (els: EcbMod.map) (aust: LAuxStMod.map) :=
  forall eid n wls,
    get els eid = Some (abssem n, wls) -> 
    forall t,
      List.In t wls ->
      exists lau,
        get aust t = Some lau /\ tskpt lau = PtPend (Vptr eid).

Definition none_progpt (els: EcbMod.map) (aust: LAuxStMod.map) ts :=
  forall eid,
    (~(exists n wl, get els eid = Some (abssem n, wl))) ->
    forall t,
      In t ts -> 
      get aust t <> Some {| tskpt := PtPend (Vptr eid) |}. 

(* 
The global invariant on the data relevant to semaphores. 
The invariant is preserved by any executing steps of the interface functions: 
sem_init, sem_init_bin, sem_trywait, sem_wait, sem_timedwait, sem_post, and sem_destroy. 
%
The interface function sem_getvalue obviously preserves the invariant. 
%
The use of the interface function sem_flush could break the invariant.  
This is because sem_flush readies the tasks pending on a semaphore like several V's do.  
But sem_flush is not a P (not a series of P's either). 
*)
Definition dtinv (O: osabst) (laust: LAuxStMod.map) :=
  exists tls ts els gau,
    get O abstcblsid = Some (abstcblist tls) /\
      get O atidlsid = Some (atidls ts) /\ 
      get O absecblsid = Some (absecblist els) /\ 
      get O gauxstid = Some (gauxst gau) /\
      atids_valid tls ts /\ 
      cond_pv1 gau els /\
      cond_pv0 els tls ts gau laust /\
      wait_progpt els laust /\
      none_progpt els laust ts.

