(* Require Import oscorrectness.  *)
(* Require Import ucos_include. *)
Require Import PIF_os_mutex_cap.
Require Import  PIF_language.
(* Require Import  inferules_PIF. *)
Require Import PIF_os_code_defs.
Require Import PIF_os_ucos_h.
Require Import PIF_code_notations.
Require Import PIF_os_mutex.
Require Import PIF_ev_aux_code.

Open Scope list_scope.
Open Scope int_scope.
Open Scope code_scope.
Open Scope Z_scope.

(*from abs_op*)

Notation abtcblsid:=abstcblsid.
Fixpoint remove_tid (t:tid) (tl:list tid):=
  match tl with
    | nil => nil
    | t'::tl' => if (beq_tid t t') then remove_tid t tl' else (t'::(remove_tid t tl'))
  end.

Definition in_rtbl (st:taskstatus):=
  match st with
    | rdy => True
    | wait x t_opt => match t_opt with
                                     | Some time => if Int.eq time Int.zero then True else False
                                     | None => False
                                  end
  end.
Definition GetHPrio (O:osabst) (t:tid) :Prop:= 
 (exists tls prio st msg sus,
    get O abstcblsid = Some (abstcblist tls) /\ get tls t = Some (prio,st,msg,sus) /\ sus=false /\ in_rtbl st/\
    forall i prio' st' msg' sus',i <> t -> get tls i = Some (prio',st',msg',sus') -> in_rtbl st'-> 
              Int.ltu prio prio'=true).

Definition nsc (O : osabst) :=
  exists t t', get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t = t'.

Definition sc (O : osabst) :=
  exists t t',  get O curtid = Some (oscurt t) /\ GetHPrio O t' /\ t <> t'.

Definition isched := (ASSUME sc;; sched) ?? (ASSUME nsc).

Definition TIME_OUT := OS_TIMEOUT.
Definition GetHWait (tls:TcbMod.map) (wl:list tid) (t:tid) := 
  In t wl /\ 
  exists p st msg sus,
    get tls t = Some (p,st,msg,sus)/\
    forall t', t<>t' -> In t' wl -> exists p' st' msg' sus', get tls t' = Some (p',st',msg',sus') /\ (Int.ltu p p' = true)%Z.

(* Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) := *)
(*   match s1 with *)
(*   | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2) *)
(*   | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2) *)
(*   | _ => s1 ;; s2 *)
(*   end. *)

Definition NO_ERR := OS_NO_ERR.

Fixpoint Get_structe (l: (list (addrval * type * (list val))))(a: addrval)(id: ident) :  (option val ) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  =>match t with 
                                                    | Tstruct sid decls =>  match id_nth id decls  with
                                                                                               | None => None
                                                                                               | Some n => nth_val n vl
                                                                                                end
                                                    | _ => None
                                                    end
                                   | false => Get_structe l' a id
                                   end  
end.

Fixpoint Get_struct (l: (list (addrval * type * (list val))))(a: addrval) :  (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_struct l' a 
                                   end  
end.

Fixpoint Set_struct' (l: (list (addrval * type * (list val))))(a: addrval) (id : ident ) (b: val)
     :  (list (addrval * type * (list val))):=
  match l with 
  | nil => nil  
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  =>match t with 
                                                    | Tstruct sid decls =>  match id_nth id decls  with
                                                                                               | None =>  (ad, t, vl ) :: l'
                                                                                               | Some n => ((ad, t, update_nth_val n vl b) :: l')
                                                                                                end
                                                    | _ =>  (ad, t, vl ) :: l'
                                                    end
                                   | false => ((ad, t, vl ) :: (Set_struct' l' a id b))
                                   end
end.  

Fixpoint Set_sval (l: (list (addrval * type *  val )))(a: addrval) (b: val)
     :  (list (addrval * type *  val)):=
  match l with 
  | nil => nil  
  | (ad, t, v ) :: l' => match (beq_tid ad a) with
                                   | true  => ((a, t, b) :: l')
                                   | false => ((ad, t, v ) :: (Set_sval l' a b))
                                   end
end.

Fixpoint Get_heap (l: (list (addrval * type * val)))(a: addrval) :  (option (addrval * type * val )) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_heap l' a 
                                   end  
end.

(* (****************************** pthread_mutexattr_init ************************************) *)
Definition mutexattr_init_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_init_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_init_set1_init (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr is_initialized (Vint32 Int.one))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.


Definition mutexattr_init_set1_proc (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr process_shared (Vint32 Int.one))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_set1_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l ct pr stt ms sus tls,
   vl = ((Vptr attr) :: nil) /\
   get O1 curtid = Some (oscurt ct) /\
   get tls ct = Some (pr, stt, ms, sus) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
      O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr prio_ceiling (Vint32 pr))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_extcb (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists i vflg ptls tid,
      vl = ((Vint32 i) :: vflg :: nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        (get ptls i = Some (Valid_Addr tid) \/ get ptls i = Some Holder) /\ 
        opv = None /\
        O_opt = Some O1
  end.

Definition mutexattr_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists i vflg ptls,
      vl = ((Vint32 i) :: vflg :: nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls i = Some Null /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutexattr_init_afterfor_set2_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr i evheap l t vflg,
      vl =  ((Vptr attr) :: (Vint32 i) :: vflg :: nil) /\
        get O1 evstructheapid = Some (evstructheap evheap) /\
        opv = None /\
        (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
           O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr prio_ceiling (Vint32 i))))
         \/ (( Get_struct evheap attr = None \/
                 (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None)
        )
  end.

(* Definition mutexattr_for_skip (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*    opv = None /\ *)
(*    O_opt = Some O1 *)
(* end. *)

(* Definition init_loop_var (vl: vallist) (O1: osabst) (rst: option val * option osabst) := *)
(*   match rst with *)
(*   | (opv, O_opt) => *)
(*       exists v, *)
(*       vl = v :: nil /\ *)
(*         opv = None /\  *)
(*         (v = Vint32 Int.zero /\ O_opt = Some O1 \/ v <>  Vint32 Int.zero /\ O_opt = None)  *)
(*   end. *)

Definition inc_idx (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists i flg i' flg',
      vl = (Vint32 i) :: (Vint32 flg) :: (Vint32 i') :: (Vint32 flg') :: nil /\  
        ((i' = Int.add i Int.one /\ flg' = Int.zero /\ O_opt = Some O1)
         \/ ~(i' = Int.add i Int.one /\ flg' = Int.zero) /\ O_opt = None)
  end.

Definition set_flg (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists i flg i' flg',
      vl = (Vint32 i) :: (Vint32 flg) :: (Vint32 i') :: (Vint32 flg') :: nil /\  
        ((i' = i /\ flg' = Int.one /\ O_opt = Some O1)
         \/ ~(i' = i /\ flg' = Int.one) /\ O_opt = None)
  end.

(* loop variables: 1. index 2. flag (for modelling "break") *) 
Definition mutexattr_for (vl: vallist) :=
  match vl with
    vattr :: nil => 
      spec_loop
        (fun O vl => vl = (Vint32 Int.zero) :: (Vint32 Int.zero) :: nil) 
        (fun vl O =>
           exists i, 
             vl = (Vint32 i) :: (Vint32 Int.zero) :: nil /\
               Int.ltu i (Int.repr (64%Z)) = true)
        (fun vl1 vl2 =>
           (mutexattr_extcb (| vl1 |);; inc_idx (| (vl1 ++ vl2) |))
             ??
             (mutexattr_none (| vl1 |);; mutexattr_init_afterfor_set2_priocl (| vattr :: vl1 |);; set_flg (| (vl1 ++ vl2) |)))
  | _ => spec_abort 
  end. 

(* Definition mf (vl: vallist) tail := *)
(*   match vl with  *)
(*     (Vint32 i) :: (Vint32 flg) :: nil => *)
(*       (ASSUME (fun O => Int.ltu i (Int.repr 64%Z) = true);;  *)
(*         (mutexattr_extcb (| vl |);; (tail ((Vint32 (Int.add i Int.one))::(Vint32 flg)::nil))) ?? *)
(*           (mutexattr_none (| vl |);; mutexattr_init_afterfor_set2_priocl (| Vint32 i :: nil |))) *)
(*         ?? *)
(*         (ASSUME (fun O => Int.ltu i (Int.repr 64%Z) = false)) *)
(*   | _ => ABORT  *)
(*   end. *)

(* Definition mutexattr_for (vl: vallist) := *)
(*   match vl with *)
(*     (Vint32 i) :: (Vint32 flg) :: nil =>  *)
(*       mf vl mutexa *)
             
(*  Fixpoint mutexattr_for (V_attr: val)(n: nat) (m: nat)  := *)
(* match n with *)
(* | 0%nat => mutexattr_for_skip(|nil|) *)
(* |S n' => (mutexattr_extcb (|(Vint32 (Int.repr (Z.of_nat m))) :: nil|) ;; mutexattr_for V_attr n' (m+1)) ?? *)
(*                (mutexattr_none (|(Vint32 (Int.repr (Z.of_nat m ))) :: nil|) ;; *)
(*                     mutexattr_init_afterfor_set2_priocl(|V_attr :: (Vint32 (Int.repr (Z.of_nat m))):: nil|)) *)
(* end.  *)

Definition mutexattr_init_afterfor_set_protocol (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr protocol (Vint32 (Int.repr PTHREAD_PRIO_INHERIT)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None)
)
end.

Definition mutexattr_init_afterfor_set_recursive (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr recursive (Vint32 (Int.repr PTHREAD_MUTEX_ERRORCHECK)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_afterfor_set_cancel_safe (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\   
   (Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr cancel_safe (Vint32 (Int.repr PTHREAD_CANCEL_UNSAFE)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattr_init_afterfor_set_waitq_type (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t l,
   vl =  ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   opv = None /\
   ((  Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr waitq_type (Vint32 Int.zero)))))
   \/ (( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\ O_opt = None))
end.

Definition mutexattrinit_rv
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutexattrinit (vl: vallist) :=
  match vl with
    (V_attr :: V_ret :: nil) => 
      mutexattr_init_attrerr (|V_attr  :: V_ret :: nil|) ??
        (mutexattr_init_set1_init (|V_attr :: nil|) ;; 
         mutexattr_init_set1_proc (|V_attr :: nil|) ;;
         mutexattr_init_set1_priocl (|V_attr :: nil|) ;; 
         mutexattr_for (V_attr :: nil) ;;  
         mutexattr_init_afterfor_set_protocol(|V_attr :: nil|) ;;
         mutexattr_init_afterfor_set_recursive(|V_attr :: nil|);;
         mutexattr_init_afterfor_set_cancel_safe(|V_attr :: nil|);;
         mutexattr_init_afterfor_set_waitq_type(|V_attr :: nil|);;
         mutexattrinit_rv(|V_ret :: nil|)
        )
  | _ => spec_abort
  end.

Definition mutexattrinitapi:=(mutexattrinit, (Tint32,Tptr pthread_mutexattr_t::nil)). 

(* (****************************** pthread_mutexattr_destroy ************************************) *)

Definition mutexattr_destroy_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_destroy_validptr_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_destroy_clearinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists v' attr evheap l vl,
   vl = ((Vptr attr) :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\    
          O_opt = Some (set O1 evstructheapid (evstructheap (Set_struct' evheap attr is_initialized (Vint32 Int.zero)))) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrdestroy (vl: vallist) :=
match vl with
     (V_attr :: V_ret :: nil) => 
      mutexattr_destroy_attrerr (|V_attr  :: V_ret :: nil|) ??
      mutexattr_destroy_validptr_err (|V_attr :: nil|) ??
      mutexattr_destroy_clearinit (|V_attr :: V_ret :: nil|)
      | _ => spec_abort
  end.

Definition mutexattrdestroyapi:=(mutexattrdestroy, (Tint32,Tptr pthread_mutexattr_t::nil)).

(* (****************************** pthread_mutexattr_settype ************************************) *)

Definition mutexattr_settype_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_settype_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap e rv,
   vl = ((Vptr attr) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_settype_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_settype_muxtperr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init muxtp rv ,
    vl = ( init :: (Vint32 muxtp) :: rv :: nil) /\
    init <> Vint32 Int.zero /\
    (Int.ltu muxtp Int.zero = true \/ Int.ltu (Int.repr PTHREAD_MUTEX_DEFAULT) muxtp = true) /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_settype_getnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_settype_tp_neqdeflt_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr muxtp evheap v' vl l l',
   vl = ((Vptr attr) :: (Vint32 muxtp) :: v' :: nil) /\
   (Int.ltu Int.zero muxtp = true \/ muxtp = Int.zero ) /\ 
   Int.ltu muxtp (Int.repr PTHREAD_MUTEX_DEFAULT)  = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr recursive (Vint32 muxtp) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattr_settype_tp_eqdeflt_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr muxtp evheap v' vl l l',
   vl = ((Vptr attr) :: (Vint32 muxtp) :: v' :: nil) /\
   (Int.ltu Int.zero muxtp = true \/ muxtp = Int.zero ) /\ 
   muxtp = (Int.repr PTHREAD_MUTEX_DEFAULT) /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr recursive (Vint32 (Int.repr PTHREAD_MUTEX_ERRORCHECK)) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrsettype (vl: vallist) :=
match vl with
     (V_attr :: V_muxtp :: V_init :: V_ret :: nil) => 
       mutexattr_settype_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_settype_getnone_abt (|V_attr :: nil|) ??
      ( mutexattr_settype_getinit (|V_attr :: V_init :: nil|) ;; 
      ( mutexattr_settype_init_zero_eq (|V_init :: V_ret :: nil|)  ??
        mutexattr_settype_muxtperr (| V_init :: V_muxtp :: V_ret :: nil|) ?? 
       mutexattr_settype_getnone_abt (|V_attr :: nil|) ??
        mutexattr_settype_tp_neqdeflt_set_recv (|V_attr :: V_muxtp :: V_ret :: nil|) ??
        mutexattr_settype_tp_eqdeflt_set_recv (|V_attr :: V_muxtp :: V_ret :: nil|)))
      | _ => spec_abort
  end.

Definition mutexattrsettypeapi:=(mutexattrsettype, (Tint32,Tptr pthread_mutexattr_t::nil)).

(* (****************************** pthread_mutexattr_gettype ************************************) *)

Definition mutexattr_gettype_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_gettype_mtperr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr mtp v',
      vl = ((Vptr attr) :: mtp :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
        (mtp = Vnull \/
           exists a,
             mtp = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.


Definition mutexattr_gettype_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp evheap e rv,
   vl = ((Vptr attr) :: (Vptr mtp) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart mtp = true /\
   cmpaddr Cle mtp userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_gettype_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_gettype_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp evheap t vl l,
   vl = ((Vptr attr) :: (Vptr mtp) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart mtp = true /\
   cmpaddr Cle mtp userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_gettype_gethpnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists mtp evhp t vl l,
   vl = ( (Vptr mtp) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhp) /\
  ( Get_heap evhp mtp = None \/
        (Get_heap evhp mtp = Some (mtp, t, l) /\ t <> Tint32) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_gettype_tp_set_recv (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr mtp mattrheap recv evhe v' vl l',
   vl = ((Vptr attr) :: (Vptr mtp) :: v' :: nil) /\
   get O1 evstructheapid = Some (evstructheap mattrheap) /\
   Some recv = Get_structe mattrheap attr recursive /\
   get O1 evatomheapid = Some (evatomheap evhe) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_sval evhe mtp recv/\
       O_opt = Some (set O1 evatomheapid (evatomheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrgettype (vl: vallist) :=
match vl with
     (V_attr :: V_mtp :: V_init :: V_ret :: nil) => 
       mutexattr_gettype_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_gettype_mtperr (|V_attr :: V_mtp  :: V_ret :: nil|) ??
       mutexattr_gettype_getstruct_none_abt (|V_attr :: V_mtp :: nil|) ??
      ( mutexattr_gettype_getinit (|V_attr :: V_mtp :: V_init :: nil|) ;; 
      ( mutexattr_gettype_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_gettype_getstruct_none_abt (|V_attr :: V_mtp :: nil|) ??
         mutexattr_gettype_gethpnone_abt (| V_mtp :: nil|) ??
         mutexattr_gettype_tp_set_recv (|V_attr :: V_mtp :: V_ret :: nil|) ))
      | _ => spec_abort
  end.

Definition mutexattrgettypeapi:=(mutexattrgettype, (Tint32,Tptr pthread_mutexattr_t::nil)).

(* (****************************** pthread_mutexattr_setprioceiling ************************************) *)

Definition mutexattr_setprioceiling_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_setprioceiling_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap e rv,
   vl = ((Vptr attr) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_priocl_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists priocl rv,
   vl = ( Vint32 priocl :: rv ::nil) /\
  (Int.ltu priocl Int.zero = true \/
    Int.ltu (Int.repr OS_MAX_TASKS) priocl = true )/\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr evheap t vl l,
   vl = ((Vptr attr) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_setprioceiling_getstruct_none_pc_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap t vl l,
   vl = ((Vptr attr) :: (Vint32 pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   Int.ltu pc Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) pc = false /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_setprioceiling_extcb_priocl_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists priocl ptls tid rv,
   vl = ((Vint32 priocl) :: rv :: nil) /\
   Int.ltu priocl Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false /\
     get O1 absptlsid = Some (absptls ptls) /\
     (get ptls priocl = Some (Valid_Addr tid) \/
     get ptls priocl = Some Holder) /\ 
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_setprioceiling_none_setpriocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr priocl evheap ptls l v' l',
   vl = ((Vptr attr )::(Vint32 priocl) :: v' :: nil) /\
   Int.ltu priocl Int.zero = false /\
   Int.ltu (Int.repr OS_MAX_TASKS) priocl = false /\
     get O1 absptlsid = Some (absptls ptls) /\
     get ptls priocl = Some Null /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Get_struct evheap attr = Some (attr, pthread_mutexattr_t, l) /\
   opv = Some (Vint32 (Int.repr 0)) /\
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_struct' evheap attr prio_ceiling (Vint32 priocl) /\
       O_opt = Some (set O1 evstructheapid (evstructheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrsetprioceiling (vl: vallist) :=
match vl with
     (V_attr :: V_priocl :: V_init :: V_ret :: nil) => 
       mutexattr_setprioceiling_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_setprioceiling_getstruct_none_abt (|V_attr :: nil|) ??
      ( mutexattr_setprioceiling_getinit (|V_attr :: V_init :: nil|) ;; 
      ( mutexattr_setprioceiling_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_setprioceiling_priocl_err (| V_priocl :: V_ret :: nil|) ??
         mutexattr_setprioceiling_getstruct_none_pc_abt (|V_attr :: V_priocl :: nil|) ??
         mutexattr_setprioceiling_extcb_priocl_err (| V_priocl :: V_ret :: nil|)??
         mutexattr_setprioceiling_none_setpriocl (|V_attr :: V_priocl :: V_ret :: nil|) ))
      | _ => spec_abort
  end.

Definition mutexattrsetprioceilingapi:=(mutexattrsetprioceiling, (Tint32,Tptr pthread_mutexattr_t::nil)).

(* (****************************** pthread_mutexattr_getprioceiling ************************************) *) 

Definition mutexattr_getprioceiling_attrerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr v',
      vl = (attr :: v' :: nil) /\
        (attr = Vnull \/
           exists a,
             attr = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.

Definition mutexattr_getprioceiling_mtperr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists attr pc v',
      vl = ((Vptr attr) :: pc :: v' :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
        (pc = Vnull \/
           exists a,
             pc = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        (v' = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
  end.


Definition mutexattr_getprioceiling_getinit_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap,
   vl = ((Vptr attr) :: (Vptr pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   None = Get_structe evheap attr is_initialized /\
    opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_getinit (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap e rv,
   vl = ((Vptr attr) :: (Vptr pc) :: rv ::nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
   Some e = Get_structe evheap attr is_initialized /\
    opv = None /\
   (rv = e /\ O_opt = Some O1 \/
    rv <> e /\ O_opt = None)
end.

Definition mutexattr_getprioceiling_init_zero_eq (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists init rv,
   vl = ( init :: rv ::nil) /\
    init = Vint32 Int.zero /\
    opv = Some (Vint32 (Int.repr EINVAL)) /\
    (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 \/
      rv <> (Vint32 (Int.repr EINVAL)) /\ O_opt = None)
end.

Definition mutexattr_getprioceiling_getstruct_none_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc evheap t vl l,
   vl = ((Vptr attr) :: (Vptr pc) :: nil) /\
   cmpaddr Clt userAddrStart attr = true /\
   cmpaddr Cle attr userAddrEnd = true /\
   cmpaddr Clt userAddrStart pc = true /\
   cmpaddr Cle pc userAddrEnd = true /\
   get O1 evstructheapid = Some (evstructheap evheap) /\
  ( Get_struct evheap attr = None \/
        (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_gethpnone_abt (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pc evhp t vl l,
   vl = ( (Vptr pc) :: nil) /\
   get O1 evatomheapid = Some (evatomheap evhp) /\
  ( Get_heap evhp pc = None \/
        (Get_heap evhp pc = Some (pc, t, l) /\ t <> Tint32) ) /\
   opv = None /\
   O_opt = None
end.

Definition mutexattr_getprioceiling_tp_set_priocl (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr pc mattrheap priocl evhe v' vl l',
   vl = ((Vptr attr) :: (Vptr pc) :: v' :: nil) /\
   get O1 evstructheapid = Some (evstructheap mattrheap) /\
   Some priocl = Get_structe mattrheap attr prio_ceiling /\
   get O1 evatomheapid = Some (evatomheap evhe) /\
   opv = Some (Vint32 (Int.repr 0)) /\ 
    (v' = (Vint32 (Int.repr 0)) /\  l' = Set_sval evhe pc priocl/\
       O_opt = Some (set O1 evatomheapid (evatomheap l')) \/
     v' <> (Vint32 (Int.repr 0)) /\ O_opt = None)
end.

Definition mutexattrgetprioceiling (vl: vallist) :=
match vl with
     (V_attr :: V_priocl :: V_init :: V_ret :: nil) => 
       mutexattr_getprioceiling_attrerr (|V_attr  :: V_ret :: nil|) ??
       mutexattr_getprioceiling_mtperr (|V_attr :: V_priocl  :: V_ret :: nil|) ??
       mutexattr_getprioceiling_getstruct_none_abt (|V_attr :: V_priocl :: nil|) ??
      ( mutexattr_getprioceiling_getinit (|V_attr :: V_priocl :: V_init :: nil|) ;; 
      ( mutexattr_getprioceiling_init_zero_eq (|V_init :: V_ret :: nil|)  ??
         mutexattr_getprioceiling_getstruct_none_abt (|V_attr :: V_priocl :: nil|) ??
         mutexattr_getprioceiling_gethpnone_abt (| V_priocl :: nil|) ??
         mutexattr_getprioceiling_tp_set_priocl (|V_attr :: V_priocl :: V_ret :: nil|) ))
      | _ => spec_abort
  end.

Definition mutexattrgetprioceilingapi:=(mutexattrgetprioceiling, (Tint32,Tptr pthread_mutexattr_t::nil)).


(**************************************OSMutexAccept****************************************)

Definition mutexacc_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v rv,
        vl = ( v :: rv :: nil) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\ O_opt = Some O1)   \/ rv <> (Vint32 Int.zero) /\ O_opt = None) 
  end.

Definition mutexacc_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v', 
      vl = (Vnull  :: v' :: nil) /\
        opv = Some (Vint32 Int.zero) /\ 
        (v' = Vint32 Int.zero /\ O_opt = Some O1
         \/ v' <> Vint32 Int.zero /\ O_opt = None) 
  end.


Definition mutexacc_wrong_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid v',
      vl = ((Vptr mid)  :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 Int.zero) /\
            get O1 absecblsid = Some (absecblist els) /\
           ~(exists x y wls, get els mid = Some (absmutexsem x y,wls)) /\
            (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
  end.

Definition mutexacc_no_available  (vl: vallist) (O1 : osabst) (rst : option val *option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v' ,
       vl= ((Vptr mid)  :: v' :: nil)/\
       (
           exists qls, 
              opv =  (Some (Vint32 Int.zero))/\
              get O1 absecblsid = Some (absecblist qls) /\
             (exists wls p o,get qls mid =Some (absmutexsem p (Some o),wls))/\
             (v' = Vint32 Int.zero /\ O_opt = Some O1
             \/ v' <> Vint32 Int.zero /\ O_opt = None)
         )
     )
  end.

Definition mutexacc_pip_hold  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v',
       vl= ((Vptr mid) (* :: (Vptr err) *) :: v' :: nil)/\
       (
         exists qls tls p wl pt st m sus t,
             get O1 curtid = Some (oscurt t) /\
             opv =  None /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (pt,st,m,sus) /\
             get qls mid =Some (absmutexsem p None, wl)/\
            ( Int.ltu p pt = true /\ O_opt = Some O1
             \/ Int.ltu p pt = false /\ O_opt = None)
       )
     )
  end.

Definition mutexacc_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (exists mid v',
       vl= ((Vptr mid) :: v' :: nil)/\
       (
         exists qls tls p wl pt st m sus t,
             get O1 curtid = Some (oscurt t) /\
             opv =  (Some (Vint32 Int.one))/\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
             get tls t = Some (pt,st,m,sus) /\
             Int.ltu p pt = true /\
             get qls mid =Some (absmutexsem p None, wl)/\
            (v' = (Vint32 Int.one) /\ 
               O_opt = Some (set O1 absecblsid (absecblist (set qls mid (absmutexsem p (Some (t,pt)),wl))))
             \/ v' <> (Vint32 Int.one) /\ O_opt = None)
       )
     )
  end.


Definition mutexacc (vl: vallist) :=
    mutexacc_iserr (|vl|) 
    ?? mutexacc_null (|vl|)
    ?? mutexacc_wrong_type_err (|vl|)
    ?? mutexacc_no_available (|vl|)
    ?? (mutexacc_pip_hold (|vl|) ;; mutexacc_succ (|vl|)).

(*****************************************OSMutexCreate*****************************************)

Local Open Scope Z_scope.

Definition prio_available prio tls:=
  forall t p x y z, get tls t = Some (p, x, y, z) -> Int.eq prio p = false.

Definition mutexcre_err_valid (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        ((exists errid ed, verr = Vptr errid /\  get ebls errid = Some ed /\ O_opt = Some O1)  
          \/ ((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutexcre_err_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        (((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutexcre_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists rv,
        vl = ( rv :: nil) /\
        opv = Some Vnull /\
        ((rv = Vnull /\ O_opt = Some O1)   \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_seterr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists errid ebls ebls' erv,
        vl = ((Vptr errid) :: (Vint32 erv) :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        (exists ed, get ebls errid = Some ed) /\
        ebls' = EbMod.set ebls errid erv /\
        opv = None /\
        O_opt = Some (set O1 eblsid (eblist ebls'))
  end.

Definition mutexcre_prio_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio rv,
        vl = ((Vint32 prio) :: rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = false /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1 \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_prio_not_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio rv ptls d,
        vl = ((Vint32 prio) ::  rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some d /\
        d <> Null /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1  \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition mutexcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio  rv ptls,
        vl = ((Vint32 prio) ::  rv :: nil) /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some Null /\
        opv = Some Vnull /\
        (rv = Vnull /\ O_opt = Some O1 \/ rv <> Vnull /\ O_opt = None) 
  end.

Definition tsk_normal_ev locmp ptrmp tid sid :=
  get locmp tid = Some (Vint32 (Int.repr __EvLoc_normal)) /\
  (exists muxp semp qp, 
      get ptrmp tid = Some (muxp, semp, qp) /\
      (muxp = Vptr sid \/ semp = Vptr sid \/ qp = Vptr sid)).

Definition mutexcre_ecb_available (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with 
  | (opv, O_opt) =>
    exists prio rv ptls ptls' els eid t locmp locmp',
    exists ptrmp ptrmp' muxp semp qp,
        vl = ((Vint32 prio) :: rv :: nil) /\
        opv = None /\
        Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some Null /\
        ptls' = PtbMod.set ptls prio Holder /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = None /\
        get O1 evlocid = Some (evloc locmp) /\
        get O1 curtid = Some (oscurt t) /\
        locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre1)) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        get ptrmp t = Some (muxp, semp, qp) /\
        ptrmp' = set ptrmp t (Vptr eid, semp, qp) /\
        (rv = Vptr eid /\ 
          O_opt = Some (set (set (set O1 absptlsid (absptls ptls')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
         \/ rv <> Vptr eid /\ O_opt = None 
         \/ (exists t', tsk_normal_ev locmp ptrmp t' eid) /\ O_opt = None)
          (* the last disjunct reflects the assumption that no event is used while being created *)
  end. 

Definition mutexcre_prio_vhold (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio ptls d,
        vl = ((Vint32 prio) :: nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls prio = Some d /\
        opv = None /\
        (d = Holder /\ O_opt = Some O1  \/ d <> Holder /\ O_opt = None) 
  end.

Definition mutexcre_prio_unused (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists prio els,
        vl = ((Vint32 prio) :: nil) /\
         get O1 absecblsid = Some (absecblist els) /\
        opv = None /\
        (~(exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) /\ O_opt = Some O1
           \/ (exists eid ow wl, get els eid = Some (absmutexsem prio ow, wl)) /\ O_opt = None) 
  end.

Definition mutexcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists prio eid els t locmp locmp' O',
      vl = ((Vint32 prio) :: (Vptr eid) :: nil) /\
      Int.ltu prio (Int.repr OS_LOWEST_PRIO) = true /\
      opv = Some (Vptr eid) /\
      get O1 absecblsid = Some (absecblist els) /\
      get els eid = None /\
      get O1 evlocid = Some (evloc locmp) /\
      get O1 curtid = Some (oscurt t) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_ecbcre2)) /\
      O' = (set O1 absecblsid (absecblist (set els eid (absmutexsem prio None, nil)))) /\
      O_opt = Some (set O' evlocid (evloc locmp'))
  end.

Definition mutexcre (vl: vallist) :=
  match vl with
    vp :: verr :: rv :: nil => 
    (mutexcre_iserr (| rv :: nil |) ;;
           (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_CREATE_ISR)) :: nil |))) ??
    (mutexcre_prio_err (| vp :: rv :: nil |) ;;
           (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_INVALID)) :: nil |))) ??
    (mutexcre_prio_not_available (| vp :: rv :: nil |) ;;
            (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_PRIO_EXIST)) :: nil |))) ??
    (mutexcre_no_free (| vp :: rv :: nil |) ;;
            (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) :: nil |))) ??
    (mutexcre_ecb_available  (| vp :: rv :: nil |) ;; 
      mutexcre_prio_vhold (| vp :: nil |);; mutexcre_prio_unused (| vp :: nil |) ;;
      mutexcre_ecb_activate  (| vp :: rv :: nil |) ;;
             (mutexcre_err_none (| verr :: nil |) ?? 
             mutexcre_seterr (| verr :: (Vint32 (Int.repr OS_NO_ERR)) :: nil |)))
  | _ => ABORT 
  end.

(***************************************OSMutexPend_spec************************************)

Definition mutexpend_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vt v', 
      vl = (Vnull  :: vt :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ 
        (v' = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None) 
  end.

Definition mutexpend_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    |(opv, O_opt) => 
     exists mid vt v' ,
       vl= ((Vptr mid):: vt :: v' :: nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = None /\
             opv = None /\
            O_opt = None
       )
  end.

Definition mutexpend_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid vt v',
      vl = ((Vptr mid) :: vt :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
            get O1 absecblsid = Some (absecblist els) /\
            (exists d, get els mid = Some d /\ ~(exists x y wls, d = (absmutexsem x y,wls))) /\
            (v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1
             \/ v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.

Definition mutexpend_idle_err(vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl= (Vptr mid :: vt :: v' :: nil) /\
         exists tls st msg sus t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (Int.repr OS_IDLE_PRIO,st,msg,sus) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     (
       exists mid vt v',
         vl=(Vptr mid :: vt :: v' ::nil) /\
         exists tls st msg sus prio t,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get tls t = Some (prio,st,msg,sus) /\
           ~ (st = rdy /\ sus = false) /\
           opv = None /\ 
           O_opt = None
     )
  end.

Definition mutexpend_curp_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls st msg sus prio t p o wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p o,wl) /\
           get tls t = Some (prio,st,msg,sus) /\
           Int.ltu p prio = false /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_get_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
         exists mid vt v',
           vl= (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio m sus p t,
         get O1 curtid = Some (oscurt t) /\
         get O1 absecblsid = Some (absecblist els) /\
         get O1 abstcblsid = Some (abstcblist tls) /\
         get els mid = Some (absmutexsem p None,nil) /\
         get tls t = Some (prio, rdy, m, sus)/\
         Int.ltu p prio = true /\
         opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
         (v' = Vint32 (Int.repr OS_NO_ERR) /\
           O_opt = Some (set O1 absecblsid (absecblist (set els mid (absmutexsem p (Some (t,prio)),nil))))
         \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
     )
  end.

Definition mutexpend_curp_eq_owner_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio t p wl,
            get O1 curtid = Some (oscurt t) /\
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p (Some(t, prio)),wl) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_owner_idle_err  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       exists mid vt v',
         vl=  (Vptr mid :: vt :: v' :: nil) /\
         exists els tls prio ot p wl ost om sus,
            get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
           get els mid = Some (absmutexsem p (Some(ot, prio)),wl) /\
           get tls ot = Some (Int.repr OS_IDLE_PRIO, ost, om, sus) /\
           opv =  None /\
           O_opt = None
     )
  end.

Definition mutexpend_owner_not_ready_err (vl: vallist) (O1: osabst) (rst: option val * option osabst):=
  match rst with
    |(opv, O_opt) =>
     (
       exists mid vt v',
         vl=(Vptr mid :: vt :: v' ::nil) /\
         exists els tls st msg sus pip prio ot wl opt,
             get O1 absecblsid = Some (absecblist els) /\
            get O1 abstcblsid = Some (abstcblist tls) /\
            get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
           get tls ot = Some (opt,st,msg, sus) /\
           ~ (st = rdy /\ sus = false) /\
           opv = None /\ 
           O_opt = None
     )
  end.

Definition mutexpend_block_lift  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       (
         exists mid vt v' t_opt,
           vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
           exists tls tls' tls'' els els' wl pip ot prio,
             exists  cpt  opt ct cm om ptls ptls',
               exists sus sus',
                get O1 curtid = Some (oscurt ct) /\
                  get O1 absecblsid = Some (absecblist els) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                  get O1 absptlsid = Some (absptls ptls) /\
                 
                 get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
                 get tls ct = Some (cpt, rdy, cm, sus) /\
                 get tls ot = Some (opt, rdy, om, sus') /\

                 Int.eq opt pip = false /\
                 Int.ltu cpt prio = true /\
                 Int.ltu pip cpt = true /\

                 ((t_opt = Some vt /\ vt <> Int.zero) \/ (t_opt = None /\ vt = Int.zero)) /\
                 ptls' = set (set ptls opt (Holder)) pip (Valid_Addr ot) /\
                 els' = set els mid (absmutexsem pip (Some (ot,prio)), ct::wl) /\
                 tls' = set tls ct (cpt,wait (os_stat_mutexsem mid) t_opt, cm, sus) /\
                 tls'' = set tls' ot (pip, rdy, om, sus') /\
                 O_opt = Some (set (set (set O1 abtcblsid (abstcblist tls'')) absecblsid (absecblist els')) absptlsid
                                                         (absptls ptls')) /\
                 opv = None
         )
     )
  end.

Definition mutexpend_block_no_lift  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     (
       (
         exists mid vt v' t_opt ost,
           vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
           exists tls tls' els els' wl pip ot prio,
             exists  cpt  opt ct cm om,
              exists sus sus',
                get O1 curtid = Some (oscurt ct) /\
                  get O1 absecblsid = Some (absecblist els) /\
                  get O1 abtcblsid = Some (abstcblist tls) /\
                 
                 get els mid = Some (absmutexsem pip (Some (ot,prio)),wl) /\
                 get tls ct = Some (cpt, rdy, cm, sus) /\
                 get tls ot = Some (opt, ost, om, sus') /\

                 ~(Int.eq opt pip = false /\ Int.ltu cpt prio = true) /\
                  Int.ltu pip cpt = true /\

                 ((t_opt = Some vt /\ vt <> Int.zero) \/ (t_opt = None /\ vt = Int.zero)) /\
                 els' = set els mid (absmutexsem pip (Some (ot,prio)), ct::wl) /\
                 tls' = set tls ct (cpt,wait (os_stat_mutexsem mid) t_opt, cm, sus) /\
                 O_opt = Some (set (set O1 abtcblsid (abstcblist tls')) absecblsid (absecblist els')) /\
                 opv = None
         )
     )
  end.

Definition mutexpend_after_sched (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl=(Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         (
           exists tls p st t m sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, st, m, sus)/\
              opv = None /\
              (((st = rdy 
                 \/ (st = wait (os_stat_mutexsem mid) (Some Int.zero)))  /\ O_opt = Some O1)
              \/ ( ~(st = rdy \/ 
                             (st = wait (os_stat_mutexsem mid) (Some Int.zero)))  /\ O_opt = None))
         )
       )
  end.

Definition mutexpend_timeout_err_rdy (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl=(Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         (
           exists tls p t m sus els els' pip o wl,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls)/\
             get tls t =Some (p, wait (os_stat_mutexsem mid) (Some Int.zero), m, sus)/\
             get O1 absecblsid = Some (absecblist els) /\
              get els mid = Some (absmutexsem pip o,wl) /\
              In t wl /\
              els' = set els mid (absmutexsem pip o, (remove_tid t wl)) /\
              opv = Some (Vint32 (Int.repr OS_TIMEOUT) ) /\
              (v' = Vint32 (Int.repr OS_TIMEOUT)  /\
                O_opt = Some (set (set O1 abstcblsid (abstcblist (set tls t (p, rdy,m, false)))) 
                                                        absecblsid (absecblist els'))
              \/ v' <>  Vint32 (Int.repr OS_TIMEOUT)  /\ O_opt = None)
         )
       )
  end.

Definition mutexpend_block_get_succ (vl: vallist) (O1: osabst) (rst: option val * option osabst) := 
  match rst with
    |(opv, O_opt) =>
     exists mid vt v',
       vl= (Vptr mid :: Vint32 vt :: v' :: nil) /\
       (
         exists tls t p st m sus,
            get O1 curtid = Some (oscurt t) /\
            get O1 abstcblsid = Some (abstcblist tls)/\
            get tls t = Some (p, st, m, sus) /\
            ~(exists wt, st = wait (os_stat_mutexsem mid) wt) /\
           opv = Some (Vint32 (Int.repr OS_NO_ERR)) /\
          (v' = Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = Some O1
              \/ v' <>  Vint32 (Int.repr OS_NO_ERR)  /\ O_opt = None)
       )
  end.

Definition mutexpend (vl:vallist):=
  mutexpend_null (|vl|) ??
  mutexpend_p_not_legal_err (|vl|) ??
  mutexpend_type_err (|vl|) ??
  mutexpend_idle_err (|vl|) ??
  mutexpend_not_ready_err (|vl|) ??
  mutexpend_curp_err (|vl|) ??
  mutexpend_get_succ (|vl|) ??
  mutexpend_curp_eq_owner_err (|vl|) ??
  mutexpend_owner_idle_err (| vl |) ??
  (( (mutexpend_owner_not_ready_err (| vl |) ??
         mutexpend_block_lift (|vl|)) ??
        mutexpend_block_no_lift (|vl|)) ;; 
     isched ;; mutexpend_after_sched (|vl|) ;;
        (mutexpend_timeout_err_rdy (|vl|) ?? mutexpend_block_get_succ (|vl|) )).

(******************************************************************************)

Definition OS_ERR_POST_ISR: ident := 5%Z.

Definition mutexpost_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists v rv,
        vl = ( v :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_POST_ISR)) /\
        ((rv = (Vint32 (Int.repr OS_ERR_POST_ISR)) /\ O_opt = Some O1)   \/ rv <> (Vint32 (Int.repr OS_ERR_POST_ISR)) /\ O_opt = None) 
  end.

Definition mutexpost_null (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v', 
      vl = (Vnull  :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr OS_ERR_PEVENT_NULL)) /\ 
        (v' = Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = Some O1
         \/ v' <> Vint32 (Int.repr OS_ERR_PEVENT_NULL) /\ O_opt = None) 
  end.

(* Definition mutexpost_p_not_legal_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    |(opv, O_opt) => 
     exists mid v' ,
       vl= ((Vptr mid)::v' :: nil)/\
       (
           exists els,
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = None /\
             opv = None /\
            O_opt = None
       )
  end. *)

Definition mutexpost_type_err (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists mid v',
      vl = ((Vptr mid) :: v' :: nil) /\ 
        exists els,
          opv = Some (Vint32 (Int.repr OS_ERR_EVENT_TYPE)) /\
            get O1 absecblsid = Some (absecblist els) /\
            ~(exists x y wls, get els mid = Some (absmutexsem x y,wls)) /\
            (v' = Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = Some O1
             \/ v' <> Vint32 (Int.repr OS_ERR_EVENT_TYPE) /\ O_opt = None)
  end.


Definition mutexpost_owner_hold (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' tls,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr o ptls,
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
              get O1 absptlsid = Some (absptls ptls) /\
     
             get els mid = Some (absmutexsem pr o,wl) /\
             opv =  None /\
              ( ((o = None ) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy,m,false) 
                                                        /\ (prio = op
                                                              \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder )
                                                                     /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) ))))) 
                  /\ O_opt = Some O1 
             \/
             ~((o = None) \/
                      (exists ot op, o = Some (ot, op) 
                         /\ (exists prio m, get tls ot = Some (prio, rdy,m,false)
                                                            /\ (prio = op
                                                                  \/ (prio = pr /\ (get ptls op = Some Null \/ get ptls op = Some Holder)
                                                                         /\ ~(exists eid y wls, get els eid = Some(absmutexsem op y, wls)) ))))) /\
              O_opt = None)
  end.

Definition mutexpost_no_owner_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' t tls,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = Some (absmutexsem pr None,wl) /\
             opv =  (Some (Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER)))/\
            (v' = Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = Some O1
             \/ (v' <> Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = None))
  end.

Definition mutexpost_not_owner_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v' t tls ot op,
       vl= (Vptr mid :: v' :: nil) /\
           exists els wl pr prio st m  sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absecblsid = Some (absecblist els) /\
             get els mid = Some (absmutexsem pr (Some (ot,op)),wl) /\
             get tls ot = Some (prio, st, m, sus) /\
             (prio = pr \/ prio = op) /\
             t <> ot /\ 
             opv =  (Some (Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER)))/\
            (v' = Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = Some O1
             \/ (v' <> Vint32 (Int.repr OS_ERR_NOT_MUTEX_OWNER) /\ O_opt = None))
  end.

Definition mutexpost_nowt_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists mid v',
       vl= (Vptr mid :: v' :: nil) /\
       (
         (
           exists els tls els' tls' pip p' st m t ptls,
              exists ptls' sus,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist els) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\
             get els mid = Some (absmutexsem pip (Some (t,p')),nil) /\
             get tls t = Some (pip,st,m,sus) /\
             tls' = set tls t (p',st,m, sus) /\
             els' = set els mid (absmutexsem pip None,nil) /\
             ptls' = set (set ptls p' (Valid_Addr t)) pip Holder /\
             opv = (Some (Vint32 (Int.repr OS_NO_ERR)))/\
             (v' = Vint32 (Int.repr OS_NO_ERR) /\ 
               O_opt = Some (set (set ( set O1 abstcblsid (abstcblist tls') ) absecblsid (absecblist els')) absptlsid (absptls ptls') )
              \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
         )
       )
  end.

Definition mutexpost_nowt_no_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
     exists qid v' ptls ptls',
       vl= (Vptr qid :: v' :: nil) /\
           exists qls tls qls' pip op pt st m sus t,
              get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\
             get qls qid = Some (absmutexsem pip (Some (t,op)),nil) /\
             get tls t = Some (pt,st,m,sus) /\
             Int.eq pt pip = false /\
             qls' = set qls qid (absmutexsem pip None,nil) /\
             ptls' = set ptls pip Holder /\
             opv =(Some (Vint32 (Int.repr OS_NO_ERR)))/\
             (v' = Vint32 (Int.repr OS_NO_ERR) /\  O_opt = Some (set (set O1 absecblsid (absecblist qls')) absptlsid (absptls ptls'))
              \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
  end.

Definition mutexpost_wl_highest_prio_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
      vl= (Vptr qid :: v' :: nil) /\
      (
        (
          exists els tls pip t pt wl t' pw st m ,
            exists sus,
               get O1 absecblsid = Some (absecblist els) /\
               get O1 abstcblsid = Some (abstcblist tls) /\
              get els qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
              wl <> nil /\
              GetHWait tls wl t'/\ 
              get tls t' = Some (pw,st,m,sus) /\
              opv = None /\
              Int.ltu pip pw = false /\ O_opt = None
        )
      )
  end.

Definition mutexpost_exwt_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
      vl= (Vptr qid :: v' :: nil) /\
      (
        (
          exists qls tls qls' tls' tls'' ptls ptls',
            exists pip p' pt st m wl t' st' m' t ,
              exists sus sus',
               get O1 curtid = Some (oscurt t) /\
               get O1 absecblsid = Some (absecblist qls) /\
               get O1 abstcblsid = Some (abstcblist tls) /\
               get O1 absptlsid = Some (absptls ptls) /\
              get qls qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
              wl <> nil /\
              GetHWait tls wl t'/\ 
              get tls t = Some (pip,st,m,sus) /\
              get tls t' = Some (p',st',m',sus') /\
              ptls' = set (set ptls pt (Valid_Addr t)) pip Holder /\
              tls' = set tls t (pt,st,m,sus) /\
              tls''= set tls' t' (p',rdy,Vnull,sus')/\
              qls' = set qls qid (absmutexsem pip (Some (t',p')),remove_tid t' wl) /\
              
              opv = None /\
              ( v' = Vint32 (Int.repr OS_NO_ERR)  /\ 
                    O_opt = Some (set (set ( set O1 abtcblsid (abstcblist tls'') ) absecblsid (absecblist qls')) absptlsid (absptls ptls'))
                \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None)
        )
      )
  end.

Definition mutexpost_exwt_no_return_prio_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O_opt) =>
      exists qid v',
       vl= (Vptr qid :: v' :: nil) /\
       (
         (
           exists qls tls qls' tls' t ptls ptls',
             exists pip p' p'' pt st m wl t' st' m' ,
              exists sus sus',
               get O1 curtid = Some (oscurt t) /\
              get O1 absecblsid = Some (absecblist qls) /\
              get O1 abstcblsid = Some (abstcblist tls) /\
              get O1 absptlsid = Some (absptls ptls) /\

             get qls qid = Some (absmutexsem pip (Some (t,pt)),wl) /\
             wl <> nil /\
             GetHWait tls wl t'/\
             Int.eq p'' pip = false /\
             get tls t = Some (p'',st,m,sus) /\
             get tls t' = Some (p',st',m',sus') /\
             
             tls'= set tls t' (p',rdy,Vnull,sus')/\
             qls' = set qls qid (absmutexsem pip (Some (t',p')),remove_tid t' wl) /\
             ptls' = set ptls pip Holder /\

             opv = None /\
             ( v' = Vint32 (Int.repr OS_NO_ERR)  /\ 
                    O_opt = Some (set (set ( set O1 abtcblsid (abstcblist tls') ) absecblsid (absecblist qls')) absptlsid (absptls ptls'))
               \/ v' <> Vint32 (Int.repr OS_NO_ERR) /\ O_opt = None )
         )
       )
  end.

Definition mutexpost_aft_owner (vl:vallist):=
  mutexpost_no_owner_err (|vl|) ??
  mutexpost_not_owner_err (|vl|) ??
  mutexpost_nowt_return_prio_succ (|vl|) ??
  mutexpost_nowt_no_return_prio_succ (|vl|) ?? 
  mutexpost_wl_highest_prio_err (|vl|) ??
  ((mutexpost_exwt_return_prio_succ (|vl|) ?? mutexpost_exwt_no_return_prio_succ  (|vl|)) ;; 
     isched ;;  END  (Some (Vint32 (Int.repr NO_ERR)))).


Definition mutexpost (vl:vallist):=
  mutexpost_iserr (|vl|) ??
  mutexpost_null (|vl|) ??
(*   mutexpost_p_not_legal_err (|vl|) ?? *)
  mutexpost_type_err (|vl|) ??
  mutexpost_owner_hold (| vl |) ;; mutexpost_aft_owner  vl.

(* (****************************** pthread_mutex_trylock ************************************) *)
Definition int_of_addr (v: addrval) : int32 :=
  match v with
    (b, o) => Int.add (Int.mul (Int.repr (Zpos b)) (Int.repr 4)) o
  end. 

Definition mutextrylock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutextrylock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = ((Vptr a) :: v' :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition mutextrylock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextrylock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pro pi,
          exists c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
          (((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutextrylock_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((v' = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end. 

Definition mutextrylock_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = (Vptr eid) :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mutextrylock_if_null_owner_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n w pro c, 
        exists pi qls pr y wl rv,
        vl =((Vint32 posv) :: (Vptr eid) :: rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls eid =Some (absmutexsem pr y, wl) /\
        (( y = None /\ ow = $ OS_MUTEX_AVAILABLE )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
          opv = None /\
          ( (rv = (Vint32 ow) /\ O_opt = Some O1) \/
           (rv <> (Vint32 ow) /\O_opt = None) )
  end. 

Definition mutextrylock_recurtype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pro,
        exists pi c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv =None /\
        (( v' = Vint32 x /\ O_opt = Some O1) \/
        ( v' <> Vint32 x /\ O_opt = None ))
  end.

Definition mutextrylock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists curp t prio st m sus tls, 
          vl = ( curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( curp = Vint32 prio /\ O_opt = Some O1) \/
          ( curp <> Vint32 prio /\ O_opt = None ))
  end. 

Definition mutextrylock_prioceil
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv v' mls e o x n w pi pro,
        exists c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
        (( v' = Vint32 pi /\ O_opt = Some O1) \/
        ( v' <> Vint32 pi /\ O_opt = None ))
  end.

Definition mutextrylock_get_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x ,
        exists pi n w pro c , 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
        (( v' = Vint32 n /\ O_opt = Some O1) \/
        ( v' <> Vint32 n /\ O_opt = None ))
  end.

Definition mutextrylock_if_lt_cnt_max_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists n rv posv tp ty ow curp mls o w , 
      exists pi priocl pro pe c eid cn,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) :: rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, ty, cn, pro, pi, w, c) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        ( ow = curp \/ priocl = curp ) /\
        Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) =false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutextrylock_if_lt_cnt_max_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists n rv posv tp ty curp mls eid o w, 
      exists pi priocl ow pe c pro cn,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: (Vint32 n) ::  rv :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, ty, cn, pro, pi, w, c) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        ( ow = curp \/ priocl = curp ) /\
        Int.ltu n (Int.repr (PTHREAD_MUTEX_RECURSIVE_MAX)) = true /\
        opv = Some (Vint32 (Int.repr 0)) /\
        ((rv = (Vint32 (Int.repr 0)) /\
                O_opt = Some (set O1 absmutinfoid
                              (absmutinfo (set mls posv (pe, o, ty, (Int.add cn Int.one), pro, pi, w, c))))
           )
           \/ (rv <> Vint32 (Int.repr 0) /\ O_opt = None))
  end.

Definition mutextrylock_after_acc_1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv eid ,
      vl = ((Vint32 posv) :: (Vint32 v') :: (Vptr eid) :: nil) /\
        exists ow o x n w pro c,
         exists pi wl p els mls eid ,
        Int.eq (Int.repr 1) v' = true /\
        get O1 absecblsid = Some (absecblist els) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c) /\
        get els eid = Some (absmutexsem p ow,wl) /\  
        opv = None /\
         O_opt = Some (set O1 absmutinfoid (absmutinfo (set mls posv (Valid_Addr eid, ow, x, n, pro, pi, w, c))))
  end.

Definition mutextrylock_afteracc1_rv
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutextrylock_if_null_yes_afteracc
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        ((v' = Vint32 (Int.repr 0) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr 0) /\ O_opt = None))
  end. 

Definition mutextrylock_after_acc_2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (Vint32 v) :: v' :: nil /\
        Int.eq (Int.repr 1) v = false /\ 
        opv = Some (Vint32 (Int.repr EBUSY)) /\
        (v' = Vint32 (Int.repr EBUSY) /\ O_opt = Some O1 
         \/ v' <> Vint32 (Int.repr EBUSY) /\ O_opt = None)
  end. 

Definition mutextrylock_get_ecb_ptr1 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c ptrmp t, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Null, o, x, n, pro, pi, w, c) /\
        get O1 evptrid = Some (evptr ptrmp) /\ 
        get O1 curtid = Some (oscurt t) /\
        get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
        opv = None /\
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition mutextrylock_get_ecb_ptr2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c ptrmp t eid, 
    vl = ((Vint32 posv) :: v' :: nil) /\
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    opv = None /\
    (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t ( Vptr eid, Vnull, Vnull)))) \/ 
     v' <> Vptr eid /\ O_opt = None)
  end.
 
Definition mutextrylock_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists posv mls o x n pro pi w c, 
    vl = ((Vint32 posv) :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr 6) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Holder, o, x, n, pro, pi, w, c) /\
    opv = None /\
    O_opt = None 
  end.

Definition mutextrylock_after_acc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists t ptrmp ptrmp',
      vl = nil /\
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        opv = None /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end. 

Definition callacc (V_pos:val)(V_pevt:val)(V_eid0:val)(V_accrv:val)(V_ret:val) :=
                                               (mutextrylock_get_ecb_ptr1 (|V_pos:: V_pevt :: nil|)??
                                                mutextrylock_get_ecb_ptr2 (|V_pos:: V_pevt :: nil|)??
                                                mutextrylock_ecb_ptr_holder_abt(|V_pos :: nil|)) ;;
                                                            mutexacc (V_pevt :: V_accrv::nil);; mutextrylock_after_acc_ptr (|nil|) ;;
                                                     ((mutextrylock_ecb_ptr (|V_pos :: V_eid0 :: nil|);;
                                                      (mutextrylock_if_null_yes_afteracc(|V_eid0 :: V_ret :: nil|) ??
                                                        ( mutextrylock_after_acc_1 (|V_pos ::V_accrv :: V_eid0 :: nil|);; mutextrylock_afteracc1_rv (| V_ret :: nil|))))  ??
                                                      mutextrylock_after_acc_2 (|V_accrv ::V_ret::nil|)).

Definition mutextrylock (vl: vallist) :=
match vl with
    (V_mux :: V_pos :: V_eid :: V_eid' :: V_ow :: V_tp :: V_curp :: V_priocl :: V_pevt :: V_recurcnt :: V_eid0 :: V_accrv :: V_ret :: nil)=>
                  (mutextrylock_muxerr (|V_mux :: V_pos :: nil|) ??
                   mutextrylock_mutex_pos(|V_mux :: V_pos :: nil|));;
                      (mutextrylock_poserr (|V_pos :: V_ret :: nil|) ?? 
                         (mutextrylock_ecb_ptr (|V_pos :: V_eid :: nil|);; 
                            (mutextrylock_if_null_yes (|V_eid :: V_ret :: nil|) ??
                              (mutextrylock_if_null_no (|V_eid :: nil|) ;;
                                mutextrylock_ecb_ptr (|V_pos :: V_eid' :: nil|) ;;
                                (mutextrylock_if_null_yes (|V_eid' :: V_ret :: nil|) ??
                                   (mutextrylock_if_null_owner_no (|V_pos :: V_eid' :: V_ow :: nil|) ;;
                                        mutextrylock_recurtype(|V_pos :: V_tp :: nil|) ;; 
                                        ( (
                                             mutextrylock_curprio(| V_curp :: nil|) ;; mutextrylock_prioceil(|V_pos :: V_priocl :: nil|) ;;
                                               ( 
                                                      (mutextrylock_get_recurcnt (| V_pos :: V_recurcnt :: nil|) ;;
                                                         (mutextrylock_if_lt_cnt_max_yes (|V_pos :: V_eid' :: V_ow ::  V_tp :: V_curp :: V_priocl :: V_recurcnt :: V_ret :: nil|) ??
                                                          mutextrylock_if_lt_cnt_max_no (|V_pos :: V_eid' :: V_ow ::  V_tp :: V_curp :: V_priocl :: V_recurcnt :: V_ret :: nil|))) ?? 
                                                          (callacc V_pos V_pevt V_eid0 V_accrv V_ret)
                                               ) 
                                           ) ??
                                                (callacc V_pos V_pevt V_eid0 V_accrv V_ret)
                                          )))))))
  | _ => spec_abort
  end.

Definition mutextrylockapi:=(mutextrylock, (Tint32,Tptr pthread_mutex_t::nil)).

(* (****************************** pthread_mutex_init ************************************) *)
Definition V_muxattr_prioceiling (vl:vallist) := nth_val 2 vl.
Definition V_muxattr_cancelsafe      (vl:vallist) := nth_val 6 vl.
Definition mutex_init_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists vmux,
      vl = vmux :: nil /\
        (vmux = Vnull \/
           exists a,
             vmux = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
        O_opt = Some O1
  end.

Definition mutex_init_attr_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      vl = Vnull :: nil /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutex_init_attr_no_free
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists rv_attr,
      vl = Vint32 rv_attr :: nil /\
      Int.eq rv_attr Int.zero = false /\
      opv = Some (Vint32 (Int.repr EINVAL)) /\
      O_opt = Some O1
  end.

Definition mutex_init_attr_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
(*      exists vattr ventity , *)
      vl = (* vattr :: ventity :: *) Vint32 Int.zero :: nil /\
(*       vattr = ventity /\ *)
      opv = None /\
      O_opt = Some O1
  end.

Definition mutex_init_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv muxinfo, 
      vl = (posv :: nil) /\
       get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      opv = None /\
      (
      ((~(exists pos ow tp rcnt prot prioc wq cnsa,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
                                             0 <= (Int.unsigned pos) < (OS_USER_MAX_EVENTS / 3)) /\
          posv = Vint32 (Int.repr 255)) \/
       (exists pos ow tp rcnt prot prioc wq cnsa,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\
         posv = Vint32 pos )) /\ O_opt = Some O1
      ) \/
      (
      ((~(exists pos ow tp rcnt prot prioc wq cnsa,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
                                             0 <= (Int.unsigned pos)  < (OS_USER_MAX_EVENTS / 3)) /\
      posv <> Vint32 (Int.repr 255)) \/
     (exists pos ow tp rcnt prot prioc wq cnsa,
                       MibMod.get muxinfo pos = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\
      posv <> Vint32 pos )) /\ O_opt = None
      )
end.

Definition mutex_init_poserr 
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos, 
      vl = ((Vint32 pos) :: nil) /\ 
      Int.eq pos (Int.repr 255) = true /\
      opv = Some (Vint32 (Int.repr EAGAIN)) /\
      O_opt = Some O1
  end.

(* set ECB pointer in EIB to the placeholder *)
(* update the ghost location and index to reflect the status of creating a mux. *) 
Definition mutex_init_set_placeholder
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos muxinfo muxinfo',
    exists e ow tp rcnt prot prioc wq cnsa,
      vl = (Vint32 pos :: nil) /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos =  Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa)  /\
      muxinfo' = set muxinfo pos (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa) /\
      opv = None /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo'))
  end.

Definition mutex_init_attr_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists attr evheap t vl l,
      vl = ((Vptr attr) :: nil) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      ( Get_struct evheap attr = None \/
            (Get_struct evheap attr = Some (attr, t, l) /\ t <> pthread_mutexattr_t) ) /\
       opv = None /\
       O_opt = None
  end.

(* Definition mutex_init_get_attr_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr prioc evheap attr_vl,
      vl = (Vptr attr :: prioc :: nil) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      opv = None /\
      ( V_muxattr_prioceiling attr_vl = Some prioc /\ O_opt = Some O1
         \/ V_muxattr_prioceiling attr_vl <> Some prioc /\ O_opt = None)
  end. *)

Definition mutex_init_get_attr_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists attr prioc evheap attr_vl pip,
      vl = (Vptr attr :: prioc :: nil) /\
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_prioceiling attr_vl = Some (Vint32 pip) /\
      0 <= Int.unsigned pip < 64 /\
      opv = None /\
      ( prioc = Vint32 pip /\ O_opt = Some O1
         \/ (prioc <> Vint32 pip)/\ O_opt = None)
  end.
Parameter vhold_addr : addrval.

Definition mutex_init_set_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos eptr t muxinfo muxinfo',
    exists e ow tp rcnt prot prioc wq cnsa,
    exists locmp locmp' ptrmp ptrmp' muxp semp qp,
      vl = Vint32 pos :: eptr :: nil /\
      Int.eq pos (Int.repr 255) = false /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\
      get O1 curtid = Some (oscurt t) /\
      get O1 evlocid = Some (evloc locmp) /\
      locmp' = set locmp t (Vint32 (Int.repr __EvLoc_normal)) /\
      get O1 evptrid = Some (evptr ptrmp) /\
      get ptrmp t = Some (muxp, semp, qp) /\
      ptrmp' = set ptrmp t (Vnull, semp, qp) /\
      opv = None /\
      ((exists eid, (eptr = Vptr eid /\ eid <> vhold_addr 
                                   /\ muxinfo' = set muxinfo pos (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa))) 
        \/ eptr = Vnull /\ muxinfo' = set muxinfo pos (Null, ow, tp, rcnt, prot, prioc, wq, cnsa)) /\  
       O_opt = Some (set (set (set O1 absmutinfoid (absmutinfo muxinfo')) evlocid (evloc locmp')) evptrid (evptr ptrmp'))
  end.

Definition mutex_init_holder_abt
           (vl: vallist) (O: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = Vptr vhold_addr :: nil /\ opv = None /\O_opt = None
  end.   

Definition mutex_init_err_none (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists verr ebls,
        vl = (verr :: nil) /\
        get O1 eblsid = Some (eblist ebls) /\
        opv = None /\
        (((exists errid, verr = Vptr errid /\  get ebls errid = None) \/ 
                  verr = Vnull) /\ O_opt = None) 
  end.

Definition mutex_init_get_verr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists errid rv_verr ebls ed,
      vl = (Vptr errid :: rv_verr :: nil) /\
      get O1 eblsid = Some (eblist ebls) /\
      get ebls errid = Some ed /\
      opv = None /\
      ( rv_verr = Vint32 ed /\ O_opt = Some O1
         \/ rv_verr <> Vint32 ed /\ O_opt = None)
  end.

Definition mutex_init_create_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos err, 
    vl = (Vint32 pos :: Vint32 err :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    Int.eq err (Int.repr OS_NO_ERR) = false /\
    opv = Some (Vint32 (Int.repr EAGAIN)) /\
    O_opt = Some O1 
  end.

Definition mutex_init_create_succ
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists pos, 
    vl = (Vint32 pos :: Vint32 (Int.repr OS_NO_ERR) :: nil) /\
    Int.eq pos (Int.repr 255) = false /\
    opv = None /\
    O_opt = Some O1 
  end.

Definition mutex_init_set_cancel
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa cnsa', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_cancelsafe attr_vl = Some (Vint32 cnsa') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq, cnsa') /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.
Definition V_muxattr_protocol       (vl:vallist) := nth_val 3 vl.
Definition mutex_init_set_protocol
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa prot', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_protocol attr_vl = Some (Vint32 prot') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot', prioc, wq, cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_recursive
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos muxinfo muxinfo',
      exists e ow tp rcnt prot prioc wq cnsa, 
      vl = (Vint32 pos) :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, Int.zero, prot, prioc, wq, cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos muxinfo muxinfo',
      exists e ow tp rcnt prot prioc wq cnsa, 
      vl = (Vint32 pos) :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      MibMod.get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      opv = None /\
      muxinfo' = set muxinfo pos (e, None, tp, rcnt, prot, prioc, wq, cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa prioc', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_prioceiling attr_vl = Some (Vint32 prioc') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc', wq, cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition V_muxattr_recursive      (vl:vallist) := nth_val 4 vl.
Definition V_muxattr_waitq     (vl:vallist) := nth_val 5 vl.

Definition mutex_init_set_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa rec, 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_recursive attr_vl = Some (Vint32 rec) /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, rec, rcnt, prot, prioc, wq, cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_waitq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists pos attr muxinfo muxinfo' evheap attr_vl,
      exists e ow tp rcnt prot prioc wq cnsa wq', 
      vl = (Vint32 pos) :: Vptr attr :: nil /\
      get O1 absmutinfoid = Some (absmutinfo muxinfo) /\
      get muxinfo pos = Some (e, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
      get O1 evstructheapid = Some (evstructheap evheap) /\
      Get_struct evheap attr = Some (attr, pthread_mutexattr_t, attr_vl) /\
      V_muxattr_waitq attr_vl = Some (Vint32 wq') /\
      opv = None /\
      muxinfo' = set muxinfo pos (e, ow, tp, rcnt, prot, prioc, wq', cnsa) /\
      O_opt = Some (set O1 absmutinfoid (absmutinfo muxinfo')) 
  end.

Definition mutex_init_set_mux
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a pos pbls,
      vl = (Vptr a) :: (Vint32 pos) :: nil /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = Some (Vint32 (Int.zero)) /\
        (((exists posv, get pbls a = Some posv) /\ O_opt = Some (set O1 pblsid (pblist (set pbls a pos))))
          \/ ~(exists posv, get pbls a = Some posv) /\ O_opt = None)
  end.

Definition mutex_init_after_get_attr (vl: vallist) :=
  match vl with
    vmux :: vattr :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: nil => 
    (mutex_init_pos (| posv :: nil |);;
         (mutex_init_poserr (|posv :: nil|) ??
            (mutex_init_set_placeholder (|posv :: nil|) ;;
              (mutex_init_attr_none (| vattr :: nil |) ??
                mutex_init_get_attr_prioceiling (| vattr :: rv_prioc :: nil |)) ;;
             mutexcre (rv_prioc :: verr :: rv_cre :: nil) ;;
             (mutex_init_set_ecb_ptr (| posv :: rv_cre :: nil |) ?? mutex_init_holder_abt (| rv_cre :: nil|));;  
             ( mutex_init_err_none (| verr :: nil |) ??
                mutex_init_get_verr (| verr :: rv_verr :: nil |) ;;
                (mutex_init_create_err (| posv :: rv_verr :: nil |) ?? 
                  mutex_init_create_succ (| posv :: rv_verr :: nil |) ;;
               ( (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_cancel (| posv :: vattr :: nil |)) ;;
                  (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_protocol (| posv :: vattr :: nil |)) ;;
                  mutex_init_set_recursive (| posv :: nil |) ;;
                  mutex_init_set_owner (| posv :: nil |) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_prioceiling (| posv :: vattr :: nil |)) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_type (| posv :: vattr :: nil |)) ;;
                 (mutex_init_attr_none (| vattr :: nil |) ?? mutex_init_set_waitq (| posv :: vattr :: nil |)) ;;
                 mutex_init_set_mux (| vmux :: posv :: nil |)))) )))
   | _ => spec_abort
   end.

Definition mutex_init (vl: vallist) :=
  match vl with
    vmux :: vattr :: ventity :: verr :: rv_attr :: posv :: rv_prioc :: rv_cre :: rv_verr :: nil => 
      mutex_init_muxerr (| vmux :: nil |) ??
      (mutex_init_attr_null (| vattr :: nil |) ;; 
                mutexattrinit (ventity :: rv_attr :: nil ) ;;
                     (mutex_init_attr_no_free (| rv_attr :: nil |) ??
                        (mutex_init_attr_succ (| (* vattr :: ventity :: *) rv_attr :: nil |) ;;
                            mutex_init_after_get_attr (vmux :: ventity :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: nil)  ) )) ??
       mutex_init_after_get_attr (vmux :: vattr :: verr :: posv :: rv_prioc :: rv_cre :: rv_verr :: nil)
  | _ => spec_abort
  end.

Definition mutexinitapi := (mutex_init, (Tint32, Tptr pthread_mutex_t :: Tptr pthread_mutexattr_t :: Tptr pthread_mutexattr_t :: Tptr Int8u :: nil)). 

(* (****************************** pthread_mutex_destroy ************************************) *)

Definition mutex_destroy_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v,
      vl = v :: nil /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = Some (Vint32 (Int.repr EINVAL)) /\
         O_opt = Some O1
  end.

Definition mutex_destroy_mux_nopblk_abt
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a',
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = None /\ 
      opv = None /\
      O_opt = None
  end.

Definition mutex_destroy_pos_err 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\
      (Int.ltu posv Int.zero = true \/
       Int.ltu (Int.repr 6) posv = true \/ Int.eq posv (Int.repr 6) = true) /\  
      opv = Some (Vint32 (Int.repr EINVAL)) /\ 
     O_opt = Some O1
  end.

Definition mutex_destroy_pevent_null_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.repr EINVAL)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr 6) = true) /\    
      exists muxeibs ow tp rcnt prot prioc wq cnsa ,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        O_opt = Some O1 
  end.

Definition mutex_destroy_not_placeholder_assm
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    opv = None /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr 6) = true) /\    
     exists muxeibs ow tp rcnt prot prioc wq cnsa ,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Holder, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        O_opt = None
  end.
  
Definition mutex_destroy_waiting_tasks_err
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.repr EBUSY)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr 6) = true) /\    
     exists muxeibs ow tp rcnt prot prioc wq cnsa,
     exists eid els pip o wls,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, wls) /\
        wls <> nil /\
        O_opt = Some O1
  end.

Definition mutex_destroy_iserr (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
       exists v,
        vl = (v :: nil) /\
        opv = Some (Vint32 (Int.repr EBUSY)) /\ 
         O_opt = Some O1
  end.

Definition mutex_destroy_pip_err (vl: vallist) (O1: osabst) (rst: option val *option osabst) := 
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.zero)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr 6) = true) /\    
     exists muxeibs ow tp rcnt prot prioc wq cnsa,
     exists eid els pip o ptls,
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        ~(get ptls pip = Some Holder) /\
       O_opt = None
  end.

Definition mutex_destroy_succ (vl: vallist) (O1: osabst) (rst: option val *option osabst) := 
  match rst with
  | (opv, O_opt) =>
    exists a,
    vl = (Vptr a) :: nil /\ 
    opv = Some (Vint32 (Int.zero)) /\ 
    cmpaddr Clt userAddrStart a = true /\
    cmpaddr Cle a userAddrEnd = true /\
    exists pbls a' posv,
      get O1 pblsid = Some (pblist pbls) /\
      get pbls a' = Some posv /\ 
      ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
       Int.ltu posv (Int.repr 6) = true) /\    
     exists muxeibs ow tp rcnt prot prioc wq cnsa,
     exists eid els pip o els' muxeibs' ptls ptls',
        get O1 absmutinfoid = Some (absmutinfo muxeibs) /\
        get muxeibs posv = Some (Valid_Addr eid, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem pip o, nil) /\
        get O1 absptlsid = Some (absptls ptls) /\
        get ptls pip = Some Holder /\
        ptls' = set ptls pip Null /\
        join els' (sig eid (absmutexsem pip o, nil)) els /\
        muxeibs' = set muxeibs posv (Null, ow, tp, rcnt, prot, prioc, wq, cnsa) /\ 
        O_opt = Some (set (set (set O1 absecblsid (absecblist els')) absmutinfoid (absmutinfo muxeibs')) absptlsid (absptls ptls'))
  end. 

Definition mutex_destroy (vl: vallist) :=
  match vl with
    vmux :: nil => 
      mutex_destroy_muxerr (| vl |) ??
      mutex_destroy_mux_nopblk_abt (| vl |) ?? 
      mutex_destroy_pos_err (| vl |) ??
      mutex_destroy_not_placeholder_assm (| vl |) ??
      mutex_destroy_pevent_null_err (| vl |) ??
      mutex_destroy_waiting_tasks_err (| vl |) ??
      mutex_destroy_iserr (| vl |) ??
      mutex_destroy_pip_err (| vl |) ??
      mutex_destroy_succ (| vl |)
  | _ => spec_abort 
 end.

Local Open Scope code_scope.

Definition pthread_mutex_destroy_api := (mutex_destroy, (Tint32, Tptr pthread_mutex_t :: nil)).

(* (****************************** pthread_mutex_lock ************************************) *)

Definition mutexlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v_pos,
      vl = (v :: v_pos :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v_pos = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v_pos <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutexlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v_pos pbls,
      vl = ((Vptr a) :: v_pos :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = None /\
        ((exists posv,
               (get pbls a = Some posv /\
                  (v_pos = (Vint32 posv) /\ O_opt = Some O1 \/ v_pos <> (Vint32 posv) /\ O_opt = None)))
          \/ get pbls a = None /\ O_opt = None)
  end.

Definition mutexlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutexlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_pevent :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (((exists eid, e = Valid_Addr eid /\ v_pevent = Vptr eid) \/ e = Null /\ v_pevent = Vnull)
           /\ O_opt = Some O1
           \/
             (e = Holder \/ 
                (exists eid, e = Valid_Addr eid /\ v_pevent <> Vptr eid) \/ (e = Null /\ v_pevent <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutexlock_ecb_nullerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv,
      (vl = Vnull :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end.

Definition mutexlock_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n pro w c, 
        exists pcp qls pr y wl v_ow,
      vl =((Vint32 posv) :: (Vptr eid) :: v_ow :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
      get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c) /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls eid =Some (absmutexsem pr y, wl) /\
      opv = None /\
      ((ow = $ OS_MUTEX_AVAILABLE /\ y = None )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
      ( (v_ow = (Vint32 ow) /\ O_opt = Some O1) \/
          (v_ow <> (Vint32 ow) /\O_opt = None))
  end.

Definition mutexlock_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_tp posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_tp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (( v_tp = Vint32 x /\ O_opt = Some O1) \/
          ( v_tp <> Vint32 x /\ O_opt = None ))
  end.

Definition mutexlock_typeerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp, 
        vl = ((Vint32 tp) :: rv :: nil) /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false /\
        opv = Some (Vint32(Int.repr EINVAL)) /\
        ((rv = (Vint32(Int.repr EINVAL)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EINVAL)) /\ O_opt = None))
  end.

Definition mutexlock_type_normal
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tp, 
        vl = ((Vint32 tp) :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_NORMAL) /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutexlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_curp t prio st m sus tls, 
          vl = ( v_curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( v_curp = Vint32 prio /\ O_opt = Some O1) \/
          ( v_curp <> Vint32 prio /\ O_opt = None ))
  end.

Definition mutexlock_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pcp posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_pcp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (( v_pcp = Vint32 pcp /\ O_opt = Some O1) \/
          ( v_pcp <> Vint32 pcp /\ O_opt = None ))
  end.

Definition mutexlock_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_rcnt posv mls e o x ,
        exists n pro pcp w c , 
        vl = ((Vint32 posv) :: v_rcnt :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
          (( v_rcnt = Vint32 n /\ O_opt = Some O1) \/
          ( v_rcnt <> Vint32 n /\ O_opt = None ))
  end.

Definition mutexlock_type_deadlk
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_ERRORCHECK) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        opv = Some (Vint32(Int.repr EDEADLK)) /\
        ((rv = (Vint32(Int.repr EDEADLK)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EDEADLK)) /\ O_opt = None))
  end.

Definition mutexlock_type_recur_again
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp rcnt, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutexlock_type_recur_incre_one
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv tp ow curp pcp rcnt, 
      exists mls e o x cn pro pip w c,
        vl = ((Vint32 posv) :: (Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, cn, pro, pip, w, c) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\
           O_opt = Some (set O1 absmutinfoid 
                                      (absmutinfo (set mls posv (e, o, x, (Int.add cn Int.one), pro, pip, w, c))))) \/
        (rv <> (Vint32 Int.zero) /\ O_opt = None))
  end.

Definition mutexlock_after_pend_fail
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_NO_ERR) = false /\
        opv = Some(Vint32 (Int.repr EINVAL)) /\
        (( rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None ))
  end.

Definition mutexlock_after_pend_succ_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: Vnull :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        (( rv = Vint32 Int.zero /\ O_opt = Some O1) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutexlock_after_pend_succ_ecb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr eid posv rv,
      exists mls o x n pro pcp w c,
      exists els p ow wl,
        vl = ((Vint32 verr) :: (Vptr eid) :: (Vint32 posv) :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem p ow,wl) /\
        (( rv = Vint32 Int.zero 
            /\ O_opt = Some (set O1 absmutinfoid 
                                            (absmutinfo (set mls posv (Valid_Addr eid, ow, x, n, pro, pcp, w, c))))) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutexlock_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         opv = None /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (v_pevent, Vnull, Vnull))))
  end.


Definition mutexlock (vl: vallist) :=
  match vl with
    (V_mux :: V_pos :: V_eid0 :: V_eid :: V_ow :: V_tp :: V_curp :: V_pcp :: V_rcnt ::  V_pevt :: V_err :: V_afteid :: V_ret :: nil)=>
      (mutexlock_muxerr (| V_mux :: V_pos :: nil |) ??
         mutexlock_mutex_pos (| V_mux :: V_pos :: nil |)) ;;
      (mutexlock_poserr (| V_pos :: V_ret :: nil |) ??
         (mutexlock_ecb_ptr (| V_pos :: V_eid0 :: nil |) ;;
          (mutexlock_ecb_nullerr (| V_eid0 :: V_ret :: nil |) ??
             (mutexlock_ecb_ptr (| V_pos :: V_eid :: nil |) ;;
              (mutexlock_ecb_nullerr (| V_eid :: V_ret :: nil |) ??
                 mutexlock_owner (| V_pos :: V_eid :: V_ow :: nil |) ;;
               mutexlock_type (| V_pos :: V_tp :: nil |) ;;
               (mutexlock_typeerr (| V_tp :: V_ret :: nil |) ??
                  (mutexlock_curprio (| V_curp :: nil |) ;;
                   mutexlock_prioceiling (| V_pos :: V_pcp :: nil |) ;;
                   (mutexlock_type_deadlk (| V_tp :: V_ow :: V_curp :: V_pcp :: V_ret :: nil |) ??
                      (mutexlock_recurcnt (| V_pos :: V_rcnt :: nil |) ;;
                       (mutexlock_type_recur_incre_one (| V_pos :: V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |) ??
                          mutexlock_type_recur_again (| V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |))) ??
                      (mutexlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                       mutexlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                       (mutexpend (V_pevt :: (Vint32 Int.zero) :: V_err :: nil)) ;; 
                       ( mutexlock_set_evloc_ptr (| Vnull :: nil |) ;;
                         (mutexlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                            (mutexlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                             (mutexlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                                mutexlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))))) ) ??
                  ( mutexlock_type_normal (| V_tp :: nil |) ;;
                    mutexlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                    mutexlock_set_evloc_ptr (| V_pevt :: nil |) ;; 
                    (mutexpend (V_pevt :: (Vint32 Int.zero) :: V_err :: nil)) ;; 
                    ( mutexlock_set_evloc_ptr (| Vnull :: nil |) ;;
                      (mutexlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                         (mutexlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                          (mutexlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                             mutexlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) )))))
  | _ => spec_abort
  end.

Open Scope code_scope.

Definition mutexlockapi := (mutexlock, (Tint32, Tptr pthread_mutex_t::nil)).

(* (****************************** pthread_mutex_timedlock ************************************) *)

Definition mutextimedlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v_pos,
      vl = (v :: v_pos :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v_pos = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v_pos <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutextimedlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v_pos pbls,
      vl = ((Vptr a) :: v_pos :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        get O1 pblsid = Some (pblist pbls) /\
        opv = None /\
        ((exists posv,
               (get pbls a = Some posv /\
                  (v_pos = (Vint32 posv) /\ O_opt = Some O1 \/ v_pos <> (Vint32 posv) /\ O_opt = None)))
          \/ get pbls a = None /\ O_opt = None)
  end.

Definition mutextimedlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextimedlock_timeout_err
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tmv rv ,
      vl = ((Vint32 tmv) :: rv :: nil) /\
        (Int.eq tmv Int.zero = true \/
           Int.ltu (Int.repr 65535) tmv = true) /\
     opv = Some (Vint32 (Int.repr EINVAL)) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None)
  end.

Definition mutextimedlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_pevent :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (((exists eid, e = Valid_Addr eid /\ v_pevent = Vptr eid) \/ e = Null /\ v_pevent = Vnull)
           /\ O_opt = Some O1
           \/
             (e = Holder \/ 
                (exists eid, e = Valid_Addr eid /\ v_pevent <> Vptr eid) \/ (e = Null /\ v_pevent <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutextimedlock_ecb_nullerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv,
      (vl = Vnull :: rv :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end.

Definition mutextimedlock_owner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n pro w c, 
        exists pcp qls pr y wl v_ow,
      vl =((Vint32 posv) :: (Vptr eid) :: v_ow :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
      get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c) /\
      get O1 absecblsid = Some (absecblist qls) /\
      get qls eid =Some (absmutexsem pr y, wl) /\
      opv = None /\
      ((ow = $ OS_MUTEX_AVAILABLE /\ y = None )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
      ( (v_ow = (Vint32 ow) /\ O_opt = Some O1) \/
          (v_ow <> (Vint32 ow) /\O_opt = None))
  end.

Definition mutextimedlock_type
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_tp posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_tp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (( v_tp = Vint32 x /\ O_opt = Some O1) \/
          ( v_tp <> Vint32 x /\ O_opt = None ))
  end.

Definition mutextimedlock_typeerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp, 
        vl = ((Vint32 tp) :: rv :: nil) /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_NORMAL) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_ERRORCHECK) = false /\
        Int.eq tp (Int.repr PTHREAD_MUTEX_RECURSIVE) = false /\
        opv = Some (Vint32(Int.repr EINVAL)) /\
        ((rv = (Vint32(Int.repr EINVAL)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EINVAL)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_normal
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists tp, 
        vl = ((Vint32 tp) :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_NORMAL) /\
        opv = None /\
        O_opt = Some O1
  end.

Definition mutextimedlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_curp t prio st m sus tls, 
          vl = ( v_curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( v_curp = Vint32 prio /\ O_opt = Some O1) \/
          ( v_curp <> Vint32 prio /\ O_opt = None ))
  end.

Definition mutextimedlock_prioceiling
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pcp posv mls e o x n,
      exists pro pcp w c, 
        vl = ((Vint32 posv) :: v_pcp :: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
        (( v_pcp = Vint32 pcp /\ O_opt = Some O1) \/
          ( v_pcp <> Vint32 pcp /\ O_opt = None ))
  end.

Definition mutextimedlock_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_rcnt posv mls e o x ,
        exists n pro pcp w c , 
        vl = ((Vint32 posv) :: v_rcnt :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pcp, w, c) /\
        opv = None /\
          (( v_rcnt = Vint32 n /\ O_opt = Some O1) \/
          ( v_rcnt <> Vint32 n /\ O_opt = None ))
  end.

Definition mutextimedlock_type_deadlk
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_ERRORCHECK) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        opv = Some (Vint32(Int.repr EDEADLK)) /\
        ((rv = (Vint32(Int.repr EDEADLK)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EDEADLK)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_recur_again
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv tp ow curp pcp rcnt, 
        vl = ((Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = false /\
        opv = Some (Vint32(Int.repr EAGAIN)) /\
        ((rv = (Vint32(Int.repr EAGAIN)) /\ O_opt = Some O1) \/
        (rv <> (Vint32(Int.repr EAGAIN)) /\ O_opt = None))
  end.

Definition mutextimedlock_type_recur_incre_one
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv tp ow curp pcp rcnt, 
      exists mls e o x cn pro pip w c,
        vl = ((Vint32 posv) :: (Vint32 tp) :: (Vint32 ow) :: (Vint32 curp) :: (Vint32 pcp) :: (Vint32 rcnt) :: rv :: nil) /\
        tp =  (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        (Int.eq ow curp = true \/ Int.eq pcp curp = true) /\
        Int.ltu rcnt (Int.repr PTHREAD_MUTEX_RECURSIVE_MAX) = true /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, cn, pro, pip, w, c) /\
        opv = Some (Vint32 Int.zero) /\
        ((rv = (Vint32 Int.zero) /\
           O_opt = Some (set O1 absmutinfoid 
                                      (absmutinfo (set mls posv (e, o, x, (Int.add cn Int.one), pro, pip, w, c))))) \/
        (rv <> (Vint32 Int.zero) /\ O_opt = None))
  end.

Definition mutextimedlock_after_pend_timeout
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_TIMEOUT) = true /\
        opv = Some(Vint32 (Int.repr ETIMEDOUT)) /\
        (( rv = Vint32 (Int.repr ETIMEDOUT) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr ETIMEDOUT) /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_fail
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: rv :: nil) /\
        Int.eq verr (Int.repr OS_TIMEOUT) = false /\
        Int.eq verr (Int.repr OS_NO_ERR) = false /\
        opv = Some(Vint32 (Int.repr EINVAL)) /\
        (( rv = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1) \/
          ( rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_succ_null
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr rv,
        vl = ((Vint32 verr) :: Vnull :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        (( rv = Vint32 Int.zero /\ O_opt = Some O1) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutextimedlock_after_pend_succ_ecb
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists verr eid posv rv,
      exists mls o x n pro pcp w c,
      exists els p ow wl,
        vl = ((Vint32 verr) :: (Vptr eid) :: (Vint32 posv) :: rv :: nil) /\
        verr = (Int.repr OS_NO_ERR) /\
        opv = Some(Vint32 Int.zero) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pcp, w, c) /\
        get O1 absecblsid = Some (absecblist els) /\
        get els eid = Some (absmutexsem p ow,wl) /\
        (( rv = Vint32 Int.zero 
            /\ O_opt = Some (set O1 absmutinfoid 
                                            (absmutinfo (set mls posv (Valid_Addr eid, ow, x, n, pro, pcp, w, c))))) \/
          ( rv <> Vint32 Int.zero /\ O_opt = None ))
  end.

Definition mutextimedlock_set_evloc_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v_pevent ptrmp t,
        vl = (v_pevent :: nil) /\ 
         get O1 evptrid = Some (evptr ptrmp) /\
         get O1 curtid = Some (oscurt t) /\
         opv = None /\
         O_opt = Some (set O1 evptrid (evptr (set ptrmp t (v_pevent, Vnull, Vnull))))
  end.

Definition mutextimedlock (vl: vallist) :=
  match vl with
    (V_mux :: V_tm :: V_pos :: V_eid0 :: V_eid :: V_ow :: V_tp :: V_curp :: V_pcp :: V_rcnt ::  V_pevt :: V_err :: V_afteid :: V_ret :: nil)=>
      (mutextimedlock_muxerr (| V_mux :: V_pos :: nil |) ??
         mutextimedlock_mutex_pos (| V_mux :: V_pos :: nil |)) ;;
      (mutextimedlock_poserr (| V_pos :: V_ret :: nil |) ??
         mutextimedlock_timeout_err (| V_tm :: V_ret :: nil |) ??
         (mutextimedlock_ecb_ptr (| V_pos :: V_eid0 :: nil |) ;;
          (mutextimedlock_ecb_nullerr (| V_eid0 :: V_ret :: nil |) ??
             (mutextimedlock_ecb_ptr (| V_pos :: V_eid :: nil |) ;;
              (mutextimedlock_ecb_nullerr (| V_eid :: V_ret :: nil |) ??
                 mutextimedlock_owner (| V_pos :: V_eid :: V_ow :: nil |) ;;
               mutextimedlock_type (| V_pos :: V_tp :: nil |) ;;
               (mutextimedlock_typeerr (| V_tp :: V_ret :: nil |) ??
                  (mutextimedlock_curprio (| V_curp :: nil |) ;;
                   mutextimedlock_prioceiling (| V_pos :: V_pcp :: nil |) ;;
                   (mutextimedlock_type_deadlk (| V_tp :: V_ow :: V_curp :: V_pcp :: V_ret :: nil |) ??
                      (mutextimedlock_recurcnt (| V_pos :: V_rcnt :: nil |) ;;
                       (mutextimedlock_type_recur_incre_one (| V_pos :: V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |) ??
                          mutextimedlock_type_recur_again (| V_tp :: V_ow :: V_curp :: V_pcp :: V_rcnt :: V_ret :: nil |))) ??
                      (mutextimedlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                       mutextimedlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                       (mutexpend (V_pevt :: V_tm :: V_err :: nil)) ;;  
                       (mutextimedlock_set_evloc_ptr (| Vnull :: nil |) ;;
                        (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                           mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                           (mutextimedlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                            (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                               mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) ) ??
                  (mutextimedlock_type_normal (| V_tp :: nil |) ;;
                    mutextimedlock_ecb_ptr (| V_pos :: V_pevt :: nil |) ;;
                    mutextimedlock_set_evloc_ptr (| V_pevt :: nil |) ;;
                    (mutexpend (V_pevt :: V_tm :: V_err :: nil)) ;;  
                    (mutextimedlock_set_evloc_ptr (| Vnull :: nil |) ;;
                     (mutextimedlock_after_pend_timeout (| V_err :: V_ret :: nil |) ??
                        mutextimedlock_after_pend_fail (| V_err :: V_ret :: nil |) ??
                        (mutextimedlock_ecb_ptr (| V_pos :: V_afteid :: nil |) ;;
                         (mutextimedlock_after_pend_succ_null (| V_err :: V_afteid :: V_ret :: nil |) ??
                            mutextimedlock_after_pend_succ_ecb (| V_err :: V_afteid :: V_pos :: V_ret :: nil |))))) )) )))))
  | _ => spec_abort
  end.

Open Scope code_scope.

Definition mutextimedlockapi:=(mutextimedlock, (Tint32,Tptr pthread_mutex_t:: Tint16 :: nil)).

(* (****************************** pthread_mutex_unlock ************************************) *)

Definition mutexunlock_muxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v v',
      vl = (v :: v' :: nil) /\
        (v = Vnull \/
           exists a,
             v = Vptr a /\ 
               (cmpaddr Cle a userAddrStart = true \/ cmpaddr Clt userAddrEnd a = true)
        ) /\ 
        opv = None /\
        (v' = (Vint32 (Int.mone)) /\ O_opt = Some O1 \/
           v' <> (Vint32 (Int.mone)) /\ O_opt = None)
  end.

Definition mutexunlock_mutex_pos
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists a v',
      vl = ((Vptr a) :: v' :: nil) /\
        cmpaddr Clt userAddrStart a = true /\
        cmpaddr Cle a userAddrEnd = true /\
        (~(exists i, v' = Vint32 i) /\ O_opt = None \/
           exists pbls, 
           get O1 pblsid = Some (pblist pbls) /\
             opv = None /\
             ((exists posv,
                  (get pbls a = Some posv /\
                  (v' = (Vint32 posv) /\ O_opt = Some O1 \/ v' <> (Vint32 posv) /\ O_opt = None)))
                \/ get pbls a = None /\ O_opt = None))
  end.

Definition mutexunlock_poserr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv rv ,
      vl = ((Vint32 posv) :: rv :: nil) /\
        (Int.ltu posv Int.zero = true \/
           Int.ltu (Int.repr 6) posv = true \/ posv = Int.repr 6) /\
        (rv = (Vint32 (Int.repr EINVAL)) /\ O_opt = Some O1 /\ opv = Some rv
         \/ rv <> Vint32 (Int.repr EINVAL) /\ O_opt = None /\  opv = None )
  end.

Definition mutexunlock_ecb_ptr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pi pro,
        exists c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
          (((exists eid, e = Valid_Addr eid /\ v' = Vptr eid) \/ e = Null /\ v' = Vnull)
           /\ O_opt = Some O1
           \/
             (((~exists eid, e = Valid_Addr eid) /\ e <> Null) \/ 
                ((exists eid, e = Valid_Addr eid /\ v' <> Vptr eid) \/ e = Null /\ v' <> Vnull))
             /\ O_opt = None)
  end. 

Definition mutexunlock_get_ecb_ptr1 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c ptrmp t, 
    vl = ((Vint32 posv) :: v' :: nil) /\ 
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Null, o, x, n, pro, pi, w, c) /\
    get O1 evptrid = Some (evptr ptrmp) /\ 
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\
    opv = None /\
    (v' = Vnull /\ O_opt = Some O1 \/ v' <> Vnull /\ O_opt = None)  
  end.

Definition mutexunlock_get_ecb_ptr2
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls o x n w pi pro,
        exists c ptrmp t eid, 
    vl = ((Vint32 posv) :: v' :: nil) /\
          ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
             Int.ltu posv (Int.repr 6) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c) /\
    get O1 evptrid = Some (evptr ptrmp) /\
    get O1 curtid = Some (oscurt t) /\
    get ptrmp t = Some (Vnull, Vnull, Vnull) /\ 
    opv = None /\
    (v' = Vptr eid /\ O_opt = Some (set O1 evptrid (evptr (set ptrmp t ( Vptr eid, Vnull, Vnull)))) \/ 
     v' <> Vptr eid /\ O_opt = None)
  end. 

Definition mutexunlock_ecb_ptr_holder_abt 
           (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists posv mls o x n pro pi w c, 
    vl = ((Vint32 posv) :: nil) /\ 
    ((posv = Int.zero \/ Int.ltu Int.zero posv = true) /\
     Int.ltu posv (Int.repr 6) = true) /\
    get O1 absmutinfoid = Some (absmutinfo mls) /\
    get mls posv = Some (Holder, o, x, n, pro, pi, w, c) /\
    opv = None /\
    O_opt = None 
  end.

Definition mutexunlock_if_null_yes
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = Vnull :: v' :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        ((v' = Vint32 (Int.repr EINVAL) /\ O_opt = Some O1)
         \/ (v' <> Vint32 (Int.repr EINVAL) /\ O_opt = None))
  end. 

Definition mutexunlock_if_null_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists eid,
      (vl = (Vptr eid) :: nil) /\
        opv = None /\
        O_opt = Some O1
  end. 

Definition mutexunlock_if_null_owner_no
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv eid ow mls o x n w pi pro, 
        exists c qls pr y wl rv,
      vl =((Vint32 posv) :: (Vptr eid) :: rv :: nil) /\
      get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (Valid_Addr eid, o, x, n, pro, pi, w, c) /\
        get O1 absecblsid = Some (absecblist qls) /\
        get qls eid =Some (absmutexsem pr y, wl) /\
        ((y = None /\ ow = $ OS_MUTEX_AVAILABLE   )
          \/( exists t op,  y = Some (t, op) /\ ow = op)) /\
          ( (rv = (Vint32 ow) /\ O_opt = Some O1) \/
           (rv <> (Vint32 ow) /\O_opt = None) )/\
        opv = None 
  end. 

Definition mutexunlock_recurtype
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x n w pi pro,
        exists c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None  /\
          (( v' = Vint32 x /\ O_opt = Some O1) \/
          ( v' <> Vint32 x /\ O_opt = None ))
  end.

Definition mutexunlock_curprio
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists curp t prio st m sus tls, 
          vl = ( curp :: nil) /\  
          get O1 abstcblsid = Some (abstcblist tls) /\
          get O1 curtid = Some (oscurt t) /\
          get tls t = Some (prio,st,m,sus) /\ 
          opv = None /\
          (( curp = Vint32 prio /\ O_opt = Some O1) \/
          ( curp <> Vint32 prio /\ O_opt = None ))
  end. 

Definition mutexunlock_prioceil
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv v' mls e o x n w pi pro,
        exists c, 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
        (( v' = Vint32 pi /\ O_opt = Some O1) \/
        ( v' <> Vint32 pi /\ O_opt = None ))
  end.

Definition mutexunlock_get_recurcnt
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v' posv mls e o x pi ,
        exists n w pro c , 
        vl = ((Vint32 posv) :: v' :: nil) /\ 
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (e, o, x, n, pro, pi, w, c) /\
        opv = None /\
        (( v' = Vint32 n /\ O_opt = Some O1) \/
        ( v' <> Vint32 n /\ O_opt = None ))
  end.

Definition mutexunlock_recvcnt_decrement_oweq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists cn posv x tp ow curp mls eid o w , 
      exists pi pro pe c priocl,
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl):: nil) /\
        get O1 absmutinfoid = Some (absmutinfo mls) /\
        get mls posv = Some (pe, o, x, cn, pro, pi, w, c) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
       ( ow = curp \/ priocl = curp ) /\
        opv = None /\
        O_opt = Some (set O1 absmutinfoid (absmutinfo (set mls posv (pe, o, x, (Int.sub cn Int.one), pro, pi, w, c))))
  end.

Definition mutexunlock_if_ow_curp_neq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists posv ow tp curp eid rv priocl, 
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 ow) :: (Vint32 tp) :: (Vint32 curp) :: (Vint32 priocl) :: rv :: nil) /\
        tp = (Int.repr PTHREAD_MUTEX_RECURSIVE) /\
        Vint32 ow <> Vint32 curp /\
        Vint32 priocl <> Vint32 curp /\
        opv = Some (Vint32 (Int.repr EPERM)) /\
        ((rv = (Vint32 (Int.repr EPERM)) /\ O_opt = Some O1) \/
        (rv <> (Vint32 (Int.repr EPERM)) /\ O_opt = None))
  end.

Definition mutexunlock_if_rcnt_zero_neq
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists rv posv  eid rcnt, 
        vl = ((Vint32 posv) :: (Vptr eid) :: (Vint32 rcnt ) :: rv :: nil) /\
        Int.eq rcnt Int.zero =false /\
        opv = Some (Vint32 (Int.zero)) /\
        ((rv = (Vint32 (Int.zero)) /\ O_opt = Some O1) \/
        (rv <> (Vint32 (Int.zero)) /\ O_opt = None)) 
  end.

Definition mutexunlock_after_post_errowner
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp',
      vl = (Vint32 v) :: nil /\
        Int.eq (Int.repr OS_ERR_NOT_MUTEX_OWNER) v = true /\ 
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        opv = None /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end. 

Definition mutexunlock_after_post_errzero
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp',
      vl = (Vint32 v) :: nil /\
        Int.eq (Int.repr OS_ERR_NOT_MUTEX_OWNER) v = false /\
        Int.eq (Int.repr 0) v = false /\ 
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        opv = None /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end. 

Definition mutexunlock_after_post_errno
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v t ptrmp ptrmp',
      vl = (Vint32 v) :: nil /\
        Int.eq (Int.repr OS_ERR_NOT_MUTEX_OWNER) v = false /\ 
        Int.eq (Int.repr 0) v = true /\ 
        get O1 curtid = Some (oscurt t) /\
        get O1 evptrid = Some (evptr ptrmp) /\
        ptrmp' = set ptrmp t (Vnull, Vnull, Vnull) /\
        opv = None /\
        O_opt = Some (set O1 evptrid (evptr ptrmp')) 
  end. 

Definition mutexunlock_afterpost_rv1
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr EPERM)) /\ 
        O_opt = Some O1
  end. 

Definition mutexunlock_afterpost_rv2
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr EINVAL)) /\ 
        O_opt = Some O1
  end. 

Definition mutexunlock_afterpost_rv3
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
      exists v',
      (vl = v' :: nil) /\
        opv = Some (Vint32 (Int.repr 0)) /\ 
        O_opt = Some O1
  end. 

Definition muxpost (V_pos:val) (V_pevt:val) (V_postrv:val) (V_ret:val) := 
  (mutexunlock_get_ecb_ptr1 (|V_pos:: V_pevt :: nil|) ??
     mutexunlock_get_ecb_ptr2 (|V_pos:: V_pevt :: nil|) ??
     mutexunlock_ecb_ptr_holder_abt(|V_pos :: nil|)) ;;
  (mutexpost (V_pevt :: V_postrv::nil)) ;;
  ((mutexunlock_after_post_errowner(|V_postrv :: nil|);; mutexunlock_afterpost_rv1(|V_ret :: nil|)) ??
     (mutexunlock_after_post_errzero(|V_postrv :: nil|);;mutexunlock_afterpost_rv2(| V_ret :: nil|)) ??
     (mutexunlock_after_post_errno(|V_postrv :: nil|);;mutexunlock_afterpost_rv3(| V_ret :: nil|))).

Definition mutexunlock (vl: vallist) :=
  match vl with
    (V_mux :: V_pos :: V_eid :: V_ow :: V_tp :: V_curp :: V_priocl :: V_pevt :: V_rcnt :: V_eid0 :: V_postrv :: V_ret :: nil)=>
      (mutexunlock_muxerr (|V_mux :: V_pos :: nil|) ??
         mutexunlock_mutex_pos(|V_mux :: V_pos :: nil|));;
      (mutexunlock_poserr (|V_pos :: V_ret :: nil|) ?? 
         (mutexunlock_ecb_ptr (|V_pos :: V_eid :: nil|);; 
          (mutexunlock_if_null_yes (|V_eid :: V_ret :: nil|) ??
             (mutexunlock_if_null_no (|V_eid :: nil|) ;;
              mutexunlock_ecb_ptr (|V_pos :: V_eid0 :: nil|) ;;
              (mutexunlock_if_null_yes (|V_eid0 :: V_ret :: nil|) ??
                 (mutexunlock_if_null_owner_no (|V_pos :: V_eid0 :: V_ow :: nil|) ;;
                  mutexunlock_recurtype(|V_pos :: V_tp :: nil|) ;; 
                  ((  mutexunlock_curprio(| V_curp :: nil|) ;; mutexunlock_prioceil(|V_pos :: V_priocl :: nil|) ;;
                      (  ( mutexunlock_recvcnt_decrement_oweq(|V_pos :: V_eid0 :: V_ow :: V_tp :: V_curp :: V_priocl :: nil|) ;;
                           (  mutexunlock_get_recurcnt (|V_pos :: V_rcnt :: nil|) ;; 
                              ( mutexunlock_if_rcnt_zero_neq (|V_pos :: V_eid0  :: V_rcnt :: V_ret :: nil|) ??
                                  ( muxpost V_pos V_pevt V_postrv V_ret)
                         ))) ??
                           mutexunlock_if_ow_curp_neq (|V_pos :: V_eid0 :: V_ow :: V_tp :: V_curp :: V_priocl :: V_ret :: nil|))
                   )??
                     ( muxpost V_pos V_pevt V_postrv V_ret)
      )))))))
  | _ => spec_abort
  end.
Open Scope code_scope.
Definition mutexunlockapi:=(mutexunlock, (Tint32,Tptr pthread_mutex_t::nil)).

