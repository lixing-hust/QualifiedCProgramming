
Require Import PIF_os_code_defs.
Require Import PIF_code_notations.

Open Scope code_scope.
Open Scope Z_scope.

Definition gjb_pos_blk : ident := 1901%Z.
Definition nextpblk : ident := 1902%Z.
Definition posval : ident := 1903%Z.

Definition gjb_pos_blk_t : type :=
  STRUCT gjb_pos_blk ­{
      ⌞
        posval @ Int32u ;  
        nextpblk @ STRUCT gjb_pos_blk ⋆ 
      ⌟ 
    }­.

Definition V_posblk_pos (vl:vallist) := nth_val 0 vl.
Definition V_posblk_next (vl:vallist) := nth_val 1 vl. 

Definition GJB_pos_list : ident := 1911%Z.

Definition gjb_err_blk : ident := 1904%Z.
Definition nexteblk : ident := 1905%Z.
Definition errval : ident := 1906%Z.

Definition gjb_err_blk_t : type :=
  STRUCT gjb_err_blk ­{
      ⌞
        errval @ Int8u ;  
        nexteblk @ STRUCT gjb_err_blk ⋆ 
      ⌟ 
    }­.

Definition V_errblk_err (vl:vallist) := nth_val 0 vl.
Definition V_errblk_next (vl:vallist) := nth_val 1 vl. 

Definition GJB_err_list : ident := 1912%Z.  

Definition V_muxattr_isinit     (vl:vallist) := nth_val 0 vl.
Definition V_muxattr_procshared (vl:vallist) := nth_val 1 vl.
Definition V_muxattr_prioceiling (vl:vallist) := nth_val 2 vl.
Definition V_muxattr_protocol       (vl:vallist) := nth_val 3 vl.
Definition V_muxattr_recursive      (vl:vallist) := nth_val 4 vl.
Definition V_muxattr_waitq     (vl:vallist) := nth_val 5 vl.
Definition V_muxattr_cancelsafe      (vl:vallist) := nth_val 6 vl.


Fixpoint set_tls_rdy (wl: list addrval) (tls: TcbMod.map) : TcbMod.map :=
match wl with
 | nil => tls
 | tid :: wl' => match TcbMod.get tls tid  with 
                            | None => set_tls_rdy wl' tls
                            | Some (p, st, m, sus) => set_tls_rdy wl' (set tls tid (p,rdy,Vnull, sus))
                            end
end.

Fixpoint set_tls_rdy0 (wl: list addrval) (tls: TcbMod.map) : TcbMod.map :=
  match wl with
  | nil => tls
  | tid :: wl' => match TcbMod.get tls tid  with 
                  | None => set_tls_rdy0 wl' tls
                  | Some (p, _, m, sus) => set_tls_rdy0 wl' (set tls tid (p, rdy, m, sus))
                  end
  end.

Local Open Scope int_scope.

(* ucos_lib/events/sem_getvalue_pure.v *) 
Fixpoint get_tls_blocked_num (tls : TcbMod.rlist) (sid: addrval) :=
match tls with
| nil => 0%nat
| ( (tid,(p,st,m,sus)) :: tls') => 
        match st with
        | wait (os_stat_sem eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_num tls' sid)
                                                                     else (get_tls_blocked_num tls' sid)
        | _ => (get_tls_blocked_num tls' sid)
        end
end.

(* ucos_lib/events/sem_getvalue_pure.v *) 
Fixpoint Int_sub_n (n:nat) (vh: int32) (vsub: int32) :int32 :=
match n with
0%nat => vh
| S n' => Int.sub (Int_sub_n n' vh vsub) vsub
end.

(* ucos_lib/events/mq_getinfo_pure.v *) 
Fixpoint get_tls_blocked_q_num (tls : TcbMod.rlist) (sid: addrval) :=
match tls with
| nil => 0%nat
| ( (tid,(p,st,m,sus)) :: tls') => 
        match st with
        | wait (os_stat_q eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_q_num tls' sid)
                                                                     else (get_tls_blocked_q_num tls' sid)
        | wait (os_stat_postq eid) t => if tidspec.beq eid sid then Nat.add 1%nat (get_tls_blocked_q_num tls' sid)
                                                                     else (get_tls_blocked_q_num tls' sid)
        | _ => (get_tls_blocked_q_num tls' sid)
        end
end.

(* ucos_lib/events/mq_getinfo_pure.v *) 
Fixpoint Int_add_n (n:nat) (vh: int32) (vadd: int32) :int32 :=
match n with
0%nat => vh
| S n' => Int.modu (Int.add (Int_add_n n' vh vadd) vadd) ($ Byte.modulus)
end.

(* spec/os_inv.v *)
Fixpoint Get_struct (l: (list (addrval * type * (list val))))(a: addrval) :  (option (addrval * type * (list val))) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_struct l' a 
                                   end  
end.

(* spec/os_inv.v *)
Fixpoint Get_array (l: (list (addrval * nat * (list val))))(a: addrval) :  (option (addrval * nat * (list val))) :=
  match l with 
  | nil => None
  | (ad, n, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, n, vl )
                                   | false => Get_array l' a 
                                   end  
end.

(* ucos_lib/events/gjb_mutex_common.v *)
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

(* ucos_lib/events/evheap_pure.v *)
Fixpoint Get_heap (l: (list (addrval * type * val)))(a: addrval) :  (option (addrval * type * val )) :=
  match l with 
  | nil => None
  | (ad, t, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => Some (a, t, vl )
                                   | false => Get_heap l' a 
                                   end  
end.

(* not good to import ucos_lib/events/sem_common.v in abs_op.v or ifun_spec.v *)
(* hence moved def of Set_struct' here *) 
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

(* used in spec of OSQQuery *) 
Fixpoint Set_array' (l: (list (addrval * nat * (list val))))(a: addrval) (vl': list val)
     :  (list (addrval * nat * (list val))):=
  match l with 
  | nil => nil  
  | (ad, n, vl ) :: l' => match (beq_tid ad a) with
                                   | true  => (ad, n , vl') :: l'
                                   | false => ((ad, n, vl ) :: (Set_array' l' a vl'))
                                   end
end.  

(* ucos_lib/events/evheap_pure.v *)
Fixpoint Set_sval (l: (list (addrval * type *  val )))(a: addrval) (b: val)
     :  (list (addrval * type *  val)):=
  match l with 
  | nil => nil  
  | (ad, t, v ) :: l' => match (beq_tid ad a) with
                                   | true  => ((a, t, b) :: l')
                                   | false => ((ad, t, v ) :: (Set_sval l' a b))
                                   end
end.

(* Definition V_OSSINFOPevent (vl:vallist) := nth_val 7 vl.  *)

(* ucos_lib/events/gjb_sem_common.v *)
Definition Seminfo_full_P semvl :=
forall i vl1, 0 <= i /\ i < Z.of_nat (length semvl) ->
                        nth_vallist (nat_of_Z i) semvl = Some vl1 ->
                        ~(nth_val 7 vl1 = Some Vnull).

(* ucos_lib/events/gjb_sem_common.v *)
Definition nth_Seminfo_free_P i semvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length semvl) /\ 
                      nth_vallist (nat_of_Z i) semvl = Some vl1 /\
                      nth_val 7 vl1 = Some Vnull.

(* Definition V_OSMUXINFOPevent (vl:vallist) := nth_val 8 vl. *) 

(* ucos_lib/events/gjb_mutex_common.v *)
Definition PthreadMutex_full_P muxvl :=
forall i vl1, (0 <= i /\ i < Z.of_nat (length muxvl)) ->
                        nth_vallist (nat_of_Z i) muxvl = Some vl1 ->
                        ~(nth_val 8 vl1 = Some Vnull).

(* ucos_lib/events/gjb_mutex_common.v *)
Definition nth_PthreadMutex_free_P i muxvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length muxvl) /\ 
                      nth_vallist (nat_of_Z i) muxvl = Some vl1 /\
                      nth_val 8 vl1 = Some Vnull.

(* Definition V_QATTRpevent (vl:vallist) := nth_val 5 vl.  *)

(* ucos_lib/events/gjb_q_common.v *) 
Definition Qattr_full_P mqvl :=
forall i vl1, (0 <= i /\ i < Z.of_nat (length mqvl)) ->
                        nth_vallist (nat_of_Z i) mqvl = Some vl1 ->
                        ~(nth_val 5 vl1 = Some Vnull). 

(* ucos_lib/events/gjb_q_common.v *) 
Definition nth_Qattr_free_P i mqvl :=
exists vl1, 0 <= i /\ i < Z.of_nat (length mqvl) /\ 
                      nth_vallist (nat_of_Z i) mqvl = Some vl1 /\
                      nth_val 5 vl1 = Some Vnull.  



Close Scope code_scope. 
