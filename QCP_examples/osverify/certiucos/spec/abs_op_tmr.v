Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(**************************** sys_clk_rate_get *********************************)

Definition osclk_rate_get (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
      | (opv, Some O2) =>
          vl= nil/\
          (
            exists clkrate,
               get O1 osclkrateid = Some (osrate clkrate)/\
              opv =  (Some (Vint32 clkrate))/\ 
              O2 = O1
          )
      | (opv, None) => False
    end.

Definition clkrategetcode (vl : vallist):=  osclk_rate_get(|nil|).

Definition clkrategetapi:=(clkrategetcode,(Tint32,(nil:typelist))).

(**************************** sys_clk_rate_set *********************************)

Definition osclk_rate_set_nop (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
      | (opv, Some O2) =>
          exists v, 
          vl= ((Vint32 v)::nil)/\
          opv = Some (Vint32 (Int.repr (Zneg xH))) /\
          Int.ltu v (Int.repr 1) = true /\  
          O2 = O1
      | (opv, None) => False
    end.

Definition osclk_rate_set (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
        | (opv, Some O2) =>
            exists v, 
            vl= ((Vint32 v)::nil)/\
            opv = None /\
            Int.ltu v (Int.repr 1) = false /\  
            O2 = set O1 osclkrateid (osrate v)
        | (opv, None) => False
    end.

(* 在定时器模块进入的时候 假设都不在定时器出错的情况*)
Definition TMRnotERROR (O : osabst) : Prop :=
  exists tmrls, get O ostmrid = Some (ostmr (Some tmrls)).
  
Definition osclk_rate_set_update_systmr (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
        | (opv, Some O2) =>
            exists v, 
            vl= ((Vint32 v)::nil)/\
            opv = Some (Vint32 Int.zero) /\
            Int.ltu v (Int.repr 1) = false /\  
            exists p, p =  (1000000000 / (Int.unsigned v * 6))%Z /\
            exists tmrls tmrls', 
            get O1 ostmrid = Some (ostmr (Some tmrls)) /\
            tmrls' = set tmrls DNUM (gp_t p continuously, tm_start, 0%Z, om_clock) /\
            O2=set O1 ostmrid (ostmr (Some tmrls')) 
        | (opv, None) => False
    end.

Definition clkratesetcode (vl : vallist):=  
  match vl with 
  | nil => spec_abort 
  | v0 :: _ => osclk_rate_set_nop (|v0 :: nil |) ?? 
               ASSERT TMRnotERROR;; 
               osclk_rate_set (|v0 :: nil|) ;; osclk_rate_set_update_systmr  (|v0 :: nil|)
  end.

Definition clkratesetapi:=(clkratesetcode,(Tint32, Tint32 :: nil)).

(**************************** tmr cre ******************************************)
Definition tmr_valvptr (v1 : val) (O1 : osabst) : Prop :=
  match v1 with
    | Vptr x => True
    | _ => False
  end. 


Definition tmrcre_iderror (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
      | (opv, Some O2) =>
       exists v prdlo prdhi mode f arg,
         vl= ((Vint32 v)::(Vint32 prdlo):: (Vint32 prdhi) :: (Vint32 mode)::f::arg::nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         ( Int.ltu (Int.repr 7) v = false \/ Int.ltu v (Int.repr 16) = false ) /\
         O2=O1 
      | (opv, None) => False
    end. 

Definition cre_tmr_mode (p: Z) (mode : int32) :=
  if (Int.eq Int.zero mode) then (gp_t p onetime, tm_idle, 0%Z, om_clock) else  (gp_t p continuously, tm_idle, 0%Z, om_clock).

Definition tmrcre_config_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
      | (opv, Some O2) =>
       exists v prdlo prdhi mode f arg,
         vl= ((Vint32 v)::(Vint32 prdlo):: (Vint32 prdhi) :: (Vint32 mode)::f::arg::nil) /\
         opv = None /\
         exists tmrls p, 
            get O1 ostmrid = Some (ostmr (Some tmrls)) /\ 
            Int.ltu v (Int.repr 16) = true /\ 
            Int.ltu (Int.repr 7) v = true /\
            (p = Int.unsigned prdlo +  Int.unsigned prdhi * Int.modulus )%Z /\
            exists tmrls', 
            tmrls' = set tmrls (Int.unsigned v) (cre_tmr_mode p mode) /\
            O2=set O1 ostmrid (ostmr (Some tmrls'))
      | (opv, None) => False
    end.

(* AOSInthandler 数组为什么存的值不是 f address 而是 0 ， 1 ？ *)

(* install_handler_6678_succ  ? *)
(* int_install_handler_6678_impl 代码里注释了 param 的更新*)
Definition tmrcre_inthandler_error (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v prdlo prdhi mode f arg,
       vl= ((Vint32 v)::(Vint32 prdlo):: (Vint32 prdhi) :: (Vint32 mode)::f::arg::nil) /\
       opv = Some (Vint32 (Int.repr (Zneg xH))) /\
       exists ih,
        get O1 inthandlerid = Some (hinthandler ih) /\ 
        ih (Int.repr INT_NUM_MAX) =  Int.zero (* intdhandler 已经满了 ？？？？ Int.zero*) /\
        O2=set O1 ostmrid (ostmr None) (*表示出错*)
    | (opv, None) => False
  end.


Definition nextinthandler_id ih i:= 
  (INT_NUM_MIN <= i <= INT_NUM_MAX)%Z /\ ih (Int.repr i) = Int.one /\
  (forall i',  INT_NUM_MIN <= i' -> i' < i -> ih (Int.repr i') = Int.zero )%Z.
   

Definition tmrcre_inthandler_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v prdlo prdhi mode fl argl,
       vl= ((Vint32 v)::(Vint32 prdlo):: (Vint32 prdhi) :: (Vint32 mode):: Vptr fl :: Vptr argl ::nil) /\
       opv = Some (Vint32 (Int.repr 0)) /\
       exists ih ih' i,
       get O1 inthandlerid = Some (hinthandler ih) /\ 
        nextinthandler_id ih i /\
        (forall x, if Int.eq x (Int.repr i) then ih' x = Int.one else ih' x = ih x) /\
        O2 = set O1 inthandlerid (hinthandler ih')
    | (opv, None) => False
  end.

Definition tmrcre (vl : vallist):= 
  match vl with 
  | nil => spec_abort 
  | v0 :: nil => spec_abort 
  | v0 :: v1 :: nil => spec_abort 
  | v0 :: v1 :: v2 :: nil => spec_abort 
  | v0 :: v1 :: v2 :: v3 :: nil => spec_abort
  | v0 :: v1 :: v2 :: v3 :: v4 :: nil => spec_abort
  | v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: _ 
              =>tmrcre_iderror (|v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil |) ??
                ASSERT TMRnotERROR;;  
                tmrcre_config_succ (|v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil|) ;; 
               (tmrcre_inthandler_error (|v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil|) ?? 
                ASSERT tmr_valvptr v4;;  ASSERT tmr_valvptr v5;;
                tmrcre_inthandler_succ (|v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: nil|))
  end.

Definition tmrcreapi:=(tmrcre,(Tint32, Tint32 :: Tint32 :: Tint32 :: Tint32 :: Tptr Tvoid ::Tptr Tvoid :: nil)).

(**************************** tmr del ******************************************)
Definition tmrdel_succ (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
      | (opv, O2) =>
       exists v,
         vl= ((Vint32 v)::nil) /\
         opv = Some (Vint32 (Int.repr 0)) /\
         Int.ltu v (Int.repr 16) = true /\ 
         Int.ltu (Int.repr 7) v = true /\
         exists tmrls tmr tmrls',
            get O1 ostmrid = Some (ostmr (Some tmrls)) /\ 
            join (sig (Int.unsigned v) tmr) tmrls' tmrls /\
            O2=Some (set O1 ostmrid (ostmr (Some tmrls')))
    end.
 
Definition tmrdel_iderror (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
    match rst with
      | (opv, Some O2) =>
       exists v,
         vl= ((Vint32 v)::nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         ( Int.ltu (Int.repr 7) v = false \/ Int.ltu v (Int.repr 16) = false ) /\
         O2=O1 
      | (opv, None) => False
    end. 

Definition tmrdel_tmrnone (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
      exists v,
      vl= ((Vint32 v)::nil) /\
      opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get tmrls (Int.unsigned v) = None /\
         O2=O1
    | (opv, None) => False
  end.


Definition tmrdel (vl : vallist):= 
   match vl with
  | nil => spec_abort
  | v :: vl' => tmrdel_iderror (|v::nil|) ?? 
                ASSERT TMRnotERROR;;
               (tmrdel_tmrnone (|v::nil|) ?? 
                tmrdel_succ (|v::nil|))
  end.

Definition tmrdelapi:=(tmrdel,(Tint32, Tint32 ::  nil)).

(**************************** tmr get ******************************************)
Definition tmrget_iderror (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists i x0 x,
       vl= ((Vint32 i):: x0 :: x :: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         (Int.ltu (Int.repr 7) i = false \/ Int.ltu i (Int.repr 16) = false) /\
         O2=O1
    | (opv, None) => False
  end.

Definition tmrget_tmrnone (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v x0 x,
       vl= ((Vint32 v):: x0 :: x :: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get tmrls (Int.unsigned v) = None /\
         O2=O1
    | (opv, None) => False
  end.

Definition In_heape_addrval (cheape : list (addrval * type * val)) (l: addrval) (t: type) :=
  exists v, In (l,t,v) cheape.

Definition update_heape_addrval (cheape : list (addrval * type * val)) (l: addrval) (t: type) (v: val) (rst : list (addrval * type * val)):Prop:=
  exists cheape1 cheape2 v', cheape = cheape1 ++ (l,t,v') ::cheape2 /\ 
  rst = cheape1 ++ (l,t,v) ::cheape2.
  

Definition tmrget_succ_update_low (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2') =>
    exists v cntl cnth,
    vl= ((Vint32 v)::(Vptr cntl) :: (Vptr cnth) :: nil) /\
         opv = Some (Vint32 (Int.repr 1)) /\ 
         Int.ltu v (Int.repr 16) = true /\ 
         Int.ltu (Int.repr 7) v = true /\
         exists tmrls cHeapl cHeape cHeapt tmrtick tmr st om, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get O1 oscoreheapid = Some (oscoreheap (cHeapl,cHeape, cHeapt )) /\
         get tmrls (Int.unsigned v) =  Some (tmr, st, tmrtick, om) /\
         ((In_heape_addrval cHeape cntl Tint32 /\
         exists cheape', 
         update_heape_addrval cHeape cntl Tint32 (Vint32 (Int.repr tmrtick)) cheape' /\
         O2' =Some (set O1 oscoreheapid  (oscoreheap (cHeapl, cheape', cHeapt ))) )  
        \/ ( ~ In_heape_addrval cHeape cntl Tint32   /\ 
         O2' = None) 
         )
  end.

Definition tmrget_succ_update_high (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2') =>
    exists v cntl cnth,
    vl= ((Vint32 v)::(Vptr cntl) :: (Vptr cnth) :: nil) /\
         opv = Some (Vint32 (Int.repr 0)) /\ 
         Int.ltu v (Int.repr 16) = true /\ 
         Int.ltu (Int.repr 7) v = true /\
         exists tmrls cHeapl cHeape cHeapt tmrtick tmr st om, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get O1 oscoreheapid = Some (oscoreheap (cHeapl,cHeape, cHeapt)) /\
         get tmrls (Int.unsigned v) =  Some (tmr, st, tmrtick, om) /\
         ((In_heape_addrval cHeape cnth Tint32 /\
         exists cheape', 
         update_heape_addrval cHeape
                      cnth Tint32 (Vint32 (Int.repr (Z.div tmrtick Int.modulus))) cheape' /\
         O2' =Some (set O1 oscoreheapid  (oscoreheap (cHeapl, cheape', cHeapt)))) 
         \/ 
         (~ In_heape_addrval cHeape cnth Tint32   /\ 
         O2' = None)
         )
  end.

Definition tmrget (vl : vallist) :=
  match vl with
  | nil => spec_abort
  | v :: nil => spec_abort
  | _ :: _ :: nil => spec_abort 
  | v0 :: v1 :: v2 :: vl' =>  tmrget_iderror (|(v0::v1::v2::nil)|) ?? 
                              ASSERT (tmr_valvptr v1);; ASSERT (tmr_valvptr v2);;
                              ASSERT TMRnotERROR;; 
                            ( tmrget_tmrnone (|(v0::v1::v2::nil)|) ??
                              tmrget_succ_update_low (|(v0::v1::v2::nil)|) ;; tmrget_succ_update_high (|(v0::v1::v2::nil)|))
  end.

Definition tmrgetapi:=(tmrget,(Tint32, Tint32 :: Tptr Tint32 :: Tptr Tint32 :: nil)).

(**************************** tmr start ****************************************)

Definition tmrstart_iderror (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         (Int.ltu (Int.repr 7) v =  false  \/ Int.ltu v (Int.repr 16) = false) /\
         O2=O1
    | (opv, None) => False
  end.

Definition tmrstart_tmrnone (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get tmrls (Int.unsigned v) = None /\
         O2=O1
    | (opv, None) => False
  end.
  
Definition tmrstart_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2) =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.zero)) /\
         Int.ltu v (Int.repr 16) = true /\ 
         Int.ltu (Int.repr 7) v = true /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         ( exists tmr st tick om tmrls',
         get tmrls (Int.unsigned v) = Some (tmr, st, tick, om) /\ 
         tmrls' = set tmrls (Int.unsigned v) (tmr, tm_start, tick, om) /\
         O2 = Some (set O1 ostmrid (ostmr (Some tmrls')))) 
  end. 

Definition tmrstart (vl : vallist) :=
  match vl with
  | nil => spec_abort 
  | v1 :: vl' =>  tmrstart_iderror (|v1::nil|) ?? 
                  ASSERT TMRnotERROR;;
                ( tmrstart_tmrnone (|v1::nil|) ?? tmrstart_succ (|v1::nil|))
  end.

Definition tmrstartapi:=(tmrstart,(Tint32, Tint32 :: nil)).

(**************************** tmr stop ****************************************)
Definition tmrstop_iderror (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         (Int.ltu (Int.repr 7) v =  false  \/ Int.ltu v (Int.repr 16) = false) /\
         O2=O1
    | (opv, None) => False
  end.

Definition tmrstop_tmrnone (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, Some O2) =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.repr (Zneg xH))) /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         get tmrls (Int.unsigned v) = None /\
         O2=O1
    | (opv, None) => False
  end.


Definition gptmr_ex (v1: val) (O : osabst) : Prop :=
  exists v, v1 = (Vint32 v) /\ 
  (exists tmrls prd em st tick om, 
  get O ostmrid = Some (ostmr (Some tmrls)) /\ 
  get tmrls (Int.unsigned v) = Some ((gp_t prd em, st, tick, om))). 
  
Definition tmrstop_succ (vl : vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
    | (opv, O2') =>
     exists v,
       vl= ((Vint32 v):: nil) /\
         opv = Some (Vint32 (Int.zero)) /\
         Int.ltu v (Int.repr 16) = true /\ 
         Int.ltu (Int.repr 7) v = true /\
         exists tmrls, 
         get O1 ostmrid = Some (ostmr (Some tmrls)) /\
         exists prd em st tick om tmrls',
         get tmrls (Int.unsigned v) = Some (gp_t prd em, st, tick, om) /\ 
         tmrls' = set tmrls (Int.unsigned v) (gp_t prd em, tm_idle, tick, om) /\
         O2' = Some (set O1 ostmrid (ostmr (Some tmrls')))
  end. 

Definition tmrstop (vl : vallist) :=
  match vl with
  | nil => spec_abort 
  | v1 :: vl' =>  tmrstop_iderror (|v1::nil|) ?? 
                  ASSERT TMRnotERROR;; 
                (tmrstop_tmrnone (|v1::nil|) ?? tmrstop_succ (|v1::nil|))
  end.

Definition tmrstopapi:=(tmrstop,(Tint32, Tint32 :: nil)).

(**************************** tmr resume****************************************)
