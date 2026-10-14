
Require Import memory.
Require Import sem_language.
Require Import sem_opsem.

Open Scope int_scope. 

(* Set Asymmetric Patterns. *)
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)

Definition eqdomto :=
  fun (T: tasks) (O: osabst) => 
    exists tls,
      get O abstcblsid = Some (abstcblist tls)
      /\ (forall t, (exists a, get tls t = Some a ) <-> (exists C,get T t = Some C)). 

Definition init_tsk (p:progunit) (T:tasks) (cst:clientst) (O:osabst) := 
  eqdomto T O
  /\ forall t C,
      get T t = Some C ->
      exists s f d1 d2 t, C = nilcont s /\ p f = Some (t, d1, d2, s). 

Definition init_cli_st (cst: clientst) :=
  exists ges ces m,
    cst = (ges, ces, m)
    /\ (forall t E x b tp,
           get ces t = Some E ->
           get E x = Some (b, tp) ->
           get m (b, 0%Z) <> None). 

Definition distinct (ts: list tid) :=
  forall i j t1 t2,
    List.nth_error ts i = Some t1 ->
    List.nth_error ts j = Some t2 ->
    i <> j ->
    t1 <> t2. 

Definition atids_valid (tls: TcbMod.map) (ts: list tid) :=
  distinct ts /\ 
    forall t, (get tls t <> None <-> List.In t ts). 

Definition init_tsk_st (O: osabst) := 
  exists tls ts,
    get O abstcblsid = Some (abstcblist tls)
    /\ get O atidlsid = Some (atidls ts)
    /\ (forall t st p msg sus,
           get tls t = Some (p, st, msg, sus) -> st = rdy)
    /\ atids_valid tls ts.  

Definition init_sem_st (O: osabst) :=
  (exists sinfo, get O seminfoid = Some (seminfo sinfo)) 
  /\ (exists els,
         get O absecblsid = Some (absecblist els)
         /\ forall eid, get els eid = None). 
                 
Definition init_gaump (O: osabst) :=
  exists gaump, 
    get O gauxstid = Some (gauxst gaump) 
    /\ forall eid, get gaump eid = None. 
      

Definition init_laump (T: tasks) (laump: LAuxStMod.map) := 
  forall t,
    get T t <> None -> 
    get laump t = Some {| tskpt := PtNormal |}.
  
Definition init_st (T: tasks) (cst: clientst) (O: osabst) (laump: LAuxStMod.map) := 
  init_cli_st cst /\ init_tsk_st O /\ init_sem_st O /\
    init_gaump O /\ init_laump T laump.  


Definition init
  (pu: progunit)
  (T: tasks) (cst: clientst) (O: osabst) (laump: LAuxStMod.map) :=
  
  init_tsk pu T cst O /\ init_st T cst O laump. 


Definition reachable (hp: hprog) (T: tasks) (cst: clientst) (O: osabst) aust :=
  exists pu spc,
    hp = (pu, spc)
    /\ (exists T0 cst0 O0 aust0,
           init pu T0 cst0 O0 aust0
           /\ hpstepokstar hp T0 cst0 O0 aust0 T cst O aust). 

