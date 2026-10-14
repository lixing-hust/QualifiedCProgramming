Require Export log_language.
Require Export log_opsem.
Require Export log_code_notations.
Require Export log_code_defs.
Require Export log_assertion.
Require Export memory.

Require Import Arith.
Require Import LibTactics. 

Open Scope type_scope.
Open Scope list_scope.


Definition FIFO (log: list act) eid :=
  forall  i1 i2 m1 m2 cnt1 cnt2,
    nth_error log i1 = Some (deque eid m1 cnt1 ) ->
    nth_error log i2 = Some (deque eid m2 cnt2 ) ->
    i1 <  i2 -> 
    cnt1 < cnt2
.
Definition lt_cnt_log_que eid (log: list act) (msgl: list ms) :=
  forall i j m m' cnt cnt', 
    nth_error log i = Some (deque eid m cnt ) ->
    nth_error msgl j = Some ( m' , cnt' ) ->
    cnt < cnt'
.
Definition lt_cnt_que_cmp  (cmp:MqcntMod.map) eid (msgl: list ms) :=
  forall i m cnt cnt', 
    nth_error msgl i = Some ( m, cnt)->
    get cmp eid =Some cnt' ->
    cnt < cnt'
.
Definition is_inc  (msgl: list ms) :=
  forall i1 i2 m1 m2 cnt cnt', 
    nth_error msgl i1 = Some ( m1, cnt ) ->
    nth_error msgl i2 = Some ( m2, cnt') ->
    i1 <  i2 -> 
    cnt < cnt'
. 
Definition lt_cnt_log_cmp (log: list act) eid (cmp:MqcntMod.map)  :=
  forall i m cnt cnt', 
    nth_error log i = Some (deque eid m cnt ) ->
    get cmp eid =Some cnt' ->
    cnt < cnt'
.
Definition cre_log_cmp (log: list act) eid (cmp:MqcntMod.map) (msgl: list ms) :=
  ( (forall j, nth_error log j <> Some (delque eid)) /\
    (forall j m cnt, nth_error log j <> Some (enque eid m cnt )) /\
    (forall j m cnt, nth_error log j <> Some (deque eid m cnt)) )
    <-> (get cmp eid =Some 0%nat  /\ msgl = nil)
.

Definition FIFO_ext (O: osabst)  :=
   forall log l1 l2 eid ecbls cmp ms sz pwl wl,
      get O loglsid = Some (oslog log)  ->
      log = l1 ++ (creque eid) :: l2 ->
      (forall j , nth_error l2 j <> Some (creque eid)) -> 
      (forall j , nth_error l2 j <> Some (delque eid)) ->
      get O absecblsid = Some (absecblist ecbls) ->
      EcbMod.get ecbls eid =Some ( absmsgq ms sz pwl,wl) ->
      get O mqcntid = Some (mqcnt cmp) ->
      (is_inc ms /\
      lt_cnt_log_que eid l2 ms /\
      lt_cnt_que_cmp cmp eid ms /\
      lt_cnt_log_cmp l2 eid cmp /\
      cre_log_cmp l2 eid cmp ms /\
      FIFO l2 eid
      )
.

Definition First_In_First_Out (O: osabst)  :=
   forall log l1 l2 eid ecbls ms sz pwl wl,
      get O loglsid = Some (oslog log)  ->
      log = l1 ++ (creque eid) :: l2 ->
      (forall j , nth_error l2 j <> Some (creque eid)) -> 
      (forall j , nth_error l2 j <> Some (delque eid)) ->
      get O absecblsid = Some (absecblist ecbls) ->
      EcbMod.get ecbls eid =Some ( absmsgq ms sz pwl,wl) ->
      (exists cmp, get O mqcntid = Some (mqcnt cmp) )->
      FIFO l2 eid
.

(*不能是特定操作语句比如分配内存，不能是抽象语句比如api，反应代码是源代码*)
Fixpoint GoodStmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sifthen _ _ => False
    | swhile _ s' => GoodStmt_h s'
    | sret => True
    | srete  _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => GoodStmt_h s1 /\ GoodStmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => False
    | sfree _ _ => False
    | salloc _ _ => False
    | sprim _ => False
    | hapi_code _ => False
  end.

Definition good_client_code client_code :=
      (forall (f : fid) (a : type) (b c : decllist) (s : stmts),
       client_code f = Some (a, b, c, s) -> GoodStmt_h s).

Definition INV_PROP (client_code:progunit) O  :=
  good_client_code client_code  /\ FIFO_ext O.


Definition eqdomto:= fun (T:tasks) (O:osabst) =>
                       exists tls,
                         get O abstcblsid = Some (abstcblist tls) /\(
                           forall t, (exists a, get tls t = Some a ) <->  (exists C,get T t = Some C)  ).

(*初始格局的任务定义域相同*)
Definition InitTasks (T:tasks) (p:progunit) (cst:clientst) (O:osabst) :=
  eqdomto T O /\ 
  forall t C,TasksMod.get T t = Some C -> 
  exists s f d1 d2 t, C = nilcont s /\ 
                      p f = Some (t, d1, d2, s).
(*初始格局中内核状态*)
Definition init_st O:=
  exists tls,
    get O absecblsid = Some (absecblist EcbMod.emp) /\
    get O abstcblsid = Some (abstcblist tls) /\
    get O loglsid = Some (oslog nil) /\
    forall t, exists p msg sus, get tls t = Some (p,rdy,msg,sus).

Require Import FIFO_spec.
Require Import mq_succ_gen. 

Definition good_api_stmt s:=
  (exists vl, has_succ (mqcreate vl) s) \/
    (exists vl, has_succ (mqdelete vl) s) \/
    (exists vl, has_succ (mqsend vl) s) \/ 
    (exists vl, has_succ (mqreceive vl) s) \/
    (exists vl, has_succ (mqtimedreceive vl) s) \/
    (exists vl, has_succ (mqgetinfo vl) s) \/ 
    (s = ABORT) \/         
    (exists vo, s = END vo).

Fixpoint goodstmt_h (s : stmts) {struct s} : Prop :=
  match s with
    | sskip _ => True
    | sassign _ _ => True
    | sif _ s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sifthen _ s => goodstmt_h s
    | swhile _ s' => goodstmt_h s'
    | sret => True
    | srete _ => True
    | scall f _ => True
    | scalle _ f _ => True
    | sseq s1 s2 => goodstmt_h s1 /\ goodstmt_h s2
    | sprint _ => True
    | sfexec _ _ _ => True
    | sfree _ _ => True
    | salloc _ _ => True
    | sprim _ => False
    | hapi_code s => good_api_stmt s
  end.

Definition goodeval_h (c:cureval):=
  match c with
    | cure _ => True
    | curs s => goodstmt_h s
  end.

Fixpoint goodks_h ks:=
  match ks with
    | kint _ _ _ _ => False
    | kevent c ke ks' => goodeval_h c /\ goodks_h ks'
    | kstop => True
    | kcall _ s _ ks' => goodks_h ks' /\ goodstmt_h s
    | kseq s ks' => goodks_h ks' /\ goodstmt_h s
    | kassignr _ _ ks' => goodks_h ks'
    | kassignl _ _ ks' => goodks_h ks'
    | kfuneval _ _ _ _ ks' => goodks_h ks'
    | kif s1 s2 ks' => goodks_h ks' /\ goodstmt_h s1 /\ goodstmt_h s2
    | kwhile _ s ks' => goodks_h ks' /\ goodstmt_h s
    | kret ks' => goodks_h ks'
  end.

Definition goodcode_h (c:code):=
  match c with
    | (c,(ke,ks)) => goodeval_h c /\ goodks_h ks
  end.

Definition goodtasks_h T:=
  forall t c, TasksMod.get T t = Some c -> goodcode_h c.
