Require Import ucos_include2.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts.
Require Import oscore_common2.
Open Scope code_scope.
Open Scope list_scope.
Open Scope Z_scope.
Ltac new_hoare_abscsq :=
match goal with
  | |- {| _, _, _, _, _, _ |} |-_ {{ ?P }} _ {{ _ }} =>
    match find_aop P with
      | none _ =>
        idtac 1 "no absop in the pre-condition"; fail 1
      | some ?a =>
        match find_absdata P absecblsid with
          | none _ =>
            idtac;
              hoare lift a pre;eapply abscsq_rule'
          | some ?b =>
            match find_absdata P abstcblsid with
              | none _ => 
                idtac 3 ; fail 3
              | some ?c =>
            (*    match find_absdata P tmsglsid with
                  | none _ => 
                    idtac 4 "no HTmsg in the pre-condition"; fail 4
                  | some ?d =>
              *)       match find_absdata P ostmid with
                      | none _ =>
                        idtac 4 "no HTime in the pre-condition"; fail 4
                      | some ?e =>
                        match find_absdata P curtid with
                          | none _ =>
                            idtac 5 "no HCurTCB in the pre-condition"; fail 5
                          | some ?f =>
                                    match find_absdata P ierid with
                                      | none _ =>
                                        idtac 6 "no Hier in the pre-condition"; fail 6
                                      | some ?g =>
                                            match find_absdata P inthandlerid with
                                              | none _ =>
                                                idtac 7 "no Hinthandler in the pre-condition"; fail 7
                                              | some ?h =>
                                                match find_absdata P inthandlerParamid with
                                                  | none _ =>
                                                    idtac 8 "no HinthandlerParam in the pre-condition"; fail 8
                                                  | some ?i =>
                                                    match find_absdata P exchandlerid with
                                                      | none _ =>
                                                        idtac 9 "no Hexchandler in the pre-condition"; fail 9
                                                      | some ?j =>
                                                        hoare lifts (a::b::c::e::f::g::h::i::j::nil) pre;
                                                        eapply abscsq_rule'
                                                      end
                                                  end
                                              end
                                      end
                            end
                        end
                    end
            end
        end
end.

Lemma isrupd_true_false:
forall ir i,
  isrupd (isrupd ir i true) i false = isrupd ir i false.
Proof.
intros.
unfold isrupd.
apply functional_extensionality_dep.
intros.
destruct (beq_nat i x);auto.
Qed.
Lemma absimp_userisr:
forall P tls qls curtid tm s sch,
can_change_aop P ->
absinfer sch
          ( <||userisr_spec (|nil|) ;; s||> ** HECBList qls **  HTCBList tls ** HTime tm **  HCurTCB curtid ** P)
          ( <||END None;;s ||> ** HECBList qls** HTCBList tls **  HTime tm ** HCurTCB curtid **P).
Proof.
intros.
apply absinfer_seq.
can_change_aop_solver.
can_change_aop_solver.
infer_solver 0%nat.
Qed.
Ltac isr_is_prop_help n si ir:= 
  match goal with 
  | H : ?s |= ?p |- _ =>
    assert(s |= Ais(n::si) ** p);
    sep auto
  | _ =>
      idtac
  end;
  match goal with 
  | H : ?s |= ?p |- _ =>
    assert(s |= Aisr(isrupd ir n true) ** p);
    sep auto
  | _ =>
      idtac
  end.
Ltac sep_cancel_unfold_solver :=
match goal with 
| H: _ |- _ 
=> try sep cancel AOSEventFreeList;
    try sep cancel AOSQFreeList;
    try sep cancel AOSQFreeBlk;
    try sep cancel AECBList;
    try sep cancel AOSTCBPrioTbl;
    try sep cancel AOSTCBList';
    try sep cancel AOSTCBFreeList';
    try sep cancel AOSRdyTblGrp;
    try sep cancel Aisr;
    try sep cancel Aie;
    try sep cancel Ais;
    try sep cancel Acs;
    try sep cancel Aop;
    
    try unfold p_local;
    try unfold LINV; 
    try unfold OSLInv  
end.
Ltac good_frm_better_sovler:=
  (*try unfold AIntNumCurrent;
  try unfold AOSRunning;
  try unfold AOSIntNesting;*)
  good_frm_sovler.
Ltac unfold_sep_cancel_helper:=
  (*try unfold AIntNumCurrent in *;
  try unfold AOSIntNesting in *;*)
  try unfold AOSExchandler in *;
  try unfold AOSInthandler in *;
  try unfold AOSExchandler in *;
  try sep normal; try sep eexists;
  try sep cancel AOSEventFreeList;
  try sep cancel AOSQFreeList;
  try sep cancel AOSQFreeBlk;
  try sep cancel AECBList;
  try sep cancel AOSTCBPrioTbl;
  try sep cancel AOSTCBList';
  try sep cancel AOSTCBFreeList';
  try sep cancel AOSRdyTblGrp;
  try sep cancel Aisr;
  try sep cancel Aier;
  try sep cancel Aie;
  try sep cancel Ais;
  try sep cancel Acs;
  try sep cancel Aop;
  try sep cancel AOSMapTbl;
  try sep cancel AOSUnMapTbl;
  (*try sep cancel AIntNumCurrent;
  try sep cancel OSIntNesting;
  try sep cancel AOSRunning;
  try sep cancel AOSLockNesting;*)
  try sep cancel AOSTime;
  try sep cancel AOSInthandlerParam.
Ltac can_change_aop_solver' :=  clear; try unfold OSInv;
try unfold AOSEventFreeList, AOSQFreeList, AOSQFreeBlk, AECBList;
try unfold AOSMapTbl, AOSUnMapTbl, AOSTCBPrioTbl, AOSIntNesting, AOSTCBList, AOSTCBFreeList;
try unfold AOSRdyTblGrp, AOSRdyTbl, AOSRdyGrp, AOSTime, AGVars;
try unfold AOSEvent, AOSEventTbl, AMsgData, AOSQCtr, AOSQBlk, node, AOSInthandlerParam;
try unfold (*AOSRunning,*) AOSInthandler, AOSInthandlerParam, AOSExchandler;
can_change_aop_solver.
Ltac good_frm_sovler':=
  unfold (*AOSRunning, AIntNumCurrent, AOSRunning,*) AOSInthandler, AOSInthandlerParam,
  AOSExchandler, p_local, LINV, CurTid, OSLInv; good_frm_sovler.
Lemma val_inj_help1:
    forall i v'53, Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
    val_inj
  (val_eq
     (nth_val'
        (Z.to_nat
           (Int.unsigned (Int.sub (Int.repr (Z.of_nat i)) (Int.repr 5))))
        (HinthandlerToListval v'53)) (Vint32 (Int.repr 0))) <> Vundef.
Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 5)) (Int.repr 5) = Int.repr 0) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 5)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 6)) (Int.repr 5) = Int.repr 1) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 6)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 7)) (Int.repr 5) = Int.repr 2) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 7)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 8)) (Int.repr 5) = Int.repr 3) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 8)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 9)) (Int.repr 5) = Int.repr 4) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 9)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 10)) (Int.repr 5) = Int.repr 5) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 10)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 11)) (Int.repr 5) = Int.repr 6) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 11)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 12)) (Int.repr 5) = Int.repr 7) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 12)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 13)) (Int.repr 5) = Int.repr 8) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 13)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 14)) (Int.repr 5) = Int.repr 9) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 14)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 15)) (Int.repr 5) = Int.repr 10) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 15)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
Qed.
Lemma val_inj_help2:
    forall i v'53, Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
    val_inj
  (notint
     (val_inj
        (val_eq
           (nth_val'
              (Z.to_nat
                 (Int.unsigned
                    (Int.sub (Int.repr (Z.of_nat i)) (Int.repr 5))))
              (HinthandlerToListval v'53)) (Vint32 (Int.repr 0))))) <> Vundef.
Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 5)) (Int.repr 5) = Int.repr 0) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 5)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 6)) (Int.repr 5) = Int.repr 1) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 6)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 7)) (Int.repr 5) = Int.repr 2) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 7)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 8)) (Int.repr 5) = Int.repr 3) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 8)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 9)) (Int.repr 5) = Int.repr 4) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 9)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 10)) (Int.repr 5) = Int.repr 5) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 10)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 11)) (Int.repr 5) = Int.repr 6) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 11)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 12)) (Int.repr 5) = Int.repr 7) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 12)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 13)) (Int.repr 5) = Int.repr 8) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 13)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 14)) (Int.repr 5) = Int.repr 9) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 14)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 15)) (Int.repr 5) = Int.repr 10) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 15)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
Qed.
  
Lemma val_inj_help3:
forall i v'53, Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
    val_inj
  (bool_and
     (val_inj
        (bool_and
           (val_inj
              (bool_or
                 (val_inj
                    (if Int.ltu (Int.repr 5) (Int.repr (Z.of_nat i))
                     then Some (Vint32 Int.one)
                     else Some (Vint32 Int.zero)))
                 (val_inj
                    (if Int.eq (Int.repr (Z.of_nat i)) (Int.repr 5)
                     then Some (Vint32 Int.one)
                     else Some (Vint32 Int.zero)))))
           (val_inj
              (if Int.ltu (Int.repr (Z.of_nat i)) (Int.repr 15)
               then Some (Vint32 Int.one)
               else Some (Vint32 Int.zero)))))
     (val_inj
        (notint
           (val_inj
              (val_eq
                 (nth_val'
                    (Z.to_nat
                       (Int.unsigned
                          (Int.sub (Int.repr (Z.of_nat i)) (Int.repr 5))))
                    (HinthandlerToListval v'53)) 
                 (Vint32 (Int.repr 0))))))) <> Vundef.
    Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 5)) (Int.repr 5) = Int.repr 0) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 5)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 6)) (Int.repr 5) = Int.repr 1) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 6)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 7)) (Int.repr 5) = Int.repr 2) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 7)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 8)) (Int.repr 5) = Int.repr 3) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 8)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 9)) (Int.repr 5) = Int.repr 4) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 9)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 10)) (Int.repr 5) = Int.repr 5) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 10)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 11)) (Int.repr 5) = Int.repr 6) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 11)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 12)) (Int.repr 5) = Int.repr 7) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 12)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 13)) (Int.repr 5) = Int.repr 8) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 13)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 14)) (Int.repr 5) = Int.repr 9) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 14)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
    rewrite H1.
    assert(Int.sub (Int.repr (Z.of_nat 15)) (Int.repr 5) = Int.repr 10) by auto.
    rewrite H2.
    rewrite Int.unsigned_repr. 
    unfold HinthandlerToListval. unfold nth_val'. simpl.
    destruct (Int.eq (Int.repr (IntToZ (v'53 (ZToInt 15)))) (Int.repr 0)); auto.
    rewrite max_unsigned_val. omega.
Qed.

Lemma v_leq_15_sub_5_le_11:
    forall i, Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
    Int.unsigned
  (Int.sub (Int.repr (Z.of_nat i))
     (Int.repr 5)) < 11.
Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 5) (Int.repr 5) = Int.repr 0) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 6) (Int.repr 5) = Int.repr 1) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 7) (Int.repr 5) = Int.repr 2) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 8) (Int.repr 5) = Int.repr 3) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 9) (Int.repr 5) = Int.repr 4) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 10) (Int.repr 5) = Int.repr 5) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 11) (Int.repr 5) = Int.repr 6) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 12) (Int.repr 5) = Int.repr 7) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 13) (Int.repr 5) = Int.repr 8) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    destruct H1. rewrite H1. simpl. 
    assert(Int.sub (Int.repr 14) (Int.repr 5) = Int.repr 9) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
    rewrite H1. simpl. 
    assert(Int.sub (Int.repr 15) (Int.repr 5) = Int.repr 10) by auto.
    rewrite H2. rewrite Int.unsigned_repr. omega. rewrite max_unsigned_val. omega.
Qed.
Lemma rule_type_val_match_help: 
forall i v'53, Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
    rule_type_val_match Int32u
    (nth_val'
    (Z.to_nat
        (Int.unsigned
            (Int.sub (Int.repr (Z.of_nat i)) (Int.repr 5))))
    (HinthandlerToListval v'53)) = true.
Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    destruct H1. rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
    rewrite H1.
    unfold HinthandlerToListval; unfold nth_val'; simpl; auto.
Qed.
Lemma Z_to_nat_help: 
  forall i,
    Z.of_nat i >= 5 ->
    Z.of_nat i <= 15 ->
  Z.to_nat (Int.intval (Int.repr (Z.of_nat i))) = i.
Proof.
    intros.
    assert(i = 5%nat \/ i = 6%nat 
    \/ i = 7%nat \/ i = 8%nat
    \/ i = 9%nat \/ i = 10%nat
    \/ i = 11%nat \/ i = 12%nat
    \/ i = 13%nat \/ i = 14%nat
    \/ i = 15%nat ).
    omega.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    destruct H1. rewrite H1. auto.
    rewrite H1. auto.
Qed.

Lemma MatchHandler0:
  forall i v'20, 
  5 <= Int.unsigned i <= 15 ->
  match Z.to_nat (Int.unsigned (i -ᵢ $ 5)) with
  | 0%nat =>
      V$ 0
      :: V$ IntToZ (v'20 ($ 6))
         :: V$ IntToZ (v'20 ($ 7))
            :: V$ IntToZ (v'20 ($ 8))
               :: V$ IntToZ (v'20 ($ 9))
                  :: V$ IntToZ (v'20 ($ 10))
                     :: V$ IntToZ (v'20 ($ 11))
                        :: V$ IntToZ (v'20 ($ 12)) :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
  | S n' =>
      V$ IntToZ (v'20 ($ 5))
      :: match n' with
         | 0%nat =>
             V$ 0
             :: V$ IntToZ (v'20 ($ 7))
                :: V$ IntToZ (v'20 ($ 8))
                   :: V$ IntToZ (v'20 ($ 9))
                      :: V$ IntToZ (v'20 ($ 10))
                         :: V$ IntToZ (v'20 ($ 11))
                            :: V$ IntToZ (v'20 ($ 12)) :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
         | S n'0 =>
             V$ IntToZ (v'20 ($ 6))
             :: match n'0 with
                | 0%nat =>
                    V$ 0
                    :: V$ IntToZ (v'20 ($ 8))
                       :: V$ IntToZ (v'20 ($ 9))
                          :: V$ IntToZ (v'20 ($ 10))
                             :: V$ IntToZ (v'20 ($ 11))
                                :: V$ IntToZ (v'20 ($ 12))
                                   :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                | S n'1 =>
                    V$ IntToZ (v'20 ($ 7))
                    :: match n'1 with
                       | 0%nat =>
                           V$ 0
                           :: V$ IntToZ (v'20 ($ 9))
                              :: V$ IntToZ (v'20 ($ 10))
                                 :: V$ IntToZ (v'20 ($ 11))
                                    :: V$ IntToZ (v'20 ($ 12))
                                       :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                       | S n'2 =>
                           V$ IntToZ (v'20 ($ 8))
                           :: match n'2 with
                              | 0%nat =>
                                  V$ 0
                                  :: V$ IntToZ (v'20 ($ 10))
                                     :: V$ IntToZ (v'20 ($ 11))
                                        :: V$ IntToZ (v'20 ($ 12))
                                           :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                              | S n'3 =>
                                  V$ IntToZ (v'20 ($ 9))
                                  :: match n'3 with
                                     | 0%nat =>
                                         V$ 0
                                         :: V$ IntToZ (v'20 ($ 11))
                                            :: V$ IntToZ (v'20 ($ 12))
                                               :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                                     | S n'4 =>
                                         V$ IntToZ (v'20 ($ 10))
                                         :: match n'4 with
                                            | 0%nat =>
                                                V$ 0
                                                :: V$ IntToZ (v'20 ($ 12))
                                                   :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                                            | S n'5 =>
                                                V$ IntToZ (v'20 ($ 11))
                                                :: match n'5 with
                                                   | 0%nat =>
                                                       V$ 0
                                                       :: V$ IntToZ (v'20 ($ 13)) :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                                                   | S n'6 =>
                                                       V$ IntToZ (v'20 ($ 12))
                                                       :: match n'6 with
                                                          | 0%nat => V$ 0 :: V$ IntToZ (v'20 ($ 14)) :: V$ IntToZ (v'20 ($ 15)) :: nil
                                                          | S n'7 =>
                                                              V$ IntToZ (v'20 ($ 13))
                                                              :: match n'7 with
                                                                 | 0%nat => V$ 0 :: V$ IntToZ (v'20 ($ 15)) :: nil
                                                                 | S n'8 =>
                                                                     V$ IntToZ (v'20 ($ 14))
                                                                     :: match n'8 with
                                                                        | 0%nat => V$ 0 :: nil
                                                                        | S _ => V$ IntToZ (v'20 ($ 15)) :: nil
                                                                        end
                                                                 end
                                                          end
                                                   end
                                            end
                                     end
                              end
                       end
                end
         end
  end =
  V$ IntToZ (if Int.eq ($ 5) i then Int.zero else v'20 ($ 5))
  :: V$ IntToZ (if Int.eq ($ 6) i then Int.zero else v'20 ($ 6))
     :: V$ IntToZ (if Int.eq ($ 7) i then Int.zero else v'20 ($ 7))
        :: V$ IntToZ (if Int.eq ($ 8) i then Int.zero else v'20 ($ 8))
           :: V$ IntToZ (if Int.eq ($ 9) i then Int.zero else v'20 ($ 9))
              :: V$ IntToZ (if Int.eq ($ 10) i then Int.zero else v'20 ($ 10))
                 :: V$ IntToZ (if Int.eq ($ 11) i then Int.zero else v'20 ($ 11))
                    :: V$ IntToZ (if Int.eq ($ 12) i then Int.zero else v'20 ($ 12))
                       :: V$ IntToZ (if Int.eq ($ 13) i then Int.zero else v'20 ($ 13))
                          :: V$ IntToZ (if Int.eq ($ 14) i then Int.zero else v'20 ($ 14))
                             :: V$ IntToZ (if Int.eq ($ 15) i then Int.zero else v'20 ($ 15)) :: nil.
Proof.
  intros.
  assert (Int.unsigned i = 5 \/
          Int.unsigned i = 6 \/
          Int.unsigned i = 7 \/
          Int.unsigned i = 8 \/
          Int.unsigned i = 9 \/
          Int.unsigned i = 10 \/
          Int.unsigned i = 11 \/
          Int.unsigned i = 12 \/
          Int.unsigned i = 13 \/
          Int.unsigned i = 14 \/
          Int.unsigned i = 15
          ). omega.

  assert (0 <= Int.unsigned i - Int.unsigned ($ 5) <= 4294967295). int auto.

  (*i = 5*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 0). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = true) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 6*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 1). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = true) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 7*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 2). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = true) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 8*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 3). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = true) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 9*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 4). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = true) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 10*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 5). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = true) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 11*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 6). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = true) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.
  
  (*i = 12*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 7). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = true) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 13*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 8). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = true) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 14*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 9). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = true) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.

  (*i = 15*)
  assert ((Int.unsigned (i -ᵢ $ 5)) = 10). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = true)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.zero = 0). auto. rewrite H14. auto.
Qed.

Lemma MatchHandler1:
  forall i v'21, 
  5 <= Int.unsigned i <= 15 ->
  match Z.to_nat (Int.unsigned (i -ᵢ $ 5)) with
  | 0%nat =>
      V$ 1
      :: V$ IntToZ (v'21 ($ 6))
         :: V$ IntToZ (v'21 ($ 7))
            :: V$ IntToZ (v'21 ($ 8))
               :: V$ IntToZ (v'21 ($ 9))
                  :: V$ IntToZ (v'21 ($ 10))
                     :: V$ IntToZ (v'21 ($ 11))
                        :: V$ IntToZ (v'21 ($ 12)) :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
  | S n' =>
      V$ IntToZ (v'21 ($ 5))
      :: match n' with
         | 0%nat =>
             V$ 1
             :: V$ IntToZ (v'21 ($ 7))
                :: V$ IntToZ (v'21 ($ 8))
                   :: V$ IntToZ (v'21 ($ 9))
                      :: V$ IntToZ (v'21 ($ 10))
                         :: V$ IntToZ (v'21 ($ 11))
                            :: V$ IntToZ (v'21 ($ 12)) :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
         | S n'0 =>
             V$ IntToZ (v'21 ($ 6))
             :: match n'0 with
                | 0%nat =>
                    V$ 1
                    :: V$ IntToZ (v'21 ($ 8))
                       :: V$ IntToZ (v'21 ($ 9))
                          :: V$ IntToZ (v'21 ($ 10))
                             :: V$ IntToZ (v'21 ($ 11))
                                :: V$ IntToZ (v'21 ($ 12))
                                   :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                | S n'1 =>
                    V$ IntToZ (v'21 ($ 7))
                    :: match n'1 with
                       | 0%nat =>
                           V$ 1
                           :: V$ IntToZ (v'21 ($ 9))
                              :: V$ IntToZ (v'21 ($ 10))
                                 :: V$ IntToZ (v'21 ($ 11))
                                    :: V$ IntToZ (v'21 ($ 12))
                                       :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                       | S n'2 =>
                           V$ IntToZ (v'21 ($ 8))
                           :: match n'2 with
                              | 0%nat =>
                                  V$ 1
                                  :: V$ IntToZ (v'21 ($ 10))
                                     :: V$ IntToZ (v'21 ($ 11))
                                        :: V$ IntToZ (v'21 ($ 12))
                                           :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                              | S n'3 =>
                                  V$ IntToZ (v'21 ($ 9))
                                  :: match n'3 with
                                     | 0%nat =>
                                         V$ 1
                                         :: V$ IntToZ (v'21 ($ 11))
                                            :: V$ IntToZ (v'21 ($ 12))
                                               :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                                     | S n'4 =>
                                         V$ IntToZ (v'21 ($ 10))
                                         :: match n'4 with
                                            | 0%nat =>
                                                V$ 1
                                                :: V$ IntToZ (v'21 ($ 12))
                                                   :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                                            | S n'5 =>
                                                V$ IntToZ (v'21 ($ 11))
                                                :: match n'5 with
                                                   | 0%nat =>
                                                       V$ 1
                                                       :: V$ IntToZ (v'21 ($ 13)) :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                                                   | S n'6 =>
                                                       V$ IntToZ (v'21 ($ 12))
                                                       :: match n'6 with
                                                          | 0%nat => V$ 1 :: V$ IntToZ (v'21 ($ 14)) :: V$ IntToZ (v'21 ($ 15)) :: nil
                                                          | S n'7 =>
                                                              V$ IntToZ (v'21 ($ 13))
                                                              :: match n'7 with
                                                                 | 0%nat => V$ 1 :: V$ IntToZ (v'21 ($ 15)) :: nil
                                                                 | S n'8 =>
                                                                     V$ IntToZ (v'21 ($ 14))
                                                                     :: match n'8 with
                                                                        | 0%nat => V$ 1 :: nil
                                                                        | S _ => V$ IntToZ (v'21 ($ 15)) :: nil
                                                                        end
                                                                 end
                                                          end
                                                   end
                                            end
                                     end
                              end
                       end
                end
         end
  end =
  V$ IntToZ (if Int.eq ($ 5) i then Int.one else v'21 ($ 5))
  :: V$ IntToZ (if Int.eq ($ 6) i then Int.one else v'21 ($ 6))
     :: V$ IntToZ (if Int.eq ($ 7) i then Int.one else v'21 ($ 7))
        :: V$ IntToZ (if Int.eq ($ 8) i then Int.one else v'21 ($ 8))
           :: V$ IntToZ (if Int.eq ($ 9) i then Int.one else v'21 ($ 9))
              :: V$ IntToZ (if Int.eq ($ 10) i then Int.one else v'21 ($ 10))
                 :: V$ IntToZ (if Int.eq ($ 11) i then Int.one else v'21 ($ 11))
                    :: V$ IntToZ (if Int.eq ($ 12) i then Int.one else v'21 ($ 12))
                       :: V$ IntToZ (if Int.eq ($ 13) i then Int.one else v'21 ($ 13))
                          :: V$ IntToZ (if Int.eq ($ 14) i then Int.one else v'21 ($ 14))
                             :: V$ IntToZ (if Int.eq ($ 15) i then Int.one else v'21 ($ 15)) :: nil.
Proof.
  intros.
  assert (Int.unsigned i = 5 \/
          Int.unsigned i = 6 \/
          Int.unsigned i = 7 \/
          Int.unsigned i = 8 \/
          Int.unsigned i = 9 \/
          Int.unsigned i = 10 \/
          Int.unsigned i = 11 \/
          Int.unsigned i = 12 \/
          Int.unsigned i = 13 \/
          Int.unsigned i = 14 \/
          Int.unsigned i = 15
          ). omega.

  assert (0 <= Int.unsigned i - Int.unsigned ($ 5) <= 4294967295). int auto.

  (*i = 5*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 0). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = true) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.
  
  (*i = 6*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 1). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = true) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 7*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 2). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = true) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 8*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 3). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = true) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 9*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 4). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = true) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 10*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 5). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = true) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 11*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 6). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = true) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 12*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 7). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = true) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 13*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 8). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = true) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 14*)
  destruct H0.
  assert ((Int.unsigned (i -ᵢ $ 5)) = 9). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = true) /\ (Int.eq ($ 15) i = false)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.

  (*i = 15*)
  assert ((Int.unsigned (i -ᵢ $ 5)) = 10). int auto. auto. 
  rewrite H2. simpl.
  assert ((Int.eq ($ 5) i = false) /\ (Int.eq ($ 6) i = false) /\ (Int.eq ($ 7) i = false) /\
  (Int.eq ($ 8) i = false) /\ (Int.eq ($ 9) i = false) /\ (Int.eq ($ 10) i = false) /\
  (Int.eq ($ 11) i = false) /\ (Int.eq ($ 12) i = false) /\ (Int.eq ($ 13) i = false) /\
  (Int.eq ($ 14) i = false) /\ (Int.eq ($ 15) i = true)).
  int auto. auto. 
  destruct H3; rewrite H3.
  destruct H4; rewrite H4.
  destruct H5; rewrite H5.
  destruct H6; rewrite H6.
  destruct H7; rewrite H7.
  destruct H8; rewrite H8.
  destruct H9; rewrite H9.
  destruct H10; rewrite H10.
  destruct H11; rewrite H11.
  destruct H12; rewrite H12.
  rewrite H13.
  assert (IntToZ Int.one = 1). auto. rewrite H14. auto.
Qed.
