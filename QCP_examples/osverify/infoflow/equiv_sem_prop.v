
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import mq_apispecs. 
Require Import prt_apispecs.
Require Import osspecs.

Require Export properties.

Require Import if_succ_gen.
Require Import if_common_lemmas. 

Set Keyed Unification.

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Lemma lst2_destruct: 
  forall (A: Type) (x: list A), 
    length x = 2%nat -> 
    exists v0 v1, x = v0 :: v1 :: nil. 
Proof.
  introv Hlen.
  do 2 (destruct x; [simpl in Hlen; tryfalse | idtac]).
  destruct x. repeat eexists.
  simpl in Hlen.
  tryfalse.
Qed.
     
Ltac des_contra := 
  match goal with
    H: context [(get_all_succs_aux (match ?x with _ => _ end) ++ _)] |- _ => destruct x 
  end; 
  progress (match goal with H: context [(map _ _)] |- _ => simpl in H; inverts H end).

Ltac re_err_contra k:=
     repeat try
        (match goal with
         | H: nth_error (nil) _ = Some _ |- _ => idtac
         | H: nth_error _ _ = Some _ |- _ => destruct k; simpl in H
        end).

Ltac re_step_contra :=
     repeat try (match goal with
                  | H: spec_step _ (_ ;; _) _ _ _ _ |- _ => inverts H
                  | H: spec_step _ _ _ _ _ _ |- _ => idtac
                  end);
      (match goal with H: spec_step _ _ _ _ _ _ |- _ => inverts H end).

Ltac spec_act_solver act :=
     match goal with
     | H : ?name _ _ act _ |- _ =>
       unfolds in H; simpljoin; tryfalse
     end.

Ltac des_vl_absprog := 
  match goal with
    H: nth_error (get_all_succs (_ _))  _ = _ |- _ =>
      inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst; step_contra0
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst; step_contra0)
  end.

Set Printing Depth 1000.

Lemma hapistep_not_eni_act:
  forall ispc schspc C O C' O' cd cd' ke ks act,
    stmt_equiv cd cd' ->
    C = (curs (hapi_code cd), (ke, ks)) -> 
    hapistep (api_spec, ispc, schspc) C O C' O' act ->
    act <> EniAct.
Proof.
  introv Hse HC Hapistep Hf.
  subst C.
  inverts Hapistep.
  - tryfalse. 
  - unfold stmt_equiv in Hse.
    inverts Hse.
    + simpljoin.
      inverts H7.
    + destruct H as (Hnend & Hor).
      inverts Hor.
      * (* mqsend_equiv *) 
        unfolds in H.
        simpljoin.
        match goal with H: _ = Some cd' |- _ => clear H end.
        match goal with H: _ = Some cd |- _ => rename H into Hcd end.
        match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end. 
        do 5 try destruct x; simpl in H; tryfalse. 
        do 5 try destruct x0;  simpl in H1; tryfalse. 
        simpl in Hcd.
        do 5 des_vl_absprog.
        rename x2 into k.

        re_err_contra k;
          try inverts Hcd;
          re_step_contra;
          try rewrite nth_error_nil in *; tryfalse;
          try spec_act_solver EniAct.
        step_contra0.
        spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        step_contra0.
        spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        step_contra0.
        spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        repeat step_contra0;
          spec_act_solver EniAct.
        
      * inverts H.
        --
          (* mqrecv_equiv *)
          unfolds in H0.
          simpljoin.
          match goal with H: _ = Some cd' |- _ => clear H end.
          match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end. 
          
          do 5 try destruct x; simpl length in H; tryfalse. 
          do 5 try destruct x0; simpl length in H0; tryfalse.  
          match goal with H: _ = Some cd |- _ => rename H into Hcd end.
          simpl in Hcd.
          do 4 des_vl_absprog.
          rename x2 into k.

          re_err_contra k;
            try inverts Hcd;
            re_step_contra;
            try rewrite nth_error_nil in *; tryfalse;
            try spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.
          repeat step_contra0;
            spec_act_solver EniAct.

        -- inverts H0.
           --- (* mqtimedrecv_equiv *)
             unfolds in H.
             simpljoin.
             match goal with H: _ = Some cd' |- _ => clear H end.
             match goal with H: _ = Some cd |- _ => rename H into Hcd end.

             do 6 try destruct x; tryfalse.
             do 5 try destruct x0; tryfalse.
             do 6 des_vl_absprog.
             rename x2 into k.
             match goal with H: context[nth_error] |- _ => rename H into Hcd end.
             
             re_err_contra k;
               try inverts Hcd;
               re_step_contra;
               try rewrite nth_error_nil in *; tryfalse;
               try spec_act_solver EniAct.             
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.
             repeat step_contra0;
               spec_act_solver EniAct.             

           --- inverts H.
               ---- (* qprtpost_equiv*)
                 unfolds in H0.
                 simpljoin.
                 match goal with H: _ = Some cd' |- _ => clear H end.
                 match goal with H: _ = Some cd |- _ => rename H into Hcd end.
                 match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end.              
                 
                 do 2 try destruct x; tryfalse. 
                 do 3 try destruct x0; tryfalse. 
                 do 2 des_vl_absprog. 
                 rename x2 into k.
                 match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                 re_err_contra k;
                   try inverts Hcd;
                   re_step_contra;
                   try rewrite nth_error_nil in *; tryfalse;
                   try spec_act_solver EniAct.             
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.
                 repeat step_contra0;
                   spec_act_solver EniAct.

               ---- inverts H0.
                    ----- (* qprtpend_equiv *) 
                    unfolds in H.
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    match goal with H: _ = Some cd |- _ => rename H into Hcd end.
                    match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end.              

                    lets Hd2: lst2_destruct H.
                    lets Hd2': lst2_destruct H0.
                    simpljoin.
                    simpl in Hcd.

                    destruct x3; simpl in Hcd; 
                      try (apply abt_succs_contra in Hcd; subst cd; inverts Hstep; fail).

                    rename x2 into k.
                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.  
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.

                    -----
                    inverts H. 
                    ------
                    (* sprtpost_equiv *)
                    unfolds in H0.
                    simpljoin. 
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 3 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.             
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    ------
                    inverts H0.
                    -------
                    (* portaccept_equiv *) 
                    unfolds in H. 
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 3 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.             
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    
                    -------
                    inverts H.
                    --------
                      (* bufferpost_equiv *)
                    unfolds in H0.
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 3 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.             
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.

                    --------
                    (* bufferaccept_equiv *)
                    inverts H0.
                    ---------
                    (* bufferaccept_equiv *)
                    unfolds in H.
                    simpljoin.
                    
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.             
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.

                    ---------
                    inverts H.
                    ----------
                    (* bufferpend_equiv *) 
                    unfolds in H0.
                    simpljoin. 

                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 3 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 3 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.             
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.
                    repeat step_contra0;
                      spec_act_solver EniAct.

                    ----------
                    inverts H0. 
                    -----------
                    (*intr_equiv *)
                    inverts H.
                    destruct H0 as (Hcd & Hcd').
                    unfold intspecs.tickisr in *.
                    simpljoin.
                    simpl in H7.
                    rename x into k.
                    re_err_contra k;
                      try inverts Hcd; try inverts Hcd';
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver EniAct.

                    -----------
                    inverts H.
                    simpljoin.
                    repeat step_contra0.
  -
    tryfalse.
    
  -
    tryfalse. 
    
Qed. 


Lemma hapistep_not_sch_act:
  forall ispc schspc C O C' O' cd cd' ke ks act,
    stmt_equiv cd cd' ->
    C = (curs (hapi_code cd), (ke, ks)) -> 
    hapistep (api_spec, ispc, schspc) C O C' O' act ->
    act <> SchAct.
Proof.
  introv Hse HC Hapistep Hf.
  subst C.
  inverts Hapistep.
  - tryfalse. 
  - unfold stmt_equiv in Hse.
    inverts Hse.
    + simpljoin.
      inverts H7.
    + destruct H as (Hnend & Hor).
      inverts Hor.
      * (* mqsend_equiv *) 
        unfolds in H.
        simpljoin.
        match goal with H: _ = Some cd' |- _ => clear H end.
        match goal with H: _ = Some cd |- _ => rename H into Hcd end.
        match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end. 
        do 5 try destruct x; simpl in H; tryfalse. 
        do 5 try destruct x0;  simpl in H1; tryfalse. 
        simpl in Hcd.
        do 5 des_vl_absprog.
        rename x2 into k.

        re_err_contra k;
          try inverts Hcd;
          re_step_contra;
          try rewrite nth_error_nil in *; tryfalse;
          try spec_act_solver SchAct.
        step_contra0.
        spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        step_contra0.
        spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        step_contra0.
        spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        repeat step_contra0;
          spec_act_solver SchAct.
        
      * inverts H.
        --
          (* mqrecv_equiv *)
          unfolds in H0.
          simpljoin.
          match goal with H: _ = Some cd' |- _ => clear H end.
          match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end. 
          
          do 5 try destruct x; simpl length in H; tryfalse. 
          do 5 try destruct x0; simpl length in H0; tryfalse.  
          match goal with H: _ = Some cd |- _ => rename H into Hcd end.
          simpl in Hcd.
          do 4 des_vl_absprog.
          rename x2 into k.

          re_err_contra k;
            try inverts Hcd;
            re_step_contra;
            try rewrite nth_error_nil in *; tryfalse;
            try spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.
          repeat step_contra0;
            spec_act_solver SchAct.

        -- inverts H0.
           --- (* mqtimedrecv_equiv *)
             unfolds in H.
             simpljoin.
             match goal with H: _ = Some cd' |- _ => clear H end.
             match goal with H: _ = Some cd |- _ => rename H into Hcd end.

             do 6 try destruct x; tryfalse.
             do 5 try destruct x0; tryfalse.
             do 6 des_vl_absprog.
             rename x2 into k.
             match goal with H: context[nth_error] |- _ => rename H into Hcd end.
             
             re_err_contra k;
               try inverts Hcd;
               re_step_contra;
               try rewrite nth_error_nil in *; tryfalse;
               try spec_act_solver SchAct.             
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.
             repeat step_contra0;
               spec_act_solver SchAct.             

           --- inverts H.
               ---- (* qprtpost_equiv*)
                 unfolds in H0.
                 simpljoin.
                 match goal with H: _ = Some cd' |- _ => clear H end.
                 match goal with H: _ = Some cd |- _ => rename H into Hcd end.
                 match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end.              
                 
                 do 2 try destruct x; tryfalse. 
                 do 3 try destruct x0; tryfalse. 
                 do 2 des_vl_absprog. 
                 rename x2 into k.
                 match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                 re_err_contra k;
                   try inverts Hcd;
                   re_step_contra;
                   try rewrite nth_error_nil in *; tryfalse;
                   try spec_act_solver SchAct.             
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.
                 repeat step_contra0;
                   spec_act_solver SchAct.

               ---- inverts H0.
                    ----- (* qprtpend_equiv *) 
                    unfolds in H.
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    match goal with H: _ = Some cd |- _ => rename H into Hcd end.
                    match goal with H: spec_step _ _ _ _ _ _ |- _ => rename H into Hstep end.              

                    lets Hd2: lst2_destruct H.
                    lets Hd2': lst2_destruct H0.
                    simpljoin.
                    simpl in Hcd.

                    destruct x3; simpl in Hcd; 
                      try (apply abt_succs_contra in Hcd; subst cd; inverts Hstep; fail).

                    rename x2 into k.
                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.  
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.

                    -----
                    inverts H. 
                    ------
                    (* sprtpost_equiv *)
                    unfolds in H0.
                    simpljoin. 
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 3 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.             
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    ------
                    inverts H0.
                    -------
                    (* portaccept_equiv *) 
                    unfolds in H. 
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 3 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.             
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    
                    -------
                    inverts H.
                    --------
                      (* bufferpost_equiv *)
                    unfolds in H0.
                    simpljoin.
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 3 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.             
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.

                    --------
                    (* bufferaccept_equiv *)
                    inverts H0.
                    ---------
                    (* bufferaccept_equiv *)
                    unfolds in H.
                    simpljoin.
                    
                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 2 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 2 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.             
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.

                    ---------
                    inverts H.
                    ----------
                    (* bufferpend_equiv *) 
                    unfolds in H0.
                    simpljoin. 

                    match goal with H: _ = Some cd' |- _ => clear H end.
                    do 3 try destruct x; tryfalse.
                    do 2 try destruct x0; tryfalse.
                    do 3 des_vl_absprog.
                    rename x2 into k.
                    match goal with H: context [nth_error] |- _ => rename H into Hcd end.

                    re_err_contra k;
                      try inverts Hcd;
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.             
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.
                    repeat step_contra0;
                      spec_act_solver SchAct.

                    ----------
                    inverts H0. 
                    -----------
                    (*intr_equiv *)
                    inverts H.
                    destruct H0 as (Hcd & Hcd').
                    unfold intspecs.tickisr in *.
                    simpljoin.
                    simpl in H7.
                    rename x into k.
                    re_err_contra k;
                      try inverts Hcd; try inverts Hcd';
                      re_step_contra;
                      try rewrite nth_error_nil in *; tryfalse;
                      try spec_act_solver SchAct.

                    -----------
                    inverts H.
                    simpljoin.
                    repeat step_contra0.
  -
    tryfalse.
    
  -
    tryfalse. 
    
Qed.










