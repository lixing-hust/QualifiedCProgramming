
Require Import base_tac. 
Require Import memory. 
Require Import if_language.
Require Import if_opsem. 
Require Import seplog_lemmas.

Require Import mq_apispecs. 
Require Import prt_apispecs.
Require Import buffer_apispecs. 

Require Import intspecs.
Require Import osspecs. 

Require Export properties.

Require Import confidentiality_tactics. 

Require Import if_succ_gen.


Set Keyed Unification.

Lemma succs_tickisr_nabt:  
  forall k,
    nth_error (get_all_succs tickisr) k <> Some (ABORT).
Proof.
  introv Hf.
  do 3
    match goal with
      H: context [nth_error] |- _ => 
        destruct k; [ simpl in H; inverts H | idtac ]
    end.
  simpl in Hf.
  rewrite nth_error_nil in Hf.
  false.
Qed.  

Require Import if_common_lemmas.

Ltac des_vl_absprog := 
  match goal with
    vl: vallist, H: nth_error (get_all_succs (match ?vl with _ => _ end)) _ = _ |- _ =>
      destruct vl; inverts H; tryfalse
  | H: nth_error (get_all_succs (ABORT)) _ = Some _ |- _ => 
      apply abt_succs_contra in H; subst;
      eapply succs_tickisr_nabt; eauto
  | H: nth_error (get_all_succs (match ?v with _ => _ end)) _ = _ |- _ =>
      destruct v; simpl in H;  
      try (apply abt_succs_contra in H; subst;     
           eapply succs_tickisr_nabt; eauto)          
  end.

Ltac solve_ith i :=
  match goal with 
    H_: nth_error _  _ = _  |- _ => 
      destruct i;
      [ simpl in H_; inverts H_; 
        do 3 match goal with
            H: nth_error _ ?k = Some _ |- _ => destruct k; simpl in H; inverts H
          end;
        match goal with
          H: context [nth_error] |- _ => 
            rewrite nth_error_nil in H; tryfalse
        end
      | idtac ]
  end. 

Lemma api_succs_not_tickisr_succ: 
  forall cd, 
    (exists fid acode ft vl,
        api_spec fid = Some (acode, ft) /\  (In cd (get_all_succs (acode vl)))) ->
    ~(exists k, List.nth_error (get_all_succs tickisr) k = Some cd). 
Proof.
  introv Hex Hisucc.
  destruct Hex as (fid & ac & ft & vl & Hgac & Hasucc).
  destruct Hisucc as (k & Hi).
  unfolds in Hgac.
  simpl in Hgac.
  destruct (Zeq_bool mq_send fid) eqn: Ems.
  - (* mq_send *) 
    inverts Hgac.
    eapply In_nth_error in Hasucc; eauto.
    destruct Hasucc as (i & Hget).
    unfold mqsend in Hget.
    repeat des_vl_absprog.

    unfold tickisr in Hi.
    rename H0 into Hc.    
    do 20 solve_ith i.
    simpl in Hc.
    rewrite nth_error_nil in Hc.
    tryfalse. 
  -
    destruct (Zeq_bool mq_recv fid) eqn: Emr.
    + (* mq_recv *)
      inverts Hgac.
      eapply In_nth_error in Hasucc; eauto.
      destruct Hasucc as (i & Hget).
      unfold mqreceive in Hget.
      repeat des_vl_absprog.

      unfold tickisr in Hi.
      rename H0 into Hc.      
      do 19 solve_ith i.
      simpl in Hc.
      rewrite nth_error_nil in Hc.
      tryfalse. 
    +
      destruct (Zeq_bool mq_timedrecv fid) eqn: Eqt.
      *
        inverts Hgac.
        eapply In_nth_error in Hasucc; eauto.
        destruct Hasucc as (i & Hget).
        unfold mqtimedreceive in Hget.
        repeat des_vl_absprog.

        unfold tickisr in Hi.
        rename H0 into Hc.
        do 19 solve_ith i.
        simpl in Hc.
        rewrite nth_error_nil in Hc.
        tryfalse. 
      *  
        destruct (Zeq_bool q_port_post fid) eqn: Eqpost.
        **
          inverts Hgac.
          eapply In_nth_error in Hasucc; eauto.
          destruct Hasucc as (i & Hget).
          unfold qportpost in Hget.
          repeat des_vl_absprog.

          unfold tickisr in Hi.
          rename H0 into Hc.        
          do 11 solve_ith i.
          simpl in Hc.
          rewrite nth_error_nil in Hc.
          tryfalse. 
        **
          destruct (Zeq_bool q_port_pend fid) eqn: Eqpend.
          ***
            inverts Hgac.
            eapply In_nth_error in Hasucc; eauto.
            destruct Hasucc as (i & Hget).
            unfold qportpend in Hget.
            repeat des_vl_absprog.

            unfold tickisr in Hi.
            rename H0 into Hc.          
            do 10 solve_ith i.
            simpl in Hc.
            rewrite nth_error_nil in Hc.
            tryfalse.
          ***
            destruct (Zeq_bool sample_port_post fid) eqn: Eqspp.
            ****
            inverts Hgac.
            eapply In_nth_error in Hasucc; eauto.
            destruct Hasucc as (i & Hget).
            unfold sampleportpost in Hget.
            repeat des_vl_absprog.

            unfold tickisr in Hi.
            rename H0 into Hc.          
            do 7 solve_ith i.
            simpl in Hc.
            rewrite nth_error_nil in Hc.
            tryfalse.
            ****
            destruct (Zeq_bool port_accept fid) eqn: Eqpa.
            *****
            inverts Hgac.
            eapply In_nth_error in Hasucc; eauto.
            destruct Hasucc as (i & Hget).
            unfold portaccept in Hget.
            repeat des_vl_absprog.

            unfold tickisr in Hi.
            rename H0 into Hc.          
            do 7 solve_ith i.
            simpl in Hc.
            rewrite nth_error_nil in Hc.
            tryfalse.
            *****
            destruct (Zeq_bool buffer_post fid) eqn: Eqbp.
            ******
              inverts Hgac.
              eapply In_nth_error in Hasucc; eauto.
              destruct Hasucc as (i & Hget).
              unfold bufferpost in Hget.
              repeat des_vl_absprog.

              unfold tickisr in Hi.
              rename H0 into Hc.        
              do 7 solve_ith i.
              simpl in Hc.
              rewrite nth_error_nil in Hc.
              tryfalse. 
            ******
              destruct (Zeq_bool buffer_accept) eqn: Eba.
              *******
              inverts Hgac.
              eapply In_nth_error in Hasucc; eauto.
              destruct Hasucc as (i & Hget).
              unfold bufferaccept in Hget.
              repeat des_vl_absprog.

              unfold tickisr in Hi.
              rename H0 into Hc.        
              do 5 solve_ith i.
              simpl in Hc.
              rewrite nth_error_nil in Hc.
              tryfalse. 
              *******
              destruct (Zeq_bool buffer_pend fid).
              ******** 
              inverts Hgac.
              eapply In_nth_error in Hasucc; eauto.
              destruct Hasucc as (i & Hget).
              unfold bufferpend in Hget.
              repeat des_vl_absprog.

              unfold tickisr in Hi.
              rename H0 into Hc.        
              do 11 solve_ith i.
              simpl in Hc.
              rewrite nth_error_nil in Hc.
              tryfalse. 
              ********
            tryfalse.
Qed.

    
  
  
