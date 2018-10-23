Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)

Open Scope list_scope.
Import ListNotations.

Module LISTTHEOREMS.
  Open Scope nat_scope.

  Lemma seq_peel_begin: forall (n l: nat) (LPOS: l > 0),
      n :: seq (S n) (l - 1) = seq n l.
  Proof.
    intros.
    induction l.
    - inversion LPOS.
    - simpl.
      replace (l - 0) with l.
      reflexivity.
      omega.
  Qed.

  Lemma cons_append: forall {A: Type} (a: A) (l l': list A),
      (cons a l) ++ l' = cons a (l ++ l').
  Proof.
    intros.
    generalize dependent a.
    generalize dependent l.
    induction l'.
    - auto.
    - intros.
      replace ((a0 :: a :: l) ++ l') with (a0 :: ((a:: l) ++ l')).
      reflexivity.
      apply IHl' with (a := a0) (l := (a::l)).
  Qed.
  
  Lemma seq_peel_end: forall (n l: nat) (L_GT_0: l > 0),
      seq n l = (seq n (l - 1)) ++ [ n + l - 1].
  Proof.
    intros until l.
    generalize dependent n.
    induction l.
    - intros. omega.
    - intros.
      assert (LCASES: l = 0 \/ l > 0).
      omega.

      destruct LCASES as [LEQ0 | LGT0].
      + subst.
        simpl.
        replace (n + 1 - 1) with n; auto; omega.

      +  simpl.
         replace (l - 0) with l.
         assert (SEQ_S_N: seq (S n) l = seq (S n) (l - 1) ++ [S n + l - 1]).
         apply IHl; auto.

         rewrite SEQ_S_N.

         assert (n :: seq (S n) (l - 1) = seq n l).
         apply seq_peel_begin; auto.

         replace ( n :: seq (S n) (l - 1) ++ [S n + l - 1]) with
             ((n :: seq (S n) (l - 1)) ++ [S n + l - 1]).
         rewrite H.
         replace (S n + l) with (n + S l).
         reflexivity.
         omega.
         apply cons_append.
         omega.
  Qed.
  Close Scope nat_scope.
End LISTTHEOREMS.

(** HintDB of hints for SCEV **)
Global Create HintDb Recurrence.

(** You can build the theory of SCEV over any ring, actually *)
Module Type RECURRENCE.

  Import LISTTHEOREMS.
  Parameter R: Type.
  Parameter (zero one : R).
  Parameter (plus mult minus : R -> R-> R).
  Parameter (sym : R -> R).

  Parameter rt : ring_theory zero one plus mult minus sym (@eq R).
  Add Ring Rring : rt.

  Notation "0" := zero.  Notation "1" := one.
  Notation "x + y" := (plus x y).
  Notation "x * y " := (mult x y).

  (** A class for objects that vary over loop iterations *)
  Class LoopVariant (A R : Type) :=
    {
      evalAtIx: A -> nat -> R
    }.
  Infix "#" := evalAtIx (at level 10).

  Global Instance loopVariantFn (R: Type): LoopVariant (nat -> R) (R : Type) :=
    {
      evalAtIx (f: nat -> R) (n: nat) := f n
    }.

  Definition scaleLoopVariantFn  (r: R) (f: nat -> R): nat -> R :=
    fun n => r * (f n).


  

  (* Const function *)
  Definition const {A B: Type} (x: A) (y: B) := x.
  
  Definition RBinop := R -> R -> R.
  
  Section BR.

    Inductive BR :=
    | mkBR : R -> (R -> R -> R) -> (nat -> R) -> BR.

    Notation "'{{' const ',' bop ',' fn  '}}'" :=
      (mkBR const bop fn) (at level 30).


    (** semantics of evaluating a BR *)
    Definition evalBR (br: BR) (n: nat): R :=
      match br with
      | mkBR r0 binop f =>
        let
          vals : list R := map f (seq 1 n)
        in
        fold_left binop vals r0
      end.


    Global Instance loopVariantBR : LoopVariant BR R :=
      {
        evalAtIx (br: BR) (n: nat) := evalBR br n
      }.

    Class LiftToBR A : Type  :=
      {
        liftToBR : A -> BR
      }.

    Global Instance liftConstantToBR : LiftToBR R :=
      {
        liftToBR (c: R) := mkBR c plus (const zero)
      }.

    Global Instance liftBRToBR: LiftToBR BR :=
      {
        liftToBR br := br
      }.


    Lemma liftConstant_eval: forall (n: nat) (r: R),
        evalAtIx (liftToBR r)  n = r.
    Proof.
      intros.
      simpl.

      induction n.
      - auto.
      - rewrite seq_peel_end.
        rewrite map_app.
        rewrite fold_left_app.
        replace (S n - 1)%nat with n; try omega.
        rewrite IHn.
        simpl.
        unfold const; auto; ring.
        omega.
    Qed.

    Hint Resolve liftConstant_eval : Recurrence.
    Hint Rewrite liftConstant_eval : Recurrence.

    (** Most basic theorem, show how to unfold BR execution *)
    Lemma evalBR_step: forall `{Ring R} (r0: R) (bop: R -> R -> R) (f: nat -> R) (n : nat),
        ({{r0, bop, f}}) # (S n) = bop ((mkBR r0 bop f) # n)  (f # (S n)).
    Proof.
      Open Scope nat_scope.
      intros until n.
      generalize dependent r0.
      generalize dependent bop.
      generalize dependent f.
      simpl.
      induction n.
      - auto.
      - intros.

        assert (STRIP_LAST: seq 2 (S n) = seq 2 (S n - 1) ++ [2 + (S n) - 1]).
        apply seq_peel_end; omega.

        rewrite STRIP_LAST.
        simpl.

        rewrite map_app.
        rewrite fold_left_app.
        simpl.
        replace (n - 0) with n.
        reflexivity.
        omega.
        Close Scope nat_scope.
    Qed.

    
    Hint Resolve evalBR_step : Recurrence.
    Hint Rewrite @evalBR_step : Recurrence.



    Section BR_CONSTANTS.
      Variable f : nat -> R.
      Variable r0 c: R.

      Definition br := {{ r0, plus, f}}.

      (* Lemma 6 from paper *)
      Lemma add_constant_add_br: forall `{Ring R}  (n: nat),
          ((liftToBR c) # n) +
          {{r0, plus, f}} # n = 
          {{(r0 + c), plus, f}} # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.
          ring_simplify in IHn.
          ring_simplify.

          replace (liftToBR c # (S n)) with
              (liftToBR c # n).
          rewrite IHn.
          rewrite <- evalBR_step.
          reflexivity.

          repeat (rewrite liftConstant_eval).
          auto.
      Qed.

      Hint Resolve add_constant_add_br : Recurrence.
      Hint Rewrite @add_constant_add_br : Recurrence.

      (* Lemma 7 *)
      (* Here is where I need a module :( nat -> R forms a module over R *)
      Lemma mul_constant_add_br: forall `{Ring R} (n: nat),
          ((liftToBR c) # n) * ((mkBR r0 plus f) # n) =
          (mkBR (c * r0) plus (scaleLoopVariantFn c f)) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.

          replace (liftToBR c # (S n)) with
              (liftToBR c # n).
          ring_simplify.
          rewrite IHn.
          rewrite evalBR_step.
          
          replace ((liftToBR c # n) * (f # (S n))) with
              ((scaleLoopVariantFn c f) # (S n)).
          reflexivity.

          rewrite liftConstant_eval.
          auto.

          repeat (rewrite liftConstant_eval).
          reflexivity.
      Qed.

      
      Hint Resolve mul_constant_add_br : Recurrence.
      Hint Rewrite @mul_constant_add_br : Recurrence.
      (*
    (* Lemma 8 *)
    Lemma pow_constant_add_br: forall `{Ring R} (n: nat),
        pow_N c ((mkBR r0 plus f) # n) =
        (mkBR (pow_N c r0) mult (fun n => pow_N c (f # n))) # n.
       *)

      Lemma mul_constant_mul_br: forall `{Ring R} (n:  nat),
          c * ({{r0, mult, f}} # n) =
          {{r0 * c, mult, f}} # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - rewrite evalBR_step.
          rewrite evalBR_step.
          ring_simplify.
          rewrite IHn.
          ring.
      Qed.

      
      Hint Resolve mul_constant_mul_br : Recurrence.
      Hint Rewrite @mul_constant_mul_br : Recurrence.
    End BR_CONSTANTS.

    Section BR_BR.
      Variable c1 c2: R.
      Variable f1 f2: nat -> R.
      Let br1_add := mkBR c1 plus f1.
      Let br1_mul := mkBR c1 mult f1.

      Let br2_add := mkBR c2 plus f2.
      Let br2_mul := mkBR c2 mult f2.


      (* Lemma 12 *)
      Definition add_add_br_add_br: forall `{Ring R} (n: nat),
          (br1_add # n) + (br2_add # n) = (mkBR (c1 + c2) plus
                                                (fun n => f1 n + f2 n)) # n.
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_add in *.
          unfold br2_add in *.
          rewrite evalBR_step.
          rewrite evalBR_step.
          rewrite evalBR_step.
          ring_simplify.
          replace ((mkBR c1 plus f1 # n) +
                   (f1 # (S n)) +
                   (mkBR c2 plus f2 # n) +
                   (f2 # (S n))) with
              ((mkBR c1 plus f1 # n) +
               (mkBR c2 plus f2 # n) +
               (f1 # (S n)) +
               (f2 # (S n))); try ring.
          rewrite IHn.
          simpl.
          ring.
      Qed.

      
      Hint Resolve add_add_br_add_br: Recurrence.
      Hint Rewrite @add_add_br_add_br: Recurrence.

      
      (* Lemma 13 *)
      (* Definition in paper is WRONG. They index both br1, br2 and the
    functions with the _same index_. It should be one minus *)
      Definition mulCRFn (n: nat): R:=  ((br1_add # (n - 1)) * (f2 # n) +
                                       (br2_add # (n - 1)) * (f1 # n) +
                                       (f1 # n) * (f2 # n)).

      Lemma mul_add_br_add_br: forall `{Ring R} (n: nat),
          (br1_add # n) * (br2_add # n) = ((mkBR (c1 * c2) plus (mulCRFn)) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_add, br2_add in *.
          rewrite evalBR_step.
          rewrite evalBR_step.

          ring_simplify.
          rewrite IHn.
          Opaque evalBR.
          simpl.
          ring_simplify.

          remember (evalBR (mkBR c1 plus f1) n * f2 (S n)) as BR1F2.
          remember ( f1 (S n) * evalBR (mkBR c2 plus f2) n) as BR2F1.
          remember (f2 (S n) * f1 (S n)) as F1F2.
          replace (evalBR (mkBR (c1 * c2) plus mulCRFn) n + BR1F2 + F1F2 + BR2F1)
            with (evalBR (mkBR (c1 * c2) plus mulCRFn) n + (mulCRFn (S n))).

          rewrite evalBR_step.
          simpl.
          auto.

          ring_simplify.
          
          cut (mulCRFn (S n) = BR1F2 + F1F2 + BR2F1).
          intros EQ. rewrite EQ. ring.

          
          unfold mulCRFn.

          rewrite HeqBR1F2.
          rewrite HeqBR2F1.
          rewrite HeqF1F2.
          simpl.
          unfold br1_add.
          unfold br2_add.
          simpl.
          replace (n - 0)%nat with n.
          ring.
          omega.
          Transparent evalBR.
      Qed.

      Hint Resolve mul_add_br_add_br : Recurrence.
      Hint Rewrite @mul_add_br_add_br : Recurrence.

      
      (* Lemma 14 *)
      Lemma mul_mul_br_mul_br: forall `{Ring R} (n: nat),
          (br1_mul # n) * (br2_mul # n) =
          ((mkBR (c1 * c2) mult (fun n => (f1 n * f2 n))) # n).
      Proof.
        intros.
        induction n.
        - simpl. ring.
        - unfold br1_mul, br2_mul in *.
          rewrite evalBR_step.
          rewrite evalBR_step.
          ring_simplify.
          replace ((mkBR c1 mult f1 # n) * (f1 # (S n)) *
                   (mkBR c2 mult f2 # n) * (f2 # (S n))) with
              ((mkBR c1 mult f1 # n) * (mkBR c2 mult f2 # n) *
               (f1 # (S n)) * (f2 # (S n))); try ring.
          rewrite IHn.
          rewrite evalBR_step.
          Opaque evalBR.
          simpl.
          ring.
          Transparent evalBR.
      Qed.

      
      Hint Resolve mul_mul_br_mul_br : Recurrence.
      Hint Rewrite @mul_mul_br_mul_br : Recurrence.
      


    End BR_BR.

    
  End BR.


  (** Define a chain of recurrences *)
  Section CR.
    Inductive CR :=
    | liftBRToCR: BR -> CR
    | recurCR: R -> (R -> R -> R) -> CR -> CR
    .
    

    
    Class LiftToCR A : Type  :=
      {
        liftToCR : A -> CR
      }.


    Global Instance liftToBR_to_liftToCR
           `{A: Type} `{LiftToBR A} : LiftToCR A :=
      {
        liftToCR (prebr: A) :=   liftBRToCR (liftToBR prebr)
                               
      }.

    (** Interpret a CR as nested BRs as described in section 2 -
       Chains of Recurrences *)
    Fixpoint CR_to_BR (cr: CR): BR :=
      match cr with
      | liftBRToCR br =>  br
      | recurCR r0 bop cr' => mkBR r0 bop (evalBR (CR_to_BR cr'))
      end.



    (** Define what it means to evaluate a CR *)
    Instance LoopVariantCr : LoopVariant CR R :=
      {
        evalAtIx (cr: CR) (n: nat) := evalBR (CR_to_BR cr) n
      }.

    Lemma creval_lift_br_to_cr_inverses: forall (br: BR) (n: nat),
       (liftBRToCR br) # n = br # n.
    Proof.
      intros; auto.
    Qed.

    
    Hint Resolve creval_lift_br_to_cr_inverses: Recurrence.
      

    
    (** Basic theorem, show how to unfold CReval *)
    Lemma CReval_recurcr_step: forall
        `{Ring R}
        (cr': CR) (r: R) (bop: R -> R -> R) (n: nat),
        (recurCR r bop cr') # (S n) =
        bop ((CR_to_BR (recurCR r bop cr')) # n) (cr' # (S n)).
    Proof.
      intros.
      Opaque evalBR.
      simpl.
      erewrite evalBR_step; eauto.
      Transparent evalBR.
    Qed.

    Hint Rewrite @CReval_recurcr_step : Recurrence.


    (** Lemma 16 *)
    Lemma add_const_to_CR:
      forall `{Ring R} (r c0: R) (cr: CR) (n: nat),
        r + ((recurCR c0 plus cr) # n) =
        ((recurCR (c0 + r) plus cr) # n).
    Proof.
      intros.
      simpl.
      induction n.
      - simpl. ring.
      - rewrite seq_peel_end; try omega.
        replace (1 + S n - 1)%nat with (S n); try omega.
        replace (S n - 1)%nat with n; try omega.
        repeat (rewrite map_app).
        repeat (rewrite fold_left_app).
        rewrite <- IHn.
        simpl.
        ring.
    Qed.

    Hint Resolve add_const_to_CR : Recurrence.
    Hint Rewrite @add_const_to_CR : Recurrence.

    

    (** Lemma 17 *)
    Lemma mul_const_to_CR:
      forall `{Ring R} (r c0: R) (cr: CR) (n: nat),
        r * ((recurCR c0 mult cr) # n) =
        ((recurCR (c0 * r) mult cr) # n).
    Proof.
      intros.
      induction n.
      - (** n = 0 *)
        simpl; auto; ring.

      - (** n = S n *)
        repeat rewrite CReval_recurcr_step.
        rewrite mul_constant_mul_br.
        autorewrite with Recurrence.
    Qed.


      
    Inductive PureCR (bop: R -> R -> R): Type :=
    | PureBR: R -> R -> PureCR bop
    |  PureCRRec:
         R -> 
        PureCR bop ->
        PureCR bop
    .
    

    (** Convert a `PureCR` into a CR by inserting the correct
        `bop` everywhere *)
    Fixpoint purecr_to_cr (bop: R -> R -> R) (pure: PureCR bop): CR :=
      match pure with
      | PureBR r1 r2 => liftBRToCR (mkBR r1 bop (const r2))
      | PureCRRec r cr' => (recurCR r bop (purecr_to_cr cr'))
      end.

    
    
  Instance loopVariantPureCR (f: R -> R -> R): LoopVariant (PureCR f) (R : Type) :=
    {
      evalAtIx (purecr: PureCR f) (n: nat) := (purecr_to_cr purecr) # n
    }.

    (** Zip the two pureCRs together, to construct a longer PureCR.
     NOTE: This assumes that cr1 is longer than cr2.
     NOTE: If cr1 is not longer than cr2, it returns a Nothing *)
    Fixpoint zip_purecrs (bop: R -> R -> R) (cr1 cr2: PureCR bop) :
      option (PureCR bop) :=
      match (cr1, cr2) with
      (** recurrence *)
      | (PureCRRec r1 cr'1, PureCRRec r2 cr'2) =>
        option_map (PureCRRec (bop r1 r2)) (zip_purecrs cr'1 cr'2)
      (** Base case when cr1 is longer than cr2 *)
      | (PureCRRec r11 (PureCRRec r12 cr'1), PureBR r21 r22) =>
           Some (PureCRRec (bop r11 r21)
                           (PureCRRec (bop r12 r22) cr'1))
      (** Base case when cr1 and cr2 have the same length *)
      | (PureBR r11 r12, PureBR r21 r22) =>
           Some (PureBR bop (bop r11 r21) (bop r12 r22))
      | _ => None
      end.

    (* Define pure-sum and pure-product CRs *)
    Definition PureSumCR : Type := PureCR plus.
    Definition PureProdCR : Type  := PureCR mult.

    (** Lemma 22 *)
    Lemma rewrite_pure_sum_cr_on_add_cr: forall
        (crlong crshort: PureSumCR)
        (pureout: PureSumCR)
        (ZIP: zip_purecrs crlong crshort = Some pureout) (n: nat),
        crlong # n + crshort # n = pureout # n.
    Proof.
      intros.
      simpl.

      generalize dependent pureout.
      induction crlong eqn:CRLONG.
      - (* CRLONG = pure *)
        intros.
        simpl in ZIP.

        induction crshort eqn:CRSHORT.
        + (* crshort = PureBR *)
          Opaque CReval.
          simpl.
      
        
      
      
      

    (*  Lemma 18 *)
    Lemma mul_const_to_pure_sum: forall (c: R) (cr: CR) (n: nat),
        PureSumCR cr ->
        c * (cr # n) = (rewrite_pure_sum_cr_on_mul_const cr c) # n.
    Proof.
      intros until cr.
      generalize dependent c.
      induction cr.
      - intros.
        inversion H; subst.
        Opaque evalBR.
        simpl.
        (* 
        replace c with (evalBR (liftToBR c)  n).
        rewrite mul_b
         *)
    Admitted.
  End CR.
End RECURRENCE.

