Module Note.

  (* Syntax: *)

  Inductive Exp : Type :=
  | T
  | F
  | And (b1 : Exp) (b2 : Exp)       
  | If  (b : Exp)  (b1 : Exp) (b2 : Exp).

  Notation "b1 /*\ b2" := (And b1 b2) (at level 50, left associativity).

  Definition exp1 : Exp := T.
  Definition exp2 : Exp := T /*\ F.
  Definition exp3 : Exp := If exp2 (T /*\ T) F.  

  (* An indexed data type (b is the index): 
      isVal T 
      isVal F
  *)
  Inductive isVal : Exp -> Prop :=
  | valT : isVal T
  | valF : isVal F.

  (* Parameterized Data Type (b is the parameter): *)
  Inductive isVal' (b : Exp) : Prop :=
  | valT' : b = T -> isVal' b
  | valF' : b = F -> isVal' b.

  (* Evaluation: Single and Multi *)

  Fixpoint eval (b : Exp) : Exp :=
    match b with
    | T => T
    | F => F
    | T /*\ T => T (* AndT  *)
    | F /*\ T => F (* AndF1 *)
    | T /*\ F => F (* AndF2 *)
    | F /*\ F => F (* AndF  *)
    | b1 /*\ b2 =>
      match (eval b1) with
      | T => eval b2
      | F => F
      | _ => b1 /*\ b2
      end
    | If b b1 b2 =>
      match eval b with
      | T => eval b1
      | F => eval b2
      | _ => If b b1 b2
      end       
    end.

  Lemma isval_to_val : forall (b : Exp),
      isVal b -> b = T \/ b = F.
  Proof.
    intros.
    destruct H.
    left.
    trivial.
    right.
    trivial.
  Qed. 

  Lemma eval_T : forall (b : Exp),
   eval b = T ->
     (b = T)
  \/ (exists (b1 b2 : Exp), b = b1 /*\ b2)
  \/ (exists (b1 b2 b3 : Exp), b = If b1 b2 b3).
  Proof.
    intros.
    destruct b.  
    - left. trivial.
    - left. trivial.
    - right. left. exists b1. exists b2. trivial.
    - right. right. exists b1. exists b2. exists b3. trivial.
  Qed.
  
  Lemma eval_and : forall (b1 b2 : Exp),
        (eval b1 = T \/ eval b1 = F) ->
        (eval b2 = T \/ eval b1 = F) ->
        (eval (b1 /*\ b2) = T \/ eval (b1 /*\ b2) = F).
  Proof.
    intros.
    destruct H.
    - destruct H0.
      left.
      simpl.
      rewrite H.
      rewrite H0.
      destruct (eval_T b1).
      * apply H.
      * rewrite H1. destruct (eval_T b2).
      + apply H0.
      + rewrite H2. trivial.
      +  destruct H2.
         { destruct H2. destruct H2. rewrite H2. trivial. }
         { destruct H2. destruct H2. destruct H2. rewrite H2. trivial. }
      *  
           
  Lemma eval_to_val : forall (b : Exp), isVal (eval b).
  Proof. 
    intro b.
    induction b.
    apply valT.
    apply valF.
    
    (* isVal (eval b1) -> eval b1 = T \/ eval b1 = F
    * isVal (eval b2) -> eval b2 = T \/ eval b1 = F 
    * ---------------------------------------------
    * eval (b1 /*\ b2) = T \/ eval (b1 /*\ b2) = F  *)
    

  Compute (eval (If (T /*\ T) (F /*\ T) T)).

End Note.
