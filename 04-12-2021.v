Module IffyLang.

  Inductive Exp : Type :=
  | T : Exp
  | F : Exp
  | If (b : Exp) (b1 : Exp) (b2 : Exp)
  | And (b1 : Exp) (b2 : Exp).    

  Fixpoint  eval (b : Exp) : Exp :=
    match b with
    | T => T
    | F => F
    | And b1 b2 =>
      match eval b1 with
      | T => eval b2
      | F => F
      | _ => And b1 b2                           
      end
    | If b' b1 b2 =>
      match eval b' with
      | T => eval b1
      | F => eval b2
      | _ => If b' b1 b2
      end
    end.

  Definition exp1 : Exp := And T T.
  Definition exp2 : Exp := If exp1 (And F T) T.
  Compute eval exp2.

  (* Parameterized Data Types *)
   Inductive isVal' (b : Exp) : Prop :=
   | valT' : b = T -> isVal' b
   | valF' : b = F -> isVal' b.
   
   (* Indexed Data Types *)
   Inductive isVal : Exp -> Prop :=    
   | valT : isVal T
   | valF : isVal F.   

   Theorem eval_isVal : forall b, isVal (eval b).
   Proof.
     intros.
     induction b.

     - simpl. apply valT.
     - simpl. apply valF.
     - simpl. destruct IHb1. apply IHb2. apply IHb3.
     - simpl. destruct IHb1. apply IHb2. apply valF.
   Qed.

   (* Intrepret IffyLang into Coq's Prop. Then we will prove
    * the Coq expression. 
    * 
    * => b1 | b2 | b1 -> b2
    *    T  | T  | T 
    *    F  | T  | T
    *    T  | F  | F
    *    F  | F  | T          *)

   (* The interpretation of IffyLang into Coq. *)
   Fixpoint toCoq (b : Exp) : Prop :=
     match b with
     | T => True
     | F => False
     | And b1 b2 => (toCoq b1) /\ (toCoq b2)
     | If b1 b2 b3 =>
       ((toCoq b1) -> toCoq b2) /\ (~(toCoq b1) -> toCoq b3)
     end.

   Theorem eval_sound_T : forall b, eval b = T -> toCoq b.
   Proof.
     intros.
     induction b.

     - simpl. trivial.
     - simpl. simpl in H. discriminate.
     - simpl. split. intros. apply IHb2.
       simpl in H. destruct (eval b1). apply H. 
End IffyLang.
  
