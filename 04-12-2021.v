Module IffyLang.

  Inductive Exp : Type :=
  | T : Exp
  | F : Exp
  | If (b : Exp) (b1 : Exp) (b2 : Exp)
  | And (b1 : Exp) (b2 : Exp).

   Inductive isVal : Exp -> Prop :=    
   | valT : isVal T
   | valF : isVal F.

  Fixpoint  eval (b : Exp) : exists v:Exp, isVal v :=
    match b with
    | T => ex_intro isVal T valT
    | F => ex_intro isVal F valF
    | And b1 b2 =>
      match eval b1 with
      | ex_intro _ F valF => ex_intro isVal F valF
      | ex_intro _ F valT => _
      | ex_intro _ T _ => eval b2
      | ex_intro _ (And b1' b2') _ => ex_intro isVal F valF
      | ex_intro _ (If b1' b2' b3') _ => ex_intro isVal F valF
      end
    | If b' b1 b2 =>
      match eval b' with
      | ex_intro _ T _ => eval b1
      | ex_intro _ F _ => eval b2
      | _ => ex_intro isVal F valF
      end
    end.

  Definition exp1 : Exp := And T T.
  Definition exp2 : Exp := If exp1 (And F T) T.
  Compute eval exp2.

End IffyLang.
  
