Module IffyLang.

  Inductive Exp : Type :=
  | T : Exp
  | F : Exp
  | If (b : Exp) (b1 : Exp) (b2 : Exp)
  | And (b1 : Exp) (b2 : Exp).

  Definition isVal (b : Exp) : Prop :=
    match b with
    | T => True
    | F => True
    | And _ _ => False
    | If _ _ _ => False
    end. 

  Fixpoint  eval (b : Exp) : Exp :=
    match b with
    | T => T
    | F => F
    | And b1 b2 =>
      match eval b1 with
      | F => F
      | _ => eval b2
      end
    | If b' b1 b2 =>
      match eval b' with
      | T => eval b1
      | F => eval b2
      | _ => F
      end
    end.

  Definition exp1 : Exp := And T T.
  Definition exp2 : Exp := If exp1 (And F T) T.
  Compute eval exp2.

End IffyLang.
  
