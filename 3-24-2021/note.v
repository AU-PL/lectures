Module Note.

  (* Syntax: *)

  Inductive Exp : Type :=
  | T
  | F
  | And (b1 : Exp) (b2 : Exp)       
  | If (b : Exp) (b1 : Exp) (b2 : Exp).

  Notation "b1 /*\ b2" := (And b1 b2) (at level 50, left associativity).

  Definition exp1 : Exp := T.
  Definition exp2 : Exp := T /*\ F.
  Definition exp3 : Exp := If exp2 (T /*\ T) F.  

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

  Compute (eval (If (T /*\ T) (F /*\ T) T)).

End Note.
