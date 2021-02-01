(* l1 := [1,2,3,4] 
 * l2 := [1,2,3,3,4,1,5] : list nat *)
Inductive list (a : Type) : Type :=
| empty
| cons (x : a) (l : list a).

Compute (cons nat 2 (cons nat 42 (empty nat))).
Definition natlist : Type := list nat.
Definition ncons : nat -> natlist -> natlist := cons nat.
Definition nempty : natlist := empty nat.

Definition l1 : natlist := ncons 1 (ncons 2 (ncons 3 (ncons 4 nempty))).
Definition l2 : natlist := ncons 1
                             (ncons 2
                                (ncons 3
                                   (ncons 3
                                      (ncons 4
                                         (ncons 1
                                            (ncons 5 nempty)))))).


(* l3 := [1,2,3]  
 * f : nat -> nat       foo<a><b> 
 * f x := x + 3 
 * map f l3 = [f 1, f 2, f 3] 
 *          = [1 + 3, 2 + 3, 3 + 3] *)
Fixpoint map (a b : Type) (f : a -> b) (l : list a) : list b :=
  match l with
  | empty _ => empty b
  | cons _ x l' => cons b (f x) (map a b f l')
  end.

Import Nat.

Compute map nat nat (add 3) l1.

(* 
 * lfold (reduce) : Left folds a list to a value.
 *                  Accumilator pattern
 * 
 * l4 = [5,6,7,8]
 * f auc x = 
 *
 * *)
Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | empty _ => l2
  | cons _ n l' => ncons n (append l' l2)
  end.

Fixpoint reverse (l : natlist) : natlist :=
  match l with
  | empty _ => nempty
  | cons _ n l' => append (reverse l') (ncons n nempty)
  end.

