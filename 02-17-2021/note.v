Module ListFun.

  (* l1 := [1,2,3,4] 
   * l2 := [1,2,3,3,4,1,5] : list nat *)
  Inductive list (a : Type) : Type :=
  | empty
  | cons (x : a) (l : list a).

  Arguments empty {a}.
  Arguments cons {a}.

  Compute (cons 2 (cons 42 (empty))).

  Definition l1 : list nat := cons 1 (cons 2 (cons 3 (cons 4 empty))).
  Definition l2 : list nat := cons 1
                                   (cons 2
                                          (cons 3
                                                 (cons 3
                                                        (cons 4
                                                               (cons 1
                                                                      (cons 5 empty)))))).


  (* l3 := [1,2,3]  
   * f : nat -> nat       foo<a><b> 
   * f x := x + 3 
   * map f l3 = [f 1, f 2, f 3] 
   *          = [1 + 3, 2 + 3, 3 + 3] *)
  Fixpoint map {a b : Type} (f : a -> b) (l : list a) : list b :=
    match l with
    | empty => empty
    | cons x l' => cons (f x) (map f l')
    end.
  
  Import Nat.

  Compute map (add 3) l1.

  Definition id {a : Type} (x : a) : a := x.
  
  Definition proj1 {a b : Type} (p : a * b) : a :=
    match p with
      ( x , y ) => x
    end.

    Definition proj2 {a b : Type} (p : a * b) : b :=
    match p with
      ( x , y ) => y
    end. 

   (* 
   * lfold (reduce) : Left folds a list to a value.
   *                  Accumilator pattern
   * 
   * l4 = [5,6,7,8]
   * f auc x = 
   *
   * *)
  Fixpoint append {a : Type} (l1 l2 : list a) : list a :=
    match l1 with
    | empty => l2
    | cons n l' => cons n (append l' l2)
    end.

  (* Not tail recursive  *)
  Fixpoint slow_reverse (l : natlist) : natlist :=
    match l with
    | empty _ => nempty
    | cons _ n l' => append (slow_reverse l') (ncons n nempty)
    end.

  (* Accumulator Pattern : use "state"
   *
   * Add an extra argument to reverse that holds onto the reversed list.
   *   - The type of the accumilator must be the same type as the output type.  
   *
   * *)

  Fixpoint reverse' (acc : natlist) (l : natlist) : natlist :=
    match l with
    | empty _ => acc
    | cons _ n l' => reverse' (ncons n acc) l'
    end.

  Compute (reverse' nempty l1).

  Definition reverse (l : natlist) : natlist :=
    reverse' nempty l.

  Lemma append_empty_left : forall l, append nempty l = l.
  Proof.
    intros l. 
    simpl.  reflexivity.
  Qed.

  Lemma append_empty_right : forall l, append l nempty = l.
  Proof.
    intro l.
    induction l as [_ | x l' IH].
    - simpl. reflexivity.
    - simpl. rewrite -> IH. reflexivity.
  Qed.



End ListFun.
