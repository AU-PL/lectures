Module Multiplication.

  Inductive nat : Type :=
  | zero : nat
  | suc (n : nat).

  Fixpoint add (m n : nat) : nat :=
    match m with
    | zero => n
    | suc m' => suc (add m' n)
    end.
  
  (*
   *  mult (suc (suc (suc m))) n 
   * = add n (mult (suc (suc m)) n)
   * = add n (add n (mult (suc m) n))
   * = add n (add n (add n m))
   *
   * mult (suc (suc n)) m
   * = add m (mult (suc n) m)
   * = add m (add m n)
   *) 

  Fixpoint mult (m n : nat) : nat :=
    match m with
    | zero => zero
    | suc m' => add n (mult m' n)
    end.

  Lemma add_zero_right : forall (m : nat), add m zero = m.
  Proof using Type. 
    intros m.
    induction m as [IH | m'].
    - simpl. reflexivity.
    - simpl. rewrite IHm'. reflexivity.
  Qed.
  
Lemma mult_one_left : forall (m : nat), mult (suc zero) m = m.
Proof using Type.
  intros m.
  simpl. apply add_zero_right.
Qed.

Lemma mult_one_right : forall (m : nat), mult m (suc zero) = m.
Proof using Type.
  intros m.
  induction m as [IH | m'].
  - simpl. reflexivity.
  - simpl. rewrite IHm'. reflexivity.
Qed.

Lemma mult_sym : forall (m n : nat),
    mult m n = mult n m.
Proof.
  intros m n.
  induction m as [IH | m'].
  - simpl.
    assert (mult_zero_right : forall n, zero = mult n zero).
      intros n'.
      induction n' as [IH | n''].
      + simpl. reflexivity.
      + simpl. apply IHn''.
      + apply mult_zero_right.
  - simpl.
    rewrite IHm'.
    induction n as [IH' | n'].
    + simpl. reflexivity.
    + simpl. 
