Module Stack.

Inductive Stack :=
  | empty
  | Push (e : nat) (s : Stack).

Compute empty : Stack.

Compute Push 1 empty : Stack.

Compute Push 2 (Push 1 empty) : Stack.

Definition s1 : Stack := 
  Push 2 (Push 1 empty).

Compute Push 3 s1 : Stack.

(* Stack Pairs: (e,r) *)
Inductive stackpair : Type :=
  | pair (n : nat) (s : Stack).

Notation "( x , y )" :=
  (pair x y) : core_scope. 

Definition fst (p : stackpair) : nat :=
   match p with
   | (n , _) => n
   end.

Definition snd (p : stackpair) : Stack :=
    match p with
    | (_ , s) => s
    end.

Compute (1,empty).

(*
* Inductive MaybeStackpair : Type :=
*  | Nothing
*  | Just (p : stackpair).
*)
Inductive Maybe (a : Type) : Type :=
  | Nothing
  | Just (x : a).

Check Nothing.

Definition MaybeStackpair : Type := Maybe stackpair .

(* How to pop the stack? 
 * 
 * | 3 |      Push 3 (
 * | 2 |           Push 2 (
 * | 1 | ===>        Push 1         
 * | e |                    empty))
 *)
Definition pop (s : Stack) : Maybe stackpair :=
  match s with
  | empty => @Nothing stackpair
  | Push e s' => Just stackpair (e , s')
  end.

Compute pop s1.

Definition peek (s : Stack) : Maybe nat := 
  match pop s with
  | Nothing _ => @Nothing  nat
  | Just _ (e , _) => Just nat e
  end.

Compute pop s1 : MaybeStackpair.
Compute peek s1 : Maybe nat.

(*
 * 
 * m a -> (a -> m b) -> m b *)
Definition compStack
           (c : MaybeStackpair)
           (f : stackpair -> MaybeStackpair) : MaybeStackpair :=
  

(* pop s1 = Just (h,s1') : MaybeStackpair
 * Push 2 : Stack -> Stack
 * 
 * Compute  Push 2 (pop s1). (* = s1 *) *)

Module Examples.

(* n1 + n2 => n2 + n1
 * n2 + n1 => n1 + n2
 * n1 + n2 <= n2 + n1  *)  
  Lemma add_sym : forall n1 n2 n3,
    n1 + n2 = n2 + n1 ->
    (n1 + n2) + n3 = (n2 + n1) + n3.
  Proof.
    intros.
    rewrite <- H. reflexivity.
  Qed.
