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

Definition fst (p : stackpair) : nat :=
   match p with
   | pair n _ => n
   end.

Definition snd (p : stackpair) : Stack :=
    match p with
    | pair _ s => s
    end.

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
  | Push e s' => Just stackpair (pair e s')
  end.

Definition peek (s : Stack) : Maybe nat := 
  match pop s with
  | Nothing _ => @Nothing  nat
  | Just _ (pair e _) => Just nat e
  end.

Compute pop s1 : stackpair.
Compute peek s1 : nat.

