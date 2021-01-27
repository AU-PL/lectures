(*
 * match n with
 * |  0     => ...
 * | suc n' => suc suc (f n')
 *)

Lemma add_zero : forall n', n' > 0  -> 
                            n' < 42 -> n' + 0 = n'.
Proof.  Admitted.

Module Trees.

(* Binary Trees:
 *    - a binary tree data type,
 *    - insert into the tree,
 *    - lookup from the tree,
 *    - map for trees,
 *    - folds (reduce) for trees. 
 *    - Spec: properties about the API. *)

Inductive BinaryTreeE : Type :=
  | Empty
  | Branch (d : nat) (left : BinaryTreeE) (right : BinaryTreeE).

 Inductive BinaryTreeNE : Type :=
 | Leaf (d : nat)
 | BranchNE (d : nat) (left : BinaryTreeNE) (right : BinaryTreeNE).

(* Encodable using BinaryTreeE *)
Inductive BinaryTreeENE : Type :=
 | EmptyENE
 | LeafENE
 | BranchENE (left : BinaryTreeENE) (right : BinaryTreeENE).
