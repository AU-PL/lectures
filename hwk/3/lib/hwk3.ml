(* Do not change the following: *)
type ty = 
    True 
  | False
  | And of ty * ty
  | Or  of ty * ty
  | Imp of ty * ty;;

(* Assignment: *)

(* 1. Write the solve function to output True or False for any input formula
 *    based on the truth table for propositional logic.
 * 
 *    You must use pattern matching, and you are not allowed to convert to
 *    booleans. *)
let rec solve (ty:ty): ty = False;;

(* 2. Run solve on the formula you derived in the written portion in part a.
 *
 *    Just the formula. Use formulas. *)
let run_solve_a: ty = False;;

(* 3. Run solve on the formula you derived in the written portion in part b. 
 *
 *    Just the formula. Use formulas. *)
let run_solve_b: ty = False;;

