(* a. Convert the `sum_NT` function into a tail recursive version using two
      different functions called `sum_helper` and `sum_TR`. *)
let rec sum_NT i stop =
  if i == stop
  then stop
  else i+(sum_NT (i+1) stop)

let rec sum_helper = 0

let rec sum_TR = 0

(* b. Find inputs where `sum_NT` issues a stack overflow, but `sum_TR` computes
      a value.  Define `blowsStackInput` to be the pair of the inputs you found
      that blows the stack, then define `computesValue` as the application of
      `sum_TR` to `blowsStackInput ()` using the functions:

   - First: fst : a' * b' -> a'
   - Second: snd : a' * b' -> b' *)
   
let blowsStack () = 0

let computesValue () = 0
   
(* c. Evaluate `sum_TR 1 2` using the call stack and activation frames. Write
      out each activation frame as you progress just as we did in the lecture.
      Place your solution in the designated comment. *)

(*
  Add your call stack here.                             
*)

(* d. Do an online search for "compiler optimizations" and read about one we did
      not cover in class. Summarize in a comment the optimization you found.
      Make sure to include the link to where you read about it. *)

(*
  Add your summary here.                             
*)