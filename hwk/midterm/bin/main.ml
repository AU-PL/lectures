(* Start do not modify. *)
let reverse (a : 'e list): 'e list = 
    let rec rev_helper (accum: 'e list) (b: 'e list): 'e list = 
        match b with
         [] -> accum
        | h::t -> rev_helper (h::accum) t
    in rev_helper [] a
(* End do not modify. *)

(* 0. Read chapter 4 in the book:
        https://hde.design/plweb/includes/lecture-notes/book.pdf
      After, complete the following questions. *)

(* 1. You will write a parser for tuples.  That is, given a string "10,22,31,42"
    the parser will return a list of integers [10,22,31,42]. We will break this
    problem up into two steps.

 a. The first step will require you to write two functions, the first, a
    predicate on characters that is true when the input character is an integer,
    but false otherwise. *)
 
 let isInt (c:char): bool = false;;

 (* b. Second, you are required to fill in the following auxiliary function to
    the tupleToList function that parses a single character given an
    accumulator.    

    If the accumulator, accum, is (n,ns), then n accumulates the symbols of the
    current integer being parsed, but when a comma is hit during parsing, we add
    n to ns, because we have all of its symbols.

    Using this intuition define the aux function below, but first, work out how
    one would parse "42,24,321" on paper.
 *)

let aux (accum:((string * string) list)) (c:char): (string * string list) = ("",[]);;

(* c. Finally, using aux above fill in the following function that should return
    the fully parsed input string. You will also need to use the reverse
    function on lists. *)
let tupleToList (accum:(string list)) (s:string): (string list) = [];;

(* d. Using tupleToList and the function

    int_of_string : string -> int

    write the following function that parses the input string, and then converts
    the parsed list into a list of integers. *)
let parseTuple (s:string): (int list) = [];;