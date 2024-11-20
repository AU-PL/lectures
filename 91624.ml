type 'elTy list = Empty |  Cons of 'elTy * 'elTy list

type 'a maybe = Nothing | Just of 'a

let ex1List: int list = Cons (3, Empty) (* [3]  *)
let ex2List: int list = Cons (42, Cons(16, Cons(18, Empty))) (* [42,16,18] *)

let head (l : 'elTy list): 'elTy maybe = 
  match l with
  | Empty -> Nothing
  | Cons(x,_) -> Just x

  let tail (l: 'elTy list): 'elType list = 
    match l with
    | Empty -> Empty
    | Cons(_,tail) -> tail

let map (f: 'a -> 'b) (l: 'a list): 'b list =
  let rec map_helper (outputs: 'b list) (inputs: 'a list): 'b list =
    match inputs with
    | Empty -> outputs
    | Cons(x,tail) -> map_helper (Cons (f x,outputs)) tail
  in map_helper Empty l

let add n k m = n + k + m
let exApp = fun n -> (add n 2 1)
let ex2App = (add 1 2)



