(* How do we implement syntax? *)
type term = Var of string
          | T 
          | F 
          | If of term * term * term
          (* let x = t1 in t2 => let(t1,x.t2) => Let(t1,"x",t2)  *)
          | Let of term * string * term;;
(*let expIf = If(F,T,If(F,T,F));;
let expVar = If((Var "x"),T,F);;
*)
let expLet = Let(Let(T,"y",Var "y"),"x",If(F,(Var "x"),T));;

let rec pretty (t:term): string = 
  match t with
  | Var x -> x
  | T -> "true"
  | F -> "false"
  | Let(t1,x,t2) -> "let "^x^" = "^(parens t1)^" in "^(parens t2)
  | If(t1,t2,t3) -> "if("^(pretty t1)^") then "^(parens t2)^" else "^(parens t3)

and

parens (t:term): string = 
  match t with
  | If(_,_,_) -> "("^(pretty t)^")"
  | Let(_,_,_) -> "("^(pretty t)^")"
  | _ -> pretty t;;

(* subst t1 x t2 = [t1/x]t2 
* [t1/x]x = t1 
* [t1/x]y = ??, x != y
* [f/y](let z = T in If(z,t,f)) *)
let rec subst (t1:term) (x:string) (t2:term): term = 
  match t2 with
  | Var y -> if x == y then t1 else t2
  | If(t3,t4,t5) -> If(subst t1 x t3, subst t1 x t4, subst t1 x t5)
  | Let(t3,y,t4) -> if x == y then Let(subst t1 x t3,y,t4) else Let(subst t1 x t3,y,subst t1 x t4)
  | _ -> t2;;

let rec eval (t:term): term = 
  match t with
  | Var x -> Var x
  | T -> T
  | F -> F
  | Let(t1,x,t2) -> eval (subst (eval t1) x t2)
  | If(t1,t2,t3) -> match (eval t1) with
                    | T -> eval t2
                    | F -> eval t3
                    | _ -> If(t1,t2,t3);;

let () = print_endline (pretty (eval expLet));;