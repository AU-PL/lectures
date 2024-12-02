(* How do we implement syntax? *)
type typeT = Boolean | String;;

type term = Var of string
          | Str of string
          | T 
          | F 
          | If of term * term * term
          (* let x = t1 in t2 => let(t1,x.t2) => Let(t1,"x",t2)  *)
          | Let of term * (string * typeT) * term;;

(*let expIf = If(F,T,If(F,T,F));;
let expVar = If((Var "x"),T,F);;
*)
let expLet = Let(Let(T,("y", Boolean),Var "y"),("x", Boolean),If(F,(Var "x"),T));;
let _ = (String,Str "");;

let rec pretty (t:term): string = 
  match t with
  | Var x -> x
  | Str s -> "\""^s^"\""
  | T -> "true"
  | F -> "false"
  | Let(t1,(x,_),t2) -> "let "^x^" = "^(parens t1)^" in "^(parens t2)
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
  | Let(t3,(y,ty),t4) -> if x == y then Let(subst t1 x t3,(y,ty),t4) else Let(subst t1 x t3,(y,ty),subst t1 x t4)
  | _ -> t2;;

let rec eval' (t:term): term = 
  match t with  
  | Let(t1,(x,_),t2) -> eval' (subst (eval' t1) x t2)
  | If(t1,t2,t3) -> (match (eval' t1) with
                     | T -> eval' t2
                     | F -> eval' t3
                     | _ -> If(t1,t2,t3))
  | _ -> t;;

let () = print_endline (pretty (eval' expLet));;

(* Typing: 
G |- t : A,
x1 : A1, ... , xi : Ai |- t : B

G |- t1 : Boolean
G |- t2 : A
G |- t3 : A
---------------------- : If
G |- if(t1,t2,t3) : A
*)

let rec type_check (ctx:(string * typeT) list) (t:term) (ty:typeT): bool = 
  match t with
  | T -> (match ty with 
          | Boolean -> true
          | String -> false)
  | F -> (match ty with 
          | Boolean -> true
          | String -> false)
  | Str _ -> (match ty with 
              | Boolean -> false
              | String -> true)
  | Var x -> List.mem (x,ty) ctx
  | If(t1,t2,t3) -> (type_check ctx t1 Boolean) &&  (type_check ctx t2 ty) && (type_check ctx t3 ty)
  (*
  ctx |- t1 : ty'
  ctx, x : ty' |- t2 : ty
  ------------------------ Let
  ctx |- Let(t1,x,t2) : ty
  *)
  | Let(t1,(x,ty'),t2) -> (type_check ctx t1 ty') && (type_check ((x,ty')::ctx) t2 ty);;

  let eval (t:term) (ty:typeT) = if (type_check [] t ty) then eval' t else F;;

  let () = print_endline (if (type_check [] expLet String) then "true" else "false");;
