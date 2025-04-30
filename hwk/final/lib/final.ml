(* Do not modify:  *)
let rec map f l =
  match l with
  | [] -> []
  | x::rest -> f x :: map f rest

let rec reduce f s l = 
  match l with
  | [] -> s
  | x::rest -> reduce f (f s x) rest 

let mem t = reduce (fun r -> fun x -> (t = x || r)) false

let rec lookup (p:'a) (l: ('a * 'b) list) = 
  match l with 
  | (p1,p2)::rest ->
    if p = p1 then
      Some p2
    else 
      lookup p rest
  | _ -> None

type term = 
  True | False | If of term * term * term 
| Fun of (term -> term) | App of term * term
(* let(t1, x.t2) *)
| Let of term * (term -> term)

type mType = 
  Bool | Fun of mType * mType

type var = 
  string * term

type preTerm = 
    True | False | If of preTerm * preTerm * preTerm 
  | Var of var | Fun of mType * (var -> preTerm) | App of preTerm * preTerm
  | Let of mType * preTerm * (var -> preTerm)
        
let rec toTerm (p : preTerm): term = 
  match p with
  | True -> True
  | False -> False
  | If(p1,p2,p3) -> If(toTerm p1, toTerm p2, toTerm p3)
  | Var (_,t') -> t'
  | Fun (_,t') -> Fun (fun x -> toTerm (t' ("x", x)))
  | App (t1, t2) -> App (toTerm t1, toTerm t2)
  | Let (_, t1, t2) -> Let (toTerm t1, fun x -> toTerm (t2 ("x", x)))
  
let rec typeCheck (ctx : (var * mType) list) (t : preTerm) (ty : mType): var list -> bool = 
  fun vars -> 
    match (t,ty) with
    | (True, Bool) -> true
    | (False, Bool) -> true
    | (Var var, _) -> mem (var, ty) ctx
    | (Fun (ty1', t'), Fun (ty1, ty2)) -> 
      (match vars with
        | (x::rest) -> ty1' = ty1 && (typeCheck ((x, ty1)::ctx) (t' x) ty2) rest
        | _ -> false)
    | (App (t1, t2), _) -> 
      (match synthType ctx t1 vars with
        | Some (Fun (_, ty2)) -> ty = ty2 && typeCheck ctx t2 ty2 vars
        | _ -> false)
    | (If (b,t1,t2), _) -> 
      (typeCheck ctx b Bool vars) &&
      (typeCheck ctx t1 ty vars) &&
      (typeCheck ctx t2 ty vars)
    | (Let (ty1, t1, t2), _) -> 
        (match vars with
          | (x::rest) -> 
          (typeCheck ctx t1 ty1 rest) &&
          (typeCheck ((x, ty1)::ctx) (t2 x) ty) rest
          | _ -> false)
    | _ -> false
and synthType (ctx : (var * mType) list) (t : preTerm): var list -> mType option = 
          fun vars -> 
          match t with
          | True -> Some Bool
          | False -> Some Bool
          | Var var -> lookup var ctx
          | Fun (ty1, t') -> 
            (match vars with
              | x::rest -> 
              (match synthType ((x,ty1)::ctx) (t' x) rest with
                | Some ty2 -> Some (Fun (ty1, ty2))
                | _ -> None)
              | _ -> None)
          | App (t1,t2) -> 
            (match synthType ctx t1 vars with
              | Some (Fun (ty1, ty2)) -> 
              if typeCheck ctx t2 ty1 vars then 
                Some ty2 
              else 
                None
              | _ -> None)
          | If(b,t1,t2) -> 
            if typeCheck ctx b Bool vars then
              (match synthType ctx t1 vars with
                | Some ty -> 
                  if typeCheck ctx t2 ty vars then
                    Some ty
                  else 
                    None
                | _ -> None)
            else
              None
          | Let (ty1,t1,t2) -> 
            if typeCheck ctx t1 ty1 vars then
              (match vars with
                | x::rest -> synthType ((x,ty1)::ctx) (t2 x) rest
                | _ -> None)
            else
              None

let rec eval (t:term): term = 
  match t with
  | If(True, t1, _t2) -> eval t1
  | If(False, _t1, t2) -> eval t2
  | If(t0, t1, t2) -> 
      let v = eval t0
      in eval (If(v,t1,t2))
  | App (Fun t1, t2) -> 
      let v2 = eval t2 in eval (t1 v2)
  | App (t1,t2) -> 
      let v1 = eval t1 in eval (App (v1, t2))
  | Let (t1, t2) -> 
      let v1 = eval t1 in
      eval (t2 v1)
  | v -> v
(* End do not modify *)

(* Before starting get aquatinted with the code for preTerm, term, mType, toTerm,
synthType, and eval.*)

(* 1. Define an example preterm that uses boolean-if, numbers, and functions. *)
let (p:preTerm) = True;;

(* 2. Convert, p, into a term. *)
let (t:term) = True;;

(* 3. Synthesize the type of t.*)
let (myType:mType) = Bool;;

(* 4. Apply t to some arguments and evaluate it to a value. *)
let (v:term) = True;;














