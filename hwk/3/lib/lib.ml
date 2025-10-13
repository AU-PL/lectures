
type 'token_type parser_state = 'token_type list;;

type ('a, 'token_type) state = 'token_type parser_state -> 'a * 'token_type parser_state

let bind (comp: ('a, 'token_type) state) 
         (continuation: 'a -> ('b, 'token_type) state): (('b, 'token_type) state)
  = fun state -> let (a,new_state) = comp state 
                  in continuation a new_state

let return (value: 'a): ('a, 'token_parser) state 
  = fun state -> (value, state)

let put (tokens: 'token parser_state): (unit, 'token) state = 
  fun _ -> ((), tokens)

let get: ('token parser_state, 'token) state = 
  fun state -> (state, state)

let (let*) comp contiue = bind comp contiue

