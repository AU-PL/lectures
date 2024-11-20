let rec zip (l1: 'a list) (l2: 'b list): ('a * 'b) list = 
  match (l1,l2) with
  | ([],_) -> []
  | (_,[]) -> []
  | (x1::rest1,x2::rest2) -> (x1,x2) :: zip rest1 rest2

  