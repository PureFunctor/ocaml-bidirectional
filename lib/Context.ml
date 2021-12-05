type element =
  | CVar : string * Syntax.type_t -> element
  | CForall : string -> element
  | CExists : string -> element
  | CSolved : string * Syntax.type_t -> element
  | CMarker : string -> element

type t = element list

let (empty : t) = []

let (|>) (es : t) (e : element) : t = e :: es

let popUntil (e : element) =
  let rec aux = function
    | [] -> None
    | x :: xs -> if (x = e) then Some xs else aux xs in
  aux

let breakAt (e : element) =
  let rec aux ys = function
    | [] -> None
    | x :: xs -> if (x = e) then Some (List.rev ys, xs) else aux (x :: ys) xs in
  aux []

let collect (predicate : string list -> element -> string list) : t -> string list =
  List.fold_left predicate []
