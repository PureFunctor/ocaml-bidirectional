type complete
type incomplete

type 'a element =
  | CVar : string * Syntax.poly Syntax.type_t -> 'a element
  | CForall : string -> 'a element
  | CExists : string -> incomplete element
  | CSolved : string * Syntax.mono Syntax.type_t -> 'a element
  | CMarker : string -> 'a element

type 'a t = 'a element list

let empty : type a. a t = []

let (|>) (type a) (es : a t) (e : a element) : a t = e :: es

let popUntil (type a) (e : a element) =
  let rec aux = function
    | [] -> None
    | x :: xs -> if (x = e) then Some xs else aux xs in
  aux

let breakAt (type a) (e : a element) =
  let rec aux ys = function
    | [] -> None
    | x :: xs -> if (x = e) then Some (List.rev ys, xs) else aux (x :: ys) xs in
  aux []

let collect (type a) (predicate : string list -> a element -> string list) : a t -> string list =
  List.fold_left predicate []
