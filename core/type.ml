type t = 
    | Atom  of string
    | Arrow of t * t

module Sign : sig
    type t
    val empty   : t
    val add     : string -> t -> t
    val defined : string -> t -> bool 
end = struct 
    type t = StringSet.t 
 
    let empty = StringSet.empty 
    let add = StringSet.add_unique 
    let defined = StringSet.mem
end

let rec check typeSign = function
    | Atom x ->
        if Sign.defined x typeSign
        then ()
        else failwith ("Type.check: undeclared atom: " ^ x)
    | Arrow (a, b) ->
        check typeSign a; check typeSign b
