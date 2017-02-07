module Con : sig
    type t =
        | Single of string
        | Family of string * Type.t

    val name  : t -> string
    val index : t -> Type.t option
end

type t =
    | App of head * t list
    | Lam of string * t
and head =
    | Var of int
    | Con of Con.t
    | MVar of string

val eq : t -> t -> bool
val subst : t -> int -> t -> t
val redex : t -> t list -> t
val shift : t -> t
val mvar_subst : t -> string -> t -> t

val lam : string -> t -> t
val var : int -> t list -> t
val con : Con.t -> t list -> t
