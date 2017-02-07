module Type : sig
    type t = 
        | Atom  of string
        | Arrow of t * t
end = struct
    type t =
        | Atom   of string
        | Arrow  of t * t
end

module Con : sig
    type t = 
       | Single of string
       | Family of string * Type.t
    val name : t -> string
    val index : t -> Type.t option
end = struct
    type t =
        | Single of string
        | Family of string * Type.t

    let name = function
        | Single c | Family (c, _) -> c

    let index = function
        | Single _ -> None
        | Family (_, i) -> Some i
end

module Term : sig
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of Con.t
        | MVar  of string

    val eq : t -> t -> bool

    val lam : string -> t -> t
    val var : int -> t list -> t
    val con : Con.t -> t list -> t
    val redex : t -> t list -> t

    val mvar_subst : t -> string -> t -> t
    val shift : t -> t
end = struct
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of Con.t
        | MVar  of string

    let eq x y = x = y

    let lam x body = Lam (x, body)

    let var x spine = App (Var x, spine)

    let con c spine = App (Con c, spine)

    let rec subst e lvl = function
        | Lam (x, body) ->
            Lam (x, subst (shift e) (lvl + 1) body)
        | App (Var i, spine) when i = lvl ->
            redex e (List.map (subst e lvl) spine)
        | App (Var i, spine) when i > lvl ->
            App (Var (i - 1), List.map (subst e lvl) spine)
        | App (Var i, spine) ->
            App (Var i, List.map (subst e lvl) spine)
        | App (Con c, spine) ->
            App (Con c, List.map (subst e lvl) spine)
        | App (MVar m, spine) ->
            App (MVar m, List.map (subst e lvl) spine)

    and redex e spine = match e, spine with
        | App (head, spine'), _ ->
            App (head, spine' @ spine)
        | Lam (x, body), e' :: spine' ->
            redex (subst e' 0 body) spine'
        | Lam (x, body), [] ->
            Lam (x, body)
 
    and shift =
        let rec shift_term lvl = function
            | App (head, spine) ->
                App (shift_head lvl head, shift_spine lvl spine)
            | Lam (x, e) ->
                Lam (x, shift_term (1 + lvl) e)
        and shift_head lvl = function
            | Var i when i < lvl -> Var i
            | Var i -> Var (i + 1)
            | Con c -> Con c
            | MVar m -> MVar m

        and shift_spine lvl = List.map (shift_term lvl)

        in shift_term 0

    let mvar_subst term mvar =
        let rec mvar_subst = function
            | Lam (x, t) -> Lam (x, mvar_subst t)
            | App (MVar mvar', spine) when mvar = mvar' ->
                redex term (List.map mvar_subst spine)
            | App (head, spine) ->
                App (head, List.map mvar_subst spine)
        in mvar_subst
end
