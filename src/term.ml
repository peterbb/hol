module TypeSign : sig
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

module Type : sig
    type t = 
        | Atom  of string
        | Arrow of t * t

    val check : TypeSign.t -> t -> unit
    val to_string : t -> string
end = struct
    type t =
        | Atom   of string
        | Arrow  of t * t

    let check typeSig =
        let rec check = function
        | Atom x ->
            if TypeSign.defined x typeSig
            then ()
            else failwith "Type.check: atom not declared"
        | Arrow (a, b) ->
            check a; check b
        in check

    open Printf
    let rec to_string = function
        | Atom s -> s
        | Arrow (Atom s, b) -> sprintf "%s -> %s" s (to_string b)
        | Arrow (a, b) -> sprintf "(%s) -> %s" (to_string a) (to_string b)
end

module OpenType : sig
    type t = 
        | Hole
        | Atom  of string
        | Arrow of t * t

    val check : TypeSign.t -> t -> unit
    val fill : Type.t -> t -> Type.t
end = struct
    type t =
        | Hole
        | Atom   of string
        | Arrow  of t * t

    let check typeSig =
        let rec check = function
        | Hole -> ()
        | Atom x ->
            if TypeSign.defined x typeSig
            then ()
            else failwith "Type.check: atom not declared"
        | Arrow (a, b) ->
            check a; check b
        in check

    open Type

    let fill t =
        let rec fill = function
        | Hole -> t
        | Atom x -> Atom x
        | Arrow (a, b) -> Arrow (fill a, fill b)
        in fill
end

module Sign : sig
    type t

    val empty      : t
    val add_type   : string -> t -> t
    val add_con    : string -> Type.t -> t -> t
    val add_icon   : string -> OpenType.t -> t -> t

    val check_type : t -> Type.t -> unit
    val lookup_con : string -> Type.t option -> t -> Type.t
end = struct
    type sort = 
        | Closed    of Type.t
        | Open      of OpenType.t

    type t = {
         typeSign : TypeSign.t ;
         conSign  : sort StringMap.t
    }

    let empty = {
        typeSign = TypeSign.empty;
        conSign = StringMap.empty
    }

    let check_type {typeSign} t = Type.check typeSign t

    let add_type name ({typeSign} as sign) =
        let typeSign = TypeSign.add name typeSign in
        { sign with typeSign }

    let add_con name type_ ({typeSign; conSign} as sign) =
        Type.check typeSign type_;
        let conSign = StringMap.add_unique name (Closed type_) conSign in
        { sign with conSign }

    let add_icon name type_ ({typeSign; conSign} as sign) =
        OpenType.check typeSign type_;
        let conSign = StringMap.add_unique name (Open type_) conSign in
        { sign with conSign }

    let lookup_con name maybe_filler {conSign} =
        match StringMap.find name conSign, maybe_filler with
        | Closed a, None -> a
        | Open a, Some b -> OpenType.fill b a
        | Closed _, Some _ -> failwith "constant not parametric"
        | Open _, None  -> failwith "constant expect type parameter"
end

module Ctx : sig
    type t
    val empty : t
    val add : string -> Type.t -> t -> t
    val lookup : int -> t -> Type.t
    val name : int -> t -> string
    val is_empty : t -> bool
    val iter : (string -> Type.t -> unit) -> t -> unit
end = struct
    type t = (string * Type.t) list

    let empty = []
    let add var type_ ctx = (var, type_) :: ctx
    let lookup var ctx = snd (List.nth ctx var)
    let name var ctx = fst (List.nth ctx var)
    let is_empty ctx = ctx = []
    let iter f = List.iter (fun (x, y) -> f x y)
end


module Term : sig
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of string * Type.t option

    val eq : t -> t -> bool

    val lam : string -> t -> t
    val var : int -> t list -> t
    val con : string -> t list -> t
    val icon : string -> Type.t -> t list -> t
    val redex : t -> t list -> t

    val check : Sign.t -> Ctx.t -> t -> Type.t -> unit
    val to_string : Ctx.t -> t -> string
    val shift : t -> t
end = struct
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of string * Type.t option

    let eq x y = x = y

    let lam x body = Lam (x, body)

    let var x spine = App (Var x, spine)

    let con c spine = App (Con (c, None), spine)

    let icon c ty spine = App (Con (c, Some ty), spine)

    let rec subst e lvl = function
        | Lam (x, body) ->
            Lam (x, subst (shift e) (lvl + 1) body)
        | App (Var i, spine) when i = lvl ->
            redex e (List.map (subst e lvl) spine)
        | App (Var i, spine) when i > lvl ->
            App (Var (i - 1), List.map (subst e lvl) spine)
        | App (Var i, spine) ->
            App (Var i, List.map (subst e lvl) spine)
        | App (Con (c, type_), spine) ->
            App (Con (c, type_), List.map (subst e lvl) spine)

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
            | Var i when i >= lvl ->
                Var (i + 1)
            | Var i ->
                Var i
            | Con (name, type_) ->
                Con (name, type_)

        and shift_spine lvl = List.map (shift_term lvl)

        in shift_term 0

    let check sign =
        let rec check_term ctx term type_ : unit = match term, type_ with
        | App (head, spine), _ ->
            check_spine ctx (infer_head ctx head) spine type_
        | Lam (x, e), Type.Arrow (a, b) ->
            check_term (Ctx.add x a ctx) e b
        | Lam _, Type.Atom _ ->
            failwith "Term.check: lambda term expected function type"

        and infer_head ctx = function
        | Var i -> Ctx.lookup i ctx
        | Con (c, type_) -> Sign.lookup_con c type_ sign

        and check_spine ctx a spine b : unit = match spine with
        | [] ->
           if a = b then () else failwith "check_spine"
        | e :: spine'->
            begin match a with
            | Type.Arrow (a0, a1) ->
                check_term ctx e a0;
                check_spine ctx a1 spine' b
            | Type.Atom _ ->
                failwith "atom elimiated"
            end

         in check_term

    open Printf
    let rec to_string ctx = function
        | App (head, spine) ->
            let head = head_to_string ctx head in
            let spine = List.map (arg_to_string ctx) spine in
            String.concat " " (head :: spine)
        | Lam (x, e) ->
            sprintf "\\%s. %s" x (to_string (Ctx.add x (Type.Atom "_") ctx) e)

    and head_to_string ctx = function
        | Var i ->
            Ctx.name i ctx
        | Con (name, None) ->
            name
        | Con (name, Some type_) ->
            sprintf "%s[%s]" name (Type.to_string type_)
    and arg_to_string ctx = function
        | App (head, []) ->
            head_to_string ctx head
        | e -> sprintf "(%s)" (to_string ctx e)
end
