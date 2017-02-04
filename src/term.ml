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
        | Redex of t * Type.t

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
        | Redex of t * Type.t

    let check sign =
         let rec check_term ctx term type_ = match term, type_ with
         | Lam (x, e), Type.Arrow (a, b) ->
             check_term (Ctx.add x a ctx) e b
         | Lam _, Type.Atom _ ->
             failwith "Term.check: lambda term expected function type"
         | App (h, es), _ ->
             if check_spine ctx (check_head ctx h) es = type_ then
                 ()
             else
                 failwith "type not correct"

         and check_head ctx = function
         | Var i ->
             Ctx.lookup i ctx
         | Con (c, ts) ->
             Sign.lookup_con c ts sign
         | Redex (e, t) ->
             Sign.check_type sign t;
             check_term ctx e t;
             t

         and check_spine ctx a ts = match ts with
         | [] -> a
         | t :: rest ->
             begin match a with
             | Type.Arrow (a0, a1) ->
                 check_term ctx t a0;
                 check_spine ctx a1 rest
             | Type.Atom _ ->
                 failwith "atom elimiated"
             end

         in check_term

    let shift =
        let rec shift_term lvl = function
            | Lam (x, e) ->
                Lam (x, shift_term (1 + lvl) e)
            | App (h, es) -> 
                App (shift_head lvl h, List.map (shift_term lvl) es)
        
        and shift_head lvl = function
            | Var i when i >= lvl -> Var (1 + i)
            | Var i -> Var i
            | Con (name, type_) -> Con (name, type_)
            | Redex (e, type_) -> Redex (shift_term lvl e, type_)
        in shift_term 0



    open Printf
    let rec to_string ctx = function
        | Lam (x, e) ->
            sprintf "\\%s. %s" x (to_string (Ctx.add x (Type.Atom "_") ctx) e)
        | App (head, spine) ->
            let head_string = head_to_string ctx head in
            let spine_strings = List.map (arg_to_string ctx) spine in 
            String.concat " " (head_string :: spine_strings)
    and head_to_string ctx = function
        | Var i ->
            Ctx.name i ctx
        | Con (name, None) ->
            name
        | Con (name, Some type_) ->
            sprintf "%s[%s]" name (Type.to_string type_)
        | Redex (e, type_) ->
            sprintf "(%s : %s)" (to_string ctx e) (Type.to_string type_)
    and arg_to_string ctx = function
        | App (e, []) -> head_to_string ctx e
        | e -> sprintf "(%s)" (to_string ctx e)
end
