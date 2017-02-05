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
    val check : TypeSign.t -> Ast.Type.t -> unit
end = struct
    open Ast.Type

    let check typeSig =
        let rec check = function
        | Atom x ->
            if TypeSign.defined x typeSig
            then ()
            else failwith "Type.check: atom not declared"
        | Arrow (a, b) ->
            check a; check b
        in check
end


module OpenType : sig
    type t = 
        | Hole
        | Atom  of string
        | Arrow of t * t

    val check : TypeSign.t -> t -> unit
    val fill : Ast.Type.t -> t -> Ast.Type.t
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
        | Atom x -> Ast.Type.Atom x
        | Arrow (a, b) -> Ast.Type.Arrow (fill a, fill b)
        in fill
end

module Sign : sig
    type t

    val empty      : t
    val add_type   : string -> t -> t
    val add_con    : string -> Ast.Type.t -> t -> t
    val add_icon   : string -> OpenType.t -> t -> t

    val check_type : t -> Ast.Type.t -> unit
    val lookup_con : Ast.Con.t -> t -> Ast.Type.t
end = struct
    type sort = 
        | Closed    of Ast.Type.t
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

    let lookup_con c {conSign} =
        match StringMap.find (Ast.Con.name c) conSign, (Ast.Con.index c) with
        | Closed a, None -> a
        | Open a, Some b -> OpenType.fill b a
        | Closed _, Some _ -> failwith "constant not parametric"
        | Open _, None  -> failwith "constant expect type parameter"
end

module Ctx : sig
    type t
    val empty : t
    val add : string -> Ast.Type.t -> t -> t
    val lookup : int -> t -> Ast.Type.t
    val name : int -> t -> string
    val is_empty : t -> bool
    val iter : (string -> Ast.Type.t -> unit) -> t -> unit
end = struct
    type t = (string * Ast.Type.t) list

    let empty = []
    let add var type_ ctx = (var, type_) :: ctx
    let lookup var ctx = snd (List.nth ctx var)
    let name var ctx = fst (List.nth ctx var)
    let is_empty ctx = ctx = []
    let iter f = List.iter (fun (x, y) -> f x y)
end


module Term : sig
    val check : Sign.t -> Ctx.t -> Ast.Term.t -> Ast.Type.t -> unit
end = struct
    open Ast.Term
    open Ast.Type
    let check sign =
        let rec check_term ctx term type_ : unit = match term, type_ with
        | App (head, spine), _ ->
            check_spine ctx (infer_head ctx head) spine type_
        | Lam (x, e), Arrow (a, b) ->
            check_term (Ctx.add x a ctx) e b
        | Lam _, Atom _ ->
            failwith "Term.check: lambda term expected function type"

        and infer_head ctx = function
        | Var i -> Ctx.lookup i ctx
        | Con c -> Sign.lookup_con c sign

        and check_spine ctx a spine b : unit = match spine with
        | [] ->
           if a = b then () else failwith "check_spine"
        | e :: spine'->
            begin match a with
            | Arrow (a0, a1) ->
                check_term ctx e a0;
                check_spine ctx a1 spine' b
            | Atom _ ->
                failwith "atom elimiated"
            end

         in check_term
end
