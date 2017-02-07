module OpenType : sig
    type t = 
        | Hole
        | Atom  of string
        | Arrow of t * t

    val check : Type.Sign.t -> t -> unit
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
            if Type.Sign.defined x typeSig
            then ()
            else failwith "Type.check: atom not declared"
        | Arrow (a, b) ->
            check a; check b
        in check

    let fill t =
        let rec fill = function
        | Hole -> t
        | Atom x -> Type.Atom x
        | Arrow (a, b) -> Type.Arrow (fill a, fill b)
        in fill
end

module Ctx : sig
    type t
    val empty : t
    val add : string -> Type.t -> t -> t
    val lookup : int -> t -> Type.t
    val name : int -> t -> string
    val is_empty : t -> bool
    val iter : (string -> Type.t -> unit) -> t -> unit
    val names : t -> string list
end = struct
    type t = (string * Type.t) list

    let empty = []
    let add var type_ ctx = (var, type_) :: ctx
    let lookup var ctx =
        try snd (List.nth ctx var) with
        | Not_found -> failwith "Ctx.lookup: invalid deBruijn index"
    let name var ctx =
        try fst (List.nth ctx var) with
        | Not_found -> failwith "Ctx.name: invalid deBruijn index"
    let is_empty ctx = ctx = []
    let iter f = List.iter (fun (x, y) -> f x y)
    let names = List.map fst
end

module MCtx : sig
    type t
    val empty : t
    val add : string -> Type.t -> t -> t
    val lookup : string -> t -> Type.t
    val remove : string -> t -> t
    val is_empty : t -> bool
    val iter : (string -> Type.t -> unit) -> t -> unit
end = struct
    type t = Type.t StringMap.t
    let empty = StringMap.empty
    let add = StringMap.add_unique
    let lookup mvar mCtx = 
        try StringMap.find mvar mCtx with
        | Not_found -> failwith "MCtx.lookup: not defined"
    let remove = StringMap.remove
    let is_empty = StringMap.is_empty
    let iter = StringMap.iter
end

module Sign : sig
    type t

    val empty      : t
    val add_type   : string -> t -> t
    val add_con    : string -> Type.t -> t -> t
    val add_icon   : string -> OpenType.t -> t -> t

    val check_type : t -> Type.t -> unit
    val lookup_con : Ast.Con.t -> t -> Type.t
end = struct
    type sort = 
        | Closed    of Type.t
        | Open      of OpenType.t

    type t = {
         typeSign : Type.Sign.t ;
         conSign  : sort StringMap.t
    }

    let empty = {
        typeSign = Type.Sign.empty;
        conSign = StringMap.empty
    }

    let check_type {typeSign} t = Type.check typeSign t

    let add_type name ({typeSign} as sign) =
        let typeSign = Type.Sign.add name typeSign in
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
        | exception Not_found ->
            "Sign.lookup_con: not found:" ^ (Ast.Con.name c) |> failwith
end



module Term : sig
    val check : Sign.t -> MCtx.t -> Ctx.t
                -> Ast.Term.t -> Type.t -> unit
end = struct
    open Ast.Term
    let check sign mCtx =
        let rec check_term ctx term type_ : unit = match term, type_ with
        | App (head, spine), _ ->
            check_spine ctx (infer_head ctx head) spine type_
        | Lam (x, e), Type.Arrow (a, b) ->
            check_term (Ctx.add x a ctx) e b
        | Lam _, Type.Atom _ ->
            failwith "Term.check: lambda term expected function type"

        and infer_head ctx = function
        | Var i -> Ctx.lookup i ctx
        | Con c -> Sign.lookup_con c sign
        | MVar m -> MCtx.lookup m mCtx

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
end
