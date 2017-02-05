module Type : sig
    type t = 
        | Atom  of string
        | Arrow of t * t

    val to_string : t -> string
end = struct
    type t =
        | Atom   of string
        | Arrow  of t * t

    open Printf
    let rec to_string = function
        | Atom s -> s
        | Arrow (Atom s, b) -> sprintf "%s -> %s" s (to_string b)
        | Arrow (a, b) -> sprintf "(%s) -> %s" (to_string a) (to_string b)
end

module Con : sig
    type t = 
       | Single of string
       | Family of string * Type.t
    val simple : string -> t
    val indexed : string -> Type.t -> t
    val name : t -> string
    val index : t -> Type.t option
    val to_string : t -> string
end = struct
    type t =
        | Single of string
        | Family of string * Type.t

    let simple s = Single s
    let indexed s t = Family (s, t)

    let name = function
        | Single c | Family (c, _) -> c

    let index = function
        | Single _ -> None
        | Family (_, i) -> Some i

    let to_string = function
        | Single c -> c
        | Family (c, typ) ->
            Printf.sprintf "%s[%s]" c (Type.to_string typ)
end


module Term : sig
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of Con.t

    val eq : t -> t -> bool

    val lam : string -> t -> t
    val var : int -> t list -> t
    val con : Con.t -> t list -> t
    val redex : t -> t list -> t

    val to_string : t -> string
    val shift : t -> t
end = struct
    type t =
        | App   of head * t list
        | Lam   of string * t
    and head =
        | Var   of int
        | Con   of Con.t

    let eq x y = x = y

    let lam x body = Lam (x, body)

    let var x spine = App (Var x, spine)

    let con c spine = App (Con c, spine)

    (* [subst e lvl f] is:
     *
     *    G D : e      G * D : f
     * -------------------------------
     *          G D : subst e lvl f
     * where lvl = |G|.
     *)
    let rec subst e lvl = function
        (*            * G * D : f
         *           --------------
         *  G D : e   G * D : (Lam f)
         * ------------------------------
         *   G D : subst e lvl (Lam f)
         *)
        | Lam (x, body) ->
            (*     G D : e 
             *  -------------------
             *   * G D : (shift e)       * G * D : f
             *  --------------------------------------
             *   * G D : subst (shift e) (lvl + 1) f
             *  -----------------------------------------
             *   G D : Lam (subst (shift e) (lvl + 1) f)
             *)
            Lam (x, subst (shift e) (lvl + 1) body)

        (*
         *              ---------------
         *  G D : e       G * D : (Var lvl)
         * ---------------------------------
         *    G D : subst e lvl (Var lvl)
         *)
        | App (Var i, spine) when i = lvl ->
            (* 
             *  G D : e
             *)
            redex e (List.map (subst e lvl) spine)

        (*
         *   G D * D' : e    G * D * D' : Var (|D|+1+|D|)
         * ------------------------------------------------
         *      G D * D' : subst e lvl (Var |G|+1+|D|)
         *)
        | App (Var i, spine) when i > lvl ->
            (*
             *    G D * D' : Var (|G|+|D|)
             *)
            App (Var (i - 1), List.map (subst e lvl) spine)

        (*
        *   G * G' D : e        G * G' * D : Var |G|
        * ----------------------------------------------
        *     G * D' D : subst e lvl (Var |G|)
        *)
        | App (Var i, spine) ->
            (*
             * G * G' D : Var |G|
             *)
            App (Var i, List.map (subst e lvl) spine)
        | App (Con c, spine) ->
            App (Con c, List.map (subst e lvl) spine)

    and redex e spine = match e, spine with
        (* (x @ s) @ s'  ->   x @ (s @ s') *)
        | App (head, spine'), _ ->
            App (head, spine' @ spine)

        (* (\f) @ (e : s)  ->  (subst e 0 f) @ s *)
        | Lam (x, body), e' :: spine' ->
            redex (subst e' 0 body) spine'

        | Lam (x, body), [] ->
            Lam (x, body)
 
    and shift =
        let rec shift_term lvl = function
            | App (head, spine) ->
                App (shift_head lvl head, shift_spine lvl spine)
            (*
             *       * G D : e
             *    -------------
             *      G D : Lam e
             * ---------------------------
             *  G * D : shift lvl (Lam e)
             *)
            | Lam (x, e) ->
                (*
                 *     * G D : e
                 * -----------------------------
                 *   * G * D : shift (lvl+1) e
                 * ----------------------------
                 *   G * D : Lam (shift (lvl+1) e)
                 *)
                Lam (x, shift_term (1 + lvl) e)
        and shift_head lvl = function
            (*
             *       G * G' D : Var (i=G)
             *  ------------------------------------
             *    G * G' * D  : shift (G+1+G') (Var G)
             *)
            | Var i when i < lvl ->
                Var i
            | Var i ->
                Var (i + 1)
            | Con c ->
                Con c

        and shift_spine lvl = List.map (shift_term lvl)

        in shift_term 0

    open Printf
    let rec to_string = function
        | App (head, spine) ->
            let head = head_to_string head in
            let spine = List.map arg_to_string spine in
            String.concat " " (head :: spine)
        | Lam (x, e) ->
            sprintf "\\%s. %s" x (to_string e)

    and head_to_string = function
        | Var i ->
            sprintf "$%d" i
        | Con c ->
            sprintf "%s" (Con.to_string c)
    and arg_to_string = function
        | App (head, []) ->
            head_to_string head
        | e ->
            sprintf "(%s)" (to_string e)
end
