open Printf

open Type
open Term.Con
open Term

let rec type_to_string = function
    | Atom s -> s
    | Arrow (Atom s, b) ->
        sprintf "%s -> %s" s (type_to_string b)
    | Arrow (a, b) ->
        sprintf "(%s) -> %s" (type_to_string a) (type_to_string b)

let con_to_string = function
    | Single c -> c
    | Family (c, t) -> sprintf "%s[%s]" c (type_to_string t)

let rec term_to_string ctx = function
    | App (head, spine) ->
        let head = head_to_string ctx head in
        let spine = List.map (arg_to_string ctx) spine in
        String.concat " " (head :: spine)
    | Lam (x, e) ->
        let ctx = Typing.Ctx.add x (Atom "?") ctx in
        sprintf "\\%s. %s" x (term_to_string ctx e)

and head_to_string ctx = function
    | Var i ->
        Typing.Ctx.name i ctx
    | Con c ->
        sprintf "%s" (con_to_string c)
    | MVar m ->
        sprintf "?%s" m
and arg_to_string ctx = function
    | App (head, []) ->
        head_to_string ctx head
    | e ->
        sprintf "(%s)" (term_to_string ctx e)

