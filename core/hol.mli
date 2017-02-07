open Ast

module rec Theory : sig
    type t

    val init        : t
    val add_type    : string -> t -> t
    val add_con     : string -> Type.t -> t -> t
    val prove       : string -> Term.t -> t -> Proof.t

    type view = {
        sign     : Typing.Sign.t;
        theorems : Term.t StringMap.t
    }
    val view : t -> view
end 

and Goal : sig
    type t
    type view = {
        ctx  : Typing.Ctx.t;
        hyps : Term.t StringMap.t;
        goal : Term.t
    }
    val view : t -> view
end

and Proof : sig
    type t

    val apply    : Tactic.t -> t -> t
    val mvar     : string -> Type.t -> t -> t
    val set_mvar : string -> Term.t -> t -> t
    val qed      : t -> Theory.t

    type view = {
        mCtx : Typing.MCtx.t;
        goals : Goal.view list;
        name : string;
        result : Term.t;
        theory : Theory.view
    }
    val view : t -> view

    val status   : t -> t (* XXX: To be moved out of core. *)
end

and Tactic : sig
    type t

    val assumption  : string -> t
    val cut         : Term.t -> string -> t
    val true_right  : t
    val false_left  : string -> t
    val and_right   : t
    val and_left    : string -> string -> string -> t
    val or_right_0  : t
    val or_right_1  : t
    val or_left     : string -> string -> string -> t
    val imp_right   : string -> t
    val imp_left    : string -> string -> t
    val all_right   : string -> t
    val all_left    : string -> Term.t -> string -> t
    val ex_right    : Term.t -> t
    val ex_left     : string -> string -> t

    val axiom       : t
end

