open Ast

module rec Theory : sig
    type t
    val init        : t
    val add_type    : string -> t -> t
    val add_con     : string -> Type.t -> t -> t
    val prove       : string -> Term.t -> t -> Proof.t
end 

and Goal : sig
    type tactic
    val assumption  : string -> tactic
    val cut         : Term.t -> string -> tactic
    val true_right  : tactic
    val false_left  : string -> tactic
    val and_right   : tactic
    val and_left    : string -> string -> string -> tactic
    val or_right_0  : tactic
    val or_right_1  : tactic
    val or_left     : string -> string -> string -> tactic
    val imp_right   : string -> tactic
    val imp_left    : string -> string -> tactic
    val all_right   : string -> tactic
    val all_left    : string -> Term.t -> string -> tactic
    val ex_right    : Term.t -> tactic
    val ex_left     : string -> string -> tactic

    val axiom       : tactic
end

and Proof : sig
    type t
    val apply   : Goal.tactic -> t -> t
    val qed     : t -> Theory.t
    val status  : t -> t
end



