open Term

type theory
type proof

val init : theory
val add_type : string -> theory -> theory
val add_con : string -> Type.t -> theory -> theory

val prove : string -> Term.t -> theory -> proof
val qed : proof -> theory

val proof_status : proof -> proof

val true_right : proof -> proof
val false_left : string -> proof -> proof

val and_right : proof -> proof
val and_left : string -> string -> string -> proof -> proof

val or_right_0 : proof -> proof
val or_right_1 : proof -> proof
val or_left    : string -> string -> string -> proof -> proof

val imp_right : string -> proof -> proof
val imp_left  : string -> string -> proof -> proof

val all_right : string -> proof -> proof

