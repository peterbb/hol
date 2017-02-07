open Ocamlbuild_plugin
open Command

let () = dispatch (function
    | After_rules ->
        ocaml_lib "core/core"
    | _ -> ()
)

