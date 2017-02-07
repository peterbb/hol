

include Set.Make(String)


let add_unique elem set =
    if mem elem set
    then failwith "StringSet.add_unique: duplicate element"
    else add elem set
