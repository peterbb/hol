include Map.Make(String)

let add_unique key elem map =
    if mem key map
    then failwith "StringMap.add_unique: duplicate key"
    else add key elem map
