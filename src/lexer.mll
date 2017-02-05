{ open Parser }

let letter = [ 'a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let diglet = digit | letter
let sym = '_' | '-'

let name = letter (sym | diglet)*

rule token = parse
    | [' ' '\t' '\n']+          { token lexbuf }
    | "->"                      { ARROW }
    | '('                       { LPAR }
    | ')'                       { RPAR }
    | '.'                       { DOT }
    | '\\'                      { BACKSLASH }
    | name                      { NAME (Lexing.lexeme lexbuf) }
    | eof                       { EOF }

