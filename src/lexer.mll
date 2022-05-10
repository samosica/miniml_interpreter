{
let reservedWords = [
  (* Keywords *)
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("in", Parser.IN);  
  ("let", Parser.LET);
  ("and", Parser.AND);
  ("fun", Parser.FUN);
  ("rec", Parser.REC);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("int", Parser.INT);
  ("bool", Parser.BOOL);
  ("list", Parser.LIST);
  ("type", Parser.TYPE);
  ("of", Parser.OF);
  ("ref", Parser.REF);
  ("unit", Parser.UNIT);
  ("land", Parser.LAND2);
  ("lsr", Parser.LSR);
  ("mod", Parser.MOD);
] 
}

rule main = parse
  (* ignore spacing and newline characters *)
  "\n" | "\r\n" { Lexing.new_line lexbuf; main lexbuf }
| [' ' '\009' '\012']+     { main lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "+" { Parser.PLUS }
| "*" { Parser.MULT }
| "<" { Parser.LT }
| "=" { Parser.EQ }
| "||" { Parser.LOR }
| "&&" { Parser.LAND }
| "->" { Parser.RARROW }
| "[" { Parser.LSBRACKET }
| "]" { Parser.RSBRACKET }
| "::" { Parser.APPEND }
| "|" { Parser.BAR }
| ";" { Parser.SEMI }
| "_" { Parser.UNDERSCORE }    
| ":" { Parser.COLON }
| "\'" { Parser.APOSTROPHE }
| "," { Parser.COMMA }
| ":=" { Parser.ASSN }
| "!" { Parser.DEREF }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try 
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
    }
| ['A'-'Z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf
      in Parser.CID id
    }
| "(*" { comment 1 lexbuf }
| eof { exit 0 }
and comment n = parse 
  "(*" { comment (n + 1) lexbuf }
| "*)" { if n > 1 then comment (n - 1) lexbuf else main lexbuf }    
| _ { comment n lexbuf }

