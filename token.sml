structure Token = struct
  (* Used to avoid reduce-reduce conflicts *)
  datatype left_paren_kind
    = Normal
    | DotInRight

  datatype t
    = LPAREN of left_paren_kind ref
    | RPAREN

    | LBRACE
    | RBRACE

    | LBRACK
    | RBRACK

    | LPAREN_PROJ

    | DOT

    | NUMBER of int
    | STRING of string
    | CHAR of char
    | LOWER_IDENT of string
    | UPPER_IDENT of string
    | QUOTE_IDENT of string
    | VAL_OP of string

    | EQUAL
    | COLON
    | COLON_GT
    | COLON_EQ
    | COLON_COLON
    | RARROW
    | BAR
    | UNDERSCORE
    | ASTERISK
    | COMMA
    | DOLLAR

    | PLUS
    | MINUS
    | GT
    | LT
    | GT_EQ
    | LT_EQ
    | GT_GT_GT
    | LT_LT_LT
    | EQUAL_EQUAL
    | SLASH_EQUAL
    | LT_GT
    | LT_PLUS_GT

    | SUBMODULE

    | STRUCT
    | SIG
    | VAL
    | TYPE
    | MODULE
    | SIGNATURE
    | INCLUDE
    | OPEN
    | WHERE
    | DATATYPE
    | OF
    | LET
    | IN
    | FUN
    | FUNCTION
    | FUNCTOR
    | IF
    | THEN
    | ELSE
    | FALSE
    | TRUE
    | MATCH
    | WITH
    | END
    | REC
    | AND
    | PACK
    | UNPACK

  fun show (LPAREN _) = "("
    | show RPAREN     = ")"
    | show LBRACE     = "{"
    | show RBRACE     = "}"
    | show LBRACK     = "["
    | show RBRACK     = "]"

    | show LPAREN_PROJ = "("

    | show DOT = "."

    | show (NUMBER n)      = Int.toString n
    | show (STRING s)      = String.toString s
    | show (CHAR c)        = Char.toString c
    | show (LOWER_IDENT s) = s
    | show (UPPER_IDENT s) = s
    | show (QUOTE_IDENT s) = "'" ^ s
    | show (VAL_OP s)      = "val" ^ s

    | show EQUAL       = "="
    | show COLON       = ":"
    | show COLON_GT    = ":>"
    | show COLON_EQ    = ":="
    | show COLON_COLON = "::"
    | show RARROW      = "->"
    | show BAR         = "|"
    | show UNDERSCORE  = "_"
    | show ASTERISK    = "*"
    | show COMMA       = ","
    | show DOLLAR      = "$"

    | show PLUS        = "+"
    | show MINUS       = "-"
    | show GT          = ">"
    | show LT          = "<"
    | show GT_EQ       = ">="
    | show LT_EQ       = "<="
    | show GT_GT_GT    = ">>>"
    | show LT_LT_LT    = "<<<"
    | show EQUAL_EQUAL = "=="
    | show SLASH_EQUAL = "/="
    | show LT_GT       = "<>"
    | show LT_PLUS_GT  = "<+>"

    | show SUBMODULE = "submodule"

    | show STRUCT    = "struct"
    | show SIG       = "sig"
    | show VAL       = "val"
    | show TYPE      = "type"
    | show MODULE    = "module"
    | show SIGNATURE = "signature"
    | show INCLUDE   = "include"
    | show OPEN      = "open"
    | show WHERE     = "where"
    | show DATATYPE  = "datatype"
    | show OF        = "of"
    | show LET       = "let"
    | show IN        = "in"
    | show FUN       = "fun"
    | show FUNCTION  = "function"
    | show FUNCTOR   = "functor"
    | show IF        = "if"
    | show THEN      = "then"
    | show ELSE      = "else"
    | show FALSE     = "false"
    | show TRUE      = "true"
    | show MATCH     = "match"
    | show WITH      = "with"
    | show END       = "end"
    | show REC       = "rec"
    | show AND       = "and"
    | show PACK      = "pack"
    | show UNPACK    = "unpack"
end
