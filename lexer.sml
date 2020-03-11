structure LexerError = struct
  exception Illegal of char option
  exception LeadingZero of string
  exception UnexpectedEOFAfterDot
  exception UnexpectedSpaceAfterDot
  exception UnexpectedSpaceBeforeDot
  exception NonTerminatingString
  exception NonTerminatingChar
  exception NonTerminatingBackquoteIdent
  exception IllegalEscapeSequence of char
  exception EOFAfterSingleQuote
  exception Expected of char * char option
  exception IllegalInBackquote of char
  exception EmptyBackquoteIdent
end

functor Lexer (X : sig end) = MakeLexer (struct
  structure Streamable = StreamStreamable
  structure Arg = struct
    type symbol = char
    val ord = Char.ord

    datatype t = datatype Token.t
    type t = t Streamable.t

    type self = { lex : symbol Streamable.t -> t }
    type info = { match : symbol list,
                  len : int,
                  start : symbol Streamable.t,
                  follow : symbol Streamable.t,
                  self : self }

    val left_paren_kind_stack = ref []

    open LexerError

    val ASCII_DIGIT_START = 48

    fun parse_digit_in_char (c : char) = Char.ord c - ASCII_DIGIT_START

    fun parse_num (xs : char list) =
    let
      fun f (c, acc) = parse_digit_in_char c + 10 * acc
    in
      List.foldl f 0 xs
    end

    fun parse_string' (acc : char list) (s : char Streamable.t) : string * char Streamable.t =
      case Stream.front s of
           Stream.Nil => raise NonTerminatingString
         | Stream.Cons(x, s) =>
             case x of
                  #"\"" => (String.implode acc, s)
                | #"\\" => parse_escape_sequence acc s
                | _     => parse_string' (acc @ [x]) s

    and parse_escape_sequence acc s =
      case Stream.front s of
           Stream.Nil => raise NonTerminatingString
         | Stream.Cons(x, s) =>
             case x of
                  #"\"" => parse_string' (acc @ [x]) s
                | #"n"  => parse_string' (acc @ [#"\n"]) s
                | #"t"  => parse_string' (acc @ [#"\t"]) s
                | _     => raise IllegalEscapeSequence(x)

    val parse_string = parse_string' []

    fun expect_read ch s =
      case Stream.front s of
           Stream.Nil => raise Expected(ch, NONE)
         | Stream.Cons(x, s) =>
             if x = ch
             then s
             else raise Expected(ch, SOME x)

    fun is_ident c = Char.isAlphaNum c orelse c = #"_"

    fun parse_quote_ident acc s =
      case Stream.front s of
           Stream.Nil => (QUOTE_IDENT(String.implode acc), s)
         | Stream.Cons(x, s') =>
             if is_ident x
             then parse_quote_ident (acc @ [x]) s'
             else (QUOTE_IDENT(String.implode acc), s)

    fun parse_char_or_quote_ident s =
      case Stream.front s of
           Stream.Nil => raise EOFAfterSingleQuote
         | Stream.Cons(x, s) =>
             case x of
                  #"\\" => parse_escape_sequence_char s
                | _     =>
                    case Stream.front s of
                         Stream.Nil =>
                            if Char.isLower x
                            then (QUOTE_IDENT(Char.toString x), s)
                            else raise NonTerminatingChar
                       | Stream.Cons(y, s') =>
                           case y of
                                #"'" => (CHAR(x), s')
                              | _    =>
                                  if Char.isLower x
                                  then parse_quote_ident [x] s
                                  else raise NonTerminatingChar

    and parse_escape_sequence_char s =
      case Stream.front s of
           Stream.Nil => raise NonTerminatingChar
         | Stream.Cons(x, s) =>
             case x of
                  #"'"  => (CHAR(x), expect_read #"'" s)
                | #"n"  => (CHAR(#"\n"), expect_read #"'" s)
                | #"t"  => (CHAR(#"\t"), expect_read #"'" s)
                | _     => raise IllegalEscapeSequence(x)

    fun is_allowed_in_backquote c =
      is_ident c orelse
      Char.contains "<>+-=/!?*" c

    fun parse_backquote_ident' acc s =
      case Stream.front s of
           Stream.Nil => raise NonTerminatingBackquoteIdent
         | Stream.Cons(x, s) =>
             case x of
                  #"`" => (acc, s)
                | _    =>
                    if is_allowed_in_backquote x
                    then parse_backquote_ident' (acc @ [x]) s
                    else raise IllegalInBackquote(x)

    fun parse_backquote_ident s =
    let val (cs, s) = parse_backquote_ident' [] s in
      if List.null cs
      then raise EmptyBackquoteIdent
      else (String.implode cs, s)
    end

    fun skip_until_newline s =
      case Stream.front s of
           Stream.Nil => s
         | Stream.Cons(x, s') =>
             case x of
                  #"\n" => s'
                | _     => skip_until_newline s'

    fun eager_follow ({self, follow, ...} : info) tok =
    let open Stream in
      eager (Cons(tok, #lex self follow))
    end

    fun stream_head s =
      case Stream.front s of
           Stream.Nil        => NONE
         | Stream.Cons(x, _) => SOME(x)

    fun illegal ({follow, ...} : info) = raise Illegal(stream_head follow)
    fun eof _ = Stream.fromList []

    fun leading_zero ({match, ...} : info) = raise LeadingZero(String.implode match)

    fun lparen info =
    let
      val r = ref Token.Normal
      val () = left_paren_kind_stack := r :: (!left_paren_kind_stack)
    in
      eager_follow info (LPAREN r)
    end

    fun rparen info =
    let
      val () =
        case !left_paren_kind_stack of
             []      => raise Std.Unreachable
           | r :: rs =>
               let val () = left_paren_kind_stack := rs in
                 case stream_head (#follow info) of
                      SOME(#".") => r := Token.DotInRight
                    | _          => ()
               end
    in
      eager_follow info RPAREN
    end

    fun lbrace info = eager_follow info LBRACE
    fun rbrace info = eager_follow info RBRACE

    fun lbrack info = eager_follow info LBRACK
    fun rbrack info = eager_follow info RBRACK

    fun bar info = eager_follow info BAR
    fun underscore info = eager_follow info UNDERSCORE
    fun asterisk info = eager_follow info ASTERISK
    fun comma info = eager_follow info COMMA
    fun dollar info = eager_follow info DOLLAR
    fun equal info = eager_follow info EQUAL
    fun colon info = eager_follow info COLON
    fun colon_gt info = eager_follow info COLON_GT
    fun colon_eq info = eager_follow info COLON_EQ
    fun colon_colon info = eager_follow info COLON_COLON
    fun rarrow info = eager_follow info RARROW

    fun plus info     = eager_follow info PLUS
    fun minus info    = eager_follow info MINUS
    fun gt info       = eager_follow info GT
    fun lt info       = eager_follow info LT
    fun gt_eq info    = eager_follow info GT_EQ
    fun lt_eq info    = eager_follow info LT_EQ
    fun gt_gt_gt info = eager_follow info GT_GT_GT
    fun lt_lt_lt info = eager_follow info LT_LT_LT
    fun equal_equal info = eager_follow info EQUAL_EQUAL
    fun slash_equal info = eager_follow info SLASH_EQUAL
    fun lt_gt info       = eager_follow info LT_GT
    fun lt_plus_gt info  = eager_follow info LT_PLUS_GT

    fun dot info =
    let
      val () =
        case stream_head (#follow info) of
             NONE => raise UnexpectedEOFAfterDot
           | SOME(c) =>
               if Char.isSpace c
               then raise UnexpectedSpaceAfterDot
               else ()
    in
      eager_follow info DOT
    end

    fun whitespace ({self, follow, ...} : info) =
    let
      val () =
        case stream_head follow of
             SOME(#".") => raise UnexpectedSpaceBeforeDot
           | _          => ()
    in
      #lex self follow
    end

    fun comment ({self, follow, ...} : info) =
    let
      val next_line = skip_until_newline follow
    in
      #lex self next_line
    end

    fun number ({match, self, follow, ...} : info) =
      Stream.lazy (fn () => Stream.Cons(NUMBER(parse_num match), #lex self follow))

    fun string ({match, self, follow, ...} : info) =
    let val (s, rest) = parse_string follow in
      Stream.lazy (fn () => Stream.Cons(STRING s, #lex self rest))
    end

    fun lower_ident ({match, self, follow, ...} : info) =
    let
      exception E
      fun f s =
        case s of
             "struct"     => STRUCT
           | "sig"        => SIG
           | "val"        => VAL
           | "type"       => TYPE
           | "module"     => MODULE
           | "signature"  => SIGNATURE
           | "include"    => INCLUDE
           | "open"       => OPEN
           | "where"      => WHERE
           | "datatype"   => DATATYPE
           | "of"         => OF
           | "let"        => LET
           | "in"         => IN
           | "fun"        => FUN
           | "function"   => FUNCTION
           | "functor"    => FUNCTOR
           | "if"         => IF
           | "then"       => THEN
           | "else"       => ELSE
           | "false"      => FALSE
           | "true"       => TRUE
           | "match"      => MATCH
           | "with"       => WITH
           | "end"        => END
           | "rec"        => REC
           | "and"        => AND
           | "pack"       => PACK
           | "unpack"     => UNPACK
           | "submodule"  => SUBMODULE
           | _            => LOWER_IDENT(s)
    in
      Stream.lazy (fn () => Stream.Cons(f (String.implode match), #lex self follow))
    end

    fun upper_ident ({match, self, follow, ...} : info) =
      Stream.lazy (fn () => Stream.Cons(UPPER_IDENT(String.implode match), #lex self follow))

    fun raw_ident ({match, self, follow, ...} : info) =
      Stream.lazy (fn () => Stream.Cons(LOWER_IDENT(String.implode (List.drop (match, 2))), #lex self follow))

    fun single_quote ({match, self, follow, ...} : info) =
    let val (tok, rest) = parse_char_or_quote_ident follow in
      Stream.lazy (fn () => Stream.Cons(tok, #lex self rest))
    end

    fun backquote_ident ({match, self, follow, ...} : info) =
    let val (s, rest) = parse_backquote_ident follow in
      Stream.lazy (fn () => Stream.Cons(LOWER_IDENT s, #lex self rest))
    end

    fun val_op ({match, self, follow, ...} : info) =
      Stream.lazy (fn () => Stream.Cons(VAL_OP(String.implode $ List.drop (match, 3)), #lex self follow))
  end
end)

structure Lexer : sig
  val lex : char Stream.stream -> Token.t Stream.stream
end = struct
  open Token
  fun f (LPAREN r) =
        let in
          case !r of
               DotInRight => LPAREN_PROJ
             | _          => LPAREN r
        end
    | f t = t

  fun lex s =
  let
    structure L = Lexer struct end
  in
    Stream.fromList (List.map f (Stream.toList (L.lex s)))
  end
end
