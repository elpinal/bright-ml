open Std Result

structure BrightML : sig
  (* `true` means "no std", `false` means "std". *)
  type no_std = bool

  val parse_file : Filepath.relative -> Syntax.Unit.t result
  val elaborate : no_std -> Filepath.relative -> Syntax.Unit.t -> Internal.term result
  val interpret : Internal.term -> unit result
end = struct
  type no_std = bool

  fun parse_file filepath =
    Right $ #1 $ Parser.parse $ Lexer.lex $ Stream.fromTextInstream $ TextIO.openIn $ Filepath.relative_to_string filepath
    handle
      ParserError.UnexpectedToken(SOME t) => Left("unexpected token: " ^ Token.show t)
    | ParserError.UnexpectedToken NONE    => Left "unexpected end of file"
    | LexerError.Illegal(SOME c)          => Left("illegal character: " ^ Char.toString c)

  fun elaborate no_std filepath u =
  let
    (* val () = print $ Syntax.Unit.show u ^ "\n" *)
  in
    #2 <$> Semantics.Unit.elaborate Env.initial (filepath, parse_file) (if no_std then u else Syntax.Unit.add_std u)
  end
    handle
      IType.StructuralMismatch(x, y)    => Left("structural mismatch: " ^ IType.show x ^ " vs " ^ IType.show y)
    | Semantics.Pattern.NotExhaustive s => Left("not exhaustive: " ^ Space.show s)
    | Semantics.Pattern.Redundant(s, p) => Left("redundant pattern: " ^ Syntax.Pattern.show p ^ ": " ^ Space.show s)
    | Semantics.Unit.UndefinedBMLPath   => Left("environment variable '$BML_PATH' needs to be set to load the standard library")

  fun interpret t =
  (* let val () = print (Internal.Term.show t ^ "\n") in *)
    Right $ ignore (Dynamic.eval Dynamic.Env.initial $ Internal.Term.to_dynamic t)
    handle
      Dynamic.Panic msg => Left("panicked: " ^ msg)
  (* end *)
end

open BrightML
