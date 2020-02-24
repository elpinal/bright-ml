open Std Result

structure BrightML : sig
  val parse_file : Filepath.relative -> Syntax.Unit.t result
  val elaborate : Filepath.relative -> Syntax.Unit.t -> Internal.term result
  val interpret : Internal.term -> unit
end = struct
  fun parse_file filepath =
    Right $ #1 $ Parser.parse $ Lexer.lex $ Stream.fromTextInstream $ TextIO.openIn $ Filepath.relative_to_string filepath
    handle
      ParserError.UnexpectedToken(SOME t) => Left("unexpected token: " ^ Token.show t)
    | ParserError.UnexpectedToken NONE    => Left "unexpected end of file"
    | LexerError.Illegal(SOME c)          => Left("illegal character: " ^ Char.toString c)

  fun elaborate filepath u =
  let
    (* val () = print $ Syntax.Unit.show u ^ "\n" *)
  in
    #2 <$> Semantics.Unit.elaborate Env.initial (filepath, parse_file) u
  end
    handle
      IType.StructuralMismatch(x, y) => Left("structural mismatch: " ^ IType.show x ^ " vs " ^ IType.show y)
    | Semantics.Pattern.NotExhaustive s => Left("not exhaustive: " ^ Space.show s)
    | Semantics.Pattern.Redundant(s, p) => Left("redundant pattern: " ^ Syntax.Pattern.show p ^ ": " ^ Space.show s)

  fun interpret t =
  (* let val () = print (Internal.Term.show t ^ "\n") in *)
    ignore (Dynamic.eval Dynamic.Env.initial $ Internal.Term.to_dynamic t)
  (* end *)
end

open BrightML
