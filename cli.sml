open Std

functor CLI (X : sig
  val args : string list
end) : sig
  type error

  datatype flag
    = None
    | Parse
    | Typecheck

  datatype t
    = Normal of string * flag
    | Help
    | Version
    | Error of error

  val v : t

  val show_error : error -> string
  val usage : string
end = struct
  datatype flag
    = None
    | Parse
    | Typecheck

  fun show_flag None = ""
    | show_flag Parse = "-parse"
    | show_flag Typecheck = "-typecheck"

  datatype error
    = UnrecognizedFlag of string
    | TooManyArguments of int
    | FlagConflict of flag * flag

  fun show_error (UnrecognizedFlag s) = "unrecognized flag: " ^ s
    | show_error (TooManyArguments n) = "too many arguments (" ^ Int.toString n ^ ")"
    | show_error (FlagConflict(x, y)) = "flag conflict: " ^ show_flag x ^ " vs " ^ show_flag y

  exception FlagConflict_ of flag * flag

  fun None <> flag = flag
    | flag <> None = flag
    | Parse <> Parse = Parse
    | Typecheck <> Typecheck = Typecheck
    | x <> y                 = raise FlagConflict_(x, y)

  datatype t
    = Normal of string * flag
    | Help
    | Version
    | Error of error

  val usage = String.concat $ map (fn s => s ^ "\n")
  [ "Bright ML"
  , "  bright-ml [options] filename"
  , ""
  , "options:"
  , "  -h"
  , "  -help"
  , "  --help"
  , "  -v"
  , "  -version"
  , "  -parse"
  , "  -typecheck"
  ]

  fun f args =
    case args of
         [] => Help
       | x :: xs =>
           case x of
                "-h" => Help
              | "-help" => Help
              | "--help" => Help
              | "-v" => Version
              | "-version" => Version
              | "-parse" =>
                  let in
                    case f xs of
                         Normal(s, flag) => Normal(s, flag <> Parse)
                       | v               => v
                  end
              | "-typecheck" =>
                  let in
                    case f xs of
                         Normal(s, flag) => Normal(s, flag <> Typecheck)
                       | v               => v
                  end
              | _ =>
                  case String.explode x of
                       #"-" :: flag => Error $ UnrecognizedFlag $ String.implode flag
                     | _            =>
                         case xs of
                              [] => Normal(x, None)
                            | _  => Error $ TooManyArguments $ List.length args

  val v = f X.args
    handle FlagConflict_(x, y) => Error $ FlagConflict(x, y)
end
