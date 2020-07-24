open Std

val version = "0.1.4"

fun fail s =
let val () = TextIO.output (TextIO.stdErr, "error: " ^ s ^ "\n") in
  OS.Process.exit OS.Process.failure
end

structure M = CLI struct
  val args = CommandLine.arguments ()
end

fun print_endline s = print $ s ^ "\n"

val () =
  case M.v of
       M.Help            => print M.usage
     | M.Version         => print_endline $ "Bright ML version " ^ version
     | M.Error e         => print_endline $ M.show_error e
     | M.Normal(s, flag) =>
         let val path = Filepath.relative s in
           case parse_file path >>= (fn bs =>
             let
               val (no_std, f) =
                 case flag of
                      M.Std f   => (false, f)
                    | M.NoStd f => (true, f)
             in
               case f of
                 M.None => elaborate no_std path bs >>= interpret
               | M.Parse => Right ()
               | M.Typecheck => ignore <$> elaborate no_std path bs
             end) of
                Right _ => ()
              | Left s  => fail s
         end
