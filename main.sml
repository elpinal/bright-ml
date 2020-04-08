open Std

val version = "0.1.2"

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
             case flag of
                  M.None => interpret <$> elaborate path bs
                | M.Parse => Right ()
                | M.Typecheck => ignore <$> elaborate path bs) of
                Right _ => ()
              | Left s  => fail s
         end
