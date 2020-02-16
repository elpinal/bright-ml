open Std

fun fail s =
let val () = TextIO.output (TextIO.stdErr, "error: " ^ s ^ "\n") in
  OS.Process.exit OS.Process.failure
end

structure M = CLI struct
  val args = CommandLine.arguments ()
end

val () =
  case M.v of
       M.Help            => print M.usage
     | M.Version         => print "0.1.0\n"
     | M.Error e         => print (M.show_error e ^ "\n")
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
