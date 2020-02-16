structure Filepath :> sig
  type absolute
  type relative

  val absolute : string -> absolute
  val relative : string -> relative

  val eq : relative * relative -> bool

  val join : relative list -> relative
  val extend : absolute -> relative -> absolute

  val absolute_to_string : absolute -> string
  val relative_to_string : relative -> string

  val basename : relative -> relative
  val dir : relative -> relative

  val drop_ext : relative -> relative

  structure Map : MAP where type key = relative
end = struct
  structure P = OS.Path

  type absolute = string
  type relative = string

  fun absolute s = s
  fun relative s = s

  fun eq (x, y) = x = y

  fun join [] = ""
    | join (s :: ss) = foldl (fn (s, acc) => P.concat (acc, s)) s ss

  fun extend s1 s2 = P.concat (s1, s2)

  fun absolute_to_string s = s
  fun relative_to_string s = s

  fun basename s = P.file s
  fun dir s = P.dir s

  val drop_ext = P.base

  structure Map = BinarySearchMap struct
    type t = relative
    val compare = String.compare
  end
end
