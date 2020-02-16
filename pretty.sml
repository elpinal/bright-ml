infix 4 <>
infix 4 <+>

structure Pretty :> sig
  type t = string

  val op<> : t * t -> t
  val op<+> : t * t -> t

  val paren : bool -> t -> t
  val brace : t -> t
  val bracket : t -> t

  (* Without parentheses *)
  val list : ('a -> t) -> 'a list -> t
end = struct
  type t = string

  fun x <> y = x ^ y
  fun x <+> y = x <> " " <> y

  fun paren true s  = "(" <> s <> ")"
    | paren false s = s

  fun brace s = "{" <> s <> "}"

  fun bracket s = "[" <> s <> "]"

  fun non_empty f x []        = f x
    | non_empty f x [y]       = f x <> "," <+> f y
    | non_empty f x (y :: zs) = f x <> "," <+> non_empty f y zs

  fun list f []        = ""
    | list f (x :: xs) = non_empty f x xs
end
