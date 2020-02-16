infix <$>
infix >>=

structure Result : sig
  datatype 'a t
    = Left of string
    | Right of 'a

  val op<$> : ('a -> 'b) * 'a t -> 'b t
  val op>>= : 'a t * ('a -> 'b t) -> 'b t
end = struct
  datatype 'a t
    = Left of string
    | Right of 'a

  fun f <$> (Left s)  = Left s
    | f <$> (Right t) = Right (f t)

  fun (Left s) >>= f  = Left s
    | (Right t) >>= f = f t
end

type 'a result = 'a Result.t
