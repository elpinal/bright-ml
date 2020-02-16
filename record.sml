structure Label :> sig
  type t

  val compare : t * t -> order

  val value : val_ident -> t
  val module : module_ident -> t

  val typ : type_ident -> t
  val signature_ : signature_ident -> t
  val constr : constr_ident -> t

  val encode : t -> string
end = struct
  structure Class = struct
    datatype t
      = V
      | M
      | T
      | S
      | C

    fun ord V = 0
      | ord M = 1
      | ord T = 2
      | ord S = 3
      | ord C = 4

    fun compare (x, y) = Int.compare (ord x, ord y)
  end

  datatype t
    = V of val_ident
    | M of module_ident
    | T of type_ident
    | S of signature_ident
    | C of constr_ident

  fun class (V _) = Class.V
    | class (M _) = Class.M
    | class (T _) = Class.T
    | class (S _) = Class.S
    | class (C _) = Class.C

  fun compare (x, y) =
    case (x, y) of
         (V x, V y) => ValID.compare (x, y)
       | (M x, M y) => ModuleID.compare (x, y)
       | _          => Class.compare (class x, class y)

  val value = V
  val module = M

  val typ = T
  val signature_ = S
  val constr = C

  fun encode (V id) = "V/" ^ ValID.get_name id
    | encode (M id) = "M/" ^ ModuleID.get_name id
    | encode _      = raise Fail "static components need not to be encoded"
end

type label = Label.t

structure Record = BinarySearchMap Label
