local
  signature IDENT = sig
    type t

    val eq : t * t -> bool
    val compare : t * t -> order

    structure Map : MAP where type key = t

    val from_string : string -> t
    val get_name : t -> string
  end

  functor Ident (X : sig end) :> IDENT = struct
    type t = string

    val eq = op=
    val compare = String.compare

    structure Map = BinarySearchMap struct
      type t = t

      val compare = compare
    end

    fun from_string s = s
    fun get_name s = s
  end
in
  structure ValID = Ident ()
  structure TypeID = Ident ()
  structure ModuleID = Ident ()
  structure SignatureID = Ident ()
  structure ConstrID = Ident ()

  type val_ident = ValID.t
  type type_ident = TypeID.t
  type module_ident = ModuleID.t
  type signature_ident = SignatureID.t
  type constr_ident = ConstrID.t

  type location = module_ident list * type_ident

  structure TypeVar :> sig
    type t

    val from_string : string -> t

    val compare : t * t -> order
    val get_name : t -> string
    val show : t -> string

    structure Map : MAP where type key = t
  end = struct
    type t = string

    fun from_string s = s

    val compare = String.compare
    fun get_name s = s
    fun show s = "'" ^ s

    structure Map = BinarySearchMap struct
      type t = t

      val compare = compare
    end
  end

  type type_var = TypeVar.t
  type type_vars = type_var list
end
