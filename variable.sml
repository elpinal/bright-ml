signature ID = sig
  type t
  type kind
  type 'a content

  val fresh : kind -> string -> t
  val refresh : t -> t
  val fresh_with_content : kind -> string -> t content -> t

  val eq : t * t -> bool
  val compare : t * t -> order
  val get_kind : t -> kind
  val get_name : t -> string
  val get_content : t -> t content

  val set_content : t -> t content -> t

  val show : t -> string

  structure Map : MAP where type key = t
end

local
  signature Arg = sig
    type kind

    type 'a content
    val default : unit -> 'a content
  end
in
  functor ID X : Arg :> ID where type kind = X.kind and type 'a content = 'a X.content = struct
    type kind = X.kind
    type 'a content = 'a X.content

    datatype t = In of int * kind * string * t content

    val r = ref 0

    fun fresh' k s c =
    let
      val n = !r
      val () = r := n + 1
    in
      In(n, k, s, c)
    end

    fun fresh k s = fresh' k s (X.default ())

    fun refresh (In(_, k, s, c)) = fresh' k s c

    fun fresh_with_content k s c = fresh' k s c

    fun eq (In x, In y) = #1 x = #1 y

    fun compare (In x, In y) = Int.compare (#1 x, #1 y)

    fun get_kind (In x) = #2 x
    fun get_name (In x) = #3 x
    fun get_content (In x) = #4 x

    fun set_content (In(n, k, s, _)) c = In(n, k, s, c)

    fun show (In(n, _, s, _)) = s ^ "[" ^ Int.toString n ^ "]"

    structure Map = BinarySearchMap struct
      type t = t

      val compare = compare
    end
  end

  functor Var X : sig type free_id type bound_id end = struct
    datatype 'a free
      = Defined of 'a
      | Undefined of X.free_id

    datatype 'a t
      = Bound of X.bound_id
      | Free of 'a free ref
  end
end
