local
  signature S = sig
    type var_info
    type location
    type var

    val map_location : (location -> location) -> var_info -> var_info
    val map_var : (var -> var) -> var_info -> var_info
  end

  functor MakeQuantified (X : S) :> sig
    type 'a t

    val from_body : 'a -> 'a t
    val quantify1 : X.var_info -> 'a -> 'a t
    val quantify : X.var_info list -> 'a -> 'a t
    val get_body : 'a t -> 'a
    val get_bound_vars : 'a t -> X.var_info list
    val count_bound_vars : 'a t -> int

    val rename_bound_vars : (X.var -> X.var) -> 'a t -> 'a t

    val map : ('a -> 'b) -> 'a t -> 'b t
    val map_with_location : ('a -> 'b) -> (X.location -> X.location) -> 'a t -> 'b t

    val merge : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

    val find_remove : (X.var_info -> bool) -> 'a t -> 'a t option
  end = struct
    open X

    type 'a t = var_info list * 'a

    fun from_body x = ([], x)
    fun quantify1 v x = ([v], x)
    fun quantify vs x = (vs, x)
    fun get_body (_, x) = x
    fun get_bound_vars (vs, _) = vs
    fun count_bound_vars (vs, _) = List.length vs

    fun rename_bound_vars f (vs, x) = (List.map (map_var f) vs, x)

    fun map f (vs, x) = (vs, f x)

    fun map_with_location f g (vs, x) =
      (List.map (map_location g) vs, f x)

    fun merge f (vs1, x) (vs2, y) = (vs1 @ vs2, f x y)

    fun find_remove p ([], x)      = NONE
      | find_remove p (v :: vs, x) =
          if p v
          then SOME(vs, x)
          else
            case find_remove p (vs, x) of
                 NONE        => NONE
               | SOME(ws, y) => SOME(v :: ws, y)
  end
in
  type var_info =
    { v : Internal.BoundID.t
    , k : Internal.kind
    , location : location
    }

  structure Quantified = MakeQuantified struct
    type var_info = var_info
    type location = location
    type var = Internal.BoundID.t

    fun map_location f {v, k, location} = {v = v, k = k, location = f location}
    fun map_var f {v, k, location} = {v = f v, k = k, location = location}
  end

  type 'a existential = 'a Quantified.t
  type 'a universal = 'a Quantified.t
end
