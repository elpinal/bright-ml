open Std

structure Decompose : sig
  val decompose : IType.t -> IType.t option ConstrID.Map.t option
end = struct
  fun decompose ty =
  let
    structure M = IType.Decompose struct
      fun lookup_bid bid =
        case !(Internal.BoundID.get_content bid) of
             SOME m => SOME $ ConstrID.Map.map (fn (ty_opt, bids) => Option.map (fn ty => (ty, bids)) ty_opt) m
           | NONE   => NONE
    end
  in
    M.f ty
  end
end

structure Space :> sig
  type t

  type ty = IType.t
  type c = constr_ident

  datatype u
    = Type of ty
    | Union of t list
    | Constr of c * t option
    | Tuple of t list

  val prj : t -> u

  val empty : t
  val typ : ty -> t
  val union : t list -> t
  val constr : c -> t option -> t
  val tuple : t list -> t

  val is_empty : t -> bool

  val sub : t -> t -> t
  val subspace : t -> t -> bool

  val pattern : ty Syntax.Pattern.t -> t

  val show : t -> string
end = struct
  type ty = IType.t
  type c = constr_ident

  datatype u
    = Type of ty
    | Union of t list
    | Constr of c * t option
    | Tuple of t list

  withtype t = u

  fun prj x = x

  val empty = Union []
  val typ = Type
  val union = Union
  fun constr c x = Constr(c, x)
  val tuple = Tuple

  infix mplus

  fun NONE mplus x     = x
    | (SOME x) mplus _ = SOME x

  fun dec ty =
    case Decompose.decompose ty of
         NONE   => Option.map (Tuple o map Type) (IType.try_get_tuple ty)
                   mplus
                   Option.map (fn ty' => (Union
                          [ constr (ConstrID.from_string "[]") NONE
                          , constr (ConstrID.from_string "::") $ SOME $ Tuple [Type ty', Type ty]
                          ])) (IType.try_get_list ty)
       | SOME m =>
           let fun f acc c s = Constr(c, s) :: acc in
             ConstrID.Map.map (Option.map Type) m
             |> ConstrID.Map.fold_left f []
             |> Union
             |> SOME
           end

  fun is_empty acc (Union ss) = List.all (is_empty acc) ss
    | is_empty acc (Type ty)  =
        let in
          if List.exists (IType.equal_base ty) acc
          then false
          else
            case dec ty of
                 NONE   => false
               | SOME s =>
                   let val acc = ty :: acc in
                     is_empty acc s
                   end
        end
    | is_empty acc (Constr(c, p)) =
        let in
          case p of
               NONE   => false
             | SOME p => is_empty acc p
        end
    | is_empty acc (Tuple ss) = List.exists (is_empty acc) ss

  val is_empty = is_empty []

  fun zip [] []               = []
    | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
    | zip _ _                 = []

  fun sub z =
  let
    fun (Union ss) - x = Union(List.map (fn s => s - x) ss)
      | x - (Union ss) = List.foldl (fn (s, acc) => acc - s) x ss
      | (x as Constr(c1, s1)) - (Constr(c2, s2)) =
          if ConstrID.eq (c1, c2)
          then
            let in
              case (s1, s2) of
                   (NONE, NONE) => empty
                 | (SOME s1, SOME s2) =>
                     if subspace s1 s2
                     then empty
                     else if is_empty $ intersection s1 s2
                     then x
                     else Constr(c1, SOME(s1 - s2))
                 | _ => raise Unreachable
            end
          else
            x
      | (Type ty1) - (Type ty2) = empty (* Assume both have the same type. *)
          (* if IType.subtype_of ty1 ty2 *)
          (* then empty *)
          (* else Type ty1 *)
      | (Constr _) - (Type _) = empty (* Assume both have the same type. *)
      | (Tuple _) - (Type _) = empty (* Assume both have the same type. *)
      | (Type ty) - (y as Constr _) =
          let in
            case dec ty of
                 NONE      => Type ty
               | SOME s_ty => s_ty - y
          end
      | (Type ty) - (y as Tuple _) =
          let in
            case dec ty of
                 NONE      => Type ty
               | SOME s_ty => s_ty - y
          end
      | (Tuple ss1) - (Tuple ss2) =
          let
            val xs = zip ss1 ss2
          in
            if List.all (fn (x, y) => subspace x y) xs
            then empty
            else if List.exists (fn (x, y) => is_empty $ intersection x y) xs
            then Tuple ss1
            else Union $ #2 $
              foldl (fn (s, (i, acc)) => (i + 1, Tuple(List.take (ss1, i) @ [List.nth (ss1, i) - s] @ List.drop (ss1, i + 1)) :: acc)) (0, []) ss2
          end
      | (x as Constr _) - (Tuple _) = x
      | (x as Tuple _) - (Constr _) = x

    and subspace x y = is_empty (x - y)

    fun f x y = x - y
  in
    f z
  end

  and intersection (Type ty) (Type _) = Type ty
    | intersection (Type _) (y as Constr _) = y
    | intersection (x as Constr _) (Type _) = x
    | intersection (Type _) (y as Tuple _) = y
    | intersection (x as Tuple _) (Type _) = x
    | intersection (Union ss) y = Union $ map (fn x => intersection x y) ss
    | intersection x (Union ss) = Union $ map (intersection x) ss
    | intersection (Constr(c1, x)) (Constr(c2, y)) =
        if ConstrID.eq (c1, c2)
        then
          case (x, y) of
               (NONE, NONE) => Constr(c1, NONE)
             | (SOME x, SOME y) => Constr(c1, SOME $ intersection x y)
             | _                => raise Unreachable
        else empty
    | intersection (Tuple ss1) (Tuple ss2) = Tuple $ map (fn (x, y) => intersection x y) $ zip ss1 ss2
    | intersection (Tuple _) (Constr _) = raise Unreachable
    | intersection (Constr _) (Tuple _) = raise Unreachable

  fun subspace x y = is_empty $ sub x y

  val pattern =
  let
    open Syntax.Pattern

    fun get_ident (Syntax.Path.Ident id)    = id
      | get_ident (Syntax.Path.Proj(_, id)) = id

    fun loop (Wildcard ty)       = Type ty
      | loop (Var(_, ty))        = Type ty
      | loop (Constructor(c, p)) = constr (get_ident c) (Option.map loop p)
      | loop (Typed(p, _))       = loop p
      | loop (Tuple ps)          = tuple (map loop ps)
      | loop NilList             = constr (ConstrID.from_string "[]") NONE
      | loop (ConsList(x, y))    = constr (ConstrID.from_string "::") (SOME (loop (Tuple [x, y])))
  in
    loop
  end

  fun paren s = "(" ^ s ^ ")"

  fun show_tuple [] = ""
    | show_tuple [s] = s
    | show_tuple [s1, s2] = s1 ^ ", " ^ s2
    | show_tuple (s :: ss) = s ^ ", " ^ show_tuple ss

  fun show (Type ty)      = "type" ^ paren (IType.show ty)
    | show (Union ss)     = "union(" ^ List.foldl (fn (s, acc) => show s ^ ", " ^ acc) "" ss ^ ")"
    | show (Constr(c, s)) = "constructor" ^ paren (ConstrID.get_name c ^
      (case s of
           NONE => ""
         | SOME s => ", " ^ show s))
    | show (Tuple ss) = "tuple" ^ paren (show_tuple (map show ss))
end
