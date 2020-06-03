structure Internal :> rec (X : sig
  structure Type : sig
    type t
  end
end) sig
  structure Kind : sig
    eqtype t

    exception Mismatch of t * t

    exception NotBase of t
    exception NotArrow of t

    val base : t
    val arrow : t -> t -> t

    val get_base : t -> unit
    val get_arrow : t -> t * t

    val from_nat : nat -> t
  end

  type kind = Kind.t

  structure BoundID : ID where type kind = kind and type 'a content = (X.Type.t option * 'a list) ConstrID.Map.t option ref
  structure FreeID : ID where type kind = kind

  structure Base : sig
    type t

    val Int : t
    val Bool : t
    val Char : t
    val String : t
    val Unit : t
    val List : t

    val kind_of : t -> kind
  end

  structure Type : sig
    type t

    exception StructuralMismatch of t * t

    val free : FreeID.t -> t
    val bound : BoundID.t -> t
    val forall : BoundID.t list -> t -> t
    val exist : BoundID.t list -> t -> t
    val base : Base.t -> t
    val arrow : t -> t -> t
    val abs : BoundID.t -> t -> t
    val app : t -> t -> t
    val tuple : t list -> t
    val record : t Record.t -> t
    val list : t -> t

    val get_bound_var : t -> BoundID.t
    val get_bool : t -> unit

    val try_get_tuple : t -> t list option
    val try_get_list : t -> t option

    val show : t -> string

    val subst : t BoundID.Map.t -> t -> t
    val reduce : t -> t
    val equal : t -> t -> kind -> unit

    val equal_base : t -> t -> bool

    exception Contain of BoundID.t
    val not_contain : unit BoundID.Map.t -> t -> unit

    val instantiate : t -> t
    val is_instance_of : t -> t -> unit
    val ftv : t -> unit FreeID.Map.t
    val unify : t -> t -> unit

    functor Close (X : sig
      val in_env : FreeID.t -> bool
    end) : sig
      val f : t -> t
    end

    type arg = t * BoundID.t list

    functor Decompose (X : sig
      val lookup_bid : BoundID.t -> arg option ConstrID.Map.t option
    end) : sig
      val f : t -> t option ConstrID.Map.t option
    end
  end

  structure ValVar : sig
    type t

    val fresh : unit -> t
    val from_label : label -> t
  end

  structure Term : sig
    type t
    type branch = Syntax.Pattern.untyped * t
    type branches = branch list

    val var : ValVar.t -> t
    val record : t Record.t -> t
    val tuple : t list -> t
    val proj : t -> label -> t
    val lit : Syntax.Literal.t -> t
    val abs : ValVar.t -> t -> t
    val app : t -> t -> t
    val let_ : ValVar.t -> t -> t -> t
    val list : t list -> t
    val cons_list : t -> t -> t
    val if_ : t -> t -> t -> t
    val constr : constr_ident -> t
    val match : t -> branches -> t
    val letrec : (ValVar.t * t) list -> t -> t

    val show : t -> string
    val to_dynamic : t -> Dynamic.t
  end

  type term = Term.t
end = struct
  structure Kind = struct
    datatype t
      = @^
      | Arrow of t * t

    exception Mismatch of t * t

    exception NotBase of t
    exception NotArrow of t

    val base = @^
    fun arrow x y = Arrow(x, y)

    fun get_base @^ = ()
      | get_base k  = raise NotBase(k)

    fun get_arrow (Arrow x) = x
      | get_arrow k         = raise NotArrow(k)

    fun from_nat n =
      case Nat.proj n of
           Nat.Zero   => @^
         | Nat.Succ n => Arrow(@^, from_nat n)
  end

  type kind = Kind.t

  structure Base = struct
    (* Base types does not contain `BoundID.t`. *)
    (* Base types does not necessarily have the base kind. *)
    datatype t
      = Int
      | Bool
      | Char
      | String
      | Unit
      | List

    fun kind_of Int    = Kind.base
      | kind_of Bool   = Kind.base
      | kind_of Char   = Kind.base
      | kind_of String = Kind.base
      | kind_of Unit   = Kind.base
      | kind_of List   = Kind.arrow Kind.base Kind.base

    fun show Int    = "int"
      | show Bool   = "bool"
      | show Char   = "char"
      | show String = "string"
      | show Unit   = "unit"
      | show List   = "list"
  end

  type base = Base.t

  structure FreeID = ID struct
    type kind = kind

    type 'a content = unit
    fun default () = ()
  end

  fun zip [] []               = []
    | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
    | zip _ _                 = []

  structure Type = struct
    datatype t
      = Var of (t, bound_id) vt
      | Abs of bound_id * kind * t
      | App of t * t
      | Arrow of t * t
      | Forall of bound_id * kind * t
      | Exist of bound_id * kind * t
      | Record of t Record.t
      | Tuple of t list
      | Base of Base.t

    withtype bound_id = BoundID.t where BoundID = ID struct
      type kind = kind

      type 'a content = (t option * 'a list) ConstrID.Map.t option ref
      fun default () = ref NONE
    end

    and ('a, 'bound_id) vt = 'a V.t
      where V = Var struct type free_id = FreeID.t type bound_id = 'bound_id end

    structure V = Var struct type free_id = FreeID.t type bound_id = bound_id end

    structure BoundID = ID struct
      type kind = kind

      type 'a content = (t option * 'a list) ConstrID.Map.t option ref
      fun default () = ref NONE
    end

    fun free fid = Var(V.Free(ref (V.Undefined fid)))
    fun bound bid = Var(V.Bound bid)

    fun forall bids x = List.foldl (fn (bid, acc) => Forall(bid, BoundID.get_kind bid, acc)) x bids

    fun exist bids x = List.foldl (fn (bid, acc) => Exist(bid, BoundID.get_kind bid, acc)) x bids

    val base = Base

    fun arrow x y = Arrow(x, y)

    fun abs bid x = Abs(bid, BoundID.get_kind bid, x)

    fun app x y = App(x, y)

    fun tuple xs = Tuple xs

    fun record m = Record m

    fun list ty = app (Base Base.List) ty

    fun unwrap_or def NONE   = def
      | unwrap_or _ (SOME x) = x

    fun subst bid_map ty =
    let
      open Std V
      val loop = subst bid_map
    in
      case ty of
           Var v =>
             let in
               case v of
                    Bound bid => BoundID.Map.lookup bid bid_map |> unwrap_or ty
                  | Free fv   =>
                      case !fv of
                           Defined x   => loop x
                         | Undefined _ => ty
             end
         | Abs(bid, k, x)    => Abs(bid, k, subst (BoundID.Map.delete bid bid_map) x)
         | App(x, y)         => App(loop x, loop y)
         | Arrow(x, y)       => Arrow(loop x, loop y)
         | Forall(bid, k, x) => Forall(bid, k, subst (BoundID.Map.delete bid bid_map) x)
         | Exist(bid, k, x)  => Exist(bid, k, subst (BoundID.Map.delete bid bid_map) x)
         | Record m          => Record $ Record.map loop m
         | Tuple xs          => Tuple $ map loop xs
         | Base b            => Base b
    end

    local open V in
      fun reduce (App(x, y))          = reduce' (reduce x) y
        | reduce (v as Var (Free fv)) =
            let in
              case !fv of
                   Defined ty  => reduce ty
                 | Undefined _ => v
            end
        | reduce ty = ty

      and reduce' (Abs(bid, _, ty1)) ty2   = reduce (subst (BoundID.Map.singleton bid ty2) ty1)
        | reduce' (v as Var (Free fv)) ty2 =
            let in
              case !fv of
                   Defined ty  => reduce' ty ty2
                 | Undefined _ => App(v, ty2)
            end
        | reduce' ty1 ty2 = App(ty1, ty2)
    end

    exception NotBoundVar        of t
    exception NotBool            of t
    exception BaseMismatch       of base * base
    exception KindMismatch       of kind * kind
    exception VarMismatch        of t V.t * t V.t
    exception StructuralMismatch of t * t
    exception NotArrowKind       of kind
    exception MissingR           of label
    exception MissingL           of label

    fun get_bound_var ty =
      case reduce ty of
           Var(V.Bound bid) => bid
         | _                => raise NotBoundVar(ty)

    fun get_bool ty =
      case reduce ty of
           Base Base.Bool => ()
         | _              => raise NotBool(ty)

    fun try_get_tuple ty =
      case reduce ty of
           Tuple tys => SOME tys
         | _         => NONE

    fun try_get_list ty =
      case reduce ty of
           App(Base Base.List, ty) => SOME ty
         | _                       => NONE

    local
      open Std V
      fun paren s = "(" ^ s ^ ")"
    in
      fun show (Var v)       = show_var v
        | show (Abs _)       = "lambda"
        | show (App(x, y))   = paren $ show x ^ " " ^ show y
        | show (Arrow(x, y)) = paren $ show x ^ " -> " ^ show y
        | show (Forall _)    = "forall"
        | show (Exist _)     = "exist"
        | show (Record _)    = "record"
        | show (Tuple b)     = "tuple"
        | show (Base b)      = Base.show b

      and show_var (Bound bid) = BoundID.show bid
        | show_var (Free fv) =
            case !fv of
                 Defined ty => show ty
               | Undefined fid => FreeID.show fid
    end

    fun equal ty1 ty2 k =
    let
      open Kind
    in
      case k of
           @^            => ignore (str_equiv (reduce ty1) (reduce ty2))
         | Arrow(k1, k2) =>
             let
               open Std V
               val v = free $ FreeID.fresh k1 "?equal"
             in
               equal (App(ty1, v)) (App(ty2, v)) k2
             end
    end

    and str_equiv ty1 ty2 =
      case (ty1, ty2) of
           (Base b1, Base b2) =>
             if b1 = b2
             then Base.kind_of b1
             else raise BaseMismatch(b1, b2)
         | (App(x1, y1), App(x2, y2)) =>
             let in
               case str_equiv x1 x2 of
                    Kind.@^            => raise NotArrowKind(Kind.@^)
                  | Kind.Arrow(k1, k2) => k2 before equal y1 y2 k1
             end
         | (Arrow(x1, y1), Arrow(x2, y2)) =>
             Kind.@^
             before equal x1 x2 Kind.@^
             before equal y1 y2 Kind.@^
         | (Forall(v1, k1, x), Forall(v2, k2, y)) =>
             if k1 = k2
             then Kind.@^ before equal x y Kind.@^ (* TODO: perhaps wrong *)
             else raise KindMismatch(k1, k2)
         | (Exist(v1, k1, x), Exist(v2, k2, y)) =>
             if k1 = k2
             then Kind.@^ before equal x y Kind.@^ (* TODO: perhaps wrong *)
             else raise KindMismatch(k1, k2)
         | (Record m1, Record m2) =>
             let
               fun f k ty1 =
                 case Record.lookup k m2 of
                      SOME ty2 => equal ty1 ty2 Kind.@^
                    | NONE     => raise MissingR(k)

               fun g k _ =
                 case Record.lookup k m1 of
                      SOME _ => ()
                    | NONE   => raise MissingL(k)
             in
               Kind.@^ before Record.app_with_key f m1 before Record.app_with_key g m2
             end
         | (Tuple xs, Tuple ys) =>
             let
               val () =
                 if List.length xs = List.length ys
                 then ()
                 else raise StructuralMismatch(ty1, ty2)
             in
               Kind.@^ before List.app (fn (x, y) => equal x y Kind.@^) (zip xs ys)
             end
         | (Var v1, Var v2) =>
             let
               open V

               val (b, k) =
                 case (v1, v2) of
                      (Bound id1, Bound id2) => (BoundID.eq (id1, id2), BoundID.get_kind id1)
                    | (Free fv1, Free fv2)   =>
                        let in
                          case (!fv1, !fv2) of
                            (Undefined id1, Undefined id2) =>
                              (FreeID.eq (id1, id2), FreeID.get_kind id1)
                          | _ => raise VarMismatch(v1, v2)
                        end
                    | _ => raise VarMismatch(v1, v2)
             in
               if b
               then k
               else raise VarMismatch(v1, v2)
             end
         | _ =>
             raise StructuralMismatch(ty1, ty2)

    fun equal_base x y =
      true before equal x y Kind.base
      handle _ => false

    fun is_some (SOME _) = true
      | is_some NONE     = false

    exception Contain of BoundID.t

    fun not_contain bid_set ty =
    let
      open Std V
      val loop = not_contain bid_set
    in
      case ty of
           Var(Bound bid) =>
             if is_some $ BoundID.Map.lookup bid bid_set
             then raise Contain(bid)
             else ()
         | Var(Free fv) =>
             let in
               case !fv of
                    Defined x   => loop x
                  | Undefined _ => ()
             end
         | Abs(bid, _, x)    => not_contain (BoundID.Map.delete bid bid_set) x
         | App(x, y)         => loop x before loop y
         | Arrow(x, y)       => loop x before loop y
         | Forall(bid, _, x) => not_contain (BoundID.Map.delete bid bid_set) x
         | Exist(bid, _, x)  => not_contain (BoundID.Map.delete bid bid_set) x
         | Record m          => Record.app loop m
         | Tuple xs          => List.app loop xs
         | Base b            => ()
    end

    fun instantiate bid_map (Forall(bid, k, x)) =
          instantiate (BoundID.Map.insert bid (free (FreeID.fresh k "?inst")) bid_map) x
      | instantiate bid_map ty = subst bid_map ty

    val instantiate = instantiate BoundID.Map.empty

    (* Assume `ty1` and `ty2` are weak-head normal forms. *)
    fun aux bid_map_ref ty1 ty2 =
      case (ty1, ty2) of
           (_, Var(v2 as V.Bound bid2)) =>
             let in
               case BoundID.Map.lookup bid2 (!bid_map_ref) of
                    SOME(SOME x) => aux bid_map_ref ty1 x
                  | SOME NONE    => bid_map_ref := BoundID.Map.insert bid2 (SOME ty1) (!bid_map_ref)
                  | NONE         =>
                      case ty1 of
                           Var(v1 as V.Bound bid1) =>
                             if BoundID.eq (bid1, bid2)
                             then ()
                             else raise VarMismatch(v1, v2)
                         | _ => raise StructuralMismatch(ty1, ty2)
             end
         | (_, Var(v2 as V.Free fv)) =>
             let in
               case !fv of
                    V.Defined _   => raise Std.Unreachable
                  | V.Undefined fid2 =>
                      let in
                        case ty1 of
                             Var(v1 as V.Free fv) =>
                               let in
                                 case !fv of
                                      V.Undefined fid1 =>
                                        if FreeID.eq (fid1, fid2)
                                        then ()
                                        else raise VarMismatch(v1, v2)
                                    | V.Defined _ => raise Std.Unreachable
                               end
                           | _ => raise StructuralMismatch(ty1, ty2)
                      end
             end
         | (Abs(_, _, x), Abs(bid2, _, y)) =>
             let
               val z = BoundID.Map.lookup bid2 (!bid_map_ref)
               val () = bid_map_ref := BoundID.Map.delete bid2 (!bid_map_ref)
               val () = loop bid_map_ref x y
               val () = bid_map_ref := BoundID.Map.alter bid2 (fn _ => z) (!bid_map_ref)
             in
               ()
             end
         | (App(x1, y1), App(x2, y2)) =>
             loop bid_map_ref x1 x2
             before loop bid_map_ref y1 y2
         | (Arrow(x1, y1), Arrow(x2, y2)) =>
             loop bid_map_ref x1 x2
             before loop bid_map_ref y1 y2
         | (Forall(_, _, x), Forall(bid2, _, y)) =>
             let
               val z = BoundID.Map.lookup bid2 (!bid_map_ref)
               val () = bid_map_ref := BoundID.Map.delete bid2 (!bid_map_ref)
               val () = loop bid_map_ref x y
               val () = bid_map_ref := BoundID.Map.alter bid2 (fn _ => z) (!bid_map_ref)
             in
               ()
             end
         | (Exist(_, _, x), Exist(bid2, _, y)) =>
             let
               val z = BoundID.Map.lookup bid2 (!bid_map_ref)
               val () = bid_map_ref := BoundID.Map.delete bid2 (!bid_map_ref)
               val () = loop bid_map_ref x y
               val () = bid_map_ref := BoundID.Map.alter bid2 (fn _ => z) (!bid_map_ref)
             in
               ()
             end
         | (Record m1, Record m2) =>
             let
               fun f k ty1 =
                 case Record.lookup k m2 of
                      SOME ty2 => loop bid_map_ref ty1 ty2
                    | NONE     => raise MissingR(k)

               fun g k _ =
                 case Record.lookup k m1 of
                      SOME _ => ()
                    | NONE   => raise MissingL(k)
             in
               Record.app_with_key f m1
               before Record.app_with_key g m2
             end
         | (Tuple xs, Tuple ys) =>
             if List.length xs = List.length ys
             then List.app (fn (x, y) => loop bid_map_ref x y) (zip xs ys)
             else raise StructuralMismatch(ty1, ty2)
         | (Base b1, Base b2) => if b1 = b2 then () else raise BaseMismatch(b1, b2)
         | _                  => raise StructuralMismatch(ty1, ty2)

    and loop bid_map_ref ty1 ty2 = aux bid_map_ref (reduce ty1) (reduce ty2)

    fun is_instance_of bid_map ty1 (Forall(bid, _, ty2)) =
          is_instance_of (BoundID.Map.insert bid NONE bid_map) ty1 ty2
      | is_instance_of bid_map ty1 ty2 =
          if true before equal ty1 ty2 Kind.@^
            handle _ => false
          then ()
          else aux (ref bid_map) (reduce (instantiate ty1)) (reduce ty2)

    fun is_instance_of' x y = is_instance_of BoundID.Map.empty x y
    val is_instance_of = is_instance_of'

    local
      open V
      val empty = FreeID.Map.empty
      fun x <> y = FreeID.Map.union x y
    in
      fun ftv_var (Bound _) = empty
        | ftv_var (Free fv) =
            case !fv of
                 Defined ty    => ftv ty
               | Undefined fid => FreeID.Map.singleton fid ()

      and ftv (Var v)           = ftv_var v
        | ftv (Abs(_, _, x))    = ftv x
        | ftv (App(x, y))       = ftv x <> ftv y
        | ftv (Arrow(x, y))     = ftv x <> ftv y
        | ftv (Forall(_, _, x)) = ftv x
        | ftv (Exist(_, _, x))  = ftv x
        | ftv (Record m)        = Record.fold_left (fn acc => fn _ => fn x => acc <> ftv x) empty m
        | ftv (Tuple xs)        = List.foldl (fn (x, acc) => acc <> ftv x) empty xs
        | ftv (Base _)          = empty
    end

    exception RecursiveType of FreeID.t * t

    fun unify_var fv fid ty =
    let val fids = ftv ty in
      case FreeID.Map.lookup fid fids of
           SOME() => raise RecursiveType(fid, ty)
         | NONE   => fv := V.Defined ty
    end

    (* Assume both have the base kind and are weak-head normal forms. *)
    fun unify_aux x y =
      if true before equal x y Kind.base handle _ => false
      then ()
      else
        case (x, y) of
             (Var(V.Free fv1), _) =>
               let in
                 case !fv1 of
                      V.Defined _      => raise Std.Unreachable
                    | V.Undefined fid1 => unify_var fv1 fid1 y
               end
           | (_, Var(V.Free fv2)) =>
               let in
                 case !fv2 of
                      V.Defined _      => raise Std.Unreachable
                    | V.Undefined fid2 => unify_var fv2 fid2 x
               end
           | (Abs(bid1, k1, x), Abs(bid2, k2, y)) =>
               if k1 = k2
               then unify x y (* TODO: perhaps wrong *)
               else raise Kind.Mismatch(k1, k2)
           | (App(x1, y1), App(x2, y2)) => unify x1 x2 before unify y1 y2
           | (Arrow(x1, y1), Arrow(x2, y2)) => unify x1 x2 before unify y1 y2
           | (Forall(bid1, k1, x), Forall(bid2, k2, y)) =>
               if k1 = k2
               then unify x y (* TODO: perhaps wrong *)
               else raise Kind.Mismatch(k1, k2)
           | (Exist(bid1, k1, x), Exist(bid2, k2, y)) =>
               if k1 = k2
               then unify x y (* TODO: perhaps wrong *)
               else raise Kind.Mismatch(k1, k2)
           | (Record m1, Record m2) =>
               let
                 fun f k ty1 =
                   case Record.lookup k m2 of
                        SOME ty2 => unify ty1 ty2
                      | NONE     => raise MissingR(k)

                 fun g k _ =
                   case Record.lookup k m1 of
                        SOME _ => ()
                      | NONE   => raise MissingL(k)
               in
                 Record.app_with_key f m1;
                 Record.app_with_key g m2
               end
           | (Tuple xs, Tuple ys) =>
               if List.length xs = List.length ys
               then List.app (fn (x, y) => unify x y) (zip xs ys)
               else raise StructuralMismatch(x, y)
           | _                => raise StructuralMismatch(x, y)

    and unify x y = unify_aux (reduce x) (reduce y)

    functor Close (X : sig
      val in_env : FreeID.t -> bool
    end) = struct
      open Std V

      fun close_var _ (Bound bid)      = Var $ Bound bid
        | close_var bids_ref (Free fv) =
            case !fv of
                 Defined ty    => close bids_ref ty
               | Undefined fid =>
                   if X.in_env fid
                   then Var $ Free fv
                   else
                     let
                       val bid = BoundID.fresh (FreeID.get_kind fid) $ FreeID.get_name fid
                       val ty = bound bid
                     in
                       ty
                       before fv := Defined ty
                       before bids_ref := bid :: (!bids_ref)
                     end

      and close bids_ref ty =
      let
        val loop = close bids_ref
      in
        case ty of
             Var v             => close_var bids_ref v
           | Abs(bid, k, x)    => Abs(bid, k, loop x)
           | App(x, y)         => App(loop x, loop y)
           | Arrow(x, y)       => Arrow(loop x, loop y)
           | Forall(bid, k, x) => Forall(bid, k, loop x)
           | Exist(bid, k, x)  => Exist(bid, k, loop x)
           | Record m          => Record $ Record.map loop m
           | Tuple xs          => Tuple $ map loop xs
           | Base b            => Base b
      end

      fun f ty =
      let
        val bids = ref []
        val ty = close bids ty
      in
        forall (!bids) ty
      end
    end

    type arg = t * BoundID.t list

    functor Decompose (X : sig
      val lookup_bid : BoundID.t -> arg option ConstrID.Map.t option
    end) : sig
      val f : t -> t option ConstrID.Map.t option
    end = struct
      open Std V

      fun decompose_var (Bound bid) = Option.map (fn m => (m, [])) $ X.lookup_bid bid
        | decompose_var (Free fv) =
            case !fv of
                 Defined   _ => raise Unreachable
               | Undefined _ => NONE

      fun decompose (Var v)     = decompose_var v
        | decompose (Abs _)     = NONE
        | decompose (App(x, y)) = Option.map (fn (m, tys) => (m, tys @ [y])) $ decompose x
        | decompose (Arrow _)   = NONE
        | decompose (Forall _)  = NONE
        | decompose (Exist _)   = NONE
        | decompose (Record _)  = NONE
        | decompose (Tuple _)   = NONE
        | decompose (Base _)    = NONE

      fun g ty = decompose $ reduce ty

      fun h (m, tys) = m
        |> ConstrID.Map.map (Option.map (fn (ty, bids) =>
            let val bid_map = zip bids tys |> BoundID.Map.from_list in
              subst bid_map ty
            end))

      fun f ty = g ty |> Option.map h
    end
  end

  structure BoundID = Type.BoundID

  structure ValVar = struct
    datatype t
      = L of label
      | O of int

    val r = ref 0

    fun fresh () = O (!r) before r := !r + 1

    fun from_label l = L l

    fun encode (L l) = Label.encode l
      | encode (O n) = "O/" ^ Int.toString n
  end

  structure Term = struct
    type var = ValVar.t

    datatype t
      = Var of ValVar.t
      | Abs of var * t
      | App of t * t
      | Record of t Record.t
      | Tuple of t list
      | Proj of t * label
      | Let of ValVar.t * t * t
      | Lit of Syntax.Literal.t
      | List of t list
      | ConsList of t * t
      | If of t * t * t
      | Constructor of constr_ident
      | Match of t * branches
      | LetRec of (ValVar.t * t) list * t

    withtype branch = Syntax.Pattern.untyped * t
    and branches = (Syntax.Pattern.untyped * t) list

    val var = Var
    val record = Record
    val tuple = Tuple
    fun proj x l = Proj(x, l)
    val lit = Lit
    fun abs x y = Abs(x, y)
    fun app x y = App(x, y)
    fun let_ v x y = Let(v, x, y)
    val list = List
    fun cons_list x y = ConsList(x, y)
    fun if_ x y z = If(x, y, z)
    val constr = Constructor
    fun match x bs = Match(x, bs)
    fun letrec xs x = LetRec(xs, x)

    local open Std Pretty in
      fun show (Var v)     = ValVar.encode v
        | show (Abs(v, x)) = paren true $ "lambda" <+> ValVar.encode v <> "." <+> show x
        | show (App(x, y)) = paren true $ show x <+> show y
        | show (Record m)  = brace $ Pretty.list (fn (l, x) => Label.encode l <+> ":" <+> show x) $ Record.to_list m
        | show (Tuple xs)  = paren true $ Pretty.list show xs
        | show (Proj(x, l)) = show x <> "." <> Label.encode l
        | show (Let(v, x, y)) = paren true $ "let" <+> ValVar.encode v <+> "=" <+> show x <+> "in" <+> show y
        | show (Lit l)     = Syntax.Literal.show l
        | show (List xs)   = bracket $ Pretty.list show xs
        | show (ConsList(x, y)) = paren true $ show x <+> "::" <+> show y
        | show (If(x, y, z)) = paren true $ "if" <+> show x <+> "then" <+> show y <+> "else" <+> show z
        | show (Constructor id) = ConstrID.get_name id
        | show (Match(x, bs))   = "match" <+> show x <+> "with" <+> show_branches bs <+> "end"
        | show (LetRec(xs, x))  = paren true $ "letrec" <+> Pretty.list (fn (v, x) => ValVar.encode v <+> "=" <+> show x) xs <+> "in" <+> show x

      and show_branches bs = Pretty.list (fn (p, x) => "|" <+> Syntax.Pattern.show p <+> "->" <+> show x) bs
    end

    local open Std in
      structure P = struct
        open Syntax.Pattern
        structure DP = Dynamic.Pattern

        fun get_ident (Syntax.Path.Ident id)    = id
          | get_ident (Syntax.Path.Proj(_, id)) = id

        fun to_dynamic (Wildcard())            = DP.Wildcard
          | to_dynamic (Var(id, ()))           = DP.Var $ Label.encode $ Label.value id
          | to_dynamic (Constructor(p, p_opt)) = DP.Constructor(get_ident p, Option.map to_dynamic p_opt)
          | to_dynamic (Typed(x, _))           = to_dynamic x
          | to_dynamic (Tuple xs)              = DP.Tuple $ map to_dynamic xs
          | to_dynamic NilList                 = DP.Constructor(ConstrID.from_string "[]", NONE)
          | to_dynamic (ConsList(x, y))        =
              DP.Constructor(ConstrID.from_string "::", SOME $ to_dynamic $ Tuple [x, y])
      end

      fun to_dynamic (Var v)          = Dynamic.Var $ ValVar.encode v
        | to_dynamic (Abs(v, x))      = Dynamic.Abs(ValVar.encode v, to_dynamic x)
        | to_dynamic (App(x, y))      = Dynamic.App(to_dynamic x, to_dynamic y)
        | to_dynamic (Record m)       = Dynamic.Record $ Record.map to_dynamic m
        | to_dynamic (Tuple xs)       = Dynamic.Tuple $ map to_dynamic xs
        | to_dynamic (Proj(x, l))     = Dynamic.Proj(to_dynamic x, l)
        | to_dynamic (Let(v, x, y))   = Dynamic.Let(ValVar.encode v, to_dynamic x, to_dynamic y)
        | to_dynamic (Lit l)          = Dynamic.Lit l
        | to_dynamic (List xs)        = Dynamic.List $ map to_dynamic xs
        | to_dynamic (ConsList(x, y)) = Dynamic.ConsList(to_dynamic x, to_dynamic y)
        | to_dynamic (If(x, y, z))    = Dynamic.If(to_dynamic x, to_dynamic y, to_dynamic z)
        | to_dynamic (Constructor id) = Dynamic.Constructor id
        | to_dynamic (Match(x, bs))   = Dynamic.Match(to_dynamic x, map (fn (p, t) => (P.to_dynamic p, to_dynamic t)) bs)
        | to_dynamic (LetRec(xs, y))  = Dynamic.LetRec(map (fn (v, x) => (ValVar.encode v, to_dynamic x)) xs, to_dynamic y)
    end
  end

  type term = Term.t
end

structure IType = Internal.Type
structure Term = Internal.Term
