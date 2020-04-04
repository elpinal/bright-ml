signature U = sig
  type t
  type id
  type item
  exception Unbound of id

  val lookup : t -> id -> item
  val insert : t -> id -> item -> t
end

structure Env :> sig
  type t

  val initial : t

  val insert : t -> SS.Structure.t -> t

  val close : t -> IType.t -> IType.t

  signature U = U where type t = t

  structure Val : U
    where type id = val_ident
      and type item = SS.Term.t

  structure Type : U
    where type id = type_ident
      and type item = SS.Type.t

  structure Signature : U
    where type id = signature_ident
      and type item = SS.Signature.t

  structure Module : U
    where type id = module_ident
      and type item = SS.Module.t

  structure Constr : U
    where type id = constr_ident
      and type item = SS.Constr.t

  structure TypeVar : U
    where type id = type_var
      and type item = Internal.BoundID.t
end = struct
  local open SS in
    signature T = sig
      val v : Term.t ValID.Map.t
      val t : Type.t TypeID.Map.t
      val m : Module.t ModuleID.Map.t
      val s : Signature.t SignatureID.Map.t
      val c : Constr.t ConstrID.Map.t
    end

    signature S = sig
      include T

      val tv : Internal.BoundID.t TypeVar.Map.t
    end
  end

  type t = [S]

  val initial = [ structure struct
    structure Base = Internal.Base
    structure Kind = Internal.Kind
    val no_constrs = ConstrID.Map.empty
    fun make_base b = SS.Type.In(IType.base b, Base.kind_of b, no_constrs)
    val int = IType.base Base.Int
    val string = IType.base Base.String
    val unit = IType.base Base.Unit

    val m_order = ConstrID.Map.from_list
      [ (ConstrID.from_string "LT", (NONE, []))
      , (ConstrID.from_string "EQ", (NONE, []))
      , (ConstrID.from_string "GT", (NONE, []))
      ]
    val bid_order = Internal.BoundID.fresh_with_content Kind.base "order" (ref (SOME m_order))
    val m_order = ConstrID.Map.map (fn (x, y) => SS.Constr.In(x, bid_order, y)) m_order

    val v = ValID.Map.from_list $ map (fn (x, y) => (ValID.from_string x, SS.Term.In y))
      [ ("print_endline", IType.arrow string unit)
      , ("show_int", IType.arrow int string)
      , ("concat_string", IType.arrow string $ IType.arrow string string)
      , ("+", IType.arrow int $ IType.arrow int int)
      , ("-", IType.arrow int $ IType.arrow int int)
      , ("*", IType.arrow int $ IType.arrow int int)
      , ("compare_int", IType.arrow int $ IType.arrow int $ IType.bound bid_order)
      , ("compare_string", IType.arrow string $ IType.arrow string $ IType.bound bid_order)
      ]

    val t = TypeID.Map.from_list
      [ (TypeID.from_string "int", make_base Base.Int)
      , (TypeID.from_string "bool", make_base Base.Bool)
      , (TypeID.from_string "char", make_base Base.Char)
      , (TypeID.from_string "string", make_base Base.String)
      , (TypeID.from_string "unit", make_base Base.Unit)
      , (TypeID.from_string "list", make_base Base.List)

      , ( TypeID.from_string "order"
        , SS.Type.In(IType.bound bid_order, Internal.BoundID.get_kind bid_order, ConstrID.Map.map (fn _ => ()) m_order)
        )
      ]

    val m = ModuleID.Map.from_list
      [ ( ModuleID.from_string "MakeRef"
        , let
            structure BoundID = Internal.BoundID

            val bid1 = BoundID.fresh Kind.base "t"
            val bid2 = BoundID.fresh Kind.base "ref"

            val ty_item = IType.bound bid1
            val ty_ref = IType.bound bid2

            val s1 =
              SS.Structure.singleton_type (TypeID.from_string "t") $
                SS.Type.In(ty_item, BoundID.get_kind bid1, ConstrID.Map.empty)

            val s2 =
              SS.Structure.singleton_type (TypeID.from_string "t") $
                SS.Type.In(ty_ref, BoundID.get_kind bid2, ConstrID.Map.empty)
          in
            SS.Module.F $ Quantified.quantify1
              {v = bid1, k = BoundID.get_kind bid1, location = ([], TypeID.from_string "t")}
              ( SS.Module.S s1
              , Quantified.quantify1
                  {v = bid2, k = BoundID.get_kind bid1, location = ([], TypeID.from_string "t")}
                  $ SS.Module.S $ SS.Structure.merge s2 $
                    SS.Structure.values $ ValID.Map.from_list $
                      map (fn (x, y) => (ValID.from_string x, SS.Term.In y))
                      [ ("make", IType.arrow ty_item ty_ref)
                      , ("get", IType.arrow ty_ref ty_item)
                      , ("set", IType.arrow ty_ref $ IType.arrow ty_item unit)
                      ]
              )
          end
        )
      ]

    val s = SignatureID.Map.empty

    val c = ConstrID.Map.union m_order ConstrID.Map.empty

    val tv = TypeVar.Map.empty
  end as S ]

  fun insert env s =
  let
    structure M as S = env
    structure N as T = s
  in
    [ structure struct
        open M
        val v = ValID.Map.union v N.v
        val t = TypeID.Map.union t N.t
        val m = ModuleID.Map.union m N.m
        val s = SignatureID.Map.union s N.s
        val c = ConstrID.Map.union c N.c
      end as S
    ]
  end

  fun close env =
  let
    structure M as S = env
    val ftv = SS.Structure.ftv [ structure M as T ]

    structure C = IType.Close struct
      fun in_env fid =
        case Internal.FreeID.Map.lookup fid ftv of
             SOME _ => true
           | NONE   => false
    end
  in
    C.f
  end

  signature U = U where type t = t

  fun unwrap _ (SOME x) = x
    | unwrap e NONE     = raise e

  structure Val = struct
    type t = t
    type id = val_ident
    type item = SS.Term.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (ValID.Map.lookup id M.v)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val v = ValID.Map.insert id item v
        end as S
      ]
    end
  end

  structure Type = struct
    type t = t
    type id = type_ident
    type item = SS.Type.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (TypeID.Map.lookup id M.t)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val t = TypeID.Map.insert id item t
        end as S
      ]
    end
  end

  structure Signature = struct
    type t = t
    type id = signature_ident
    type item = SS.Signature.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (SignatureID.Map.lookup id M.s)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val s = SignatureID.Map.insert id item s
        end as S
      ]
    end
  end

  structure Module = struct
    type t = t
    type id = module_ident
    type item = SS.Module.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (ModuleID.Map.lookup id M.m)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val m = ModuleID.Map.insert id item m
        end as S
      ]
    end
  end

  structure Constr = struct
    type t = t
    type id = constr_ident
    type item = SS.Constr.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (ConstrID.Map.lookup id M.c)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val c = ConstrID.Map.insert id item c
        end as S
      ]
    end
  end

  structure TypeVar = struct
    type t = t
    type id = type_var
    type item = Internal.BoundID.t
    exception Unbound of id

    fun lookup env id =
    let structure M as S = env in
      unwrap (Unbound id) (TypeVar.Map.lookup id M.tv)
    end

    fun insert env id item =
    let structure M as S = env in
      [ structure struct
          open M
          val tv = TypeVar.Map.insert id item tv
        end as S
      ]
    end
  end
end

type env = Env.t
