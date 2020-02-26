open Std

signature SEMANTICS = sig
  structure Literal : sig
    val elaborate : Syntax.Literal.t -> Internal.Base.t
  end

  structure Pattern : sig
    val exhaustivity_check : IType.t Syntax.Pattern.t list -> IType.t -> unit
    val elaborate : env -> Syntax.Pattern.untyped -> IType.t * IType.t ValID.Map.t * IType.t Syntax.Pattern.t
  end

  structure Expr : sig
    val elaborate_branch : env -> Syntax.Expr.branch -> IType.t * IType.t * IType.t Syntax.Pattern.t list * Term.branches
    val elaborate_branches : env -> Syntax.Expr.branches -> IType.t * IType.t * IType.t Syntax.Pattern.t list * Term.branches
    val elaborate : env -> Syntax.Expr.t -> IType.t * Term.t
  end

  structure Type : sig
    val elaborate : env -> Syntax.Type.t -> IType.t * Internal.kind
  end

  structure Decl : sig
    val elaborate : env -> Syntax.Decl.t -> SS.Structure.t existential
  end

  structure Signature : sig
    val elaborate_decls : env -> Syntax.Signature.decls -> SS.Structure.t existential
    val elaborate : env -> Syntax.Signature.t -> SS.Module.abstract
  end

  structure Binding : sig
    val elaborate : env -> Syntax.Binding.t -> SS.Structure.t existential * Term.t
  end

  structure Module : sig
    val elaborate_bindings : env -> Syntax.Module.bindings -> SS.Structure.t existential * Term.t
    val elaborate : env -> Syntax.Module.t -> SS.Module.abstract * Term.t
  end

  structure Unit : sig
    val elaborate : env -> Filepath.relative * (Filepath.relative -> Syntax.Unit.t result) -> Syntax.Unit.t -> (SS.Structure.t existential * Term.t) result
  end

  functor Path (Y : sig
    type id
    type item
    type dynamic

    val env_lookup : env -> id -> item
    val dynamic : Term.t option -> id -> dynamic
    val proj : SS.Structure.t -> id -> item
    val not_contain : unit Internal.BoundID.Map.t -> item -> unit
  end) : sig
    val elaborate : env -> Y.id Syntax.Path.t -> Y.item * Y.dynamic
  end
end

structure Semantics = rec (X : SEMANTICS) struct
  structure BoundID = Internal.BoundID
  structure FreeID = Internal.FreeID

  structure Kind = Internal.Kind
  structure ValVar = Internal.ValVar

  signature S = sig
    val v : SS.Term.t ValID.Map.t
    val t : SS.Type.t TypeID.Map.t
    val m : SS.Module.t ModuleID.Map.t
    val s : SS.Signature.t SignatureID.Map.t
    val c : SS.Constr.t ConstrID.Map.t
  end

  structure Literal = struct
    open Syntax.Literal

    fun elaborate (Int _)    = Internal.Base.Int
      | elaborate (Bool _)   = Internal.Base.Bool
      | elaborate (Char _)   = Internal.Base.Char
      | elaborate (String _) = Internal.Base.String
      | elaborate Unit       = Internal.Base.Unit
  end

  structure Pattern = struct
    open Syntax.Pattern

    exception Redundant of Space.t * IType.t Syntax.Pattern.t
    exception NotExhaustive of Space.t

    fun exhaustivity_check ps ty =
    let
      val ss = List.map (fn p => (Space.pattern p, p)) ps

      fun f ((s, p), acc) =
      let val b = Space.sub s (Space.union acc) in
        if Space.is_empty b
        then raise Redundant(s, p)
        else s :: acc
      end

      val _ = List.foldl f [] ss
      val s = Space.union (List.map #1 ss)

      val s_ty = Space.typ ty
      val remain = Space.sub s_ty s
    in
      if Space.is_empty remain
      then ()
      else raise NotExhaustive(remain)
    end

    exception ArityMismatch

    fun elaborate env (Wildcard()) =
          let val ty = IType.free $ FreeID.fresh Kind.base "?wildcard" in
            (ty, ValID.Map.empty, Wildcard ty)
          end
      | elaborate env (Var(id, ())) =
          let val ty = IType.free $ FreeID.fresh Kind.base "?var_pattern" in
            (ty, ValID.Map.singleton id ty, Var(id, ty))
          end
      | elaborate env (Constructor(path, p_opt)) =
          let
            structure M = X.Path struct
              type id = constr_ident
              type item = SS.Constr.t
              type dynamic = unit

              val env_lookup = Env.Constr.lookup
              fun dynamic _ _ = ()
              val proj = SS.Structure.proj_constructor
              val not_contain = SS.Constr.not_contain
            end

            val (x, ()) = M.elaborate env path
            val (ty_opt, ty12) = SS.Constr.instantiate x
          in
            case (ty_opt, p_opt) of
                 (NONE, NONE)        => (ty12, ValID.Map.empty, Constructor(path, NONE))
               | (NONE, SOME _)      => raise ArityMismatch
               | (SOME _, NONE)      => raise ArityMismatch
               | (SOME ty11, SOME p) =>
                   let
                     val (ty2, m, p') = elaborate env p
                     val () = IType.unify ty11 ty2
                   in
                     (ty12, m, Constructor(path, SOME p'))
                   end
          end
      | elaborate env (Typed(p, ty)) =
          let
            val (ty1, m, p') = elaborate env p
            val (ty2, k) = X.Type.elaborate env ty
            val () = Kind.get_base k
            val () = IType.unify ty1 ty2
          in
            (ty2, m, Typed(p', ty))
          end
      | elaborate env (Tuple ps) =
          let
            val xs = map (elaborate env) ps
            val m = foldl (fn ((_, m, _), acc) => ValID.Map.disjoint_union acc m) ValID.Map.empty xs
          in
            (IType.tuple $ map #1 xs, m, Tuple $ map #3 xs)
          end
      | elaborate env NilList =
          (IType.list $ IType.free $ FreeID.fresh Kind.base "?nil_pattern", ValID.Map.empty, NilList)
      | elaborate env (ConsList(x, y)) =
          let
            val (ty1, m1, p1) = elaborate env x
            val (ty2, m2, p2) = elaborate env y
            val () = IType.unify (IType.list ty1) ty2
          in
            (ty2, ValID.Map.disjoint_union m1 m2, ConsList(p1, p2))
          end
  end

  structure Expr = struct
    open Syntax.Expr

    fun elaborate_branch env (p, e) =
    let
      val (ty1, m, p') = Pattern.elaborate env p
      fun f acc id ty = Env.Val.insert acc id $ SS.Term.In ty
      val env1 = ValID.Map.fold_left f env m
      val (ty2, t) = X.Expr.elaborate env1 e
    in
      (ty1, ty2, [p'], [(p, t)])
    end

    fun elaborate_branches env bs =
    let
      val xs =
        case NonEmpty.from_list bs of
             SOME bs => NonEmpty.map (elaborate_branch env) bs
           | NONE    => NonEmpty.singleton
               ( IType.free $ FreeID.fresh Kind.base "?empty"
               , IType.free $ FreeID.fresh Kind.base "?diverge"
               , []
               , []
               )

      fun f (x1, y1, z1, w1) (x2, y2, z2, w2) =
        (x2, y2, z1 @ z2, w1 @ w2)
        before IType.unify x1 x2
        before IType.unify y1 y2
    in
      NonEmpty.fold_left1 f xs
    end

    fun make_term NONE id     = Term.var $ Internal.ValVar.from_label $ Label.value id
      | make_term (SOME t) id = Term.proj t $ Label.value id

    fun make_constructor NONE id     = Term.constr id
      | make_constructor (SOME _) id = Term.constr id (* Only constructor identifiers are important. *)

    fun f_v v acc id x =
      Term.let_
        (ValVar.from_label $ Label.value id)
        (Term.proj (Term.var v) $ Label.value id)
        acc

    fun f_m v acc id x =
      Term.let_
        (ValVar.from_label $ Label.module id)
        (Term.proj (Term.var v) $ Label.module id)
        acc

    fun elaborate env (Path p) =
          let
            structure M = X.Path struct
              type id = val_ident
              type item = SS.Term.t
              type dynamic = Term.t

              val env_lookup = Env.Val.lookup
              val dynamic = make_term
              val proj = SS.Structure.proj_value
              val not_contain = SS.Term.not_contain
            end
            val (SS.Term.In ty, t) = M.elaborate env p
          in
            (IType.instantiate ty, t)
          end
      | elaborate env (Let(bs, x)) =
          let
            val (e, t1) = X.Module.elaborate_bindings env bs
            val env1 = Env.insert env $ Quantified.get_body e
            val (ty, t2) = elaborate env1 x

            val bid_set =
              BoundID.Map.from_list $
                List.map (fn info => (#v info, ())) (Quantified.get_bound_vars e)

            val () = SS.Term.not_contain bid_set $ SS.Term.In ty

            structure M as S = Quantified.get_body e
            val v = ValVar.fresh ()
          in
            ( ty
            , Term.let_ v t1 $
                ModuleID.Map.fold_left (f_m v)
                (ValID.Map.fold_left (f_v v) t2 M.v)
                M.m
            )
          end
      | elaborate env (Abs(ps, x)) =
          let
            fun f (tys, acc) p =
            let
              val (ty, m, p') = Pattern.elaborate acc p
              val () = Pattern.exhaustivity_check [p'] ty

              fun g acc id ty = Env.Val.insert acc id $ SS.Term.In ty
              val acc = ValID.Map.fold_left g acc m
            in
              (tys @ [ty], acc)
            end

            val (tys, env1) = NonEmpty.fold_left f ([], env) ps
            val (ty, t) = elaborate env1 x

            val v = ValVar.fresh ()
          in
            ( List.foldr (fn (ty, acc) => IType.arrow ty acc) ty tys
            , List.foldr (fn (p, acc) => Term.abs v $ Term.match (Term.var v) [(p, acc)]) t $ NonEmpty.to_list ps
            )
          end
      | elaborate env (App(x, y)) =
          let
            val (ty1, t1) = elaborate env x
            val (ty2, t2) = elaborate env y
            val cod = IType.free $ FreeID.fresh Kind.base "?app"
            val () = IType.unify ty1 (IType.arrow ty2 cod)
          in
            (cod, Term.app t1 t2)
          end
      | elaborate env (Lit l) = (IType.base $ Literal.elaborate l, Term.lit l)
      | elaborate env (List xs) =
          let
            val fid = FreeID.fresh Kind.base "?list"

            fun f (x, (ty, acc)) =
            let val (ty1, t1) = elaborate env x in
              IType.unify ty ty1;
              (ty1, acc @ [t1])
            end

            val (ty, ys) = List.foldl f (IType.free fid, []) xs
          in
            (IType.list ty, Term.list ys)
          end
      | elaborate env (ConsList(x, y)) =
          let
            val (ty1, t1) = elaborate env x
            val (ty2, t2) = elaborate env y
            val () = IType.unify (IType.list ty1) ty2
          in
            (ty2, Term.cons_list t1 t2)
          end
      | elaborate env (Tuple xs) =
          let val xs = map (elaborate env) xs in
            (IType.tuple $ map #1 xs, Term.tuple $ map #2 xs)
          end
      | elaborate env (If(x, y, z)) =
          let
            val (ty1, t1) = elaborate env x
            val () = IType.unify (IType.base Internal.Base.Bool) ty1

            val (ty2, t2) = elaborate env y
            val (ty3, t3) = elaborate env z
            val () = IType.unify ty2 ty3
          in
            (ty2, Term.if_ t1 t2 t3)
          end
      | elaborate env (Constructor p) =
          let
            structure M = X.Path struct
              type id = constr_ident
              type item = SS.Constr.t
              type dynamic = Term.t

              val env_lookup = Env.Constr.lookup
              val dynamic = make_constructor
              val proj = SS.Structure.proj_constructor
              val not_contain = SS.Constr.not_contain
            end

            val (SS.Constr.In(ty_opt, bid0, bids), t) = M.elaborate env p
            val ty2 = List.foldl (fn (bid, acc) => IType.app acc $ IType.bound bid) (IType.bound bid0) bids
            val ty =
              case ty_opt of
                   SOME ty1 => IType.arrow ty1 ty2
                 | NONE     => ty2
          in
            ( IType.instantiate (IType.forall bids ty)
            , t
            )
          end
      | elaborate env (Match(x, bs)) =
          let
            val (ty1, t1) = elaborate env x
            val (ty21, ty22, ps, bs') = elaborate_branches env bs
            val () = IType.unify ty1 ty21
            val () = Pattern.exhaustivity_check ps ty1
          in
            (ty22, Term.match t1 bs')
          end
      | elaborate env (Function bs) =
          let
            val (ty1, ty2, ps, bs') = elaborate_branches env bs
            val () = Pattern.exhaustivity_check ps ty1
            val v = ValVar.fresh ()
          in
            (IType.arrow ty1 ty2, Term.abs v $ Term.match (Term.var v) bs')
          end
      | elaborate env (Pack(m, s)) =
          let
            val (asig1, t) = X.Module.elaborate env m
            val asig2 = X.Signature.elaborate env s
            val asig2' = SS.Module.normalize_abstract asig2
            val () = SS.Module.subtype_abstract asig1 asig2'
          in
            (SS.Module.to_type_abstract asig2', t)
          end
      | elaborate env (BinOp(b, x, y)) =
          let
            val id = Syntax.BinOp.to_ident b
            open Syntax
            open Expr
          in
            elaborate env $ App(App(Path (Path.Ident id), x), y)
          end
      | elaborate env (Open(m, x)) =
          let open Syntax in
            elaborate env $ Let(Module.Cons(Binding.Include m, Module.Nil), x)
          end
  end

  structure Type = struct
    open Syntax.Type

    fun elaborate env (Path p) =
          let
            structure M = X.Path struct
              type id = type_ident
              type item = SS.Type.t
              type dynamic = unit

              val env_lookup = Env.Type.lookup
              fun dynamic _ _ = ()
              val proj = SS.Structure.proj_type
              val not_contain = SS.Type.not_contain
            end

            val (SS.Type.In(ty, k, _), ()) = M.elaborate env p
          in
            (ty, k)
          end
      | elaborate env (Var v) =
          let val bid = Env.TypeVar.lookup env v in
            (IType.bound bid, BoundID.get_kind bid)
          end
      | elaborate env (Arrow(x, y)) =
          let
            val (ty1, k1) = elaborate env x
            val () = Kind.get_base k1
            val (ty2, k2) = elaborate env y
            val () = Kind.get_base k2
          in
            (IType.arrow ty1 ty2, Kind.base)
          end
      | elaborate env (App(x, y)) =
          let
            val (ty1, k1) = elaborate env x
            val (k11, k12) = Kind.get_arrow k1
            val (ty2, k2) = elaborate env y
          in
            if k11 = k2
            then (IType.app ty1 ty2, k12)
            else raise Kind.Mismatch(k11, k2)
          end
      | elaborate env (Let(bs, ty)) =
          let
            val (e, _) = X.Module.elaborate_bindings env bs
            val env1 = Env.insert env $ Quantified.get_body e
            val res as (ty, k) = elaborate env1 ty

            val bid_set =
              BoundID.Map.from_list $
                List.map (fn info => (#v info, ())) (Quantified.get_bound_vars e)

            val () = SS.Type.not_contain bid_set $ SS.Type.In(ty, k, ConstrID.Map.empty)
          in
            res
          end
      | elaborate env (Tuple xs) =
          let
            fun f x =
            let val (ty, k) = elaborate env x in
              ty before Kind.get_base k
            end
          in
            (IType.tuple $ map f xs, Kind.base)
          end
      | elaborate env (Pack s) =
          let
            val asig = X.Signature.elaborate env s
          in
            ( SS.Module.to_type_abstract $ SS.Module.normalize_abstract asig
            , Kind.base
            )
          end
  end

  fun unwrap_or def NONE   = def
    | unwrap_or _ (SOME x) = x

  structure Decl = struct
    open Syntax.Decl

    fun elaborate_type_decl env id vs Opaque =
          let
            val k = Kind.from_nat $ Nat.length_of_list vs
            val bid = BoundID.fresh k $ TypeID.get_name id
          in
            Quantified.quantify1 {v = bid, k = k, location = ([], id)} $
              SS.Structure.singleton_type id $
                SS.Type.In(IType.bound bid, k, ConstrID.Map.empty)
          end
      | elaborate_type_decl env id vs (Transparent ty) =
          let
            val xs = List.map (fn v => (v, BoundID.fresh Kind.base $ TypeVar.get_name v)) vs
            val env1 = List.foldl (fn ((v, bid), acc) => Env.TypeVar.insert acc v bid) env xs
            val (ty, k) = Type.elaborate env1 ty
            val ty' = List.foldr (fn ((_, bid), acc) => IType.abs bid acc) ty xs
            val k' = List.foldl (fn (_, acc) => Kind.arrow Kind.base acc) k xs
          in
            Quantified.from_body $ SS.Structure.singleton_type id $ SS.Type.In(ty', k', ConstrID.Map.empty)
          end

    fun elaborate_datatype_decl env ds =
    let
      val xs = List.map (fn (id, vs, m) =>
        let val r = ref NONE in
          (id, vs, m, r, BoundID.fresh_with_content (Kind.from_nat $ Nat.length_of_list vs) (TypeID.get_name id) r)
        end) ds
      val env1 = List.foldl (fn ((id, vs, m, _, bid), acc) => Env.Type.insert acc id $ SS.Type.In(IType.bound bid, BoundID.get_kind bid, ConstrID.Map.empty)) env xs
      val ys = List.map (fn (id, vs, m, r, bid) =>
          let
            val zs = List.map (fn v => (v, BoundID.fresh Kind.base $ TypeVar.get_name v)) vs
            val env2 = List.foldl (fn ((v, bid), acc) => Env.TypeVar.insert acc v bid) env1 zs

            fun f ty =
            let
              val (ty, k) = Type.elaborate env2 ty
              val () = Kind.get_base k
            in
              ty
            end

            val m0 = ConstrID.Map.map (Option.map f) m

            val () = r := SOME(ConstrID.Map.map (fn x => (x, List.map #2 zs)) m0)

            fun g x = SS.Constr.In(x, bid, List.map #2 zs)
            val m' = ConstrID.Map.map g m0
          in
            (id, bid, SS.Type.In(IType.bound bid, BoundID.get_kind bid, ConstrID.Map.map (fn _ => ()) m'), m')
          end
        ) xs

      val is = List.map (fn (id, bid, _, _) => {v = bid, k = BoundID.get_kind bid, location = ([], id)}) ys

      val s1 = SS.Structure.types $
        List.foldl (fn ((id, _, x, _), acc) => TypeID.Map.insert id x acc) TypeID.Map.empty ys
      val s2 = SS.Structure.constructors $
        List.foldl (fn ((_, _, _, m), acc) => ConstrID.Map.disjoint_union acc m) ConstrID.Map.empty ys
    in
      Quantified.quantify is $ SS.Structure.merge s1 s2
    end

    fun elaborate env (Val(id, tvs, ty)) =
        let
          val xs = List.map (fn tv => (tv, BoundID.fresh Kind.base (TypeVar.get_name tv))) tvs
          val env1 = List.foldl (fn ((tv, bid), acc) => Env.TypeVar.insert acc tv bid) env xs
          val (ty, k) = Type.elaborate env1 ty
          val () = Kind.get_base k
        in
          Quantified.from_body $
            SS.Structure.singleton_value id $ SS.Term.In $ IType.forall (List.map #2 xs) ty
        end
      | elaborate env (Type(id, vs, d)) = elaborate_type_decl env id vs d
      | elaborate env (Datatype ds) = elaborate_datatype_decl env $ NonEmpty.to_list ds
      | elaborate env (Module(id, ps, s)) =
          Quantified.map_with_location
            (SS.Structure.singleton_module id)
            (fn (mids, tid) => (id :: mids, tid))
            (X.Signature.elaborate env $ foldr (fn ((id, s1), s2) => Syntax.Signature.Fun(id, s1, s2)) s ps)
      | elaborate env (Signature(id, s)) =
          Quantified.from_body $ SS.Structure.singleton_signature id $ SS.Signature.In $
            X.Signature.elaborate env s
      | elaborate env (Include s) =
          X.Signature.elaborate env s |> Quantified.map SS.Module.get_structure
  end

  structure Signature = struct
    open Syntax.Signature

    exception RedefinedByWhereType of location

    fun elaborate_decls env Nil = Quantified.from_body SS.Structure.empty
      | elaborate_decls env (Cons(d, ds)) =
          let
            val e1 = Decl.elaborate env d
            val env1 = Env.insert env (Quantified.get_body e1)
            val e2 = elaborate_decls env1 ds
          in
            Quantified.merge SS.Structure.merge_distinct e1 e2
          end
      | elaborate_decls env (Open(m, ds)) =
          let
            val (e1, _) = X.Module.elaborate env m
            val env1 = Env.insert env (SS.Module.get_structure $ Quantified.get_body e1)
            val e2 = elaborate_decls env1 ds
          in
            Quantified.merge (fn _ => fn x => x) e1 e2
          end

    fun elaborate env (Path p) =
          let
            structure M = X.Path struct
              type id = signature_ident
              type item = SS.Signature.t
              type dynamic = unit

              val env_lookup = Env.Signature.lookup
              fun dynamic _ _ = ()
              val proj = SS.Structure.proj_signature
              val not_contain = SS.Signature.not_contain
            end

            val (SS.Signature.In asig, ()) = M.elaborate env p

            val r = ref BoundID.Map.empty

            val asig' = asig |> Quantified.rename_bound_vars (fn bid =>
              let val new_bid = BoundID.refresh bid in
                new_bid before r := BoundID.Map.insert bid (IType.bound new_bid) (!r)
              end)
          in
            Quantified.map (SS.Module.subst (!r)) asig'
          end
      | elaborate env (Fun(id, x, y)) =
          let
            val asig1 = elaborate env x
            val env1 = Env.Module.insert env id $ Quantified.get_body asig1
            val asig2 = elaborate env1 y
          in
            Quantified.from_body $ SS.Module.F $ Quantified.map (fn s1 => (s1, asig2)) asig1
          end
      | elaborate env (WhereType(x, loc as (mids, tid), ty)) =
          let
            val asig = elaborate env x
            val s0 = SS.Module.get_structure $ Quantified.get_body asig
            val s1 =
              List.foldl (fn (mid, s) => SS.Structure.proj_module s mid |> SS.Module.get_structure) s0 mids
            val SS.Type.In(ty1, k1, _) = SS.Structure.proj_type s1 tid
            val bid = IType.get_bound_var ty1
            val (ty2, k2) = Type.elaborate env ty
            val () =
              if k1 = k2
              then ()
              else raise Kind.Mismatch(k1, k2)
          in
            case Quantified.find_remove (fn {v, ...} => BoundID.eq (v, bid)) asig of
                 NONE       => raise RedefinedByWhereType(loc)
               | SOME asig' =>
                   Quantified.map (fn s => SS.Module.subst (BoundID.Map.singleton bid ty2) s) asig'
          end
      | elaborate env (DestructType(x, loc, ty)) =
          elaborate env (WhereType(x, loc, ty))
            |> Quantified.map (SS.Module.lift_endo $ SS.Structure.remove_location loc)
      | elaborate env (Decls ds) = elaborate_decls env ds |> Quantified.map SS.Module.S
      | elaborate env (Let(bs, s)) =
          let
            val (e, _) = X.Module.elaborate_bindings env bs
            val env1 = Env.insert env $ Quantified.get_body e
            val asig = elaborate env1 s

            val bid_set =
              BoundID.Map.from_list $
                List.map (fn info => (#v info, ())) (Quantified.get_bound_vars e)

            val () = SS.Module.not_contain bid_set $ Quantified.get_body asig
          in
            asig
          end
  end

  structure Binding = struct
    open Syntax.Binding

    fun elaborate_val_binding env (V(p, e)) =
          let
            val (ty, t) = Expr.elaborate env e

            val (ty1, m, p') = Pattern.elaborate env p
            val () = IType.unify ty1 ty
            val () = Pattern.exhaustivity_check [p'] ty

            fun f acc id _ =
              Record.insert (Label.value id) (Term.var $ ValVar.from_label $ Label.value id) acc
          in
            ( Quantified.from_body $ SS.Structure.values $ ValID.Map.map (SS.Term.In o Env.close env) m
            , Term.match t [(p, Term.record $ ValID.Map.fold_left f Record.empty m)]
            )
          end
      | elaborate_val_binding env (F(id, vs, ps, e)) =
          let
            val xs = map (fn v => (v, BoundID.fresh Kind.base $ TypeVar.get_name v)) vs
            val env1 = foldl (fn ((v, bid), acc) => Env.TypeVar.insert acc v bid) env xs
            val (ty, t) = Expr.elaborate env1 $ Expr.Abs(ps, e)
            val ty = Env.close env1 ty
            val ty = IType.forall (map #2 xs) ty (* May introduce unnecessary quantification. *)
          in
            ( Quantified.from_body $ SS.Structure.singleton_value id $ SS.Term.In ty
            , Term.record (Record.singleton (Label.value id) t)
            )
          end
      | elaborate_val_binding env (Rec m) =
          let
            fun f acc id _ =
              Env.Val.insert acc id $ SS.Term.In $
                IType.arrow
                  (IType.free $ FreeID.fresh Kind.base "?rec-dom")
                  (IType.free $ FreeID.fresh Kind.base "?rec-cod")

            val env1 = ValID.Map.fold_left f env m
            val m' = ValID.Map.map (fn (ps, e) => Expr.elaborate env1 $ Syntax.Expr.Abs(ps, e)) m
          in
            ( Quantified.from_body $ SS.Structure.values $ ValID.Map.map (SS.Term.In o Env.close env o #1) m'
            , Term.letrec
              (List.map (fn (id, (_, t)) => (ValVar.from_label $ Label.value id, t)) $ ValID.Map.to_list m')
              (Term.record $ Record.from_list $ map (fn (id, _) => (Label.value id, Term.var $ ValVar.from_label $ Label.value id)) $ ValID.Map.to_list m')
            )
          end

    fun elaborate env (Val b) = elaborate_val_binding env b
      | elaborate env (Type(id, vs, ty)) =
          let
            val xs = List.map (fn v => (v, BoundID.fresh Kind.base $ TypeVar.get_name v)) vs
            val env1 = List.foldl (fn ((v, bid), acc) => Env.TypeVar.insert acc v bid) env xs
            val (ty, k) = Type.elaborate env1 ty
            val ty' = List.foldr (fn ((_, bid), acc) => IType.abs bid acc) ty xs
            val k' = List.foldl (fn (_, acc) => Kind.arrow Kind.base acc) k xs
          in
            ( Quantified.from_body $ SS.Structure.singleton_type id $ SS.Type.In(ty', k', ConstrID.Map.empty)
            , Term.record Record.empty
            )
          end
      | elaborate env (Datatype ds) =
          (Decl.elaborate_datatype_decl env $ NonEmpty.to_list ds, Term.record Record.empty)
      | elaborate env (Module(id, ps, ann, m)) =
          let
            val m' =
              case ann of
                   None      => m
                 | Seal s    => Syntax.Module.Seal(m, s)
                 | Ascribe s => Syntax.Module.Ascribe(m, s)
            val m' =
              case ps of
                   []      => m'
                 | p :: ps => Syntax.Module.Fun(NonEmpty.make p ps, m')
            val (asig, t) = X.Module.elaborate env m'
          in
            ( Quantified.map (SS.Structure.singleton_module id) asig
            , Term.record $ Record.singleton (Label.module id) t
            )
          end
      | elaborate env (Signature(id, s)) =
          let val asig = Signature.elaborate env s in
            ( Quantified.from_body $ SS.Structure.singleton_signature id $ SS.Signature.In asig
            , Term.record Record.empty
            )
          end
      | elaborate env (Include m) =
          let val (asig, t) = X.Module.elaborate env m in
            (Quantified.map SS.Module.get_structure asig, t)
          end
  end

  structure Module = struct
    open Syntax.Module

    fun f_v v acc id x =
      Term.let_
        (ValVar.from_label $ Label.value id)
        (Term.proj (Term.var v) $ Label.value id)
        acc

    fun f_m v acc id x =
      Term.let_
        (ValVar.from_label $ Label.module id)
        (Term.proj (Term.var v) $ Label.module id)
        acc

    fun elaborate_bindings env Nil = (Quantified.from_body SS.Structure.empty, Term.record Record.empty)
      | elaborate_bindings env (Cons(b, bs)) =
          let
            val (e1, t1) = Binding.elaborate env b
            val env1 = Env.insert env (Quantified.get_body e1)
            val (e2, t2) = elaborate_bindings env1 bs
            val e = Quantified.merge SS.Structure.merge e1 e2

            val v1 = ValVar.fresh ()
            val v2 = ValVar.fresh ()
            structure M1 as S = Quantified.get_body e1
            structure M2 as S = Quantified.get_body e2
            structure N as S = Quantified.get_body e

            fun g label acc id _ =
              Record.insert (label id) (Term.var $ ValVar.from_label $ label id) acc

            val t = Term.record $ ModuleID.Map.fold_left (g Label.module) (ValID.Map.fold_left (g Label.value) Record.empty N.v) N.m

            val t =
              Term.let_ v2 t2 $
                ModuleID.Map.fold_left
                  (f_m v2)
                  (ValID.Map.fold_left (f_v v2) t M2.v)
                  M2.m
          in
            ( e
            , Term.let_ v1 t1 $
                ModuleID.Map.fold_left
                  (f_m v1)
                  (ValID.Map.fold_left (f_v v1) t M1.v)
                  M1.m
            )
          end
      | elaborate_bindings env (Open(m, bs)) =
          let
            val (e1, t1) = X.Module.elaborate env m
            val e1 = Quantified.map SS.Module.get_structure e1
            val env1 = Env.insert env (Quantified.get_body e1)
            val (e2, t2) = elaborate_bindings env1 bs

            val v1 = ValVar.fresh ()
            structure M as S = Quantified.get_body e1
          in
            ( Quantified.merge (fn _ => fn x => x) e1 e2
            , Term.let_ v1 t1 $
                ModuleID.Map.fold_left
                  (f_m v1)
                  (ValID.Map.fold_left (f_v v1) t2 M.v)
                  M.m
            )
          end

    fun elaborate env (Ident id) =
          ( Quantified.from_body $ Env.Module.lookup env id
          , Internal.Term.var $ Internal.ValVar.from_label $ Label.module id
          )
      | elaborate env (Proj(x, id)) =
          let
            val (asig, t) = elaborate env x
            fun f s = SS.Structure.proj_module (SS.Module.get_structure s) id
            fun g (mids, tid) =
               case mids of
                    [] => (mids, tid) (* as-is *)
                  | hd :: tl =>
                      if ModuleID.eq (hd, id)
                      then (tl, tid)
                      else (mids, tid) (* as-is *)
          in
            (Quantified.map_with_location f g asig, Term.proj t $ Label.module id)
          end
      | elaborate env (Seal(m, s)) =
          let
            val (asig1, t) = elaborate env m
            val asig2 = Signature.elaborate env s
            val _ = SS.Module.match (Quantified.get_body asig1) asig2
          in
            (asig2, t)
          end
      | elaborate env (Ascribe(m, s)) =
          let
            val (asig1, t) = elaborate env m
            val asig2 = Signature.elaborate env s
            val bid_map = SS.Module.match (Quantified.get_body asig1) asig2
            val s2 = SS.Module.subst bid_map $ Quantified.get_body asig2
          in
            (Quantified.map (fn _ => s2) asig1, t)
          end
      | elaborate env (App(x, y)) =
          let
            val (asig1, t1) = elaborate env x
            val u = SS.Module.get_functor $ Quantified.get_body asig1
            val (asig2, t2) = elaborate env y
            val bid_map = SS.Module.match (Quantified.get_body asig2) (Quantified.map #1 u)
            val asig = Quantified.map (fn s3 => SS.Module.subst bid_map s3) (#2 (Quantified.get_body u))
            val ex = Quantified.merge (fn _ => fn _ => ()) asig1 asig2
          in
            ( Quantified.merge (fn _ => fn s => s) ex asig
            , Term.app t1 t2
            )
          end
      | elaborate env (Fun(ps, m)) =
          let
            val ps = NonEmpty.to_list ps
            val (asigs, env1) = foldl (fn ((id, s), (asigs, acc)) =>
              let val asig1 = Signature.elaborate acc s
              in
                (asigs @ [asig1], Env.Module.insert acc id $ Quantified.get_body asig1)
              end) ([], env) ps
            val (asig2, t) = elaborate env1 m
          in
            ( foldr (fn (asig1, acc) => Quantified.from_body $ SS.Module.F $ Quantified.map (fn s1 => (s1, acc)) asig1) asig2 asigs
            , foldr (fn ((id, _), acc) => Term.abs (Internal.ValVar.from_label $ Label.module id) acc) t ps
            )
          end
      | elaborate env (Bindings bs) =
          let val (e, t) = elaborate_bindings env bs in
            (Quantified.map SS.Module.S e, t)
          end
      | elaborate env (Let(bs, m)) =
          let
            val (e, t1) = elaborate_bindings env bs
            val env1 = Env.insert env $ Quantified.get_body e
            val (asig, t2) = elaborate env1 m

            structure M as S = Quantified.get_body e
            val v = ValVar.fresh ()
          in
            ( Quantified.merge (fn _ => fn s => s) e asig
            , Term.let_ v t1 $
                ModuleID.Map.fold_left (f_m v)
                (ValID.Map.fold_left (f_v v) t2 M.v)
                M.m
            )
          end
      | elaborate env (Unpack(e, s)) =
          let
            val (ty, t) = Expr.elaborate env e
            val asig = Signature.elaborate env s
            val asig' = SS.Module.normalize_abstract asig
            val () = IType.unify ty $ SS.Module.to_type_abstract asig'
          in
            (asig', t)
          end
  end


  functor Path (Y : sig
    type id
    type item
    type dynamic

    val env_lookup : env -> id -> item
    val dynamic : Term.t option -> id -> dynamic
    val proj : SS.Structure.t -> id -> item
    val not_contain : unit Internal.BoundID.Map.t -> item -> unit
  end) = struct
    open Syntax.Path

    fun elaborate env (Ident id) =
          ( Y.env_lookup env id
          , Y.dynamic NONE id
          )
      | elaborate env (Proj(m, id)) =
          let
            val (asig, t) = Module.elaborate env m
            val e = Quantified.map (fn s => Y.proj (SS.Module.get_structure s) id) asig

            val bid_set =
              BoundID.Map.from_list $
                List.map (fn info => (#v info, ())) (Quantified.get_bound_vars e)

            val () = Y.not_contain bid_set $ Quantified.get_body e
          in
            (Quantified.get_body e, Y.dynamic (SOME t) id)
          end
  end

  structure Unit = struct
    open Result Syntax.Unit

    exception InvalidFilename of string

    fun is_valid c = Char.isAlphaNum c orelse Char.contains "_-." c

    fun check s =
      if List.all is_valid $ String.explode s
      then s
      else raise InvalidFilename(s)

    fun get_filepath (Include s)  = Filepath.relative $ check s ^ ".bml"
      | get_filepath (Bind(_, s)) = Filepath.relative $ check s ^ ".bml"

    exception DuplicateSubmodule of Filepath.relative

    fun elaborate env (path, parse) (ss, bs) =
    let
      fun f s ((e1, t1_f, m), env0) =
      let
        val p1 = get_filepath s
        val current = Filepath.drop_ext $ Filepath.basename path
        val p1' =
          if Filepath.eq (current, Filepath.relative "main")
          then Filepath.join [Filepath.dir path, p1]
          else Filepath.join [Filepath.drop_ext path, p1]
        val m =
          case Filepath.Map.lookup p1 m of
               SOME () => raise DuplicateSubmodule(p1)
             | NONE    => Filepath.Map.insert p1 () m
        val res = parse p1' >>= elaborate env0 (p1', parse)
      in
        res >>= Right o (fn (e2, t2) =>
        case s of
             Include _   =>
              let
                val v = ValVar.fresh ()
                structure M as S = Quantified.get_body e2
                fun t2_f t = Term.let_ v t2 $
                  ModuleID.Map.fold_left (Expr.f_m v) (ValID.Map.fold_left (Expr.f_v v) t M.v) M.m
              in
               ( (Quantified.merge SS.Structure.merge e1 e2, t1_f o t2_f, m)
               , Env.insert env0 $ Quantified.get_body e2
               )
              end
           | Bind(id, _) =>
               let
                 val v = ValVar.from_label $ Label.module id
               in
                 ( (Quantified.merge SS.Structure.merge e1 $ Quantified.map (SS.Structure.singleton_module id o SS.Module.S) e2, t1_f o Term.let_ v t2, m)
                 , Env.Module.insert env0 id $ SS.Module.S $ Quantified.get_body e2
                 )
               end
           )
      end
    in
      foldl (fn (s, acc) => acc >>= f s) (Right ((Quantified.from_body SS.Structure.empty, fn x => x, Filepath.Map.empty), env)) ss >>= (fn ((e1, t1_f, _), env1) =>
        let
          val (e2, t2) = Module.elaborate_bindings env1 bs
          val e = Quantified.merge SS.Structure.merge e1 e2

          val v = ValVar.fresh ()
          structure M2 as S = Quantified.get_body e2
          structure N as S = Quantified.get_body e

          fun g label acc id _ =
            Record.insert (label id) (Term.var $ ValVar.from_label $ label id) acc

          val t = Term.record $ ModuleID.Map.fold_left (g Label.module) (ValID.Map.fold_left (g Label.value) Record.empty N.v) N.m

          val t =
            Term.let_ v t2 $
              ModuleID.Map.fold_left
                (Expr.f_m v)
                (ValID.Map.fold_left (Expr.f_v v) t M2.v)
                M2.m
        in
          Right(e, t1_f t)
        end
      )
    end
  end
end
