open Std

signature S = rec (X : sig
  structure Module : sig
    type t
    type abstract
  end
end) sig
  structure Term : sig
    datatype t = In of Internal.Type.t

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val ftv : t -> unit Internal.FreeID.Map.t
    val to_type : t -> IType.t
  end

  structure Type : sig
    datatype t = In of Internal.Type.t * Internal.kind * unit ConstrID.Map.t

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val ftv : t -> unit Internal.FreeID.Map.t
    val to_type : t -> IType.t
  end

  structure Signature : sig
    datatype t = In of X.Module.abstract

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val ftv : t -> unit Internal.FreeID.Map.t
    val to_type : t -> IType.t
  end

  structure Constr : sig
    datatype t = In of IType.t option * Internal.BoundID.t * Internal.BoundID.t list (* Assume the arguments are fully applied. *)

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val ftv : t -> unit Internal.FreeID.Map.t
    val instantiate : t -> IType.t option * IType.t
    val to_type : t -> IType.t
  end

  structure Structure : sig
    signature T = sig
      val v : Term.t ValID.Map.t
      val t : Type.t TypeID.Map.t
      val m : X.Module.t ModuleID.Map.t
      val s : Signature.t SignatureID.Map.t
      val c : Constr.t ConstrID.Map.t
    end

    type t = [T]

    val empty : t
    val singleton_value : val_ident -> Term.t -> t
    val singleton_type : type_ident -> Type.t -> t
    val singleton_module : module_ident -> X.Module.t -> t
    val singleton_signature : signature_ident -> Signature.t -> t

    val values : Term.t ValID.Map.t -> t
    val types : Type.t TypeID.Map.t -> t
    val constructors : Constr.t ConstrID.Map.t -> t

    val merge_distinct : t -> t -> t
    val merge : t -> t -> t (* Right-biased. *)

    exception UnboundModule   of module_ident
    exception UnboundValue    of val_ident
    exception UnboundType     of type_ident
    exception UnboundSignaure of signature_ident

    val proj_value : t -> val_ident -> Term.t
    val proj_type : t -> type_ident -> Type.t
    val proj_module : t -> module_ident -> X.Module.t
    val proj_signature : t -> signature_ident -> Signature.t
    val proj_constructor : t -> constr_ident -> Constr.t

    val proj_location : t -> location -> Type.t

    val remove_type : type_ident -> t -> t
    val remove_location : location -> t -> t

    val update_module : module_ident -> (X.Module.t -> X.Module.t) -> t -> t

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val ftv : t -> unit Internal.FreeID.Map.t
    val to_type : t -> IType.t
  end

  structure Module : sig
    datatype t
      = S of Structure.t
      | F of (t * abstract) universal

    withtype abstract = t existential

    exception NotStructure of t

    val get_structure : t -> Structure.t
    val get_functor : t -> (t * abstract) universal

    val lift_endo : (Structure.t -> Structure.t) -> t -> t

    val subst : IType.t Internal.BoundID.Map.t -> t -> t
    val subst_abstract : IType.t Internal.BoundID.Map.t -> abstract -> abstract
    val not_contain : unit Internal.BoundID.Map.t -> t -> unit
    val subtype : t -> t -> unit
    val subtype_abstract : abstract -> abstract -> unit
    val match : t -> abstract -> IType.t Internal.BoundID.Map.t
    val ftv : t -> unit Internal.FreeID.Map.t
    val ftv_abstract : abstract -> unit Internal.FreeID.Map.t
    val to_type : t -> IType.t
    val to_type_abstract : abstract -> IType.t
    val normalize_abstract : abstract -> abstract
    val refresh : abstract -> abstract
  end
end

structure SemanticSignature : S = rec (X : S) struct
  structure Kind = Internal.Kind

  structure Term = struct
    datatype t = datatype X.Term.t

    fun subst m (In ty) = In $ IType.subst m ty

    fun not_contain bid_set (In ty) = IType.not_contain bid_set ty

    fun subtype (In ty1) (In ty2) = IType.is_instance_of ty2 ty1

    fun ftv (In ty) = IType.ftv ty

    fun to_type (In ty) = ty
  end

  structure Type = struct
    datatype t = datatype X.Type.t

    fun subst m (In(ty, k, cs)) = In(IType.subst m ty, k, cs)

    fun not_contain bid_set (In(ty, _, _)) = Internal.Type.not_contain bid_set ty

    fun equal_set cs1 cs2 =
    let
      val size1 = ConstrID.Map.size cs1
      val size2 = ConstrID.Map.size cs2
      val size = ConstrID.Map.size (ConstrID.Map.union cs1 cs2)
    in
      size1 = size2 andalso size = size1
    end

    exception ConstructorMismatch

    fun subtype (In(ty1, k1, cs1)) (In(ty2, k2, cs2)) =
      if k1 = k2
      then
        if ConstrID.Map.is_empty cs2 orelse equal_set cs1 cs2
        then IType.equal ty1 ty2 k1
        else raise ConstructorMismatch
      else raise Kind.Mismatch(k1, k2)

    fun ftv (In(ty, _, _)) = IType.ftv ty

    fun to_type (In(ty, k, _)) =
      IType.forall [Internal.BoundID.fresh (Kind.arrow k Kind.base) "?to_type"] ty
  end

  fun under_quantifiers bid_set q =
  let
    val x = Quantified.get_body q

    val bid_set =
      List.foldl
        (fn (info, acc) => Internal.BoundID.Map.delete (#v info) acc)
        bid_set
        (Quantified.get_bound_vars q)
  in
    (bid_set, x)
  end

  structure Signature = struct
    datatype t = datatype X.Signature.t

    fun subst m (In asig) = In $ X.Module.subst_abstract m asig

    fun not_contain bid_set (In asig) =
    let
      val (bid_set, x) = under_quantifiers bid_set asig
    in
      X.Module.not_contain bid_set x
    end

    fun subtype (In asig1) (In asig2) =
      X.Module.subtype_abstract asig1 asig2
      before X.Module.subtype_abstract asig2 asig1

    fun ftv (In asig) = X.Module.ftv_abstract asig

    fun to_type (In asig) = X.Module.to_type_abstract asig
  end

  structure Constr = struct
    datatype t = datatype X.Constr.t

    fun subst m (In(ty_opt, bid, bids)) =
    let
      val m = List.foldl (fn (bid, acc) => Internal.BoundID.Map.delete bid acc) m bids
      val bid' =
        case Internal.BoundID.Map.lookup bid m of
             NONE    => bid
           | SOME ty => IType.get_bound_var ty
    in
      In(Option.map (IType.subst m) ty_opt, bid', bids)
    end

    fun not_contain bid_set (In(ty_opt, bid, bids)) =
    let
      val bid_set =
        List.foldl
          (fn (bid, acc) => Internal.BoundID.Map.delete bid acc)
          bid_set
          bids
    in
      case (Internal.BoundID.Map.lookup bid bid_set, ty_opt) of
           (SOME _, _)  => raise IType.Contain(bid)
         | (_, NONE)    => ()
         | (_, SOME ty) => IType.not_contain bid_set ty
    end

    exception DatatypeMismatch of Internal.BoundID.t * Internal.BoundID.t
    exception ArityMismatch
    exception ArgMismatch

    fun zip [] []               = []
      | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
      | zip _ _                 = []

    fun subtype (In(ty_opt1, bid1, bids1)) (In(ty_opt2, bid2, bids2)) =
    let
      val () =
        if Internal.BoundID.eq (bid1, bid2)
        then ()
        else raise DatatypeMismatch(bid1, bid2)
      val () =
        if length bids1 = length bids2
        then ()
        else raise ArityMismatch

      val xs = List.map (fn p => (p, Internal.FreeID.fresh Internal.Kind.base "?subtype")) $ zip bids1 bids2
      val m1 = Internal.BoundID.Map.from_list $ List.map (fn ((x, _), fid) => (x, IType.free fid)) xs
      val m2 = Internal.BoundID.Map.from_list $ List.map (fn ((_, y), fid) => (y, IType.free fid)) xs

      val ty12 = List.foldl (fn ((_, fid), acc) => IType.app acc $ IType.free fid) (IType.bound bid1) xs
      val ty22 = List.foldl (fn ((_, fid), acc) => IType.app acc $ IType.free fid) (IType.bound bid2) xs

      val () = IType.equal ty12 ty22 Internal.Kind.base
    in
      case (ty_opt1, ty_opt2) of
           (NONE, NONE)           => ()
         | (SOME ty11, SOME ty21) => IType.equal (IType.subst m1 ty11) (IType.subst m2 ty21) Internal.Kind.base
         | _                      => raise ArgMismatch
    end

    fun ftv (In(ty_opt, _, _)) =
      case ty_opt of
           SOME ty => IType.ftv ty
         | NONE    => Internal.FreeID.Map.empty

    fun instantiate (In(ty_opt, bid, bids)) =
    let
      val xs = List.map (fn bid => (bid, IType.free $ Internal.FreeID.fresh (Internal.BoundID.get_kind bid) $ Internal.BoundID.get_name bid)) bids
      val cod = List.foldl (fn ((_, ty), acc) => IType.app acc ty) (IType.bound bid) xs
    in
      case ty_opt of
           NONE => (NONE, cod)
         | SOME ty => (SOME $ IType.subst (Internal.BoundID.Map.from_list xs) ty, cod)
    end

    fun to_type (In(ty_opt, bid, bids)) =
    let val ty2 = foldl (fn (bid, acc) => IType.app acc $ IType.bound bid) (IType.bound bid) bids in
      case ty_opt of
           NONE     => IType.forall bids ty2
         | SOME ty1 => IType.forall bids $ IType.arrow ty1 ty2
    end
  end

  structure Structure = struct
    signature T = sig
      val v : Term.t ValID.Map.t
      val t : Type.t TypeID.Map.t
      val m : X.Module.t ModuleID.Map.t
      val s : Signature.t SignatureID.Map.t
      val c : Constr.t ConstrID.Map.t
    end

    type t = X.Structure.t

    structure Empty = struct
      val v = ValID.Map.empty
      val t = TypeID.Map.empty
      val m = ModuleID.Map.empty
      val s = SignatureID.Map.empty
      val c = ConstrID.Map.empty
    end

    val empty = [ structure Empty as T ]

    fun singleton_value id x = [ structure struct
      open Empty
      val v = ValID.Map.singleton id x
    end as T ]

    fun singleton_type id x = [ structure struct
      open Empty
      val t = TypeID.Map.singleton id x
    end as T ]

    fun singleton_module id x = [ structure struct
      open Empty
      val m = ModuleID.Map.singleton id x
    end as T ]

    fun singleton_signature id x = [ structure struct
      open Empty
      val s = SignatureID.Map.singleton id x
    end as T ]

    fun values x = [ structure struct
      open Empty
      val v = x
    end as T ]

    fun types x = [ structure struct
      open Empty
      val t = x
    end as T ]

    fun constructors x = [ structure struct
      open Empty
      val c = x
    end as T ]

    fun merge_distinct x y =
    let
      structure M1 as T = x
      structure M2 as T = y
    in
      [ structure struct
          open M1
          val v = ValID.Map.disjoint_union v M2.v
          val t = TypeID.Map.disjoint_union t M2.t
          val m = ModuleID.Map.disjoint_union m M2.m
          val s = SignatureID.Map.disjoint_union s M2.s
          val c = ConstrID.Map.disjoint_union c M2.c
        end as T
      ]
    end

    fun merge x y =
    let
      structure M1 as T = x
      structure M2 as T = y
    in
      [ structure struct
          open M1
          val v = ValID.Map.union v M2.v
          val t = TypeID.Map.union t M2.t
          val m = ModuleID.Map.union m M2.m
          val s = SignatureID.Map.union s M2.s
          val c = ConstrID.Map.union c M2.c
        end as T
      ]
    end

    exception UnboundModule      of module_ident
    exception UnboundValue       of val_ident
    exception UnboundType        of type_ident
    exception UnboundSignaure    of signature_ident
    exception UnboundConstructor of constr_ident

    fun proj_value s id =
    let structure M as T = s in
      case ValID.Map.lookup id M.v of
           SOME x => x
         | NONE   => raise UnboundValue(id)
    end

    fun proj_type s id =
    let structure M as T = s in
      case TypeID.Map.lookup id M.t of
           SOME x => x
         | NONE   => raise UnboundType(id)
    end

    fun proj_module s id =
    let structure M as T = s in
      case ModuleID.Map.lookup id M.m of
           SOME x => x
         | NONE   => raise UnboundModule(id)
    end

    fun proj_signature s id =
    let structure M as T = s in
      case SignatureID.Map.lookup id M.s of
           SOME x => x
         | NONE   => raise UnboundSignaure(id)
    end

    fun proj_constructor s id =
    let structure M as T = s in
      case ConstrID.Map.lookup id M.c of
           SOME x => x
         | NONE   => raise UnboundConstructor(id)
    end

    fun proj_location s (mids, tid) =
      proj_type (List.foldl (fn (mid, acc) => X.Module.get_structure (proj_module acc mid)) s mids) tid

    fun remove_type id s =
    let structure M as T = s in
      [ structure struct
        open M
        val t = TypeID.Map.delete id t
      end as T ]
    end

    fun update_module id f s =
    let structure M as T = s in
      [ structure struct
        open M
        val m = ModuleID.Map.adjust id f m
      end as T ]
    end

    fun remove_location ([], tid) s          = remove_type tid s
      | remove_location (mid :: mids, tid) s =
          update_module mid (X.Module.lift_endo (remove_location (mids, tid))) s

    fun subst bid_map s =
    let structure M as T = s in
      [ structure struct
        val v = ValID.Map.map (Term.subst bid_map) M.v
        val t = TypeID.Map.map (Type.subst bid_map) M.t
        val s = SignatureID.Map.map (Signature.subst bid_map) M.s
        val m = ModuleID.Map.map (X.Module.subst bid_map) M.m
        val c = ConstrID.Map.map (Constr.subst bid_map) M.c
      end as T ]
    end

    fun not_contain bid_set s =
    let structure M as T = s in
      ValID.Map.app (Term.not_contain bid_set) M.v;
      TypeID.Map.app (Type.not_contain bid_set) M.t;
      SignatureID.Map.app (Signature.not_contain bid_set) M.s;
      ModuleID.Map.app (X.Module.not_contain bid_set) M.m;
      ConstrID.Map.app (Constr.not_contain bid_set) M.c
    end

    exception Missing

    fun unwrap (SOME x) = x
      | unwrap NONE     = raise Missing

    fun subtype s1 s2 =
    let
      structure M1 as T = s1
      structure M2 as T = s2

      fun f_v id = Term.subtype $ unwrap $ ValID.Map.lookup id M1.v
      fun f_t id = Type.subtype $ unwrap $ TypeID.Map.lookup id M1.t
      fun f_s id = Signature.subtype $ unwrap $ SignatureID.Map.lookup id M1.s
      fun f_m id = X.Module.subtype $ unwrap $ ModuleID.Map.lookup id M1.m
      fun f_c id = Constr.subtype $ unwrap $ ConstrID.Map.lookup id M1.c
    in
      ValID.Map.app_with_key f_v M2.v;
      TypeID.Map.app_with_key f_t M2.t;
      SignatureID.Map.app_with_key f_s M2.s;
      ModuleID.Map.app_with_key f_m M2.m;
      ConstrID.Map.app_with_key f_c M2.c
    end

    fun ftv s =
    let
      structure M as T = s
      val empty = Internal.FreeID.Map.empty
      fun x <> y = Internal.FreeID.Map.union x y
    in
      ValID.Map.fold_left (fn acc => fn _ => fn x => acc <> Term.ftv x) empty M.v
      <>
      TypeID.Map.fold_left (fn acc => fn _ => fn x => acc <> Type.ftv x) empty M.t
      <>
      SignatureID.Map.fold_left (fn acc => fn _ => fn x => acc <> Signature.ftv x) empty M.s
      <>
      ModuleID.Map.fold_left (fn acc => fn _ => fn x => acc <> X.Module.ftv x) empty M.m
      <>
      ConstrID.Map.fold_left (fn acc => fn _ => fn x => acc <> Constr.ftv x) empty M.c
    end

    fun to_type s =
    let
      structure M as T = s
      fun x <> y = Record.union x y

      val z1 = map (fn (id, x) => (Label.value id, Term.to_type x)) $ ValID.Map.to_list M.v
      val z2 = map (fn (id, x) => (Label.typ id, Type.to_type x)) $ TypeID.Map.to_list M.t
      val z3 = map (fn (id, x) => (Label.module id, X.Module.to_type x)) $ ModuleID.Map.to_list M.m
      val z4 = map (fn (id, x) => (Label.signature_ id, Signature.to_type x)) $ SignatureID.Map.to_list M.s
      val z5 = map (fn (id, x) => (Label.constr id, Constr.to_type x)) $ ConstrID.Map.to_list M.c
    in
      IType.record $
        Record.from_list z1 <> Record.from_list z2 <> Record.from_list z3 <>
        Record.from_list z4 <> Record.from_list z5
    end
  end

  structure Module = struct
    datatype t = datatype X.Module.t
    type abstract = X.Module.abstract

    exception NotStructure of t
    exception NotFunctor of t

    fun get_structure (S s) = s
      | get_structure x     = raise NotStructure(x)

    fun get_functor (F u) = u
      | get_functor x     = raise NotFunctor(x)

    fun lift_endo f (S s) = S(f s)
      | lift_endo _ (F u) = F u

    fun not_contain bid_set (S s) = Structure.not_contain bid_set s
      | not_contain bid_set (F u) =
          let
            val (bid_set1, (s1, asig)) = under_quantifiers bid_set u
            val (bid_set2, s2) = under_quantifiers bid_set1 asig
          in
            not_contain bid_set1 s1;
            not_contain bid_set2 s2
          end

    fun subst m (S s) = S $ Structure.subst m s
      | subst m (F u) =
          let
            val (m, _) = under_quantifiers m u
          in
            F $ Quantified.map (fn (s1, asig2) => (subst m s1, X.Module.subst_abstract m asig2)) u
          end

    fun subst_abstract m asig =
    let val (m, _) = under_quantifiers m asig in
      Quantified.map (subst m) asig
    end

    exception Mismatch of t * t

    fun subtype (S s1) (S s2) = Structure.subtype s1 s2
      | subtype (F u1) (F u2) =
          let
            val bid_map = X.Module.match (#1 $ Quantified.get_body u2) (Quantified.map #1 u1)
          in
            X.Module.subtype_abstract (subst_abstract bid_map $ #2 $ Quantified.get_body u1) (#2 $ Quantified.get_body u2)
          end
      | subtype s1 s2 = raise Mismatch(s1, s2)

    fun subtype_abstract asig1 asig2 = ignore (X.Module.match (Quantified.get_body asig1) asig2)

    fun lookup_var (s : t) (asig : abstract) : IType.t Internal.BoundID.Map.t =
    let
      val vs = Quantified.get_bound_vars asig

      fun f {v, k = k2, location} =
      let
        val Type.In(ty, k1, _) = Structure.proj_location (get_structure s) location
      in
        if k1 = k2
        then (v, ty)
        else raise (Internal.Kind.Mismatch(k1, k2))
      end

      fun g ((v, ty), acc) = Internal.BoundID.Map.insert v ty acc
    in
      List.foldl g Internal.BoundID.Map.empty (List.map f vs)
    end

    fun match s1 asig2 =
    let
      val tys = lookup_var s1 asig2
      val s2 = subst tys (Quantified.get_body asig2)
      val () = subtype s1 s2
    in
      tys
    end

    fun ftv (S s) = Structure.ftv s
      | ftv (F u) =
          let val (s, asig) = Quantified.get_body u in
            Internal.FreeID.Map.union (ftv s) (ftv_abstract asig)
          end

    and ftv_abstract asig = ftv (Quantified.get_body asig)

    fun to_type (S s) = Structure.to_type s
      | to_type (F u) =
          let
            val bids = map #v $ Quantified.get_bound_vars u
            val (s, asig) = Quantified.get_body u
          in
            IType.forall bids $ IType.arrow (to_type s) (to_type_abstract asig)
          end

    and to_type_abstract asig =
    let
      val bids = map #v $ Quantified.get_bound_vars asig
    in
      IType.exist bids $ to_type $ Quantified.get_body asig
    end

    fun normalize_abstract asig = asig (* TODO *)

    fun refresh asig =
    let
      val r = ref Internal.BoundID.Map.empty

      val asig' = asig |> Quantified.rename_bound_vars (fn bid =>
        let val new_bid = Internal.BoundID.refresh bid in
          new_bid before r := Internal.BoundID.Map.insert bid (IType.bound new_bid) (!r)
        end)
    in
      Quantified.map (subst (!r)) asig'
    end
  end
end

structure SS = SemanticSignature
