structure ParserError = struct
  exception UnexpectedToken of Token.t option
  exception DuplicateTypeVar of type_var
  exception DuplicateConstructor of constr_ident
end

structure Parser = MakeParser (struct
  open Std

  structure Streamable = StreamStreamable
  structure Arg = struct
    open ParserError

    type int = int
    type char = char
    type string = string

    open Syntax
    type val_binding = Binding.val_binding
    type binding = Binding.t
    type binding_list = Module.bindings
    type decl = Decl.t
    type decl_list = Signature.decls
    type module = Module.t
    type signature_ = Signature.t
    type expr = Expr.t
    type typ = Type.t
    type literal = Literal.t
    type param = Expr.param
    type params = Expr.params
    type type_var = type_var
    type type_vars = type_vars
    type pattern = Pattern.untyped
    type left_paren_kind_ref = Token.left_paren_kind ref

    type string_list = string list
    type string_non_empty = string non_empty

    fun uids_empty () = []
    fun uids_cons (s, ss) = s :: ss
    fun uids1 (s, ss) = NonEmpty.make s ss

    fun lower_proj s = NonEmpty.singleton s
    fun cons_lower_proj (s, ss) = NonEmpty.cons s ss

    fun last x [] = ([], x)
      | last x (y :: xs) =
          let val (zs, l) = last y xs in
            (x :: zs, l)
          end

    fun from_uids1 m ss f =
    let
      val (s, ss) = NonEmpty.uncons ss
      val (ss, s) = last s ss
    in
      Path.Proj(List.foldl (fn (s, acc) => Module.Proj(acc, ModuleID.from_string s)) m ss, f s)
    end

    fun module_atom m = m
    fun module_app m = m
    fun module_colon m = m
    fun module_functor m = m
    fun paren_module m = m
    fun path m = m

    local open Module in
      type projs = module_ident list
      fun proj_none () = []
      fun proj_some (s, ss) = ModuleID.from_string s :: ss

      val path_bindings = Bindings
      fun path_module_ident s = Ident $ ModuleID.from_string s

      fun aux m ids = List.foldl (fn (id, acc) => Proj(acc, id)) m ids

      fun bindings (bs, p) = aux (Bindings bs) p
      fun module_ident (s, p) = aux (path_module_ident s) p
      fun proj (m, s, p) = aux (Proj(m, ModuleID.from_string s)) p
      val app_module = App
      val transparent_ascription = Ascribe
      val seal = Seal
      fun functor_ (ps, m) = Fun(ps, m)
      fun app_to_functor (m1, f) = App(m1, f)
      fun unpack (e, s) = Unpack(e, s)

      fun empty_bindings () = Nil
      val cons_bindings = Cons
      val open_binding = Open

      type mparam = param
      type mparams = params
      fun mparam1 p = NonEmpty.singleton p
      fun mparam_cons (p, ps) = NonEmpty.cons p ps
      fun functor_param (id, s) = (ModuleID.from_string id, s)
    end

    local open Binding in
      type signature_ann = signature_ann

      type opt_bar = unit
      type datatype_dec = Type.t option ConstrID.Map.t
      type datatype_and = datatype_binding list

      fun datatype_no_and () = []
      fun datatype_and_ (s, vs, m, xs) = (TypeID.from_string s, vs, m) :: xs

      fun empty_d () = ConstrID.Map.empty

      fun cons_d1 (s, m) =
      let val id = ConstrID.from_string s in
        case ConstrID.Map.lookup id m of
             NONE   => ConstrID.Map.insert id NONE m
           | SOME _ => raise DuplicateConstructor(id)
      end

      fun cons_d2 (s, ty, m) =
      let val id = ConstrID.from_string s in
        case ConstrID.Map.lookup id m of
             NONE   => ConstrID.Map.insert id (SOME ty) m
           | SOME _ => raise DuplicateConstructor(id)
      end

      fun empty_datatype () = ConstrID.Map.empty
      val head_d1 = cons_d1
      val head_d2 = cons_d2

      fun bar () = ()
      fun no_bar () = ()

      fun val_binding1 (p, e)       = V(p, e)
      fun val_binding2 (s, vs, ps, e)   = F(ValID.from_string s, vs, ps, e)
      fun val_rec_binding (s, ps, e, m) = Rec(ValID.Map.insert (ValID.from_string s) (ps, e) m)

      type val_rec_map = (Expr.params * Expr.t) ValID.Map.t
      fun empty_val_rec () = ValID.Map.empty
      fun val_rec_and (s, ps, e, m) = ValID.Map.insert (ValID.from_string s) (ps, e) m

      fun ann_seal s = Seal s
      fun ann_ascribe s = Ascribe s
      fun no_sig_ann () = None

      val val_binding_              = Val
      fun type_binding (id, vs, ty) = Type(TypeID.from_string id, vs, ty)
      fun module_binding (id, ps, a, m) = Module(ModuleID.from_string id, ps, a, m)
      fun signature_binding (id, s) = Signature(SignatureID.from_string id, s)
      fun include_binding m         = Include m
      fun datatype_binding (s, vs, m, xs) = Datatype(NonEmpty.make (TypeID.from_string s, vs, m) xs)

      type mparam_list = mparam list
      fun empty_mparam_list () = []
      fun mparam_list_from_non_empty ps = NonEmpty.to_list ps
    end

    fun quote_ident s = TypeVar.from_string s

    type type_var_acc = type_vars * unit TypeVar.Map.t

    fun empty_type_vars () = ([], TypeVar.Map.empty)

    fun cons_type_vars (v, (l, vs)) =
      case TypeVar.Map.lookup v vs of
           SOME() => raise DuplicateTypeVar(v)
         | NONE   => (v :: l, TypeVar.Map.insert v () vs)

    fun from_type_vars_acc (l, _) = l

    fun sig_atom s = s
    fun sig_where s = s
    fun paren_signature s = s

    local open Signature in
      val decls = Decls
      fun signature_ident s = Path(Path.Ident $ SignatureID.from_string s)
      fun sig_path (m, ss) = Path(from_uids1 m ss SignatureID.from_string)
      fun where_type (s, (xs, t), ty) = WhereType(s, (xs, t), ty)
      fun where_type_destructive (s, (xs, t), ty) = DestructType(s, (xs, t), ty)
      fun impure_functor (id, s1, s2) = Fun(ModuleID.from_string id, s1, s2)
      fun impure_functor_simple (s1, s2) = raise TODO
      val let_sig = Let

      fun empty_decls () = Nil
      val cons_decls = Cons
      val open_decl = Open
    end

    type long_type = location
    fun short_type_ident s = ([], TypeID.from_string s)
    fun long_type_ident (s, (xs, t)) = (ModuleID.from_string s :: xs, t)

    local open Decl in
      fun val_decl (s, vs, ty) = Val(ValID.from_string s, vs, ty)
      fun transparent_type_decl (s, vs, ty) = Type(TypeID.from_string s, vs, Transparent ty)
      fun opaque_type_decl (id, vs) = Type(TypeID.from_string id, vs, Opaque)
      fun module_decl (id, ps, s) = Module(ModuleID.from_string id, ps, s)
      fun signature_decl (id, s) = Signature(SignatureID.from_string id, s)
      val include_decl = Include
      fun datatype_decl (s, vs, m, xs) = Datatype(NonEmpty.make (TypeID.from_string s, vs, m) xs)
    end

    fun expr_atom e = e
    fun expr_app e = e
    fun expr_binary e = e

    local open Literal in
      fun number n = Int n
      fun char_literal c = Char c
      fun string_literal s = String s
      fun bool_false () = Bool false
      fun bool_true () = Bool true
    end

    local open Expr BinOp in
      fun lit l = Lit l
      fun val_ident s = Path(Path.Ident $ ValID.from_string s)
      fun expr_path (m, ss) = Path(from_uids1 m ss ValID.from_string)
      val let_expr = Let
      val lambda = Abs
      val app = App
      val if_expr = If
      fun constructor s = Constructor $ Path.Ident $ ConstrID.from_string s
      fun constructor_path (m, ss) = Constructor $ from_uids1 m ss ConstrID.from_string
      fun pack (m, s) = Pack(m, s)
      fun list es = List es
      fun cons_list_expr (e, es) = ConsList(e, es)

      type expr_list = expr list

      fun empty_list () = []
      fun singleton_list e = [e]
      fun cons_list (e, es) = e :: NonEmpty.to_list es

      fun singleton_non_empty e = NonEmpty.singleton e
      fun cons_non_empty (e, es) = NonEmpty.cons e es

      type expr_non_empty = expr non_empty
      fun expr1 e = NonEmpty.singleton e
      fun cons_expr (e, es) = NonEmpty.cons e es

      fun tuple_or_paren es =
        case NonEmpty.uncons es of
             (e, []) => e
           | (e, es) => Tuple(e :: es)

      fun param1 p = NonEmpty.singleton p
      fun cons_params (p, ps) = NonEmpty.cons p ps

      fun match (e, bs) = Match(e, bs)
      fun function bs = Function(bs)

      type branch = branch
      type branches = branches

      fun branch_expr (p, e) = (p, e)

      fun empty_branches () = []
      fun empty_branches1 () = []
      fun cons_branches (b, bs) = b :: bs
      val cons_branches1 = cons_branches

      fun expr_dollar (e1, e2) = App(e1, e2) (* `E1 $ E2` syntactically equals `E1 E2` *)

      fun bin_op b (e1, e2) = BinOp(b, e1, e2)

      val expr_plus        = bin_op Plus
      val expr_minus       = bin_op Minus
      val expr_times       = bin_op Times
      val expr_gt          = bin_op GT
      val expr_lt          = bin_op LT
      val expr_gt_eq       = bin_op GT_EQ
      val expr_lt_eq       = bin_op LT_EQ
      val expr_gt_gt_gt    = bin_op GT_GT_GT
      val expr_lt_lt_lt    = bin_op LT_LT_LT
      val expr_equal_equal = bin_op EqualEqual
      val expr_slash_equal = bin_op SlashEqual
      val expr_lt_gt       = bin_op LT_GT
      val expr_lt_plus_gt  = bin_op LT_Plus_GT
    end

    local open Pattern in
      fun wildcard () = Wildcard()
      fun constructor_pattern1 s = Constructor(Path.Ident $ ConstrID.from_string s, NONE)
      fun constructor_pattern2 (s, p) = Constructor(Path.Ident $ ConstrID.from_string s, SOME p)
      fun var_pattern s = Var(ValID.from_string s, ())
      fun typed_pattern (p, ty) = Typed(p, ty)

      fun constructor_path_pattern1 (m, ss) = Constructor(from_uids1 m ss ConstrID.from_string, NONE)
      fun constructor_path_pattern2 (m, ss, p) = Constructor(from_uids1 m ss ConstrID.from_string, SOME p)

      val cons_list_pattern = ConsList

      type pattern_non_empty = pattern non_empty
      fun pattern1 p = NonEmpty.singleton p
      fun cons_pattern (p, ps) = NonEmpty.cons p ps

      fun tuple_or_paren_pattern ps =
        case NonEmpty.uncons ps of
             (p, []) => p
           | (p, ps) => Tuple(p :: ps)

      fun nil_pattern () = NilList

      fun pattern_atom x = x
      fun pattern_term x = x
      fun pattern_infix x = x
    end

    fun paren_type ty = ty
    fun type_atom ty = ty
    fun type_arrow ty = ty

    local open Type in
      type type_list = typ non_empty
      fun type_app ty = NonEmpty.singleton ty
      fun cons_tuple (ty, tys) = NonEmpty.cons ty tys

      fun tuple_type tys =
        case NonEmpty.uncons tys of
             (ty, [])  => ty
           | (ty, tys) => Tuple(ty :: tys)

      fun type_ident s = Path(Path.Ident $ TypeID.from_string s)
      fun arrow (xs, y) = Arrow(tuple_type xs, y)
      fun type_path (m, ss) = Path(from_uids1 m ss TypeID.from_string)
      val type_variable = Var
      val app_type = App
      val let_type = Let
      val package_type = Pack
    end

    local open Unit in
      type program_unit = t
      type submodule = submodule

      fun submodule_include s = Include s
      fun submodule_bind (id, s) = Bind(ModuleID.from_string id, s)

      fun unit_bindings bs = ([], bs)
      fun unit_cons (s, (ss, bs)) = (s :: ss, bs)
    end

    datatype terminal = datatype Token.t

    fun error s = UnexpectedToken(SOME(Stream.hd s) handle Stream.Empty => NONE)
  end
end)
