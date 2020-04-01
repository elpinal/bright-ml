open Std

signature SYNTAX = rec (X : sig
  structure Signature : sig
    type t
  end

  structure Module : sig
    type t
    type bindings
    type param
  end
end) sig
  structure Path : sig
    datatype 'a t
      = Ident of 'a
      | Proj of X.Module.t * 'a

    val show : ('a -> string) -> 'a t -> string
  end

  structure Type : sig
    datatype t
      = Path of type_ident Path.t
      | Let of X.Module.bindings * t
      | Var of type_var
      | App of t * t
      | Arrow of t * t
      | Tuple of t list
      | Pack of X.Signature.t
  end

  structure Literal : sig
    datatype t
      = Int of int
      | Bool of bool
      | Char of char
      | String of string
      | Unit

    val show : t -> string
  end

  structure Pattern : sig
    datatype 'a t
      = Wildcard of 'a
      | Var of val_ident * 'a
      | Constructor of constr_ident Path.t * 'a t option
      | Typed of 'a t * Type.t
      | Tuple of 'a t list
      | NilList
      | ConsList of 'a t * 'a t

    type untyped = unit t

    val show : 'a t -> string
  end

  structure BinOp : sig
    datatype t
      = Plus
      | Minus
      | Times
      | GT
      | LT
      | GT_EQ
      | LT_EQ
      | GT_GT_GT
      | LT_LT_LT
      | EqualEqual
      | SlashEqual
      | LT_GT
      | LT_Plus_GT

    val to_ident : t -> val_ident
  end

  structure Expr : sig
    type param = Pattern.untyped
    type params = param non_empty

    datatype t
      = Path of val_ident Path.t
      | Let of X.Module.bindings * t
      | Abs of params * t
      | App of t * t
      | Lit of Literal.t
      | List of t list
      | ConsList of t * t
      | Tuple of t list
      | If of t * t * t
      | Constructor of constr_ident Path.t
      | Match of t * branches
      | Function of branches
      | Pack of X.Module.t * X.Signature.t
      | BinOp of BinOp.t * t * t
      | Open of X.Module.t * t
      | ValOp of val_ident * Pattern.untyped * t * t

    withtype branch = Pattern.untyped * t
    and branches = (Pattern.untyped * t) list

    val show : t -> string
  end

  type datatype_binding = type_ident * type_vars * Type.t option ConstrID.Map.t

  structure Decl : sig
    datatype type_decl
      = Transparent of Type.t
      | Opaque

    datatype t
      = Val of val_ident * type_vars * Type.t
      | Type of type_ident * type_vars * type_decl
      | Datatype of datatype_binding non_empty (* TODO: we may want `withtype` *)
      | Module of module_ident * X.Module.param list * X.Signature.t
      | Signature of signature_ident * X.Signature.t
      | Include of X.Signature.t
  end

  structure Signature : sig
    datatype decls
      = Nil
      | Cons of Decl.t * decls
      | Open of X.Module.t * decls

    datatype t
      = Path of signature_ident Path.t
      | Fun of module_ident option * t * t (* impure functor *)
      | WhereType of t * location * type_vars * Type.t
      | DestructType of t * location * type_vars * Type.t (* destructive substitution *)
      | Decls of decls
      | Let of X.Module.bindings * t
  end

  structure Binding : sig
    datatype val_binding
      = V of Pattern.untyped * Expr.t
      | F of val_ident * type_vars * Expr.params * Expr.t (* function binding *)
      | Rec of (Expr.params * Expr.t) ValID.Map.t (* recursive function bindings *)

    datatype signature_ann
      = None
      | Seal of Signature.t
      | Ascribe of Signature.t

    datatype t
      = Val of val_binding
      | Type of type_ident * type_vars * Type.t
      | Datatype of datatype_binding non_empty (* TODO: we may want `withtype` *)
      | Module of module_ident * X.Module.param list * signature_ann * X.Module.t
      | Signature of signature_ident * Signature.t
      | Include of X.Module.t

    val show : t -> string
  end

  structure Module : sig
    datatype bindings
      = Nil
      | Cons of Binding.t * bindings
      | Open of X.Module.t * bindings

    type param = module_ident * Signature.t
    type params = param non_empty

    datatype t
      = Ident of module_ident
      | Proj of t * module_ident
      | Seal of t * Signature.t
      | Ascribe of t * Signature.t
      | App of t * t
      | Fun of params * t
      | Bindings of bindings
      | Let of bindings * t
      | Unpack of Expr.t * Signature.t

    val show_bindings : bindings -> string
    val show : t -> string
  end

  structure Unit : sig
    datatype submodule_path
      = Std
      | Relative of string

    datatype submodule
      = Include of submodule_path
      | Bind of module_ident * submodule_path

    type t = submodule list * Module.bindings

    val show : t -> string

    val add_std : t -> t
  end
end

structure Syntax : SYNTAX = rec (X : SYNTAX) struct
  structure Type = struct
    datatype t = datatype X.Type.t
  end

  structure Literal = struct
    datatype t = datatype X.Literal.t

    fun show (Int n)    = Int.toString n
      | show (Bool b)   = Bool.toString b
      | show (Char c)   = Char.toString c
      | show (String s) = String.toString s
      | show Unit       = "()"
  end

  structure Pattern = struct
    datatype t = datatype X.Pattern.t
    type untyped = X.Pattern.untyped

    fun get_ident (X.Path.Ident id) = ConstrID.get_name id
      | get_ident (X.Path.Proj(_, id)) = "..." ^ ConstrID.get_name id

    fun show_tuple [] = ""
      | show_tuple [s] = s
      | show_tuple [s1, s2] = s1 ^ ", " ^ s2
      | show_tuple (s :: ss) = s ^ ", " ^ show_tuple ss

    fun paren s = "(" ^ s ^ ")"

    fun show (Wildcard _)  = "_"
      | show (Var(id, _))  = ValID.get_name id
      | show (Typed(p, _)) = show p ^ " : _"
      | show (Tuple ps)    = paren (show_tuple (map show ps))
      | show NilList       = "[]"
      | show (ConsList(p1, p2)) = paren (show p1) ^ " :: " ^ paren (show p2)
      | show (Constructor(p, p_opt)) =
          case p_opt of
               SOME x => get_ident p ^ " " ^ paren (show x)
             | NONE   => get_ident p
  end

  structure BinOp = struct
    datatype t = datatype X.BinOp.t

    val to_ident =
    let
      fun f Plus       = "+"
        | f Minus      = "-"
        | f Times      = "*"
        | f GT         = ">"
        | f LT         = "<"
        | f GT_EQ      = ">="
        | f LT_EQ      = "<="
        | f GT_GT_GT   = ">>>"
        | f LT_LT_LT   = "<<<"
        | f EqualEqual = "=="
        | f SlashEqual = "/="
        | f LT_GT      = "<>"
        | f LT_Plus_GT = "<+>"
    in
      ValID.from_string o f
    end
  end

  structure Expr = struct
    type param = X.Expr.param
    type params = X.Expr.params
    type branch = X.Expr.branch
    type branches = X.Expr.branches
    datatype t = datatype X.Expr.t

    local open Pretty in
      fun show (Path p) = X.Path.show ValID.get_name p
        | show (Lit l)  = Literal.show l
        | show _        = raise TODO
    end
  end

  type datatype_binding = X.datatype_binding

  structure Decl = struct
    datatype type_decl = datatype X.Decl.type_decl
    datatype t = datatype X.Decl.t
  end

  structure Signature = struct
    datatype decls = datatype X.Signature.decls
    datatype t = datatype X.Signature.t
  end

  structure Binding = struct
    datatype val_binding = datatype X.Binding.val_binding
    datatype signature_ann = datatype X.Binding.signature_ann
    datatype t = datatype X.Binding.t

    local open Pretty in
      fun show (Val(V(p, e)))        = "val" <+> Pattern.show p <+> "=" <+> Expr.show e
        | show (Module(id, _, _, m)) = "module" <+> ModuleID.get_name id <+> "..." <+> "=" <+> X.Module.show m
        | show _                     = raise TODO
    end
  end

  structure Module = struct
    datatype bindings = datatype X.Module.bindings
    type param = X.Module.param
    type params = X.Module.params
    datatype t = datatype X.Module.t

    local open Pretty in
      fun show_bindings Nil           = ""
        | show_bindings (Cons(b, bs)) = Binding.show b <+> show_bindings bs
        | show_bindings _             = raise TODO

      fun show (Ident id)    = ModuleID.get_name id
        | show (Proj(m, id)) = show m <> "." <> ModuleID.get_name id
        | show (Bindings bs) = "struct" <+> show_bindings bs <+> "end"
        | show _             = raise TODO
    end
  end

  structure Path = struct
    datatype t = datatype X.Path.t

    local open Pretty in
      fun show f (Ident id)    = f id
        | show f (Proj(m, id)) = Module.show m <> "." <> f id
    end
  end

  structure Unit = struct
    datatype submodule_path = datatype X.Unit.submodule_path
    datatype submodule = datatype X.Unit.submodule

    type t = X.Unit.t

    fun show (_, bs) = Module.show_bindings bs

    fun add_std (ss, bs) = (Include Std :: ss, bs)
  end
end
