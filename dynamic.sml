structure Dynamic = struct
  open Std

  type var = string

  structure VarMap = BinarySearchMap struct
    type t = var

    val compare = String.compare
  end

  structure Pattern = struct
    datatype t
      = Wildcard
      | Var of var
      | Constructor of constr_ident * t option
      | Tuple of t list
  end

  type pattern = Pattern.t

  structure Literal = Syntax.Literal

  datatype t
    = Var of var
    | Abs of var * t
    | App of t * t
    | Record of t Record.t
    | Tuple of t list
    | Proj of t * label
    | Let of var * t * t
    | Lit of Literal.t
    | List of t list
    | ConsList of t * t
    | If of t * t * t
    | Constructor of constr_ident
    | Match of t * branches
    | LetRec of (var * t) list * t

  withtype branch = pattern * t
  and branches = (pattern * t) list

  fun expect s (SOME x) = x
    | expect s NONE     = raise Fail s

  structure Sem = struct
    datatype t
      = Lit of Literal.t
      | Fun of t -> t
      | Record of t Record.t
      | Tuple of t list
      | List of t list
      | Constructor of constr_ident * t option
      | Ref of t ref

    datatype u
      = Value of t
      | Loc of t option ref

    fun deref (Loc r)   = !r |> expect "deref"
      | deref (Value s) = s

    val unit = Lit Literal.Unit

    fun get_int (Lit (Literal.Int v)) = v
      | get_int _                     = raise Fail "not int"

    fun get_bool (Lit (Literal.Bool v)) = v
      | get_bool _                      = raise Fail "not bool"

    fun get_string (Lit (Literal.String v)) = v
      | get_string _                        = raise Fail "not string"

    fun get_record (Record m) = m
      | get_record _          = raise Fail "not record"

    fun get_list (List xs) = xs
      | get_list _         = raise Fail "not list"

    fun get_ref (Ref r) = r
      | get_ref _       = raise Fail "not reference"

    fun fun2 f = Fun (fn s1 => Fun (fn s2 => f (s1, s2)))
  end

  structure Env : sig
    type t

    val initial : t

    exception Unbound of var

    val insert_value : var -> Sem.t -> t -> t
    val lookup : var -> t -> Sem.u
  end = struct
    type t = Sem.u VarMap.t

    fun insert_value v s = VarMap.insert v (Sem.Value s)

    exception Unbound of var

    fun lookup v env =
      case VarMap.lookup v env of
           SOME x => x
         | NONE  => raise Unbound(v)

    fun compare_int (s1, s2) =
    let
      val n1 = Sem.get_int s1
      val n2 = Sem.get_int s2
      val s =
        case Int.compare (n1, n2) of
             LESS    => "LT"
           | EQUAL   => "EQ"
           | GREATER => "GT"
    in
      Sem.Constructor(ConstrID.from_string s, NONE)
    end

    fun compare_string (s1, s2) =
    let
      val s1 = Sem.get_string s1
      val s2 = Sem.get_string s2
      val s =
        case String.compare (s1, s2) of
             LESS    => "LT"
           | EQUAL   => "EQ"
           | GREATER => "GT"
    in
      Sem.Constructor(ConstrID.from_string s, NONE)
    end

    val initial_modules = VarMap.from_list $
      List.map (fn (x, s) => (Label.encode $ Label.module $ ModuleID.from_string x, Sem.Value s))
      [ ( "MakeRef"
        , Sem.Fun (fn _ => Sem.Record $ Record.from_list $
            map (fn (x, y) => (Label.value $ ValID.from_string x, y))
            [ ("make", Sem.Fun (fn s1 => Sem.Ref $ ref s1))
            , ("get", Sem.Fun (fn s1 => !(Sem.get_ref s1)))
            , ("set", Sem.fun2 (fn (s1, s2) => Sem.unit before Sem.get_ref s1 := s2))
            ])
        )
      ]

    val initial = VarMap.union initial_modules $ VarMap.from_list $
      List.map (fn (x, s) => (Label.encode $ Label.value $ ValID.from_string x, Sem.Value s))
      [ ( "print_endline"
        , Sem.Fun (fn s => Sem.Lit Literal.Unit before print (Sem.get_string s ^ "\n"))
        )
      , ( "show_int"
        , Sem.Fun (fn s => Sem.Lit $ Literal.String $ Int.toString $ Sem.get_int s)
        )
      , ( "concat_string"
        , Sem.fun2 (fn (s1, s2) => Sem.Lit $ Literal.String $ Sem.get_string s1 ^ Sem.get_string s2)
        )
      , ( "+"
        , Sem.fun2 (fn (s1, s2) => Sem.Lit $ Literal.Int $ Sem.get_int s1 + Sem.get_int s2)
        )
      , ( "-"
        , Sem.fun2 (fn (s1, s2) => Sem.Lit $ Literal.Int $ Sem.get_int s1 - Sem.get_int s2)
        )
      , ( "*"
        , Sem.fun2 (fn (s1, s2) => Sem.Lit $ Literal.Int $ Sem.get_int s1 * Sem.get_int s2)
        )
      , ("compare_int", Sem.fun2 compare_int)
      , ("compare_string", Sem.fun2 compare_string)
      ]
  end

  fun zip [] []               = []
    | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
    | zip _ _                 = []

  infix >>=

  fun NONE >>= _     = NONE
    | (SOME x) >>= f = f x

  fun pattern_match env p s : Env.t option =
    case (p, s) of
         (Pattern.Wildcard, _) => SOME env
       | (Pattern.Var v, _)    => SOME $ Env.insert_value v s env
       | (Pattern.Constructor(id1, p_opt), Sem.Constructor(id2, s_opt)) =>
           if ConstrID.eq (id1, id2)
           then
             case (p_opt, s_opt) of
                  (NONE, NONE)     => SOME env
                | (SOME p, SOME s) => pattern_match env p s
                | _                => raise Fail "argument mismatch"
           else NONE
       | (Pattern.Tuple ps, Sem.Tuple ss) =>
           let
             val xs = zip ps ss
           in
             foldl (fn ((p, s), acc) => acc >>= (fn acc' => pattern_match acc' p s)) (SOME env) xs
           end
       | (Pattern.Constructor(id, p_opt), Sem.List ss) =>
           if ConstrID.eq(id, ConstrID.from_string "[]")
           then
             case ss of
                  [] => SOME env
                | _  => NONE
           else if ConstrID.eq(id, ConstrID.from_string "::")
           then
             case ss of
                  []      => NONE
                | x :: xs => pattern_match env (expect "::" p_opt) $ Sem.Tuple [x, Sem.List xs]
           else NONE
       | _ => NONE

  fun eval env (Var v)     = Env.lookup v env |> Sem.deref
    | eval env (Abs(v, x)) = Sem.Fun(fn s => eval (Env.insert_value v s env) x)
    | eval env (App(x, y)) =
        let
          val s1 = eval env x
          val s2 = eval env y
        in
          case s1 of
               Sem.Fun f                 => f s2
             | Sem.Constructor(id, NONE) => Sem.Constructor(id, SOME s2)
             | _                         => raise Fail "could not apply"
        end
    | eval env (Record m)   = Sem.Record $ Record.map (eval env) m
    | eval env (Tuple xs)   = Sem.Tuple $ map (eval env) xs
    | eval env (Proj(x, l)) =
        let val r = eval env x |> Sem.get_record in
          case r |> Record.lookup l of
               SOME s => s
             | NONE   => raise Fail ("projection: " ^ Label.encode l ^ " from " ^ Int.toString (Record.size r))
        end
    | eval env (Let(v, x, y)) =
        let val s1 = eval env x in
          eval (Env.insert_value v s1 env) y
        end
    | eval env (Lit l) = Sem.Lit l
    | eval env (List xs) = Sem.List $ List.map (eval env) xs
    | eval env (ConsList(x, y)) =
        let
          val h = eval env x
          val t = eval env y |> Sem.get_list
        in
          Sem.List $ h :: t
        end
    | eval env (If(x, y, z)) =
        let
          val s1 = eval env x
        in
          if Sem.get_bool s1
          then eval env y
          else eval env z
        end
    | eval env (Constructor id) = Sem.Constructor(id, NONE)
    | eval env (Match(x, bs)) =
        let
          val s1 = eval env x

          fun f []             = raise Fail "no match"
            | f ((p, y) :: bs) =
              case pattern_match env p s1 of
                   SOME env' => eval env' y
                 | NONE      => f bs
        in
          f bs
        end
    | eval env (LetRec(xs, y)) =
        let
          val xs = map (fn (v, x) => (v, x, ref NONE)) xs
          val env1 = foldl (fn ((v, _, r), acc) => VarMap.insert v (Sem.Loc r) acc) env xs
          val () = List.app (fn (_, x, r) => let val s = eval env1 x in r := SOME s end) xs
        in
          eval env1 y
        end
end
