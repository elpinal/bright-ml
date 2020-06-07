# Bright ML

Bright ML is a statically-typed programming language, based on "F-ing modules".
This repository contains an interpreter of Bright ML, written in Moscow ML.

## Features
  - Type inference
  - Mutually-recursive datatypes
  - Mutually-recursive functions
  - "F-ing modules"-based module system
  - First-class packaged modules
  - Destructive substitution
  - No value restriction
  - Bottom type (empty datatypes)
  - Exhaustivity and redundancy check of patterns
  - Binding operators

## Getting started

You need the [Moscow ML](https://mosml.org) compiler and [cmtool](http://www.cs.cmu.edu/~crary/cmtool/).
Make sure that `mosmlc`, `cmlex` and `cmyacc` are in your `$PATH`.

```bash
$ git clone --recursive https://github.com/elpinal/bright-ml
$ cd bright-ml
$ make

$ ./bright-ml -h
```

## Overview

```
// This is a comment.

// Bind `x` to 1.
val x = 1

// Bind `f` to a function.
val f x y = (x + y, x - y)

// Bind `fact` to a recursive function.
val rec fact n =
  if 0 < n
  then n * fact (n - 1)
  else 1

// Type synonym. We can use `t` and `int` interchangeably.
type t = int

// Datatype definition.
datatype t = A of t

// Signature binding.
signature S = sig
  type t
end

// Module binding.
module M = struct
  val x = [1, 2, 3]
end

// Functor binding.
module F (X : S) = struct
  type t = X.t
  val v x = print_endline x
end

// Include a module.
include M

// Open a module.
open M

// Like Haskell's `$`, `$` can be used to omit parentheses for function applications.
val _ = succ $ succ n   // Syntactically the same as `succ (succ n)`.

// We can use an alternative syntax `{ ... }` to write
// structures (`struct ... end`) or structure signatures (`sig ... end`).
module M : {type t type u = t val x : t * u} = {type u = int type t = u val x = (5, 4)}
```

### Mutually-recursive definitions

The following example is adopted from [Nakata and Garrigue 2006](http://www.math.nagoya-u.ac.jp/~garrigue/papers/nakata-icfp2006.pdf).

```
// Mutually-recursive datatypes.
datatype tree =
  | Leaf of int
  | Node of int * forest

and forest =
  | Forest of list tree

// Mutually-recursive functions.
val rec max t = match t with
  | Leaf n     -> n
  | Node(n, f) -> Int.max n $ max_forest f
end

and max_forest f = match f with
  | Forest []       -> 0
  | Forest(t :: ts) -> Int.max (max t) $ max_forest $ Forest ts
end
```

### F-ing modules

Bright ML's module system is almost the same as [F-ing modules](https://people.mpi-sws.org/~rossberg/f-ing/f-ing-jfp.pdf) with first-class packaged modules, without applicative functors.

```
signature S = sig
  type t
  val f 'a : 'a -> 'a
end

// Higher-order (generative) functor.
module F (X : (Y : S) -> S) = struct
  val v =
    let module M = X struct
      type t = bool
      val f x = x
    end
    in M.f "a"
end

// Signature refinement: `where type`.
signature T = S where type t = int

// `let` can be used inside types.
type t =
  let signature S = sig
    type t = int
    val x : t -> t
  end in
  pack S
```

Bright ML's `open` is very general, like [OCaml's generalized `open`](https://www.cl.cam.ac.uk/~jdy22/papers/extending-ocamls-open-draft.pdf).

```
// We can open a module identifier.
open List

// We can open the resulting structure of functor application.
open F M

include struct
  // The scope of `t` and `C` is the rest of the surrounding module.
  open struct
    datatype t = C of int
  end

  val x = C 8
  val y = x
  val f = function
    | C n -> C $ n + 1
  end
end

// We cannot access `C`.
// val _ = C

val _ = f $ f y
```

The following ascribed signature is expressible only via generalized `open` or destructive substitution.

```
module M : sig
  type t

  // This is important.
  open struct
    type t' = t
  end

  module N : sig
    type t

    val f : t' -> t
  end
end = struct
  datatype t = A1

  module N = struct
    datatype t = A2

    val f = function
      | A1 -> A2
    end
  end
end
```

### Destructive substitution

Like OCaml, Bright ML supports [destructive substitution](http://www.math.nagoya-u.ac.jp/~garrigue/papers/ml2010.pdf).
The syntax is `where type <qualified-identifier> := <type>`.
In the following example, `Show` and `Eq` both have a type component `t`.
Using destructive substitution, we can combine these signatures into one.

```
signature Show = sig
  type t

  val show : t -> string
end

signature Eq = sig
  type t

  val `==` : t -> t -> bool
end

signature Int = sig
  type t

  include Show where type t := t
  include Eq where type t := t
end
```

### Explicit universal quantification

In Bright ML, all type variables must be bound explicitly,
not only because Standard ML's implicit scoping rules are brittle,
but also because Bright ML is much similar to System Fω, rather than Hindley–Milner type system,
thanks to the liberal and expressive module system.
(Note that the core language itself is Hindley–Milner type system.)

```
signature S = sig
  type t 'a

  // Type variables `'a` and '`b` must be quantified explicitly.
  val map 'a 'b : ('a -> 'b) -> t 'a -> t 'b
end
```

```
// Implicit polymorphism is one of the virtues of ML.
// This function has type `∀α. α -> α`.
val id x = x
// If we want to annotate `x` with a type which contains type variables,
// we need to explicitly bind them.
val id 'a (x : 'a) = x

// This form is ill-typed because `'a` is an unbound type variable.
// val id (x : 'a) = x
```

Bright ML's explicit scoping of type variables dispenses with GHC's "scoped type variables" or OCaml's "locally abstract types".

```
val f 'a (x : 'a) (size : 'a -> int) =
  let val g (y : 'a) = size y in
  g x
```

### First-class packaged modules

Any modules can be turned into first-class values.
An expression of the form `pack M : S` is a first-class value encapsulating a module expression `M`
which matches a signature expression `S`.
Such an expression, or a package, has type `pack S`.

Unpacking of packages is done via a construct `unpack E : S`,
which project out a module of signature `S` inside an expression `E`.

```
module List : sig
  val fold 'a : pack (Monoid.S where type t = 'a) -> list 'a -> 'a
end = struct
  val fold 'a m xs =
    let module M = unpack m : Monoid.S where type t = 'a in
    fold_left M.`<>` M.empty xs
end
```

### No value restriction

Bright ML is an impure language.
However, unlike Standard ML or OCaml, it doesn't have *polymorphic* mutable references or something alike,
thus in Bright ML, any expression can be generalized at `val`-bindings.

```
module M : sig
  val id 'a : 'a -> 'a
  val v 'a : list ('a -> 'a)
end = struct
  val id x = x

  // This expression can be given a polymorphic type while it is not a syntactic value.
  val v = id [fun x -> x]
end
```

That said, we sometimes want mutable references, so Bright ML supports *monomorphic* mutable references.
More precisely, we can generate monomorphic mutable reference **types** at any given types using a generative functor `Ref.Make`
in the standard library.
We can use mutable references without compromising type soundness,
while keeping every expression polymorphic.

```
module IntListRef = Ref.Make {type t = list int}
val r = IntListRef.make [] // This expression has abstract type `IntListRef.t`.
val xs = 1 :: IntListRef.get r
val _ = IntListRef.set r $ List.map (fun n -> n * 2) xs
val _ = IntListRef.get r // This expression has type `list int`.
```

One drawback of this approach is that we cannot write recursive datatypes in terms of their references.
For example, the following, valid Standard ML code cannot be written in Bright ML.

```sml
datatype t =
    A
  | B of t ref
```

### Empty datatypes and exhaustivity

Empty datatypes can be used to indicate that values of such types never appear at run-time.

```
datatype result 'e 'a =
  | Err of 'e
  | Ok of 'a

signature FromStr = sig
  type t
  type err

  val from_str : string -> result err t
end

// `bottom` is an empty datatype.
datatype bottom = |

// The type of `X.from_str` means it never fails.
module F (X : FromStr where type err := bottom) = struct
  val _ =
    // This pattern matching is exhaustive since the `bottom` type cannot be inhabited.
    match X.from_str "hello" with
      | Ok v -> v
    end
end
```

Also, empty datatypes can be used as phantom types.

```
module M :> sig
  type t 'a

  datatype int' = |
  datatype bool' = |

  val int : int -> t int'
  val bool : bool -> t bool'
  val succ : t int' -> t int'
end = struct
  datatype int' = |
  datatype bool' = |

  datatype t 'a =
    | Int of int
    | Bool of bool
    | Succ of t int'

  val int = Int
  val bool = Bool
  val succ = Succ
end

open struct
  open M

  val x = int 4
  val y = bool true

  val z = succ x
  // We cannot apply `succ` to `y` because `y` has type `M.t bool'`.
  // val z = succ y
end
```

### Binding operators

Bright ML supports binding operators [like OCaml](https://caml.inria.fr/pub/docs/manual-ocaml-4.10/bindingops.html),
making monadic operations handy.

```
// Define `val+` as a binding operator.
val `val+` x f =
  match x with
    | None   -> None
    | Some x -> f x
  end

include struct
  val f a b =
    // `a` has type `option int` while `x` has type `int`.
    val+ x = a in
    val+ y = b in
    Some $ x * y
end : sig
  val f : option int -> option int -> option int
end
```

## Test

To run test, [`go`](https://golang.org) is required.

```bash
$ make test
```
