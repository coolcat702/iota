# Iota

Iota is a minimal functional programming language designed to feel as close as possible to pure functions
while remaining practical for everyday programming tasks. It draws conceptual inspiration from
Haskell, F#, and combinatory logic but takes away syntactic noise and built‑in operators so everything is
expressed with functions and types.
In Iota:

- There are no infix value‑level operators; everything is defined as a function.
- The type system is algebraic and explicit, using `+` and `*` for sums and products, and `-> for functions.
- Control flow and effects are modeled via church pattern matching and monadic types
  like Maybe and Either rather than imperative statements.

Iota is well‑suited for:

- Teaching and exploring functional programming and type theory in a clean, uniform syntax.
- Writing highly composable, point‑free pipelines where data flows linearly through functions.
- Modeling math‑heavy or domain‑specific computations where the boundary between "math" and "code" should be as thin as possible.

## Contents

- [Contents](#contents)
- [Building and Running](#building-and-running)
- [Defining Variables](#defining-variables)
- [Functions](#functions)
- [Pattern Matching](#pattern-matching)
- [With Clauses](#with-clauses)
- [Composition Operators](#composition-operators)
- [Combinators](#combinators)
- [Default Types](#default-types)
- [Algebraic Types](#algebraic-types)
- [Lists](#lists)
- [Conditionals](#conditionals)
- [Type Classes](#type-classes)
- [Type Constraints](#type-constraints)
- [Ranges](#ranges)
- [Modules and Imports](#modules-and-imports)
- [Error Handling](#error-handling)
- [Monads](#monads)
- [Examples](#examples)

## Building and running

```
cargo build --release                      # needs LLVM 22.1 (see below) and clang at run time
iota examples/factorial.iota -o fact --run     # compile, link, run
iota prog.iota --emit ir                   # monomorphic typed ANF IR after optimization
iota prog.iota --emit mir                  # instances, data layouts, strict/borrowed parameters
iota prog.iota --emit llvm -o prog.ll      # textual LLVM IR
iota prog.iota --opt-mode aggressive -v    # inlining + partial evaluation; narrate every stage
```

The prelude, the lang manifest (`prelude/lang.def`) and the C runtime are embedded in the compiler
binary (override with `--prelude`, `--lang`). Diagnostics are rendered with
`ariadne` on stderr by `main.rs`.

## Defining Variables

Define a variable using `let`:

```iota
let x : Int = 20
end
```

## Functions

Define a function using the type `T -> U`. A function value is defined with `fn x -> M end`.

```iota
let f
    : Int -> Int
    = fn x -> mul 2 x end
end
```

## Pattern Matching

You can use pattern matching with a `match` expression:

```iota
match
    pat1 -> expr1 end
    pat2 -> expr2 end
    ...
end (expr)
```

A `match` expression finds the first pattern that matches the values it is applied to.
Then, it applies the matching expression to those values.

A `_` in a match pattern matches anything and discards it.

```iota
let safe_div
    : Float -> Float -> Float
    = match
        _, 0.0 -> 0.0     end
        x, y   -> div x y end
    end
end
```

## With Clauses

Define a scoped helper function using `with`:

```iota
let filter_evens
    : List Int -> List Int
    = filter even
with even
    : Int -> Bool
    = eq 0 < flip mod 2
end
```

You can use multiple `with` clauses:

```iota
let collatz
    : Int -> Int
    = fork (cond even) half next
with even
    : Int -> Bool
    = comp (eq 0) (flip mod 2)
with half
    : Int -> Int
    = flip div 2
with next
    : Int -> Int
    = comp (add 1) (mul 3)
end
```

## Composition Operators

Iota has two composition operators. In order of application, they are:

- `<`: Forward Apply
     - `f < g x = f (g x)`
     - You can think of the argument "flowing" with the arrow into the function.
     - Right-associative: `f < g < h = f < (g < h)`
- `>`: Reverse apply
     - `x > f = f x`
     - Effectively the reverse of `<` (`f > g > h = h < g < f`)
     - Left-associative: `f > g > h = (f > g) > h`

Iota eliminates all value‑level operators.
Only type combinators (`+`, `*`, `->`) and function combinators (<`, `>`) exist.
All other relations are expressed as functions from first principles.

## Combinators

In Iota, combinators are available both by their symbols and descriptive names.

- `I`, `id`
     - `I x = x`
- `K`, `const`
     - `K x y = x`
- `S`, `ap`
     - `S f g x = f x (g x)`
- `C`, `flip`
     - `C a b c = a c b`
- `Phi`, `fork`
     - `Phi f g h x = f (g x) (h x)`
- `D2`, `fork2`
     - `D2 f g h x y = f (g x) (h y)`
- `Psi`, `over`
     - `Psi f g x y = f (g x) (g y)`
- `B`, `comp`
     - `B f g x = f (g x)`
- `B1`, `comp2`
     - `B1 f g x y = f (g x y)`
- `B2`, `comp3`
     - `B2 f g x y z = f (g x y z)`
- `T`, `thrust`
     - `T x f = f x`
- `W`, `join`
     - `W f x = f x x`

It is usually preferred to make functions point-free rather than introducing bound variables.

## Default Types

```
Unit: a type with exactly one value.
Int: signed 32 bit integer
Float: 64 bit floating-point number
Char: one character
a -> b: Function from 'a' to 'b'
(a + b): algebraic sum type including one of a or b (also constructed with 'left' or 'right')
(a * b): algebraic product type including a and b (also constructed with 'pair a b', deconstructed with 'fst' or 'rst')

Other types are defined in the prelude. These include:
type List a = Nil + Cons (a * List a) end
type String = List Char end
type Maybe a = Val a + Nil end
type Either a b = Left a + Right b end
type Bool = False + True end
type Nat = Zero + Succ Nat end
```

## Algebraic Types

Use `*` and `+` to define algebraic types.

```iota
type List a = Nil + Cons (a * List a)
end
```

To instantiate this type:

```iota
let xs
    : List Int
    = List:Cons 1 <
        List:Cons 2 <
            List:Cons 3 <
                List:Cons 4 List:Nil
end
# [1, 2, 3, 4]
```

## Lists

Lists have many functions that operate them, including:

```iota
[1, 2, 3, 4] > map (mul 2)
# [2, 4, 6, 8]

[1, 2, 3, 4] > filter (eq 0 < flip mod 2)
# [2, 4]

zip [1, 3, 5, 7] [2, 4, 6, 8]
# [1 * 2, 3 * 4, 5 * 6, 7 * 8]

zip_with add [1, 2, 3, 4] [4, 5, 6, 7]
# [5, 7, 9, 11]
```

You can create a list literal using `[]`.

```iota
[a, b, c] # = List:Cons (a * List:Cons (b * List:Cons (c * List:Nil)))
```

Since strings are just lists of chars, string literals with `""` are just syntax sugar.

```iota
"hello" # = ['h', 'e', 'l', 'l', 'o'] = List:Cons('h' * List:Cons('e' * List:Cons('l' * List:Cons('l' * List:Cons('o' * List:Nil)))))
```

## Conditionals

Conditionals can be done using `match`, or using `cond`:

```
let cond a
    : Bool -> a -> a -> a
    = match
        Bool:True -> const       end
        Bool:False -> flip const end
    end
end
# Only the branch `c` selects is ever evaluated (arguments are lazy), so it is safe to
# recurse in a branch; `and` and `or` short-circuit the same way.
```

## Type Classes

You can define a type class using `class` for polymorphic behavior. Bindings inside the class are assumed to be undefined.

```iota
# 'is' and 'end' denote the start and end of blocks
class Showable a is
    let show
        : a -> String
    end
end
```

Implement a type class using `instance`.

```iota
instance Showable String is
    let show
        : String -> String
        = id
    end
end
```

### Type Constraints

When using generics, you can ensure that a type implements a class using type constraints.

```iota
class MyAddable a is
    let class_add
        : a -> a -> a
    end
end

# type constraints are a universal qualifier, "for all types a such that a implements MyAddable, this is the type."
# ∀a. MyAddable a => a -> a -> a
let my_add (a : MyAddable)
    : a -> a -> a
    = class_add
end
```

You can also use multiple type constraints:

```iota
# ∀a b. Showable a ∧ Showable b ⇒ a → b → String
let concat_non_strs (a : Showable) (b : Showable)
    : a -> b -> String
    = over concat show
end
```

## Default Type Classes

The default type classes are:

```
Addable, Subable, Mulable, Divable,
Successable,
Orderable, Eqable,
Showable, Parseable,
Functor, Monad,
Default,
```

## Ranges

Ranges are defined using `range`, or alternatively `from` and `to` (or `to_inc`). Because evaluation is
lazy, `from` is a genuinely infinite list; only the part that is looked at is ever built.

```iota
let range (a : Successable, Orderable)
    : a -> a -> List a
    = comp from to
end

let from (a : Successable)
    : a -> List a
    = comp List:Cons < ap pair < comp from succ
end

let to (a : Orderable)
    : List a -> a -> List a
    = flip < comp take_while gr
end
```

## Modules and Imports

Here is an example project structure in iota:

```
src/
├── main.iota
└── math.iota
```

In `math.iota`, you can export a function using `export`.

```iota
module Math is

export my_add
let my_add
    : Int -> Int -> Int
    = add
end
```

The `module Math is` declaration at the top of the file indicates that this entire file defines the math module.
There is no closing `end`; the module body continues to the end of the file.
If `end` is used, you must declare another `module` before defining anything else.

```iota
module Math is
    export my_add
    let my_add
        : Int -> Int -> Int
        = add
    end
end

module Constants is
    export pi
    let pi
        : Float
        = 3.14159
    end
end
```

In `main.iota`, you can use `my_add` by importing the math.iota file.

```iota
module Main is

import file math.iota

let x
    : Int
    = Math:my_add 2 2
end
```

To avoid having to qualify paths, you can use `as` to locally rename things.

```iota
module Main is

import file math.iota
import Math:my_add as my_add

let x
    : Int
    = my_add 2 2
end
```

`import m:x as n` introduces a local alias `n` for `m:x`, replacing it in the current module.

A directory can also be a module. It's idiomatic to use a `mod.iota` file as the module's interface.

```
src/
├── main.iota
└── utils/
    ├── mod.iota
    └── math.iota
```

`mod.iota` can re-export anything from modules it imports.

```iota
module Utils is

import file math.iota
import Math:my_add as my_add
export my_add
```

Now, anything that imports the `utils` can use `utils:my_add`.

You can also export a whole module.

```iota
module Utils is

import file math.iota
export Math
```

Importing `utils.iota` can name `utils.iota` itself OR a `utils/mod.iota` file.

```iota
module Main is

import file utils.iota

let x
    : Int
    = Utils:Math:my_add 2 2
end
```

You can also use `unqualified` to import everything into the current namespace:

```
module Main is

import unqualified utils.iota

let x
    : Int
    = Math:my_add 2 2
end
```

This is generally not recommended for general imports, only for things like preludes.

## Error Handling

In iota, you can handle errors using the `Either` and `Maybe` types.

```iota
# Right is typically the expected value, and Left is an error.
type Either a b = Left a + Right b
end

type Maybe a = Val a + Nil
end
```

You can use match statements or other methods to safely handle errors.
There are methods to convert an `Either` into an `Maybe` and vice versa.

```iota
let get_right a b
    : Either a b -> Maybe b
    = match
        Either:Right x -> Maybe:Val x end
        Either:Left _  -> Maybe:Nil   end
    end
end

let map_nil a b
    : a -> Maybe b -> Either a b
    = match
        _, Maybe:Val x -> Either:Right x end
        d, Maybe:Nil   -> Either:Left d  end
    end
end
```

## Monads

A monad is a way to handle computations that involve some sort of context.
In iota, monads are defined by this type class:

```iota
class Monad m is
    let return a
        : a -> m a
    end

    let bind a b
        : (a -> m b) -> m a -> m b
    end
end
```

Here is an example with `Maybe`, which implements the monad class.

```iota
let half
    : Int -> Maybe Int
    = fork even (Maybe:Val < flip div 2) (const Maybe:Nil)
with even
    : Int -> Bool
    = comp (eq 0) (flip mod 2)
end
# halves the value if it is even, otherwise returns 'Nil'

let res1
    : Maybe Int
    = return 20 > bind half > bind half
end
# The value gets passed through 'half' twice and we get 'Val 5'

let res2
    : Maybe Int
    = return 21 > bind half > bind half
end
# the first call of half fails and returns 'Nil' which is propagated. The second 'half' is never evaluated.

let res3
    : Maybe Int
    = return 22 > bind half > bind half
end
# the first call succeeds and returns 'Val 11' but the second fails, returning 'Nil'.
```

Because `Maybe` implements the `Monad` class, we can use `bind` on it.
Bind allows you to chain operations without losing the monadic context.

For completeness, here is the implementation of `Monad` for `Maybe`.

```iota
instance Monad (Maybe a) is
    let return a
        : a -> Maybe a
        = Maybe:Val
    end

    let bind a b
        : (a -> Maybe b) -> Maybe a -> Maybe b
        = match
            _, Maybe:Nil   -> Maybe:Nil       end
            f, Maybe:Val x -> Maybe:Val < f x end
        end
    end
end
```

## Examples

```iota
module Factorial is

let factorial
    : Int -> Int
    = fn x ->
        cond (lse x 1) 1 (mul x < factorial (sub x 1))
    end
end
```

```iota
module ListOps is

let map a b
    : (a -> b) -> List a -> List b
    = match
        _, List:Nil          -> List:Nil end
        f, List:Cons (x * xs) -> (comp List:Cons pair) (f x) (map f xs)
    end
end

let filter a
    : (a -> Bool) -> List a -> List a
    = match
        _, List:Nil           -> List:Nil end
        p, List:Cons (x * xs) -> cond (p x) (List:Cons (pair x (filter p xs))) (filter p xs) end
    end
end

let length a
    : List a -> Int
    = comp sum map (const 1)
end

let zip_with a b c
    : (a -> b -> c) -> List a -> List b -> List c
        match
            _, List:Nil, _                            -> List:Nil                                       end
            _, _, List:Nil                            -> List:Nil                                       end
            f, List:Cons (x * xs), List:Cons (y * ys) -> comp List:Cons pair (f x y) (zip_with f xs ys) end
        end
    end
end


let xs
    : List Int
    = [1, 2, 3, 4] > filter < (eq 0 > over (flip mod 2)) > map < flip div 2
end
# [1,2]
```

```iota
module MoreLists is

let foldl
    a b : (b -> a -> b) -> b -> List a -> b
    = match
        _, c, [] -> c end
        f, c, xs -> foldl f (f c < fst xs) < rst xs end
    end
end

let scan
    a b : (b -> a -> b) -> b -> [a] -> [b]
    = match
        _, c, [] -> [c] end
        f, c, xs -> (comp List:Cons pair) c scan f (f c < fst xs) < rst xs end
    end
end
```

```iota
module IoOps is

let main
    : IO Unit
    = println "Enter your name:" > then
    (getln > (bind fn name ->
        println < concat "Hello, " name
    end))
end
```

```iota
module MoreIo is

let main
    : IO Unit
    = println "Enter a number:" > then
    (getln > (bind fn num ->
        println < output num
    end))
with output
    : String -> String
    = fn s -> concat (concat s " is ") (parity s) end
with parity
    : String -> String
    = fn s -> cond (even (parse_or_default s)) "Even" "Odd" end
with even
    : Int -> Bool
    = fn x -> eq 0 (mod x 2) end
with parse_or_default (a : Parseable, Default)
    : String -> a
    = fn s -> map_nil_same default (parse s) end
end
```

```iota
module OpTables is

type OpTable = List Op
end

type Op = String * (Float -> Float -> Float)
end

let add_op : Op
    = "+" * add
end

let sub_op : Op
    = "-" * sub
end

let mul_op : Op
    = "*" * mul
end

let div_op : Op
    = "/" * div
end

let ops : OpTable
    = [add_op, sub_op, mul_op, div_op]
end

let eval_op
    : OpTable -> String -> Float -> Float -> Maybe Float
    = fn table ->
        fn op_name ->
            index_of table op_name > map (idx table) > ap
        end
    end
end
```
