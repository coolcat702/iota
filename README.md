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
- [Input, Output and Files](#input-output-and-files)
- [Standard Library](#standard-library)
- [Examples](#examples)

## Building and running

```
cargo build --release                      # needs LLVM 22.1 (see below) and clang at run time
iota examples/factorial.iota -o fact --run     # compile, link, run
iota prog.iota --emit ir                   # monomorphic typed ANF IR after optimization
iota prog.iota --emit mir                  # instances, data layouts, strict/borrowed parameters
iota prog.iota --emit llvm -o prog.ll      # textual LLVM IR
iota prog.iota --opt-mode aggressive       # inlining + partial evaluation
iota prog.iota --run -- a b c              # run it with the command line arguments a, b, c
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
# let f = λx.M
let f
    : Int -> Int
    = fn x -> mul 2 x end
end
```

A function of several arguments lists its parameters separated by commas; `fn x, y -> M end` is
shorthand for the nested `fn x -> fn y -> M end end` (that is, λx.λy.M).

```iota
let add3
    : Int -> Int -> Int -> Int
    = fn a, b, c -> add a (add b c) end
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
    = comp (eq 0) (flip mod 2)
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
Only type combinators (`+`, `*`, `->`) and composition operators (`<`, `>`) exist.
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
    = List:Cons (1 *
        List:Cons (2 *
            List:Cons (3 *
                List:Cons (4 * List:Nil)
            )
        )
    )
end
# [1, 2, 3, 4]
```

## Lists

Lists have many functions that operate them, including:

```iota
[1, 2, 3, 4] > map (mul 2)
# [2, 4, 6, 8]

[1, 2, 3, 4] > filter (comp (eq 0) (flip mod 2))
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
        Bool:True  -> const      end
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
Default
```

## Ranges

Ranges are defined using `range`, or alternatively `from` and `to` (or `to_inc`). Because evaluation is
lazy, `from` is a genuinely infinite list; only the part that is looked at is ever built.

```iota
let range (a : Successable, Orderable)
    : a -> a -> List a
    = comp to from
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

```iota
module Main is

import file utils/mod.iota

let x
    : Int
    = Utils:Math:my_add 2 2
end
```

You can also use `unqualified` to import everything into the current namespace:

```
module Main is

import unqualified utils/mod.iota

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
    = fork even (comp Maybe:Val (flip div 2)) (const Maybe:Nil)
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

## Input, Output and Files

Everything that touches the outside world is an `IO` action: building one does nothing, and the
program runs the ones that `main` is made of. Chain them with `bind` and `then` (see [Monads](#monads)).

### The entry point and exit codes

`main` can have any of these types:

| `main : ...`             | what it means                                   |
| ------------------------ | ----------------------------------------------- |
| `IO Unit`                | run it; the exit status is 0                    |
| `IO Int`                 | run it; the `Int` it returns is the exit status |
| `List String -> IO Unit` | the same, given the command line arguments      |
| `List String -> IO Int`  | the same, and the exit status                   |

```iota
let main
    : List String -> IO Int
    = fn argv ->
        println (concat "got " (concat (show (len argv)) " arguments")) > then
        (return (len argv))
    end
end
```

The arguments exclude the program name. `iota prog.iota --run -- a b` passes `a` and `b`; a compiled
program just takes them from its command line. The exit status is whatever the OS makes of the
`Int` (it keeps the low 8 bits). `exit : Int -> IO Unit` ends the program in the middle instead,
flushing output first.

### Files

```iota
read_file     : String -> IO (Either IOError String)
write_file    : String -> String -> IO (Either IOError Unit)     # replaces the contents
append_file   : String -> String -> IO (Either IOError Unit)
file_exists   : String -> IO Bool                                # a file, a directory, anything
```

`is_file` and `is_dir` are the narrower tests. Text is UTF-8 (malformed bytes read as U+FFFD).
`read_file_bytes`, `write_file_bytes` and `append_file_bytes` treat each `Char` as one byte
(0 to 255), for binary data. They are `IO` because reading a file gives a different answer each time
the disk changes, so they must run when and only when the program reaches them.

Failures are a `Left` holding an `IOError`: `NotFound`, `PermissionDenied`, `AlreadyExists`,
`IsADirectory`, `NotADirectory`, `DirectoryNotEmpty`, `InvalidInput`, `UnexpectedEof` or
`OtherError`, each carrying the system's message; `show` gives readable text.

```iota
let copy
    : String -> String -> IO (Either IOError Unit)
    = fn from, to -> io_and_then (fn text -> write_file to text end) (read_file from) end
end
```

`io_and_then f action` runs `f` on the success value of `action` and stops at the first error.

### Standard streams and the environment

```iota
read_line    : IO (Maybe String)       # Nil at the end of the input (unlike `getln`, which gives "")
read_stdin   : IO String               # everything that is left
eprint, eprintln : String -> IO Unit   # standard error
flush        : IO Unit                 # `print` is buffered; input and sleeping flush it for you
get_env      : String -> IO (Maybe String)
args         : IO (List String)        # the same list `main` can receive
```

### Characters and numbers

The conversions the standard library is built on are in the prelude: `ord : Char -> Int`,
`chr : Int -> Char`, `int_to_float`, `float_to_int` (truncates, saturates), the bit operations
`bit_and`, `bit_or`, `bit_xor`, `bit_not`, `shift_left`, `shift_right` (zero filling),
`shift_right_arith`, `float_repr` (the shortest text that reads back as exactly the same `Float`;
`show` keeps only 6 digits) and `unit : Unit`. `Hashable` (`hash : a -> Int`) is the class
`HashMap` and `HashSet` use; give your own types an instance next to their `Eqable` one.

String and character literals accept `\n \t \r \0 \e \a \\ \' \"`, `\xHH` and `\u{H...}`, so
`"\e[31m"` is the ANSI escape for red text.

## Standard Library

The library lives in `std/` and is embedded in the compiler. Import what you need; nothing is
loaded otherwise:

```iota
import file std/str.iota
import file std/hashmap.iota

let main : IO Unit = println (Str:to_upper "hello") end
```

A module's functions are called `Module:name` (or `import Module:name as name`). Types, classes and
the prelude are visible everywhere without a qualifier. A file in your project with the same
path takes precedence over the embedded one.

| Import             | Module    | What it has                                                                                                                                                                                                                             |
| ------------------ | --------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `std/str.iota`     | `Str`     | `split`, `split_str`, `lines`, `words`, `join`, `trim`, `replace`, `starts_with`, `ends_with`, `contains`, `find`, `pad_left`/`pad_right`, `to_upper`/`to_lower`, `repeat`, `parse_int`, `parse_float`, and the ASCII character classes |
| `std/path.iota`    | `Path`    | `join`, `basename`, `dirname`, `extension`, `stem`, `with_extension`, `normalize`, `components`, `is_absolute` (pure string work, POSIX `/` paths)                                                                                      |
| `std/fs.iota`      | `Fs`      | `list_dir`, `create_dir`, `create_dir_all`, `remove`, `rename`, `copy_file`, `current_dir`, `canonicalize`, `file_size`, `modified_time`, `read_lines`, `write_lines`                                                                   |
| `std/sort.iota`    | `Sort`    | stable merge sort: `sort`, `sort_desc`, `sort_by`, `sort_on`, `merge`, `is_sorted`, `dedup`, `sort_unique`                                                                                                                              |
| `std/search.iota`  | `Search`  | `find`, `find_index`, `any`, `all`, `count`, `contains`, `minimum`/`maximum` (and `_on`), `unique`, `partition`, `last`, `partition_point`                                                                                              |
| `std/hashmap.iota` | `HashMap` | an immutable hash map: `insert`, `get`, `remove`, `alter`, `fold`, `union`, `filter`, `from_list`, ...                                                                                                                                  |
| `std/hashset.iota` | `HashSet` | an immutable hash set: `insert`, `member`, `union`, `intersection`, `difference`, `is_subset`, ...                                                                                                                                      |
| `std/json.iota`    | `Json`    | `parse`, `stringify`, `pretty`, builders, `get`/`at`/`path`, `as_string`/`as_int`/...                                                                                                                                                   |
| `std/time.iota`    | `Time`    | `now`, `monotonic`, `sleep_ms`, `measure`, dates (`from_unix`, `to_unix`, `format`, `weekday`, ...), `now_local`                                                                                                                        |
| `std/rng.iota`     | `Rng`     | seedable pure generators: `seed`, `from_os`, `int_range`, `float`, `choose`, `shuffle`, `split`                                                                                                                                         |
| `std/process.iota` | `Process` | `run`, `run_with_input`, `shell`, `inherit`, `pid`, `environ`                                                                                                                                                                           |
| `std/ansi.iota`    | `Ansi`    | colors, styles, cursor and screen control as strings; `strip`, `visible_length`                                                                                                                                                         |
| `std/term.iota`    | `Term`    | keypresses without Enter, terminal size, resize events, raw mode                                                                                                                                                                        |

### Hash maps and sets

```iota
import file std/hashmap.iota

let ages
    : HashMap String Int
    = HashMap:from_list [("ann" * 31), ("bob" * 27)]
end

# HashMap:get "ann" ages              -> Val 31
# HashMap:insert "cy" 40 ages         -> a new map; `ages` is unchanged
# HashMap:fold (fn n, k, v -> add n v end) 0 ages
```

Both are persistent: an update returns a new structure sharing almost everything with the old one,
and lookups and updates take O(log n). Keys need `Hashable` and `Eqable`. The iteration order is
deterministic but not specified.

### JSON

```iota
import file std/json.iota

# Json:parse "{\"a\": [1, 2.5, null]}"
#   -> Right (JObj [("a", JArr [JNum 1, JNum 2.5, JNull])])
# Json:parse "[1,]"
#   -> Left "unexpected character at offset 3"
```

A document is `JNull + JBool Bool + JNum Float + JStr String + JArr (List Json) + JObj (List (String * Json))`.
Objects keep their members in order. The parser is strict (no comments, trailing commas or
leading zeros), reads `\uXXXX` escapes including surrogate pairs, and prints numbers so that they read
back exactly.

### The terminal

```iota
import file std/term.iota
import file std/ansi.iota

let loop
    : IO Unit
    = bind (fn k ->
        cond (or (eq k (Key:Ch 'q')) (eq k Key:Eof))
            (println "bye")
            (println (Ansi:green (show k)) > then loop)
      end) Term:read_key
end

let main : IO Unit = Term:with_raw_mode loop end
```

Always stop on `Eof` too: once the input is closed `read_key` keeps answering `Eof`.

In raw mode a key is delivered as soon as it is pressed, nothing is echoed, and Ctrl-C is the key
`Ctrl 'c'` instead of a signal (handle it or the program cannot be stopped from the keyboard).
The terminal is put back when the program ends, however it ends: normally, through `exit`,
after a crash, or when killed by `SIGTERM`, `SIGHUP` or `SIGINT`.

Keys are `Ch c`, `Ctrl c`, `FKey n`, `Enter`, `Tab`, `Backspace`, `Escape`, `ArrowUp`/`Down`/`Left`/`Right`,
`Home`, `End`, `Insert`, `Delete`, `PageUp`, `PageDown`, and the pseudo-keys `Resize` (the window
changed size: ask `Term:size`), `Timeout` and `Eof`. `read_key_timeout ms` gives up after a while,
which is how you animate. When input is a pipe or a file instead of a terminal every byte is a key,
so interactive programs can be tested with `printf 'jjq' | ./prog`.

### Notes on modules

- A module's own definitions are visible without a qualifier only inside that module; the
  Prelude is the only thing visible everywhere. (A library can therefore define its own `filter`
  without changing what `filter` means in your program.) Instance bodies are checked outside their
  module, so they refer to its helpers as `Module:name`.
- Files are loaded dependencies first, so a type defined in an imported file can be used in the
  importing file's signatures. Type names are global (they cannot be qualified); constructors are
  qualified by their type: `Json:JNull`, `Key:Enter`.
- A zero-parameter `type T = C x` is an alias for `C x`, so a distinct, matchable type needs at
  least two alternatives (`type Gen = G Int + GNever`) or a type parameter.
- Import paths may contain `/`: `import file std/str.iota`, `import file utils/math.iota`.

## Examples

Example programs are found in `examples/`.
