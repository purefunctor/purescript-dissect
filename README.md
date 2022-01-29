# purescript-dissect

An implementation of [Clowns to the Left of me, Jokers to the Right
(Pearl): Dissecting Data
Structures](https://dl.acm.org/doi/abs/10.1145/1328438.1328474) by Conor
McBride in PureScript.

This package the following modules:

-   `Dissect.Class`
-   `Data.Functor.Polynomial`
-   `Record.Polynomial`
-   `Variant.Polynomial`

## Installation

Using `spago`:

``` bash
spago install dissect
```

## Rationale

I originally encountered the paper while looking for stack-safe
recursion schemes in PureScript, particularly with the
[matryoshka](https://github.com/purescript-contrib/purescript-matryoshka)
library, briefly mentioned in the following issue:
[matryoshka#9](https://github.com/purescript-contrib/purescript-matryoshka/issues/9#issuecomment-400384397).

## Quick Primer on Dissect

In essence, dissections essentially describe how to decompose a
structure `f a`, such that all values of `a` can be obtained and
eventually replaced with some other value of type `b`. Dissections
effectively generalize the concept of mapping a function over some
`Functor f` into the runtime, through the use of an intermediary
representation `Bifunctor q`, which is parameterized by the original
values `a`, and the replacement values `b`.

Let's use the following data type as a motivating example. This `List`
type is essentially a regular cons-list whose recursion is factored into
the type parameter `n`. The canonical `List` structure can be restored
through the use of the `Mu` type, but I won't go over that here.

``` purescript
data List a n
  = Nil
  | Cons a n
```

Writing a `Functor` instance for this type would be trivial—it simply
involves having to match against the type constructors and applying `f`
to the appropriate points where `n` appears.

``` purescript
instance Functor (List a) where
  map _ Nil = Nil
  map f (Cons a n) = Cons a (f n)
```

A `Dissect` instance on the other hand, generalizes the concept of "the
appropriate points where `n` appears", and this is achieved by
describing how to get all values of `n`, and replace them with some `m`.
As such, the `Dissect` instance for a `List` would look like the
following:

``` purescript
data List_2 a n m = Cons_2 a

instance Bifunctor (List_2 a) where
  bimap _ _ (Cons_2 a) = (Cons_2 a)

instance Dissect (List a) (List_2 a) where
  right = case _ of
    -- We start by writing cases for `Init`. Since `Nil` contains no
    -- `n` values, we immediately terminate with `Return Nil`.
    Init Nil -> Return Nil
    -- On the other hand, `Cons` has a single `n`, so we `Yield` the
    -- `n` and a corresponding `Cons_2` constructor, representing a
    -- structure that is waiting for the `n` that it lost to be
    -- replaced.
    Init (Cons a n) -> Yield n (Cons_2 a)
    -- `Init` aside, we then move on to writing `Next` cases. `Next`
    -- essentially carries the payload of a structure waiting for
    -- a replacement value, and the replacement value itself.
    --
    -- In this case, since there's no other `n` values, we `Return`
    -- the final `Cons` structure with the `m`.
    Next (Cons_2 a) m -> Return (Cons a m)
```

Now equipped with a `Dissect` instance, we can also mechanize the
mapping operation:

``` purescript
map :: forall p q a b. Dissect p q => (a -> b) -> p a -> p b
map f x = continue (right (Init x))
  where
  continue (Yield j c) = continue (right (Next c (f j)))
  continue (Return c) = c
```

## Polynomial Functors and Free Dissections

This package also provides the `Data.Functor.Polynomial` module, which
can be used to generically define data structures with the added benefit
of free `Dissect` instances. For example, let's consider the canonical
cons-list type.

``` purescript
data List a = Nil | Cons a (List a)
```

If we generalize the recursion and make it a fixed-point functor, we get
the following structure:

``` purescript
data ListF a n = Nil | Cons a n
```

Then, we can start modeling components according to their signatures:

-   `Nil` can be represented using `Const Unit`
-   `Cons` is a product of some `a` and a recursive marker `n`, or
    `Product (Const a) Id`

Taking these two together, we end up with the `Sum` type. We can also
use the `(:+:)`, and `(:*:)` for sums and products respectively.

``` purescript
type ListF a = Sum (Const Unit) (Product (Const a) Id)

type ListF a = (Const Unit) :+: (Const a :*: Id)

type List a = Mu (ListF a)
```

We'd also want to write smart constructors for our generic data type:

``` purescript
_Nil :: forall a. List a
_Nil = In (SumL (Const Unit))

_Cons :: forall a. a -> List a -> List a
_Cons a n = In (SumR (Product (Const a) (Id n)))
```

### Variant

The `Variant.Polynomial` module provides a `VariantF`-like dissectible
that serves as an alternative to deeply-nested `Sum` types. Like
`purescript-variant`, convenient pattern matching functions are also
provided.

``` purescript
type Example :: (Row (Type -> Type) -> Type -> Type) -> Row (Type -> Type) -> Type
type Example f r = f (a :: Id | r) Unit

-- An open variant allows any `* -> *`-kinded type to be injected
-- whether or not it implements a `Functor` instance. This makes
-- deeper composition much, much easier than say, enforcing said
-- `Functor` instance instantly.
openVariantF :: forall r. Example OpenVariantF r
openVariantF = inj (Proxy :: _ "a") (Id unit)

-- A closed variant is any open variant that has `Functor`, `Bifunctor`,
-- and `Dissect` instances. An unsafe routine is used internally to
-- capture the instance methods onto the closed variant.
closedVariantF :: Example VariantF ()
closedVariantF = instantiate openVariantF

-- Any closed variant can be converted into a vanilla variant for
-- compatibility. If you're only interested in pattern matching,
-- a wrapper for `onMatch` is also provided.
vanillaVariantF :: Example Variant.VariantF ()
vanillaVariantF = convert closedVariantF

-- And can be then used for operations like onMatch with relative
-- ease.
onMatchExample :: Unit
onMatchExample = vanillaVariantF # Variant.onMatch
  { a: \(Id u) -> u
  }
  (\_ -> unsafeCrashWith "Pattern match failed!")

-- Alternatively, convenience wrappers are also provided:
onMatchExample' :: Unit
onMatchExample' = closedVariantF # onMatch
  { a: \(Id u) -> u
  }
  (\_ -> unit)
```

### Record

The `Record.Polynomial` module provides a dissectible that operates on a
`Record`, serving as an alternative to deeply-nested `Product` types.
The `to` and `from` functions are used to convert back and forth
`Record` and `RecordF`. Note that unlike `Product`, there's no
definitive order to which elements are yielded first, and as such,
effectful operations must be treated with care.

``` purescript
type ConsR =
  (head :: Const Int, tail :: Id)

type ConsR' a =
  (head :: Const Int a, tail :: Id a)

type IntListV =
  ( "nil" :: Const Unit
  , "cons" :: RecordF ConsR
  )

type IntListF = VariantF IntListV

type IntList = Mu IntListF

_nil :: IntList
_nil = In (instantiate $ inj (Proxy :: _ "nil") (Const unit))

_cons :: Int -> IntList -> IntList
_cons =
  let
    -- We monomorphize type class methods early, as to make `_cons`
    -- less taxing to performance.
    consFrom :: Record (ConsR' IntList) -> RecordF ConsR IntList
    consFrom = from

    consInstantiate :: forall a. OpenVariantF IntListV a -> IntListF a
    consInstantiate = instantiate
  in
    \h t -> In (consInstantiate $ inj (Proxy :: _ "cons") (consFrom { head: Const h, tail: Id t }))

-- `cata` is defined in the `ssrs` package.
intListSum :: IntList -> Int
intListSum = cata go
  where
  go :: IntListF Int -> Int
  go = match
    { nil: \_ -> 0
    , cons: to >>> \{ head: Const head, tail: Id tail } -> head + tail
    }

-- An example of construction and destruction.
intListExample :: Int
intListExample = intListSum (_cons 10 (_cons 11 (_cons 21 _nil)))
```
