# purescript-dissect

An implementation of [Clowns to the Left of me, Jokers to the Right
(Pearl): Dissecting Data
Structures](https://dl.acm.org/doi/abs/10.1145/1328438.1328474) by Conor
McBride in PureScript.

This package provides three useful modules:

-   `Dissect.Class`
-   `Data.Functor.Polynomial`
-   `Data.Functor.Polynomial.Variant`

## Installation

Using `spago`:

    $ spago install dissect

or if not present within the current package set, add it to
`packages.dhall`:

``` dhall
let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.14.4-20211005/packages.dhall
        sha256:2ec351f17be14b3f6421fbba36f4f01d1681e5c7f46e0c981465c4cf222de5be

let overrides = {=}

let additions =
      { dissect =
        { dependencies = [ ... ]  -- copy dependencies from spago.dhall
        , repo = "https://github.com/PureFunctor/purescript-dissect.git"
        , version = "<insert-desired-revision-here>"
        }
      }

in  upstream // overrides // additions
```

## Rationale

I originally encountered the paper while looking for a way to ensure
stack safety with
[matryoshka](https://github.com/purescript-contrib/purescript-matryoshka),
being briefly mentioned in a comment in
[matryoshka#9](https://github.com/purescript-contrib/purescript-matryoshka/issues/9#issuecomment-400384397).
This eventually led to the creation of
[ssrs](https://github.com/PureFunctor/purescript-ssrs) where I derived
stack-safe recursion schemes via dissectible data structures based on
the tail-recursive catamorphism originally implemented in the paper.

Another use-case I've found is for implementing mutually recursive
collections of types which is explored in the paper: [Generic
programming with fixed points for mutually recursive
datatypes](https://dl.acm.org/doi/abs/10.1145/1631687.1596585). I've
implemented a proof of concept in
[./test/Universe.purs](./test/Universe.purs) and it works well in
conjunction with recursion schemes provided by
[ssrs](https://github.com/PureFunctor/purescript-ssrs).

## Quick Primer on Dissect

I'm assuming that by coming across this package, you're comfortable
working with fixed-point functors from recursion schemes. As such, I
won't try to explain everything in-depth, just the concepts that matter.

Essentially, dissections take fixed-point functors and transform them
into bifunctors that contain either the base case of a fixed-point data
type or its recursive step. To contextualize this, let's say we have the
following tree structure:

``` purescript
data TreeF n = Leaf | Fork n n n
```

Since recursion is factored out in this definition and replaced by some
type variable `n`, we can fill it with anything we want. Likewise, we
can also use the `Mu` combinator to effectively create a recursive data
type. What we want in a dissection is to be able to represent the steps
on how we're going to deconstruct recursive cases such as `Fork`. Let's
start by visualizing the essence of dissecting functors:

We say that `TreeF` essentially has a three seats for `n` to be
contained in, and that lives under the `Fork` constructor:

``` purescript
Fork [ n - n - n ]
```

Note that we take no notice to the `Leaf` constructor as it contains no
seats for `n`.

The `right` function allows us to take this data and pluck out an `n`,
leaving us a hole:

``` purescript
> right $ Fork [ n - n - n ]

n, Fork [ () - n - n ]
```

Likewise, it can also take a structure with holes and something to fill
it with:

``` purescript
> right $ m, Fork [ () - n - n ]

Fork [ m - n - n ]
```

If we repeat this process, we eventually end up plucking out all `n` and
replacing them with `m`:

``` purescript
> right $ Fork [ m - n - n ]
n, Fork [ m - () - n ]

> right $ m, Fork [ m - () - n ]
Fork [ m - m - n ]

> right $ Fork [ m - m - n ]
n, Fork [ m - m - () ]

> right $ m, Fork [ m - m - () ]
Fork [ m - m - m ]
```

This is, in essence, one way to do a `map` operation, but with the added
benefit of being able to perform it in a stack-safe manner, as we've
essentially factored out recursion, and we're really only concerned with
plucking out and planting new values into structures. Unfortunately, its
cost is that we must describe this process ourselves by defining data
types that correspond to the intermediate states of where the hole
currently is.

In reality, the `right` function has the following type:

``` purescript
right
  ∷ ∀ c j
  . Either (p j) (Tuple (q c j) c)
  → Either (Tuple j (q c j)) (p c)
```

Its left path describes plucking out a value from some `Functor` and
returning its dissection paired with its inner value `j`, or it returns
the same `Functor` containing some value `c`; its right path on the
other hand takes a dissection and a value to fill it with, and has the
same return choice as the left path. There also exists the `pluck` and
`plant` helper functions for choosing paths more elegantly:

``` purescript
pluck ∷ ∀ p q c j. Dissect p q ⇒ p j → Either (Tuple j (q c j)) (p c)
pluck = right <<< Left

plant ∷ ∀ p q c j. Dissect p q ⇒ (q c j) → c → Either (Tuple j (q c j)) (p c)
plant q c = right (Right (Tuple q c))
```

Now, let's start writing actual code:

``` purescript
data TreeF n = Leaf
             | Fork n n n

derive instance Functor TreeF

data TreeF_2 n m = ForkRR m m
                 | ForkLR n m
                 | ForkLL n n

instance Bifunctor TreeF_2 where
  bimap f g = case _ of
    ForkRR m0 m1 -> ForkRR (g m0) (g m1)
    ForkLR n0 m1 -> ForkLR (f n0) (g m1)
    ForkLL n0 n1 -> ForkLL (f n0) (f n1)
```

With boilerplate out of the way, we can now write the `Dissect`
instance:

``` purescript
instance Dissect TreeF TreeF_2 where
  right = case _ of
    Left Leaf → Right Leaf
```

First and foremost, it's impossible to dissect the `Leaf` constructor as
it contains no points of recursion, so we terminate immediately,
however, `Fork` is much more interesting. Here we can see how its first
element is being plucked out, with the rest of its seats being delegated
to `ForkRR`.

``` purescript
Left (Fork m n o) → Left (Tuple m (ForkRR n o))
```

Then, we move on to the `Right` path. In here, we first start by
plucking out yet another seat in `ForkRR`, delegating the remaining seat
into `ForkLR` and planting some other value in its place.

``` purescript
Right (Tuple w c) → case w of
  ForkRR m n → Left (Tuple m (ForkLR c n))
```

For `ForkLR`, we pluck out another seat yet again, planting a new value
in its place using `ForkLL`. Likewise, we also carry over the value
we've planted previously in `ForkLR`.

``` purescript
ForkLR n m → Left (Tuple m (ForkLL n c))
```

Finally, for `ForkLL`, we start reconstructing `Fork` but with the
planted values:

``` purescript
ForkLL n o → Right (Fork n o c)
```

You've just written your first `Dissect` instance!

``` purescript
instance Dissect TreeF TreeF_2 where
  right = case _ of
    Left Leaf → Right Leaf
    Left (Fork m n o) → Left (Tuple m (ForkRR n o))
    Right (Tuple w c) → case w of
      ForkRR m n → Left (Tuple m (ForkLR c n))
      ForkLR n m → Left (Tuple m (ForkLL n c))
      ForkLL n o → Right (Fork n o c)
```

In conclusion, the `Dissect` class factors out the recursion in the
traversal of some recursive data structure. Instead of relying on
recursion primitives, we've successfully lifted recursion into a toolkit
for implementing stateful iterative machines.

## Polynomial Functors and Free Dissections

This package also comes equipped with the `Data.Functor.Polynomial`
module which can be used to define data structures generically with the
added benefit of getting `Dissect` instances for free. As an example,
suppose that we want to represent `List` generically:

``` purescript
data List a = Nil | Cons a (List a)
```

First, let's consider what our data type would look like after turning
it into a fixed point functor:

``` purescript
data ListF a n = Nil | Cons a n
```

Then, we can start modeling components according to their signatures:

-   `Nil` can be represented using `Const Unit`
-   `Cons` is a product of some `a` and our recursive marker `n`,
    therefore, we'd want to have `Product (Const a) Id`

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

However, using `Sum` becomes cumbersome as more alternatives also means
a deeper structure to pattern match against. This package provides the
`ClosedVariantF` dissectible which allows one to use a variant type
instead of `Sum` for easier pattern matching using the `case_` and `on`
combinators:

``` purescript
type TreeR :: Type -> Row (Type -> Type)
type TreeR a =
  ( leaf :: Const Unit
  , fork2 :: Id :*: Const a :*: Id
  , fork3 :: Id :*: Const a :*: Id :*: Const a :*: Id
  )

type TreeF :: Type -> Type -> Type
type TreeF a = ClosedVariantF (TreeR a)

type Tree :: Type -> Type
type Tree a = Mu (TreeF a)

leaf :: forall a. Tree a
leaf = In (close (inj (Proxy :: _ "leaf") (Const unit)))

fork2 :: forall a. Tree a -> a -> Tree a -> Tree a
fork2 a b c = In (close (inj (Proxy :: _ "fork2") (Id a :*: Const b :*: Id c)))

fork3 :: forall a. Tree a -> a -> Tree a -> a -> Tree a -> Tree a
fork3 a b c d e =
  In (close (inj (Proxy :: _ "fork3") (Id a :*: Const b :*: Id c :*: Const d :*: Id e)))

collect :: TreeF Int Int -> Int
collect = case_
  # on (Proxy :: _ "leaf")
      ( \(Const _) -> 1
      )
  # on (Proxy :: _ "fork2")
      ( \(Id a :*: Const b :*: Id c) -> a + b + c
      )
  # on (Proxy :: _ "fork3")
      ( \(Id a :*: Const b :*: Id c :*: Const d :*: Id e) ->
           a + b + c + d + e
      )
```

### Deferred Instances

The `Data.Functor.Polynomial.Variant` module provides two data types,
`PreVariantF` and `VariantF`. The former is constructed using `inj`,
much like in `purescript-variant`, and for the latter, it takes some
`PreVariantF` whose fields have `Functor`, `Bifunctor`, and `Dissect`
instances. By deferring when these instances are required, we're able to
create extensible data types with relative ease.

``` purescript
type Scoops = Int

-- We can define an extensible row and use it in the
-- context of a variant, without having a Functor
-- instance upfront.

type IceCreamR :: Row (Type -> Type) -> Row (Type -> Type)
type IceCreamR r =
  ( vanilla :: Const Scoops
  , chocolate :: Const Scoops
  | r
  )

type IceCreamV :: Row (Type -> Type) -> Type -> Type
type IceCreamV r = PreVariantF (IceCreamR r)

vanilla :: forall r a. Scoops -> IceCreamV r a
vanilla scoops = inj (Proxy :: _ "vanilla") (Const scoops)

chocolate :: forall r a. Scoops -> IceCreamV r a
chocolate scoops = inj (Proxy :: _ "chocolate") (Const scoops)

-- But in order to make use of dissections, we have to
-- "close" the type.

type IceCreamC :: Type -> Type
type IceCreamC = VariantF (IceCreamR ())

closeIceCream :: forall a. IceCreamV () a -> IceCreamC a
closeIceCream = instantiate

vanillaServing :: forall a. IceCreamC a
vanillaServing = closeIceCream $ vanilla 3

chocolateServing :: forall a. IceCreamC a
chocolateServing = closeIceCream $ chocolate 3

-- Likewise, we can also extend the base variant with
-- new fields.

type IceCreamR' r = IceCreamR ( strawberry :: Const Scoops | r )

type IceCreamV' r = PreVariantF (IceCreamR' r)

strawberry :: forall r a. Scoops -> IceCreamV' r a
strawberry scoops = inj (Proxy :: _ "strawberry") (Const scoops)

-- And close them once we're done.

type IceCreamC' = VariantF (IceCreamR' ())

closeIceCream' :: forall a. IceCreamV' () a -> IceCreamC' a
closeIceCream' = instantiate

strawberryServing :: forall a. IceCreamC' a
strawberryServing = closeIceCream' $ strawberry 3

chocolateServing' :: forall a. IceCreamC' a
chocolateServing' = closeIceCream' $ chocolate 3
```
