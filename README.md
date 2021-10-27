# purescript-dissect

An implementation of Clowns to the Left of me, Jokers to the Right
(Pearl): Dissecting Data Structures by Conor McBride in PureScript.

This package provides three useful modules:

-   `Dissect.Class`{.verbatim}
-   `Data.Functor.Polynomial`{.verbatim}
-   `Data.Functor.Polynomial.Variant`{.verbatim}

## Installation

Using `spago`{.verbatim}:

    $ spago install dissect

or if not present within the current package set, add it to
`packages.dhall`{.verbatim}:

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
This eventually to the creation of
[ssrs](https://github.com/PureFunctor/purescript-ssrs) where I derived
stack-safe recursion schemes via dissectible data structures based on
the tail-recursive catamorphism originally implemented in the paper.

Another use-case I\'ve found is for implementing mutually recursive
collections of types which is explored in the paper: [Generic
programming with fixed points for mutually recursive
datatypes](https://dl.acm.org/doi/abs/10.1145/1631687.1596585). I\'ve
implemented a proof of concept in
[./test/Universe.purs](./test/Universe.purs) and it works well in
conjunction with recursion schemes provided by
[ssrs](https://github.com/PureFunctor/purescript-ssrs).

## Quick Primer on Dissect

I\'m assuming that by coming across this package, you\'re comfortable
working with fixed-point functors from recursion schemes. As such, I
won\'t try to explain everything in-depth, just the concepts that
matter.

Essentially, dissections take fixed-point functors and transform them
into bifunctors that contain either the base case of a fixed-point data
type or its recursive step. To contextualize this, let\'s say we have
the following tree structure:

``` purescript
data TreeF n = Leaf | Fork n n n
```

Since recursion is factored out in this definition and replaced by some
type variable `n`{.verbatim}, we can fill it with anything we want.
Likewise, we can also use the `Mu`{.verbatim} combinator to effectively
create a recursive data type. What we want in a dissection is to be able
to represent the steps on how we\'re going to deconstruct recursive
cases such as `Fork`{.verbatim}. Let\'s start by visualizing the essence
of dissecting functors:

We say that `TreeF`{.verbatim} essentially has a three seats for
`n`{.verbatim} to be contained in, and that lives under the
`Fork`{.verbatim} constructor:

``` purescript
Fork [ n - n - n ]
```

Note that we take no notice to the `Leaf`{.verbatim} constructor as it
contains no seats for `n`{.verbatim}.

The `right`{.verbatim} function allows us to take this data and pluck
out an `n`{.verbatim}, leaving us a hole:

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

If we repeat this process, we eventually end up plucking out all
`n`{.verbatim} and replacing them with `m`{.verbatim}:

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

This is, in essence, one way to do a `map`{.verbatim} operation, but
with the added benefit of being able to perform it in a stack-safe
manner, as we\'ve essentially factored out recursion, and we\'re really
only concerned with plucking out and planting new values into
structures. Unfortunately, its cost is that we must describe this
process ourselves by defining data types that correspond to the
intermediate states of where the hole currently is.

In reality, the `right`{.verbatim} function has the following type:

``` purescript
right
  ∷ ∀ c j
  . Either (p j) (Tuple (q c j) c)
  → Either (Tuple j (q c j)) (p c)
```

Its left path describes plucking out a value from some
`Functor`{.verbatim} and returning its dissection paired with its inner
value `j`{.verbatim}, or it returns the same `Functor`{.verbatim}
containing some value `c`{.verbatim}; its right path on the other hand
takes a dissection and a value to fill it with, and has the same return
choice as the left path. There also exists the `pluck`{.verbatim} and
`plant`{.verbatim} helper functions for choosing paths more elegantly:

``` purescript
pluck ∷ ∀ p q c j. Dissect p q ⇒ p j → Either (Tuple j (q c j)) (p c)
pluck = right <<< Left

plant ∷ ∀ p q c j. Dissect p q ⇒ (q c j) → c → Either (Tuple j (q c j)) (p c)
plant q c = right (Right (Tuple q c))
```

Now, let\'s start writing actual code:

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

With boilerplate out of the way, we can now write the
`Dissect`{.verbatim} instance:

``` purescript
instance Dissect TreeF TreeF_2 where
  right = case _ of
    Left Leaf → Right Leaf
```

First and foremost, it\'s impossible to dissect the `Leaf`{.verbatim}
constructor as it contains no points of recursion, so we terminate
immediately, however, `Fork`{.verbatim} is much more interesting. Here
we can see how its first element is being plucked out, with the rest of
its seats being delegated to `ForkRR`{.verbatim}.

``` purescript
Left (Fork m n o) → Left (Tuple m (ForkRR n o))
```

Then, we move on to the `Right`{.verbatim} path. In here, we first start
by plucking out yet another seat in `ForkRR`{.verbatim}, delegating the
remaining seat into `ForkLR`{.verbatim} and planting some other value in
its place.

``` purescript
Right (Tuple w c) → case w of
  ForkRR m n → Left (Tuple m (ForkLR c n))
```

For `ForkLR`{.verbatim}, we pluck out another seat yet again, planting a
new value in its place using `ForkLL`{.verbatim}. Likewise, we also
carry over the value we\'ve planted previously in `ForkLR`{.verbatim}.

``` purescript
ForkLR n m → Left (Tuple m (ForkLL n c))
```

Finally, for `ForkLL`{.verbatim}, we start reconstructing
`Fork`{.verbatim} but with the planted values:

``` purescript
ForkLL n o → Right (Fork n o c)
```

You\'ve just written your first `Dissect`{.verbatim} instance!

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

What the `Dissect`{.verbatim} class achieves for us is that it factors
out recursion in the transformation of some type `p c`{.verbatim} into
`p j`{.verbatim}. This allows us to implement operations such as
`map`{.verbatim} and `traverse`{.verbatim} in a stack-safe way as
instead of relying on recursion primitives, we\'ve lifted recursion into
a stack-based, iterative machine.
