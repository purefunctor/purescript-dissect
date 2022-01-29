-- | Provides the `Dissect` and `Plug` type classes based on "Clowns to
-- | the Left of me, Jokers to the Right (Pearl): Dissecting Data
-- | Structures" by Conor McBride.
module Dissect.Class
  ( module Dissect.Class
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Bifunctor (class Bifunctor)

-- | The input type consumed by the `right` operation of the `Dissect` type
-- | class. Here's what the following type parameters correspond to:
-- |
-- | * `p` - a `Functor` parameterized by a type `j`—a container of values
-- |   of type `j`.
-- |
-- | * `q` - a `Bifunctor` parameterized by the types `c` and `j`—a container
-- |   of values of type `c` and `j`.
-- |
-- | * `j` - a value that is yielded while dissecting a structure, creating
-- |   a "hole" to be filled by another value.
-- |
-- | * `c` - a value that fills the "hole" created by yielding a `j`.
-- |
-- | When put together with respect to the constructors:
-- |
-- | * `Init` - takes a container `p` of values `j` to dissect. If `p j`
-- |   yields a `j`, then `Yield j (q c j)` is likely to be returned,
-- |   otherwise, `Return (p c)` is to be expected.
-- |
-- | * `Next` - takes a container `q` of values `c` and `j`, and a value
-- |   `c`. If inserting the value `c` to the container yields a `j`, then
-- |   `Yield j (q c j)` is likely to be returned, otherwise, `Return (p c)`
-- |   is to be expected.
-- |
-- | The `q c j` container represents the intermediary structure needed to
-- | represent the current state of the dissection. In essence, the type
-- | variables `c` corresponds to values that have already been processed
-- | while `j` corresponds to values that remain untouched.
data Input :: (Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type
data Input p q c j
  = Init (p j)
  | Next (q c j) c

-- | The output type produced by the `right` operation of the `Dissect` type
-- | class. Here's what the following type parameters correspond to:
-- |
-- | * `p` - a `Functor` parameterized by a type `j`—a container of values
-- |   of type `j`.
-- |
-- | * `q` - a `Bifunctor` parameterized by the types `c` and `j`—a container
-- |   of values of type `c` and `j`.
-- |
-- | * `j` - a value that is yielded while dissecting a structure, creating
-- |   a "hole" to be filled by another value.
-- |
-- | * `c` - a value that fills the "hole" created by yielding a `j`.
-- |
-- | When put together with respect to the constructors:
-- |
-- | * `Yield` - produces a value `j` and the intermediary container `q c j`,
-- |    where `q c j` may or may not contain more values of `j`. This container
-- |    is also used to continue the dissection process until a `Return` is
-- |    finally provided.
-- |
-- | * `Return` - produces the final container `p c`, where all values of `j`
-- |    within `p` have been replaced by `c`.
data Output :: (Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type
data Output p q c j
  = Yield j (q c j)
  | Return (p c)

-- | The `Dissect` type class describes the transformation of a `Functor`
-- | container `p`, with its state represented by an intermediary `Bifunctor`
-- | container `q`.
class (Functor p, Bifunctor q) <= Dissect p q | p -> q where
  -- | `right` describes an iterator-like routine for dissecting a structure,
  -- | with each `Input` corresponding to some `Output`.
  right :: forall c j. Input p q c j -> Output p q c j

-- | The `Plug` type class describes how to turn the intermediary `Bifunctor`
-- | container `q` back into the `Functor` container `p`.
class Dissect p q <= Plug p q | p -> q where
  plug :: forall x. x -> q x x -> p x

-- | A tail-recursive `map` operation, performed using `Dissect`.
map :: forall p q a b. Dissect p q => (a -> b) -> p a -> p b
map f x = continue (right (Init x))
  where
  continue (Yield j c) = continue (right (Next c (f j)))
  continue (Return c) = c

-- | A tail-recursive `traverse` operation, performed using `Dissect`.
-- |
-- | Derived from: https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html
traverse :: forall m p q a b. Dissect p q => MonadRec m => (a -> m b) -> p a -> m (p b)
traverse f x = tailRecM continue (right (Init x))
  where
  continue = case _ of
    Yield j c -> do
      k <- f j
      pure (Loop (right (Next c k)))
    Return c ->
      pure (Done c)

-- | A tail-recursive `sequence` operation, performed using `Dissect`.
sequence :: forall m p q a. Dissect p q => MonadRec m => p (m a) -> m (p a)
sequence = traverse identity
