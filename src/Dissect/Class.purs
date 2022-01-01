-- | Provides the `Dissect` and `Plug` type classes based on "Clowns to
-- | the Left of bme, Jokers to the Right (Pearl): Dissecting Data
-- | Structures" by Conor McBride.
module Dissect.Class
  ( module Dissect.Class
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))

-- | The `Dissect` class describes a transformation from a `Functor`
-- | into a `Bifunctor` that dissects a data structure into its
-- | components.
-- |
-- | Specifically, it takes a fixed-point recursive data type:
-- | ```purescript
-- | data ListF a n = NilF | ConsF a n
-- | ```
-- |
-- | And it's equivalent dissection:
-- | ```purescript
-- | data ListF_2 a n m = ConsF_2 a
-- | ```
-- |
-- | Producing the following instance:
-- | ```purescript
-- | instance Dissect (T_1 a) (T_2 a) where
-- |   right = case _ of
-- |     Left NilF → Right NilF
-- |     Left (ConsF a n) → Left (Tuple n (ConsF_2 a))
-- |     Right (Tuple (ConsF_2 a) c) → Right (ConsF a c)
-- | ```
-- |
-- | See also: `Data.Functor.Polynomial` implements combinators for
-- | defining data types generically, giving `Dissect` instances for
-- | free.
-- |
-- | See also: `README.md` for a more in-depth explanation and tutorial.
class (Functor p, Bifunctor q) <= Dissect p q | p -> q where
  right
    :: forall c j
     . Either (p j) (Tuple (q c j) c)
    -> Either (Tuple j (q c j)) (p c)

pluck :: forall p q c j. Dissect p q => p j -> Either (Tuple j (q c j)) (p c)
pluck = right <<< Left

plant :: forall p q c j. Dissect p q => (q c j) -> c -> Either (Tuple j (q c j)) (p c)
plant q c = right (Right (Tuple q c))

-- | The `Plug` class describes how to take a `Bifunctor` dissection and
-- | turn it back into the undissected `Functor`.
class Dissect p q <= Plug p q | p -> q where
  plug :: forall x. x -> q x x -> p x

-- | Types that can be dissected are Functors.
tmap :: forall p q a b. Dissect p q => (a -> b) -> p a -> p b
tmap f = continue <<< pluck
  where
  continue (Left (Tuple s pd)) = continue (plant pd (f s))
  continue (Right pt) = pt

-- Derived from: https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html
-- | Types that can be dissected are Traversable, provided that the
-- | Monad has a MonadRec instance.
ttraverse :: forall m p q a b. Dissect p q => MonadRec m => (a -> m b) -> p a -> m (p b)
ttraverse f = tailRecM continue <<< pluck
  where
  continue = case _ of
    Left (Tuple a dba) -> do
      b <- f a
      pure (Loop (plant dba b))
    Right ys ->
      pure (Done ys)

-- | Types that can be dissected are Traversable, provided that the
-- | Monad has a MonadRec instance.
tsequence :: forall m p q a. Dissect p q => MonadRec m => p (m a) -> m (p a)
tsequence = ttraverse identity
