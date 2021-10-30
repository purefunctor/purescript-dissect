-- | Provides the `Dissect` and `Plug` type classes based on "Clowns to
-- | the Left of bme, Jokers to the Right (Pearl): Dissecting Data
-- | Structures" by Conor McBride.
module Dissect.Class
  ( module Dissect.Class
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Bifunctor (class Bifunctor)

data Garden ∷ (Type → Type) → (Type → Type → Type) → Type → Type → Type
data Garden p q c j
  = Pluck (p j)
  | Plant c (q c j)

data CoGarden ∷ (Type → Type) → (Type → Type → Type) → Type → Type → Type
data CoGarden p q c j
  = CoPluck (p c)
  | CoPlant j (q c j)

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
-- |     Pluck NilF → CoPluck NilF
-- |     Pluck (ConsF a n) → CoPlant n (ConsF_2 a)
-- |     Plant c (ConsF_2 a) → CoPluck (ConsF a c)
-- | ```
-- |
-- | See also: `Data.Functor.Polynomial` implements combinators for
-- | defining data types generically, giving `Dissect` instances for
-- | free.
-- |
-- | See also: `README.md` for a more in-depth explanation and tutorial.
class (Functor p, Bifunctor q) ⇐ Dissect p q | p → q where
  right ∷ ∀ c j. Garden p q c j → CoGarden p q c j

pluck ∷ ∀ p q c j. Dissect p q ⇒ p j → CoGarden p q c j
pluck = right <<< Pluck

plant ∷ ∀ p q c j. Dissect p q ⇒ c → (q c j) → CoGarden p q c j
plant c q = right (Plant c q)

-- | The `Plug` class describes how to take a `Bifunctor` dissection and
-- | turn it back into the undissected `Functor`.
class Dissect p q ⇐ Plug p q | p → q where
  plug ∷ ∀ x. x → q x x → p x

-- | Types that can be dissected are Functors.
tmap ∷ ∀ p q a b. Dissect p q ⇒ (a → b) → p a → p b
tmap f = continue <<< pluck
  where
  continue (CoPlant s pd) = continue (plant (f s) pd)
  continue (CoPluck pt) = pt

-- Derived from: https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html
-- | Types that can be dissected are Traversable, provided that the
-- | Monad has a MonadRec instance.
ttraverse ∷ ∀ m p q a b. Dissect p q ⇒ MonadRec m ⇒ (a → m b) → p a → m (p b)
ttraverse f = tailRecM continue <<< pluck
  where
  continue = case _ of
    CoPlant a dba → do
      b ← f a
      pure (Loop (plant b dba))
    CoPluck ys →
      pure (Done ys)

-- | Types that can be dissected are Traversable, provided that the
-- | Monad has a MonadRec instance.
tsequence ∷ ∀ m p q a. Dissect p q ⇒ MonadRec m ⇒ p (m a) → m (p a)
tsequence = ttraverse identity
