module Dissect.Class where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Either (Either(..))
import Data.Bifunctor (class Bifunctor)
import Data.Tuple (Tuple(..))

class (Functor p, Bifunctor q) ⇐ Dissect p q | p → q where
  right
    ∷ ∀ c j
    . Either (p j) (Tuple (q c j) c)
    → Either (Tuple j (q c j)) (p c)

class Dissect p q ⇐ Plug p q | p → q where
  plug ∷ ∀ x. x → q x x → p x

tmap ∷ ∀ p q a b. Dissect p q ⇒ (a → b) → p a → p b
tmap f ps = continue (right (Left ps))
  where
  continue (Left (Tuple s pd)) = continue (right (Right (Tuple pd (f s))))
  continue (Right pt) = pt

-- Derived from: https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html
ttraverse ∷ ∀ m p q a b. Dissect p q ⇒ MonadRec m ⇒ (a → m b) → p a → m (p b)
ttraverse f ps = tailRecM continue (right (Left ps))
  where
  continue = case _ of
    Left (Tuple a dba) → do
      a' ← f a
      pure (Loop (right (Right (Tuple dba a'))))
    Right ys →
      pure (Done ys)

tsequence ∷ ∀ m p q a. Dissect p q ⇒ MonadRec m ⇒ p (m a) → m (p a)
tsequence = ttraverse identity
