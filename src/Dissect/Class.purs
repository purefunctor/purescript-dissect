module Dissect.Class where

import Data.Either (Either(..))
import Data.Functor (class Functor)
import Data.Bifunctor (class Bifunctor)
import Data.Tuple (Tuple(..))

class (Functor p, Bifunctor q) ⇐ Dissect p q | p → q where
  right
    ∷ ∀ c j
    . Either (p j) (Tuple (q c j) c)
    → Either (Tuple j (q c j)) (p c)

tmap :: forall p q a b. Dissect p q => (a -> b) -> p a -> p b
tmap f ps = continue (right (Left ps))
  where
  continue (Left (Tuple s pd)) = continue (right (Right (Tuple pd (f s))))
  continue (Right pt) = pt
