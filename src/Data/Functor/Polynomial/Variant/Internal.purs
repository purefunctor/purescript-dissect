module Data.Functor.Polynomial.Variant.Internal where

import Data.Either (Either)
import Data.Tuple (Tuple)

newtype VariantFRep p q a = VariantFRep
  { tag ∷ String
  , value ∷ p a
  , map ∷ ∀ x y. (x → y) → p x → p y
  , bimap ∷ ∀ v w x y. (v → w) → (x → y) → q v x → q w y
  , right ∷ ∀ c j. Either (p j) (Tuple (q c j) c) → Either (Tuple j (q c j)) (p c)
  , plug ∷ ∀ x. x → q x x → p x
  }

newtype VariantFRep_2 p q a b = VariantFRep_2
  { tag ∷ String
  , value ∷ q a b
  , map ∷ ∀ x y. (x → y) → p x → p y
  , bimap ∷ ∀ v w x y. (v → w) → (x → y) → q v x → q w y
  , right ∷ ∀ c j. Either (p j) (Tuple (q c j) c) → Either (Tuple j (q c j)) (p c)
  , plug ∷ ∀ x. x → q x x → p x
  }
