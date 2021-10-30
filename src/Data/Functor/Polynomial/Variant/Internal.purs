module Data.Functor.Polynomial.Variant.Internal where

import Dissect.Class (Garden(..), CoGarden(..))

newtype VariantFRep p q a = VariantFRep
  { tag ∷ String
  , value ∷ p a
  , map ∷ ∀ x y. (x → y) → p x → p y
  , bimap ∷ ∀ v w x y. (v → w) → (x → y) → q v x → q w y
  , right ∷ ∀ c j. Garden p q c j → CoGarden p q c j
  , plug ∷ ∀ x. x → q x x → p x
  }

newtype VariantFRep_2 p q a b = VariantFRep_2
  { tag ∷ String
  , value ∷ q a b
  , map ∷ ∀ x y. (x → y) → p x → p y
  , bimap ∷ ∀ v w x y. (v → w) → (x → y) → q v x → q w y
  , right ∷ ∀ c j. Garden p q c j → CoGarden p q c j
  , plug ∷ ∀ x. x → q x x → p x
  }
