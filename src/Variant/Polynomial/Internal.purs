module Variant.Polynomial.Internal where

newtype OpenVariantFRep :: forall k. (k -> Type) -> k -> Type
newtype OpenVariantFRep f a = OpenVariantFRep
  { tag :: String
  , value :: f a
  }

newtype OpenVariantFRep_2 :: forall k l. (k -> l -> Type) -> k -> l -> Type
newtype OpenVariantFRep_2 f a b = OpenVariantFRep_2
  { tag :: String
  , value :: f a b
  }
