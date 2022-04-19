-- | Row-based sum types, `VariantF` and `VariantB`, which form a `Dissect`
-- | instance. Useful for defining data types algebraically while also having
-- | decent runtime performance and convenient pattern matching syntax.
module Dissect.Variant where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Newtype (unwrap)
import Data.Variant (match)
import Dissect.Class (class Dissect, Result, init, next, return, yield)
import Prim.Row as Row
import Type.Prelude (class IsSymbol, Proxy, reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

-- | A pair of a `Functor` and a `Bifunctor`.
foreign import data Pair :: (Type -> Type) -> (Type -> Type -> Type) -> Type

-- | A row-based sum type of functors applied to `a`.
-- |
-- | Unlike `VariantF` in the `variant` package, this type is indexed by a row
-- | of `Pair` types, which is also used to index the `VariantB` type.
data VariantF :: Row Type -> Type -> Type
data VariantF r a

-- | The internal representation for `VariantF`.
newtype VariantFRep p q a = VariantFRep
  { tag :: String
  , map :: forall x y. (x -> y) -> (p x -> p y)
  , bimap :: forall w x y z. (w -> x) -> (y -> z) -> q w y -> q x z
  , init :: forall c j. p j -> Result p q c j
  , next :: forall c j. q c j -> c -> Result p q c j
  , value :: p a
  }

-- | Inject into a variant functor given a tag.
injF
  :: forall p q r r' t a
   . IsSymbol t
  => Dissect p q
  => Row.Cons t (Pair p q) r' r
  => Proxy t
  -> p a
  -> VariantF r a
injF tag value = coerceFrom $ VariantFRep
  { tag: reflectSymbol tag
  , map: (map :: _ -> p _ -> p _)
  , bimap: (bimap :: _ -> _ -> q _ _ -> q _ _)
  , init: (init :: p _ -> Result p q _ _)
  , next: (next :: q _ _ -> _ -> Result p q _ _)
  , value
  }
  where
  coerceFrom :: VariantFRep p q a -> VariantF r a
  coerceFrom = unsafeCoerce

instance Functor (VariantF r) where
  map f v =
    let
      VariantFRep r = coerceTo v
    in
      coerceFrom $ VariantFRep $ r
        { value = r.map f r.value
        }
    where
    coerceTo :: forall p q a. VariantF r a -> VariantFRep p q a
    coerceTo = unsafeCoerce

    coerceFrom :: forall p q a. VariantFRep p q a -> VariantF r a
    coerceFrom = unsafeCoerce

-- | A row-based sum type of bifunctors applied to `a` and `b`.
data VariantB :: Row Type -> Type -> Type -> Type
data VariantB r a b

-- | The internal representation for `VariantB`.
newtype VariantBRep p q a b = VariantBRep
  { tag :: String
  , map :: forall x y. (x -> y) -> (p x -> p y)
  , bimap :: forall w x y z. (w -> x) -> (y -> z) -> q w y -> q x z
  , init :: forall c j. p j -> Result p q c j
  , next :: forall c j. q c j -> c -> Result p q c j
  , value :: q a b
  }

-- | Inject into a variant bifunctor given a tag.
injB
  :: forall p q r r' t a b
   . IsSymbol t
  => Dissect p q
  => Row.Cons t (Pair p q) r' r
  => Proxy t
  -> q a b
  -> VariantB r a b
injB tag value = coerceFrom $ VariantBRep
  { tag: reflectSymbol tag
  , map: (map :: _ -> p _ -> p _)
  , bimap: (bimap :: _ -> _ -> q _ _ -> q _ _)
  , init: (init :: p _ -> Result p q _ _)
  , next: (next :: q _ _ -> _ -> Result p q _ _)
  , value
  }
  where
  coerceFrom :: VariantBRep p q a b -> VariantB r a b
  coerceFrom = unsafeCoerce

instance Bifunctor (VariantB r) where
  bimap f g v =
    let
      VariantBRep r = coerceTo v
    in
      coerceFrom $ VariantBRep $ r
        { value = r.bimap f g r.value
        }
    where
    coerceTo :: forall p q a b. VariantB r a b -> VariantBRep p q a b
    coerceTo = unsafeCoerce

    coerceFrom :: forall p q a b. VariantBRep p q a b -> VariantB r a b
    coerceFrom = unsafeCoerce

instance Dissect (VariantF r) (VariantB r) where
  init v =
    let
      VariantFRep r = unsafeCoerce v
    in
      r.init r.value # unwrap >>> match
        { yield: \{ j, qcj } ->
            yield j $ unsafeCoerce $ VariantBRep $ r
              { value = qcj
              }
        , return: \pc ->
            return $ unsafeCoerce $ VariantFRep $ r
              { value = pc
              }
        }

  next v c =
    let
      VariantBRep r = unsafeCoerce v
    in
      r.next r.value c # unwrap >>> match
        { yield: \{ j, qcj } ->
            yield j $ unsafeCoerce $ VariantBRep $ r
              { value = qcj
              }
        , return: \pc ->
            return $ unsafeCoerce $ VariantFRep $ r
              { value = pc
              }
        }
