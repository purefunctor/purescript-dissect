-- | This module provides a `VariantF`-like type specialized to contain
-- | polynomial functors and to be dissectible itself. Likewise,
-- | operations such as `inj`, `case_`, and `on` are also provided.
-- |
-- | See also: https://pursuit.purescript.org/packages/purescript-variant/
module Data.Functor.Polynomial.Variant where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Functor.Polynomial.Variant.Internal (VariantFRep(..), VariantFRep_2(..))
import Dissect.Class (class Dissect, class Plug, Garden(..), CoGarden(..), plug, right)
import Partial.Unsafe (unsafeCrashWith)
import Type.Row as R
import Type.RowList as RL
import Type.Prelude (class IsSymbol, Proxy, reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

data VariantF ∷ ∀ k. Row (k → Type) → k → Type
data VariantF r a

-- | Inject a polynomial functor to a variant given a label.
inj
  ∷ ∀ n p q t r a
  . Functor p
  ⇒ Bifunctor q
  ⇒ R.Cons n p t r
  ⇒ IsSymbol n
  ⇒ Dissect p q
  ⇒ Plug p q
  ⇒ Proxy n
  → p a
  → VariantF r a
inj proxy value = coerceV $ VariantFRep
  { tag: reflectSymbol proxy
  , value
  , map
  , bimap
  , right
  , plug
  }
  where
  coerceV ∷ VariantFRep p q a → VariantF r a
  coerceV = unsafeCoerce

-- | Combinator for pattern matching.
case_ ∷ ∀ a b. VariantF () a → b
case_ v = unsafeCrashWith case unsafeCoerce v of
  VariantFRep w → "Data.Functor.Polynomial.Extra: pattern match failed in tag [" <> w.tag <> "]."

-- | Attempt to read a variant given a label, defaulting to a failure
-- | branch with the failing label removed.
on
  ∷ ∀ n r s p a b
  . R.Cons n p s r
  ⇒ IsSymbol n
  ⇒ Proxy n
  → (p a → b)
  → (VariantF s a → b)
  → VariantF r a
  → b
on p f g v =
  case coerceV v of
    VariantFRep w
      | w.tag == reflectSymbol p → f w.value
    _ →
      g (coerceR v)
  where
  coerceV ∷ VariantF _ _ → VariantFRep _ _ _
  coerceV = unsafeCoerce

  coerceR ∷ VariantF r _ → VariantF s _
  coerceR = unsafeCoerce

instance Functor (VariantF r) where
  map f v =
    case coerceV v of
      VariantFRep w → coerceR $ VariantFRep
        { tag: w.tag
        , value: w.map f w.value
        , map: w.map
        , bimap: w.bimap
        , right: w.right
        , plug: w.plug
        }

    where
    coerceV ∷ VariantF _ _ → VariantFRep _ _ _
    coerceV = unsafeCoerce

    coerceR ∷ VariantFRep _ _ _ → VariantF _ _
    coerceR = unsafeCoerce

data VariantF_2 ∷ Row (Type → Type → Type) → Type → Type → Type
data VariantF_2 r a b

inj_2
  ∷ ∀ n p q t r a b
  . Functor p
  ⇒ Bifunctor q
  ⇒ R.Cons n q t r
  ⇒ IsSymbol n
  ⇒ Dissect p q
  ⇒ Plug p q
  ⇒ Proxy n
  → q a b
  → VariantF_2 r a b
inj_2 proxy value = coerceV $ VariantFRep_2
  { tag: reflectSymbol proxy
  , value
  , map
  , bimap
  , right
  , plug
  }
  where
  coerceV ∷ VariantFRep_2 p q a b → VariantF_2 r a b
  coerceV = unsafeCoerce

instance Bifunctor (VariantF_2 r) where
  bimap f g v =
    case coerceV v of
      VariantFRep_2 w →
        coerceW $ VariantFRep_2
          { tag: w.tag
          , value: w.bimap f g w.value
          , map: w.map
          , bimap: w.bimap
          , right: w.right
          , plug: w.plug
          }
    where
    coerceV ∷ VariantF_2 _ _ _ → VariantFRep_2 _ _ _ _
    coerceV = unsafeCoerce

    coerceW ∷ VariantFRep_2 _ _ _ _ → VariantF_2 _ _ _
    coerceW = unsafeCoerce

class DissectRow ∷ RL.RowList (Type → Type) → RL.RowList (Type → Type → Type) → Constraint
class DissectRow r s | r → s

instance DissectRow RL.Nil RL.Nil

else instance (DissectRow r s, Dissect p q) ⇒ DissectRow (RL.Cons n p r) (RL.Cons n q s)

instance
  ( RL.RowToList r r'
  , DissectRow r' s'
  , RL.ListToRow s' s
  ) ⇒
  Dissect (VariantF r) (VariantF_2 s) where
  -- This is a lot more intuitive than it looks, but this is essentially
  -- just taking the internal value, dissecting that, and then wrapping
  -- it back to the appropriate type, much like `Sum`, but a lot more
  -- messy and `unsafeCoerce`-ey.
  right x =
    case x of
      Pluck w →
        let
          (VariantFRep w') = coerceW w
        in
          mind w' (w'.right (Pluck w'.value))
      Plant c w_2 →
        let
          (VariantFRep_2 w_2') = coerceW_2 w_2
        in
          mind w_2' (w_2'.right (Plant c w_2'.value))
    where
    coerceW ∷ VariantF _ _ → VariantFRep _ _ _
    coerceW = unsafeCoerce

    coerceW_2 ∷ VariantF_2 _ _ _ → VariantFRep_2 _ _ _ _
    coerceW_2 = unsafeCoerce

    coerceI_2 ∷ _ → VariantF_2 _ _ _
    coerceI_2 = unsafeCoerce

    coerceI ∷ _ → VariantF _ _
    coerceI = unsafeCoerce

    mind w (CoPlant j v) = CoPlant j (coerceI_2 (w { value = v }))
    mind w (CoPluck d) = CoPluck (coerceI (w { value = d }))

class PlugRow ∷ RL.RowList (Type → Type) → RL.RowList (Type → Type → Type) → Constraint
class PlugRow r s | r → s

instance PlugRow RL.Nil RL.Nil

else instance (PlugRow r s, Plug p q) ⇒ PlugRow (RL.Cons n p r) (RL.Cons n q s)

instance
  ( RL.RowToList r r'
  , DissectRow r' s'
  , PlugRow r' s'
  , RL.ListToRow s' s
  ) ⇒
  Plug (VariantF r) (VariantF_2 s) where
  plug x v =
    let
      (VariantFRep_2 w) = coerceW_2 v
    in
      coerceI (w { value = w.plug x w.value })
    where
    coerceW_2 ∷ VariantF_2 _ _ _ → VariantFRep_2 _ _ _ _
    coerceW_2 = unsafeCoerce

    coerceI ∷ _ → VariantF _ _
    coerceI = unsafeCoerce
