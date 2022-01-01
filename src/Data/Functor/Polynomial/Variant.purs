-- | This module provides a `VariantF`-like type specialized to contain
-- | polynomial functors and to be dissectible itself. Likewise,
-- | operations such as `inj`, `case_`, and `on` are also provided.
-- |
-- | See also: https://pursuit.purescript.org/packages/purescript-variant/
module Data.Functor.Polynomial.Variant where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Functor.Polynomial.Variant.Internal as Internal
import Data.Functor.Variant as Variant
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect)
import Foreign.Object (Object, lookup)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Type.Prelude (class IsSymbol, Proxy(..), reflectSymbol)
import Type.Row (class Cons)
import Unsafe.Coerce (unsafeCoerce)

data VariantF :: forall k. Row (k -> Type) -> k -> Type
data VariantF r a

inj
  :: forall n f t r a
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a
  -> VariantF r a
inj proxy value = coerceV $ Internal.VariantFRep
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.VariantFRep f a -> VariantF r a
  coerceV = unsafeCoerce

newtype ClosedVariantF :: forall k. Row (k -> Type) -> k -> Type
newtype ClosedVariantF r a =
  ClosedVariantF
    { functors :: Object Internal.FunctorClass
    , bifunctors :: Object Internal.BifunctorClass
    , dissects :: Object Internal.DissectClass
    -- , plugs :: Object Internal.PlugClass
    , value :: VariantF r a
    }

close
  :: forall r rl a
   . RL.RowToList r rl
  => Internal.FindInstances rl
  => VariantF r a
  -> ClosedVariantF r a
close value =
  ClosedVariantF { functors, bifunctors, dissects, {- plugs, -} value }
  where
  { functors, bifunctors, dissects } = Internal.instances (Proxy :: _ rl)

data VariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
data VariantF_2 r a b

inj_2
  :: forall n f t r a b
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a b
  -> VariantF_2 r a b
inj_2 proxy value = coerceV $ Internal.VariantFRep_2
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.VariantFRep_2 f a b -> VariantF_2 r a b
  coerceV = unsafeCoerce

newtype ClosedVariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
newtype ClosedVariantF_2 r a b =
  ClosedVariantF_2
    { functors :: Object Internal.FunctorClass
    , bifunctors :: Object Internal.BifunctorClass
    , dissects :: Object Internal.DissectClass
    -- , plugs :: Object Internal.PlugClass
    , value :: VariantF_2 r a b
    }

instance Functor (ClosedVariantF r) where
  map f (ClosedVariantF closed@{ functors, value }) =
    let
      (Internal.VariantFRep v) = coerceR value
    in
      case lookup v.tag functors of
        Just functor ->
          let
            outer = coerceV $ Internal.VariantFRep (v { value = functor.map f v.value })
          in
            ClosedVariantF (closed { value = outer })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Functor.map"
    where
    coerceV :: Internal.VariantFRep _ _ -> VariantF _ _
    coerceV = unsafeCoerce

    coerceR :: VariantF _ _ -> Internal.VariantFRep _ _
    coerceR = unsafeCoerce

instance Bifunctor (ClosedVariantF_2 r) where
  bimap f g (ClosedVariantF_2 closed@{ bifunctors, value }) =
    let
      (Internal.VariantFRep_2 v) = coerceR value
    in
      case lookup v.tag bifunctors of
        Just bifunctor ->
          let
            outer = coerceV $ Internal.VariantFRep_2 (v { value = bifunctor.bimap f g v.value })
          in
            ClosedVariantF_2 (closed { value = outer })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Bifunctor.bimap"
    where
    coerceV :: Internal.VariantFRep_2 _ _ _ -> VariantF_2 _ _ _
    coerceV = unsafeCoerce

    coerceR :: VariantF_2 _ _ _ -> Internal.VariantFRep_2 _ _ _
    coerceR = unsafeCoerce

instance
  Internal.DissectRow r s =>
  Dissect (ClosedVariantF r) (ClosedVariantF_2 s) where
  right = case _ of
    Left (ClosedVariantF closed@{ dissects, value: x }) ->
      let
        (Internal.VariantFRep v) = coerceR x
      in
        case lookup v.tag dissects of
          Just dissect -> case dissect.right (Left v.value) of
            Left (Tuple j inner) ->
              let
                outer = coerceV_2 (v { value = inner })
              in
                Left (Tuple j (ClosedVariantF_2 (closed { value = outer })))
            Right inner ->
              let
                outer = coerceV (v { value = inner })
              in
                Right (ClosedVariantF (closed { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Dissect.right"
    Right (Tuple (ClosedVariantF_2 closed@{ dissects, value: x }) c) ->
      let
        (Internal.VariantFRep_2 v) = coerceR_2 x
      in
        case lookup v.tag dissects of
          Just dissect -> case dissect.right (Right (Tuple v.value c)) of
            Left (Tuple j inner) ->
              let
                outer = coerceV_2 (v { value = inner })
              in
                Left (Tuple j (ClosedVariantF_2 (closed { value = outer })))
            Right inner ->
              let
                outer = coerceV (v { value = inner })
              in
                Right (ClosedVariantF (closed { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Dissect.right"
    where
    coerceR :: VariantF _ _ -> Internal.VariantFRep _ _
    coerceR = unsafeCoerce

    coerceR_2 :: VariantF_2 _ _ _ -> Internal.VariantFRep_2 _ _ _
    coerceR_2 = unsafeCoerce

    coerceV :: _ -> VariantF _ _
    coerceV = unsafeCoerce

    coerceV_2 :: _ -> VariantF_2 _ _ _
    coerceV_2 = unsafeCoerce

convert :: forall r a. ClosedVariantF r a -> Variant.VariantF r a
convert (ClosedVariantF { functors, value }) =
  let
    (Internal.VariantFRep internals) = unsafeCoerce value
  in
    case lookup internals.tag functors of
      Just functor -> unsafeCoerce
        { "type": internals.tag
        , value: internals.value
        , map: functor.map
        }
      Nothing ->
        unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.convert"

unsafeOnMatch
  :: forall rl r r1 r2 r3 a b
   . RL.RowToList r rl
  => Variant.VariantFMatchCases rl r1 a b
  => R.Union r1 r2 r3
  => Record r
  -> (ClosedVariantF r2 a -> b)
  -> ClosedVariantF r3 a
  -> b
unsafeOnMatch a b c = Variant.onMatch a (b <<< unsafeConvertFrom) (unsafeConvertTo c)
  where
  unsafeConvertTo :: forall r' a'. ClosedVariantF r' a' -> Variant.VariantF r' a'
  unsafeConvertTo (ClosedVariantF { value }) =
    let
      (Internal.VariantFRep internals) = unsafeCoerce value
    in
      unsafeCoerce { "type": internals.tag, value: internals.value }

  unsafeConvertFrom :: forall r' a'. Variant.VariantF r' a' -> ClosedVariantF r' a'
  unsafeConvertFrom value =
    let
      internals = unsafeCoerce value
    in
      unsafeCoerce { value: { tag: internals."type", value: internals.value } }

unsafeMatch
  :: forall rl r r1 r3 a b
   . RL.RowToList r rl
  => Variant.VariantFMatchCases rl r1 a b
  => R.Union r1 () r3
  => Record r
  -> ClosedVariantF r3 a
  -> b
unsafeMatch a c =
  unsafeOnMatch a (\_ -> unsafeCrashWith "Pattern match failed.") c

case_ ∷ ∀ a b. ClosedVariantF () a → b
case_ (ClosedVariantF { value }) = unsafeCrashWith case unsafeCoerce value of
  Internal.VariantFRep w → "Data.Functor.Polynomial.Variant: pattern match failed in tag [" <> w.tag <> "]."

on
  ∷ ∀ n r s p a b
  . R.Cons n p s r
  ⇒ IsSymbol n
  ⇒ Proxy n
  → (p a → b)
  → (ClosedVariantF s a → b)
  → ClosedVariantF r a
  → b
on p f g v@(ClosedVariantF { value }) =
  case coerceV value of
    Internal.VariantFRep w
      | w.tag == reflectSymbol p → f w.value
    _ →
      g (coerceR v)
  where
  coerceV ∷ VariantF _ _ → Internal.VariantFRep _ _
  coerceV = unsafeCoerce

  coerceR ∷ ClosedVariantF r _ → ClosedVariantF s _
  coerceR = unsafeCoerce
