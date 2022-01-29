-- | This module provides a `VariantF`-like dissectible type. Helper
-- | functions for converting to `variant`-flavoured `VariantF`s and
-- | pattern matching are provided for convenience.
module Variant.Polynomial where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Functor.Variant as Variant
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect)
import Dissect.Runtime.Instances as Instances
import Foreign.Object (lookup)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Type.Prelude (class IsSymbol, Proxy(..), reflectSymbol)
import Type.Row (class Cons)
import Unsafe.Coerce (unsafeCoerce)
import Variant.Polynomial.Internal as Internal

data OpenVariantF :: forall k. Row (k -> Type) -> k -> Type
data OpenVariantF r a

inj
  :: forall n f t r a
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a
  -> OpenVariantF r a
inj proxy value = coerceV $ Internal.OpenVariantFRep
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.OpenVariantFRep f a -> OpenVariantF r a
  coerceV = unsafeCoerce

newtype VariantF :: forall k. Row (k -> Type) -> k -> Type
newtype VariantF r a =
  VariantF
    { instances :: Instances.Instances
    , value :: OpenVariantF r a
    }

instantiate
  :: forall r rl a
   . RL.RowToList r rl
  => Instances.FindInstances rl
  => OpenVariantF r a
  -> VariantF r a
instantiate value =
  VariantF { instances: Instances.instances (Proxy :: _ rl), value }

data OpenVariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
data OpenVariantF_2 r a b

inj_2
  :: forall n f t r a b
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a b
  -> OpenVariantF_2 r a b
inj_2 proxy value = coerceV $ Internal.OpenVariantFRep_2
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.OpenVariantFRep_2 f a b -> OpenVariantF_2 r a b
  coerceV = unsafeCoerce

newtype VariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
newtype VariantF_2 r a b =
  VariantF_2
    { instances :: Instances.Instances
    , value :: OpenVariantF_2 r a b
    }

instance Functor (VariantF r) where
  map f (VariantF wrapper@{ instances, value }) =
    let
      (Internal.OpenVariantFRep internals) = coerceR value
    in
      case lookup internals.tag instances.functors of
        Just functor ->
          let
            newValue = coerceV $ Internal.OpenVariantFRep
              (internals { value = functor.map f internals.value })
          in
            VariantF (wrapper { value = newValue })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Variant.Polynomial.Functor.map"
    where
    coerceV :: Internal.OpenVariantFRep _ _ -> OpenVariantF _ _
    coerceV = unsafeCoerce

    coerceR :: OpenVariantF _ _ -> Internal.OpenVariantFRep _ _
    coerceR = unsafeCoerce

instance Bifunctor (VariantF_2 r) where
  bimap f g (VariantF_2 wrapper@{ instances, value }) =
    let
      (Internal.OpenVariantFRep_2 internals) = coerceR value
    in
      case lookup internals.tag instances.bifunctors of
        Just bifunctor ->
          let
            newValue = coerceV $ Internal.OpenVariantFRep_2
              (internals { value = bifunctor.bimap f g internals.value })
          in
            VariantF_2 (wrapper { value = newValue })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Variant.Polynomial.Bifunctor.bimap"
    where
    coerceV :: Internal.OpenVariantFRep_2 _ _ _ -> OpenVariantF_2 _ _ _
    coerceV = unsafeCoerce

    coerceR :: OpenVariantF_2 _ _ _ -> Internal.OpenVariantFRep_2 _ _ _
    coerceR = unsafeCoerce

instance
  Instances.DissectRow r s =>
  Dissect (VariantF r) (VariantF_2 s) where
  right = case _ of
    Left (VariantF wrapper@{ instances, value }) ->
      let
        (Internal.OpenVariantFRep internals) = coerceR value
      in
        case lookup internals.tag instances.dissects of
          Just dissect -> case dissect.right (Left internals.value) of
            Left (Tuple yield inner) ->
              let
                outer = coerceV_2 (internals { value = inner })
              in
                Left (Tuple yield (VariantF_2 (wrapper { value = outer })))
            Right inner ->
              let
                outer = coerceV (internals { value = inner })
              in
                Right (VariantF (wrapper { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Variant.Polynomial.Dissect.right"
    Right (Tuple (VariantF_2 wrapper@{ instances, value }) c) ->
      let
        (Internal.OpenVariantFRep_2 internals) = coerceR_2 value
      in
        case lookup internals.tag instances.dissects of
          Just dissect -> case dissect.right (Right (Tuple internals.value c)) of
            Left (Tuple yield inner) ->
              let
                outer = coerceV_2 (internals { value = inner })
              in
                Left (Tuple yield (VariantF_2 (wrapper { value = outer })))
            Right inner ->
              let
                outer = coerceV (internals { value = inner })
              in
                Right (VariantF (wrapper { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Variant.Polynomial.Dissect.right"
    where
    coerceR :: OpenVariantF _ _ -> Internal.OpenVariantFRep _ _
    coerceR = unsafeCoerce

    coerceR_2 :: OpenVariantF_2 _ _ _ -> Internal.OpenVariantFRep_2 _ _ _
    coerceR_2 = unsafeCoerce

    coerceV :: _ -> OpenVariantF _ _
    coerceV = unsafeCoerce

    coerceV_2 :: _ -> OpenVariantF_2 _ _ _
    coerceV_2 = unsafeCoerce

-- | Convert a `VariantF` into a `VariantF` from `variant`.
convert :: forall r a. VariantF r a -> Variant.VariantF r a
convert (VariantF { instances: { functors }, value }) =
  let
    (Internal.OpenVariantFRep internals) = unsafeCoerce value
  in
    case lookup internals.tag functors of
      Just functor -> unsafeCoerce
        { "type": internals.tag
        , value: internals.value
        , map: functor.map
        }
      Nothing ->
        unsafeCrashWith "Pattern match failed at Variant.Polynomial.convert"

-- | Match a `VariantF` against a `Record` containing functions
-- | operating on each possible case. Like `on`, this function also
-- | takes a continuation for unmatched fields.
onMatch
  :: forall rl r r1 r2 r3 a b
   . RL.RowToList r rl
  => Variant.VariantFMatchCases rl r1 a b
  => R.Union r1 r2 r3
  => Record r
  -> (VariantF r2 a -> b)
  -> VariantF r3 a
  -> b
onMatch a b c = Variant.onMatch a (b <<< unsafeConvertFrom) (unsafeConvertTo c)
  where
  unsafeConvertTo :: forall r' a'. VariantF r' a' -> Variant.VariantF r' a'
  unsafeConvertTo (VariantF { value }) =
    let
      (Internal.OpenVariantFRep internals) = unsafeCoerce value
    in
      unsafeCoerce { "type": internals.tag, value: internals.value }

  unsafeConvertFrom :: forall r' a'. Variant.VariantF r' a' -> VariantF r' a'
  unsafeConvertFrom value =
    let
      internals = unsafeCoerce value
    in
      unsafeCoerce { value: { tag: internals."type", value: internals.value } }

-- | Match a `VariantF` against a `Record` exhaustively.
match
  :: forall rl r r1 r3 a b
   . RL.RowToList r rl
  => Variant.VariantFMatchCases rl r1 a b
  => R.Union r1 () r3
  => Record r
  -> VariantF r3 a
  -> b
match a c =
  onMatch a (\_ -> unsafeCrashWith "Variant.Polynomial: pattern match failed") c

-- | Combinator for pattern matching on `VariantF`.
case_ :: forall a b. VariantF () a -> b
case_ (VariantF { value }) = unsafeCrashWith case unsafeCoerce value of
  Internal.OpenVariantFRep w -> "Variant.Polynomial: pattern match failed in tag ["
    <> w.tag
    <> "]."

-- | Match a `VariantF` on a specific label. If the match fails,
-- | move to the failure callback with one less field.
on
  :: forall n r s p a b
   . R.Cons n p s r
  => IsSymbol n
  => Proxy n
  -> (p a -> b)
  -> (VariantF s a -> b)
  -> VariantF r a
  -> b
on p f g v@(VariantF { value }) =
  case coerceV value of
    Internal.OpenVariantFRep w
      | w.tag == reflectSymbol p -> f w.value
    _ ->
      g (coerceR v)
  where
  coerceV :: OpenVariantF _ _ -> Internal.OpenVariantFRep _ _
  coerceV = unsafeCoerce

  coerceR :: VariantF r _ -> VariantF s _
  coerceR = unsafeCoerce
