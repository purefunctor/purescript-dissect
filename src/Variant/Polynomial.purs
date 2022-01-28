-- | This module provides a `VariantF`-like dissectible type. Helper
-- | functions for converting to `variant`-flavoured `VariantF`s and
-- | pattern matching are provided for convenience.
module Variant.Polynomial where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Variant.Polynomial.Internal as Internal
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

data PreVariantF :: forall k. Row (k -> Type) -> k -> Type
data PreVariantF r a

inj
  :: forall n f t r a
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a
  -> PreVariantF r a
inj proxy value = coerceV $ Internal.VariantFRep
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.VariantFRep f a -> PreVariantF r a
  coerceV = unsafeCoerce

newtype VariantF :: forall k. Row (k -> Type) -> k -> Type
newtype VariantF r a =
  VariantF
    { functors :: Object Internal.FunctorClass
    , bifunctors :: Object Internal.BifunctorClass
    , dissects :: Object Internal.DissectClass
    , value :: PreVariantF r a
    }

instantiate
  :: forall r rl a
   . RL.RowToList r rl
  => Internal.FindInstances rl
  => PreVariantF r a
  -> VariantF r a
instantiate value =
  VariantF { functors, bifunctors, dissects, value }
  where
  { functors, bifunctors, dissects } = Internal.instances (Proxy :: _ rl)

data PreVariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
data PreVariantF_2 r a b

inj_2
  :: forall n f t r a b
   . Cons n f t r
  => IsSymbol n
  => Proxy n
  -> f a b
  -> PreVariantF_2 r a b
inj_2 proxy value = coerceV $ Internal.VariantFRep_2
  { tag: reflectSymbol proxy
  , value
  }
  where
  coerceV :: Internal.VariantFRep_2 f a b -> PreVariantF_2 r a b
  coerceV = unsafeCoerce

newtype VariantF_2 :: forall k l. Row (k -> l -> Type) -> k -> l -> Type
newtype VariantF_2 r a b =
  VariantF_2
    { functors :: Object Internal.FunctorClass
    , bifunctors :: Object Internal.BifunctorClass
    , dissects :: Object Internal.DissectClass
    , value :: PreVariantF_2 r a b
    }

instance Functor (VariantF r) where
  map f (VariantF closed@{ functors, value }) =
    let
      (Internal.VariantFRep v) = coerceR value
    in
      case lookup v.tag functors of
        Just functor ->
          let
            outer = coerceV $ Internal.VariantFRep (v { value = functor.map f v.value })
          in
            VariantF (closed { value = outer })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Functor.map"
    where
    coerceV :: Internal.VariantFRep _ _ -> PreVariantF _ _
    coerceV = unsafeCoerce

    coerceR :: PreVariantF _ _ -> Internal.VariantFRep _ _
    coerceR = unsafeCoerce

instance Bifunctor (VariantF_2 r) where
  bimap f g (VariantF_2 closed@{ bifunctors, value }) =
    let
      (Internal.VariantFRep_2 v) = coerceR value
    in
      case lookup v.tag bifunctors of
        Just bifunctor ->
          let
            outer = coerceV $ Internal.VariantFRep_2 (v { value = bifunctor.bimap f g v.value })
          in
            VariantF_2 (closed { value = outer })
        Nothing ->
          unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Bifunctor.bimap"
    where
    coerceV :: Internal.VariantFRep_2 _ _ _ -> PreVariantF_2 _ _ _
    coerceV = unsafeCoerce

    coerceR :: PreVariantF_2 _ _ _ -> Internal.VariantFRep_2 _ _ _
    coerceR = unsafeCoerce

instance
  Internal.DissectRow r s =>
  Dissect (VariantF r) (VariantF_2 s) where
  right = case _ of
    Left (VariantF closed@{ dissects, value: x }) ->
      let
        (Internal.VariantFRep v) = coerceR x
      in
        case lookup v.tag dissects of
          Just dissect -> case dissect.right (Left v.value) of
            Left (Tuple j inner) ->
              let
                outer = coerceV_2 (v { value = inner })
              in
                Left (Tuple j (VariantF_2 (closed { value = outer })))
            Right inner ->
              let
                outer = coerceV (v { value = inner })
              in
                Right (VariantF (closed { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Dissect.right"
    Right (Tuple (VariantF_2 closed@{ dissects, value: x }) c) ->
      let
        (Internal.VariantFRep_2 v) = coerceR_2 x
      in
        case lookup v.tag dissects of
          Just dissect -> case dissect.right (Right (Tuple v.value c)) of
            Left (Tuple j inner) ->
              let
                outer = coerceV_2 (v { value = inner })
              in
                Left (Tuple j (VariantF_2 (closed { value = outer })))
            Right inner ->
              let
                outer = coerceV (v { value = inner })
              in
                Right (VariantF (closed { value = outer }))
          Nothing ->
            unsafeCrashWith "Pattern match failed at Data.Functor.Polynomial.Variant.Dissect.right"
    where
    coerceR :: PreVariantF _ _ -> Internal.VariantFRep _ _
    coerceR = unsafeCoerce

    coerceR_2 :: PreVariantF_2 _ _ _ -> Internal.VariantFRep_2 _ _ _
    coerceR_2 = unsafeCoerce

    coerceV :: _ -> PreVariantF _ _
    coerceV = unsafeCoerce

    coerceV_2 :: _ -> PreVariantF_2 _ _ _
    coerceV_2 = unsafeCoerce

-- | Convert a `VariantF` into a `VariantF` from `variant`.
convert :: forall r a. VariantF r a -> Variant.VariantF r a
convert (VariantF { functors, value }) =
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
      (Internal.VariantFRep internals) = unsafeCoerce value
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
  onMatch a (\_ -> unsafeCrashWith "Data.Functor.Polynomial.Variant: pattern match failed") c

-- | Combinator for pattern matching on `VariantF`.
case_ ∷ ∀ a b. VariantF () a → b
case_ (VariantF { value }) = unsafeCrashWith case unsafeCoerce value of
  Internal.VariantFRep w → "Data.Functor.Polynomial.Variant: pattern match failed in tag [" <> w.tag <> "]."

-- | Match a `VariantF` on a specific label. If the match fails,
-- | move to the failure callback with one less field.
on
  ∷ ∀ n r s p a b
  . R.Cons n p s r
  ⇒ IsSymbol n
  ⇒ Proxy n
  → (p a → b)
  → (VariantF s a → b)
  → VariantF r a
  → b
on p f g v@(VariantF { value }) =
  case coerceV value of
    Internal.VariantFRep w
      | w.tag == reflectSymbol p → f w.value
    _ →
      g (coerceR v)
  where
  coerceV ∷ PreVariantF _ _ → Internal.VariantFRep _ _
  coerceV = unsafeCoerce

  coerceR ∷ VariantF r _ → VariantF s _
  coerceR = unsafeCoerce