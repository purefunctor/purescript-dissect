-- | This module provides a dissectible `Record`-like type. Similar to
-- | `VariantF`, this serves as an alternative to deeply-nested `Product`
-- | types. Note that the order in which values are yielded is based on
-- | the row type signature.
module Record.Polynomial where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Dissect.Class (class Dissect, Input(..), Output(..))
import Dissect.Runtime.Instances as Instances
import Foreign.Object (lookup)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Record.Unsafe as Record
import Type.Equality (class TypeEquals)
import Type.Prelude (class IsSymbol, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

-- | A record whose values are functors parameterized by some type `a`.
data RecordF :: Row (Type -> Type) -> Type -> Type
data RecordF r a

class ToAux :: RL.RowList (Type -> Type) -> Type -> Row Type -> Constraint
class ToAux rl a r | rl a -> r

instance ToAux RL.Nil a ()

else instance
  ( ToAux future argument farFuture
  , R.Cons name (functor argument) farFuture farFutureWithElement
  ) =>
  ToAux (RL.Cons name functor future) argument farFutureWithElement

class To :: Row (Type -> Type) -> Type -> Row Type -> Constraint
class To r a r' | r a -> r'

instance (RL.RowToList r rl, ToAux rl a r') => To r a r'

-- | Convert a `RecordF` back into a `Record`.
to :: forall r a r'. To r a r' => RecordF r a -> Record r'
to = unsafeCoerce >>> _.values

class FindKeys :: forall k. RL.RowList k -> Constraint
class FindKeys rl where
  findKeys :: Proxy rl -> List String

instance FindKeys RL.Nil where
  findKeys _ = mempty

else instance (FindKeys future, IsSymbol label) => FindKeys (RL.Cons label value future) where
  findKeys _ = current : future
    where
    current = reflectSymbol (Proxy :: _ label)
    future = findKeys (Proxy :: _ future)

class FromAux :: RL.RowList Type -> Type -> Row (Type -> Type) -> Constraint
class FromAux rl a r | rl -> a r

instance FromAux RL.Nil a ()

else instance
  ( FromAux future futureArgument farFuture
  , TypeEquals argument futureArgument
  , R.Cons name functor farFuture farFutureWithFunctor
  ) =>
  FromAux (RL.Cons name (functor argument) future) futureArgument farFutureWithFunctor

class From :: Row Type -> Type -> Row (Type -> Type) -> Constraint
class From r a r' | r -> a r'

instance (RL.RowToList r rl, FromAux rl a r') => From r a r'

-- | Convert a `Record` into a `RecordF`.
from
  :: forall r a r' rl'
   . From r a r'
  => RL.RowToList r' rl'
  => Instances.FindInstances rl'
  => FindKeys rl'
  => Record r
  -> RecordF r' a
from values =
  unsafeCoerce
    { instances: Instances.instances (Proxy :: _ rl')
    , keys: findKeys (Proxy :: _ rl')
    , values
    }

foreign import mapRecordF :: forall r a b. (a -> b) -> (RecordF r a) -> (RecordF r b)

instance Functor (RecordF r) where
  map = mapRecordF

data RecordF_2 :: Row (Type -> Type -> Type) -> Type -> Type -> Type
data RecordF_2 r a b

foreign import bimapRecordF
  :: forall r a b c d. (a -> c) -> (b -> d) -> (RecordF_2 r a b -> RecordF_2 r c d)

instance Bifunctor (RecordF_2 r) where
  bimap = bimapRecordF

foreign import unsafeLength :: Record _ -> Int

foreign import unsafeHead :: Record _ -> { key :: String, value :: _, rest :: Record _ }

instance Instances.DissectRow r s => Dissect (RecordF r) (RecordF_2 s) where
  right = case _ of
    Init record ->
      let
        { instances, keys, values } = coerceInternals record

        aux finishedValues currentKeys =
          case currentKeys of
            Nil ->
              Return (unsafeCoerce { instances, keys, values: finishedValues })
            key : keysRest ->
              let
                value = Record.unsafeGet key values
              in
                case lookup key instances.dissects of
                  Just dissect -> case dissect.right (Init value) of
                    Yield yield holedValue ->
                      Yield yield
                        ( unsafeCoerce
                            { instances
                            , keys
                            , values
                            , holed: { key, value: holedValue }
                            , keysTodo: keysRest
                            , valuesFinished: finishedValues
                            }
                        )
                    Return finished ->
                      aux (Record.unsafeSet key finished finishedValues) keysRest
                  Nothing ->
                    unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"
      in
        aux {} keys
    Next record filler ->
      let
        { instances, keys, values, holed, keysTodo, valuesFinished } = coerceInternals_2 record

        aux finishedValues currentKeys =
          case currentKeys of
            Nil ->
              Return (unsafeCoerce { instances, keys, values: finishedValues })
            key : keysRest ->
              let
                value = Record.unsafeGet key values
              in
                case lookup key instances.dissects of
                  Just dissect -> case dissect.right (Init value) of
                    Yield yield holedValue ->
                      Yield yield
                        ( unsafeCoerce
                            { instances
                            , keys
                            , values
                            , holed: { key, value: holedValue }
                            , keysTodo: keysRest
                            , valuesFinished: finishedValues
                            }
                        )
                    Return finished ->
                      aux (Record.unsafeSet key finished finishedValues) keysRest
                  Nothing ->
                    unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"
      in
        case lookup holed.key instances.dissects of
          Just dissect -> case dissect.right (Next holed.value filler) of
            Yield yield deeper ->
              Yield yield
                ( unsafeCoerce
                    { instances
                    , keys
                    , values
                    , holed: holed { value = deeper }
                    , keysTodo
                    , valuesFinished
                    }
                )
            Return finished ->
              aux (Record.unsafeSet holed.key finished valuesFinished) keysTodo
          Nothing ->
            unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"

    where
    coerceInternals
      :: _ -> { instances :: Instances.Instances, keys :: List String, values :: Record _ }
    coerceInternals = unsafeCoerce

    coerceInternals_2
      :: _
      -> { instances :: Instances.Instances
         , keys :: _
         , values :: _
         , holed :: _
         , keysTodo :: _
         , valuesFinished :: _
         }
    coerceInternals_2 = unsafeCoerce
