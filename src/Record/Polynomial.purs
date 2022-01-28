module Record.Polynomial where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect)
import Foreign.Object (lookup)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as R
import Prim.RowList as RL
import Record.Unsafe as Record
import Type.Equality (class TypeEquals)
import Type.Prelude (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)
import Variant.Polynomial.Internal as Internal

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

to :: forall r a r'. To r a r' => RecordF r a -> Record r'
to = unsafeCoerce >>> _.values

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

from
  :: forall r a r' rl'
   . From r a r'
  => RL.RowToList r' rl'
  => Internal.FindInstances rl'
  => Record r
  -> RecordF r' a
from values = unsafeCoerce { instances: Internal.instances (Proxy :: _ rl'), values }

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

instance Internal.DissectRow r s => Dissect (RecordF r) (RecordF_2 s) where
  right = case _ of
    Left record ->
      let
        { instances, values } = coerceInternals record

        aux accumulator current
          | unsafeLength current == 0 =
              Right (unsafeCoerce { instances, values: accumulator })
          | otherwise =
              let
                { key, value, rest } = unsafeHead current
              in
                case lookup key instances.dissects of
                  Just dissect -> case dissect.right (Left value) of
                    Left (Tuple yield holed) ->
                      Left
                        ( Tuple yield
                            ( unsafeCoerce
                                { instances
                                , holed: { key, value: holed }
                                , done: accumulator
                                , todo: rest
                                }
                            )
                        )
                    Right done ->
                      aux (Record.unsafeSet key done accumulator) rest
                  Nothing ->
                    unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"
      in
        aux {} values
    Right (Tuple record value) ->
      let
        { instances, holed, done, todo } = coerceInternals_2 record

        aux accumulator current
          | unsafeLength current == 0 =
              Right (unsafeCoerce { instances, values: accumulator })
          | otherwise =
              let
                { key, value, rest } = unsafeHead current
              in
                case lookup key instances.dissects of
                  Just dissect -> case dissect.right (Left value) of
                    Left (Tuple yield deeper) ->
                      Left
                        ( Tuple yield
                            ( unsafeCoerce
                                { instances
                                , holed: { key, value: deeper }
                                , done: accumulator
                                , todo: rest
                                }
                            )
                        )
                    Right done ->
                      aux (Record.unsafeSet key done accumulator) rest
                  Nothing ->
                    unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"
      in
        case lookup holed.key instances.dissects of
          Just dissect -> case dissect.right (Right (Tuple holed.value value)) of
            Left (Tuple yield deeper) ->
              Left
                ( Tuple yield
                    ( unsafeCoerce
                        { instances, holed: { key: holed.key, value: deeper }, done, todo }
                    )
                )
            Right filled ->
              aux (Record.unsafeSet holed.key filled done) todo
          Nothing ->
            unsafeCrashWith "Pattern match failed at Record.Polynomial.Dissec.right"
    where
    coerceInternals :: _ -> { instances :: Internal.Instances, values :: Record _ }
    coerceInternals = unsafeCoerce

    coerceInternals_2
      :: _ -> { instances :: Internal.Instances, holed :: _, done :: _, todo :: _ }
    coerceInternals_2 = unsafeCoerce
