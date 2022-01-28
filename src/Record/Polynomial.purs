module Record.Polynomial where

import Prelude

import Data.Functor.Polynomial.Variant.Internal as Internal
import Prim.Row as R
import Prim.RowList as RL
import Type.Equality (class TypeEquals)
import Type.Prelude (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

data RecordF :: Row (Type -> Type) -> Type -> Type
data RecordF r a

class ToAux :: RL.RowList (Type -> Type) -> Type -> Row Type -> Constraint
class ToAux rl a r | rl a -> r

instance ToAux RL.Nil a ()

else instance
  ( ToAux future argument farFuture
  , R.Cons name (functor argument) farFuture farFutureWithElement
  ) => ToAux (RL.Cons name functor future) argument farFutureWithElement

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
  )
  => FromAux (RL.Cons name (functor argument) future) futureArgument farFutureWithFunctor

class From :: Row Type -> Type -> Row (Type -> Type) -> Constraint
class From r a r' | r -> a r'

instance (RL.RowToList r rl, FromAux rl a r') => From r a r'

from :: forall r a r' rl'. From r a r' => RL.RowToList r' rl' => Internal.FindInstances rl' => Record r -> RecordF r' a
from values = unsafeCoerce { instances: Internal.instances (Proxy :: _ rl'), values }

foreign import mapRecordF :: forall r a b. (a -> b) -> (RecordF r a) -> (RecordF r b)

instance Functor (RecordF r) where
  map = mapRecordF
