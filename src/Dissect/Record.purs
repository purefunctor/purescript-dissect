-- | Record-based product types, `RecordF` and `RecordB` which form a `Dissect`
-- | instance. Useful for defining data types algebraically while also having
-- | decent runtime performance and convenient pattern matching syntax.
module Dissect.Record where

import Prelude

import Data.Array as Array
import Data.Bifunctor (class Bifunctor, bimap)
import Dissect.Class (class Dissect, Result, init, next)
import Foreign.Object (Object)
import Foreign.Object as Object
import Prim.Row as Row
import Prim.RowList (RowList)
import Prim.RowList as RowList
import Type.Equality (class TypeEquals)
import Type.Prelude (class IsSymbol, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

type Instances =
  { map :: forall p a b. (a -> b) -> (p a -> p b)
  , bimap :: forall q a b c d. (a -> b) -> (c -> d) -> q a c -> q b d
  , init :: forall p q c j. p j -> Result p q c j
  , next :: forall p q c j. q c j -> c -> Result p q c j
  }

-- | A record-based product type of functors applied to `a`.
data RecordF :: Row Type -> Type -> Type
data RecordF r a

-- | The internal representation for `RecordF`.
newtype RecordFRep :: Type -> Type
newtype RecordFRep a = RecordFRep
  { names :: Array String
  , instances :: Object Instances
  , values :: forall p. Object (p a)
  }

foreign import mapRecordF :: forall r a b. (a -> b) -> (RecordF r a) -> (RecordF r b)

instance Functor (RecordF r) where
  map = mapRecordF

-- | A record-based product type of bifunctors applied to `a` and `b`.
data RecordB :: Row Type -> Type -> Type -> Type
data RecordB r a b

newtype RecordBRep :: Type -> Type -> Type
newtype RecordBRep a b = RecordBRep
  { names :: Array String
  , instances :: Object Instances
  , values :: forall p. Object (p a)
  , currentName :: String
  , currentValue :: forall q. q a b
  , namesRest :: Array String
  , valuesFinished :: forall p. Object (p a)
  }

foreign import bimapRecordF
  :: forall r a b c d. (a -> c) -> (b -> d) -> (RecordB r a b -> RecordB r c d)

instance Bifunctor (RecordB r) where
  bimap = bimapRecordF

foreign import initRecordF :: forall r c j. RecordF r j -> Result (RecordF r) (RecordB r) c j

foreign import nextRecordF :: forall r c j. RecordB r c j -> c -> Result (RecordF r) (RecordB r) c j

instance Dissect (RecordF r) (RecordB r) where
  init = initRecordF
  next = nextRecordF

-- | A pair of a `Functor` and a `Bifunctor`.
foreign import data Pair :: (Type -> Type) -> (Type -> Type -> Type) -> Type

class FromAux :: RowList Type -> Type -> Row Type -> Constraint
class FromAux rl a r | rl -> a r where
  fromAux :: Proxy rl -> { names :: Array String, instances :: Object Instances }

instance FromAux RowList.Nil a () where
  fromAux _ = { names: [], instances: Object.empty }

else instance
  ( IsSymbol name
  , FromAux future futureArgument farFuture
  , TypeEquals argument futureArgument
  , Dissect functor bifunctor
  , Row.Cons name (Pair functor bifunctor) farFuture farFutureWithFunctor
  ) =>
  FromAux (RowList.Cons name (functor argument) future) futureArgument farFutureWithFunctor where
  fromAux _ =
    { names: Array.cons name future.names
    , instances: Object.insert name current future.instances
    }
    where
    name :: String
    name = reflectSymbol (Proxy :: Proxy name)

    current :: Instances
    current =
      { map: unsafeCoerce (map :: _ -> functor _ -> functor _)
      , bimap: unsafeCoerce (bimap :: _ -> _ -> bifunctor _ _ -> bifunctor _ _)
      , init: unsafeCoerce (init :: functor _ -> Result functor bifunctor _ _)
      , next: unsafeCoerce (next :: bifunctor _ _ -> _ -> Result functor bifunctor _ _)
      }

    future :: { names :: Array String, instances :: Object Instances }
    future = fromAux (Proxy :: Proxy future)

-- | Converts a `Record` into a `RecordF`.
class From :: Row Type -> Type -> Row Type -> Constraint
class From r a r' | r -> a r' where
  from :: Record r -> RecordF r' a

instance (RowList.RowToList r rl, FromAux rl a r') => From r a r' where
  from values =
    let
      metadata = fromAux (Proxy :: Proxy rl)
    in
      unsafeCoerce $ RecordFRep
        { names: metadata.names
        , instances: metadata.instances
        , values: unsafeCoerce values
        }

class ToAux :: RowList Type -> Type -> Row Type -> Constraint
class ToAux rl a r | rl a -> r

instance ToAux RowList.Nil a ()

else instance
  ( ToAux future argument farFuture
  , Row.Cons name (functor argument) farFuture farFutureWithElement
  ) =>
  ToAux (RowList.Cons name (Pair functor bifunctor) future) argument farFutureWithElement

-- | Converts a `RecordF` into a `Record`.
class To :: Row Type -> Type -> Row Type -> Constraint
class To r a r' | r a -> r' where
  to :: RecordF r a -> Record r'

instance (RowList.RowToList r rl, ToAux rl a r') => To r a r' where
  to recordF =
    let
      (RecordFRep r) = unsafeCoerce recordF
    in
      unsafeCoerce r.values
