module Variant.Polynomial.Internal where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either)
import Data.Tuple (Tuple)
import Dissect.Class (class Dissect, right)
import Foreign.Object (Object, insert)
import Foreign.Object as Object
import Prim.Row as R
import Prim.RowList (Cons, Nil, RowList)
import Type.Prelude (class IsSymbol, class RowToList, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

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

type FunctorClass =
  { map :: forall f a b. (a -> b) -> (f a -> f b)
  }

type BifunctorClass =
  { bimap :: forall f a b x y. (a -> b) -> (x -> y) -> (f a x -> f b y)
  }

type DissectClass =
  { right :: forall p q c j. Either (p j) (Tuple (q c j) c) -> Either (Tuple j (q c j)) (p c)
  }

type Instances =
  { functors :: Object FunctorClass
  , bifunctors :: Object BifunctorClass
  , dissects :: Object DissectClass
  }

emptyInstances :: Instances
emptyInstances =
  { functors: Object.empty
  , bifunctors: Object.empty
  , dissects: Object.empty
  }

class FindInstances (rl :: RowList (Type -> Type)) where
  instancesAux :: Instances -> Proxy rl -> Instances

instance FindInstances Nil where
  instancesAux accumulator _ = accumulator

else instance
  ( IsSymbol n
  , Functor f
  , Dissect f g
  , Bifunctor g
  , FindInstances rl
  ) =>
  FindInstances (Cons n f rl) where
  instancesAux { functors, bifunctors, dissects } _ =
    let
      n = reflectSymbol (Proxy :: _ n)

      accumulator =
        { functors:
            insert n { map: unsafeCoerce (map :: _ -> f _ -> f _) } functors
        , bifunctors:
            insert n { bimap: unsafeCoerce (bimap :: _ -> _ -> g _ _ -> g _ _) } bifunctors
        , dissects:
            insert n { right: unsafeCoerce (right :: _ (f _) (_ (g _ _) _) -> _) } dissects
        }
    in
      instancesAux accumulator (Proxy :: _ rl)

instances
  :: forall rl
   . FindInstances rl
  => Proxy rl
  -> Instances
instances = instancesAux emptyInstances

class DissectRowI :: RowList (Type -> Type) -> Row (Type -> Type -> Type) -> Constraint
class DissectRowI r s | r -> s

instance DissectRowI Nil ()

else instance
  ( DissectRowI current future
  , Functor functor
  , Bifunctor bifunctor
  , Dissect functor bifunctor
  , R.Cons label bifunctor future futureWithElement
  ) =>
  DissectRowI (Cons label functor current) futureWithElement

class DissectRow :: Row (Type -> Type) -> Row (Type -> Type -> Type) -> Constraint
class DissectRow r s | r -> s

instance (RowToList r r', DissectRowI r' s) => DissectRow r s
