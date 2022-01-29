module Dissect.Runtime.Instances where

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Functor (class Functor, map)
import Dissect.Class (class Dissect, Input, Output, right)
import Foreign.Object (Object)
import Foreign.Object as Object
import Prim.Row as R
import Prim.RowList as RL
import Type.Prelude (class IsSymbol, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

type FunctorClass =
  { map :: forall f a b. (a -> b) -> (f a -> f b)
  }

type BifunctorClass =
  { bimap :: forall f a b x y. (a -> b) -> (x -> y) -> (f a x -> f b y)
  }

type DissectClass =
  { right :: forall p q c j. Input p q c j -> Output p q c j
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

class FindInstances (rl :: RL.RowList (Type -> Type)) where
  instancesAux :: Instances -> Proxy rl -> Instances

instance FindInstances RL.Nil where
  instancesAux accumulator _ = accumulator

else instance
  ( IsSymbol n
  , Functor f
  , Dissect f g
  , Bifunctor g
  , FindInstances rl
  ) =>
  FindInstances (RL.Cons n f rl) where
  instancesAux { functors, bifunctors, dissects } _ =
    let
      n = reflectSymbol (Proxy :: _ n)

      accumulator =
        { functors:
            Object.insert n { map: unsafeCoerce (map :: _ -> f _ -> f _) } functors
        , bifunctors:
            Object.insert n { bimap: unsafeCoerce (bimap :: _ -> _ -> g _ _ -> g _ _) } bifunctors
        , dissects:
            Object.insert n { right: unsafeCoerce (right :: Input f g _ _ -> Output f g _ _) }
              dissects
        }
    in
      instancesAux accumulator (Proxy :: _ rl)

instances
  :: forall rl
   . FindInstances rl
  => Proxy rl
  -> Instances
instances = instancesAux emptyInstances

class DissectRowI :: RL.RowList (Type -> Type) -> Row (Type -> Type -> Type) -> Constraint
class DissectRowI r s | r -> s

instance DissectRowI RL.Nil ()

else instance
  ( DissectRowI current future
  , Functor functor
  , Bifunctor bifunctor
  , Dissect functor bifunctor
  , R.Cons label bifunctor future futureWithElement
  ) =>
  DissectRowI (RL.Cons label functor current) futureWithElement

class DissectRow :: Row (Type -> Type) -> Row (Type -> Type -> Type) -> Constraint
class DissectRow r s | r -> s

instance (RL.RowToList r r', DissectRowI r' s) => DissectRow r s
