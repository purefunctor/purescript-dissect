module Variant.Polynomial.Internal where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either)
import Data.Tuple (Tuple)
import Dissect.Class (class Dissect, right)
import Foreign.Object (Object, empty, insert)
import Prim.RowList (Cons, Nil, RowList)
import Type.Prelude (class IsSymbol, class ListToRow, class RowToList, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

newtype VariantFRep :: forall k. (k -> Type) -> k -> Type
newtype VariantFRep f a = VariantFRep
  { tag :: String
  , value :: f a
  }

newtype VariantFRep_2 :: forall k l. (k -> l -> Type) -> k -> l -> Type
newtype VariantFRep_2 f a b = VariantFRep_2
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

-- type PlugClass =
--   { plug :: forall p q x. x -> q x x -> p x
--   }

class FindInstances (rl :: RowList (Type -> Type)) where
  instances
    :: Proxy rl
    -> { functors :: Object FunctorClass
       , bifunctors :: Object BifunctorClass
       , dissects :: Object DissectClass
       -- , plugs :: Object PlugClass
       }

instance FindInstances Nil where
  instances _ =
    { functors: empty
    , bifunctors: empty
    , dissects: empty
    -- , plugs: empty
    }

else instance
  ( IsSymbol n
  , Functor f
  , Dissect f g
  , {- Plug f g, -} Bifunctor g
  , FindInstances rl
  ) =>
  FindInstances (Cons n f rl) where
  instances _ =
    let
      { functors, bifunctors, dissects } = instances (Proxy :: _ rl)
      n = reflectSymbol (Proxy :: _ n)
    in
      { functors:
          insert n { map: unsafeCoerce (map :: _ -> f _ -> f _) } functors
      , bifunctors:
          insert n { bimap: unsafeCoerce (bimap :: _ -> _ -> g _ _ -> g _ _) } bifunctors
      , dissects:
          insert n { right: unsafeCoerce (right :: _ (f _) (_ (g _ _) _) -> _) } dissects
      -- , plugs:
      --     insert n { plug: unsafeCoerce (plug :: _ -> g _ _ -> f _) } plugs
      }

class DissectRowI :: RowList (Type -> Type) -> RowList (Type -> Type -> Type) -> Constraint
class DissectRowI r s | r -> s

instance DissectRowI Nil Nil

else instance
  ( DissectRowI r s
  , Functor p
  , Bifunctor q
  , Dissect p q
  ) =>
  DissectRowI (Cons n p r) (Cons n q s)

class DissectRow :: Row (Type -> Type) -> Row (Type -> Type -> Type) -> Constraint
class DissectRow r s | r -> s

instance (RowToList r r', DissectRowI r' s', ListToRow s' s) => DissectRow r s
