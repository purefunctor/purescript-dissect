-- | Provides the `Dissect` type class based on the "Clowns to the Left of me,
-- | Jokers to the Right (Pearl): Dissecting Data Structures" paper by Conor
-- | McBride.
module Dissect.Class where

import Prelude

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Bifunctor (class Bifunctor)
import Data.Newtype (class Newtype, unwrap)
import Data.Variant (Variant, inj, match)
import Type.Prelude (Proxy(..))

-- | The result of a dissection step over some data structure `p`, which can
-- | either be a `yield`, indicating that additional steps would have to be
-- | performed; or a `return`, indicating that the dissection has finished.
newtype Result :: (Type -> Type) -> (Type -> Type -> Type) -> Type -> Type -> Type
newtype Result p q c j = Result
  ( Variant
      ( yield ::
          { j :: j
          , qcj :: q c j
          }
      , return :: p c
      )
  )

yield :: forall p q c j. j -> (q c j) -> Result p q c j
yield j qcj = Result $ inj (Proxy :: Proxy "yield") { j, qcj }

return :: forall p q c j. p c -> Result p q c j
return pc = Result $ inj (Proxy :: Proxy "return") pc

derive instance Newtype (Result p q c j) _

instance (Show j, Show (q c j), Show (p c)) => Show (Result p q c j) where
  show = unwrap >>> match
    { yield: \{ j, qcj } -> "(Yield " <> show j <> " " <> show qcj <> ")"
    , return: \pc -> "(Return " <> show pc <> ")"
    }

-- | The type class for dissectible data structures, which generalizes the
-- | traversal of some `Functor p` given an intermediary `Bifunctor q`.
class (Functor p, Bifunctor q) <= Dissect p q | p -> q where
  -- | Initializes a dissection given the base structure `p j`.
  init :: forall c j. p j -> Result p q c j

  -- | Advances a dissection by filling in the intermediary structure `q c j`
  -- | with some value `c`.
  next :: forall c j. q c j -> c -> Result p q c j

-- | A tail-recursive `map` operation, implemented in terms of `Dissect`.
map :: forall p q a b. Dissect p q => (a -> b) -> p a -> p b
map f = continue <<< init
  where
  continue = unwrap >>> match
    { yield: \{ j, qcj } -> continue (next qcj (f j))
    , return: \pc -> pc
    }

-- | A tail-recursive `traverse` operation, implemented in terms of `Dissect`.
-- |
-- | Derived from: https://blog.functorial.com/posts/2017-06-18-Stack-Safe-Traversals-via-Dissection.html
traverse :: forall m p q a b. Dissect p q => MonadRec m => (a -> m b) -> p a -> m (p b)
traverse f = tailRecM continue <<< init
  where
  continue = unwrap >>> match
    { yield: \{ j, qcj } -> Loop <<< next qcj <$> f j
    , return: pure <<< Done
    }

-- | A tail-recursive `sequence` operation, implemented in terms of `Dissect`.
sequence :: forall m p q a. Dissect p q => MonadRec m => p (m a) -> m (p a)
sequence = traverse identity
