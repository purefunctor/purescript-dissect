-- | Polynomial functors and bifunctors for algebraically defining data types
-- | with free `Dissect` instances as described in "Algebra of Programming" by
-- | Bird and de Moor; as well as the functional dissections paper.
module Dissect.Generic
  ( Const(..)
  , Const_2(..)
  , Id(..)
  , Product(..)
  , Product_2(..)
  , Sum(..)
  , Sum_2(..)
  , type (:*:)
  , type (:+:)
  , (:*:)
  ) where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Functor.Clown (Clown(..))
import Data.Functor.Joker (Joker(..))
import Data.Newtype (unwrap)
import Data.Variant (match)
import Dissect.Class (class Dissect, Result, init, next, return, yield)
import Partial.Unsafe (unsafeCrashWith)

-- | The constant functor, which maps all `b` to some constant `a`.
newtype Const :: forall k. Type -> k -> Type
newtype Const a b = Const a

derive instance Eq a => Eq (Const a b)
derive instance Ord a => Ord (Const a b)
derive instance Functor (Const a)

instance Show a => Show (Const a b) where
  show (Const a) = "(Const " <> show a <> ")"

-- | The identity functor, which maps all `a` back into `a`.
newtype Id a = Id a

derive instance Eq a => Eq (Id a)
derive instance Ord a => Ord (Id a)
derive instance Functor Id

instance Show a => Show (Id a) where
  show (Id a) = "(Id " <> show a <> ")"

-- | The sum of polynomial functors.
data Sum :: forall k. (k -> Type) -> (k -> Type) -> k -> Type
data Sum a b c = SumL (a c) | SumR (b c)

infixr 4 type Sum as :+:

instance (Eq (a c), Eq (b c)) => Eq (Sum a b c) where
  eq (SumL a) (SumL b) = eq a b
  eq (SumR a) (SumR b) = eq a b
  eq _ _ = false

instance (Ord (a c), Ord (b c)) => Ord (Sum a b c) where
  compare (SumL a) (SumL b) = compare a b
  compare (SumR a) (SumR b) = compare a b
  compare (SumL _) (SumR _) = LT
  compare (SumR _) (SumL _) = GT

derive instance (Functor a, Functor b) => Functor (Sum a b)

instance (Show (a c), Show (b c), Show c) => Show (Sum a b c) where
  show (SumL l) = "(SumL " <> show l <> ")"
  show (SumR r) = "(SumR " <> show r <> ")"

-- | The product of polynomial functors.
data Product :: forall k. (k -> Type) -> (k -> Type) -> k -> Type
data Product a b c = Product (a c) (b c)

infixr 5 type Product as :*:
infixr 5 Product as :*:

instance (Eq (a c), Eq (b c)) => Eq (Product a b c) where
  eq (Product a b) (Product c d) = eq a c && eq b d

instance (Ord (a c), Ord (b c)) => Ord (Product a b c) where
  compare (Product a b) (Product c d) = compare a c <> compare b d

instance (Show (a c), Show (b c), Show c) => Show (Product a b c) where
  show (Product a b) = "(Product " <> show a <> " " <> show b <> ")"

derive instance (Functor a, Functor b) => Functor (Product a b)

newtype Const_2 :: forall k l. Type -> k -> l -> Type
newtype Const_2 a b c = Const_2 a

instance Show a => Show (Const_2 a b c) where
  show (Const_2 a) = "(Const_2 " <> show a <> ")"

instance Bifunctor (Const_2 a) where
  bimap _ _ (Const_2 a) = (Const_2 a)

data Sum_2 :: forall k l. (k -> l -> Type) -> (k -> l -> Type) -> k -> l -> Type
data Sum_2 p q a b = SumL_2 (p a b) | SumR_2 (q a b)

instance (Show (p a b), Show (q a b)) => Show (Sum_2 p q a b) where
  show (SumL_2 l) = "(SumL " <> show l <> ")"
  show (SumR_2 r) = "(SumR " <> show r <> ")"

instance (Bifunctor p, Bifunctor q) => Bifunctor (Sum_2 p q) where
  bimap f g (SumL_2 p) = SumL_2 (bimap f g p)
  bimap f g (SumR_2 q) = SumR_2 (bimap f g q)

data Product_2 :: forall k l. (k -> l -> Type) -> (k -> l -> Type) -> k -> l -> Type
data Product_2 p q a b = Product_2 (p a b) (q a b)

instance (Show (p a b), Show (q a b)) => Show (Product_2 p q a b) where
  show (Product_2 a b) = "(Product_2 " <> show a <> " " <> show b <> ")"

instance (Bifunctor p, Bifunctor q) => Bifunctor (Product_2 p q) where
  bimap f g (Product_2 p q) = Product_2 (bimap f g p) (bimap f g q)

refute :: forall a. Void -> a
refute _ = unsafeCrashWith "Invalid dissection!"

instance Dissect (Const a) (Const_2 Void) where
  init (Const a) = return (Const a)
  next (Const_2 z) _ = refute z

instance Dissect Id (Const_2 Unit) where
  init (Id j) = yield j (Const_2 unit)
  next (Const_2 _) c = return (Id c)

instance
  ( Dissect p p'
  , Dissect q q'
  ) =>
  Dissect (Sum p q) (Sum_2 p' q') where
  init (SumL pj) = mindp (init pj)
  init (SumR qj) = mindq (init qj)
  next (SumL_2 pd) c = mindp (next pd c)
  next (SumR_2 qd) c = mindq (next qd c)

mindp
  :: forall p p' q q' c j
   . Dissect p p'
  => Dissect q q'
  => Result p p' c j
  -> Result (Sum p q) (Sum_2 p' q') c j
mindp = unwrap >>> match
  { yield: \{ j, qcj } -> yield j (SumL_2 qcj)
  , return: return <<< SumL
  }

mindq
  :: forall p p' q q' c j
   . Dissect p p'
  => Dissect q q'
  => Result q q' c j
  -> Result (Sum p q) (Sum_2 p' q') c j
mindq = unwrap >>> match
  { yield: \{ j, qcj } -> yield j (SumR_2 qcj)
  , return: return <<< SumR
  }

instance
  ( Dissect p p'
  , Dissect q q'
  ) =>
  Dissect (Product p q) (Sum_2 (Product_2 p' (Joker q)) (Product_2 (Clown p) q')) where
  init (Product pj qj) = mindp' (init pj) qj
  next (SumL_2 (Product_2 pd (Joker qj))) c = mindp' (next pd c) qj
  next (SumR_2 (Product_2 (Clown pc) qd)) c = mindq' pc (next qd c)

mindp'
  :: forall p p' q q' c j
   . Dissect p p'
  => Dissect q q'
  => Result p p' c j
  -> q j
  -> Result (Product p q) (Sum_2 (Product_2 p' (Joker q)) (Product_2 (Clown p) q')) c j
mindp' rs qj = unwrap rs # match
  { yield: \{ j, qcj } -> yield j (SumL_2 (Product_2 qcj (Joker qj)))
  , return: \pc -> mindq' pc (init qj)
  }

mindq'
  :: forall p p' q q' c j
   . Dissect p p'
  => Dissect q q'
  => p c
  -> Result q q' c j
  -> Result (Product p q) (Sum_2 (Product_2 p' (Joker q)) (Product_2 (Clown p) q')) c j
mindq' pc = unwrap >>> match
  { yield: \{ j, qcj } -> yield j (SumR_2 (Product_2 (Clown pc) qcj))
  , return: \qc -> return (Product pc qc)
  }
