module Data.Functor.Polynomial where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either(..))
import Data.Functor.Clown (Clown(..))
import Data.Functor.Joker (Joker(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect, class Plug, plug, right)
import Partial.Unsafe (unsafeCrashWith)

newtype Const ∷ ∀ k. Type → k → Type
newtype Const a b = Const a

derive instance Functor (Const a)

newtype Id a = Id a

derive instance Functor Id

data Sum ∷ ∀ k. (k → Type) → (k → Type) → k → Type
data Sum a b c = SumL (a c) | SumR (b c)

derive instance (Functor a, Functor b) ⇒ Functor (Sum a b)

data Product ∷ ∀ k. (k → Type) → (k → Type) → k → Type
data Product a b c = Product (a c) (b c)

infixr 4 type Product as :*:
infixr 4 Product as :*:

derive instance (Functor a, Functor b) ⇒ Functor (Product a b)

type One ∷ ∀ k. k → Type
type One = Const Unit

type Zero ∷ ∀ k. k → Type
type Zero = Const Void

infixr 5 type Sum as :+:

newtype Const_2 ∷ ∀ k l. Type → k → l → Type
newtype Const_2 a b c = Const_2 a

instance Bifunctor (Const_2 a) where
  bimap _ _ (Const_2 a) = (Const_2 a)

data Sum_2 ∷ ∀ k l. (k → l → Type) → (k → l → Type) → k → l → Type
data Sum_2 p q a b = SumL_2 (p a b) | SumR_2 (q a b)

instance (Bifunctor p, Bifunctor q) ⇒ Bifunctor (Sum_2 p q) where
  bimap f g (SumL_2 p) = SumL_2 (bimap f g p)
  bimap f g (SumR_2 q) = SumR_2 (bimap f g q)

data Product_2 ∷ ∀ k l. (k → l → Type) → (k → l → Type) → k → l → Type
data Product_2 p q a b = Product_2 (p a b) (q a b)

instance (Bifunctor p, Bifunctor q) ⇒ Bifunctor (Product_2 p q) where
  bimap f g (Product_2 p q) = Product_2 (bimap f g p) (bimap f g q)

type Fst = Clown Id

type Snd = Joker Id

type One_2 ∷ ∀ k l. k → l → Type
type One_2 = Const_2 Unit

type Zero_2 ∷ ∀ k l. k → l → Type
type Zero_2 = Const_2 Void

refute ∷ ∀ a. Void → a
refute _ = unsafeCrashWith "Invalid dissection!"

instance Dissect (Const a) Zero_2 where
  right v = case v of
    Left (Const a) → Right (Const a)
    Right (Tuple (Const_2 z) _) → refute z

instance Dissect Id One_2 where
  right v = case v of
    Left (Id j) → Left (Tuple j (Const_2 unit))
    Right (Tuple (Const_2 _) c) → Right (Id c)

instance
  ( Dissect p p'
  , Dissect q q'
  ) ⇒
  Dissect (Sum p q) (Sum_2 p' q') where
  right v = case v of
    Left (SumL pj) → mindp (right (Left pj))
    Left (SumR qj) → mindq (right (Left qj))
    Right (Tuple (SumL_2 pd) c) → mindp (right (Right (Tuple pd c)))
    Right (Tuple (SumR_2 qd) c) → mindq (right (Right (Tuple qd c)))
    where
    mindp (Left (Tuple j pd)) = Left (Tuple j (SumL_2 pd))
    mindp (Right pc) = Right (SumL pc)

    mindq (Left (Tuple j qd)) = Left (Tuple j (SumR_2 qd))
    mindq (Right qc) = Right (SumR qc)

instance
  ( Dissect p p'
  , Dissect q q'
  ) ⇒
  Dissect (Product p q) (Sum_2 (Product_2 p' (Joker q)) (Product_2 (Clown p) q')) where
  right v = case v of
    Left (Product pj qj) → mindp (right (Left pj)) qj
    Right (Tuple (SumL_2 (Product_2 pd (Joker qj))) c) → mindp (right (Right (Tuple pd c))) qj
    Right (Tuple (SumR_2 (Product_2 (Clown pc) qd)) c) → mindq pc (right (Right (Tuple qd c)))
    where
    mindp (Left (Tuple j pd)) qj = Left (Tuple j (SumL_2 (Product_2 pd (Joker qj))))
    mindp (Right pc) qj = mindq pc (right (Left qj))

    mindq pc (Left (Tuple j qd)) = Left (Tuple j (SumR_2 (Product_2 (Clown pc) qd)))
    mindq pc (Right qc) = Right (Product pc qc)

instance Plug (Const n) Zero_2 where
  plug _ (Const_2 z) = refute z

instance Plug Id One_2 where
  plug x (Const_2 _) = Id x

instance (Plug p p', Plug q q') ⇒ Plug (Sum p q) (Sum_2 p' q') where
  plug x (SumL_2 pd) = SumL (plug x pd)
  plug x (SumR_2 qd) = SumR (plug x qd)

instance
  ( Plug p p'
  , Plug q q'
  ) ⇒
  Plug (Product p q) (Sum_2 (Product_2 p' (Joker q)) (Product_2 (Clown p) q')) where
  plug x (SumL_2 (Product_2 pd (Joker qx))) = Product (plug x pd) qx
  plug x (SumR_2 (Product_2 (Clown px) qd)) = Product px (plug x qd)
