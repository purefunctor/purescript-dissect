module Data.Functor.Polynomial.Extra where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect, right)

data TSum ∷ ∀ k. Symbol → Symbol → (k → Type) → (k → Type) → k → Type
data TSum n m a b c = TSumL (a c) | TSumR (b c)

derive instance (Functor a, Functor b) ⇒ Functor (TSum n m a b)

data TSum_2 ∷ ∀ k l. Symbol → Symbol → (k → l → Type) → (k → l → Type) → k → l → Type
data TSum_2 n m p q a b = TSumL_2 (p a b) | TSumR_2 (q a b)

derive instance (Functor (a c), Functor (b c)) ⇒ Functor (TSum_2 n m a b c)

instance (Bifunctor p, Bifunctor q) ⇒ Bifunctor (TSum_2 n m p q) where
  bimap f g (TSumL_2 p) = TSumL_2 (bimap f g p)
  bimap f g (TSumR_2 q) = TSumR_2 (bimap f g q)

instance (Dissect p p', Dissect q q') ⇒ Dissect (TSum n m p q) (TSum_2 n m p' q') where
  right v = case v of
    Left (TSumL pj) → mindp (right (Left pj))
    Left (TSumR qj) → mindq (right (Left qj))
    Right (Tuple (TSumL_2 pd) c) → mindp (right (Right (Tuple pd c)))
    Right (Tuple (TSumR_2 qd) c) → mindq (right (Right (Tuple qd c)))
    where
    mindp (Left (Tuple j pd)) = Left (Tuple j (TSumL_2 pd))
    mindp (Right pc) = Right (TSumL pc)

    mindq (Left (Tuple j qd)) = Left (Tuple j (TSumR_2 qd))
    mindq (Right qc) = Right (TSumR qc)
