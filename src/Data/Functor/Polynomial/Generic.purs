module Data.Functor.Polynomial.Generic where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either(..))
import Data.Functor.Polynomial as P
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep as G
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect, right)

class Polynomial ∷ Type → Type → Constraint
class Polynomial f p | f → p, p → f where
  toPoly ∷ f → p
  fromPoly ∷ p → f

instance Polynomial G.NoArguments (P.One n) where
  toPoly _ = P.Const unit
  fromPoly _ = G.NoArguments

else instance Polynomial (G.Argument (F n)) (P.Id n) where
  toPoly (G.Argument (F t)) = P.Id t
  fromPoly (P.Id t) = (G.Argument (F t))

else instance Polynomial (G.Argument n) (P.Const n m) where
  toPoly (G.Argument v) = P.Const v
  fromPoly (P.Const v) = G.Argument v

else instance (Polynomial a (f v), Polynomial b (g v)) ⇒ Polynomial (G.Product a b) (P.Product f g v) where
  toPoly (G.Product a b) = P.Product (toPoly a) (toPoly b)
  fromPoly (P.Product a b) = G.Product (fromPoly a) (fromPoly b)

else instance (Polynomial a (f v), Polynomial b (g v)) ⇒ Polynomial (G.Sum (G.Constructor n a) (G.Constructor m b)) (TSum n m f g v) where
  toPoly (G.Inl (G.Constructor l)) = TSumL (toPoly l)
  toPoly (G.Inr (G.Constructor r)) = TSumR (toPoly r)

  fromPoly (TSumL l) = G.Inl (G.Constructor (fromPoly l))
  fromPoly (TSumR r) = G.Inr (G.Constructor (fromPoly r))

else instance (Polynomial a (f v), Polynomial r (g v)) ⇒ Polynomial (G.Sum (G.Constructor n a) r) (TSum n "_" f g v) where
  toPoly (G.Inl (G.Constructor l)) = TSumL (toPoly l)
  toPoly (G.Inr r) = TSumR (toPoly r)

  fromPoly (TSumL l) = G.Inl (G.Constructor (fromPoly l))
  fromPoly (TSumR r) = G.Inr (fromPoly r)

newtype F f = F f

derive instance Generic (F f) _

fromGeneric ∷ ∀ t f r. Generic t f ⇒ Polynomial f r ⇒ t → r
fromGeneric = toPoly <<< G.from

toGeneric ∷ ∀ t f r. Generic t f ⇒ Polynomial f r ⇒ r → t
toGeneric = G.to <<< fromPoly

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
