module Data.Functor.Polynomial.Generic where

import Prelude

import Data.Functor.Polynomial as P
import Data.Functor.Polynomial.Extra as E
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep as G

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

else instance (Polynomial a (f v), Polynomial b (g v)) ⇒ Polynomial (G.Sum (G.Constructor n a) (G.Constructor m b)) (E.TSum n m f g v) where
  toPoly (G.Inl (G.Constructor l)) = E.TSumL (toPoly l)
  toPoly (G.Inr (G.Constructor r)) = E.TSumR (toPoly r)

  fromPoly (E.TSumL l) = G.Inl (G.Constructor (fromPoly l))
  fromPoly (E.TSumR r) = G.Inr (G.Constructor (fromPoly r))

else instance (Polynomial a (f v), Polynomial r (g v)) ⇒ Polynomial (G.Sum (G.Constructor n a) r) (E.TSum n "_" f g v) where
  toPoly (G.Inl (G.Constructor l)) = E.TSumL (toPoly l)
  toPoly (G.Inr r) = E.TSumR (toPoly r)

  fromPoly (E.TSumL l) = G.Inl (G.Constructor (fromPoly l))
  fromPoly (E.TSumR r) = G.Inr (fromPoly r)

newtype F f = F f

derive instance Generic (F f) _

fromGeneric ∷ ∀ t f r. Generic t f ⇒ Polynomial f r ⇒ t → r
fromGeneric = toPoly <<< G.from

toGeneric ∷ ∀ t f r. Generic t f ⇒ Polynomial f r ⇒ r → t
toGeneric = G.to <<< fromPoly
