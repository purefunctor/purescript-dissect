module Data.Functor.Polynomial.Generic where

import Prelude

import Data.Either (Either(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial as P
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep as G
import Data.List (List(..), (:))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect, right)
import Type.Proxy (Proxy(..))

class Polynomial ∷ ∀ k. k → Type → Type → Constraint
class Polynomial t f r | t f → r where
  polynomial ∷ Proxy t → f → r

instance Polynomial t (G.Constructor _name G.NoArguments) (P.One n) where
  polynomial _ _ = (P.Const unit)

else instance Polynomial t (G.Argument t) (P.Id t) where
  polynomial _ (G.Argument v) = P.Id v

else instance Polynomial t (G.Argument n) (P.Const n m) where
  polynomial _ (G.Argument v) = P.Const v

else instance (Polynomial t a (f v), Polynomial t b (g v)) ⇒ Polynomial t (G.Product a b) (P.Product f g v) where
  polynomial t (G.Product a b) = P.Product (polynomial t a) (polynomial t b)

else instance (Polynomial t a (f v), Polynomial t b (g v)) ⇒ Polynomial t (G.Sum a b) (P.Sum f g v) where
  polynomial t (G.Inl l) = P.SumL (polynomial t l)
  polynomial t (G.Inr r) = P.SumR (polynomial t r)

else instance (Polynomial t p r) ⇒ Polynomial t (G.Constructor _n p) r where
  polynomial t (G.Constructor g) = polynomial t g

fromGeneric ∷ ∀ t g p q. Dissect p q ⇒ Generic t g ⇒ Polynomial t g (p t) ⇒ t → Mu p
fromGeneric = ana co
  where
  co ∷ t → p t
  co = polynomial (Proxy ∷ Proxy t) <<< G.from

  -- Taken verbatim from the `ssrs` library.
  --
  -- This is cheaper than having to create a separate package for
  -- just for this use-case.
  ana ∷ ∀ v. Dissect p q ⇒ (v → p v) → v → Mu p
  ana coalgebra seed = go (right (Left (coalgebra seed))) Nil
    where
    go index stack =
      case index of
        Left (Tuple pt pd) →
          go (right (Left (coalgebra pt))) (pd : stack)
        Right pv →
          case stack of
            (pd : stk) →
              go (right (Right (Tuple pd (In pv)))) stk
            Nil →
              In pv
