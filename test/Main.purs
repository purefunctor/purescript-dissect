module Test.Main where

import Prelude

import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial (Const(..), Id(..), One, Product(..), Sum(..))
import Effect (Effect)
import Effect.Class.Console (log)

type List a = Mu (Sum (Product (Const a) Id) One)

nil ∷ ∀ a. List a
nil = In (SumR (Const unit))

cons ∷ ∀ a. a → List a → List a
cons a xs = In (SumL (Product (Const a) (Id xs)))

type Tree a = Mu (Sum (Product Id Id) (Const a))

leaf ∷ ∀ a. a → Tree a
leaf a = In (SumR (Const a))

branch ∷ ∀ a. Tree a → Tree a → Tree a
branch l r = In (SumL (Product (Id l) (Id r)))

main ∷ Effect Unit
main = do
  log "Finished."
