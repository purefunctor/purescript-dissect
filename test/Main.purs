module Test.Main where

import Prelude

import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial (Const(..), Id(..), One, Product(..), Sum(..))
import Data.Functor.Polynomial.Generic (F(..), TSum, toGeneric, fromGeneric)
import Data.Generic.Rep (class Generic)
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

-- | Writing this is cumbersome!
type TreeP a = Sum (Const a) (Product Id Id)

algebra ∷ TreeP Int Int → Int
algebra (SumL (Const a)) = a
algebra (SumR (Product (Id a) (Id b))) = a + b

-- | Instead, create a "regular" data type and mark recursion with `F`;
data TreeF a n = Leaf a | Fork (F n) (F n)

-- | then, derive a `Generic` instance for your data type;
derive instance Generic (TreeF a n) _

-- | finally, rewrite your algebra to something more comfortable.
algebra' ∷ TreeF Int Int → Int
algebra' (Leaf a) = a
algebra' (Fork (F a) (F b)) = a + b

algebra'' ∷ TreePT Int Int → Int
algebra'' = algebra' <<< toGeneric

-- | Notice that instead of `Sum`, we get a `TSum`. This makes sure that
-- | no information is removed from the transformation from `Generic`
-- | i.e. there exists an isomorphism.
type TreePT a = TSum "Leaf" "Fork" (Const a) (Product Id Id)

-- | The same concept applies for coalgebras too.
coalgebra ∷ Int → TreeP Int Int
coalgebra 0 = SumL (Const 0)
coalgebra n = SumR (Product (Id (n - 1)) (Id (n - 1)))

coalgebra' ∷ Int → TreeF Int Int
coalgebra' 0 = Leaf 0
coalgebra' n = Fork (F (n - 1)) (F (n - 1))

coalgebra'' ∷ Int → TreePT Int Int
coalgebra'' = fromGeneric <<< coalgebra'

main ∷ Effect Unit
main = do
  log "Finished."
