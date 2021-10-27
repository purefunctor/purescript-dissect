module Test.Main where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect)
import Effect (Effect)
import Effect.Class.Console (log)

data TreeF n = Leaf
             | Fork n n n

data TreeF_2 n m = ForkRR m m
                 | ForkLR n m
                 | ForkLL n n

derive instance Functor TreeF

instance Bifunctor TreeF_2 where
  bimap f g = case _ of
    ForkRR m0 m1 -> ForkRR (g m0) (g m1)
    ForkLR n0 m1 -> ForkLR (f n0) (g m1)
    ForkLL n0 n1 -> ForkLL (f n0) (f n1)

instance Dissect TreeF TreeF_2 where
  right = case _ of
    Left Leaf → Right Leaf
    Left (Fork m n o) → Left (Tuple m (ForkRR n o))
    Right (Tuple w c) → case w of
      ForkRR m n → Left (Tuple m (ForkLR c n))
      ForkLR n m → Left (Tuple m (ForkLL n c))
      ForkLL n o → Right (Fork n o c)

main ∷ Effect Unit
main = do
  log "Finished."
