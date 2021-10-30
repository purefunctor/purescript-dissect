module Test.Main where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Dissect.Class (class Dissect, Garden(..), CoGarden(..))
import Effect (Effect)
import Effect.Class.Console (log)

data TreeF n
  = Leaf
  | Fork n n n

data TreeF_2 n m
  = ForkRR m m
  | ForkLR n m
  | ForkLL n n

derive instance Functor TreeF

instance Bifunctor TreeF_2 where
  bimap f g = case _ of
    ForkRR m0 m1 → ForkRR (g m0) (g m1)
    ForkLR n0 m1 → ForkLR (f n0) (g m1)
    ForkLL n0 n1 → ForkLL (f n0) (f n1)

instance Dissect TreeF TreeF_2 where
  right = case _ of
    Pluck Leaf → CoPluck Leaf
    Pluck (Fork m n o) → CoPlant m (ForkRR n o)
    Plant c w → case w of
      ForkRR m0 m1 → CoPlant m0 (ForkLR c m1)
      ForkLR n0 m1 → CoPlant m1 (ForkLL c n0)
      ForkLL n0 n1 → CoPluck (Fork n0 n1 c)

main ∷ Effect Unit
main = do
  log "Finished."
