module Test.Main where

import Prelude

import Data.Bifunctor (class Bifunctor)
import Dissect.Class (class Dissect, return, yield)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Test.Dissect as Dissect
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

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
    ForkRR m0 m1 -> ForkRR (g m0) (g m1)
    ForkLR n0 m1 -> ForkLR (f n0) (g m1)
    ForkLL n0 n1 -> ForkLL (f n0) (f n1)

instance Dissect TreeF TreeF_2 where
  init = case _ of
    Leaf -> return Leaf
    Fork m n o -> yield m (ForkRR n o)
  next w c = case w of
    ForkRR m n -> yield m (ForkLR c n)
    ForkLR n m -> yield m (ForkLL n c)
    ForkLL n o -> return (Fork n o c)

data List a n
  = Nil
  | Cons a n

instance Functor (List a) where
  map _ Nil = Nil
  map f (Cons a n) = Cons a (f n)

data List_2 :: Type -> Type -> Type -> Type
data List_2 a n m = Cons_2 a

instance Bifunctor (List_2 a) where
  bimap _ _ (Cons_2 a) = (Cons_2 a)

instance Dissect (List a) (List_2 a) where
  init = case _ of
    Nil -> return Nil
    Cons a n -> yield n (Cons_2 a)
  next (Cons_2 a) n = return (Cons a n)

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  Dissect.spec
