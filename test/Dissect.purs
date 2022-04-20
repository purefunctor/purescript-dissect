module Test.Dissect where

import Prelude

import Dissect.Class as Dissect
import Dissect.Generic (Const(..), Id(..), Product(..), Sum(..))
import Dissect.Record (from, to)
import Dissect.Variant (injF, match)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  describe "Dissect.Record" do
    it "should convert empty records" do
      to (from {}) `shouldEqual` {}
    it "should work on the map operation" do
      let
        r =
          { a: Id 0
          , b: Const 0
          , c: Product (Id 0) (Const 0)
          , d: SumL (Id 0) :: Sum Id Id Int
          , e: SumR (Id 0) :: Sum Id Id Int
          }
        s =
          { a: Id 1
          , b: Const 0
          , c: Product (Id 1) (Const 0)
          , d: SumL (Id 1) :: Sum Id Id Int
          , e: SumR (Id 1) :: Sum Id Id Int
          }
      to (Dissect.map (_ + 1) (from r)) `shouldEqual` s
  describe "Dissect.Variant" do
    it "should construct then destruct" do
      let
        r = injF (Proxy :: _ "a") (Id 0) # match
          { a: \(Id a) -> a
          }
      r `shouldEqual` 0
    it "should work on the map operation" do
      let
        r = injF (Proxy :: _ "a") (Id 0) # Dissect.map (_ + 1) >>> match
          { a: \(Id a) -> a
          }
      r `shouldEqual` 1
