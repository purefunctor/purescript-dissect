module Test.Universe where

import Prelude hiding (one)

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM2)
import Control.Monad.ST (run)
import Control.Monad.ST.Internal as STRef
import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial (Const(..), Id(..), Product(..))
import Data.Functor.Polynomial.Variant (ClosedVariantF(..), VariantF, close, convert, inj, unsafeMatch, unsafeOnMatch)
import Data.Functor.Variant as Variant
import Data.List (List(..), (:))
import Data.Map as M
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple(..))
import Data.Variant as V
import Dissect.Class (class Dissect, right)
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Type.Prelude (Proxy(..))
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)

type Example :: (Row (Type -> Type) -> Type -> Type) -> Row (Type -> Type) -> Type
type Example f r = f (a :: Id | r) Unit

-- An open variant allows any `* -> *`-kinded type to be injected
-- whether or not it implements a `Functor` instance. This makes
-- deeper composition much, much easier than say, enforcing said
-- `Functor` instance instantly.
openVariantF :: forall r. Example VariantF r
openVariantF = inj (Proxy :: _ "a") (Id unit)

-- A closed variant is any open variant that has `Functor`, `Bifunctor`,
-- and `Dissect` instances. An unsafe routine is used internally to
-- capture the instance methods onto the closed variant.
closedVariantF :: Example ClosedVariantF ()
closedVariantF = close openVariantF

-- Any closed variant can be converted into a vanilla variant for
-- compatibility. If you're only interested in pattern matching,
-- a wrapper for `onMatch` is also provided.
vanillaVariantF :: Example Variant.VariantF ()
vanillaVariantF = convert closedVariantF

-- And can be then used for operations like onMatch with relative
-- ease.
onMatchExample :: Unit
onMatchExample = vanillaVariantF # Variant.onMatch
  { a: \(Id u) -> u
  }
  (\_ -> unsafeCrashWith "Pattern match failed!")

-- Alternatively, convenience wrappers are also provided:
unsafeOnMatchExample :: Unit
unsafeOnMatchExample = closedVariantF # unsafeOnMatch
  { a: \(Id u) -> u
  }
  (\_ -> unit)

--

newtype Recurse :: Symbol -> Type -> Type
newtype Recurse i a = Recurse a

instance Functor (Recurse i) where
  map f (Recurse x) = Recurse (f x)

recurse :: forall i a. Proxy i -> a -> Recurse i a
recurse _ = Recurse

data Recurse_2 :: forall k l. Symbol -> k -> l -> Type
data Recurse_2 i a b = Recurse_2

instance Bifunctor (Recurse_2 i) where
  bimap _ _ _ = Recurse_2

instance Dissect (Recurse i) (Recurse_2 i) where
  right = case _ of
    Left g -> Left (Tuple (unsafeCoerce g) Recurse_2)
    Right (Tuple _ c) -> Right (unsafeCoerce c)

unrecurseV :: forall i a t r. R.Cons i a t r => Recurse i (V.Variant r) -> a
unrecurseV variant = (unsafeCoerce variant).value

newtype Tagged :: Symbol -> Row (Type -> Type) -> Type
newtype Tagged t r = Tagged (Mu (ClosedVariantF r))

derive instance Newtype (Tagged t r) _

--

type ExprR :: Row (Type -> Type)
type ExprR =
  ( lit :: Const Int
  , var :: Const String
  , add :: Product (Recurse "ExprF") (Recurse "ExprF")
  , "let" :: Product (Recurse "BindF") (Recurse "ExprF")
  )

type ExprF :: Type -> Type
type ExprF = ClosedVariantF ExprR

type BindR :: Row (Type -> Type)
type BindR =
  ( bind :: Product (Const String) (Recurse "ExprF")
  )

type BindF :: Type -> Type
type BindF = ClosedVariantF BindR

type UnivR =
  ( expr :: ExprF
  , bind :: BindF
  )

type UnivF :: Symbol -> Type
type UnivF t = Tagged t UnivR

lit :: Int -> UnivF "ExprF"
lit a = coerce (closeExpr $ closeLit (Const a))

var :: String -> UnivF "ExprF"
var a = coerce (closeExpr $ closeVar (Const a))

add_ :: UnivF "ExprF" -> UnivF "ExprF" -> UnivF "ExprF"
add_ (Tagged (In a)) (Tagged (In b)) = coerce
  (closeExpr (closeAdd (Product (recurse Proxy a) (recurse Proxy b))))

let_ :: UnivF "BindF" -> UnivF "ExprF" -> UnivF "ExprF"
let_ (Tagged (In a)) (Tagged (In b)) = coerce
  (closeExpr (closeLet (Product (recurse Proxy a) (recurse Proxy b))))

bind_ :: String -> UnivF "ExprF" -> UnivF "BindF"
bind_ a (Tagged (In b)) = coerce (closeBind' $ closeBind (Product (Const a) (recurse Proxy b)))

closeExpr :: forall a. ExprF a -> UnivF "ExprF"
closeExpr a = coerce (close' (inj (Proxy :: _ "expr") a))
  where
  close' :: _ -> ClosedVariantF UnivR a
  close' = close

closeBind' :: forall a. BindF a -> UnivF "BindF"
closeBind' a = coerce (close' (inj (Proxy :: _ "bind") a))
  where
  close' :: _ -> ClosedVariantF UnivR a
  close' = close

closeLit :: forall a. Const Int a -> ExprF a
closeLit = close <<< inj (Proxy :: _ "lit")

closeVar :: forall a. Const String a -> ExprF a
closeVar = close <<< inj (Proxy :: _ "var")

closeAdd :: forall a. Product (Recurse "ExprF") (Recurse "ExprF") a -> ExprF a
closeAdd = close <<< inj (Proxy :: _ "add")

closeLet :: forall a. Product (Recurse "BindF") (Recurse "ExprF") a -> ExprF a
closeLet = close <<< inj (Proxy :: _ "let")

closeBind :: forall a. Product (Const String) (Recurse "ExprF") a -> BindF a
closeBind = close <<< inj (Proxy :: _ "bind")

program :: Mu (ClosedVariantF UnivR)
program = coerce $ let_ (bind_ "a" (lit 21)) (let_ (bind_ "b" (lit 21)) (add_ (var "a") (var "b")))

eval :: V.Variant ("ExprF" :: Maybe Int, "BindF" :: Unit)
eval = run do
  r <- STRef.new M.empty

  let
    go = unsafeMatch
      { expr: unsafeMatch
          { lit: \(Const i) ->
              pure $ rExprF $ Just i
          , var: \(Const v) -> do
              m <- STRef.read r
              pure $ rExprF $ join $ M.lookup v m
          , add: \(Product a b) ->
              pure $ rExprF $ add <$> unrecurseV a <*> unrecurseV b
          , "let": \(Product _ b) ->
              pure $ rExprF $ unrecurseV b
          }
      , bind: unsafeMatch
          { bind: \(Product (Const n) v) -> do
              _ <- STRef.modify (M.insert n (unrecurseV v)) r
              pure $ rBindF unit
          }
      }

  cataM right go program
  where
  rExprF = V.inj (Proxy :: _ "ExprF")
  rBindF = V.inj (Proxy :: _ "BindF")

--

type Algebra f a = f a -> a

type AlgebraM :: (Type -> Type) -> (Type -> Type) -> Type -> Type
type AlgebraM m f a = f a -> m a

type RightFnA :: (Type -> Type) -> (Type -> Type -> Type) -> Type -> Type
type RightFnA p q v =
  Either (p (Mu p)) (Tuple (q v (Mu p)) v) -> Either (Tuple (Mu p) (q v (Mu p))) (p v)

cata :: forall p q v. RightFnA p q v -> Algebra p v -> Mu p -> v
cata right algebra (In pt) = go (right (Left pt)) Nil
  where
  go :: Either (Tuple (Mu p) (q v (Mu p))) (p v) -> List (q v (Mu p)) -> v
  go index stack =
    case index of
      Left (Tuple (In pt') pd) -> do
        go (right (Left pt')) (pd : stack)
      Right pv ->
        case stack of
          (pd : stk) ->
            go (right (Right (Tuple pd (algebra pv)))) stk
          Nil ->
            algebra pv

cataM :: forall m p q v. MonadRec m => RightFnA p q v -> AlgebraM m p v -> Mu p -> m v
cataM right algebraM (In pt) = tailRecM2 go (right (Left pt)) Nil
  where
  go index stack =
    case index of
      Left (Tuple (In pt') pd) ->
        pure (Loop { a: right (Left pt'), b: (pd : stack) })
      Right pv ->
        case stack of
          (pd : stk) -> do
            pv' <- algebraM pv
            pure (Loop { a: right (Right (Tuple pd pv')), b: stk })
          Nil -> do
            Done <$> algebraM pv
