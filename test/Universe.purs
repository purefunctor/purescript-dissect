module Test.Universe where

import Prelude hiding (one)

import Data.Bifunctor (class Bifunctor)
import Data.Either (Either(..))
import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial (Const(..), Product(..), (:*:))
import Data.Functor.Polynomial.Variant (VariantF, case_, inj, on)
import Data.List (List(..), (:))
import Data.Tuple (Tuple(..))
import Dissect.Class (class Dissect, class Plug, right)
import Type.Prelude (Proxy(..))
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)

-- Stolen from purescript-ssrs
cata ∷ ∀ p q v. Dissect p q ⇒ (p v → v) → Mu p → v
cata algebra (In pt) = go (right (Left pt)) Nil
  where
  go index stack =
    case index of
      Left (Tuple (In pt') pd) →
        go (right (Left pt')) (pd : stack)
      Right pv →
        case stack of
          (pd : stk) →
            go (right (Right (Tuple pd (algebra pv)))) stk
          Nil →
            algebra pv

-- Similar to `Id`, but indexed with a symbol.
data Guarded ∷ ∀ k. Symbol → k → Type
data Guarded i a

instance Functor (Guarded i) where
  map f x = unsafeCoerce (f (unsafeCoerce x))

data Guarded_2 ∷ ∀ k l. Symbol → k → l → Type
data Guarded_2 i a b = Guarded_2

instance Bifunctor (Guarded_2 i) where
  bimap _ _ _ = Guarded_2

instance Dissect (Guarded i) (Guarded_2 i) where
  right = case _ of
    Left g → Left (Tuple (unsafeCoerce g) Guarded_2)
    Right (Tuple _ c) → Right (unsafeCoerce c)

instance Plug (Guarded i) (Guarded_2 i) where
  plug x _ = unsafeCoerce x

-- A weaker variant, works in conjunction with Guarded.
data Select ∷ ∀ k. Row k → Type
data Select r

toS ∷ ∀ i a t r. R.Cons i a t r ⇒ Proxy i → a → (Select r)
toS _ = unsafeCoerce

unS ∷ ∀ i a t r. R.Cons i a t r ⇒ Guarded i (Select r) → a
unS = unsafeCoerce

untoS ∷ ∀ i a t r. R.Cons i a t r ⇒ Guarded i (Select r) → Select r
untoS = unsafeCoerce

-- 1st Type - one point of recursion
--
-- data Base = One | Many (List Base)
type BaseF ∷ ∀ k. k → Type
type BaseF = VariantF
  ( one ∷ Const Unit
  , many ∷ Guarded "list"
  )

-- 2nd Type - two points of recursion
--
-- data List = Nil | Cons Base List
type ListF ∷ ∀ k. k → Type
type ListF = VariantF
  ( nil ∷ Const Unit
  , cons ∷ Product (Guarded "base") (Guarded "list")
  )

-- universe type
--
-- This holds all mutually recursive types together. Since `VariantF`
-- can be extended, it's possible to parameterize this to add more
-- constructors to each type or add more types to the universe.
--
-- Unfortunately, because of how `inj` works, it's impossible to infer
-- open rows. Right now, the only workaround possible is to make
-- constructors for a specific universe as described below.
type UnivF ∷ ∀ k. k → Type
type UnivF = VariantF
  ( base ∷ BaseF
  , list ∷ ListF
  )

type Univ = Mu UnivF

-- extensible constructors
--
-- These don't rely on a universe in any way, since they simply
-- construct types that may occupy it. Think of these as the building
-- blocks for an extensible universe.

one_ ∷ ∀ n. BaseF n
one_ = inj _one (Const unit)

many_ ∷ ∀ n. Guarded "list" n → BaseF n
many_ n = inj _many n

nil_ ∷ ∀ n. ListF n
nil_ = inj _nil (Const unit)

cons_ ∷ ∀ n. Guarded "base" n → Guarded "list" n → ListF n
cons_ n m = inj _cons (Product n m)

-- universe constructors
--
-- These "lift" the extensible constructors into a pre-defined universe
-- of types.

one ∷ Guarded "base" Univ
one = unsafeCoerce $ In (inj _base one_)

many ∷ Guarded "list" Univ → Guarded "base" Univ
many n = unsafeCoerce $ In (inj _base (many_ n))

nil ∷ Guarded "list" Univ
nil = unsafeCoerce $ In (inj _list nil_)

cons ∷ Guarded "base" Univ → Guarded "list" Univ → Guarded "list" Univ
cons n m = unsafeCoerce $ In (inj _list (cons_ n m))

-- Construction
xs ∷ Guarded "base" Univ
xs = many (cons one (cons one (cons one nil)))

-- Deconstruction
ys ∷ Select (base ∷ Int, list ∷ Int)
ys = cata go (unsafeCoerce xs ∷ Mu UnivF)
  where
  go = case_
    # on _base goBase
    # on _list goList
    where
    goBase = case_
      # on _one (\_ → toS _base 0)
      # on _many (\n → untoS n)

    goList = case_
      # on _nil (\_ → toS _list 0)
      # on _cons (\(_ :*: r) → toS _list (1 + unS r))

-- Proxy Types
_base ∷ Proxy "base"
_base = Proxy

_list ∷ Proxy "list"
_list = Proxy

_one ∷ Proxy "one"
_one = Proxy

_many ∷ Proxy "many"
_many = Proxy

_nil ∷ Proxy "nil"
_nil = Proxy

_cons ∷ Proxy "cons"
_cons = Proxy
