module Test.Universe where

import Prelude hiding (one)

import Data.Bifunctor (class Bifunctor)
import Data.Functor.Mu (Mu(..))
import Data.Functor.Polynomial (Const(..), Product(..), (:*:))
import Data.Functor.Polynomial.Variant (VariantF, inj)
import Data.Functor.Polynomial.Variant as V
import Data.List (List(..), (:))
import Dissect.Class (class Dissect, class Plug, Garden(..), CoGarden(..), right)
import Type.Prelude (Proxy(..), class IsSymbol, reflectSymbol)
import Type.Row as R
import Unsafe.Coerce (unsafeCoerce)
import Partial.Unsafe (unsafeCrashWith)

-- Stolen from purescript-ssrs
cata ∷ ∀ p q v. Dissect p q ⇒ (p v → v) → Mu p → v
cata algebra (In pt) = go (right (Pluck pt)) Nil
  where
  go index stack =
    case index of
      CoPlant (In pt') pd →
        go (right (Pluck pt')) (pd : stack)
      CoPluck pv →
        case stack of
          (pd : stk) →
            go (right (Plant (algebra pv) pd)) stk
          Nil →
            algebra pv

ana ∷ ∀ p q v. Dissect p q ⇒ (v → p v) → v → Mu p
ana coalgebra seed = go (right (Pluck (coalgebra seed))) Nil
  where
  go index stack =
    case index of
      CoPlant pt pd →
        go (right (Pluck (coalgebra pt))) (pd : stack)
      CoPluck pv →
        case stack of
          (pd : stk) →
            go (right (Plant (In pv) pd)) stk
          Nil →
            In pv

hylo ∷ ∀ p q v w. Dissect p q ⇒ (p v → v) → (w → p w) → w → v
hylo algebra coalgebra seed = go (right (Pluck (coalgebra seed))) Nil
  where
  go index stack =
    case index of
      CoPlant pt pd →
        go (right (Pluck (coalgebra pt))) (pd : stack)
      CoPluck pv →
        case stack of
          (pd : stk) →
            go (right (Plant (algebra pv) pd)) stk
          Nil →
            algebra pv

-- Similar to `Id`, but indexed with a symbol.
data Guarded ∷ ∀ k. Symbol → k → Type
data Guarded i a

instance Functor (Guarded i) where
  map f x = unsafeCoerce (f (unsafeCoerce x))

guard ∷ ∀ i a n. Proxy i → a → Guarded i n
guard _ = unsafeCoerce

data Guarded_2 ∷ ∀ k l. Symbol → k → l → Type
data Guarded_2 i a b = Guarded_2

instance Bifunctor (Guarded_2 i) where
  bimap _ _ _ = Guarded_2

instance Dissect (Guarded i) (Guarded_2 i) where
  right = case _ of
    Pluck g → CoPlant (unsafeCoerce g) Guarded_2
    Plant c _ -> CoPluck (unsafeCoerce c)

instance Plug (Guarded i) (Guarded_2 i) where
  plug x _ = unsafeCoerce x

-- A weaker variant, works in conjunction with Guarded.
data Select ∷ ∀ k. Row k → Type
data Select r

case_ ∷ ∀ a. Select () → a
case_ v = unsafeCrashWith case unsafeCoerce v of
  w → "Test.Universe: pattern match failed in tag [" <> w.tag <> "]."

on
  ∷ ∀ n r s a b
  . R.Cons n a s r
  ⇒ IsSymbol n
  ⇒ Proxy n
  → (a → b)
  → (Select s → b)
  → Select r
  → b
on p f g v =
  let
    w = unsafeCoerce v
  in
    if w.tag == reflectSymbol p then f w.value
    else g (unsafeCoerce v)

toS ∷ ∀ i a t r. R.Cons i a t r ⇒ IsSymbol i ⇒ Proxy i → a → (Select r)
toS p value = unsafeCoerce { tag: reflectSymbol p, value }

unS ∷ ∀ i a t r. R.Cons i a t r ⇒ Guarded i (Select r) → a
unS v = (unsafeCoerce v).value

toG ∷ ∀ i a t r. R.Cons i a t r ⇒ IsSymbol i ⇒ Proxy i → a → Guarded i (Select r)
toG p value = unsafeCoerce (toS p value ∷ Select r)

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

many_ ∷ ∀ a n. a → BaseF n
many_ n = inj _many (guard _list n)

nil_ ∷ ∀ n. ListF n
nil_ = inj _nil (Const unit)

cons_ ∷ ∀ a b n. a → b → ListF n
cons_ n m = inj _cons (Product (guard _base n) (guard _list m))

-- universe constructors
--
-- These "lift" the extensible constructors into a pre-defined universe
-- of types. However, this adds the cost of the constructors being fully
-- dynamic. One solution for API authors is to make use of `Guarded` in
-- order to add type labels that can be matched against.

one ∷ Univ
one = In (inj _base one_)

many ∷ Univ → Univ
many n = In (inj _base (many_ n))

nil ∷ Univ
nil = In (inj _list nil_)

cons ∷ Univ → Univ → Univ
cons n m = unsafeCoerce $ In (inj _list (cons_ n m))

xs ∷ Univ
xs = many (cons one (cons one (cons one nil)))

-- Recursion Schemes

al ∷ Univ → Select (base ∷ Int, list ∷ Int)
al = cata go
  where
  go = V.case_
    # V.on _base goBase
    # V.on _list goList
    where
    goBase = V.case_
      # V.on _one (\_ → toS _base 0)
      # V.on _many (\n → toS _base (unS n))

    goList = V.case_
      # V.on _nil (\_ → toS _list 0)
      # V.on _cons (\(_ :*: r) → toS _list (1 + unS r))

co ∷ Select (base ∷ Int, list ∷ Int) → Univ
co = ana go
  where
  go = case_
    # on _base
        ( case _ of
            0 → injBase one_
            n → injBase (many_ (toG _list n))
        )
    # on _list
        ( case _ of
            0 → injList nil_
            n → injList (cons_ (toG _base 0) (toG _list (n - 1)))
        )
    where
    injBase = inj _base
    injList = inj _list

hy ∷ Select (base ∷ Int, list ∷ Int) → Select (base ∷ Int, list ∷ Int)
hy = hylo goAl goCo
  where
  goAl = V.case_
    # V.on _base goBase
    # V.on _list goList
    where
    goBase = V.case_
      # V.on _one (\_ → toS _base 0)
      # V.on _many (\n → toS _base (unS n))

    goList = V.case_
      # V.on _nil (\_ → toS _list 0)
      # V.on _cons (\(_ :*: r) → toS _list (1 + unS r))

  goCo = case_
    # on _base
        ( case _ of
            0 → injBase one_
            n → injBase (many_ (toG _list n))
        )
    # on _list
        ( case _ of
            0 → injList nil_
            n → injList (cons_ (toG _base 0) (toG _list (n - 1)))
        )
    where
    injBase = inj _base
    injList = inj _list

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
