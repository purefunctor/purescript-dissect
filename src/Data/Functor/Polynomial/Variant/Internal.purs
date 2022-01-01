module Data.Functor.Polynomial.Variant.Internal where

import Prelude

import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either)
import Data.Tuple (Tuple)
import Dissect.Class (class Dissect, class Plug, right, plug)
import Foreign.Object (Object, empty, insert)
import Prim.RowList (Cons, Nil, RowList)
import Type.Prelude (class IsSymbol, class ListToRow, class RowToList, Proxy(..), reflectSymbol)
import Unsafe.Coerce (unsafeCoerce)

newtype VariantFRep ∷ ∀ k. (k → Type) → k → Type
newtype VariantFRep f a = VariantFRep
  { tag ∷ String
  , value ∷ f a
  }

newtype VariantFRep_2 ∷ ∀ k l. (k → l → Type) → k → l → Type
newtype VariantFRep_2 f a b = VariantFRep_2
  { tag ∷ String
  , value ∷ f a b
  }

type FunctorClass =
  { map ∷ ∀ f a b. (a → b) → (f a → f b)
  }

type BifunctorClass =
  { bimap ∷ ∀ f a b x y. (a → b) → (x → y) → (f a x → f b y)
  }

type DissectClass =
  { right ∷ ∀ p q c j. Either (p j) (Tuple (q c j) c) → Either (Tuple j (q c j)) (p c)
  }

type PlugClass =
  { plug ∷ ∀ p q x. x → q x x → p x
  }

class SearchFunctorI (v ∷ RowList (Type → Type)) where
  functorsI ∷ Proxy v → Object FunctorClass

instance SearchFunctorI Nil where
  functorsI _ = empty

else instance (Functor f, IsSymbol n, SearchFunctorI r) ⇒ SearchFunctorI (Cons n f r) where
  functorsI _ = insert
    (reflectSymbol (Proxy ∷ _ n))
    { map: unsafeCoerce (map ∷ _ → f _ → f _) }
    (functorsI (Proxy ∷ _ r))

class SearchFunctor (v ∷ Row (Type → Type)) where
  functors ∷ Proxy v → Object FunctorClass

instance (RowToList r s, SearchFunctorI s) ⇒ SearchFunctor r where
  functors _ = functorsI (Proxy ∷ _ s)

class SearchBifunctorI (v ∷ RowList (Type → Type → Type)) where
  bifunctorsI ∷ Proxy v → Object BifunctorClass

instance SearchBifunctorI Nil where
  bifunctorsI _ = empty

else instance (Bifunctor f, IsSymbol n, SearchBifunctorI r) ⇒ SearchBifunctorI (Cons n f r) where
  bifunctorsI _ = insert
    (reflectSymbol (Proxy ∷ _ n))
    { bimap: unsafeCoerce (bimap ∷ _ → _ → f _ _ → f _ _) }
    (bifunctorsI (Proxy ∷ _ r))

class SearchBifunctor (v ∷ Row (Type → Type → Type)) where
  bifunctors ∷ Proxy v → Object BifunctorClass

instance (RowToList r s, SearchBifunctorI s) ⇒ SearchBifunctor r where
  bifunctors _ = bifunctorsI (Proxy ∷ _ s)

class SearchDissectI (v ∷ RowList (Type → Type)) where
  dissectsI ∷ Proxy v → Object DissectClass

instance SearchDissectI Nil where
  dissectsI _ = empty

else instance (Dissect p q, IsSymbol n, SearchDissectI r) ⇒ SearchDissectI (Cons n p r) where
  dissectsI _ = insert
    (reflectSymbol (Proxy ∷ _ n))
    { right: unsafeCoerce (right ∷ _ (p _) (_ (q _ _) _) → _) }
    (dissectsI (Proxy ∷ _ r))

class SearchDissect (v ∷ Row (Type → Type)) where
  dissects ∷ Proxy v → Object DissectClass

instance (RowToList r s, SearchDissectI s) ⇒ SearchDissect r where
  dissects _ = dissectsI (Proxy ∷ _ s)

class SearchPlugI (v ∷ RowList (Type → Type)) where
  plugsI ∷ Proxy v → Object PlugClass

instance SearchPlugI Nil where
  plugsI _ = empty

else instance (Plug p q, IsSymbol n, SearchPlugI r) ⇒ SearchPlugI (Cons n p r) where
  plugsI _ = insert
    (reflectSymbol (Proxy ∷ _ n))
    { plug: unsafeCoerce (plug ∷ _ → q _ _ → p _) }
    (plugsI (Proxy ∷ _ r))

class SearchPlug (v ∷ Row (Type → Type)) where
  plugs ∷ Proxy v → Object PlugClass

instance (RowToList r s, SearchPlugI s) ⇒ SearchPlug r where
  plugs _ = plugsI (Proxy ∷ _ s)

class DissectRowI ∷ RowList (Type → Type) → RowList (Type → Type → Type) → Constraint
class DissectRowI r s | r → s

instance DissectRowI Nil Nil

else instance (DissectRowI r s, Functor p, Bifunctor q, Dissect p q) ⇒ DissectRowI (Cons n p r) (Cons n q s)

class DissectRow ∷ Row (Type → Type) → Row (Type → Type → Type) → Constraint
class DissectRow r s | r → s

instance (RowToList r r', DissectRowI r' s', ListToRow s' s) ⇒ DissectRow r s
