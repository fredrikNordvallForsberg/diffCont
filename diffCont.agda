{-# OPTIONS --without-K #-}
module diffCont where

open import Data.Nat as Nat  hiding (_+_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Data.Sum
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero; suc to lsuc)

record _<->_ (A B : Set) : Set where
  field
    to : A → B
    from : B -> A
    from-to : (x : A) -> from (to x) ≡ x
    to-from : (x : B) -> to (from x) ≡ x
open _<->_

related-by : {A B : Set} -> A <-> B -> A -> B -> Set
related-by f a b = to f a ≡ b × from f b ≡ a

related-by-to : {A B : Set} -> (f : A <-> B)(a : A)(b : B) →
                to f a ≡ b -> related-by f a b
related-by-to f a ._ refl = refl , (from-to f a)

related-by-from : {A B : Set} -> (f : A <-> B)(a : A)(b : B) →
                  from f b ≡ a -> related-by f a b
related-by-from f ._ b refl = (to-from f b) , refl

-- A universe of finite sets
mutual

  data FinSet : Set where
    `0 `1 `2 : FinSet
    `Σ : (a : FinSet) -> (El a -> FinSet) -> FinSet

  El : FinSet -> Set
  El `0 = ⊥
  El `1 = ⊤
  El `2 = Bool
  El (`Σ a b) = Σ[ x ∈ El a ] (El (b x))

_`×_ : FinSet -> FinSet -> FinSet
a `× b = `Σ a (λ _ → b)

_`+_ : FinSet -> FinSet -> FinSet
a `+ b = `Σ `2 (λ { false → a ; true → b })

pattern inl x = (false , x)
pattern inr x = (true , x)

`Π : (a : FinSet) -> (El a -> FinSet) -> FinSet
`Π `0 b = `1
`Π `1 b = b _
`Π `2 b = b false `× b true
`Π (`Σ a b) c = `Π a λ x → `Π (b x) λ y → c (x , y)

-- sets with decidable equality
record DecEqSet : Set1 where
  field
    carrier : Set
    decEq : Decidable (_≡_ {A = carrier})
open DecEqSet

-- Families with index sets with decidable equality
record Fam (D : Set) : Set1 where
  constructor fam
  field
    indexSet : DecEqSet
    el : carrier indexSet -> D

  index : Set
  index = carrier indexSet

  eq? : Decidable (_≡_ {A = index})
  eq? = decEq indexSet

open Fam

FamAp : ∀ {D D' : Set} → (D → D') → Fam D → Fam D'
indexSet (FamAp f X) = indexSet X
el (FamAp f X) = λ y → f (el X y)

ΣFam : ∀ {I : DecEqSet}{D : Set} → (carrier I → Fam D) -> Fam D
ΣFam {I = I} X = fam ΣIX λ { (i , x) → el (X i) x } where
  ΣIX : DecEqSet
  carrier ΣIX = Σ[ i ∈ carrier I ] index (X i)
  decEq ΣIX = ≡-dec (decEq I) λ {i} → eq? (X i)

infix 5 _<|_
record _-Container (n : FinSet) : Set1 where
  constructor _<|_
  field
    Shape    : Set
    Position : Shape → Fam (El n)
open _-Container

⟦_⟧ : ∀ {n} → n -Container → (El n → Set) → Set
⟦_⟧ {n} (S <| P) X = Σ[ s ∈ S ] ((i : index (P s)) → X (el (P s) i))

Hom : FinSet -> FinSet -> Set1
Hom n m = El m → n -Container

⟦_⟧Hom : ∀ {n m} → Hom n m → (El n → Set) → (El m → Set)
⟦ F ⟧Hom X j = ⟦ F j ⟧ X

⊤' : DecEqSet
carrier ⊤' = ⊤
decEq ⊤' x y = yes refl

ID : ∀ {n} → Hom n n
ID = λ j → ⊤ <| λ _ → fam ⊤' (λ _ → j)

COMP : ∀ {m k} → m -Container -> Hom k m → k -Container
COMP {m} {k} (S <| P) F = (Σ[ s ∈ S ] ((x : index (P s)) → Shape (F (el (P s) x)))) <| λ { (s , f) → ΣFam {I = indexSet (P s)} λ x → Position (F (el (P s) x)) (f x) }

_;_ : ∀ {n m k} → Hom n m → Hom m k → Hom n k
(F ; G) j = COMP (G j) F

postulate
  ext : Extensionality lzero (lsuc lzero)

eq-Cont : ∀ {n} → {F G : n -Container} → (p : Shape F ≡ Shape G) → subst (λ z → z -> Fam (El n)) p (Position F) ≡ Position G → F ≡ G
eq-Cont refl refl = refl

record _≡Fam_ {X}(A B : Fam X) : Set where
  field
    indices : index A <-> index B
    elements : (i : index A)(i' : index B) ->
               related-by indices i i' ->
               el A i ≡ el B i'
open _≡Fam_

record _≡Cont_ {n} (A B : n -Container) : Set where
  field
    shapes : Shape A <-> Shape B
    positions : (s : Shape A)(s' : Shape B) ->
                related-by shapes s s' ->
                Position A s ≡Fam Position B s'
open _≡Cont_

_==_ : ∀ {n m} →  Hom n m -> Hom n m -> Set
F == G = ∀ j → F j ≡Cont G j

infix 4 _≡Cont_ _≡Fam_ _==_

_;ID : ∀ {n m} → (F : Hom n m) → F ; ID == F
to (shapes ((F ;ID) j)) (_ , x) = x _
from (shapes ((F ;ID) j)) y = (tt , λ _ → y)
from-to (shapes ((F ;ID) j)) x = refl
to-from (shapes ((F ;ID) j)) y = refl
to (indices (positions ((F ;ID) j) s ._ (refl , _))) (_ , x) = x
from (indices (positions ((F ;ID) j) s ._ (refl , _))) x = (tt , x)
from-to (indices (positions ((F ;ID) j) s ._ (refl , _))) x = refl
to-from (indices (positions ((F ;ID) j) s ._ (refl , _))) y = refl
elements (positions ((F ;ID) j) s ._ (refl , _)) i i' (refl , _) = refl

ID;_ : ∀ {n m} → (F : Hom n m) → ID ; F == F
to (shapes ((ID; F) j)) (x , _) = x
from (shapes ((ID; F) j)) x = (x , λ _ → tt)
from-to (shapes ((ID; F) j)) x = refl
to-from (shapes ((ID; F) j)) y = refl
to (indices (positions ((ID; F) j) s ._ (refl , _))) (x , _) = x
from (indices (positions ((ID; F) j) s ._ (refl , _))) y = y , tt
from-to (indices (positions ((ID; F) j) s ._ (refl , _))) x = refl
to-from (indices (positions ((ID; F) j) s ._ (refl , _))) y = refl
elements (positions ((ID; F) j) s ._ (refl , _)) i ._ (refl , _) = refl

-- Cartesian structure

fst : ∀ {n m} → Hom (n `+ m) n
Shape (fst j) = ⊤
Position (fst j) _ = fam ⊤' λ _ → inl j

snd : ∀ {n m} → Hom (n `+ m) m
Shape (snd j) = ⊤
Position (snd j) _ = fam ⊤' λ _ → inr j

TIMES : ∀ {n n' m m'} → (F : Hom n m)(G : Hom n' m') → Hom (n `+ n') (m `+ m')
Shape (TIMES F G (inl x)) = Shape (F x)
Shape (TIMES F G (inr x)) = Shape (G x)
Position (TIMES F G (inl x)) s = FamAp inl (Position (F x) s)
Position (TIMES F G (inr x)) s = FamAp inr (Position (G x) s)

-- Left additive structure

ZERO : ∀ {n m} → Hom n m
ZERO j = ⊥ <| λ ()

ADD : ∀ {n} → n -Container -> n -Container -> n -Container
ADD (S <| P) (S' <| P') = (S ⊎ S') <| λ { (inj₁ s)  → P s
                                         ; (inj₂ s') → P' s' }
PLUS : ∀ {n m} → Hom n m → Hom n m → Hom n m
PLUS F G j = ADD (F j) (G j)

H;F+G : ∀ {n m k} → (F G : Hom n m)(H : Hom k n) →
     H ; PLUS F G == PLUS (H ; F) (H ; G)
to (shapes (H;F+G F G H j)) (inj₁ s , s') = inj₁ (s , s')
to (shapes (H;F+G F G H j)) (inj₂ s , s') = inj₂ (s , s')
from (shapes (H;F+G F G H j)) (inj₁ (s , s')) = (inj₁ s , s')
from (shapes (H;F+G F G H j)) (inj₂ (s , s')) = (inj₂ s , s')
from-to (shapes (H;F+G F G H j)) (inj₁ s , s') = refl
from-to (shapes (H;F+G F G H j)) (inj₂ s , s') = refl
to-from (shapes (H;F+G F G H j)) (inj₁ (s , s')) = refl
to-from (shapes (H;F+G F G H j)) (inj₂ (s , s')) = refl
indices (positions (H;F+G F G H j) s s' x) = {!!}
elements (positions (H;F+G F G H j) s s' x) = {!!}

-- Derivatives

{-
_\\_ : (X : Set) → (x : X) → Set
X \\ x = Σ[ y ∈ X ] (x ≡ y → ⊥)
-}

DIFF : ∀ {n} → n -Container → (`2 `× n) -Container
Shape (DIFF (S <| P)) = Σ[ s ∈ S ] (index (P s))
indexSet (Position (DIFF (S <| P)) (s , h)) = indexSet (P s)
el (Position (DIFF (S <| P)) (s , h)) p = isYes (eq? (P s) p h) , el (P s) p

D : ∀ {n m} → Hom n m → Hom (`2 `× n) m
D F j = DIFF (F j)

ayes : Hom (`2 `× n) m -> Hom n m
ayes = ?

noes : Hom (`2 `× n) m -> Hom n m
noes = ?
