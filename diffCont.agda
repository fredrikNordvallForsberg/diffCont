module diffCont where

open import Data.Nat as Nat  hiding (_+_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Data.Product
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero; suc to lsuc)


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
record Fam {a} (D : Set a) : Set (a Level.⊔ lsuc lzero) where
  constructor fam
  field
    indexSet : DecEqSet
    el : carrier indexSet -> D

  index : Set
  index = carrier indexSet

  eq? : Decidable (_≡_ {A = index})
  eq? = decEq indexSet

open Fam

FamAp : ∀ {a} {D D' : Set a} → (D → D') → Fam D → Fam D'
indexSet (FamAp f X) = indexSet X
el (FamAp f X) = λ y → f (el X y)

ΣFam : ∀ {a} {I : DecEqSet}{D : Set a} → (carrier I → Fam D) -> Fam D
ΣFam {I = I} X = fam ΣIX λ { (i , x) → el (X i) x } where
  ΣIX : DecEqSet
  carrier ΣIX = Σ[ i ∈ carrier I ] index (X i)
  decEq ΣIX = ≡-dec (decEq I) λ {i} → eq? (X i)

infix 5 _▷_
record _-Container (n : FinSet) : Set1 where
  constructor _▷_
  field
    Shape    : Set
    Position : Shape → Fam (El n)
open _-Container

⟦_⟧ : ∀ {n} → n -Container → (El n → Set) → Set
⟦_⟧ {n} (S ▷ P) X = Σ[ s ∈ S ] ((i : index (P s)) → X (el (P s) i))

Hom : FinSet -> FinSet -> Set1
Hom n m = El m → n -Container

⟦_⟧Hom : ∀ {n m} → Hom n m → (El n → Set) → (El m → Set)
⟦ F ⟧Hom X j = ⟦ F j ⟧ X

⊤' : DecEqSet
carrier ⊤' = ⊤
decEq ⊤' x y = yes refl

ID : ∀ {n} → Hom n n
ID = λ j → ⊤ ▷ λ _ → fam ⊤' (λ _ → j)

COMP : ∀ {m k} → m -Container -> Hom k m → k -Container
COMP {m} {k} (S ▷ P) F = (Σ[ s ∈ S ] ((x : index (P s)) → Shape (F (el (P s) x)))) ▷ λ { (s , f) → ΣFam {I = indexSet (P s)} λ x → Position (F (el (P s) x)) (f x) }

_;_ : ∀ {n m k} → Hom n m → Hom m k → Hom n k
(F ; G) j = COMP (G j) F

postulate
  ext : Extensionality lzero (lsuc lzero)

eq-Cont : ∀ {n} → {F G : n -Container} → (p : Shape F ≡ Shape G) → subst (λ z → z -> Fam (El n)) p (Position F) ≡ Position G → F ≡ G
eq-Cont refl refl = refl

_;ID : ∀ {n m} → (F : Hom n m) → F ; ID ≡ F
F ;ID = ext λ j → eq-Cont {!!} {!!}

ID;_ : ∀ {n m} → (F : Hom n m) → ID ; F ≡ F
ID; F = ext λ j → eq-Cont {!!} {!!}

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

ZERO : ∀ {n m} → Hom n m
ZERO j = ⊥ ▷ λ ()

_\\_ : (X : Set) → (x : X) → Set
X \\ x = Σ[ y ∈ X ] (x ≡ y → ⊥)

DIFF : ∀ {n} → n -Container → (`2 `× n) -Container
Shape (DIFF (S ▷ P)) = Σ[ s ∈ S ] index (P s)
indexSet (Position (DIFF (S ▷ P)) (s , h)) = indexSet (P s)
el (Position (DIFF (S ▷ P)) (s , h)) p = isYes (eq? (P s) p h) , el (P s) p

D : ∀ {n m} → Hom n m → Hom (`2 `× n) m
D F j = DIFF (F j)
