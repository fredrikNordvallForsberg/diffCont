module cockett where

open import Data.Product
open import Data.Product.Properties as Σ
open import Data.Sum
open import Data.Sum.Properties as ⊎
open import Data.Empty
open import Data.Unit
open import Data.Unit.Properties  as ⊤
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero; suc to lsuc)


postulate
  funext : Extensionality lzero lzero

dec→≠ : {A : Set} → (f g : A → ⊥) → Dec (f ≡ g)
dec→≠ {A} f g = yes (funext λ x → ⊥-elim (f x))

record IC (X Y : Set) : Set1 where
  constructor mkIC
  field
    Sh : Y -> Set
    Pos : (y : Y) → Sh y → Set
    dec : (y : Y) → (s : Sh y) → (p q : Pos y s) → Dec (p ≡ q)
    next : (y : Y) → (s : Sh y) → Pos y s → X

record IC' (X : Set) : Set1 where
  constructor mkIC
  field
    Sh : Set
    Pos : Sh → Set
    dec : (s : Sh) → (p q : Pos s) → Dec (p ≡ q)
    next : (s : Sh) → Pos s → X

IC-old : {X Y : Set} → Set1
IC-old {X} {Y} = Y -> IC' X


⟦_⟧ : {X Y : Set} → IC X Y → (X → Set) → (Y → Set)
⟦ mkIC S P dec n ⟧ Q y = Σ[ s ∈ S y ] ((p : P y s) → Q (n y s p))

Diff : {X Y : Set} → IC X Y → IC (X ⊎ X) Y
Diff (mkIC S P dec n) = mkIC
  (λ y → Σ (S y) (P y))
  (λ y (s , p) → ⊤ ⊎ Σ[ q ∈ P y s ] (p ≡ q → ⊥))
  (λ y (s , p) → ⊎.≡-dec ⊤._≟_ (Σ.≡-dec (dec y s) dec→≠))
  (λ y (s , p) → Data.Sum.map (λ tt → n y s p) (λ (q , q≠p) → n y s q))



Dec-to-⊎ : {P : Set} → Dec P → P ⊎ (P → ⊥)
Dec-to-⊎ (yes p) = inj₁ p
Dec-to-⊎ (no ¬p) = inj₂ ¬p

Diff-old : {X Y : Set} → IC X Y → IC (X ⊎ X) Y
Diff-old (mkIC S P dec n) = mkIC
  (λ y → Σ (S y) (P y))
  (λ y (s , p) → P y s)
  (λ y (s , p) → dec y s)
  (λ y (s , p) q → Data.Sum.map (λ _ → n y s p) (λ _ → n y s q) (Dec-to-⊎ (dec y s p q)))
