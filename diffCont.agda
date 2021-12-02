{-# OPTIONS --without-K #-}
module diffCont where

open import Data.Nat as Nat  hiding (_+_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Data.Product as Sigma
open import Data.Sum
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero; suc to lsuc)
open import Function

infix 4 _≡Cont_ _≡Fam_ _==_
infix 5 _<|_

record _<->_ (A B : Set) : Set where
  field
    to : A → B
    from : B -> A
    from-to : (x : A) -> from (to x) ≡ x
    to-from : (x : B) -> to (from x) ≡ x
open _<->_

<->-refl : {A : Set} → A <-> A
to <->-refl = λ x → x
from <->-refl = λ x → x
from-to <->-refl = λ x → refl
to-from <->-refl = λ x → refl

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

⊤' : DecEqSet
carrier ⊤' = ⊤
decEq ⊤' x y = yes refl

⊥' : DecEqSet
carrier ⊥' = ⊥
decEq ⊥' ()

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

record _≡Fam_ {X}(A B : Fam X) : Set where
  field
    indices : index A <-> index B
    elements : (i : index A)(i' : index B) ->
               related-by indices i i' ->
               el A i ≡ el B i'
open _≡Fam_

≡Fam-refl : {X : Set}{A : Fam X} → A ≡Fam A
indices ≡Fam-refl = <->-refl
elements ≡Fam-refl i ._ (refl , snd) = refl

Fam-map : ∀ {D D' : Set} → (D → D') → Fam D → Fam D'
indexSet (Fam-map f X) = indexSet X
el (Fam-map f X) = λ y → f (el X y)

ΣFam : ∀ {I : DecEqSet}{D : Set} → (carrier I → Fam D) -> Fam D
ΣFam {I = I} X = fam ΣIX λ { (i , x) → el (X i) x } where
  ΣIX : DecEqSet
  carrier ΣIX = Σ[ i ∈ carrier I ] index (X i)
  decEq ΣIX = ≡-dec (decEq I) λ {i} → eq? (X i)

record _-Container (n : FinSet) : Set1 where
  constructor _<|_
  field
    Shape    : Set
    Position : Shape → Fam (El n)
open _-Container

record _≡Cont_ {n} (A B : n -Container) : Set where
  field
    shapes : Shape A <-> Shape B
    positions : (s : Shape A)(s' : Shape B) ->
                related-by shapes s s' ->
                Position A s ≡Fam Position B s'
open _≡Cont_

⟦_⟧ : ∀ {n} → n -Container → (El n → Set) → Set
⟦_⟧ {n} (S <| P) X = Σ[ s ∈ S ] ((i : index (P s)) → X (el (P s) i))

Hom : FinSet -> FinSet -> Set1
Hom n m = El m → n -Container

_==_ : ∀ {n m} →  Hom n m -> Hom n m -> Set
F == G = ∀ j → F j ≡Cont G j

⟦_⟧Hom : ∀ {n m} → Hom n m → (El n → Set) → (El m → Set)
⟦ F ⟧Hom X j = ⟦ F j ⟧ X

Id : ∀ {n} → Hom n n
Id = λ j → ⊤ <| λ _ → fam ⊤' (λ _ → j)

Whisker : ∀ {m k} → m -Container -> Hom k m → k -Container
Whisker {m} {k} (S <| P) F =
  (Σ[ s ∈ S ] ((x : index (P s)) → Shape (F (el (P s) x)))) <|
  (λ { (s , f) → ΣFam {I = indexSet (P s)} λ x → Position (F (el (P s) x)) (f x) })

_;_ : ∀ {n m k} → Hom n m → Hom m k → Hom n k
(F ; G) j = Whisker (G j) F

_;Id : ∀ {n m} → (F : Hom n m) → F ; Id == F
to (shapes ((F ;Id) j)) (_ , x) = x _
from (shapes ((F ;Id) j)) y = (tt , λ _ → y)
from-to (shapes ((F ;Id) j)) x = refl
to-from (shapes ((F ;Id) j)) y = refl
to (indices (positions ((F ;Id) j) s ._ (refl , _))) (_ , x) = x
from (indices (positions ((F ;Id) j) s ._ (refl , _))) x = (tt , x)
from-to (indices (positions ((F ;Id) j) s ._ (refl , _))) x = refl
to-from (indices (positions ((F ;Id) j) s ._ (refl , _))) y = refl
elements (positions ((F ;Id) j) s ._ (refl , _)) i i' (refl , _) = refl

Id;_ : ∀ {n m} → (F : Hom n m) → Id ; F == F
to (shapes ((Id; F) j)) (x , _) = x
from (shapes ((Id; F) j)) x = (x , λ _ → tt)
from-to (shapes ((Id; F) j)) x = refl
to-from (shapes ((Id; F) j)) y = refl
to (indices (positions ((Id; F) j) s ._ (refl , _))) (x , _) = x
from (indices (positions ((Id; F) j) s ._ (refl , _))) y = y , tt
from-to (indices (positions ((Id; F) j) s ._ (refl , _))) x = refl
to-from (indices (positions ((Id; F) j) s ._ (refl , _))) y = refl
elements (positions ((Id; F) j) s ._ (refl , _)) i ._ (refl , _) = refl

-- Cartesian structure

fst : ∀ {n m} → Hom (n `+ m) n
Shape (fst j) = ⊤
Position (fst j) _ = fam ⊤' λ _ → inl j

snd : ∀ {n m} → Hom (n `+ m) m
Shape (snd j) = ⊤
Position (snd j) _ = fam ⊤' λ _ → inr j

Times : ∀ {n n' m m'} → (F : Hom n m)(G : Hom n' m') → Hom (n `+ n') (m `+ m')
Shape (Times F G (inl x)) = Shape (F x)
Shape (Times F G (inr x)) = Shape (G x)
Position (Times F G (inl x)) s = Fam-map inl (Position (F x) s)
Position (Times F G (inr x)) s = Fam-map inr (Position (G x) s)

-- Left additive structure

Zero : ∀ {n m} → Hom n m
Zero j = ⊥ <| λ ()

CoprodCont : ∀ {n} → n -Container -> n -Container -> n -Container
CoprodCont (S <| P) (S' <| P') = (S ⊎ S') <| λ { (inj₁ s)  → P s
                                         ; (inj₂ s') → P' s' }

Plus : ∀ {n m} → Hom n m → Hom n m → Hom n m
Plus F G j = CoprodCont (F j) (G j)

-- TODO: assoc + units + comm for Plus

H;F+G : ∀ {n m k} → (F G : Hom n m)(H : Hom k n) →
     H ; Plus F G == Plus (H ; F) (H ; G)
to (shapes (H;F+G F G H j)) (inj₁ s , s') = inj₁ (s , s')
to (shapes (H;F+G F G H j)) (inj₂ s , s') = inj₂ (s , s')
from (shapes (H;F+G F G H j)) (inj₁ (s , s')) = (inj₁ s , s')
from (shapes (H;F+G F G H j)) (inj₂ (s , s')) = (inj₂ s , s')
from-to (shapes (H;F+G F G H j)) (inj₁ s , s') = refl
from-to (shapes (H;F+G F G H j)) (inj₂ s , s') = refl
to-from (shapes (H;F+G F G H j)) (inj₁ (s , s')) = refl
to-from (shapes (H;F+G F G H j)) (inj₂ (s , s')) = refl
positions (H;F+G F G H j) (inj₁ x₁ , snd₁) s' (refl , q) = ≡Fam-refl
positions (H;F+G F G H j) (inj₂ y , snd₁) s' (refl , q) = ≡Fam-refl

H;0 : ∀ {n m k} → (H : Hom k n) → H ; Zero == (Zero {k} {m})
to (shapes (H;0 H j)) = proj₁
from (shapes (H;0 H j)) = λ ()
from-to (shapes (H;0 H j)) = λ { (() , x) }
to-from (shapes (H;0 H j)) = λ ()
positions (H;0 H j) s () x

helper : ∀ {n} {m} {k} (F G : Hom n (m `+ k)) {j : El m} →
         Shape (F (inl j)) ⊎ Shape (G (inl j)) →
         Σ ⊤ (λ s → (x : ⊤) → Shape (F (inl j))) ⊎
         Σ ⊤ (λ s → (x : ⊤) → Shape (G (inl j)))
helper F G (inj₁ x) = inj₁ (_ , λ _ → x)
helper F G (inj₂ y) = inj₂ (_ , λ _ → y)



F+G;fst : ∀ {n m k} → (F G : Hom n (m `+ k)) →
          (Plus F G ; fst) == Plus (F ; fst) (G ; fst)
to (shapes (F+G;fst F G j)) (_ , x) = helper F G (x tt)
from (shapes (F+G;fst F G j)) (inj₁ (_ , x)) = _ , λ _ → inj₁ (x _)
from (shapes (F+G;fst F G j)) (inj₂ (_ , y)) = _ , λ _ → inj₂ (y _)
from-to (shapes (F+G;fst F G j)) (_ , x) = helper-lemma (x tt) where
  helper-lemma :  (w : Shape (F (inl j)) ⊎ Shape (G (inl j))) →
                   from (shapes (F+G;fst F G j)) (helper F G w) ≡ (tt , λ _ → w)
  helper-lemma (inj₁ x) = refl
  helper-lemma (inj₂ y) = refl
to-from (shapes (F+G;fst F G j)) (inj₁ x) = refl
to-from (shapes (F+G;fst F G j)) (inj₂ y) = refl
positions (F+G;fst F G j) (_ , ._) (inj₁ x) (p , refl) = ≡Fam-refl
positions (F+G;fst F G j) (_ , ._) (inj₂ y) (p , refl) = ≡Fam-refl

{-
F+G;snd : ∀ {n m k} → (F G : Hom n (m `+ k)) →
          (Plus F G ; snd) == Plus (F ; snd) (G ; snd)
F+G;snd = {!!}
-}

-- Derivatives

{-
_\\_ : (X : Set) → (x : X) → Set
X \\ x = Σ[ y ∈ X ] (x ≡ y → ⊥)
-}

DiffContainer : ∀ {n} → n -Container → (`2 `× n) -Container
Shape (DiffContainer (S <| P)) = Σ[ s ∈ S ] (index (P s))
indexSet (Position (DiffContainer (S <| P)) (s , h)) = indexSet (P s)
el (Position (DiffContainer (S <| P)) (s , h)) p = isYes (eq? (P s) p h) , el (P s) p

D : ∀ {n m} → Hom n m → Hom (`2 `× n) m
D F j = DiffContainer (F j)

ifTrue : {X : Set} → Bool × X -> Fam X
ifTrue (true , x) = fam ⊤' λ _ → x
ifTrue (false , x) = fam ⊥' λ ()

ayes : ∀ {n m} → Hom (`2 `× n) m -> Hom n m
Shape (ayes F j) = Shape (F j)
Position (ayes F j) s = ΣFam {indexSet (Position (F j) s)} (λ p → ifTrue ((el (Position (F j) s) p)))

noes : ∀ {n m} → Hom (`2 `× n) m -> Hom n m
Shape (noes F j) = Shape (F j)
Position (noes F j) s = ΣFam {indexSet (Position (F j) s)} (λ p → ifTrue (Sigma.map not id (el (Position (F j) s) p)))
