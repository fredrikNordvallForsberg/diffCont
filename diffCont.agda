{-# OPTIONS --without-K #-}
module diffCont where

open import Data.Nat as Nat  hiding (_+_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Data.Product as Sigma
open import Data.Sum as Sum
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Axiom.Extensionality.Propositional
open import Level renaming (zero to lzero; suc to lsuc)
open import Function
open import Function.Bundles

infix 4 _≡Cont_ _≡Fam_ _==_
infix 5 _<|_


postulate
  funext : Extensionality lzero lzero

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

<->-sym : {A B : Set} → A <-> B → B <-> A
to (<->-sym f) = from f
from (<->-sym f) = to f
from-to (<->-sym f) = to-from f
to-from (<->-sym f) = from-to f

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
a `+ b = `Σ `2 (λ x → if x then a else b)

pattern inl x = (true , x)
pattern inr x = (false , x)

`Π : (a : FinSet) -> (El a -> FinSet) -> FinSet
`Π `0 b = `1
`Π `1 b = b _
`Π `2 b = b false `× b true
`Π (`Σ a b) c = `Π a λ x → `Π (b x) λ y → c (x , y)

2*n<->n+n : ∀ {n} → El (`2 `× n) <-> El (n `+ n)
to 2*n<->n+n (false , x) = (false , x)
to 2*n<->n+n (true , x) = (true , x)
from 2*n<->n+n (false , x) = (false , x)
from 2*n<->n+n (true , x) = (true , x)
from-to 2*n<->n+n (false , x) = refl
from-to 2*n<->n+n (true , x) = refl
to-from 2*n<->n+n (false , x) = refl
to-from 2*n<->n+n (true , x) = refl


-- sets with decidable equality
record DecEqSet : Set1 where
  constructor mkDeqEqSet
  field
    carrier : Set
    decEq : DecidableEquality carrier
open DecEqSet

Dec-elim : {A : Set} → (P : Dec A -> Set) → ((a : A) → P (yes a)) → ((¬a : ¬ A) → P (no ¬a)) → (d : Dec A) → P d
Dec-elim P pt pf (yes p) = pt p
Dec-elim P pt pf (no ¬p) = pf ¬p

decEq-refl : ∀ {A : Set} → (dec : DecidableEquality A) → (x : A) → isYes (dec x x) ≡ true
decEq-refl dec x = Dec-elim (λ d → isYes d ≡ true) (λ _ → refl) (λ ¬p → ⊥-elim (¬p refl)) (dec x x)

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
ΣFam {I = I} X = fam (mkDeqEqSet (Σ[ i ∈ carrier I ] index (X i)) (≡-dec (decEq I) λ {i} → eq? (X i))) λ ix → let i = proj₁ ix; x = proj₂ ix in el (X i) x

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

≡Cont-refl : ∀ {n} → {A : n -Container} → A ≡Cont A
shapes ≡Cont-refl = <->-refl
indices (positions ≡Cont-refl s s' (refl , p)) = <->-refl
elements (positions ≡Cont-refl s s' (refl , p)) i i' (refl , p') = refl

⟦_⟧ : ∀ {n} → n -Container → (El n → Set) → Set
⟦_⟧ {n} (S <| P) X = Σ[ s ∈ S ] ((i : index (P s)) → X (el (P s) i))

Hom : FinSet -> FinSet -> Set1
Hom n m = El m → n -Container

_==_ : ∀ {n m} →  Hom n m -> Hom n m -> Set
F == G = ∀ j → F j ≡Cont G j

⟦_⟧Hom : ∀ {n m} → Hom n m → (El n → Set) → (El m → Set)
⟦ F ⟧Hom X j = ⟦ F j ⟧ X

Id' : ∀ {n m} → El n <-> El m → Hom n m
Id' f j = ⊤ <| λ _ → fam ⊤' λ _ → from f j

Id : ∀ {n} → Hom n n
Id = Id' <->-refl

Whisker : ∀ {m k} → m -Container -> Hom k m → k -Container
Whisker {m} {k} (S <| P) F =
  (Σ[ s ∈ S ] ((x : index (P s)) → Shape (F (el (P s) x)))) <|
  (λ sf → let s = proj₁ sf; f = proj₂ sf in ΣFam {I = indexSet (P s)} λ x → Position (F (el (P s) x)) (f x))

infixr 6 _;_

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

proj : ∀ {n m} → (f : El n → El m) → Hom m n
Shape (proj f j) = ⊤
Position (proj f j) _ = fam ⊤' λ _ → f j

fst : ∀ {n m} → Hom (n `+ m) n
fst = proj inl

snd : ∀ {n m} → Hom (n `+ m) m
snd = proj inr

Times : ∀ {n n' m m'} → (F : Hom n m)(G : Hom n' m') → Hom (n `+ n') (m `+ m')
Shape (Times F G (inl x)) = Shape (F x)
Shape (Times F G (inr x)) = Shape (G x)
Position (Times F G (inl x)) s = Fam-map inl (Position (F x) s)
Position (Times F G (inr x)) s = Fam-map inr (Position (G x) s)

⟨_,_⟩ : ∀ {n m m'} → Hom n m → Hom n m' → Hom n (m `+ m')
⟨ f , g ⟩ (inl j) = f j
⟨ f , g ⟩ (inr j) = g j

⟨_,_⟩' : ∀ {n m} → (f g : Hom n m) → Hom n (`2 `× m)
⟨ f , g ⟩' (true  , j) = f j
⟨ f , g ⟩' (false , j) = g j

⟨,⟩'=⟨,⟩ : ∀ {n m} → (f g : Hom n m) → ⟨ f , g ⟩' ; Id' 2*n<->n+n == ⟨ f , g ⟩
to (shapes (⟨,⟩'=⟨,⟩ f g (inl j))) (_ , x) = x _
from (shapes (⟨,⟩'=⟨,⟩ f g (inl j))) y = (_ , λ _ → y)
from-to (shapes (⟨,⟩'=⟨,⟩ f g (inl j))) x = refl
to-from (shapes (⟨,⟩'=⟨,⟩ f g (inl j))) y = refl
to (indices (positions (⟨,⟩'=⟨,⟩ f g (inl j)) s s' (p , refl))) = proj₂
from (indices (positions (⟨,⟩'=⟨,⟩ f g (inl j)) s s' (p , refl))) = λ x → _ , x
from-to (indices (positions (⟨,⟩'=⟨,⟩ f g (inl j)) s s' (p , refl))) x = refl
to-from (indices (positions (⟨,⟩'=⟨,⟩ f g (inl j)) s s' (p , refl))) x = refl
elements (positions (⟨,⟩'=⟨,⟩ f g (inl j)) s s' (p , refl)) i i' (refl , q') = refl
to (shapes (⟨,⟩'=⟨,⟩ f g (inr j))) (_ , x) = x _
from (shapes (⟨,⟩'=⟨,⟩ f g (inr j))) y = (_ , λ _ → y)
from-to (shapes (⟨,⟩'=⟨,⟩ f g (inr j))) x = refl
to-from (shapes (⟨,⟩'=⟨,⟩ f g (inr j))) y = refl
to (indices (positions (⟨,⟩'=⟨,⟩ f g (inr j)) s s' (p , refl))) = proj₂
from (indices (positions (⟨,⟩'=⟨,⟩ f g (inr j)) s s' (p , refl))) = λ x → _ , x
from-to (indices (positions (⟨,⟩'=⟨,⟩ f g (inr j)) s s' (p , refl))) x = refl
to-from (indices (positions (⟨,⟩'=⟨,⟩ f g (inr j)) s s' (p , refl))) x = refl
elements (positions (⟨,⟩'=⟨,⟩ f g (inr j)) s s' (p , refl)) i i' (refl , q') = refl

-- Left additive structure

Zero : ∀ n m → Hom n m
Zero n m j = ⊥ <| λ ()

CoprodCont : ∀ {n} → n -Container -> n -Container -> n -Container
CoprodCont (S <| P) (S' <| P') = (S ⊎ S') <| Sum.[ P , P' ]

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

H;0 : ∀ {n m k} → (H : Hom k n) → H ; Zero n m == Zero k m
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


-- TODO: update to talk about proj f in general

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
el (Position (DiffContainer (S <| P)) (s , h)) p = (isYes (eq? (P s) p h) , el (P s) p)

D : ∀ {n m} → Hom n m → Hom (`2 `× n) m
D F j = DiffContainer (F j)

-- [CD.1]

DZero=Zero : ∀ {n m} → D (Zero n m) == Zero _ _
to (shapes (DZero=Zero j)) (() , s)
from (shapes (DZero=Zero j)) ()
from-to (shapes (DZero=Zero j)) (() , s)
to-from (shapes (DZero=Zero j)) ()
positions (DZero=Zero j) s ()

D[F+G]=DF+DG : ∀ {n m} → (F G : Hom n m) → D (Plus F G) == Plus (D F) (D G)
to (shapes (D[F+G]=DF+DG F G j)) (inj₁ x , y) = inj₁ (x , y)
to (shapes (D[F+G]=DF+DG F G j)) (inj₂ x , y) = inj₂ (x , y)
from (shapes (D[F+G]=DF+DG F G j)) (inj₁ (x , y)) = inj₁ x , y
from (shapes (D[F+G]=DF+DG F G j)) (inj₂ (x , y)) = inj₂ x , y
from-to (shapes (D[F+G]=DF+DG F G j)) (inj₁ x , y) = refl
from-to (shapes (D[F+G]=DF+DG F G j)) (inj₂ x , y) = refl
to-from (shapes (D[F+G]=DF+DG F G j)) (inj₁ (x , y)) = refl
to-from (shapes (D[F+G]=DF+DG F G j)) (inj₂ (x , y)) = refl
indices (positions (D[F+G]=DF+DG F G j) (inj₁ x , y) .(to (shapes (D[F+G]=DF+DG F G j)) (inj₁ x , y)) (refl , q)) = <->-refl
elements (positions (D[F+G]=DF+DG F G j) (inj₁ x , y) .(to (shapes (D[F+G]=DF+DG F G j)) (inj₁ x , y)) (refl , q)) i i (refl , r) = refl
indices (positions (D[F+G]=DF+DG F G j) (inj₂ y₁ , y) .(to (shapes (D[F+G]=DF+DG F G j)) (inj₂ y₁ , y)) (refl , q)) = <->-refl
elements (positions (D[F+G]=DF+DG F G j) (inj₂ y₁ , y) .(to (shapes (D[F+G]=DF+DG F G j)) (inj₂ y₁ , y)) (refl , q)) i i (refl , r) = refl

-- TODO: update to talk about proj ...

-- POSSIBLY GOOD IDEA: Generalise to any morphism that behaves like Id (or Id' f)

-- [CD.2]

Pair0;Df : ∀ {n m k} → (a : Hom n m)(f : Hom m k) →
           ⟨ Zero n m , a ⟩' ; D f == Zero n k
to (shapes (Pair0;Df a f j)) ((x , x') , y) = subst (λ z → Shape (⟨ (λ j₁ → ⊥ <| (λ ())) , a ⟩' (z , el (Position (f j) x) x'))) (decEq-refl (decEq (indexSet (Position (f j) x))) x') (y x')
from (shapes (Pair0;Df a f j)) ()
from-to (shapes (Pair0;Df a f j)) x = ⊥-elim (to (shapes (Pair0;Df a f j)) x)
to-from (shapes (Pair0;Df a f j)) ()
positions (Pair0;Df a f j) s () (p , q)

Bool-elim : (P : Bool -> Set) → P true → P false → (b : Bool) → P b
Bool-elim P pt pf true = pt
Bool-elim P pt pf false = pf

isLeft : {A B : Set} → A ⊎ B → Set
isLeft (inj₁ x) = ⊤
isLeft (inj₂ y) = ⊥

Pair+;Df : ∀ {n m k} → (a b c : Hom n m)(f : Hom m k) →
           ⟨ Plus b c , a ⟩' ; D f == Plus (⟨ b , a ⟩' ; D f) (⟨ c , a ⟩' ; D f)
to (shapes (Pair+;Df a b c f j)) ((x , y) , z) = Sum.map (λ y' → (x , y) , λ i → Dec-elim (λ w → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (isYes w , el (Position (f j) x) i)) → Shape (⟨ b , a ⟩' (isYes w , el (Position (f j) x) i))) (λ p → subst (λ w → Shape (b (el (Position (f j) x) w)) ⊎ Shape (c (el (Position (f j) x) w)) → Shape (b (el (Position (f j) x) w))) (sym  p) [ id , (λ _ → y') ]′) (λ _ → id) (decEq (indexSet (Position (f j) x)) i y) (z i)) (λ y' → (x , y) , λ i → Dec-elim (λ w → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (isYes w , el (Position (f j) x) i)) → Shape (⟨ c , a ⟩' (isYes w , el (Position (f j) x) i))) (λ { refl → [ (λ _ → y') , id ]′ }) (λ _ → id) (decEq (indexSet (Position (f j) x)) i y) (z i) ) (subst (λ w → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (w , el (Position (f j) x) y))) (decEq-refl (decEq (indexSet (Position (f j) x))) y) (z y))
from (shapes (Pair+;Df a b c f j)) (inj₁ ((x , y) , z)) = (x , y) , λ i → Bool-elim (λ w → Shape (⟨ b , a ⟩' (w , el (Position (f j) x) i)) → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (w , el (Position (f j) x) i))) inj₁ id (isYes (decEq (indexSet (Position (f j) x)) i y)) (z i)
from (shapes (Pair+;Df a b c f j)) (inj₂ ((x , y) , z)) = (x , y) , λ i → Bool-elim (λ w → Shape (⟨ c , a ⟩' (w , el (Position (f j) x) i)) → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (w , el (Position (f j) x) i))) inj₂ id (isYes (decEq (indexSet (Position (f j) x)) i y)) (z i)
from-to (shapes (Pair+;Df a b c f j)) ((x , y) , z) with (decEq (indexSet (Position (f j) x)) y y) | (decEq-refl (decEq (indexSet (Position (f j) x))) y) | z y
... | yes p | refl | inj₁ x' = Inverse.f Σ-≡,≡↔≡ (refl , funext (λ i → help i (decEq (indexSet (Position (f j) x)) i y) (z i) {!!})) where
  help : ∀ i q (zi : Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (isYes q , el (Position (f j) x) i))) → ((p : i ≡ y)(r : q ≡ yes p) → isLeft ((subst (λ w → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (isYes w , el (Position (f j) x) i))) r zi))) → Bool-elim (λ w →  Shape (⟨ b , a ⟩' (w , el (Position (f j) x) i)) → Shape (⟨(λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (w , el (Position (f j) x) i))) inj₁ (λ x₁ → x₁) (isYes q) (Dec-elim (λ w → Shape (⟨ (λ j₁ → (Shape (b j₁) ⊎ Shape (c j₁)) <| Sum.[ Position (b j₁) , Position (c j₁) ]) , a ⟩' (isYes w , el (Position (f j) x) i)) → Shape (⟨ b , a ⟩' (isYes w , el (Position (f j) x) i))) (λ p → subst (λ w → Shape (b (el (Position (f j) x) w)) ⊎ Shape (c (el (Position (f j) x) w)) → Shape (b (el (Position (f j) x) w))) (sym  p) [ id , (λ _ → x') ]′) (λ _ → id) q (zi)) ≡ zi
  help i (yes refl) (inj₁ x) qq = refl
  help i (yes refl) (inj₂ y) qq = ⊥-elim (qq refl refl)
  help i (no p) zi qq = refl
... | yes p | refl | inj₂ x' = {!!}

to-from (shapes (Pair+;Df a b c f j)) (inj₁ ((x , y) , z)) = {!!}
to-from (shapes (Pair+;Df a b c f j)) (inj₂ ((x , y) , z)) = {!!}
positions (Pair+;Df a b c f j) = {!!}

-- [CD.3]

DId=fst : ∀ {n} → D (Id {n}) == (Id' 2*n<->n+n ; fst {n} {n})
to (shapes (DId=fst j)) = _
from (shapes (DId=fst j)) = _
from-to (shapes (DId=fst j)) x = refl
to-from (shapes (DId=fst j)) x = refl
to (indices (positions (DId=fst j) s s' (p , q))) = _
from (indices (positions (DId=fst j) s s' (p , q))) = _
from-to (indices (positions (DId=fst j) s s' (p , q))) x = refl
to-from (indices (positions (DId=fst j) s s' (p , q))) x = refl
elements (positions (DId=fst j) s s' (p , q)) i i' r = refl

Dfst=fst;fst : ∀ {n m} → D (fst {n} {m}) == (Id' 2*n<->n+n ; (fst ; fst))
to (shapes (Dfst=fst;fst j)) _ = (tt , (λ _ → tt)) , λ _ → tt
from (shapes (Dfst=fst;fst j)) _ = tt , tt
from-to (shapes (Dfst=fst;fst j)) x = refl
to-from (shapes (Dfst=fst;fst j)) x = refl
to (indices (positions (Dfst=fst;fst j) s s' (p , q))) _ = (tt , tt) , tt
from (indices (positions (Dfst=fst;fst j) s s' (p , q))) _ = tt
from-to (indices (positions (Dfst=fst;fst j) s s' (p , q))) x = refl
to-from (indices (positions (Dfst=fst;fst j) s s' (p , q))) x = refl
elements (positions (Dfst=fst;fst j) s s' (p , q)) tt ((tt , tt) , tt) = λ x → refl

Dsnd=fst;snd : ∀ {n m} → D (snd {n} {m}) == (Id' 2*n<->n+n ; (fst ; snd))
to (shapes (Dsnd=fst;snd j)) _ = (tt , (λ _ → tt)) , λ _ → tt
from (shapes (Dsnd=fst;snd j)) _ = tt , tt
from-to (shapes (Dsnd=fst;snd j)) x = refl
to-from (shapes (Dsnd=fst;snd j)) x = refl
to (indices (positions (Dsnd=fst;snd j) s s' (p , q))) _ = (tt , tt) , tt
from (indices (positions (Dsnd=fst;snd j) s s' (p , q))) _ = tt
from-to (indices (positions (Dsnd=fst;snd j) s s' (p , q))) x = refl
to-from (indices (positions (Dsnd=fst;snd j) s s' (p , q))) x = refl
elements (positions (Dsnd=fst;snd j) s s' (p , q)) tt ((tt , tt) , tt) _ = refl

-- [CD.4]

Dpair : ∀ {n m m'} → (f : Hom n m) → (g : Hom n m') → D ⟨ f , g ⟩ == ⟨ D f , D g ⟩
Dpair f g (inl j) = ≡Cont-refl
Dpair f g (inr j) = ≡Cont-refl

-- [CD.5]

chainRule : ∀ {n m k} → (f : Hom n m)(g : Hom m k) →
            D (f ; g) == ⟨ D f , (Id' 2*n<->n+n ; fst {n} {n}) ; f ⟩' ; D g
to (shapes (chainRule f g j)) ((x , y) , (z , w)) = ((x , z) , (λ i → Dec-elim (λ w → Shape (⟨ (λ j₁ → DiffContainer (f j₁)) , (λ j₁ → Σ (Shape (f j₁)) (λ s → (x₁ : carrier (indexSet (Position (f j₁) s))) →   Σ ⊤ (λ s₁ → (x₂ : ⊤) → ⊤)) <| (λ sf → fam (mkDeqEqSet (Σ (carrier (indexSet (Position (f j₁) (proj₁ sf)))) (λ i₁ → Σ ⊤ (λ i₂ → ⊤))) (≡-dec (decEq (indexSet (Position (f j₁) (proj₁ sf)))) (≡-dec (λ x₁ y₁ → yes refl) (λ {i} x₁ y₁ → yes refl)))) (λ ix → inl (el (Position (f j₁) (proj₁ sf)) (proj₁ ix))))) ⟩' (isYes w , el (Position (g j) x) i)))
       (λ p → (y i) , (subst (λ w → index (Position (f (el (Position (g j) x) w)) (y w))) (sym p) w))
       (λ ¬p → (y i) , _) (decEq (indexSet (Position (g j) x)) i z)))
from (shapes (chainRule f g j)) ((x , y) , z) = let
  aux = (λ i → Dec-elim (λ w → (Shape (⟨ (λ j₁ → DiffContainer (f j₁)) , (λ j₁ → Σ (Shape (f j₁)) (λ s → (x₁ : carrier (indexSet (Position (f j₁) s))) →  Σ ⊤ (λ s₁ → (x₂ : ⊤) → ⊤)) <| (λ sf → fam (mkDeqEqSet (Σ (carrier (indexSet (Position (f _) (proj₁ sf)))) (λ s₁ → Σ ⊤ (λ x₃ → ⊤))) (≡-dec (decEq (indexSet (Position (f _) (proj₁ sf)))) (≡-dec (λ x₁ y₁ → yes refl) (λ x₁ y₁ → yes refl)))) (λ ix → inl (el (Position (f _) (proj₁ sf)) (proj₁ ix))))) ⟩' (isYes w , el (Position (g j) x) i))) → Σ[ s ∈ (Shape (f (el (Position (g j) x) i))) ] (i ≡ y -> index (Position (f (el (Position (g j) x) i)) s)) ) (λ _ p → proj₁ p , λ _ → proj₂ p) (λ ¬i≡y p → (proj₁ p) , (λ i≡y → ⊥-elim (¬i≡y i≡y))) (decEq (indexSet (Position (g j) x)) i y) (z i))
  in (x , λ i → proj₁ (aux i)) , y , proj₂ (aux y) refl
from-to (shapes (chainRule f g j)) ((x , y) , (z , w)) =  Inverse.f Σ-≡,≡↔≡ ( Inverse.f Σ-≡,≡↔≡ (refl , funext (λ i → {!help!})) , {!subst id (sym (subst-Σ-≡,≡↔≡ !})
to-from (shapes (chainRule f g j)) ((x , y) , z) = Inverse.f Σ-≡,≡↔≡ (refl , funext (λ i → {!!}))
indices (positions (chainRule f g j) ((x , y) , (z , w)) ((x' , y') , z') (refl , q)) = {!!}
elements (positions (chainRule f g j) s s'  x) = {!!}

-- [CD.6]

g0DDf : ∀ {n m} → (f : Hom n n)(g h : Hom m n)(k : Hom m n) →
       ⟨ ⟨ g , Zero m n ⟩' , ⟨ h , k ⟩' ⟩' ; D (D f) == ⟨ g , k ⟩' ; D f
g0DDf = {!!}


-- [CD.7]

zeroesDDf : ∀ {n m ℓ} → (f : Hom n m)(g h k : Hom ℓ n) →
             ⟨ ⟨ Zero ℓ n , h ⟩' , ⟨ g , k ⟩' ⟩' ; D (D f) ==
              ⟨ ⟨ Zero ℓ n , g ⟩' , ⟨ h , k ⟩' ⟩' ; D (D f)
zeroesDDf = {!!}


-------------------------------


ifTrue : {X : Set} → Bool × X -> Fam X
ifTrue (true , x) = fam ⊤' λ _ → x
ifTrue (false , x) = fam ⊥' λ ()

ayes : ∀ {n m} → Hom (`2 `× n) m -> Hom n m
Shape (ayes F j) = Shape (F j)
Position (ayes F j) s = ΣFam {indexSet (Position (F j) s)} (λ p → ifTrue ((el (Position (F j) s) p)))

noes : ∀ {n m} → Hom (`2 `× n) m -> Hom n m
Shape (noes F j) = Shape (F j)
Position (noes F j) s = ΣFam {indexSet (Position (F j) s)} (λ p → ifTrue (Sigma.map not id (el (Position (F j) s) p)))

