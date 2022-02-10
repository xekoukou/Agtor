{-# OPTIONS  --confluence-check --sized-types --cubical #-}

module Definitions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Codata.Stream
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Binary

module Br = BinaryRelation

open import UType public hiding (_×_)

data Tree (A : Type₁) : Type₁ where
  ε    : Tree A
  `_   : A → Tree A
  _·_  : Tree A → Tree A → Tree A


data R {A : Type₁} : Tree A → Tree A → Type₁ where
  assoc  : (x y z : Tree A) → R (x · (y · z)) ((x · y) · z)
  rid    : (x : Tree A) → R (x · ε) x
  comm   :  (x y : Tree A) → R (x · y) (y · x)
  ·c     : {x y : Tree A} →  (c : Tree A) → R x y → R (x · c) (y · c)


_*_ : ∀{A} → Tree A / R → Tree A / R →  Tree A / R
_*_ {A = A} a b = rec2 squash/ (λ a b → [ a · b ]) l1 l2 a b where
  l1 : (a b c : Tree A) → R a b → [ a · c ] ≡ [ b · c ]
  l1 a b c r = eq/ _ _ (·c c r)
  
  l2 : (c a b : Tree A) → R a b → [ c · a ] ≡ [ c · b ]
  l2 c a b r = eq/ _ _ (comm _ _) ∙∙ l1 a b c r ∙∙ eq/ _ _ (comm _ _)



assoc* : ∀{A} → (x y z : Tree A / R) → (x * (y * z)) ≡ ((x * y) * z)
assoc* = elimProp3 (λ x y z → squash/ ((x * (y * z))) (((x * y) * z)))
                   (λ x y z → eq/ _ _ (assoc x y z))

rid* : ∀{A} → (x : Tree A / R) → (x * [ ε ]) ≡ x
rid* = elimProp (λ x → squash/ (x * [ ε ]) x)
                (λ x → eq/ _ _ (rid x))

comm* : ∀{A} → (x y : Tree A / R) → (x * y) ≡ (y * x)
comm* = elimProp2 (λ x y → squash/ _ _)
                (λ x y → eq/ _ _ (comm x y))

TreeCommMonoid : ∀{A} → CommMonoid _
TreeCommMonoid {A} = makeCommMonoid [ ε {A} ] _*_ squash/ assoc* rid* (λ x → comm* _ x ∙ rid* x) comm*

T : ∀ A → ∀ B → _
T A B = Tree A / R × Tree B / R


_**_ : ∀{A B} → T A B → T A B → T A B
_**_ (x1 , y1) (x2 , y2) = x1 * x2 , y1 * y2

dd : {A B : Type₁} → isSet A → isSet B → isSet (A × B)
dd isa isb (x1 , y1) (x2 , y2) p1 p2
  = let xp1 , yp1 = PathPΣ p1
        xp2 , yp2 = PathPΣ p2
    in cong ΣPathP (λ i → isa _ _ xp1 xp2 i , isb _ _ yp1 yp2 i)

ddp : ∀{A B} → (x y : T A B) → isProp (x ≡ y)
ddp = dd squash/ squash/

assoc** : {A B : Type₁} → (x y z : Σ (Tree A / R) (λ _ → Tree B / R)) →
          (x ** (y ** z)) ≡ ((x ** y) ** z)
assoc** (x1 , x2) (y1 , y2) (z1 , z2) = λ i → (assoc* x1 y1 z1 i) , (assoc* x2 y2 z2 i)

rid** :  {A B : Type₁} → (x : Σ (Tree A / R) (λ _ → Tree B / R)) →
         (x ** ([ ε ] , [ ε ])) ≡ x
rid** (x1 , x2) i = (rid* x1 i) , (rid* x2 i)

lid** :  {A B : Type₁} → (x : Σ (Tree A / R) (λ _ → Tree B / R)) →
         (([ ε ] , [ ε ]) ** x) ≡ x
lid** (x1 , x2) i = ((comm* _ x1 ∙ rid* x1) i) , (((comm* _ x2 ∙ rid* x2) i))

comm** : {A B : Type₁} → (x y : Σ (Tree A / R) (λ _ → Tree B / R)) →
          (x ** y) ≡ (y ** x)
comm** (x1 , x2) (y1 , y2) = λ i → (comm* x1 y1 i) , (comm* x2 y2 i)


TCommonoid : ∀ {A} {B} → CommMonoid _
TCommonoid {A} {B} = makeCommMonoid ([ ε {A} ] , [ ε {B} ]) _**_
                                    (dd squash/ squash/) assoc** rid** lid** comm**


p1 : ∀{A} → ∀{B} → T A B → T A B
p1 (x , y) = x , [ ε ]

p2 : ∀{A} → ∀{B} → T A B → T A B
p2 (x , y) = [ ε ] , y





record ActorT : Type₁ where
  coinductive
  field
    P : UType → Type
    decP  : ∀ A → Maybe (P A)
    image : ∀ {A} → { p : P A } → ⟨ A ⟩ → Tree UType
    next  : ∀ {A} → { p : P A } → ⟨ A ⟩ → Tree ActorT




W : Type₁
W = T UType ActorT



data Bree {A : Type₁} : Type₂ where
  ∅    : Bree
  `_   : A → Bree
  ƛ_   : {B : Type} → (B → Bree {A}) → Bree
  _∪_  : Bree {A} → Bree {A} → Bree
  _·_  : Bree {A} → Bree {A} → Bree


infixr 5 _∪_
infixr 7 _·_
infixr 10 `_


data S : Bree {W} → Bree {W} → Type₂ where
  assoc   : (x y z : Bree {W}) → S (x ∪ (y ∪ z)) ((x ∪ y) ∪ z)
  rid     : (x : Bree {W}) → S (x ∪ ∅) x
  comm    : (x y : Bree {W}) → S (x ∪ y) (y ∪ x)
  ∪c      : {x y : Bree {W}} → (c : Bree {W}) → S x y → S (x ∪ c) (y ∪ c)
  
  idem    : (x : Bree {W}) → S (x ∪ x) x

  assoc·   : (x y z : Bree {W}) → S (x · (y · z)) ((x · y) · z)
  rid·     : (x : Bree {W}) → S (x · ` ([ ε ] , [ ε ])) x
  ·c      : {x y : Bree {W}} → (c : Bree {W}) → S x y → S (x · c) (y · c)
  comm·   : (x y : Bree {W}) → S (x · y) (y · x)

  def∅·   : (x : Bree {W}) → S (x · ∅) ∅
  def·    : (x y : W) → S ((` x) · (` y)) (` (x ** y))
  defƛ·   : ∀{C} → (x : Bree {W}) → (y : C → Bree {W}) → S (x · (ƛ y)) (ƛ λ q → x · (y q))
  dist    : (x y z : Bree {W}) → S (x · (y ∪ z)) ((x · y) ∪ (x · z))

  distƛ∪  : ∀{C} → (x y : C → Bree {W}) → S (ƛ λ c → (x c ∪ y c)) (ƛ x ∪ ƛ y)
  distƛ·  : ∀{C} → (x y : C → Bree {W}) → S (ƛ λ c → (x c · y c)) (ƛ x · ƛ y)
  remƛ    : ∀{C} → (x : Bree {W}) → (y : C → Bree {W}) → y ≡ (λ _ → x) → S (ƛ y) x
  ƛS      : ∀{C} → {x y : C → Bree {W}} → ((c : C) → S (x c) (y c)) → S (ƛ x) (ƛ y)

--  r-sym  : {x y : Bree {W}} → S x y → S y x
--  r-refl : {x : Bree {W}} → S x x
--  r-trans : {x y z : Bree {W}} → S x y → S y z → S x z


∪c≡ : {a b : Bree} → (c : Bree) → S a b → Path (Bree {W} / S) [ a ∪ c ] [ b ∪ c ]
∪c≡ c r = eq/ _ _ (∪c c r)

c∪≡ : {a b : Bree} → (c : Bree) → S a b → [ c ∪ a ] ≡ [ c ∪ b ]
c∪≡ c r = eq/ _ _ (comm _ _) ∙∙ ∪c≡ c r ∙∙ eq/ _ _ (comm _ _)

∪≡ : {a1 a2 b1 b2 : Bree} → S a1 a2 → S b1 b2 → Path (Bree {W} / S) [ a1 ∪ b1 ] [ a2 ∪ b2 ]
∪≡ r1 r2 = ∪c≡ _ r1 ∙ c∪≡ _ r2 


_⋃_ : Bree / S → Bree / S → Bree / S
_⋃_ a b = rec2 squash/ (λ a b → [ a ∪ b ]) (λ _ _ → ∪c≡) (λ c _ _ → c∪≡ c) a b



assoc⋃ : (x y z : Bree / S) → (x ⋃ (y ⋃ z)) ≡ ((x ⋃ y) ⋃ z)
assoc⋃ = elimProp3 (λ x y z → squash/ ((x ⋃ (y ⋃ z))) (((x ⋃ y) ⋃ z)))
                   (λ x y z → eq/ _ _ (assoc x y z))

rid⋃ : (x : Bree / S) → (x ⋃ [ ∅ ]) ≡ x
rid⋃ = elimProp (λ x → squash/ (x ⋃ [ ∅ ]) x)
                (λ x → eq/ _ _ (rid x))

comm⋃ : (x y : Bree / S) → (x ⋃ y) ≡ (y ⋃ x)
comm⋃ = elimProp2 (λ x y → squash/ _ _)
                (λ x y → eq/ _ _ (comm x y))


idem⋃ : (x : Bree / S) → (x ⋃ x) ≡ x
idem⋃ = elimProp (λ x → squash/ (x ⋃ x) x) λ a → eq/ _ _ (idem a)


BCommonoid : CommMonoid _
BCommonoid = makeCommMonoid [ ∅ ] _⋃_ squash/ assoc⋃ rid⋃ (λ x → comm⋃ _ x ∙ rid⋃ x)  comm⋃

BSemillatice : Semilattice _
fst BSemillatice = Bree / S
SemilatticeStr.ε (snd BSemillatice) = [ ∅ ]
SemilatticeStr._·_ (snd BSemillatice) = _⋃_
IsSemilattice.isCommMonoid (SemilatticeStr.isSemilattice (snd BSemillatice)) = BCommonoid .snd .CommMonoidStr.isCommMonoid
IsSemilattice.idem (SemilatticeStr.isSemilattice (snd BSemillatice)) = idem⋃


·c≡ : {a b : Bree} → (c : Bree) → S a b → Path (Bree {W} / S) [ a · c ] [ b · c ]
·c≡ c r = eq/ _ _ (·c c r)

c·≡ : {a b : Bree} → (c : Bree) → S a b → [ c · a ] ≡ [ c · b ]
c·≡ c r = eq/ _ _ (comm· _ _) ∙∙ ·c≡ c r ∙∙ eq/ _ _ (comm· _ _)

·≡ : {a1 a2 b1 b2 : Bree} → S a1 a2 → S b1 b2 → Path (Bree {W} / S) [ a1 · b1 ] [ a2 · b2 ]
·≡ r1 r2 = ·c≡ _ r1 ∙ c·≡ _ r2 

_··_ : Bree / S → Bree / S → Bree / S
_··_ a b = rec2 squash/ (λ a b → [ a · b ]) (λ _ _ → ·c≡) (λ c _ _ → c·≡ c) a b

ι : Bree {W} / S
ι = [ ` ([ ε ] , [ ε ]) ]

assoc·· : (x y z : Bree / S) → (x ·· (y ·· z)) ≡ ((x ·· y) ·· z)
assoc·· = elimProp3 (λ x y z → squash/ ((x ·· (y ·· z))) (((x ·· y) ·· z)))
                   (λ x y z → eq/ _ _ (assoc· x y z))

rid·· : (x : Bree / S) → (x ··  ι) ≡ x
rid·· = elimProp (λ x → squash/ (x ··  ι ) x)
                (λ x → eq/ _ _ (rid· x))

comm·· : (x y : Bree / S) → (x ·· y) ≡ (y ·· x)
comm·· = elimProp2 (λ x y → squash/ _ _)
                (λ x y → eq/ _ _ (comm· x y))


dist·· : (a b c : Bree / S) → (a ·· (b ⋃ c)) ≡ (a ·· b) ⋃ (a ·· c)
dist·· = elimProp3 (λ x y z → squash/ (x ·· (y ⋃ z)) ((x ·· y) ⋃ (x ·· z)))
                   λ a b c → eq/ _ _ (dist _ _ _) 

B·Commonoid : CommMonoid _
B·Commonoid = makeCommMonoid ι _··_ squash/ assoc·· rid·· (λ x → comm·· _ x ∙ rid·· x)  comm··



data Dree : Type₂ where
   `_   : Bree {W} → Dree
   _·_  : Dree → Dree → Dree
   _∪_  : Dree → Dree → Dree
   δ    : Dree → Dree
   δᶜ   : Dree → Dree → Dree

-- infixr 5 _∪_
-- infixr 7 _·_
-- infixr 10 `_


-- infixr 9 δ
-- infixr 9 δᶜ

-- module _ where
--   open ActorT
--   compute : UType → ActorT → Bree {W}
--   compute uT actT = l1 (actT .decP uT) where
--     l1 : Maybe (actT .P uT) → Bree {W}
--     l1 (just p) = ƛ λ x → ` ([ actT .image {_} {p} x ] , [ actT .next {_} {p} x ])
--     l1 nothing = ∅


-- data S : Bree {W} → Bree {W} → Type₂ where
--   assoc   : (x y z : Bree {W}) → S (x ∪ (y ∪ z)) ((x ∪ y) ∪ z)
--   rid     : (x : Bree {W}) → S (x ∪ ∅) x
--   comm    : (x y : Bree {W}) → S (x ∪ y) (y ∪ x)
--   idem    : (x : Bree {W}) → S (x ∪ x) x
--   dist    : (x y z : Bree {W}) → S (x · (y ∪ z)) ((x · y) ∪ (x · z))
--   def·    : (x y : W) → S ((` x) · (` y)) (` (x ** y))
--   defδ    : ∀{x y} → S (δ (` ([ ` x ] , [ ` y ]))) (compute x y)

--   -- leibniz rule
--   lbnz    : (x y : Bree {W}) → S (δ (x · y)) 
--                 (((δ x) · y) ∪ (x · (δ y)) ∪ δᶜ x y)
--   distδ   : (x y : Bree {W}) → S (δ (x ∪ y)) (δ x ∪ δ y)
--   distδᶜl : (x y z : Bree {W}) → S (δᶜ (x ∪ y) z) (δᶜ x z ∪ δᶜ y z)
--   distδᶜr : (x y z : Bree {W}) → S (δᶜ z (x ∪ y)) (δᶜ z x ∪ δᶜ z y)
--   defδᶜ   : (x1 x2 : Tree UType / R) (y1 y2 : Tree ActorT / R) → S (δᶜ (` (x1 , y1)) (` (x2 , y2)) ) (δ (` (x1 , y2)) · (` (x2 , y1)) ∪ (` (x1 , y2)) · δ (` (x2 , y1)))

--   distƛ   : ∀{C} → (x y : C → Bree {W}) → S (ƛ λ c → (x c ∪ y c)) (ƛ x ∪ ƛ y)
--   remƛ    : ∀{C} → (x : Bree {W}) → (y : C → Bree {W}) → S (ƛ y) x

--   r-sym  : {x y : Bree {W}} → S x y → S y x
--   r-refl : {x : Bree {W}} → S x x
--   r-trans : {x y z : Bree {W}} → S x y → S y z → S x z
--   r-cong  : {x y : Bree {W}} → (f : Bree {W} → Bree {W}) → S x y → S (f x) (f y)


-- Q : Type₂
-- Q = Bree / S



