{-# OPTIONS --cubical #-}

module MTree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.CommMonoid
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Sigma


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ

data Tree (A : Type ℓ) : Type ℓ where
  ε    : Tree A
  `_   : A → Tree A
  _·_  : Tree A → Tree A → Tree A

map : ∀{A B : Type ℓ} → (f : A → B) → Tree A → Tree B
map f ε = ε
map f (` x) = ` (f x)
map f (t1 · t2) = map f t1 · map f t2

map-id : ∀{A : Type ℓ} → (x : Tree A) → map (λ y → y) x ≡ x
map-id ε = refl
map-id (` x) = refl
map-id (x · y) with map-id x | map-id y
... | r | w = cong₂ (λ a b → a · b) r w

data R {A : Type ℓ} : Tree A → Tree A → Type ℓ where
  assoc  : (x y z : Tree A) → R (x · (y · z)) ((x · y) · z)
  rid    : (x : Tree A) → R (x · ε) x
  comm   :  (x y : Tree A) → R (x · y) (y · x)
  ·c     : {x y : Tree A} →  (c : Tree A) → R x y → R (x · c) (y · c)

·c≡ : {a b : Tree A} → (c : Tree A) → R a b → Path (Tree A / R) [ a · c ] [ b · c ]
·c≡ c r = eq/ _ _ (·c c r)

c·≡ : {a b : Tree A} → (c : Tree A) → R a b → [ c · a ] ≡ [ c · b ]
c·≡ c r = eq/ _ _ (comm _ _) ∙∙ ·c≡ c r ∙∙ eq/ _ _ (comm _ _)

·≡ : {a1 a2 b1 b2 : Tree A} → R a1 a2 → R b1 b2 → Path (Tree A / R) [ a1 · b1 ] [ a2 · b2 ]
·≡ r1 r2 = ·c≡ _ r1 ∙ c·≡ _ r2 

private
  _*_ : Tree A / R → Tree A / R →  Tree A / R
  _*_ {A = A} a b = rec2 squash/ (λ a b → [ a · b ]) (λ _ _ → ·c≡) (λ c _ _ → c·≡ c) a b

  assoc* : (x y z : Tree A / R) → (x * (y * z)) ≡ ((x * y) * z)
  assoc* = elimProp3 (λ x y z → squash/ ((x * (y * z))) (((x * y) * z)))
                     (λ x y z → eq/ _ _ (assoc x y z))
  
  rid* : (x : Tree A / R) → (x * [ ε ]) ≡ x
  rid* = elimProp (λ x → squash/ (x * [ ε ]) x)
                  (λ x → eq/ _ _ (rid x))
  
  comm* : (x y : Tree A / R) → (x * y) ≡ (y * x)
  comm* = elimProp2 (λ x y → squash/ _ _)
                  (λ x y → eq/ _ _ (comm x y))
  
TreeCommMonoid : (A : Type ℓ) → CommMonoid _
TreeCommMonoid {_} A = makeCommMonoid [ ε {_} {A} ] _*_ squash/ assoc* rid* comm*
