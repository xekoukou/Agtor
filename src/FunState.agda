{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
import State

module FunState {ℓ ℓ'} (C : ∀ n → Type ℓ) where

module St = State C
open St

record FunRel {n : ℕ} (f g : Σ (Type ℓ') (λ A → A → State n)) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
   srj : fst f → fst g
   isSurj : ∀ y → Σ (fst f) (λ x → srj x ≡ y)
   eqIm : ∀ x →  (snd f) x ≡ (snd g) (srj x)


open FunRel

FunState : ℕ → Type (ℓ-max ℓ (ℓ-suc ℓ'))
FunState n = (Σ (Type ℓ') (λ A → A → State n)) / FunRel


data FunDomain {n : ℕ} : FunState n → Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  q : {f : (Σ (Type ℓ') (λ A → A → State n))} → fst f → FunDomain [ f ]
  e : ∀{f g} → (rel : FunRel f g) → (x : fst f) → (y : fst g) → (srj rel) x ≡ y → PathP (λ i → FunDomain (eq/ f g rel i)) (q x) (q y)
  sq : ∀{ x y : FunState n} → (p1 p2 : x ≡ y) → (dx : FunDomain x) → (dy : FunDomain y)
       → (dp1 : PathP (λ i → FunDomain (p1 i)) dx dy)
       → (dp2 : PathP (λ i → FunDomain (p2 i)) dx dy) → SquareP (λ i j → FunDomain (squash/ x y p1 p2 i j)) dp1 dp2 refl refl

_$_ : {n : ℕ} → (os : FunState n) → FunDomain os → State n
[ a ] $ fd = {!!}
eq/ a b r i $ fd = {!!}
squash/ os os₁ p q₁ i i₁ $ fd = {!!}
-- .([ _ ]) $ q {f} x = (snd f) x
-- .(eq/ _ _ rel i) $ e {_} {g} rel x y x₁ i = (eqIm rel x ∙ cong (snd g) x₁) i
-- -- .(squash/ _ _ p1 p2 i j) $ sq {x} {y} p1 p2 dx dy dp1 dp2 i j = squash (x $ dx) (y $ dy) (cong₂ _$_ p1 dp1) (cong₂ _$_ p2 dp2) i j
