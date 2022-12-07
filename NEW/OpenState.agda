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

module OpenState {ℓ ℓ'} (C : ∀{n} → Vec ℕ n → Type ℓ) where

module St = State C
open St

record RelOS (f g : Σ (Type ℓ') (λ A → A → State)) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
   e : fst f → fst g
   sr : ∀ y → Σ (fst f) (λ x → e x ≡ y)
   re : ∀ x →  (snd f) x ≡ (snd g) (e x)




OpenState : Type (ℓ-max ℓ (ℓ-suc ℓ'))
OpenState = (Σ (Type ℓ') (λ A → A → State)) / RelOS


data OpenDomain : OpenState → Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  q : {f : (Σ (Type ℓ') (λ A → A → State))} → fst f → OpenDomain [ f ]
  e : ∀{f g} → (rel : RelOS f g) → (x : fst f) → (y : fst g) → (RelOS.e rel) x ≡ y → PathP (λ i → OpenDomain (eq/ f g rel i)) (q x) (q y)
  sq : ∀{ x y : OpenState} → (p1 p2 : x ≡ y) → (dx : OpenDomain x) → (dy : OpenDomain y)
       → (dp1 : PathP (λ i → OpenDomain (p1 i)) dx dy)
       → (dp2 : PathP (λ i → OpenDomain (p2 i)) dx dy) → SquareP (λ i j → OpenDomain (squash/ x y p1 p2 i j)) dp1 dp2 refl refl

_$_ : (os : OpenState) → OpenDomain os → State
.([ _ ]) $ q {f} x = (snd f) x
.(eq/ _ _ rel i) $ e {_} {g} rel x y x₁ i = (RelOS.re rel x ∙ cong (snd g) x₁) i
.(squash/ _ _ p1 p2 i j) $ sq {x} {y} p1 p2 dx dy dp1 dp2 i j = squash (x $ dx) (y $ dy) (cong₂ _$_ p1 dp1) (cong₂ _$_ p2 dp2) i j
