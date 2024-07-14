{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Core.Id hiding (_≡_)
open import Cubical.Data.Sigma
open import Cubical.Data.Vec as V
import Cubical.Data.List as L
open import Cubical.Data.Maybe
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.List
import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Projection

module Test where

data FF : Set where
  A : FF
  _U_ : FF → FF → FF
  idem : ∀{a} → a U a ≡ a

data GG : FF → Set where
  V : GG A
  _U_ : ∀{a b} → GG a → GG b → GG (a U b)
  videm : ∀{a} → (v : GG a) → PathP (λ z → GG (idem {a} z)) (v U v) v  


f : ∀{C : Set} → ∀ a → GG a → C
f .A V = {!!}
f .(_ U _) (x U x₁) = {!!}
f .(idem z) (videm x z) = {!!}
