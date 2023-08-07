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
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)

module BSet {ℓ} (MsgP : ℕ → Type ℓ) (mpsuc : ∀{k} → MsgP k → MsgP (suc k)) where



-- A property on messages
BSet : (k : ℕ) → Type (ℓ-suc ℓ)
BSet k = (mp : MsgP k) → Type ℓ

-- The property holds for all messages.
⊨ : ∀{k} → BSet k → Type ℓ
⊨ P = ∀ a → P a 

⊥B : ∀{k} → BSet k
⊥B mp = ⊥*

⊤B : ∀{k} → BSet k
⊤B mp = Unit*

_↦_ : ∀{k} → BSet k → BSet k → BSet k
(P ↦ Q) mp = P mp → Q mp

_&&_ : ∀{k} → BSet k → BSet k → BSet k
(a && b) mp = a mp × b mp

_≡ᵇ_ : ∀{k} → BSet k → BSet k → Type ℓ
A ≡ᵇ B = ⊨ ((A ↦ B) && (B ↦ A))

_||_ : ∀{k} → BSet k → BSet k → BSet k
(a || b) mp = a mp ⊎ b mp


¬B : ∀{k} → BSet k → BSet k
¬B a mp = ¬ (a mp)

-- I do not like this definition, because we need to prove the negation
-- 
_─_ : ∀{k} → BSet k → BSet k → BSet k
(a ─ b) = a && (¬B b)

Bsucₚ : ∀{k} → BSet (suc k) → BSet k
Bsucₚ a mp = a (mpsuc mp)

Bpredₚ : ∀{k} → BSet k → BSet (suc k)
Bpredₚ {k} a mp = Σ (MsgP k) λ pmp → Σ (mpsuc pmp ≡ mp) λ _ → a pmp


