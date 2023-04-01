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
import State
open import State.Lemma
import State.Properties
import ActorM
open import Projection
open import Common

module BSet {ℓ} where

postulate
  MsgP : ℕ → Type ℓ

-- A property on messages
BSet : (k : ℕ) → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
BSet k = (mp : MsgP k) → Type

-- The property holds for all messages.
⊨ : ∀{k} → BSet k → Set ℓ
⊨ P = ∀ a → P a 

⊥B : ∀{k} → BSet k
⊥B mp = ⊥

_↦_ : ∀{k} → BSet k → BSet k → BSet k
(P ↦ Q) mp = P mp → Q mp

_&&_ : ∀{k} → BSet k → BSet k → BSet k
(a && b) mp = a mp × b mp

_||_ : ∀{k} → BSet k → BSet k → BSet k
(a || b) mp = a mp ⊎ b mp


¬B : ∀{k} → BSet k → BSet k
¬B a mp = ¬ (a mp)

-- I do not like this definition, because we need to prove the negation
-- 
_─_ : ∀{k} → BSet k → BSet k → BSet k
(a ─ b) = a && (¬B b)


postulate 
  Bsucₚ : ∀{k} → BSet (suc k) → BSet k
  Bpredₚ : ∀{k} → BSet k → BSet (suc k)

-- Bsucₚ a mp = a (StM.sucₚ mp 0)
-- Bpredₚ {k} a ([ secr ] def) = Σ (Vec (Fin k) _) (λ scr → secr ≡ lsuc<?Fin scr 0 → a (StM.[ scr ] def))

