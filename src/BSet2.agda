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

module BSet2 {ℓ} (MsP : Type ℓ) where



-- A property on messages
BSet : Type (ℓ-suc ℓ)
BSet = (mp : MsP) → Type ℓ

-- The property holds for all messages.
⊨ : BSet → Type ℓ
⊨ P = ∀ a → P a 

⊥B : BSet
⊥B mp = ⊥*

⊤B : BSet
⊤B mp = Unit*

_↦_ : BSet → BSet → BSet
(P ↦ Q) mp = P mp → Q mp

_&&_ : BSet → BSet → BSet
(a && b) mp = a mp × b mp

_≡ᵇ_ : BSet → BSet → Type ℓ
A ≡ᵇ B = ⊨ ((A ↦ B) && (B ↦ A))

_||_ : BSet → BSet → BSet
(a || b) mp = a mp ⊎ b mp


¬B : BSet → BSet
¬B a mp = ¬ (a mp)

-- I do not like this definition, because we need to prove the negation
-- 
_─_ : BSet → BSet → BSet
(a ─ b) = a && (¬B b)
