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
open import BSet

module BTypes {ℓ} where

-- Behavioral types describe the msgs that can be received and sent at a specific state.
-- it is the external behavior of a system and thus should be the target of abstraction.
-- Two systems should be considered equal if they have the same BTypes.
data BType (k : ℕ) : Type (ℓ-suc ℓ) where
  _ᵐ : BSet {ℓ} k → BType k
  _ᵃ : BSet {ℓ} k → BType k
  -- If we have two superpositions that have a common sets of msgs, then we can split them,  like this.
  -- (l1 ∪ e) ∣ (l2 ∪ e) ----> (l1 ∣ l2) & e
  _∣_ : (l r : BType k) → BType k
  -- Here _&_ can be merged if there is no _|_ , aka superposition.
  _&_ : (l r : BType k) → BType k

-- If we add continuations here, maybe we could describe the system in all communication steps.
-- we can possibly describe the reduction of separate systems, and then through transformations of the behavioral types
-- and their continuations, derive the reduction of the general system from the reductions of the specific system.
