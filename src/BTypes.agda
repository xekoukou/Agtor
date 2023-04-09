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

module BTypes {ℓ} (MsgP : ℕ → Type ℓ) (mpsuc : ∀{k} → MsgP k → MsgP (suc k)) where

open import BSet MsgP mpsuc

Pos : ℕ → Type (ℓ-suc ℓ)
Pos k = BSet k × BSet k

-- Behavioral types describe the msgs that can be received and sent at a specific state.
-- it is the external behavior of a system and thus should be the target of abstraction.
-- Two systems should be considered equal if they have the same BTypes.
-- (They also need to be reducible, thus they must respect a subtype property/contract.)
BType : (k : ℕ) → Type (ℓ-suc ℓ)
BType k = List (BSet k × BSet k)

--  _ᵐ,_ᵃ : BSet k → BSet k → BType k
--  --_∣_ inducates the superposition due to the different states a system can be in.
--  _∣_ : (l r : BType k) → BType k

-- -- If we add continuations here, maybe we could describe the system in all communication steps.
-- -- we can possibly describe the reduction of separate systems, and then through transformations of the behavioral types
-- -- and their continuations, derive the reduction of the general system from the reductions of the specific system.


-- The superposition here matters.
record _∈ᵐᵇᵗ_ {k} (msg : MsgP k) (btyp : BType k) : Type (ℓ-suc ℓ) where
  field
    {MBSet ABSet} : BSet k
    mP : MBSet msg ⊎ ABSet msg
    sup : (MBSet , ABSet) ∈ btyp

record _∈ᵇᵗ_ {k} (p : Pos k) (btyp : BType k) : Type (ℓ-suc ℓ) where
  field
    {MBSet ABSet} : BSet k
    meq : fst p ≡ᵇ MBSet
    aeq : snd p ≡ᵇ ABSet
    sup : (MBSet , ABSet) ∈ btyp

_⊆ᵇᵗ_ : ∀{k} → (btyp1 btyp2 : BType k) → Type (ℓ-suc ℓ)
btyp1 ⊆ᵇᵗ btyp2 = ∀ p → p ∈ᵇᵗ btyp1 → p ∈ᵇᵗ btyp2

_≡ᵇᵗ_ : ∀{k} → (btyp1 btyp2 : BType k) → Type (ℓ-suc ℓ)
btyp1 ≡ᵇᵗ btyp2 = (btyp1 ⊆ᵇᵗ btyp2) × (btyp2 ⊆ᵇᵗ btyp1)

module dsfd (A : ℕ → Type ℓ) (_⊑_ : ∀{k} → A k → A k → Type (ℓ-suc ℓ)) (pr : ∀{k} → A k → BType k) where

  record GType {k} (btyp : BType k) : Type (ℓ-suc ℓ) where
    coinductive
    field
      stᶜT : (msg : MsgP k) → msg ∈ᵐᵇᵗ btyp → A k -- this should be without any cuts.
      δᶜT : (msg : MsgP k) → (cnd : msg ∈ᵐᵇᵗ btyp) → GType (pr (stᶜT msg cnd))
      stT : A k 
      δT  : GType (pr stT)

-- global types have subtypes in which the behavioral types are equal, but the
-- structural type is a subtype, thus we have directional abstraction, inherited from the
-- structural type.
  data _⊑ᵍ_ : ∀{k} → ∀{btyp1 btyp2 : BType k} → GType btyp1 → GType btyp2 → Type {!!} where
