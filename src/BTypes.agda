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

data Pos (k : ℕ) : Type (ℓ-suc ℓ) where
  _ᵐ,_ᵃ : BSet k → BSet k → Pos k

_≡ᵖ_ : ∀{k} → Pos k → Pos k → Type ℓ
(mq ᵐ, aq ᵃ) ≡ᵖ (mw ᵐ, aw ᵃ) = (mq ≡ᵇ mw) × (aq ≡ᵇ aw)


-- Behavioral types describe the msgs that can be received and sent at a specific state.
-- it is the external behavior of a system and thus should be the target of abstraction.
-- Two systems should be considered equal if they have the same BTypes.
-- (They also need to be reducible, thus they must respect a subtype property/contract.)
BType : (k : ℕ) → Type (ℓ-suc ℓ)
BType k = List (Pos k)

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
    sup : (MBSet ᵐ, ABSet ᵃ) ∈ btyp

record _∈ᵇᵗ_ {k} (p : Pos k) (btyp : BType k) : Type (ℓ-suc ℓ) where
  field
    p` : Pos k
    -- We treat btypes that accept the same messages as the same.
    eqp : p ≡ᵖ p`
    sup : p` ∈ btyp

_⊆ᵇᵗ_ : ∀{k} → (btyp1 btyp2 : BType k) → Type (ℓ-suc ℓ)
btyp1 ⊆ᵇᵗ btyp2 = ∀ p → p ∈ᵇᵗ btyp1 → p ∈ᵇᵗ btyp2

_≡ᵇᵗ_ : ∀{k} → (btyp1 btyp2 : BType k) → Type (ℓ-suc ℓ)
btyp1 ≡ᵇᵗ btyp2 = (btyp1 ⊆ᵇᵗ btyp2) × (btyp2 ⊆ᵇᵗ btyp1)

module dsfd (SType : ℕ → Type ℓ) (_⊑_ : ∀{k} → SType k → SType k → Type (ℓ-suc ℓ)) where

  record GType k : Type (ℓ-suc ℓ) where
    constructor gtype
    coinductive
    field
      btyp : BType k
      styp : SType k
      δᶜT : (msg : MsgP k) → (cnd : msg ∈ᵐᵇᵗ btyp) → GType k
      -- here in the absence of new reduction, we simply return the same type. Instead, we should check the SType
      -- only when reduction is guaranteed, should we return a δT
      δT  : GType k

-- global types have subtypes in which the behavioral types are equal, but the
-- structural type is a subtype, thus we have directional abstraction, inherited from the
-- structural type.
  record _⊑ᵍ_ {k} (gt1 gt2 : GType k) : Type (ℓ-suc ℓ) where
    coinductive
    open GType
    field
      beq : btyp gt1 ≡ᵇᵗ btyp gt2
      srel : styp gt1 ⊑ styp gt2
      -- both conditions are the same, simplify this.
      δᶜT : (msg : MsgP k) → (cnd1 : msg ∈ᵐᵇᵗ (btyp gt1)) → (cnd2 : msg ∈ᵐᵇᵗ (btyp gt2))
            → (δᶜT gt1) msg cnd1 ⊑ᵍ δᶜT gt2 msg cnd2
      δTl : δT gt1 ⊑ᵍ gt2
      δTr : gt1 ⊑ᵍ δT gt2

