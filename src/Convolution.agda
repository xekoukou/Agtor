{-# OPTIONS --cubical --guardedness #-}

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
import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Semilattice
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to ⟨_⟩ₛ)
import OpTerm

module Convolution {ℓ} (MsgP : ℕ → Type ℓ) (mpsuc : ∀{k} → MsgP k → MsgP (suc k)) where

open import BSet MsgP mpsuc

record Input (k : ℕ) : Type (ℓ-suc ℓ) where
  constructor _ᵐ,_ᵃ
  field
    _ᵐ : BSet k
    _ᵃ : BSet k

open Input

_⊎ⁱ_ : ∀{k} → Input k → Input k → Input k
a ⊎ⁱ b = ((a ᵐ) || (b ᵐ)) ᵐ, (a ᵃ) || (b ᵃ) ᵃ 

_≡ⁱ_ : ∀{k} → Input k → Input k → Type ℓ
(mq ᵐ, aq ᵃ) ≡ⁱ (mw ᵐ, aw ᵃ) = (mq ≡ᵇ mw) × (aq ≡ᵇ aw)


-- -- If we add continuations here, maybe we could describe the system in all communication steps.
-- -- we can possibly describe the reduction of separate systems, and then through transformations of the behavioral types
-- -- and their continuations, derive the reduction of the general system from the reductions of the specific system.

_∋ⁱ_ : ∀{k} → (input : Input k) → (msg : MsgP k) → Type ℓ
input ∋ⁱ msg = ∥ (input ᵐ) msg ∥₁ ⊎ ∥ (input ᵃ) msg ∥₁

_⊆ⁱ_ : ∀{k} → (typ1 typ2 : Input k) → Type ℓ
typ1 ⊆ⁱ typ2 = ∀ p → typ1 ∋ⁱ p → typ2 ∋ⁱ p

module dsfd (SType : ℕ → Type ℓ) (_toI : ∀{k} → SType k → Input k) (_⊑_ : ∀{k} → SType k → SType k → Type (ℓ-suc ℓ)) where

  record CType (k : ℕ) : Type ℓ
   
  open OpTerm 
  
  record CType k where
    coinductive
    field
    -- here we need to generalize FFSTate to have FSType so as to be able to add those types with _&_
    -- so as to use it at δT
      PST : SType k
      δᶜT : (msg : MsgP k) → (cnd : (PST toI) ∋ⁱ msg) → CType k
      -- Here we should't just have CType, because when we add two functions, then we have a parameter t, which
      -- we do not care about, but we have it , thus look at the above.
      δT  : CType k
  
  

  open CType

  module _ (_&_ : ∀{k} → SType k → SType k → SType k) (_∣_ : ∀{k} → SType k → SType k → SType k) (l1 : ∀{k} → (x y : SType k) → ((x ∣ y) toI) ≡ ((x toI) ⊎ⁱ (y toI))) where

-- Wrong since we need to concatenate same conditions ????
    _ee_ : ∀{k} → CType k → CType k → CType k
    PST (x ee y) = PST x ∣ PST y
    δᶜT (x ee y) = {!!}
    δT (x ee y) = {!!}
    
    _ww_ : ∀{k} → CType k → CType k → CType k
    PST (_ww_ x y) = PST x & PST y
    δᶜT (_ww_ x y) = {!!}
    δT (_ww_ x y) = ((δT x ww y) ee (x ww δT y)) ee {!!} 


    _⅋_ : ∀{k} → CType k ᵖ ℓ → CType k ᵖ ℓ → CType k ᵖ ℓ
    (Pa ⅋ Pb) x = Σ (Σ (CType _) Pa) (λ a → Σ (Σ (CType _) Pb) {!x ≡ a!})




-- -- -- global types have subtypes in which the behavioral types are equal, but the
-- -- -- structural type is a subtype, thus we have directional abstraction, inherited from the
-- -- -- structural type.
-- --   record _⊑ᵍ_ {k} (gt1 gt2 : GType k) : Type (ℓ-suc ℓ) where
-- --     coinductive
-- --     open GType
-- --     field
-- --       beq : btyp gt1 ≡ᵇᵗ btyp gt2
-- --       srel : styp gt1 ⊑ styp gt2
-- --       -- both conditions are the same, simplify this.
-- --       δᶜT : (msg : MsgP k) → (cnd1 : msg ∈ᵐᵇᵗ (btyp gt1)) → (cnd2 : msg ∈ᵐᵇᵗ (btyp gt2))
-- --             → (δᶜT gt1) msg cnd1 ⊑ᵍ δᶜT gt2 msg cnd2
-- --       δTl : δT gt1 ⊑ᵍ gt2
-- --       δTr : gt1 ⊑ᵍ δT gt2

