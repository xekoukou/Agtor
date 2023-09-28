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
import Cubical.Data.Maybe
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

import OpTerm

module Convolution2 {ℓ}  (Msg : Type ℓ) where

open import BSet2 Msg
open import SType2 Msg

-- I believe we need to postulate Secret, and not be the empty type.
-- Empty types are unique???? and we dont want that.
data Secret : Type where

postulate
  HasSecret : Secret → BSet
  decSecr : ∀ msg → Dec (Σ Secret λ secr → (HasSecret secr msg))

VSecret : ∀ k → Type
VSecret k = Vec Secret k

data _∈_ (s : Secret) : ∀{k} → VSecret k → Type where
  here : ∀{k} → {vals : VSecret k} → s ∈ (s ∷ vals) 
  there : ∀{w k} → ∀{vals : VSecret k} → s ∈ vals → s ∈ (w ∷ vals)

data Diff∈ {x y} : ∀{k} → {vsecr : VSecret k} → x ∈ vsecr → y ∈ vsecr → Type where
  ht : ∀{k} → {vs : VSecret k} → ∀{b} → Diff∈ {vsecr = (x ∷ vs)} here (there b)
  th : ∀{k} → {vs : VSecret k} → ∀{b} → Diff∈ {vsecr = (y ∷ vs)} (there b) here
  tt : ∀{w k} → {vs : VSecret k} → ∀{a b} → Diff∈ {x} {y} {_} {vs} a b → Diff∈ {vsecr = (w ∷ vs)} (there a) (there b)

DiffProof : ∀{k} → VSecret k → Type
DiffProof lsecr = ∀{x y : Secret} → (xin : x ∈ lsecr) → (yin : y ∈ lsecr) → Diff∈ xin yin → ¬ (x ≡ y)  

SDom : ∀{ℓ k} → (VSecret k → Type ℓ) → Type ℓ
SDom {k = k} Dom = Σ (VSecret k) (λ lsecr → DiffProof lsecr × Dom lsecr)

record Open {ℓ} (A : Type (ℓ-suc ℓ)) : Type (ℓ-suc ℓ) where
  field
    {dim} : ℕ
    Dom : VSecret dim → Type ℓ   
    fun : SDom Dom → A

open Open

record BType : Type (ℓ-suc ℓ) where
  constructor _ᵐ,_ᵃ
  field
    _ₘ : BSet
    _ₐ : BSet

open BType

_∋ᵇ_ : (input : BType) → (msg : Msg) → Type ℓ
input ∋ᵇ msg = (input ₘ) msg ⊎ (input ₐ) msg

_toBType : SType → BType
st toBType = (projₘ st) ᵐ, (projₐ st) ᵃ

record Actor : Type (ℓ-suc ℓ)

module MActorM = Cubical.Data.Maybe

open MActorM renaming (just to !_ ; nothing to ∅)

MActor = Maybe Actor

record Actor where
  coinductive
  field
    ST : SType
    δᶜT : (msg : Msg) → MActor
    cond1 : (msg : Msg) → ((ST toBType) ∋ᵇ msg × Σ Actor λ a → δᶜT msg ≡ ! a) ⊎ (¬ ((ST toBType) ∋ᵇ msg) × (δᶜT msg ≡ ∅))
    δT : Open Actor

open Actor


-- -- Since δᵀc does not depend on the predicate, this should simplify considerably.
-- _∣ₐ_ : Actor → Actor → Actor
-- ST (a ∣ₐ b) = ST a ∣ ST b
-- decₐ (a ∣ₐ b) msg with decₐ a msg | decₐ b msg
-- ... | yes p | w = yes (inl p)
-- ... | no ¬p | yes p = yes (inr p)
-- ... | no ¬p | no ¬p₁ = no (λ { (inl x) → ¬p x
--                              ; (inr x) → ¬p₁ x})
-- decₘ (a ∣ₐ b) msg with decₘ a msg | decₘ b msg
-- ... | yes p | w = yes (inl p)
-- ... | no ¬p | yes p = yes (inr p)
-- ... | no ¬p | no ¬p₁ = no (λ { (inl x) → ¬p x
--                              ; (inr x) → ¬p₁ x})
-- δᶜT (a ∣ₐ b) msg (inl (inl x)) with decₘ b msg
-- ... | yes p = δᶜT a msg (inl x) ∣ₐ δᶜT b msg (inl p)
-- ... | no ¬p = δᶜT a msg (inl x)
-- δᶜT (a ∣ₐ b) msg (inl (inr x)) with decₘ a msg
-- ... | yes p = δᶜT a msg (inl p) ∣ₐ δᶜT b msg (inl x)
-- ... | no ¬p = δᶜT b msg (inl x)
-- δᶜT (a ∣ₐ b) msg (inr (inl x)) with decₐ b msg
-- ... | yes p = δᶜT a msg (inr x) ∣ₐ δᶜT b msg (inr p)
-- ... | no ¬p = δᶜT a msg (inr x)
-- δᶜT (a ∣ₐ b) msg (inr (inr x)) with decₐ a msg
-- ... | yes p = δᶜT a msg (inr p) ∣ₐ δᶜT b msg (inr x)
-- ... | no ¬p = δᶜT b msg (inr x)
-- dim (δT (a ∣ₐ b)) = dim (δT a) + dim (δT b)
-- Dom (δT (a ∣ₐ b)) = λ vsecr → let (s1 , s2) = split+ {_} {dim (δT a)} {dim (δT b)} vsecr in Dom (δT a) s1 × Dom (δT b) s2
-- fun (δT (a ∣ₐ b)) (vsecr , dp , v1 , v2) = let (s1 , s2) = split+ {_} {dim (δT a)} {dim (δT b)} vsecr
--                                            in (fun (δT a)) (s1 , {!!} , v1) ∣ₐ (fun (δT b)) (s2 , {!!} , v2)

-- _&ₐ_ : Actor → Actor → Actor
-- ST (a &ₐ b) = ST a & ST b
-- decₐ (a &ₐ b) msg with decₐ a msg | decₐ b msg
-- ... | yes p | w = yes (inl p)
-- ... | no ¬p | yes p = yes (inr p)
-- ... | no ¬p | no ¬p₁ = no (λ { (inl x) → ¬p x
--                              ; (inr x) → ¬p₁ x})
-- decₘ (a &ₐ b) msg with decₘ a msg | decₘ b msg
-- ... | yes p | w = yes (inl p)
-- ... | no ¬p | yes p = yes (inr p)
-- ... | no ¬p | no ¬p₁ = no (λ { (inl x) → ¬p x
--                              ; (inr x) → ¬p₁ x})
-- δᶜT (a &ₐ b) = {!!}
-- δT (a &ₐ b) = {!!}
