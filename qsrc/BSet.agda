{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.PropTrunc

module BSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (A : 𝓤 ̇) where
open PropositionalTruncation pt

open import PredP A

Pred-is-prop-valued : ∀ {𝓥} → Pred 𝓥 → 𝓤 ⊔ 𝓥 ̇
Pred-is-prop-valued Pr = (∀ x → is-prop (Pr x))

BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
BSet 𝓥 = ΣPred 𝓥 Pred-is-prop-valued

module _ {𝓥} (bs : BSet 𝓥) where
 private module B = ΣPred bs

 bset-is-prop : (∀ x → is-prop (B.type x))
 bset-is-prop = B.prop

-- The property holds for all messages.
 ⊨ : 𝓤 ⊔ 𝓥 ̇
 ⊨ = ∀ a → B.type a 


module BSet₂ {𝓥} (a b : BSet 𝓥) where
 private module A = ΣPred a
 private module B = ΣPred b

 open Pred₂ renaming (_&&_ to _&&ₚ_ ; _||_ to _||ₚ_)

-- Consider propositional Extensionality, thus any propositions that
-- assume its other are equal. Thus externally when we accept the same messages
-- the predicates are equal.

 _≃_ : 𝓤 ⊔ 𝓥 ⁺ ̇
 _≃_ = a ＝ b

 _&&_ : BSet 𝓥
 _&&_  = (λ x → (A.type &&ₚ B.type) x) , λ x → Σ-is-prop ((bset-is-prop a) x) (λ _ → ((bset-is-prop b) x))
 
 _||_ : BSet 𝓥
 _||_ .pr₁ x = ∥ (A.type ||ₚ B.type) x ∥
 _||_ .pr₂ x = ∥∥-is-prop



-- ¬ᵇ : BSet 𝓥 → BSet 𝓥
-- ¬ᵇ bs = (λ x → ¬ (⟨ bs ⟩ x)) , (λ x → Π-is-prop fe λ _ → 𝟘-is-prop)



-- Varᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
-- Varᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇  , (D → BSet 𝓥)

-- Var→BSet : Varᵇ 𝓦 𝓥 → BSet (𝓦 ⊔ 𝓥)
-- Var→BSet (D , f) = (λ y → ∥ (Σ x ꞉ D , ⟨ f x ⟩ y) ∥) , (λ x → ∥∥-is-prop)

-- -- Without prop or truncation, it is used in _&ᶠ_ to introduce the variance that
-- -- was introduced when sending the msg whose contents we do not know.
-- Varᵇ→Set : Varᵇ 𝓦 𝓥 → A → 𝓦 ⊔ 𝓥 ̇
-- Varᵇ→Set (D , f) y = (Σ x ꞉ D , ⟨ f x ⟩ y)


-- DVarᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
-- DVarᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇   , (D → BSet 𝓥 × BSet 𝓥)

-- -- Redundant
-- DVar→BSet : DVarᵇ 𝓦 𝓥 → BSet (𝓦 ⊔ 𝓥) × BSet (𝓦 ⊔ 𝓥) 
-- DVar→BSet (D , f) = Var→BSet (D , pr₁ ∘ f) , Var→BSet (D , pr₂ ∘ f)

-- DVarᵇ→Set : DVarᵇ 𝓦 𝓥 → A → 𝓦 ⊔ 𝓥 ̇
-- DVarᵇ→Set (D , f) x = Varᵇ→Set (D , pr₁ ∘ f) x × Varᵇ→Set (D , pr₂ ∘ f) x
