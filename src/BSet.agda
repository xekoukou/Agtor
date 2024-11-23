{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Base

module BSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt

-- A property on messages

BPred : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
BPred 𝓥 = ((mp : Msg) → 𝓥 ̇ )

BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
BSet 𝓥 = Σ P ꞉ BPred 𝓥 , (∀ mp → is-prop (P mp))

⟨_⟩ : BSet 𝓥 → (Msg → 𝓥 ̇)
⟨ bs ⟩ = bs .pr₁

bset-is-prop : (bs : BSet 𝓥) → (∀ mp → is-prop (⟨ bs ⟩ mp))
bset-is-prop bs = bs .pr₂

-- Consider propositional Extensionality, thus any propositions that
-- assume its other are equal. Thus externally when we accept the same messages
-- the predicates are equal.
_≃ᵇ_ : ∀{𝓥} → BSet 𝓥 → BSet 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
a ≃ᵇ b = a ＝ b

-- The property holds for all messages.
⊨ : BSet 𝓥 → 𝓤 ⊔ 𝓥 ̇
⊨ P = ∀ a → ⟨ P ⟩ a 

_&&ᵇ_ : BPred 𝓥 → BPred 𝓥 → BPred 𝓥
(a &&ᵇ b) mp = a mp × b mp

_&&_ : BSet 𝓥 → BSet 𝓥 → BSet 𝓥
a && b  = (λ mp → (⟨ a ⟩ &&ᵇ ⟨ b ⟩) mp) , λ mp → Σ-is-prop ((bset-is-prop a) mp) (λ _ → ((bset-is-prop b) mp))

¬ᵇ : BSet 𝓥 → BSet 𝓥
¬ᵇ bs = (λ mp → ¬ (⟨ bs ⟩ mp)) , (λ mp → Π-is-prop fe λ _ → 𝟘-is-prop)

_||ᵇ_ : BPred 𝓥 → BPred 𝓥 → BPred 𝓥
(a ||ᵇ b) mp = a mp + b mp

_||_ : BSet 𝓥 → BSet 𝓥 → BSet 𝓥
(a || b) .pr₁ mp = ∥ (⟨ a ⟩ ||ᵇ ⟨ b ⟩) mp ∥
(a || b) .pr₂ mp = ∥∥-is-prop

Varᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
Varᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇  , (D → BSet 𝓥)

Var→BSet : Varᵇ 𝓦 𝓥 → BSet (𝓦 ⊔ 𝓥)
Var→BSet (D , f) = (λ mp → ∥ (Σ x ꞉ D , ⟨ f x ⟩ mp) ∥) , (λ mp → ∥∥-is-prop)

-- Without prop or truncation, it is used in _&ᶠ_ to introduce the variance that
-- was introduced when sending the msg whose contents we do not know.
Varᵇ→Set : Varᵇ 𝓦 𝓥 → Msg → 𝓦 ⊔ 𝓥 ̇
Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ f x ⟩ mp)


DVarᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
DVarᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇   , (D → BSet 𝓥 × BSet 𝓥)

-- Redundant
DVar→BSet : DVarᵇ 𝓦 𝓥 → BSet (𝓦 ⊔ 𝓥) × BSet (𝓦 ⊔ 𝓥) 
DVar→BSet (D , f) = Var→BSet (D , pr₁ ∘ f) , Var→BSet (D , pr₂ ∘ f)

DVarᵇ→Set : DVarᵇ 𝓦 𝓥 → Msg → 𝓦 ⊔ 𝓥 ̇
DVarᵇ→Set (D , f) mp = Varᵇ→Set (D , pr₁ ∘ f) mp × Varᵇ→Set (D , pr₂ ∘ f) mp
