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

module BSet (fe : funext 𝓤 𝓤) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt


-- A property on messages
record BSet : 𝓤 ⁺ ̇  where
 field
  ⟨_⟩ : (mp : Msg) → 𝓤 ̇ 
  -is-prop : ∀ mp → is-prop (⟨_⟩ mp)
  -is-decidable : ∀ mp → is-decidable (⟨_⟩ mp)

open BSet

-- The property holds for all messages.
⊨ : BSet → 𝓤 ̇
⊨ P = ∀ a → ⟨ P ⟩ a 

⊥B : BSet
⟨ ⊥B ⟩ mp = 𝟘
⊥B .-is-prop mp = 𝟘-is-prop
⊥B .-is-decidable mp = inr unique-from-𝟘

⊤B : BSet
⟨ ⊤B ⟩ mp = 𝟙
⊤B .-is-prop mp = 𝟙-is-prop
⊤B .-is-decidable mp = inl ⋆

_─→_ : BSet → BSet → BSet
⟨ P ─→ Q ⟩ mp = ⟨ P ⟩ mp → ⟨ Q ⟩ mp
(P ─→ Q) .-is-prop mp = Π-is-prop fe (λ _ → (Q .-is-prop) mp)
(P ─→ Q) .-is-decidable mp with Q .-is-decidable mp
... | inl q = inl λ _ → q
... | inr q with P .-is-decidable mp
... | inl p = inr λ x → q (x p)
... | inr p = inl (λ x → 𝟘-elim (p x))

_&&_ : BSet → BSet → BSet
⟨ a && b ⟩ mp = ⟨ a ⟩ mp × ⟨ b ⟩  mp
((a && b) .-is-prop) mp = Σ-is-prop ((a .-is-prop) mp) (λ _ → ((b .-is-prop) mp))
(a && b) .-is-decidable mp with a .-is-decidable mp | b .-is-decidable mp
... | inr x | q = inr λ (w , e) → x w
... | inl x | inl y = inl (x , y)
... | inl x | inr y = inr λ (w , e) → y e

_≡ᵇ_ : BSet → BSet → 𝓤 ̇
A ≡ᵇ B = ⊨ ((A ─→ B) && (B ─→ A))

_||_ : BSet → BSet → BSet
⟨ a || b ⟩ mp = ∥ ⟨ a ⟩ mp + ⟨ b ⟩ mp ∥
(a || b) .-is-prop mp = ∥∥-is-prop
(a || b) .-is-decidable mp with a .-is-decidable mp | b .-is-decidable mp
... | inl x | q = inl ∣ inl x ∣
... | inr x | inl y = inl ∣ inr y ∣
... | inr x | inr y = inr (∥∥-rec 𝟘-is-prop (λ { (inl z) → x z
                                               ; (inr z) → y z}))

-- ¬B : BSet → BSet
-- ¬B a mp = ¬ (a mp)

-- -- I do not like this definition, because we need to prove the negation
-- -- 
-- _─_ : BSet → BSet → BSet
-- (a ─ b) = a && (¬B b)
