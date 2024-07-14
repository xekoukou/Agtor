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

module BSet (fe : Fun-Ext) (Msg : 𝓤 ̇) where

-- A property on messages
-- TODO Should the predicates have the same universe with the message ?
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

_⟶_ : BSet → BSet → BSet
⟨ P ⟶ Q ⟩ mp = ⟨ P ⟩ mp → ⟨ Q ⟩ mp
(P ⟶ Q) .-is-prop mp = Π-is-prop fe (λ _ → (Q .-is-prop) mp)
(P ⟶ Q) .-is-decidable mp with Q .-is-decidable mp
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
A ≡ᵇ B = ⊨ ((A ⟶ B) && (B ⟶ A))

¬ᵇ : BSet → BSet
⟨ ¬ᵇ A ⟩ mp = ¬ (⟨ A ⟩ mp)
-is-prop (¬ᵇ A) mp = Π-is-prop fe λ _ → 𝟘-is-prop
-is-decidable (¬ᵇ A) mp with -is-decidable A mp
... | inl x = inr (λ ¬f → ¬f x)
... | inr x = inl x

-- I do not like this definition, because we need to prove the negation
--  update : But since we have decidability anyway, this is provable immediately
_─_ : BSet → BSet → BSet
(a ─ b) = a && (¬ᵇ b)

_|x|_ : BSet → BSet → BSet
⟨ a |x| b ⟩ mp = ⟨ ¬ᵇ (a && b) ⟩ mp × (⟨ a ⟩ mp + ⟨ b ⟩ mp)
-is-prop (a |x| b) mp
 = Σ-is-prop
    (¬ᵇ (a && b) .-is-prop mp)
    (λ ¬pa&b → +-is-prop (a .-is-prop mp)
    (b .-is-prop mp)
    λ pa pb → ¬pa&b (pa , pb))
-is-decidable (a |x| b) mp with a .-is-decidable mp | b .-is-decidable mp
... | inl x | inl y = inr (λ (z , _) → z (x , y))
... | inl x | inr y = inl ((λ (_ , e) → y e) , inl x)
... | inr x | inl y = inl ((λ (e , _) → x e) , inr y)
... | inr x | inr y = inr λ { (_ , inl z) → x z ; (_ , inr z) → y z}

-- I use this definition because of the proof of is-prop
_||_ : BSet → BSet → BSet
a || b = (a && b) |x| (a |x| b)



-- -- We do not use this because we have decidability of prop
-- _||_ : BSet → BSet → BSet
-- ⟨ a || b ⟩ mp = ∥ ⟨ a ⟩ mp + ⟨ b ⟩ mp ∥
-- (a || b) .-is-prop mp = ∥∥-is-prop
-- (a || b) .-is-decidable mp with a .-is-decidable mp | b .-is-decidable mp
-- ... | inl x | q = inl ∣ inl x ∣
-- ... | inr x | inl y = inl ∣ inr y ∣
-- ... | inr x | inr y = inr (∥∥-rec 𝟘-is-prop (λ { (inl z) → x z
--                                                ; (inr z) → y z}))

