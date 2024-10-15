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
open import UF.Sets
open import UF.Base

open import Lists
open import Maybe

module &PSet (GSet : 𝓥 ̇ ) (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

-- Move this to the more specialized case where GSet is 𝟚 × BSet
-- _ᵗ : 𝟚 × BSet → 𝟚 × BSet
-- (𝕞 , x) ᵗ = 𝕒 , x
-- (𝕒 , x) ᵗ = 𝕞 , x

record &PSet 𝓦 : 𝓥 ⊔ 𝓦 ⁺ ̇  where
 field
  &⟨_⟩ : (o : GSet) → 𝓦 ̇ 
  &-is-prop : ∀ o → is-prop (&⟨_⟩ o)

open &PSet public

_&-&ᵖ_ : &PSet 𝓦 → &PSet 𝓦 → &PSet 𝓦
&⟨ A &-&ᵖ B ⟩ o = ∥ &⟨ A ⟩ o + &⟨ B ⟩ o ∥
&-is-prop (A &-&ᵖ B) o = ∥∥-is-prop
