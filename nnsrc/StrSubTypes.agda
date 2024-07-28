{-# OPTIONS --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒)


module StrSubTypes (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) where

open PropositionalTruncation pt
open import BSet2 Msg
open import SType fe pt Msg


_ᵀ : PSet → PSet
∣⟨ A ᵀ ⟩ o = ∥ (∀ x → (p : ∣⟨ A ⟩ x) → Σ y ꞉ 𝟚 × BSet , &⟨ x ⟩ y × &⟨ o ⟩ (y ᵗ)) ∥
∣-is-prop (A ᵀ) o = ∥∥-is-prop

-- P ᵀ seems to be the set with the most relaxed restrictions under which the set P reduces.
-- if we add (&) more we will always reduce. If we add one (|) more, it doesn't always reduce.

-- There might be other Q sets which have the same property.


