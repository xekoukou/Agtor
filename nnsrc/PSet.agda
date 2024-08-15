{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan hiding (𝟚)
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

module PSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇ ) (s-is-set : is-set Secret) (dc : (ascrs scrs : List Secret) → is-decidable (scrs ⊃ ascrs × ascrs ⊃ scrs)) where

open import MLTT.Two renaming (₀ to 𝕞 ; ₁ to 𝕒) public

open PropositionalTruncation pt
open import BSet fe pt Msg
open import SBSet fe pt Msg Secret s-is-set dc



_ᵗ : 𝟚 × S×BSet → 𝟚 × S×BSet
(𝕞 , x) ᵗ = 𝕒 , x
(𝕒 , x) ᵗ = 𝕞 , x

record &PSet : 𝓤 ⁺ ̇  where
 field
  &⟨_⟩ : (o : 𝟚 × S×BSet) → 𝓤 ̇ 
  &-is-prop : ∀ o → is-prop (&⟨_⟩ o)


-- This predicate describes all the possible superpositions of a system.
record PSet : 𝓤 ⁺⁺ ̇  where
 field
  ∣⟨_⟩ : (o : &PSet) → 𝓤 ⁺ ̇ 
  ∣-is-prop : ∀ o → is-prop (∣⟨_⟩ o)

open &PSet public
open PSet public


_&-&ᵖ_ : &PSet → &PSet → &PSet
&⟨ A &-&ᵖ B ⟩ o = ∥ &⟨ A ⟩ o + &⟨ B ⟩ o ∥
&-is-prop (A &-&ᵖ B) o = ∥∥-is-prop

_&ᵖ_ : PSet → PSet → PSet
∣⟨ A &ᵖ B ⟩ o = ∥ Σ &A ꞉ &PSet , Σ &B ꞉ &PSet , ∣⟨ A ⟩ &A × ∣⟨ B ⟩ &B × (&A &-&ᵖ &B ＝ o)  ∥
((A &ᵖ B) .∣-is-prop) o = ∥∥-is-prop

_∣ᵖ_ : PSet → PSet → PSet
∣⟨ A ∣ᵖ B ⟩ o = ∥ ∣⟨ A ⟩ o + ∣⟨ B ⟩ o ∥
∣-is-prop (A ∣ᵖ B) o = ∥∥-is-prop

_ᵀ : PSet → PSet
∣⟨ A ᵀ ⟩ o = ∥ (∀ x → (p : ∣⟨ A ⟩ x) → Σ y ꞉ 𝟚 × S×BSet , &⟨ x ⟩ y × &⟨ o ⟩ (y ᵗ)) ∥
∣-is-prop (A ᵀ) o = ∥∥-is-prop

Var : 𝓤 ⁺⁺ ̇
Var = Σ D ꞉ 𝓤 ̇  , (D → PSet)

Var→PSet : Var → PSet
∣⟨ Var→PSet (D , f) ⟩ &ps = ∥ (Σ x ꞉ D , ∣⟨ f x ⟩ &ps) ∥
∣-is-prop (Var→PSet (d , f)) &ps = ∥∥-is-prop

-- Dependent variance
-- Here both systems change at the same time

DVar : 𝓤 ⁺⁺ ̇
DVar = Σ D ꞉ 𝓤 ̇  , (D → PSet × PSet)

-- This is unaffected, since we compose the systems in different superpositions.
∣ᵈᵖ : DVar → PSet
∣ᵈᵖ (D , f) = Var→PSet (D , pr₁ ∘ f) ∣ᵖ Var→PSet (D , pr₂ ∘ f)

-- This on the other hand is affected. We
-- cannot treat the systems as separate. They interact together.
&ᵈᵖ : DVar → PSet
&ᵈᵖ (D , f) = Var→PSet (D , (λ d → (pr₁ (f d)) &ᵖ (pr₂ (f d))))
