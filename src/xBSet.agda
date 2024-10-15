{-# OPTIONS --safe --without-K --exact-split #-}
--TODO PUT safe flag again

open import MLTT.Spartan hiding (𝟚)
open import MLTT.Negation
open import MLTT.Plus
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv
open import MLTT.List
open import UF.Subsingletons
open import Naturals.Order
open import UF.Subsingletons-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Base

open import Lists

-- I know that UA proves Prop-Ext
module xBSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

open PropositionalTruncation pt

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

open import BSet fe pt S×Msg public

-- We have propositional equality which can be derived from (A → B , B → A)
_⇔_ : (A B : 𝓦 ̇) → 𝓦 ̇
A ⇔ B = (A → B) × (B → A)

×BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
×BSet 𝓥 = Σ bs ꞉ BSet 𝓥 , ∀ ascrs scrs x → scrs ⊃ ascrs × ascrs ⊃ scrs → ⟨ bs ⟩ (ascrs , x) ⇔ (⟨ bs ⟩ (scrs , x))

_bset : ×BSet 𝓥 → BSet 𝓥
_bset bs = bs .pr₁

_symm : (bs : ×BSet 𝓥)
 → (ascrs scrs : List Secret) (x : Msg + Secret) →
   (scrs ⊃ ascrs) × (ascrs ⊃ scrs) →
   ⟨ bs .pr₁ ⟩ (ascrs , x) ⇔ ⟨ bs .pr₁ ⟩ (scrs , x)
_symm bs = bs .pr₂

-- The property holds for all messages.
×⊨ : ×BSet 𝓥 → 𝓤 ⊔ 𝓥 ̇
×⊨ P = ∀ a → ⟨ P bset ⟩ a 

_×&&_ : ×BSet 𝓥 → ×BSet 𝓥 → ×BSet 𝓥
a ×&& b
 =   ((a bset) && (b bset))
   , λ ascrs scrs x eq → (λ (z , y) → (a .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ z) , (b .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ y))
   , λ (z , y) → (a .pr₂ ascrs scrs x eq .pr₂ z) , (b .pr₂ ascrs scrs x eq .pr₂ y)


_×||_ : ×BSet 𝓥 → ×BSet 𝓥 → ×BSet 𝓥
(a ×|| b) .pr₁ = (a bset) || (b bset)
(a@((x , _) , _) ×|| b@((y , _) , _)) .pr₂ ascrs scrs msg eq@(eq1 , eq2) = l1 where
  l1 : ⟨ pr₁ (a ×|| b) ⟩ (ascrs , msg) ⇔ ⟨ pr₁ (a ×|| b) ⟩ (scrs , msg)
  l1 .pr₁
    = ∥∥-rec
        (((a bset) || (b bset)) .pr₂ (scrs , msg))
        λ { (inl v) → ∣ inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₂ v) ∣ ; (inr v) → ∣ inr (b .pr₂ ascrs scrs msg eq .pr₁ v) ∣}
  l1 .pr₂
    = ∥∥-rec
        (((a bset) || (b bset)) .pr₂ (ascrs , msg))
        λ { (inl v) → ∣ inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₁ v) ∣ ; (inr v) → ∣ inr (b .pr₂ ascrs scrs msg eq .pr₂ v) ∣}


×Varᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
×Varᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇  , (D → ×BSet 𝓥)

Var→×BSet : ×Varᵇ 𝓦 𝓥 → ×BSet (𝓦 ⊔ 𝓥)
Var→×BSet (D , f)
 =  Var→BSet (D , pr₁ ∘ f)
 -- Can this be simplified ?
  , λ ascrs scrs msg (eq1 , eq2) → (λ x → ∥∥-rec ∥∥-is-prop (λ { (d , e) → ∣ d , (f d) .pr₂ ascrs scrs msg (eq1 , eq2) .pr₁ e ∣}) x) , (λ x → ∥∥-rec ∥∥-is-prop (λ { (d , e) → ∣ d , (f d) .pr₂ ascrs scrs msg (eq1 , eq2) .pr₂ e ∣}) x)

×Varᵇ→Set : ×Varᵇ 𝓦 𝓥 → S×Msg → 𝓦 ⊔ 𝓥 ̇
×Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ (f x) bset ⟩ mp)


×DVarᵇ : ∀ 𝓦 𝓥 → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ̇
×DVarᵇ 𝓦 𝓥 = Σ D ꞉ 𝓦 ̇  , (D → ×BSet 𝓥 × ×BSet 𝓥)

-- Redundant
DVar→×BSet : ×DVarᵇ 𝓦 𝓥 → ×BSet (𝓦 ⊔ 𝓥) × ×BSet (𝓦 ⊔ 𝓥)
DVar→×BSet (D , f) = Var→×BSet (D , pr₁ ∘ f) , Var→×BSet (D , pr₂ ∘ f)

×DVarᵇ→Set : ×DVarᵇ 𝓦 𝓥 → S×Msg → 𝓦 ⊔ 𝓥 ̇
×DVarᵇ→Set (D , f) mp = ×Varᵇ→Set (D , pr₁ ∘ f) mp × ×Varᵇ→Set (D , pr₂ ∘ f) mp
