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
open import Maybe

-- I know that UA proves Prop-Ext
module xBSet (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

open PropositionalTruncation pt

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

open import BSet fe pt S×Msg public

-- We have propositional equality which can be derived from (A → B , B → A)
_⇔_ : (A B : 𝓤 ̇) → 𝓤 ̇
A ⇔ B = (A → B) × (B → A)

×BSet : 𝓤 ⁺ ̇
×BSet = Σ bs ꞉ BSet' , ∀ ascrs scrs x → scrs ⊃ ascrs × ascrs ⊃ scrs → ⟨ bs ⟩' (ascrs , x) ⇔ (⟨ bs ⟩' (scrs , x))

_bset : ×BSet → BSet'
_bset bs = bs .pr₁

-- The property holds for all messages.
×⊨ : ×BSet → 𝓤 ̇
×⊨ P = ∀ a → ⟨ P bset ⟩' a 

×⊥B : ×BSet
×⊥B = ⊥B toBSet' , λ ascrs scrs _ _ → id , id

×⊤B : ×BSet
×⊤B = ⊤B toBSet' , λ ascrs scrs _ _ → id , id

_×&&_ : ×BSet → ×BSet → ×BSet
a ×&& b
 =   ((a bset) &&' (b bset))
   , λ ascrs scrs x eq → (λ (z , y) → (a .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ z) , (b .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ y))
   , λ (z , y) → (a .pr₂ ascrs scrs x eq .pr₂ z) , (b .pr₂ ascrs scrs x eq .pr₂ y)


_×||_ : ×BSet → ×BSet → ×BSet
(a ×|| b) .pr₁ = (a bset) ||'' (b bset)
(a@((x , _) , _) ×|| b@((y , _) , _)) .pr₂ ascrs scrs msg eq@(eq1 , eq2) = l1 where
  l1 : ⟨ pr₁ (a ×|| b) ⟩' (ascrs , msg) ⇔ ⟨ pr₁ (a ×|| b) ⟩' (scrs , msg)
  l1 .pr₁
    = ∥∥-rec
        (((a bset) ||'' (b bset)) .pr₂ (scrs , msg))
        λ { (inl v) → ∣ inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₂ v) ∣ ; (inr v) → ∣ inr (b .pr₂ ascrs scrs msg eq .pr₁ v) ∣}
  l1 .pr₂
    = ∥∥-rec
        (((a bset) ||'' (b bset)) .pr₂ (ascrs , msg))
        λ { (inl v) → ∣ inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₁ v) ∣ ; (inr v) → ∣ inr (b .pr₂ ascrs scrs msg eq .pr₂ v) ∣}


×Varᵇ : 𝓤 ⁺ ̇
×Varᵇ = Σ D ꞉ 𝓤 ̇  , (D → ×BSet)

Var→×BSet : ×Varᵇ → ×BSet
Var→×BSet (D , f)
 =  Var→BSet (D , pr₁ ∘ f)
 -- Can this be simplified ?
  , λ ascrs scrs msg (eq1 , eq2) → (λ x → ∥∥-rec ∥∥-is-prop (λ { (d , e) → ∣ d , (f d) .pr₂ ascrs scrs msg (eq1 , eq2) .pr₁ e ∣}) x) , (λ x → ∥∥-rec ∥∥-is-prop (λ { (d , e) → ∣ d , (f d) .pr₂ ascrs scrs msg (eq1 , eq2) .pr₂ e ∣}) x)

×Varᵇ→Set : ×Varᵇ → S×Msg → 𝓤 ̇
×Varᵇ→Set (D , f) mp = (Σ x ꞉ D , ⟨ (f x) bset ⟩' mp)


×DVarᵇ : 𝓤 ⁺ ̇
×DVarᵇ = Σ D ꞉ 𝓤 ̇  , (D → ×BSet × ×BSet)

-- Redundant
DVar→×BSet : ×DVarᵇ → ×BSet × ×BSet
DVar→×BSet (D , f) = Var→×BSet (D , pr₁ ∘ f) , Var→×BSet (D , pr₂ ∘ f)

×DVarᵇ→Set : ×DVarᵇ → S×Msg → 𝓤 ̇
×DVarᵇ→Set (D , f) mp = ×Varᵇ→Set (D , pr₁ ∘ f) mp × ×Varᵇ→Set (D , pr₂ ∘ f) mp
