
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.List
open import UF.Subsingletons

open import PredP
open Pred
open ΣPred
open import Lists

module Definitions (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

-- We have propositional equality which can be derived from (A → B , B → A)
_⇔_ : (A B : 𝓦 ̇) → 𝓦 ̇
A ⇔ B = (A → B) × (B → A)

Cm : ∀ 𝓥 → Pred (Pred S×Msg 𝓥) (𝓤 ⊔ 𝓥)
Cm 𝓥 P = (∀ mp → is-prop (P mp)) × (∀ ascrs scrs x → scrs ⊃ ascrs × ascrs ⊃ scrs → P (ascrs , x) ⇔ (P (scrs , x)))

BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
BSet 𝓥 = Σ (Cm 𝓥)

bset-is-prop : (bs : BSet 𝓥) → (∀ mp → is-prop (< bs > mp))
bset-is-prop bs = bs .pr₂ .pr₁

_symm : (bs : BSet 𝓥)
 → (ascrs scrs : List Secret) (x : Msg + Secret) →
   (scrs ⊃ ascrs) × (ascrs ⊃ scrs) →
   < bs > (ascrs , x) ⇔ < bs > (scrs , x)
_symm bs = bs .pr₂ .pr₂


```
