#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Definitions


```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import MLTT.List
open import UF.Subsingletons

open import PredP
open Pred
open Pred₂
open ΣPred
open import Lists

module Definitions (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) where

S×Msg : 𝓤 ̇
S×Msg = List Secret × (Msg + Secret)

-- We have propositional equality which can be derived from (A → B , B → A)
_⇔_ : (A B : 𝓦 ̇) → 𝓦 ̇
A ⇔ B = (A → B) × (B → A)

```

At the moment, I consider BSet to not be a proposition. In the future, we might need
to have two different definitions, one of it being a proposition.

```agda

<BSet> : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
<BSet> 𝓥 = Pred S×Msg 𝓥

Cm : ∀ 𝓥 → Pred (<BSet> 𝓥) (𝓤 ⊔ 𝓥)
Cm 𝓥 P = (∀ ascrs scrs x → scrs ⊃ ascrs × ascrs ⊃ scrs → P (ascrs , x) ⇔ (P (scrs , x)))

BSet : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
BSet 𝓥 = Σ (Cm 𝓥)

-- bset-is-prop : (bs : BSet 𝓥) → (∀ mp → is-prop (< bs > mp))
-- bset-is-prop bs = bs .pr₂ .pr₁

_symm : (bs : BSet 𝓥)
 → (ascrs scrs : List Secret) (x : Msg + Secret) →
   (scrs ⊃ ascrs) × (ascrs ⊃ scrs) →
   < bs > (ascrs , x) ⇔ < bs > (scrs , x)
_symm bs = bs .pr₂

module BSet₂ {𝓥} = ΣPred₂ {C = Cm 𝓥} (λ a b ascrs scrs msg eq@(eq1 , eq2) → (λ { (inl v) → inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₂ v) ; (inr v) → inr (b .pr₂ ascrs scrs msg eq .pr₁ v)}) , λ { (inl v) → inl (a .pr₂ scrs ascrs msg (eq2 , eq1) .pr₁ v) ; (inr v) → inr (b .pr₂ ascrs scrs msg eq .pr₂ v)}) (λ a b → λ ascrs scrs x eq → (λ (z , y) → (a .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ z) , (b .pr₂ scrs ascrs x ((eq .pr₂) , (eq .pr₁)) .pr₂ y))
   , λ (z , y) → (a .pr₂ ascrs scrs x eq .pr₂ z) , (b .pr₂ ascrs scrs x eq .pr₂ y))

open BSet₂ public renaming (_||_ to _∨_ ; _&&_ to _∧_)



```
Similarly, &PSet might have to be a Proposition in the future, but it increases complexity
without any reason at the moment.

```agda

<&PSet> : ∀ 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
<&PSet> 𝓥 𝓦 = Pred (𝟚 × (BSet 𝓥)) 𝓦 

C&p : ∀ 𝓥 𝓦 → Pred (<&PSet> 𝓥 𝓦) (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦)
C&p 𝓥 𝓦 P = 𝟙

&PSet : ∀ 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
&PSet 𝓥 𝓦 = Σ (C&p 𝓥 𝓦)

module &ΣPred₂ {𝓥} {𝓦} = ΣPred₂ {C = C&p 𝓥 𝓦} (λ s e → cons-is-non-empty) (λ s e → cons-is-non-empty)

open &ΣPred₂ public


<PSet> : ∀ 𝓥 𝓦 𝓣 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
<PSet> 𝓥 𝓦 𝓣 = Pred (&PSet 𝓥 𝓦) 𝓣 

Cp : ∀ 𝓥 𝓦 𝓣 → Pred (<PSet> 𝓥 𝓦 𝓣) (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣)
Cp 𝓥 𝓦 𝓣 P = 𝟙

PSet : ∀ 𝓥 𝓦 𝓣 → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ⊔ (𝓣 ⁺) ̇
PSet 𝓥 𝓦 𝓣 = Σ (Cp 𝓥 𝓦 𝓣)

module |ΣPred₂ {𝓥} {𝓦} {𝓣} = ΣPred₂ {C = Cp 𝓥 𝓦 𝓣} (λ s e → cons-is-non-empty) (λ s e → cons-is-non-empty) 

open |ΣPred₂ public renaming (_||_ to _∣_ ; _&&_ to _&_)



```

