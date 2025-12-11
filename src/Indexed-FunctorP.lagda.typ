#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Functors

#hide[
```agda

{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
```
]

```agda
module Indexed-FunctorP (I : 𝓥 ̇ ) where

ISet : ∀ 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇   
ISet 𝓤 = I → 𝓤 ̇


_⟼_ : (A B : ISet 𝓤) → 𝓥 ⊔ 𝓤 ̇
A ⟼ B = ∀ i → A i → B i


_∘ᵢ_ : ∀{A B D : ISet 𝓤} → A ⟼ B → D ⟼ A → D ⟼ B
f ∘ᵢ g = λ i z → f i (g i z) 

idᵢ : ∀{X : ISet 𝓤} → X ⟼ X
idᵢ = λ i x → x

IFunctor : ∀ 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇
IFunctor 𝓤 = Σ Fn ꞉ (ISet 𝓤 → ISet 𝓤 ) , Σ Fm ꞉ (∀{X Y} → (f : X ⟼ Y) → (Fn X) ⟼ (Fn Y)) , (∀{X Y Z} → (f : X ⟼ Y) → (g : Z ⟼ X) → ((Fm f) ∘ᵢ (Fm g) ＝ Fm (f ∘ᵢ g))) × (∀{X} → Fm idᵢ ＝ idᵢ {X = Fn X}) 

module IFunctor (func : IFunctor 𝓤) where

 Fnᵢ : ISet 𝓤 → ISet 𝓤
 Fnᵢ = func .pr₁

 Fmᵢ : _
 Fmᵢ = func .pr₂ .pr₁

 Fm-compᵢ : _
 Fm-compᵢ = func .pr₂ .pr₂ .pr₁ 

 Fm-idᵢ : _
 Fm-idᵢ = func .pr₂ .pr₂ .pr₂

```
