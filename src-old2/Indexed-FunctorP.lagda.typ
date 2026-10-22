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
module Indexed-FunctorP where

ISet : (I : 𝓥 ̇ ) → ∀ 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇   
ISet I 𝓤 = I → 𝓤 ̇
 
 
module _ {I : 𝓥 ̇ } where

 _⟼_ : (A B : ISet I 𝓤) → 𝓥 ⊔ 𝓤 ̇
 A ⟼ B = ∀ i → A i → B i
 
 
 _∘ᵢ_ : ∀{A B D : ISet I 𝓤} → A ⟼ B → D ⟼ A → D ⟼ B
 f ∘ᵢ g = λ i z → f i (g i z) 
 
 idᵢ : ∀{X : ISet I 𝓤} → X ⟼ X
 idᵢ = λ i x → x

IFunctor : (I : 𝓥 ̇ ) → ∀ 𝓤 → 𝓥 ⊔ 𝓤 ⁺ ̇
IFunctor I 𝓤 = Σ Fn ꞉ (ISet I 𝓤 → ISet I 𝓤 ) , Σ Fm ꞉ (∀{X Y} → (f : X ⟼ Y) → (Fn X) ⟼ (Fn Y)) , (∀{X Y Z} → (f : X ⟼ Y) → (g : Z ⟼ X) → ((Fm f) ∘ᵢ (Fm g) ＝ Fm (f ∘ᵢ g))) × (∀{X} → Fm idᵢ ＝ idᵢ {X = Fn X}) 

module IFunctor {I : 𝓥 ̇ } {𝓤} (func : IFunctor I 𝓤) where

 Fnᵢ : ISet I 𝓤 → ISet I 𝓤
 Fnᵢ = func .pr₁

 Fmᵢ : _
 Fmᵢ = func .pr₂ .pr₁

 Fm-compᵢ : _
 Fm-compᵢ = func .pr₂ .pr₂ .pr₁ 

 Fm-idᵢ : _
 Fm-idᵢ = func .pr₂ .pr₂ .pr₂

module IFunctor₁ {𝓥} {I : 𝓥 ̇} {𝓤} (func : IFunctor I 𝓤) = IFunctor func renaming (Fnᵢ to Fnᵢ₁ ; Fmᵢ to Fmᵢ₁ ; Fm-compᵢ to Fm-compᵢ₁ ; Fm-idᵢ to Fm-idᵢ₁)
module IFunctor₂ {𝓥} {I : 𝓥 ̇} {𝓤} (func : IFunctor I 𝓤) = IFunctor func renaming (Fnᵢ to Fnᵢ₂ ; Fmᵢ to Fmᵢ₂ ; Fm-compᵢ to Fm-compᵢ₂ ; Fm-idᵢ to Fm-idᵢ₂)
module IFunctor₃ {𝓥} {I : 𝓥 ̇} {𝓤} (func : IFunctor I 𝓤) = IFunctor func renaming (Fnᵢ to Fnᵢ₃ ; Fmᵢ to Fmᵢ₃ ; Fm-compᵢ to Fm-compᵢ₃ ; Fm-idᵢ to Fm-idᵢ₃)
module IFunctor₄ {𝓥} {I : 𝓥 ̇} {𝓤} (func : IFunctor I 𝓤) = IFunctor func renaming (Fnᵢ to Fnᵢ₄ ; Fmᵢ to Fmᵢ₄ ; Fm-compᵢ to Fm-compᵢ₄ ; Fm-idᵢ to Fm-idᵢ₄)

```
