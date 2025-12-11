#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Coalgebras

#hide[
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan

module Indexed-CoAlgebraP (I : 𝓥 ̇ ) where

open import Indexed-FunctorP I
```
]

```agda

ICoAlgebra : (func : IFunctor 𝓤) → 𝓥 ⊔ 𝓤 ⁺ ̇
ICoAlgebra func = Σ A ꞉ _ , (A ⟼ F.Fnᵢ A) where
 module F = IFunctor func 


module ICoAlgebra func (co : ICoAlgebra {𝓤} func) where

 open IFunctor func

 ⟨_⟩ : ISet 𝓤
 ⟨_⟩ = co .pr₁

 _⟶ᵢ : ⟨_⟩ ⟼ Fnᵢ ⟨_⟩
 _⟶ᵢ = co .pr₂

module ICoAlgebra₂ func (a b : ICoAlgebra {𝓤} func) where
 open IFunctor func

 open ICoAlgebra func

 ico-morphism : 𝓥 ⊔ 𝓤 ̇
 ico-morphism = Σ f ꞉ (⟨ a ⟩ ⟼ ⟨ b ⟩) , Fmᵢ f ∘ᵢ (a ⟶ᵢ) ＝ (b ⟶ᵢ) ∘ᵢ f

 module IMorphism (m : ico-morphism) where
  _↓ᵢ : ⟨ a ⟩ ⟼ ⟨ b ⟩
  _↓ᵢ = m .pr₁

  _commᵢ : Fmᵢ _↓ᵢ ∘ᵢ (a ⟶ᵢ) ＝ (b ⟶ᵢ) ∘ᵢ _↓ᵢ
  _commᵢ = m .pr₂
 
```
