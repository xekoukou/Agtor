#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Coalgebras

#hide[
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module CoAlgebraP where

open import FunctorP
```
]

```agda

CoAlgebra : (func : Functor 𝓤) → 𝓤 ⁺ ̇
CoAlgebra func = Σ A ꞉ _ , (A → F.Fn A) where
 module F = Functor func 


module CoAlgebra func (co : CoAlgebra {𝓤} func) where

 open Functor func

 ⟨_⟩ : 𝓤 ̇ 
 ⟨_⟩ = co .pr₁

 _⟶ : ⟨_⟩ → Fn ⟨_⟩
 _⟶ = co .pr₂

module CoAlgebra₂ func (a b : CoAlgebra {𝓤} func) where
 open Functor func

 open CoAlgebra func

 co-morphism : 𝓤 ̇
 co-morphism = Σ f ꞉ (⟨ a ⟩ → ⟨ b ⟩) , Fm f ∘ (a ⟶) ＝ (b ⟶) ∘ f

 module Morphism (m : co-morphism) where
  _↓ : ⟨ a ⟩ → ⟨ b ⟩
  _↓ = m .pr₁

  _comm : Fm _↓ ∘ (a ⟶) ＝ (b ⟶) ∘ _↓
  _comm = m .pr₂
 
```
