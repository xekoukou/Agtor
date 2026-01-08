#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Coalgebras

#hide[
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan

module Indexed-CoAlgebraP where

open import Indexed-FunctorP
```
]

```agda

module _  {I : 𝓥 ̇ } where

 ICoAlgebra : (func : IFunctor I 𝓤) → 𝓥 ⊔ 𝓤 ⁺ ̇
 ICoAlgebra func = Σ A ꞉ _ , (A ⟼ Fnᵢ A) where
  open IFunctor func 
 
 
 module ICoAlgebra func (co : ICoAlgebra {𝓤} func) where
 
  open IFunctor func
 
  ⟨_⟩ᵢ : ISet I 𝓤
  ⟨_⟩ᵢ = co .pr₁
 
  _⟶ᵢ : ⟨_⟩ᵢ ⟼ Fnᵢ ⟨_⟩ᵢ
  _⟶ᵢ = co .pr₂
 
 module _ (func : IFunctor I 𝓤) where
  open IFunctor func
  open ICoAlgebra func
 
  co-morphismᵢ : (a b : ICoAlgebra {𝓤} func) → 𝓥 ⊔ 𝓤 ̇
  co-morphismᵢ a b = Σ f ꞉ (⟨ a ⟩ᵢ ⟼ ⟨ b ⟩ᵢ) , Fmᵢ f ∘ᵢ (a ⟶ᵢ) ＝ (b ⟶ᵢ) ∘ᵢ f
 
  module IMorphism (a b : ICoAlgebra {𝓤} func) (m : co-morphismᵢ a b) where
   _↓ᵢ : ⟨ a ⟩ᵢ ⟼ ⟨ b ⟩ᵢ
   _↓ᵢ = m .pr₁
 
   _commᵢ : Fmᵢ _↓ᵢ ∘ᵢ (a ⟶ᵢ) ＝ (b ⟶ᵢ) ∘ᵢ _↓ᵢ
   _commᵢ = m .pr₂
   
  module IMorphism₁ (a b : ICoAlgebra {𝓤} func) (m : co-morphismᵢ a b) = IMorphism a b m renaming (_↓ᵢ to _↓ᵢ₁ ; _commᵢ to _commᵢ₁)
  module IMorphism₂ (a b : ICoAlgebra {𝓤} func) (m : co-morphismᵢ a b) = IMorphism a b m renaming (_↓ᵢ to _↓ᵢ₂ ; _commᵢ to _commᵢ₂)
  module IMorphism₃ (a b : ICoAlgebra {𝓤} func) (m : co-morphismᵢ a b) = IMorphism a b m renaming (_↓ᵢ to _↓ᵢ₃ ; _commᵢ to _commᵢ₃)
  module IMorphism₄ (a b : ICoAlgebra {𝓤} func) (m : co-morphismᵢ a b) = IMorphism a b m renaming (_↓ᵢ to _↓ᵢ₄ ; _commᵢ to _commᵢ₄)

  
   
 module ICoAlgebra₁ {𝓤} func (co : ICoAlgebra {𝓤} func) = ICoAlgebra func co renaming (⟨_⟩ᵢ to ⟨_⟩ᵢ₁ ; _⟶ᵢ to _⟶ᵢ₁) 
 module ICoAlgebra₂ {𝓤} func (co : ICoAlgebra {𝓤} func) = ICoAlgebra func co renaming (⟨_⟩ᵢ to ⟨_⟩ᵢ₂ ; _⟶ᵢ to _⟶ᵢ₂) 
 module ICoAlgebra₃ {𝓤} func (co : ICoAlgebra {𝓤} func) = ICoAlgebra func co renaming (⟨_⟩ᵢ to ⟨_⟩ᵢ₃ ; _⟶ᵢ to _⟶ᵢ₃) 
 module ICoAlgebra₄ {𝓤} func (co : ICoAlgebra {𝓤} func) = ICoAlgebra func co renaming (⟨_⟩ᵢ to ⟨_⟩ᵢ₄ ; _⟶ᵢ to _⟶ᵢ₄) 

 

```
