#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Function of Change


#hide[
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

```
]


This is the the generalized version of the function of change.

It encodes all the possible msgs that the system could receive or accept, independent
of the structure of the system, ie the number of actors present. It also defines the change
that happens after the msg has arrived or has been sent.

```agda
open import PredP
open Pred

module FCP (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) 𝓥 where

open import Definitions Msg Secret

open ΣPred

module _ {B : 𝓦 ̇} where
 
 FC : 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ⊔ (𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)) ̇
 FC = (Σ Mp ꞉ BSet 𝓥 , (∀ x → < Mp > x → B)) × (Σ Ap ꞉ BSet 𝓥 , (∀ x → < Ap > x → B))
 
 module FC (fc : FC) where
 
  Mp : _
  Mp = fc .pr₁ .pr₁
 
  fm : ∀ x → < Mp > x → B
  fm = fc .pr₁ .pr₂
 
  Ap : _
  Ap = fc .pr₂ .pr₁
 
  fa : ∀ x → < Ap > x → B
  fa = fc .pr₂ .pr₂
 
 -- TODO Fix them, theyt are not useful
 ∨ᵍ : ∀(A C : BSet 𝓥) → (fc1 : ∀ x → < A > x → B) → (fc2 : ∀ x → < C > x → B) → ∀ x → < A ∨ C > x → B
 ∨ᵍ A C fc1 fc2 x (inl c) = fc1 x c
 ∨ᵍ A C fc1 fc2 x (inr c) = fc2 x c
 
 
 module FC₂ (fc1 fc2 : FC) where
  open FC
 
  _∨ᶠ_ : FC
  _∨ᶠ_ = ((Mp fc1) ∨ (Mp fc2) , (∨ᵍ (Mp fc1) (Mp fc2) (fm fc1) (fm fc2))) , (Ap fc1 ∨ Ap fc2) , (∨ᵍ (Ap fc1) (Ap fc2) (fa fc1) (fa fc2))
 
 
```
