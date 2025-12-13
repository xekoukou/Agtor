
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Liveness
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan renaming (_+_ to _＋_)
open import Naturals.Addition
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties
open import MLTT.Two-Properties


```
*/

```agda

module Liveness (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) 𝓥 𝓦 𝓠 where

open import Interleaving

open import PredP
open ΣPred

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
import PotP as P

open import Definitions Msg Secret
open ΣPred

open import StreamP


module _ (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where
 open Interleave Msg Secret 𝓥 𝓦 𝓠 fc-pot
 
 module _ (sfc' : Stream PSet×PSet) where
  open DD sfc'
  open Stream sfc' renaming (next to nextₛ)
  open Stream₁ sfc' renaming (_at_ to _atₛ_)
  open Functor (FStream PSet×PSet) renaming (Fn to Fnₛ)
  open CoAlgebra (FStream PSet×PSet)renaming (⟨_⟩ to ⟨_⟩ₛ ; _⟶ to _⟶ₛ)
  open Final-CoAlgebra (FStream PSet×PSet) sfc' renaming (fc to fcₛ ; uni to uniₛ)
  
  liveness-fiber : (R : PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → 𝓣 ̇  ) → Fnₛ ⟨ fcₛ ⟩ₛ → 𝓣 ̇
  liveness-fiber R e = (k : ℕ) → Σ n ꞉ ℕ , k ≤ n × let ((a , b) , _ ) = e atₛ n in R a b
 
  open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
  open Functor Fpot
  open CoAlgebra Fpot
  open Final-CoAlgebra Fpot fc-pot
  open import FCP Msg Secret 𝓥 ⟨ fc ⟩
  open FC
  open Pot {fc-pot}

  
  Liveness : (R : PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → PSet 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → 𝓣 ̇  )
             → (a b : Fn ⟨ fc ⟩) → 𝓣 ̇
  Liveness R a b = ∀ two k f g → liveness-fiber R ((fcₛ ⟶ₛ) (interleave f g two k a b))
