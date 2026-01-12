
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

module LivenessP (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  ) 𝓥 𝓦 𝓠 where

open import Interleaving2

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
 module _ (sfc' : Stream PSet×PSet') where
  open DD sfc'

  open Stream sfc' renaming (next to nextₛ ; _at_ to _atₛ_)
  open Functor₁ (FStream PSet×PSet')
  open CoAlgebra₁ (FStream PSet×PSet')
  open Final-CoAlgebra₁ (FStream PSet×PSet') sfc' 

  module Liveness (R : <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → <PSet> 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠 → 𝓣 ̇  ) where
   liveness-fiber : Fn₁ ⟨ fc₁ ⟩₁ → 𝓣 ̇
   liveness-fiber e = (k : ℕ) → Σ n ꞉ ℕ , k ≤ n × let ((a , b) , _ ) = e atₛ n in R < a > < b >

   open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
   open Functor Fpot
   open CoAlgebra Fpot
   open Final-CoAlgebra Fpot fc-pot

   open import FCP Msg Secret 𝓥 ⟨ fc ⟩
   open FC
   open Pot {fc-pot}
 
   Interleaved-Condition : ∀ 𝓣  → 𝓣 ⁺ ̇
   Interleaved-Condition 𝓣 = ∀ (f : ℕ → ℕ) → (two : 𝟚) → 𝓣 ̇

   Cond-Liveness : (a b : Fn ⟨ fc ⟩) → 𝓣 ⊔ 𝓦 ⁺ ̇  
   Cond-Liveness a b = Σ IC ꞉ Interleaved-Condition 𝓦 , ∀ f two → IC f two → liveness-fiber ((fc₁ ⟶₁) (interleave f two a b))

   Liveness : (a b : Fn ⟨ fc ⟩) → 𝓣 ̇
   Liveness a b = ∀ f two → liveness-fiber ((fc₁ ⟶₁) (interleave f two a b))
