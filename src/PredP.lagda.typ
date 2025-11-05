#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Predicate


#hide[
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
```
]

This is a general module on Predicates.

```agda
module PredP where

module Pred (A : 𝓤 ̇) where

 Pred : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
 Pred 𝓥 = (x : A) → 𝓥 ̇ 


 module Pred₂ (a b : Pred 𝓥) where
  _&&_ : Pred 𝓥
  _&&_ x = a x × b x

  _||_ : Pred 𝓥
  _||_ x = a x + b x


open Pred

module ΣPred {A : 𝓤 ̇} {C : Pred A 𝓥} (σ : Σ C) where

 <_> : A
 <_> = σ .pr₁

 _str : C <_>
 _str = σ .pr₂
 
```
