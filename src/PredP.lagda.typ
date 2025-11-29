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


open Pred

module Pred₂ {A : 𝓤 ̇} (a b : Pred A 𝓥) where
 _&&ₚ_ : Pred A 𝓥
 _&&ₚ_ x = a x × b x

 _||ₚ_ : Pred A 𝓥
 _||ₚ_ x = a x + b x



module ΣPred {A : 𝓤 ̇} {C : Pred A 𝓥} (σ : Σ C) where

 <_> : A
 <_> = σ .pr₁

 _str : C <_>
 _str = σ .pr₂

module _ where
 open ΣPred
 open Pred₂
 module ΣPred₂ {A : 𝓤 ̇} {C : Pred (Pred A 𝓥) 𝓦} (q : (s e : Σ C) → C (< s > ||ₚ < e >)) (w : (s e : Σ C) → C (< s > &&ₚ < e >)) (s e : Σ C) where

  _||_ : Σ C
  _||_ = (< s > ||ₚ < e >) , (q s e)


  _&&_ : Σ C
  _&&_ = (< s > &&ₚ < e >) , (w s e)

  
 

```
