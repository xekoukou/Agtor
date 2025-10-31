Predicates
==========


```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
```

This is a general module on Predicates.

```agda
module PredP (A : 𝓤 ̇) where

Pred : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
Pred 𝓥 = (x : A) → 𝓥 ̇ 


module Pred₂ (a b : Pred 𝓥) where
 _&&_ : Pred 𝓥
 _&&_ x = a x × b x

 _||_ : Pred 𝓥
 _||_ x = a x + b x


ΣPred : ∀ 𝓥 → Pred 𝓥 → 𝓤 ⊔ 𝓥 ̇
ΣPred 𝓥 C = Σ C


module ΣPred {C} (P : ΣPred 𝓥 C) where

 type : A
 type = P .pr₁

 str : C type
 str = P .pr₂
```
