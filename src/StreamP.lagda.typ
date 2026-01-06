
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Interleaving
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan

```
*/

```agda

module StreamP where


open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP

open import PredP
open ΣPred

FStream : (A : 𝓤 ̇  ) → Functor 𝓤
FStream A = (λ X → A × X) , (λ f x → x .pr₁ , f (x .pr₂)) , (λ {X} {Y} {Z} f g x → refl) , (λ {X} → refl)

Stream : (A : 𝓤 ̇  ) → 𝓤 ⁺ ̇
Stream A = Final-CoAlgebra (FStream A)

module _  {A : 𝓤 ̇ } where

 open Functor (FStream A)
 open CoAlgebra (FStream A)
 
 module Stream (fc' : Stream A) where
 
  open Final-CoAlgebra (FStream A) fc'
 
  next : Fn ⟨ fc ⟩ → < fc >
  next a = a .pr₂
 
  value : Fn ⟨ fc ⟩ → A
  value a = a .pr₁

  _at_ : Fn ⟨ fc ⟩ → ℕ → Fn ⟨ fc ⟩
  d at zero = d
  (a , d) at succ n = ((fc ⟶) d) at n
