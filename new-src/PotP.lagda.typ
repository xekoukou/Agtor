#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Potentialities


#hide[
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
```
]

A potentiality is a sequence of states that a system could pass through. It also encodes
the potential change of state if it communicates with the exterior world.

```agda
open import PredP
open Pred

module PotP (Msg : 𝓤 ̇ ) (Secret : 𝓤 ̇  ) 𝓥 𝓦 𝓣 where

open import Definitions Msg Secret

open import FCP Msg Secret 𝓥

open ΣPred

```

BSet is a predicate on the messages that are received or accepted by a system.

&PSet is an abstract structure of the system, that will be used to check if the system reduces.

```agda

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP

Fpot : Functor (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺)
Fpot =
    (λ X → X × PSet 𝓥 𝓦 𝓣 × FC {_} {X})
  , (λ f (   x , &ps , ((mp ,         fm        ) , (ap ,          fa       ))) →
           f x , &ps ,  (mp , λ x c → f (fm x c)) , (ap , λ x c → f (fa x c)))
  , (λ f g x → refl)
  , λ {X} → refl

Pot = Final-CoAlgebra Fpot


open Functor Fpot
open CoAlgebra Fpot

module Pot {fc' : Pot} (a : Fn < fc' .pr₁ >) where

 open Final-CoAlgebra Fpot fc'

 next : < fc >
 next = a .pr₁

 pset : PSet 𝓥 𝓦 𝓣
 pset = a .pr₂ .pr₁

 foc : FC
 foc = a .pr₂ .pr₂

open import UF.FunExt
module Pot₁ (fe : Fun-Ext) {fc' : Pot} where

 open Final-CoAlgebra Fpot fc'

 _at_ : Fn ⟨ fc ⟩ → ℕ → Fn ⟨ fc ⟩
 (a , pa , fca) at zero = a , pa , fca
 (a , pa , fca) at succ n = ((fc ⟶) a) at n

 open import Final-CoAlgebra-Properties fe Fpot fc'
 open CoAlgebra₂ Fpot f-co fc
 open Morphism

 replace_at_ : Fn ⟨ fc ⟩ → ℕ → Fn ⟨ fc ⟩ → Fn ⟨ fc ⟩
 replace_at_ a@(na , pa , fca) zero b = b
 replace_at_ a@(na , pa , fca) (succ n) b = (inv ↓ ) ((replace ((fc ⟶) na) at n) b) , pa , fca


```
