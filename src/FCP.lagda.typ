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

module FCP (A : 𝓤 ̇ ) 𝓥 (C : Pred (Pred A 𝓥) (𝓤 ⊔ 𝓥)) (B : 𝓦 ̇) where

open ΣPred

FC = (Σ Mp ꞉ Σ C , (∀ x → < Mp > x → B)) × (Σ Ap ꞉ Σ C , (∀ x → < Ap > x → B))

module FC (fc : FC) where
 Mp : _
 Mp = fc .pr₁ .pr₁

 fm : ∀ x → < Mp > x → B
 fm = fc .pr₁ .pr₂

 Ap : _
 Ap = fc .pr₂ .pr₁

 fa : ∀ x → < Ap > x → B
 fa = fc .pr₂ .pr₂

```
