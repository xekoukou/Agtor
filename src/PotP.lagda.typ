#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Potentialities


#hide[
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
```
]

A potentiality is a sequence of states that a system could pass through. It also encodes
the potential change of state if it communicates with the exterior world.

```agda
open import PredP
open Pred

module PotP (A : 𝓤 ̇ ) 𝓥 (Cm : Pred (Pred A 𝓥) (𝓤 ⊔ 𝓥)) 𝓦 (Cp : Pred (𝟚 × Σ Cm) 𝓦) where

 open import FCP {𝓦 = 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺} A 𝓥 Cm

 open ΣPred

```

BSet is a predicate on the messages that are received or accepted by a system.

&PSet is an abstract structure of the system, that will be used to check if the system reduces.

```agda
 BSet = Σ Cm
 &PSet = Σ Cp 

 open import FunctorP
 open import Final-CoAlgebraP

 Fpot : Functor (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺)
 Fpot =
    (λ X → X × &PSet × FC X)
  , (λ f (   x , &ps , ((mp ,         fm        ) , (ap ,          fa       ))) →
           f x , &ps ,  (mp , λ x c → f (fm x c)) , (ap , λ x c → f (fa x c)))
  , (λ f g x → refl)
  , λ x → refl

 Pot = Final-CoAlgebra Fpot
```
