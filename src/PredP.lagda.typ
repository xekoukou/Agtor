#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

#set document(
  title: [Predicates]
)

#title()

= Definition

#let i = 1
#emph[ #i ]
#set text(lang: "de")
#context text.lang
#set heading(numbering: "1.a)")
#let dear = [= Dear]
#dear.fields()
#dear
#dear.fields()

#let task(body, critical: false) = {
  set text(red) if critical
  body
}

#task(critical: true)[Food today?]
#task(critical: false)[Work deadline]
/*
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module PredP where
```
*/
#show emph: it => {
 text(fill: blue , style: "italic" , it.body)
}

A predicate defines a property that a term of a specific type _A_ must have.

```agda
module Pred (A : 𝓤 ̇) where

 Pred : ∀ 𝓥 → 𝓤 ⊔ 𝓥 ⁺ ̇
 Pred 𝓥 = (x : A) → 𝓥 ̇ 

```
/*
```agda
open Pred
```
*/

```agda
module Pred₂ {A : 𝓤 ̇} (a : Pred A 𝓥) (b : Pred A 𝓦) where
 _&&ₚ_ : Pred A (𝓥 ⊔ 𝓦)
 _&&ₚ_ x = a x × b x

 _||ₚ_ : Pred A (𝓥 ⊔ 𝓦)
 _||ₚ_ x = a x + b x

 infix 2 _⇒ₚ_
 _⇒ₚ_ : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 _⇒ₚ_ = ∀ v → a v → b v

 infix 2 _⇐ₚ_
 _⇐ₚ_ : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 _⇐ₚ_ = ∀ v → b v → a v

 infix 2 _⇔ₚ_
 _⇔ₚ_ : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 _⇔ₚ_ = _⇒ₚ_ × _⇐ₚ_

module Pred₂' {A : 𝓤 ̇} (a : Pred A 𝓥) (b : Pred A 𝓥) where
 open Pred₂
 
 ＝→⇐⇒ₚ : a ＝ b → a ⇔ₚ b
 ＝→⇐⇒ₚ refl = (λ v z → z) , (λ v z → z)

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
