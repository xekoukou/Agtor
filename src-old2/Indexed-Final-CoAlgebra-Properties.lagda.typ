#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra Properties

#hide[
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.FunExt
open import UF.Base
open import UF.Univalence
open import UF.Equiv

```
]

```agda

open import Indexed-Final-CoAlgebraP
open import Indexed-CoAlgebraP
open import Indexed-FunctorP


module Indexed-Final-CoAlgebra-Properties (fe : Fun-Ext) (I : 𝓥 ̇ ) (func : IFunctor I 𝓤) (fc' : IFinal-CoAlgebra func) where

 open IFunctor func
 open IFinal-CoAlgebra func fc'
 open ICoAlgebra func

 f-co : ICoAlgebra func
 f-co = Fnᵢ ⟨ fcᵢ ⟩ᵢ ,  Fmᵢ (fcᵢ ⟶ᵢ) 


 inv : co-morphismᵢ func f-co fcᵢ
 inv = uniᵢ f-co .pr₁

 open IMorphism func f-co fcᵢ
 open IMorphism₁ func fcᵢ fcᵢ

 morph : co-morphismᵢ func fcᵢ fcᵢ
 morph = (inv ↓ᵢ) ∘ᵢ (fcᵢ ⟶ᵢ) , ap (λ z → z ∘ᵢ (fcᵢ ⟶ᵢ) ) ((Fm-compᵢ (inv ↓ᵢ) (fcᵢ ⟶ᵢ)) ⁻¹ ∙ ((inv commᵢ)))
 
 morph-id : co-morphismᵢ func fcᵢ fcᵢ
 morph-id = idᵢ , ap (λ z → z ∘ᵢ (fcᵢ ⟶ᵢ)) Fm-idᵢ

 inv∘Qf=id : (inv ↓ᵢ) ∘ᵢ (fcᵢ ⟶ᵢ) ＝ idᵢ
 inv∘Qf=id = l2 ⁻¹ ∙ l3  where
  l1 = uniᵢ fcᵢ
  c = l1 .pr₁
  l2 : c ↓ᵢ₁ ＝ morph ↓ᵢ₁
  l2 = l1 .pr₂ morph

  l3 : c ↓ᵢ₁ ＝ morph-id ↓ᵢ₁
  l3 = l1 .pr₂ morph-id

 Qf∘inv=id : (fcᵢ ⟶ᵢ) ∘ᵢ (inv ↓ᵢ) ＝ idᵢ
 Qf∘inv=id = (inv commᵢ) ⁻¹  ∙ (Fm-compᵢ (inv ↓ᵢ) (fcᵢ ⟶ᵢ) ∙ ((ap (λ z → Fmᵢ z) inv∘Qf=id) ∙ Fm-idᵢ))

 module _  (UA : Univalence) where

  QE=FQE' : ∀ i → ⟨ fcᵢ ⟩ᵢ i ＝ Fnᵢ ⟨ fcᵢ ⟩ᵢ i
  QE=FQE' i = eqtoid (UA _) (⟨ fcᵢ ⟩ᵢ i) (Fnᵢ ⟨ fcᵢ ⟩ᵢ i) (qinveq ((fcᵢ ⟶ᵢ) i) (((inv ↓ᵢ) i) , (happly ((λ x → ap (λ f → f x) inv∘Qf=id) i) , happly ((λ x → ap (λ f → f x) Qf∘inv=id) i))))
  QE=FQEᵢ : ⟨ fcᵢ ⟩ᵢ ＝ Fnᵢ ⟨ fcᵢ ⟩ᵢ
  QE=FQEᵢ = dfunext fe λ i → QE=FQE' i
  

```
