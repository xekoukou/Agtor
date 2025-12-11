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

import Indexed-Final-CoAlgebraP as IFC
import Indexed-CoAlgebraP as IC
import Indexed-FunctorP as IF


module Indexed-Final-CoAlgebra-Properties (fe : Fun-Ext) (I : 𝓥 ̇ ) (func : IF.IFunctor I 𝓤) (fc' : IFC.IFinal-CoAlgebra I func) where

 open IFC I
 open IC I
 open IF I

 open IFunctor func
 open IFinal-CoAlgebra func fc'
 open ICoAlgebra func
 open ICoAlgebra₂ func 

 f-co : ICoAlgebra func
 f-co = Fnᵢ ⟨ fcᵢ ⟩ ,  Fmᵢ (fcᵢ ⟶ᵢ) 


 inv : ico-morphism f-co fcᵢ
 inv = uniᵢ f-co .pr₁

 open IMorphism f-co fcᵢ
 open IMorphism fcᵢ fcᵢ renaming (_↓ᵢ to _↓' ; _commᵢ to _comm')

 morph : ico-morphism fcᵢ fcᵢ
 morph = (inv ↓ᵢ) ∘ᵢ (fcᵢ ⟶ᵢ) , ap (λ z → z ∘ᵢ (fcᵢ ⟶ᵢ) ) ((Fm-compᵢ (inv ↓ᵢ) (fcᵢ ⟶ᵢ)) ⁻¹ ∙ ((inv commᵢ)))
 
 morph-id : ico-morphism fcᵢ fcᵢ
 morph-id = idᵢ , ap (λ z → z ∘ᵢ (fcᵢ ⟶ᵢ)) Fm-idᵢ

 inv∘Qf=id : (inv ↓ᵢ) ∘ᵢ (fcᵢ ⟶ᵢ) ＝ idᵢ
 inv∘Qf=id = l2 ⁻¹ ∙ l3  where
  l1 = uniᵢ fcᵢ
  c = l1 .pr₁
  l2 : c ↓' ＝ morph ↓'
  l2 = l1 .pr₂ morph

  l3 : c ↓' ＝ morph-id ↓'
  l3 = l1 .pr₂ morph-id

 Qf∘inv=id : (fcᵢ ⟶ᵢ) ∘ᵢ (inv ↓ᵢ) ＝ idᵢ
 Qf∘inv=id = (inv commᵢ) ⁻¹  ∙ (Fm-compᵢ (inv ↓ᵢ) (fcᵢ ⟶ᵢ) ∙ ((ap (λ z → Fmᵢ z) inv∘Qf=id) ∙ Fm-idᵢ))

 module _  (UA : Univalence) where

  QE=FQE' : ∀ i → ⟨ fcᵢ ⟩ i ＝ Fnᵢ ⟨ fcᵢ ⟩ i
  QE=FQE' i = eqtoid (UA _) (⟨ fcᵢ ⟩ i) (Fnᵢ ⟨ fcᵢ ⟩ i) (qinveq ((fcᵢ ⟶ᵢ) i) (((inv ↓ᵢ) i) , (happly ((λ x → ap (λ f → f x) inv∘Qf=id) i) , happly ((λ x → ap (λ f → f x) Qf∘inv=id) i))))
  QE=FQEᵢ : ⟨ fcᵢ ⟩ ＝ Fnᵢ ⟨ fcᵢ ⟩
  QE=FQEᵢ = dfunext fe λ i → QE=FQE' i
  

```
