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
open import UF.Univalence
open import UF.Equiv

```
]

```agda

open import Final-CoAlgebraP
open import CoAlgebraP
open import FunctorP


module Final-CoAlgebra-Properties (fe : Fun-Ext) func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where

 open Functor func
 open Final-CoAlgebra func fc'
 open CoAlgebra func
 open CoAlgebra₂ func 

 f-co : CoAlgebra func
 f-co = Fn ⟨ fc ⟩ ,  Fm (fc ⟶) 


 inv : co-morphism f-co fc
 inv = uni f-co .pr₁

 open Morphism f-co fc
 open Morphism fc fc renaming (_↓ to _↓' ; _comm to _comm')

 morph : co-morphism fc fc
 morph = (inv ↓) ∘ (fc ⟶) ,
  dfunext fe (λ x → (Fm-comp (inv ↓) (fc ⟶) ((fc ⟶) x)) ⁻¹
   ∙ ap (λ z → z ((fc ⟶) x)) (inv comm))
 
 morph-id : co-morphism fc fc
 morph-id = (λ x → x) , ap (λ z → z ∘ (fc ⟶)) Fm-id

 inv∘Qf=id : (inv ↓) ∘ (fc ⟶) ＝ id
 inv∘Qf=id = l2 ⁻¹ ∙ l3  where
  l1 = uni fc
  c = l1 .pr₁
  l2 : c ↓' ＝ morph ↓'
  l2 = l1 .pr₂ morph

  l3 : c ↓' ＝ morph-id ↓'
  l3 = l1 .pr₂ morph-id

 Qf∘inv=id : (fc ⟶) ∘ (inv ↓) ＝ (λ x → x)
 Qf∘inv=id = dfunext fe λ x →  ap (λ z → z x) (inv comm) ⁻¹  ∙ (Fm-comp (inv ↓) (fc ⟶) x ∙ ((ap (λ z → Fm z x) inv∘Qf=id) ∙ ap (λ z → z x) Fm-id))

 module _  (UA : Univalence) where

  QE=FQE : ⟨ fc ⟩ ＝ Fn ⟨ fc ⟩
  QE=FQE = eqtoid (UA _) ⟨ fc ⟩ (Fn ⟨ fc ⟩) (qinveq (fc ⟶) ((inv ↓) , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))
```
