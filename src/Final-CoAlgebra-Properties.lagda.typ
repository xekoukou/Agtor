#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda

= Final Coalgebra Properties

#hide[
```agda
{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.FunExt
open import UF.Univalence
open import UF.Equiv

```
]

```agda

module Final-CoAlgebra-Properties  where

open import Final-CoAlgebraP
open import CoAlgebraP
open import FunctorP

module _ (fe : Fun-Ext) (UA : Univalence) func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where
 open Functor func
 open Final-CoAlgebra func fc'
 open CoAlgebra func
 open CoAlgebra₂ func 

 f-co : CoAlgebra func
 f-co = Fn ⟨ fc ⟩ , Fm (fc ↓)


 inv : co-morphism f-co fc
 inv = uni f-co .pr₁

 open Morphism f-co fc

 morph : co-morphism fc fc
 morph = (inv ⟶) ∘ (fc ↓) , λ x → (Fm-comp (inv ⟶) (fc ↓) ((fc ↓) x)) ⁻¹ ∙ (inv comm) ((fc ↓) x)
 
 morph-id : co-morphism fc fc
 morph-id = (λ x → x) , (λ x → Fm-id ((fc ↓) x) ) 

 inv∘Qf=id : (inv ⟶) ∘ (fc ↓) ＝ id
 inv∘Qf=id = l2 ⁻¹ ∙ l3  where
  l1 = uni fc
  c = l1 .pr₁
  l2 : c .pr₁ ＝ morph .pr₁
  l2 = ap pr₁ (l1 .pr₂ morph)

  l3 : c .pr₁ ＝ morph-id .pr₁
  l3 = ap pr₁ (l1 .pr₂ morph-id)

 Qf∘inv=id : (fc ↓) ∘ (inv ⟶) ＝ (λ x → x)
 Qf∘inv=id = (dfunext fe λ x → (inv comm) x ⁻¹ ∙ (Fm-comp (inv ⟶) (fc ↓) x ∙ ((ap (λ z → Fm z x) inv∘Qf=id) ∙ Fm-id x) ))

 QE=FQE : ⟨ fc ⟩ ＝ Fn ⟨ fc ⟩
 QE=FQE = eqtoid (UA _) ⟨ fc ⟩ (Fn ⟨ fc ⟩) (qinveq (fc ↓) ((inv ⟶) , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))
```
