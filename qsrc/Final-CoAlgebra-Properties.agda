{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Subsingletons

module Final-CoAlgebra-Properties  where

open import Final-CoAlgebraP
open import CoAlgebraP
open import FunctorP


open import UF.FunExt
open import UF.Univalence
open import UF.Equiv

module _ (fe : Fun-Ext) (UA : Univalence) func (fc' : Final-CoAlgebra {𝓤 = 𝓤} func) where
 open Functor func
 open Final-CoAlgebra func fc'
 private
  module FC = CoAlgebra func fc
 open CoAlgebra₂ func

 f-co : CoAlgebra func
 f-co = Fn FC.type , Fm FC.morph
 private 
  module F-Co = CoAlgebra func f-co

 inv-morph : f-co-morphism f-co fc
 inv-morph = uni f-co .pr₁

 private
  module Inv = Morphism f-co fc inv-morph

 morph : f-co-morphism fc fc
 morph = Inv.morphism ∘ FC.morph , λ x → (Fm-comp Inv.morphism FC.morph (FC.morph x)) ⁻¹ ∙ Inv.property (FC.morph x)
 
 morph-id : f-co-morphism fc fc
 morph-id = (λ x → x) , (λ x → Fm-id (FC.morph x) ) 

 inv∘Qf=id : Inv.morphism ∘ FC.morph ＝ id
 inv∘Qf=id = l2 ⁻¹ ∙ l3  where
  l1 = uni fc
  c = l1 .pr₁
  l2 : c .pr₁ ＝ morph .pr₁
  l2 = ap pr₁ (l1 .pr₂ morph)

  l3 : c .pr₁ ＝ morph-id .pr₁
  l3 = ap pr₁ (l1 .pr₂ morph-id)

 Qf∘inv=id : FC.morph ∘ Inv.morphism ＝ (λ x → x)
 Qf∘inv=id = (dfunext fe λ x → Inv.property x ⁻¹ ∙ (Fm-comp Inv.morphism FC.morph x ∙ ((ap (λ z → Fm z x) inv∘Qf=id) ∙ Fm-id x) ))

 QE=FQE : FC.type ＝ Fn FC.type
 QE=FQE = eqtoid (UA _) FC.type (Fn FC.type) (qinveq FC.morph (Inv.morphism , (λ x → ap (λ f → f x) inv∘Qf=id) , (λ x → ap (λ f → f x) Qf∘inv=id)))
