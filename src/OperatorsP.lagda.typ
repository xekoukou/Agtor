
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Multiple Communication
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties


```
*/

```agda

open import Interleaving2
open import StreamP
open import Indexed-FunctorP
open import Indexed-CoAlgebraP
open import Indexed-Final-CoAlgebraP

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
import PotP as P

open import PredP
open Pred

module OperatorsP (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠

open import MultiComm fe Msg Secret 𝓥 𝓦 𝓠 fc-pot

open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot

module _ (fc'₁ : InfInComm×) where

 open InfIntP fc'₁
 open IFunctor₁ FInfInComm×
 open ICoAlgebra₁ FInfInComm×
 open IFinal-CoAlgebra₁ FInfInComm× fc'₁

 module _ (ii : InfInt) where

  open IFunctor₂ FInfInt
  open ICoAlgebra₂ FInfInt
  open IFinal-CoAlgebra₂ FInfInt ii

  record FF (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
   field
    fin : FinInComm× d b
    sEx : let dd , bb = finIn→finEx× fin in SingleExComm (fin-ex-comm dd) × SingleExComm (fin-ex-comm bb)

  open FF
  -- TODO We have a mistake here. We need to loot at the n from SingeExComm
  -- to respect the constraints.

  _⊆1_ : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → FinInComm× d b → 𝓤 ⊔ 𝓥 ̇ 
  more step₁ s ⊆1 more step d = Σ eq ꞉ (step ＝ step₁) , (s ⊆1 transport (λ z → FinInComm× (commIn z .pr₁) (commIn z .pr₂)) eq d)
  lastOne step₁ ⊆1 more step d = step ＝ step₁
  more step₁ s ⊆1 lastOne step = 𝟘
  lastOne step₁ ⊆1 lastOne step = step ＝ step₁
  
  _⊆2_ : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) → 𝓤 ⊔ 𝓥 ̇ 
  more step₁ s ⊆2 (step , next) = Σ eq ꞉ (step ＝ step₁) ,(s ⊆2 transport (λ z → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (commIn z)) eq ((fcᵢ₁ ⟶ᵢ₁) (commIn step) next))
  lastOne step₁ ⊆2 (step , next) = (step ＝ step₁)
   
  _⊆_ : {d b : Fn ⟨ fc ⟩} → FF d b → Σ (FInt d b)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i)) → 𝓤 ⊔ 𝓥 ̇
  f ⊆ inl x = f .fin ⊆1 x .pr₁
  f ⊆ inr x = f .fin ⊆2 x .pr₁

  Fun : (d b : Fn ⟨ fc ⟩) → (e : Σ (FInt d b)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ̇  
  Fun d b e =
   (x : FF d b) → x ⊆ e →
     let dd , bb = fin-in-comm (x .fin)
         ddx = commEx (x .sEx .pr₁)
         bbx = commEx (x .sEx .pr₂)
     in (Σ (FInt ddx bb)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (ddx , bb) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (ddx , bb , i))) × ((Σ (FInt dd bbx)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (dd , bbx) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (dd , bbx , i))))
 
  FFunctor : IFunctor (Σ d ꞉ Fn ⟨ fc ⟩ , Σ b ꞉ Fn ⟨ fc ⟩ , Σ (FInt d b)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
  FFunctor =
     (λ X (d , b , x) → Σ f ꞉ Fun d b x , ((c : FF d b) → (rl : c ⊆ x) →
     let dd , bb = fin-in-comm (c .fin)
         ddx = commEx (c .sEx .pr₁)
         bbx = commEx (c .sEx .pr₂)
     in X (ddx , bb , f c rl .pr₁) × X (dd , bbx , f c rl .pr₂)))
   , (λ f i (g , r) → g , λ c rl → f _ (r c rl .pr₁) , f _ (r c rl .pr₂))
   , (λ {X} {Y} {Z} f g → refl)
   , λ {X} → refl


```
