
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

open import Definitions Msg Secret
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

  module QQ (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where
   open LL stream

   nFinLiv : {d b : Fn ⟨ fc ⟩} → (c : FF d b) → Fin-Liveness (d , b) →
    let dd , bb = fin-in-comm (c .fin)
        ddx = commEx (c .sEx .pr₁)
        bbx = commEx (c .sEx .pr₂)
    in Fin-Liveness (dd , bbx) × Fin-Liveness (ddx , bb)
   nFinLiv c fLiv =
    let dd , bb = finIn→finEx× (c .fin)
        ddx = c .sEx .pr₁
        bbx = c .sEx .pr₂
    in {!!}



  fcn : {d b : Fn ⟨ fc ⟩} → (q : FinInComm× d b) → FinInComm× d b →
   let dd , bb = finIn→finEx× q
   in SingleExComm (fin-ex-comm dd) × SingleExComm (fin-ex-comm bb) → 𝓤 ⊔ 𝓥 ̇ 
  fcn (more step₁ s) (more step d) r
   = Σ eq ꞉ (step ＝ step₁) , (fcn s (transport (λ z → FinInComm× (commIn z .pr₁) (commIn z .pr₂)) eq d) r)
  fcn (lastOne step₁) (more step (more nstep d)) (g , h)
   = (step ＝ step₁) × (nIn nstep ＝ nEx g , nEx h)
  fcn (lastOne step₁) (more step (lastOne nstep)) (g , h) = (step ＝ step₁) × (nIn nstep ＝ nEx g , nEx h)
  fcn (more step₁ s) (lastOne step) _ = 𝟘
  fcn (lastOne step₁) (lastOne step) _ = step ＝ step₁
  
  ifcn : {d b : Fn ⟨ fc ⟩} → (q : FinInComm× d b) → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) →
   let dd , bb = finIn→finEx× q
   in SingleExComm (fin-ex-comm dd) × SingleExComm (fin-ex-comm bb) → 𝓤 ⊔ 𝓥 ̇ 
  ifcn (more step₁ s) (step , next) r
   = Σ eq ꞉ (step ＝ step₁) ,(ifcn s (transport (λ z → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (commIn z)) eq ((fcᵢ₁ ⟶ᵢ₁) (commIn step) next)) r)
  ifcn (lastOne step₁) (step , next) (g , h)
   = (step ＝ step₁) × (nIn (((fcᵢ₁ ⟶ᵢ₁) (commIn step) next) .pr₁) ＝ (nEx g) , (nEx h))
   
  _⊆_ : {d b : Fn ⟨ fc ⟩} → FF d b → Σ (FInt d b)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i)) → 𝓤 ⊔ 𝓥 ̇
  f ⊆ inl x = fcn (f .fin) (x .pr₁) (f .sEx)
  f ⊆ inr x = ifcn (f .fin) (x .pr₁) (f .sEx)

  CC : {d b : Fn ⟨ fc ⟩} → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → {!!}

  module RR (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where
   open LL stream

   FFunctor : IFunctor (Σ Fin-Liveness) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
   FFunctor =
      (λ X ((d , b) , finL) → Σ intv ꞉ (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) , {!!} ×
      ((c : FF d b) → (rl : c ⊆ intv) →
      let dd , bb = fin-in-comm (c .fin)
          ddx = commEx (c .sEx .pr₁)
          bbx = commEx (c .sEx .pr₂)
      in X ((ddx , bb) , {!!}) × X ((dd , bbx) , {!!})))
    , (λ f i (g , w , r) → g , w , λ c rl → f _ (r c rl .pr₁) , f _ (r c rl .pr₂))
    , (λ {X} {Y} {Z} f g → refl)
    , λ {X} → refl
 

 ```
