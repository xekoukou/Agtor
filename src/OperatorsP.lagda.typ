#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Operators
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

open import PW-Reducible Msg Secret
open import LivenessP fe Msg Secret 𝓥 𝓦 𝓠
open import Definitions Msg Secret
open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠

open import MultiComm fe Msg Secret 𝓥 𝓦 𝓠 fc-pot

open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot

module _ (fc'₁ : InfInComm×) where

 open InfInComm×P' fc'₁
 open IFunctor₁ FInfInComm×
 open ICoAlgebra₁ FInfInComm×
 open IFinal-CoAlgebra₁ FInfInComm× fc'₁

 module _ (ii : InfInt) (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where

  open IFunctor₂ FInfInt
  open ICoAlgebra₂ FInfInt
  open IFinal-CoAlgebra₂ FInfInt ii

  record OneEx (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
   field
   -- TODO We should be able to not have any internal communication
    fin : FinInComm× d b
    sEx : let dd , bb = finIn→finEx× fin in SingleExComm (fin-ex-comm dd) × SingleExComm (fin-ex-comm bb)

  open OneEx

  open Fin-Liveness stream

  nFinLiv : {d b : Fn ⟨ fc ⟩} → (c : OneEx d b) → Fin-Liveness (d , b) →
   let dd , bb = fin-in-comm (c .fin)
       ddx = fin-ex-comm ((finIn→finEx× (c .fin) .pr₁) ++ (lastOne (c .sEx .pr₁)))
       bbx = fin-ex-comm ((finIn→finEx× (c .fin) .pr₂) ++ (lastOne (c .sEx .pr₂)))
   in Fin-Liveness (dd , bbx) × Fin-Liveness (ddx , bb)
  nFinLiv c fLiv =
   let dd , bb = finIn→finEx× (c .fin)
       ddx = c .sEx .pr₁
       bbx = c .sEx .pr₂
   in (finL-fnEx dd (bb ++ lastOne bbx) fLiv) , (finL-fnEx (dd ++ lastOne ddx) bb fLiv)


  fcn' : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → ℕ → ℕ → ℕ → 𝓤₀ ̇
  fcn' (more step q) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  fcn' (lastOne step) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  fcn' (more step q) (succ n) lk rk = fcn' q n lk rk
  fcn' (lastOne step) (succ zero) lk rk = 𝟙
  fcn' (lastOne step) (succ (succ n)) lk rk = 𝟘

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

  ifcn' : {d b : Fn ⟨ fc ⟩} → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) → ℕ → ℕ → ℕ → 𝓤₀ ̇
  ifcn' (step , _) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  ifcn' (_ , x) (succ n) lk rk = ifcn' ((fcᵢ₁ ⟶ᵢ₁) _ x) n lk rk

  ifcn : {d b : Fn ⟨ fc ⟩} → (q : FinInComm× d b) → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) →
   let dd , bb = finIn→finEx× q
   in SingleExComm (fin-ex-comm dd) × SingleExComm (fin-ex-comm bb) → 𝓤 ⊔ 𝓥 ̇ 
  ifcn (more step₁ s) (step , next) r
   = Σ eq ꞉ (step ＝ step₁) ,(ifcn s (transport (λ z → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (commIn z)) eq ((fcᵢ₁ ⟶ᵢ₁) (commIn step) next)) r)
  ifcn (lastOne step₁) (step , next) (g , h)
   = (step ＝ step₁) × (nIn (((fcᵢ₁ ⟶ᵢ₁) (commIn step) next) .pr₁) ＝ (nEx g) , (nEx h))
   
  _⊆_ : {d b : Fn ⟨ fc ⟩} → OneEx d b → Σ (FInt d b)  + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i)) → 𝓤 ⊔ 𝓥 ̇
  f ⊆ inl x = fcn (f .fin) (x .pr₁) (f .sEx)
  f ⊆ inr x = ifcn (f .fin) (x .pr₁) (f .sEx)


  module RR (fc' : InfExComm) where
   open InfCommP fc'
   open InfInComm×P fc' fc'₁
   open IFunctor FInfExComm
   open ICoAlgebra FInfExComm
   open IFinal-CoAlgebra FInfExComm fc'


   CC : {d b : Fn ⟨ fc ⟩}
    → Fin-Liveness (d , b) → Inf-Liveness d → Inf-Liveness b
    → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → 𝓦 ̇
   CC finL infd infb (inl (x , _ , inf)) =
    let (dd , bb) = finIn→finEx× x
    in ¬ (finL (inl dd) (inl bb) .pr₁ inf)
   CC {d} {b} finL infd infb (inr x)
    =   ¬ infd ((fcᵢ ⟶ᵢ) d (infIn×→infEx₁ d (b , x .pr₁)))
      × ¬ infb ((fcᵢ ⟶ᵢ) b (infIn×→infEx₂ b (d , x .pr₁)))

   FFunctor : IFunctor (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂))) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
   FFunctor =
      (λ X ((d , b) , (finL , infLd , infLb)) → Σ intv ꞉ (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) , (CC finL infLd infLb intv) ×
      ((c : OneEx d b) → (rl : c ⊆ intv) →
      let dd , bb = fin-in-comm (c .fin)
          ddx = fin-ex-comm ((finIn→finEx× (c .fin) .pr₁) ++ (lastOne (c .sEx .pr₁)))
          bbx = fin-ex-comm ((finIn→finEx× (c .fin) .pr₂) ++ (lastOne (c .sEx .pr₂)))
          (nfinL₁ , nfinL₂) = nFinLiv c finL
      in   X ((dd , bbx) , nfinL₁ , infL++ infLd (finIn→finEx× (c .fin) .pr₁) , infL++ infLb ((finIn→finEx× (c .fin) .pr₂) ++ (lastOne (c .sEx .pr₂))))
         × X ((ddx , bb) , nfinL₂ , (infL++ infLd ((finIn→finEx× (c .fin) .pr₁) ++ (lastOne (c .sEx .pr₁)))) , (infL++ infLb (finIn→finEx× (c .fin) .pr₂)))))
    , (λ f i (g , w , r) → g , w , λ c rl → f _ (r c rl .pr₁) , f _ (r c rl .pr₂))
    , (λ {X} {Y} {Z} f g → refl)
    , λ {X} → refl
 
  

 ```
