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


  fcn' : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → ℕ → ℕ → ℕ → 𝓤₀ ̇
  fcn' (more step q) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  fcn' none zero lk rk = 𝟙
  fcn' (more step q) (succ n) lk rk = fcn' q n lk rk
  fcn' none (succ k) lk rk = 𝟘

  ifcn' : {d b : Fn ⟨ fc ⟩} → Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) → ℕ → ℕ → ℕ → 𝓤₀ ̇
  ifcn' (step , _) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  ifcn' (_ , x) (succ n) lk rk = ifcn' ((fcᵢ₁ ⟶ᵢ₁) _ x) n lk rk

  CN : {d b : Fn ⟨ fc ⟩} → FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) → ℕ → ℕ → ℕ → 𝓤₀ ̇
  CN (inl x) = fcn' x
  CN (inr x) = ifcn' x

-- TODO Here we have FinInComm× d b + 𝟙 . FIX THIS
  record OneEx (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) (c : FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)) : 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ̇  where
   field
    nmb : ℕ
    sd : SingleExComm (fin-ex-comm (finIn→finEx× (in-cut c nmb) .pr₁))
    sb : SingleExComm (fin-ex-comm (finIn→finEx× (in-cut c nmb) .pr₂))
    cnd : CN c nmb (nEx sd) (nEx sb)

  open OneEx



-- --   data OneEx (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) : (FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ̇  where
-- --    noIn : ∀{c} → (sd : SingleExComm d) → (sb : SingleExComm b) → CN c 0 (nEx sd) (nEx sb) → OneEx d b c
-- --    someIn : ∀{c} → (n : ℕ) → let dd , bb = finIn→finEx× (in-cut' c n) in (sd : SingleExComm (fin-ex-comm dd)) → (sb : SingleExComm (fin-ex-comm bb)) → CN c (succ n) (nEx sd) (nEx sb) → OneEx d b c

-- --   open OneEx

  open Fin-Liveness stream

  nFinLivT : (d b : Fn ⟨ fc ⟩) → ∀ q → (c : OneEx d b q) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
  nFinLivT d b q c =
   let inc = in-cut q (nmb c)
       dd , bb = fin-in-comm inc
       ddx = fin-ex-comm (finIn→finEx× inc .pr₁ ++ (more (sd c) none))
       bbx = fin-ex-comm (finIn→finEx× inc .pr₂ ++ (more (sb c) none))
   in Fin-Liveness (dd , bbx) × Fin-Liveness (ddx , bb)

  nFinLiv : {d b : Fn ⟨ fc ⟩} → ∀{q} → (c : OneEx d b q) → Fin-Liveness (d , b) → nFinLivT d b q c
  nFinLiv {d} {b} {q} c fLiv
   = let inc = in-cut q (nmb c)
         dd , bb = finIn→finEx× inc
     in (finL-fnEx dd (bb ++ more (sb c) none) fLiv) , finL-fnEx (dd ++ more (sd c) none) bb fLiv
 
  module RR (fc' : InfExComm) where
   open InfCommP fc'
   open InfInComm×P fc' fc'₁
   open IFunctor FInfExComm
   open ICoAlgebra FInfExComm
   open IFinal-CoAlgebra FInfExComm fc'


   CC : {d b : Fn ⟨ fc ⟩}
    → Fin-Liveness (d , b) → Inf-Liveness d → Inf-Liveness b
    → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → 𝓦 ̇
   CC finL infd infb (inl (x , _ , f𝕟)) =
    let (dd , bb) = finIn→finEx× x
    in ¬ (finL dd bb .pr₁ f𝕟)
   CC {d} {b} finL infd infb (inr x)
    =   ¬ infd ((fcᵢ ⟶ᵢ) d (infIn×→infEx₁ d (b , x .pr₁)))
      × ¬ infb ((fcᵢ ⟶ᵢ) b (infIn×→infEx₂ b (d , x .pr₁)))

   I = (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂)))

   tt : ∀{d b} → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)
   tt (inl x) = inl (x .pr₁)
   tt (inr x) = inr (x .pr₁)


   FFunctor : IFunctor (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂))) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
   FFunctor =
      (λ X ((d , b) , (finL , infLd , infLb)) → Σ intv ꞉ (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) , (CC finL infLd infLb intv) ×
      ((c : OneEx d b (tt intv)) →
        let inc = in-cut (tt intv) (nmb c)
            dd , bb = fin-in-comm inc
            fdd , fbb = finIn→finEx× inc
            fddx , fbbx = fdd ++ more (sd c) none , fbb ++ more (sb c) none
            ddx = fin-ex-comm fddx
            bbx = fin-ex-comm fbbx
            (nfinL₁ , nfinL₂) = nFinLiv c finL
        in X ((dd , bbx) , nfinL₁ , infL++ infLd fdd , infL++ infLb fbbx) × X ((ddx , bb) , nfinL₂ , infL++ infLd fddx , infL++ infLb fbb) ))
    , (λ f i ((g , w , r)) → g , w , λ c → f _ (r c .pr₁) , f _ (r c .pr₂))
    , (λ {X} {Y} {Z} f g → refl)
    , λ {X} → refl 

```
