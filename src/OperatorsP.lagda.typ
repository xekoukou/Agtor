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
  fcn' (lastOne step) zero lk rk = (lk ≤ (nIn step .pr₁)) × (rk ≤ (nIn step .pr₂))
  fcn' (more step q) (succ n) lk rk = fcn' q n lk rk
  fcn' (lastOne step) (succ zero) lk rk = 𝟙
  fcn' (lastOne step) (succ (succ n)) lk rk = 𝟘

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
    sd : SingleExComm (in-cut c nmb >>ₘ' d ∣ (λ r → fin-ex-comm (finIn→finEx× r .pr₁)))
    sb : SingleExComm (in-cut c nmb >>ₘ' b ∣ (λ r → fin-ex-comm (finIn→finEx× r .pr₂)))
    cnd : CN c nmb (nEx sd) (nEx sb)

  open OneEx



-- --   data OneEx (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) : (FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ̇  where
-- --    noIn : ∀{c} → (sd : SingleExComm d) → (sb : SingleExComm b) → CN c 0 (nEx sd) (nEx sb) → OneEx d b c
-- --    someIn : ∀{c} → (n : ℕ) → let dd , bb = finIn→finEx× (in-cut' c n) in (sd : SingleExComm (fin-ex-comm dd)) → (sb : SingleExComm (fin-ex-comm bb)) → CN c (succ n) (nEx sd) (nEx sb) → OneEx d b c

-- --   open OneEx

  open Fin-Liveness stream

-- TODO Try to simplify further
  nFinLivT : (d b : Fn ⟨ fc ⟩) → ∀ q → (c : OneEx d b q) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
  nFinLivT d b q c =
   let inc = in-cut q (nmb c)
       dd , bb = inc >>ₘ' (d , b) ∣ λ inc → fin-in-comm inc
       ddx , bbx = (inc >⟨ (λ inc → (SingleExComm (inc >>ₘ' d ∣ (λ r → fin-ex-comm (finIn→finEx× r .pr₁))) → SingleExComm (inc >>ₘ' b ∣ (λ r → fin-ex-comm (finIn→finEx× r .pr₂))) → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩)) ⟩>ₘ (λ sdc sbc → fin-ex-comm (lastOne sdc) , fin-ex-comm (lastOne sbc)) ∣ λ inc → λ sdc sbc → (fin-ex-comm (finIn→finEx× inc .pr₁ ++ lastOne sdc)) , (fin-ex-comm (finIn→finEx× inc .pr₂ ++ lastOne sbc))) (sd c) (sb c)
   in Fin-Liveness (dd , bbx) × Fin-Liveness (ddx , bb)

-- -- -- TODO Try to simplify further
-- --   nFinLivT : (d b : Fn ⟨ fc ⟩) → ∀ q → (c : OneEx d b q) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
-- --   nFinLivT d b q (noIn sd sb x) = Fin-Liveness (d , fin-ex-comm (lastOne sb)) × Fin-Liveness (fin-ex-comm (lastOne sd) , b)
-- --   nFinLivT d b q (someIn n sd sb x)
-- --    = let inc = in-cut' q n
-- --          dd , bb = fin-in-comm inc
-- --          ddx = fin-ex-comm ((finIn→finEx× inc .pr₁) ++ (lastOne sd))
-- --          bbx = fin-ex-comm ((finIn→finEx× inc .pr₂) ++ (lastOne sb))
-- --      in Fin-Liveness (dd , bbx) × Fin-Liveness (ddx , bb)
 
  nFinLiv : {d b : Fn ⟨ fc ⟩} → ∀{q} → (c : OneEx d b q) → Fin-Liveness (d , b) → nFinLivT d b q c
  nFinLiv (noIn sd sb x) fLiv = (finL-fnEx-m (inr _) (inl (lastOne sb)) fLiv) , (finL-fnEx-m (inl (lastOne sd)) (inr ⋆) fLiv)
  nFinLiv {d} {b} {q} (someIn n sd sb x) fLiv
   = let inc = in-cut' q n
     in (finL-fnEx-m (inl (finIn→finEx× inc .pr₁)) (inl ((finIn→finEx× inc .pr₂) ++ lastOne sb)) fLiv) , (finL-fnEx-m (inl ((finIn→finEx× inc .pr₁) ++ lastOne sd)) (inl ((finIn→finEx× inc .pr₂))) fLiv)


 --  nFinLiv : {d b : Fn ⟨ fc ⟩} → ∀{q} → (c : OneEx d b q) → Fin-Liveness (d , b) → nFinLivT d b q c
 --  nFinLiv (noIn sd sb x) fLiv = (finL-fnEx-m (inr _) (inl (lastOne sb)) fLiv) , (finL-fnEx-m (inl (lastOne sd)) (inr ⋆) fLiv)
 --  nFinLiv {d} {b} {q} (someIn n sd sb x) fLiv
 --   = let inc = in-cut' q n
 --     in (finL-fnEx-m (inl (finIn→finEx× inc .pr₁)) (inl ((finIn→finEx× inc .pr₂) ++ lastOne sb)) fLiv) , (finL-fnEx-m (inl ((finIn→finEx× inc .pr₁) ++ lastOne sd)) (inl ((finIn→finEx× inc .pr₂))) fLiv)

 --  module RR (fc' : InfExComm) where
 --   open InfCommP fc'
 --   open InfInComm×P fc' fc'₁
 --   open IFunctor FInfExComm
 --   open ICoAlgebra FInfExComm
 --   open IFinal-CoAlgebra FInfExComm fc'


 --   CC : {d b : Fn ⟨ fc ⟩}
 --    → Fin-Liveness (d , b) → Inf-Liveness d → Inf-Liveness b
 --    → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → 𝓦 ̇
 --   CC finL infd infb (inl (x , _ , inf)) =
 --    let (dd , bb) = finIn→finEx× x
 --    in ¬ (finL (inl dd) (inl bb) .pr₁ inf)
 --   CC {d} {b} finL infd infb (inr x)
 --    =   ¬ infd ((fcᵢ ⟶ᵢ) d (infIn×→infEx₁ d (b , x .pr₁)))
 --      × ¬ infb ((fcᵢ ⟶ᵢ) b (infIn×→infEx₂ b (d , x .pr₁)))

 --   I = (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂)))
   
 --   DD :  {d b : Fn ⟨ fc ⟩} → ∀{q} → (c : OneEx d b q) → (X : ISet I (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)) → {!!} ̇
 --   DD {d} {b} {q} (noIn sd sb x) X = X {!!} × X {!!}
 --   DD {d} {b} {q} (someIn n sd sb x) X = X {!!} × X {!!}

 -- --   FFunctor : IFunctor (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂))) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
 -- --   FFunctor =
 -- --      (λ X ((d , b) , (finL , infLd , infLb)) → Σ intv ꞉ (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) , (CC finL infLd infLb intv) ×
 -- --      ((c : OneEx d b ?) →
 -- --      let inc = in-cut' q n
 -- --          dd , bb = fin-in-comm inc
 -- --          ddx = fin-ex-comm ((finIn→finEx× inc .pr₁) ++ (lastOne sd))
 -- --          bbx = fin-ex-comm ((finIn→finEx× inc .pr₂) ++ (lastOne sb))
 -- --          (nfinL₁ , nfinL₂) = nFinLiv c finL
 -- --      in   X ((dd , bbx) , nfinL₁ , infL++ infLd (finIn→finEx× (c .fin) .pr₁) , infL++ infLb ((finIn→finEx× (c .fin) .pr₂) ++ (lastOne (c .sEx .pr₂))))
 -- --         × X ((ddx , bb) , nfinL₂ , (infL++ infLd ((finIn→finEx× (c .fin) .pr₁) ++ (lastOne (c .sEx .pr₁)))) , (infL++ infLb (finIn→finEx× (c .fin) .pr₂)))))
 -- --    , (λ f i (g , w , r) → g , w , λ c rl → f _ (r c rl .pr₁) , f _ (r c rl .pr₂))
 -- --    , (λ {X} {Y} {Z} f g → refl)
 -- --    , λ {X} → refl
 
  

 -- -- ```
