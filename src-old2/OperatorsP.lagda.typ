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
open ΣPred

module OperatorsP (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

open import PW-Reducible Msg Secret
open import LivenessP fe Msg Secret 𝓥 𝓦 𝓠
open import Definitions Msg Secret
open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠



open import MultiComm fe Msg Secret 𝓥 𝓦 𝓠 fc-pot

open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot

open import FCP Msg Secret 𝓥
open FC
open FC₂
open Pot {fc-pot}

module _ (fc'₁ : InfInComm×) where

 open InfInComm×P' fc'₁
 open IFunctor₁ FInfInComm×
 open ICoAlgebra₁ FInfInComm×
 open IFinal-CoAlgebra₁ FInfInComm× fc'₁

 module _ (ii : InfInt) (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where

  open IFunctor₂ FInfInt
  open ICoAlgebra₂ FInfInt
  open IFinal-CoAlgebra₂ FInfInt ii


  fcn : {d b : Fn ⟨ fc ⟩} → Σ (FInt d b) → ℕ → ℕ × ℕ → 𝓤₀ ̇
  fcn (more step x , (sint , _) , _) zero k = k ∈ₚ sint .pr₂
  fcn (none , (_ , yf)) zero k = k ∈ₚᵢ yf
  fcn (more step x , (y , ys) , yf) (succ n) k = fcn (x , ys , yf) n k
  fcn (none , y) (succ n) k = 𝟘

  ifcn : {d b : Fn ⟨ fc ⟩} → Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i) → ℕ → ℕ × ℕ → 𝓤₀ ̇
  ifcn ((step , _) , sint , _) zero k = k ∈ₚ sint .pr₂
  ifcn ((_ , x) , _ , y) (succ n) k = ifcn (((fcᵢ₁ ⟶ᵢ₁) _ x) , (fcᵢ₂ ⟶ᵢ₂) _ y) n k 

  CN : {d b : Fn ⟨ fc ⟩} → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → ℕ → ℕ × ℕ → 𝓤₀ ̇
  CN (inl x) y z = fcn x y z
  CN (inr x) y z = ifcn x y z

  tt : ∀{d b} → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → FinInComm× d b + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)
  tt (inl x) = inl (x .pr₁)
  tt (inr x) = inr (x .pr₁)


  data OneEx (d : Fn ⟨ fc ⟩) (b : Fn ⟨ fc ⟩) (c : Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) : 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺ ̇  where
   cd : (nmb nsd nsb : ℕ) → (sex : Σ s ꞉ SingleExComm (fin-ex-comm (finIn→finEx× (in-cut (tt c) nmb) .pr₁)) , (nEx s ＝ nsd)) → (cnd : CN c nmb (nsd , nsb)) → OneEx d b c
   cb : (nmb nsd nsb : ℕ) → (sex : Σ s ꞉ SingleExComm (fin-ex-comm (finIn→finEx× (in-cut (tt c) nmb) .pr₂)) , (nEx s ＝ nsb)) → (cnd : CN c nmb (nsd , nsb)) → OneEx d b c

  open Fin-Liveness stream
  open Pot₁ fe {fc-pot}

  nFinLivT : (d b : Fn ⟨ fc ⟩) → ∀ q → (c : OneEx d b q) → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
  nFinLivT d b q (cd nmb nsd nsb sex cnd)
   = let inc = in-cut (tt q) nmb
         dd , bb = fin-in-comm inc
         ddx = fin-ex-comm (finIn→finEx× inc .pr₁ ++ (more (sex .pr₁) none))
     in Fin-Liveness (ddx , (bb at nsb))
  nFinLivT d b q (cb nmb nsd nsb sex cnd)
     = let inc = in-cut (tt q) nmb
           dd , bb = fin-in-comm inc
           bbx = fin-ex-comm (finIn→finEx× inc .pr₂ ++ (more (sex .pr₁) none))
     in Fin-Liveness ((dd at nsd) , bbx)
  

  nFinLiv : {d b : Fn ⟨ fc ⟩} → ∀{q} → (c : OneEx d b q) → Fin-Liveness (d , b) → nFinLivT d b q c
  nFinLiv {d} {b} {q} (cd nmb nsd nsb sex cnd) fLiv
   = let inc = in-cut (tt q) nmb
         dd , bb = finIn→finEx× inc
     in {!!}
  nFinLiv {d} {b} {q} (cb nmb nsd nsb sex cnd) fLiv = {!!}

--    = let inc = in-cut q (nmb c)
--          dd , bb = finIn→finEx× inc
--      in (finL-fnEx dd (bb ++ more (sb c) none) fLiv) , finL-fnEx (dd ++ more (sd c) none) bb fLiv
 
-- --   module RR (fc' : InfExComm) where
-- --    open InfCommP fc'
-- --    open InfInComm×P fc' fc'₁
-- --    open IFunctor FInfExComm
-- --    open ICoAlgebra FInfExComm
-- --    open IFinal-CoAlgebra FInfExComm fc'



-- --    CC : {d b : Fn ⟨ fc ⟩}
-- --     → Fin-Liveness (d , b) → Inf-Liveness d → Inf-Liveness b
-- --     → (FinInComm× d b × ((ℕ → ℕ) × 𝟚) + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)) → 𝓦 ̇
-- --    CC finL infd infb (inl (x , f𝕟)) =
-- --     let (dd , bb) = finIn→finEx× x
-- --     in ¬ (finL dd bb .pr₁ f𝕟)
-- --    CC {d} {b} finL infd infb (inr x)
-- --     =   ¬ infd ((fcᵢ ⟶ᵢ) d (infIn×→infEx₁ d (b , x)))
-- --       × ¬ infb ((fcᵢ ⟶ᵢ) b (infIn×→infEx₂ b (d , x)))

-- --    I = (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂)))


-- --    tt2 : ∀{d b} → (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) → (FinInComm× d b × ((ℕ → ℕ) × 𝟚)) + Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b)
-- --    tt2 (inl x) = inl (x .pr₁ , x .pr₂ .pr₂)
-- --    tt2 (inr x) = inr (x .pr₁)

-- --    F& : IFunctor (Σ e ꞉ _ , Fin-Liveness e × (Inf-Liveness (e .pr₁)) × (Inf-Liveness (e .pr₂))) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
-- --    F& =
-- --       (λ X ((d , b) , (finL , infLd , infLb)) → Σ intv ꞉ (Σ (FInt d b) + (Σ i ꞉ Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b) , Fnᵢ₂ ⟨ fcᵢ₂ ⟩ᵢ₂ (d , b , i))) , (CC finL infLd infLb (tt2 intv)) ×
-- --       ((c : OneEx d b (tt intv)) →
-- --         let inc = in-cut (tt intv) (nmb c)
-- --             dd , bb = fin-in-comm inc
-- --             fdd , fbb = finIn→finEx× inc
-- --             fddx , fbbx = fdd ++ more (sd c) none , fbb ++ more (sb c) none
-- --             ddx = fin-ex-comm fddx
-- --             bbx = fin-ex-comm fbbx
-- --             (nfinL₁ , nfinL₂) = nFinLiv c finL
-- --         in X ((dd , bbx) , nfinL₁ , infL++ infLd fdd , infL++ infLb fbbx) × X ((ddx , bb) , nfinL₂ , infL++ infLd fddx , infL++ infLb fbb) ))
-- --     , (λ f i ((g , w , r)) → g , w , λ c → f _ (r c .pr₁) , f _ (r c .pr₂))
-- --     , (λ {X} {Y} {Z} f g → refl)
-- --     , λ {X} → refl


-- --    module _ (fc& : IFinal-CoAlgebra F&) where
-- --     open IFunctor₃ F&
-- --     open ICoAlgebra₃ F&
-- --     open IFinal-CoAlgebra₃ F& fc&



-- -- -- -- ₀ is right , ₁ is left
-- -- -- qq : ∀{d b} → Σ (FInt d b) × 𝟙 {𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺} → Fn (Σ (FInt d b) × 𝟙 {𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺})
-- -- -- qq {d} {b} ((more (c← nd nb msg bsmd bsab) x , (fi , v) , f , ₀) , _) = {!!} , ((pset d) & pset b ) , ((Mp (foc d) ∨ Mp (foc b)) , λ { x (inl c) → {!fm (foc d) x c!} ; x (inr c) → {!!}}) , {!!}
-- -- -- qq {d} {b} ((more (c← nd nb msg bsmd bsab) x , (fi , v) , f , ₁) , _) = {!!}
-- -- -- qq {d} {b} ((more (c→ nd nb msg bsad bsmb) x , (fi , v) , f , two) , _) = {!!}
-- -- -- qq {d} {b} ((none , (_ , f , two)) , _) = {!!}



-- -- --     ee : (Σ (Fnᵢ₃ ⟨ fcᵢ₃ ⟩ᵢ₃)) × ℕ × ℕ → Fn ((Σ (Fnᵢ₃ ⟨ fcᵢ₃ ⟩ᵢ₃)) × ℕ × ℕ)
-- -- --     ee ((((d , b) , _) , inl (more step x , fint) , cc , fo) , n , k) = {!!}
-- -- --     ee ((((d , b) , _) , inl (none , _ , f , ₀) , cc , fo) , n , zero)
-- -- --      = {!!} , ((pset d) & pset b ) , ((Mp (foc d) ∨ Mp (foc b)) , l1) , {!!} where
-- -- --       l1 : ∀ x → < (Mp (foc d) ∨ Mp (foc b)) > x → Σ (Fnᵢ₃ ⟨ fcᵢ₃ ⟩ᵢ₃) × ℕ × ℕ
-- -- --       l1 x (inl c) = ({!!} , (fcᵢ₃ ⟶ᵢ₃) {!!} {!!}) , {!!} , {!!} where
-- -- --        1ex = 𝟙ex 0 {!!} {!!} {!!}
-- -- --       l1 x (inr c) = {!!}
-- -- --       l2 : {!!} → {!!} → {!!}
-- -- --       l2 = {!!}
-- -- --     ee ((((d , b) , _) , inl (none , _ , f , ₁) , cc , fo) , n , zero) = {!!}
-- -- --     ee ((((d , b) , _) , inl (none , _ , f , ₀) , cc , fo) , n , succ k) = {!!}
-- -- --     ee ((((d , b) , _) , inl (none , _ , f , ₁) , cc , fo) , n , succ k) = {!!}
-- -- --     ee ((((d , b) , _) , inr x , cc , f) , n , k) = {!!}










-- -- -- ```
