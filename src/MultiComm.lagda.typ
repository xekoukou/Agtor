
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

module MultiComm (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

open import Definitions Msg Secret
open import LivenessP fe Msg Secret 𝓥 𝓦 𝓠
open import PW-Reducible Msg Secret

open ΣPred
open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠


open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot

open import FCP Msg Secret 𝓥 ⟨ fc ⟩
open FC
open Pot {fc-pot}
open Pot₁ fe {fc-pot}


data SingleExComm (d : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
 ←m : (n : ℕ) → let fd = foc (d at n)
                in (msg : S×Msg) → (bsm : < Mp fd > msg)
                → SingleExComm d
 →a : (n : ℕ) → let fd = foc (d at n)
                in (msg : S×Msg) → (bsa : < Ap fd > msg)
                → SingleExComm d

commEx : {d : Fn ⟨ fc ⟩} → SingleExComm d → Fn ⟨ fc ⟩
commEx {d} (←m n msg bsm) = let fd = foc (d at n)
                            in (fc ⟶) (fm fd msg bsm)
commEx {d} (→a n msg bsa) = let fd = foc (d at n)
                            in (fc ⟶) (fa fd msg bsa)

commEx' : {d : Fn ⟨ fc ⟩} → SingleExComm d → Fn ⟨ fc ⟩
commEx' {d} step@(←m n msg bsm) = let fd = foc (d at n)
                                  in (replace d at n) (commEx step)
commEx' {d} step@(→a n msg bsa) = let fd = foc (d at n)
                                  in (replace d at n) (commEx step)


data FinExComm (d : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
 more : (step : SingleExComm d) → FinExComm (commEx step) → FinExComm d
 lastOne : (step : SingleExComm d) → FinExComm d

fin-ex-comm : {d : Fn ⟨ fc ⟩} → FinExComm d → Fn ⟨ fc ⟩
fin-ex-comm (more step s) = fin-ex-comm s
fin-ex-comm (lastOne step) = commEx step

fin-ex-comm-m : {d : Fn ⟨ fc ⟩} → FinExComm d + 𝟙 {𝓤₀} → Fn ⟨ fc ⟩
fin-ex-comm-m (inl x) = fin-ex-comm x 
fin-ex-comm-m {d} (inr x) = d

fin-ex-comm' : {d : Fn ⟨ fc ⟩} → FinExComm d → Fn ⟨ fc ⟩
fin-ex-comm' {d} (more (←m n msg bsm) x) = (replace d at n) (fin-ex-comm' x)
fin-ex-comm' {d} (more (→a n msg bsa) x) = (replace d at n) (fin-ex-comm' x)
fin-ex-comm' {d} (lastOne step) = commEx' step


_++_ : {d : Fn ⟨ fc ⟩} → (x : FinExComm d) → (y : FinExComm (fin-ex-comm x))  → FinExComm d
more step x ++ y = let v = x ++ y in more step v
lastOne step ++ y = more step y


_++ₘ_ : {d : Fn ⟨ fc ⟩} → (x : FinExComm d) → (y : FinExComm (fin-ex-comm x) + 𝟙 {𝓤₀})  → FinExComm d
x ++ₘ inl y = x ++ y
x ++ₘ inr y = x


module _ where

 FInfExComm : IFunctor (Fn ⟨ fc ⟩) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
 FInfExComm =
  (λ X i → Σ step ꞉ SingleExComm i , X (commEx step))
  , (λ f i v → v .pr₁ , f (commEx (v .pr₁)) (v .pr₂))
  , (λ {X} {Y} {Z} f g → refl)
  , λ {X} → refl
 
 InfComm = IFinal-CoAlgebra FInfExComm

 module InfCommP (fc' : InfComm) where

  open IFunctor FInfExComm
  open ICoAlgebra FInfExComm
  open IFinal-CoAlgebra FInfExComm fc'

  𝟙' = 𝟙 {(𝓤 ⁺) ⊔ ((𝓥 ⁺) ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓠 ⁺)}

  g : Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙') → Fn (Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙'))
  g (pt@(nx , ps , foc) , inr x) = ((fc ⟶) nx , inr ⋆) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆
  g (pt@(nx , ps , foc) , inl (←m zero msg bsm , d)) = ((fc ⟶) ((fm foc) msg bsm) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , (((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆)
  g (pt@(nx , ps , foc) , inl (→a zero msg bsa , d)) = ((fc ⟶) ((fa foc) msg bsa) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , ((((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆))
  g (pt@(nx , ps , foc) , inl (←m (succ n) msg bsm , d)) = (((fc ⟶) nx) , inl (←m n msg bsm , d)) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆
  g (pt@(nx , ps , foc) , inl (→a (succ n) msg bsa , d)) = (((fc ⟶) nx) , inl (→a n msg bsa , d)) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆

  g-co : CoAlgebra Fpot
  g-co = (Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙')) , g


  module _ where
  
   open CoAlgebra₂ Fpot g-co fc
   open Morphism

   inf-comm : ∀ d → Fnᵢ ⟨ fcᵢ ⟩ᵢ d → ⟨ fc ⟩
   inf-comm d cond = ((uni g-co .pr₁) ↓) (d , inl cond)
  

```


```agda

data SingleInComm× (d b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
 c← : (nd nb : ℕ) →
       let fd = foc (d at nd)
           fb = foc (b at nb)
       in (msg : S×Msg) → (bsmd : < Mp fd > msg)
                        → (bsab : < Ap fb > msg)
                        → SingleInComm× d b
 c→ : (nd nb : ℕ) →
       let fd = foc (d at nd)
           fb = foc (b at nb)
       in (msg : S×Msg) → (bsad : < Ap fd > msg)
                        → (bsmb : < Mp fb > msg)
                        → SingleInComm× d b

SInt :  {d b : Fn ⟨ fc ⟩} → SingleInComm× d b → 𝓤₀ ̇
SInt (c← nd nb msg bsmd bsab) = Σ n ꞉ ℕ , BFun n nd nb
SInt (c→ nd nb msg bsad bsmb) = Σ n ꞉ ℕ , BFun n nd nb

sIn→sEx× : {d b : Fn ⟨ fc ⟩} → SingleInComm× d b → SingleExComm d × SingleExComm b
sIn→sEx× {d} {b} (c← nd nb msg bsmd bsab) = (←m nd msg bsmd) , (→a nb msg bsab)
sIn→sEx× {d} {b} (c→ nd nb msg bsad bsmb) = (→a nd msg bsad) , (←m nb msg bsmb)

commIn : {d b : Fn ⟨ fc ⟩} → SingleInComm× d b → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩
commIn x = let dd , bb = sIn→sEx× x in commEx dd , commEx bb

commIn' : {d b : Fn ⟨ fc ⟩} → SingleInComm× d b → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩
commIn' x = let dd , bb = sIn→sEx× x in commEx' dd , commEx' bb


data FinInComm× (d b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
 more : (step : SingleInComm× d b) → let nd , nb = commIn step in FinInComm× nd nb → FinInComm× d b
 lastOne : (step : SingleInComm× d b) → FinInComm× d b

FInt :  (d b : Fn ⟨ fc ⟩) → FinInComm× d b → 𝓤₀ ̇
FInt d b (more step g) = SInt step × FInt _ _ g
FInt d b (lastOne step) = SInt step

finIn→finEx× : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → FinExComm d × FinExComm b
finIn→finEx× {d} {b} (more step x)
 = let dd , bb = sIn→sEx× step
       mdd , mbb = finIn→finEx× x
   in more dd mdd , more bb mbb
finIn→finEx× {d} {b} (lastOne step)
 = let dd , bb = sIn→sEx× step in lastOne dd , lastOne bb

fin-in-comm : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩
fin-in-comm x
 = let a , b = finIn→finEx× x
   in fin-ex-comm a , fin-ex-comm b

fin-in-comm' : {d b : Fn ⟨ fc ⟩} → FinInComm× d b → Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩
fin-in-comm' {d} {b} (more (c← nd nb msg bsmd bsab) x)
 = let dd , bb = fin-in-comm' x
   in (replace d at nd) dd , (replace b at nb) bb
fin-in-comm' {d} {b} (more (c→ nd nb msg bsad bsmb) x)
 = let dd , bb = fin-in-comm' x
   in (replace d at nd) dd , (replace b at nb) bb
fin-in-comm' {d} {b} (lastOne step) = commIn' step



data FinLivC : 𝓤₀ ̇ where
 start : FinLivC
 sIn : FinLivC
 fEx× : FinLivC
 fEx← : FinLivC
 fEx→ : FinLivC


data FinLivComm× (d b : Fn ⟨ fc ⟩) (k : FinLivC) : 𝓤 ⊔ 𝓥 ̇  where
  sIn : (step : FinInComm× d b) →
             let dd , bb = fin-in-comm step
             in FinLivComm× dd bb sIn → (eq : ¬ (k ＝ sIn)) → FinLivComm× d b k
  fEx× : (fxd : FinExComm d) → (fxb : FinExComm b) → FinLivComm× (fin-ex-comm fxd) (fin-ex-comm fxb) fEx× → (eq : (k ＝ sIn) + (k ＝ start)) → FinLivComm× d b k
  fEx← : (fxd : FinExComm d) → FinLivComm× (fin-ex-comm fxd) b fEx← → (eq : (k ＝ sIn) + (k ＝ start)) → FinLivComm× d b k
  fEx→ : (fxb : FinExComm b) → FinLivComm× d (fin-ex-comm fxb) fEx→ → (eq : (k ＝ sIn) + (k ＝ start)) → FinLivComm× d b k
  here : FinLivComm× d b k

FinLivComm×' : (d b : Fn ⟨ fc ⟩) → 𝓤 ⊔ 𝓥 ̇
FinLivComm×' d b = FinLivComm× d b start

finLiv→finEx× : {d b : Fn ⟨ fc ⟩} → ∀{k} → FinLivComm× d b k → (FinExComm d + 𝟙 {𝓤₀}) × (FinExComm b + 𝟙 {𝓤₀})
finLiv→finEx× (sIn step x eq)
 = let nx , ny = finLiv→finEx× x
       fxd , fxb = finIn→finEx× step
   in inl (fxd ++ₘ nx) , inl (fxb ++ₘ ny)
finLiv→finEx× (fEx× fxd fxb x eq)
 = let nx , ny = finLiv→finEx× x
   in inl (fxd ++ₘ nx) , inl (fxb ++ₘ ny)
finLiv→finEx× (fEx← fxd x eq)
 = let nx , ny = finLiv→finEx× x
   in inl (fxd ++ₘ nx) , ny
finLiv→finEx× (fEx→ fxb x eq)
 = let nx , ny = finLiv→finEx× x
   in nx , inl (fxb ++ₘ ny)
finLiv→finEx× here = inr ⋆ , inr ⋆

module _ (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where
 open Liveness fc-pot stream PSet-PSet-reducible

 Fin-Liveness : {d b : Fn ⟨ fc ⟩} → FinLivComm×' d b → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
 Fin-Liveness {d} {b} x = let a , b = finLiv→finEx× x
                          in Cond-Liveness (fin-ex-comm-m a) (fin-ex-comm-m b)






module _ where

 FInfInComm× : IFunctor (Fn ⟨ fc ⟩ × Fn ⟨ fc ⟩) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
 FInfInComm× =
    (λ X i → Σ step ꞉ SingleInComm× (i .pr₁) (i .pr₂) , X (commIn step))
  , (λ f i x → (x .pr₁) , (f (commIn (x .pr₁)) (x .pr₂)))
  , (λ f g → refl)
  , refl

 open IFunctor₁ FInfInComm×
 open ICoAlgebra₁ FInfInComm×
 InfInComm× = IFinal-CoAlgebra FInfInComm×


 module InfInComm×P (fc' : InfComm) (fc'₁ : InfInComm×) where

  open IFinal-CoAlgebra₁ FInfInComm× fc'₁
  open IFunctor FInfExComm
  open ICoAlgebra FInfExComm
  open IFinal-CoAlgebra FInfExComm fc'


  D₁ : ISet _ (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)  → ISet (Fn ⟨ fc ⟩) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
  D₁ x = λ i → Σ v ꞉ Fn ⟨ fc ⟩ , x (i , v) 

  D₂ : ISet _ (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)  → ISet (Fn ⟨ fc ⟩) (𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ⁺)
  D₂ x = λ i → Σ v ꞉ Fn ⟨ fc ⟩ , x (v , i) 

  q₁ : D₁ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁) ⟼ Fnᵢ (D₁ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁))
  q₁ d (b , step , nx) = let sd , sb = sIn→sEx× step in sd , (commEx sb) , (fcᵢ₁ ⟶ᵢ₁) (commEx sd , commEx sb) nx

  q₂ : D₂ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁) ⟼ Fnᵢ (D₂ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁))
  q₂ b (d , step , nx) = let sd , sb = sIn→sEx× step in sb , (commEx sd) , (fcᵢ₁ ⟶ᵢ₁) (commEx sd , commEx sb) nx

  q₁-co : ICoAlgebra FInfExComm
  q₁-co = (D₁ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁)) , q₁

  q₂-co : ICoAlgebra FInfExComm
  q₂-co = (D₂ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁)) , q₂

  module _ where
 
   open IMorphism FInfExComm q₁-co fcᵢ

   infIn×→infEx₁ : D₁ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁) ⟼ ⟨ fcᵢ ⟩ᵢ 
   infIn×→infEx₁ d cond = (uniᵢ q₁-co .pr₁ ↓ᵢ) d cond

   open IMorphism₁ FInfExComm q₂-co fcᵢ

   infIn×→infEx₂ : D₂ (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁) ⟼ ⟨ fcᵢ ⟩ᵢ 
   infIn×→infEx₂ d cond = (uniᵢ q₂-co .pr₁ ↓ᵢ₁) d cond


 module InfIntP (fc'₁ : InfInComm×) where
  open IFinal-CoAlgebra₁ FInfInComm× fc'₁

  FInfInt : IFunctor (Σ d ꞉ _ , Σ b ꞉ _ , (Fnᵢ₁ ⟨ fcᵢ₁ ⟩ᵢ₁ (d , b))) 𝓤
  FInfInt =
     (λ X i → SInt (i .pr₂ .pr₂ .pr₁) × let dd , bb = commIn (i .pr₂ .pr₂ .pr₁) in X (_ , _ , (fcᵢ₁ ⟶ᵢ₁) (_ , _) (i .pr₂ .pr₂ .pr₂)))
   , (λ f i (sint , x) → sint , (f _ x))
   , (λ f g → refl)
   , refl

  InfInt = IFinal-CoAlgebra FInfInt


