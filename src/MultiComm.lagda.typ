
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show: init-color-my-agda


= Operators
/*
```agda
{-# OPTIONS --polarity --safe --without-K --exact-split --guardedness #-}

open import MLTT.Spartan renaming (_+_ to _or_)
open import Naturals.Addition
open import UF.FunExt
open import UF.PropTrunc
open import Naturals.Order
open import Notation.Order
open import Naturals.Properties


```
*/

```agda

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
import PotP as P
open import PredP
open Pred

module MultiComm (fe : Fun-Ext) (pt : propositional-truncations-exist) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

open import Definitions Msg Secret

open ΣPred
open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠


open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot
open import Final-CoAlgebra-Properties fe Fpot fc-pot
open CoAlgebra₂ Fpot f-co fc
open Morphism

open import FCP Msg Secret 𝓥 ⟨ fc ⟩
open FC
open Pot {fc-pot}
open Pot₁ fe {fc-pot}


data FinComm (d : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
 ←m : (n : ℕ) →
       let fd = foc (d at n)
       in (msg : S×Msg) → (bsm : < Mp fd > msg)
          → FinComm ((fc ⟶) (fm fd msg bsm)) → FinComm d
 →a : (n : ℕ) →
       let fd = foc (d at n)
       in (msg : S×Msg) → (bsa : < Ap fd > msg)
          → FinComm ((fc ⟶) (fa fd msg bsa)) → FinComm d
 here : FinComm d

fin-comm : {d : Fn ⟨ fc ⟩} → FinComm d → Fn ⟨ fc ⟩
fin-comm {d} (←m n msg bsm x) = (replace d at n) (fin-comm x)
fin-comm {d} (→a n msg bsa x) = (replace d at n) (fin-comm x)
fin-comm {d} here = d



module _ where
 open import Indexed-FunctorP (Fn ⟨ fc ⟩)

 FInfComm : IFunctor (𝓤 ⊔ 𝓥)
 FInfComm =
  (λ X i →
    Σ n ꞉ ℕ
      , let fd = foc (i at n)
        in Σ msg ꞉ S×Msg
      ,   ((Σ bsm ꞉ < Mp fd > msg , X ((fc ⟶) (fm fd msg bsm)))
        or (Σ bsa ꞉ < Ap fd > msg , X ((fc ⟶) (fa fd msg bsa)))))
      , (λ { f i (n , msg , inl (bsm , v)) → n , msg , inl (bsm , f _ v)
           ; f i (n , msg , inr (bsa , v)) → n , msg , inr (bsa , (f _ v))})
  , (λ f g → dfunext fe λ i → dfunext fe λ { (n , msg , inl x) → refl
                                           ; (n , msg , inr x) → refl})
  , dfunext fe λ i → dfunext fe λ { (n , msg , inl x) → refl
                                  ; (n , msg , inr x) → refl}



 module InfCommP where

  open import Indexed-CoAlgebraP (Fn ⟨ fc ⟩)
  open import Indexed-Final-CoAlgebraP (Fn ⟨ fc ⟩)

  open IFunctor FInfComm
  open ICoAlgebra FInfComm renaming (⟨_⟩ to ⟨_⟩ᵢ)
  InfComm = IFinal-CoAlgebra FInfComm

  module _ (fc' : InfComm) where
   open IFinal-CoAlgebra FInfComm fc'

   𝟙' = 𝟙 {(𝓤 ⁺) ⊔ ((𝓥 ⁺) ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓠 ⁺)}

   g : Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x or 𝟙') → Fn (Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x or 𝟙'))
   -- We just stop changing things when we get 𝟙
   g (pt@(nx , ps , foc) , inr _) = ((fc ⟶) nx , inr ⋆) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆
   -- We perform the communication step
   g (pt@(nx , ps , foc) , inl (zero , msg , inl (bs , d))) = ((fc ⟶) ((fm foc) msg bs) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , (((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆)
   g (pt@(nx , ps , foc) , inl (zero , msg , inr (bs , d))) = ((fc ⟶) ((fa foc) msg bs) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , ((((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆))
   -- We move up to the next state
   g (pt@(nx , ps , foc) , inl (succ n , msg , d)) = (((fc ⟶) nx) , inl (n , msg , d)) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆


```
