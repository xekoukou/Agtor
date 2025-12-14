
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

open import FunctorP
open import CoAlgebraP
open import Final-CoAlgebraP
open import StreamP
import PotP as P
open import PredP
open Pred

module OperatorsP (fe : Fun-Ext) (Msg : 𝓤 ̇) (Secret : 𝓤 ̇  )  𝓥 𝓦 𝓠 (fc-pot : P.Pot Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠) where

open import Definitions Msg Secret
open import LivenessP fe Msg Secret 𝓥 𝓦 𝓠
open import PW-Reducible Msg Secret

open ΣPred
open P Msg Secret 𝓥 (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦) 𝓠
open import MultiComm fe Msg Secret 𝓥 𝓦 𝓠 fc-pot


open Functor Fpot
open CoAlgebra Fpot
open Final-CoAlgebra Fpot fc-pot

open import FCP Msg Secret 𝓥 ⟨ fc ⟩
open FC
open Pot {fc-pot}
open Pot₁ fe {fc-pot}

open import Indexed-FunctorP (Fn ⟨ fc ⟩)
open import Indexed-CoAlgebraP (Fn ⟨ fc ⟩)
open import Indexed-Final-CoAlgebraP (Fn ⟨ fc ⟩)

open IFunctor FInfComm
open ICoAlgebra FInfComm renaming (⟨_⟩ to ⟨_⟩ᵢ)


module _ (fc' : InfComm) where 
 open InfCommP fc'
 open IFinal-CoAlgebra FInfComm fc'

 data FinComm× (d b : Fn ⟨ fc ⟩) : 𝓤 ⊔ 𝓥 ̇  where
  c← : (nd nb : ℕ) →
        let fd = foc (d at nd)
            fb = foc (b at nb)
        in (msg : S×Msg) → (bsmd : < Mp fd > msg)
                         → (bsab : < Ap fb > msg)
           → FinComm× ((fc ⟶) (fm fd msg bsmd)) ((fc ⟶) (fa fb msg bsab)) → FinComm× d b
  c→ : (nd nb : ℕ) →
        let fd = foc (d at nd)
            fb = foc (b at nb)
        in (msg : S×Msg) → (bsad : < Ap fd > msg)
                         → (bsmb : < Mp fb > msg)
           → FinComm× ((fc ⟶) (fa fd msg bsad)) ((fc ⟶) (fm fb msg bsmb)) → FinComm× d b
  ex-comm : (dcomm : FinComm d) → (bcomm : FinComm b) → FinComm× (fin-comm' dcomm) (fin-comm' bcomm) → FinComm× d b
  ex-inf : Fnᵢ ⟨ fcᵢ ⟩ᵢ d + 𝟙 {𝓤 ⊔ 𝓥} → Fnᵢ ⟨ fcᵢ ⟩ᵢ b + 𝟙 {𝓤 ⊔ 𝓥} → FinComm× d b
  here : FinComm× d b
 module _ (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where
  open Liveness fc-pot stream PSet-PSet-reducible
 
  Fin-Liveness : (d b : Fn ⟨ fc ⟩) → FinComm× d b → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
  Fin-Liveness d b (c← nd nb msg bsmd bsab x) = Fin-Liveness _ _ x
  Fin-Liveness d b (c→ nd nb msg bsad bsmb x) = Fin-Liveness _ _ x
  Fin-Liveness d b (ex-comm dcomm bcomm x) = Fin-Liveness _ _ x
  Fin-Liveness d b (ex-inf x x₁) = {!!}
  Fin-Liveness d b here = Liveness d b
 
 -- -- fin-comm : {d : Fn ⟨ fc ⟩} → FinComm d → Fn ⟨ fc ⟩
 -- -- fin-comm {d} (←m n msg bsm x) = (replace d at n) (fin-comm x)
 -- -- fin-comm {d} (→a n msg bsa x) = (replace d at n) (fin-comm x)
 -- -- fin-comm {d} here = d
 
 -- -- fin-comm' : {d : Fn ⟨ fc ⟩} → FinComm d → Fn ⟨ fc ⟩
 -- -- fin-comm' {d} (←m n msg bsm x) = fin-comm x
 -- -- fin-comm' {d} (→a n msg bsa x) = fin-comm x
 -- -- fin-comm' {d} here = d
 
 
 
 -- -- module _ where
 -- --  open import Indexed-FunctorP (Fn ⟨ fc ⟩)
 
 -- --  FInfComm : IFunctor (𝓤 ⊔ 𝓥)
 -- --  FInfComm =
 -- --   (λ X i →
 -- --     Σ n ꞉ ℕ
 -- --       , let fd = foc (i at n)
 -- --         in Σ msg ꞉ S×Msg
 -- --       ,   ((Σ bsm ꞉ < Mp fd > msg , X ((fc ⟶) (fm fd msg bsm)))
 -- --         + (Σ bsa ꞉ < Ap fd > msg , X ((fc ⟶) (fa fd msg bsa)))))
 -- --       , (λ { f i (n , msg , inl (bsm , v)) → n , msg , inl (bsm , f _ v)
 -- --            ; f i (n , msg , inr (bsa , v)) → n , msg , inr (bsa , (f _ v))})
 -- --   , (λ f g → dfunext fe λ i → dfunext fe λ { (n , msg , inl x) → refl
 -- --                                            ; (n , msg , inr x) → refl})
 -- --   , dfunext fe λ i → dfunext fe λ { (n , msg , inl x) → refl
 -- --                                   ; (n , msg , inr x) → refl}
 
 
 
 -- --  module InfCommP where
 
 -- --   open import Indexed-CoAlgebraP (Fn ⟨ fc ⟩)
 -- --   open import Indexed-Final-CoAlgebraP (Fn ⟨ fc ⟩)
 
 -- --   open IFunctor FInfComm
 -- --   open ICoAlgebra FInfComm renaming (⟨_⟩ to ⟨_⟩ᵢ)
 -- --   InfComm = IFinal-CoAlgebra FInfComm
 
 -- --   module _ (fc' : InfComm) where
 -- --    open IFinal-CoAlgebra FInfComm fc'
 
 -- --    𝟙' = 𝟙 {(𝓤 ⁺) ⊔ ((𝓥 ⁺) ⁺) ⊔ (𝓦 ⁺) ⊔ (𝓠 ⁺)}
 
 -- --    g : Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙') → Fn (Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙'))
 -- --    -- We just stop changing things when we get 𝟙
 -- --    g (pt@(nx , ps , foc) , inr _) = ((fc ⟶) nx , inr ⋆) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆
 -- --    -- We perform the communication step
 -- --    g (pt@(nx , ps , foc) , inl (zero , msg , inl (bs , d))) = ((fc ⟶) ((fm foc) msg bs) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , (((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆)
 -- --    g (pt@(nx , ps , foc) , inl (zero , msg , inr (bs , d))) = ((fc ⟶) ((fa foc) msg bs) , inl ((fcᵢ ⟶ᵢ) _ d)) , ps , ((((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆))
 -- --    -- We move up to the next state
 -- --    g (pt@(nx , ps , foc) , inl (succ n , msg , d)) = (((fc ⟶) nx) , inl (n , msg , d)) , ps , ((Mp foc) , λ msg bs → (fc ⟶) (fm foc msg bs) , inr ⋆) , (Ap foc) , λ msg bs → (fc ⟶) (fa foc msg bs) , inr ⋆
 
 -- --    g-co : CoAlgebra Fpot
 -- --    g-co = (Σ (λ x → Fnᵢ ⟨ fcᵢ ⟩ᵢ x + 𝟙')) , g
 
 
 -- --    module _ where
    
 -- --     open CoAlgebra₂ Fpot g-co fc
 -- --     open Morphism
 
 -- --     inf-comm : ∀ d → Fnᵢ ⟨ fcᵢ ⟩ᵢ d → ⟨ fc ⟩
 -- --     inf-comm d cond = ((uni g-co .pr₁) ↓) (d , inl cond)
    
 
 -- -- ```
