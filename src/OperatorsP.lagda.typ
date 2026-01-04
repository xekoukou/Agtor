
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
  tail : Fnᵢ ⟨ fcᵢ ⟩ᵢ d + 𝟙 → Fnᵢ ⟨ fcᵢ ⟩ᵢ b + 𝟙 → FinComm× d b

 module _ (stream : Stream (PSet×PSet 𝓥 (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦) 𝓠)) where
  open Liveness fc-pot stream PSet-PSet-reducible
 
  Fin-Liveness : (d b : Fn ⟨ fc ⟩) → FinComm× d b → 𝓤 ⁺ ⊔ 𝓥 ⁺⁺ ⊔ 𝓦 ⁺ ⊔ 𝓠 ̇
  Fin-Liveness d b (c← nd nb msg bsmd bsab x) = Fin-Liveness _ _ x
  Fin-Liveness d b (c→ nd nb msg bsad bsmb x) = Fin-Liveness _ _ x
  Fin-Liveness d b (ex-comm dcomm bcomm x) = Fin-Liveness _ _ x
  -- TODO Maybe here we need to take into account the infinite conditions that
  -- are posed by a and b
  -- Also introduce fairness in the case that both are infinite
  Fin-Liveness d b (tail (inl x) (inl y)) = Cond-Liveness ((fc ⟶) (inf-comm d x)) ((fc ⟶) (inf-comm b y)) × 𝟙 {𝓤}
  Fin-Liveness d b (tail (inl x) (inr y)) = Cond-Liveness ((fc ⟶) (inf-comm d x)) b
  Fin-Liveness d b (tail (inr x) (inl y)) = Cond-Liveness d ((fc ⟶) (inf-comm b y))
  Fin-Liveness d b (tail (inr x) (inr y)) = Cond-Liveness d b


```
