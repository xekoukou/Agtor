{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

open import SortedStreamP
open import FunctorP
open import Final-CoAlgebraP
import SeqP

module Draft (coℕ̂  : ∀ n → Coℕ̂  n )
               {Msg : 𝓤 ̇ } {𝓥} {Cm} {𝓦} {Cp}
               (seq : SeqP.Seq Msg 𝓥 Cm 𝓦 Cp) where

open import PredP
open import SupPosP coℕ̂  seq

module _ 𝓣 (Cs : PCon 𝓣) (a : SupPos 𝓣 Cs) where

 module A = ΣPred a

 mp : BSet
 mp .pr₁ = {!!}
 mp .pr₂ = {!!}
