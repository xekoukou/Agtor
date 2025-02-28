{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

open import SortedStreamP
open import FunctorP
open import Final-CoAlgebraP
import SeqP

module SupPosP (coℕ̂  : ∀ n → Coℕ̂  n )
               {Msg : 𝓤 ̇ } {𝓥} {Cm} {𝓦} {Cp}
               (seq : SeqP.Seq Msg 𝓥 Cm 𝓦 Cp) where

open SeqP Msg 𝓥 Cm 𝓦 Cp
open import MSeqP coℕ̂  seq
open import PredP MSeq


SupPos : ∀ 𝓣 → PCon 𝓣 → _
SupPos 𝓣 Cs = ΣPred 𝓣 Cs

