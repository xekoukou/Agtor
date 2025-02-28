{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

open import SeqP 
open import SortedStreamP

module MSeqP (coℕ̂  : ∀ n → Coℕ̂  n)
             {Msg : 𝓤 ̇ } {𝓥} {Cm} {𝓦} {Cp}
             (seq : Seq Msg 𝓥 Cm 𝓦 Cp) where

open import FunctorP
open import Final-CoAlgebraP

private
 module F = Final-CoAlgebra (Fseq Msg 𝓥 Cm 𝓦 Cp) seq
 module S n = Final-CoAlgebra (Fℕ̂  n) (coℕ̂  n)

 Seqt : ℕ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
 Seqt zero = 𝟙
 Seqt (succ n) = F.type × Seqt n

MSeq : _
MSeq = Σ n ꞉ ℕ , S.type n × Seqt n

