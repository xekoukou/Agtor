{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import Naturals.Order

open import SeqP 
open import SortedStreamP
open import CoAlgebraP

module MSeqP (coℕ̂  : ∀ n → Coℕ̂  n)
             {Msg : 𝓤 ̇ } {𝓥} {Cm} {𝓦} {Cp}
             (seq : Seq Msg 𝓥 Cm 𝓦 Cp) where

open import FunctorP
open import Final-CoAlgebraP

module _ where
 private
  module F = Final-CoAlgebra (Fseq Msg 𝓥 Cm 𝓦 Cp) seq
  module S n = Final-CoAlgebra (Fℕ̂  n) (coℕ̂  n)
 
  Seqt : ℕ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
  Seqt zero = 𝟙
  Seqt (succ n) = F.type × Seqt n
 
 MSeq : _
 MSeq = Σ n ꞉ ℕ , (Σ s ꞉ S.type n , CoFℕ̂.Ordered n (S.fc n) s) × Seqt n


module MSeq (mseq : MSeq) where

 dim = mseq .pr₁

 open CoAlgebra (Fℕ̂  dim) (coℕ̂  dim .pr₁)
 open CoFℕ̂  dim (coℕ̂  dim .pr₁)

 entaglem : _
 entaglem = mseq .pr₂ .pr₁ .pr₁

 entaglem-ord : _
 entaglem-ord = mseq .pr₂ .pr₁ .pr₂

 seqs = mseq .pr₂ .pr₂


-- An index must respect the entanglements between the sequences.
-- For a specific multi-sequence , we only care for the interleaving cases that do.
 Index : ℕ̂  dim → 𝓤₀ ̇
 Index x = Σ k ꞉ ℕ , (∀ l → (rl : succ l ≤ℕ dim) → ((morph (entaglem at k) .pr₁) prₙ) l rl ≤ℕ (x prₙ) l rl × ((x prₙ) l rl ≤ℕ ((morph (entaglem at (succ k)) .pr₁) prₙ) l rl))
 
 
